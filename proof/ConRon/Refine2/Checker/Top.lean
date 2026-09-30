/-
# `ConRon.Refine2.Checker.Top` — Theorem 2 for `arena::checker`, and the tier's capstone

**Task #97-P5-Checker**, deliverables 2 and 3 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{check_decl,checker}.rs` against
`proof/ConRon/Arena/{CheckDecl,Checker}.lean`: `check_decl`'s seven arms, the pure fold
`check_decls_pure`, the two-phase fold `install_then_check` that the binary
runs, and the startup walk `intern_all_pins`.

**`install_then_check_refines` and `check_decls_pure_refines` are §8.2's own
sentence**: *the Aeneas model of the Rust `check_decls` accepting implies (B)
accepting with the abstracted state/result, over the whole outcome* — a port
`Native` included, as the twin's `native` (task #98-NATIVE; it used to claim
nothing).  The driver's fold above them is unverified
and calls this per record.

## Finding 13 — the fold's error channel is a PAIR, and that is a fifth shape

`installThenCheck` and its two phases return
`AM (Except (CheckError × Nat) IFEnv)` — the position travels as a VALUE
because (B) has ONE monad (DESIGN §8.4), where con-leche changes monad to
`StateT CState (Except (CheckError × Nat))`.  The port matches that exactly:
`Result<IFEnv, (CheckError, u64)>`.  So neither side uses its THROW channel at
the fold, and the refinement's shape is neither `Sim` (whose error arm is
`AErrSim` on a throw) nor `SimRel₀`: it is **`SimFold`** below, whose error arm
compares the pair — the kind mirrored, the position equal.

The position is real content and is compared: `absU p.2 = n`.  What is not
compared is the state on the error arm, and it must not be —
`AState.abandoned` is what the twin hands back there, deliberately (task
#97g's item 5: a second reference to the whole `AState` held across a step
made every append inside it copy), and the port's `&mut` state is simply not
read by anything after an `Err`.

## Finding 14 — `check_ind_decl` is the Inductives tier's, and it is DISCHARGED

`arena::check_decl::check_ind_decl` (task #105: the fold's arms moved out of
`arena::checker` with con-leche's `Kernel/CheckDecl.lean`) is the pinned-basis
test, the declared parameter count, the recogniser and ONE route: the uniform
install `check_block` or the decline `check_shapeless`.  The route's three
stages are `arena::inductives::*`, not this tier's, and
`Refine2/Inductives/Top.lean` exports them as `@[lockstep]` lemmas
(`block_parts_ls`, `check_block_ls`, `check_shapeless_ls`) over this tier's
base (`Checker/Base.lean`); this file imports that module and proves
`check_ind_decl_refines` by one `lockstep` call.  A capstone with no
hypotheses must transitively import every tier that discharges one.

`KnotRel checkFuel` went the same way and needed nothing:
`Refine2/Checker/KnotHyp.lean`'s `knotRel_checkFuel'` is a theorem of task
#97-P5-Arms, so the sixty-two binders that carried it were carrying a
redundant hypothesis.

## What this file's capstone still owes (task #97-T2-LOCKSTEP lane Checker)

**Nothing but its own leaves, and no precondition on the twin.**
`install_then_check_refines` and `check_decls_pure_refines` take
`AStateRel₀` and `AStateInv` and nothing else: the statements are lockstep
(the Rust and the twin do the same operations from related states), so the
declaration boundary `BrOK`, ruling 2's `DeclResolves` over an abstract `Good`
and the promote window `AStateRelW` — all Theorem-1 content that had leaked
into Theorem 2 (task #97-T2-AUDIT §2) — are deleted.  The bracket is three
`SimS₀` lemmas (`Refine2/Core/Bracket.lean`), and a bracketed step
(`check_decl_step`, `annot_step`, `annot_step_promote`, `check_pending`) is
ONE `lockstep` call over its callees' `@[lockstep]` wrappers.

The spine is `annot_fold_refines` / `annot_decl_step_refines` /
`check_pending_list_refines` / `check_decls_pure_go_refines` (cursor folds,
by hand: the twin is a list recursion with a `tryCatch`, not a zip), all
closed, and so are the arms' leaves under them: the spine is `sorry`-free
(the census at the end of the file).
-/
import ConRon.Refine2.Checker.DeclCheck
import ConRon.Refine2.Inductives.Top

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The fold's outcome shape (finding 13) -/

/-- **The outcome of a fold or a fold step.**  The Rust's error channel
carries the fold POSITION beside the error; the twin's `AM` returns an
`Except (CheckError × Nat)` as its VALUE.  The success arm is `SimRel₀`'s; the
error arm compares the kind and the position and claims nothing about the
state (both sides abandon it). -/
def SimFold {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64) ×
      arena.monad.AState)
    (x : AM (Except (Arena.CheckError × Nat) β)) : Prop :=
  match o.1 with
  | .Ok r => ∃ v lst', x.run lst = .ok (.ok v, lst') ∧ R r v ∧
      AStateRel₀ pers o.2 lst' ∧ AStateInv pers o.2
  | .Err p => ∀ k, absAErrKind p.1 = some k →
      ∃ le lst', x.run lst = .ok (.error (le, absU p.2), lst') ∧
        lAErrKind le = some k

/-! ## The arms' remaining callees in the judgements `lockstep` zips with

`DeclCheck.lean` files the `*_ok` gates' `_ls`; the Rust-only copy is here. -/

namespace Lockstep

@[lockstep] theorem top_i_constant_info_dup_spec (c : arena.env.IConstantInfo) :
    LSP (arena.env.i_constant_info_dup c)
      (fun o => absIConstantInfo o = absIConstantInfo c) :=
  fun _ h => i_constant_info_dup_abs h

end Lockstep

/-- `checkBasisDecl` at the quotient kind, in the Rust's arrangement: the
`Eq`-basis requirement as one reader (`eqBasisPinnedSpec`), then the install. -/
theorem checkBasisDecl_quotK (fe : IFEnv) :
    checkBasisDecl fe ConLeche.BasisKind.quotK = (do
      if ← eqBasisPinnedSpec fe then installBasisDecls fe (← BasisKind.declsA ConLeche.BasisKind.quotK)
      else fail (.notImplemented "quotient basis requires the pinned Eq basis")) := by
  simp only [checkBasisDecl, eqBasisPinnedSpec, bind_assoc, pure_bind, if_pos, beq_self_eq_true]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro en
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro ea
  by_cases h : (fe.find? en == some ea) = true
  · simp [h]
  · simp [h, am_fail_bind]

/-- `checkBasisDecl` at every other kind is the install alone. -/
theorem checkBasisDecl_ne (fe : IFEnv) (k : ConLeche.BasisKind) (hk : k ≠ .quotK) :
    checkBasisDecl fe k = (do installBasisDecls fe (← BasisKind.declsA k)) := by
  have : (k == ConLeche.BasisKind.quotK) = false := by cases k <;> simp_all
  simp only [checkBasisDecl, this]
  rfl

/-- `check_basis_decl_install` is `checkBasisDecl`'s tail past the `Eq`-basis
requirement. -/
theorem check_basis_decl_install_refines {pers st lst} {rf lf}
    {kind : kernel.env.BasisKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_basis_decl_install pers st rf kind = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do installBasisDecls lf (← BasisKind.declsA (ConRon.Refine.absBasisKind kind))) := by
  rw [arena.checker.check_basis_decl_install] at hrun
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS := basis_kind_decls_a_refines hrel hinv h1
  cases r with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    show AErrSim e _
    rw [StateT.run_bind]; exact AErrSim.bind hS _
  | Ok decls =>
    obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain rfl := (Result.ok_injective hrun).symm
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := hS.apply
    -- the basis's constants are canonical Rust data (`basis_kind_decls_a_wf`)
    have hI := install_basis_decls_refines (lst := lst1) hfe hfinv
      (basis_kind_decls_a_wf h1) hr1
    have e0 : absICILFrom decls 0#usize = absICIL decls := by
      simp [absICILFrom, absICIL]
    rw [e0] at hI
    show AOutRel₀ IFEnvRelI pers r1 st1 _
    rw [StateT.run_bind, hx]
    cases r1 with
    | Ok fe2 =>
      obtain ⟨v, hv, hR⟩ := hI
      exact AOutRel₀.ok hv hR hrel1 hinv1
    | Err e => exact hI

open Lockstep in
@[lockstep] theorem check_basis_decl_install_ls {pers st lst} {rf lf}
    {kind : kernel.env.BasisKind}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.checker.check_basis_decl_install pers st rf kind) lst
      (do installBasisDecls lf (← BasisKind.declsA (ConRon.Refine.absBasisKind kind))) :=
  LS.ofSimRel₀ fun _ h => check_basis_decl_install_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_basis_decl` ⊑ `checkBasisDecl`** — the quotient block's types
mention the pinned equality former, which is why it requires the `Eq` basis
first. -/
theorem check_basis_decl_refines {pers st lst} {rf lf}
    {kind : kernel.env.BasisKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_basis_decl pers st rf kind = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkBasisDecl lf (ConRon.Refine.absBasisKind kind)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  cases kind <;> rw [arena.checker.check_basis_decl.eq_def] <;> simp only
  case QuotK =>
    rw [ConRon.Refine.absBasisKind, checkBasisDecl_quotK]
    have hvis := hfe.visibleBelow.symm
    lockstep
  all_goals (rw [checkBasisDecl_ne _ _ (by simp [ConRon.Refine.absBasisKind])]; lockstep)

open Lockstep in
@[lockstep] theorem check_basis_decl_ls {pers st lst}
    {rf lf}
    {kind : kernel.env.BasisKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_basis_decl pers st rf kind) lst
      (checkBasisDecl lf (ConRon.Refine.absBasisKind kind)) :=
  LS.ofSimRel₀ fun _ h => check_basis_decl_refines hrel hinv hfe.rel hfe.inv h

/-- `check_quot_decl` ⊑ `checkDecl`'s `.quotDecl` arm — the export writes the
quotient package as four records; each is compared with the pinned block's
constant at its own kind, and the FIRST that matches installs the pinned
block whole. -/
theorem check_quot_decl_refines {pers st lst} {rf lf}
    {k : kernel.env.QuotKind} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_quot_decl pers st rf k cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkQuotDeclSpec lf (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_quot_decl]
  try unfold checkQuotDeclSpec
  lockstep

open Lockstep in
/-- `basis_pin_hit` in `LS` form: the glue `check_ind_decl_refines` zips with
(task #97-T2-LOCKSTEP lane Inductives round 3). -/
@[lockstep] theorem basis_pin_hit_ls {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map ConRon.Refine.absBasisKind a)
      (arena.basis.basis_pin_hit pers st block) lst (basisPinHit (absICIL block)) :=
  LS.ofSim₀ fun _ h => basis_pin_hit_refines hrel hinv h

/-- `check_ind_decl` ⊑ `checkDecl`'s `.indDecl` arm — the pinned basis blocks
recognised first (a stream's `Nat` block arrives as an ordinary `indDecl`),
then the declared parameter count, the recogniser and the one uniform route
(finding 14). -/
theorem check_ind_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_ind_decl pers st mode rf block n_p = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkIndDeclArmSpec (ConRon.Refine.absMode mode) lf (absICIL block)
        (absU n_p)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_ind_decl, checkIndDeclArmSpec]
  lockstep

/-! ## The axiom arm, in five -/

/-- `check_axiom_decl_rest` — the three remaining name tests: the two standard
axioms' shape mismatch, `sorryAx` tolerated as a DECLARATION, and everything
else declined. -/
theorem check_axiom_decl_rest_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_rest st rf cv_a = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclRestSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_rest]
  try unfold checkAxiomDeclRestSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_rest_ls {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.check_decl.check_axiom_decl_rest st rf cv_a) lst
      (checkAxiomDeclRestSpec lf (absIConstantVal cv_a)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_rest_refines hrel hinv hfe.rel hfe.inv h

/-- `check_axiom_decl_of_reduce` — the `ofReduce*` arm. -/
theorem check_axiom_decl_of_reduce_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_of_reduce pers st rf cv_a = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclOfReduceSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_of_reduce, checkAxiomDeclOfReduceSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_of_reduce_ls {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.check_decl.check_axiom_decl_of_reduce pers st rf cv_a) lst
      (checkAxiomDeclOfReduceSpec lf (absIConstantVal cv_a)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_of_reduce_refines hrel hinv hfe.rel hfe.inv h

/-- `check_axiom_decl_trust` — the `Lean.trustCompiler` arm. -/
theorem check_axiom_decl_trust_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_trust pers st rf cv_a = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclTrustSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_trust, checkAxiomDeclTrustSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_trust_ls {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.check_decl.check_axiom_decl_trust pers st rf cv_a) lst
      (checkAxiomDeclTrustSpec lf (absIConstantVal cv_a)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_trust_refines hrel hinv hfe.rel hfe.inv h

/-- `check_axiom_decl_std` — the axiom arm past `Quot.sound`: the common
constant check, then the standard-axiom gate. -/
theorem check_axiom_decl_std_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_std pers st mode rf cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclStdSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_std, checkAxiomDeclStdSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_std_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.check_decl.check_axiom_decl_std pers st mode rf cv) lst
      (checkAxiomDeclStdSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_std_refines hrel hinv hfe.rel hfe.inv h

@[lockstep_simp] theorem absICIL_length (v : alloc.vec.Vec arena.env.IConstantInfo) :
    (absICIL v).length = v.val.length := by simp [absICIL]

/-- `checkQuotSoundRecordSpec` in the Rust's arrangement: the length test, then
the pinned record at slot 4. -/
theorem checkQuotSoundRecordSpec_split (fe : IFEnv) (cv : IConstantVal) :
    checkQuotSoundRecordSpec fe cv = (do
      let blk ← BasisKind.decls ConLeche.BasisKind.quotK
      if blk.length ≤ 4 then fail (.notImplemented "quotient soundness axiom mismatch")
      else if ← IConstantInfo.canonEq (.axiomInfo cv) (blk.getD 4 default) then pure fe
      else fail (.notImplemented "quotient soundness axiom mismatch")) := by
  rw [checkQuotSoundRecordSpec]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro blk
  by_cases h : blk.length ≤ 4
  · rw [if_pos h, List.getElem?_eq_none h]
  · rw [if_neg h, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]

/-- `check_quot_sound_record` — **`Quot.sound` is the pinned quotient BLOCK's
own record**: the export writes it as an ordinary axiom record beside the four
`#QUOT` ones, so it arrives at the axiom arm, is compared with the pin,
installs NOTHING of its own, and DECLINES when it does not match. -/
theorem check_quot_sound_record_refines {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_quot_sound_record pers st rf cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkQuotSoundRecordSpec lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_quot_sound_record, checkQuotSoundRecordSpec_split]
  lockstep

open Lockstep in
@[lockstep] theorem check_quot_sound_record_ls {pers st lst}
    {rf lf}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.check_decl.check_quot_sound_record pers st rf cv) lst
      (checkQuotSoundRecordSpec lf (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_quot_sound_record_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_axiom_decl` ⊑ `checkDecl`'s `.axiomDecl` arm**. -/
theorem check_axiom_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl pers st mode rf cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl, checkAxiomDeclSpec]
  lockstep

/-! ## The three value arms -/

/-- `check_opaque_reduce_pin` — the compiler-trust opaques' install gate,
after the ordinary opaque check.  `k_pre` is the visibility counter the check
ran at, which the twin carries as a second environment.

**Restated by task #97-T2-LOCKSTEP lane Checker**: the old twin side ran
`checkReducePin` unconditionally, where the Rust first tests
`reduce_op_names` (`Ok fe2` for an ordinary opaque) — false as stated; the
twin side is now `checkOpaqueDeclSpec`'s own tail.  It was then open on
`hkpre` (the Rust ran the gate at `restrict(fe2, k_pre)`, the twin at `fe`);
lane Checker round 2 fixed that in the twin, and it is closed. -/
theorem check_opaque_reduce_pin_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.check_decl.check_opaque_reduce_pin pers st mode rf2 k_pre n value
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do if (← reduceOpNames).contains (absNIdx n) then
            checkReducePin (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)
              (absEIdx value)
          pure lf2) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_opaque_reduce_pin]
  lockstep

open Lockstep in
@[lockstep] theorem check_opaque_reduce_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.check_decl.check_opaque_reduce_pin pers st mode rf2 k_pre n value) lst
      (do if (← reduceOpNames).contains (absNIdx n) then
            checkReducePin (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
              (absNIdx n) (absEIdx value)
          pure lf2) :=
  LS.ofSimRel₀ fun _ h => check_opaque_reduce_pin_refines hrel hinv hfe.rel hfe.inv hk h

/-- **`check_opaque_decl` ⊑ `checkDecl`'s `.opaqueDecl` arm**. -/
theorem check_opaque_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_opaque_decl pers st mode rf cv value = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkOpaqueDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_opaque_decl, checkOpaqueDeclSpec]
  lockstep

/-- **`check_thm_decl` ⊑ `checkDecl`'s `.thmDecl` arm**. -/
theorem check_thm_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_thm_decl pers st mode rf cv value = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do
        let cvA ← checkConstantVal (ConRon.Refine.absMode mode) lf
          (absIConstantVal cv)
        checkThmVal (ConRon.Refine.absMode mode) lf cvA (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_thm_decl]
  lockstep

/-- `check_structural_nat_pin_certify` — the recurrence equations checked by
definitional equality, in the PRE-insertion environment with the operation's
self-references replaced by its stored value. -/
theorem check_structural_nat_pin_certify_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64}
    {seqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.check_decl.check_structural_nat_pin_certify pers st mode rf2 k_pre
      seqs = ok o) :
    SimRel₀ (fun r _ => IFEnvRelI r lf2) pers lst o
      (checkStructuralNatPinCertifySpec (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
        (absEqPairs seqs)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_structural_nat_pin_certify, checkStructuralNatPinCertifySpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_structural_nat_pin_certify_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64}
    {seqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers (fun r _ => IFEnvRelI r lf2)
      (arena.check_decl.check_structural_nat_pin_certify pers st mode rf2 k_pre seqs) lst
      (checkStructuralNatPinCertifySpec (ConRon.Refine.absMode mode)
        (lf2.restrictTo (absU k_pre)) lf2 (absEqPairs seqs)) :=
  LS.ofSimRel₀ fun _ h => check_structural_nat_pin_certify_refines hrel hinv hfe.rel hfe.inv hk h

/-- `check_structural_nat_pin_eqs` — the operation's own equations, built. -/
theorem check_structural_nat_pin_eqs_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.check_decl.check_structural_nat_pin_eqs pers st mode rf2 k_pre n
      = ok o) :
    SimRel₀ (fun r _ => IFEnvRelI r lf2) pers lst o
      (checkStructuralNatPinEqsSpec (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
        (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_structural_nat_pin_eqs, checkStructuralNatPinEqsSpec_split]
  lockstep

open Lockstep in
@[lockstep] theorem check_structural_nat_pin_eqs_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers (fun r _ => IFEnvRelI r lf2)
      (arena.check_decl.check_structural_nat_pin_eqs pers st mode rf2 k_pre n) lst
      (checkStructuralNatPinEqsSpec (ConRon.Refine.absMode mode)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) :=
  LS.ofSimRel₀ fun _ h => check_structural_nat_pin_eqs_refines hrel hinv hfe.rel hfe.inv hk h

/-- `check_structural_nat_pin` — the fast-path ops must be the standard
structural recursions. -/
theorem check_structural_nat_pin_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.check_decl.check_structural_nat_pin pers st mode rf2 k_pre n = ok o) :
    SimRel₀ (fun r _ => IFEnvRelI r lf2) pers lst o
      (checkStructuralNatPinSpec (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
        (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_structural_nat_pin, checkStructuralNatPinSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_structural_nat_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers (fun r _ => IFEnvRelI r lf2)
      (arena.check_decl.check_structural_nat_pin pers st mode rf2 k_pre n) lst
      (checkStructuralNatPinSpec (ConRon.Refine.absMode mode)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) :=
  LS.ofSimRel₀ fun _ h => check_structural_nat_pin_refines hrel hinv hfe.rel hfe.inv hk h

/-- `check_defn_div_mod_pin` — the `Nat.div`/`Nat.mod` gate at a definition. -/
theorem check_defn_div_mod_pin_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.check_decl.check_defn_div_mod_pin pers st mode pins rf2 k_pre n
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDefnDivModPinSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_defn_div_mod_pin, checkDefnDivModPinSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_defn_div_mod_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.check_decl.check_defn_div_mod_pin pers st mode pins rf2 k_pre n) lst
      (checkDefnDivModPinSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) :=
  LS.ofSimRel₀ fun _ h => check_defn_div_mod_pin_refines hrel hinv hfe.rel hfe.inv hk h

/-- `check_defn_pins` — both pin gates, in the twin's order. -/
theorem check_defn_pins_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.check_decl.check_defn_pins pers st mode pins rf2 k_pre n = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDefnPinsSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_defn_pins, checkDefnPinsSpec]
  -- The Rust's structural gate is a state bind right after the `contains`
  -- test; the tactic decides the twin's `if` from that test first (task
  -- #97-T2-TACTIC round 2).
  lockstep

open Lockstep in
@[lockstep] theorem check_defn_pins_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.check_decl.check_defn_pins pers st mode pins rf2 k_pre n) lst
      (checkDefnPinsSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) :=
  LS.ofSimRel₀ fun _ h => check_defn_pins_refines hrel hinv hfe.rel hfe.inv hk h

/-- **`check_defn_decl` ⊑ `checkDecl`'s `.defnDecl` arm**. -/
theorem check_defn_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {cv : arena.env.IConstantVal} {value : arena.handle.EIdx}
    {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_defn_decl pers st mode pins rf cv value hint = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDefnDeclSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_defn_decl, checkDefnDeclSpec]
  lockstep

/-! ## One declaration, and the pure fold -/

/-- **`check_decl` ⊑ `checkDecl`** — check a single declaration, extending the
environment on success.  Clause for clause; the `.indDecl` arm's route choice
is the Inductives seam (finding 14). -/
theorem check_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {d : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_decl pers st mode pins rf d = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) := by
  cases d with
  | AxiomDecl cv =>
    rw [absIDeclaration, checkDecl_axiomDecl]
    exact check_axiom_decl_refines hrel hinv hfe hfinv hrun
  | DefnDecl cv value hint =>
    -- an equation since task #97-T2-LOCKSTEP lane Checker (the twin's
    -- declines no longer read the name back)
    rw [absIDeclaration, checkDecl_defnDecl]
    exact check_defn_decl_refines hrel hinv hfe hfinv hrun
  | ThmDecl cv value =>
    rw [absIDeclaration, checkDecl_thmDecl]
    exact check_thm_decl_refines hrel hinv hfe hfinv hrun
  | OpaqueDecl cv value =>
    rw [absIDeclaration, checkDecl_opaqueDecl]
    exact check_opaque_decl_refines hrel hinv hfe hfinv hrun
  | BasisDecl kind =>
    rw [absIDeclaration, checkDecl_basisDecl]
    exact check_basis_decl_refines hrel hinv hfe hfinv hrun
  | IndDecl block n_p =>
    rw [absIDeclaration, checkDecl_indDecl]
    exact check_ind_decl_refines hrel hinv hfe hfinv hrun
  | QuotDecl k cv =>
    rw [absIDeclaration, checkDecl_quotDecl]
    exact check_quot_decl_refines hrel hinv hfe hfinv hrun

open Lockstep in
@[lockstep] theorem check_decl_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {d : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.check_decl.check_decl pers st mode pins rf d) lst
      (checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) :=
  LS.ofSimRel₀ fun _ h => check_decl_refines hrel hinv hfe.rel hfe.inv h

/-! ### The bracketed step, composed (task #98-FREEZE)

`flush_caches ; enter_scratch ; check_decl ; promote_new ; drop_scratch` on
both sides.  **The reader changes twice**: the body runs at the frozen tier
`enter_scratch` returned, the promotion writes that tier (it is read through
`glue`, `Refine2/Promote/Prims.lean`), and `drop_scratch` thaws it back into
the store, after which the reader is the caller's again.  `lockstep` keeps
one reader per judgement, so the three changes are composed here by hand at
`SimRel₀`; each body in between is one lemma.  Phase A's reader is the empty
stand-in (`hpers : pers.frozen = false`). -/

/-- A promotion's `LST` outcome, read back at the tier it returned: the glued
state through the stand-in is the frozen state through its tier. -/
theorem LST.glue_out {α β : Type} {P t' : arena.store.PersTier}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.PersTier)}
    {x : AM β} {o : core.result.Result α kernel.core_types.CheckError}
    (hP : P.frozen = false) (hsc : ScratchOn st.store)
    (h : Lockstep.LST P (fun p v => R p.1 v ∧ p.2.frozen = true) (fun t' => glue t' st) m lst x)
    (hm : m = ok (o, t')) :
    Lockstep.LOut t' (fun a b => R a b ∧ t'.frozen = true) o st (x.run lst) := by
  have hp : Lockstep.packT (fun t' => glue t' st) m
      = ok (Lockstep.packTOut (fun t' => glue t' st) (o, t')) := by
    simp only [Lockstep.packT, hm, bind_tc_ok]
  cases o with
  | Err e => exact h _ _ hp
  | Ok a =>
    obtain ⟨b, lst', hx, ⟨hR, hf⟩, hrel, hinv⟩ := h _ _ hp
    exact ⟨b, lst', hx, ⟨hR, hf⟩, (glue_rel hP).mp hrel, (glue_inv hP hsc).mp hinv⟩

/-- A stand-in reader: the tier's tables, not frozen. -/
def standIn (t : arena.store.PersTier) : arena.store.PersTier := { t with frozen := false }

/-- **`promote_new` at a frozen tier**, read back at the tier it returns — the
promotion every bracket ends in, before its `drop_scratch`. -/
theorem promote_new_drop {tier st lst rm lm rf lf} {fuel k : Std.U64} {r1 tier1}
    (htf : tier.frozen = true)
    (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hk : absU k ≤ rf.env.consts.val.length)
    (hrun : arena.promote.promote_new tier st rm fuel k rf = ok (r1, tier1)) :
    Lockstep.LOut tier1 (fun a b => (PMemoRel a.1 b.1 ∧ IFEnvRelI a.2 b.2) ∧
        tier1.frozen = true) r1 st ((promoteNew lm (absU fuel) (absU k) lf).run lst) := by
  have hsc := ScratchOn.of_inv hinv htf
  have hP : (standIn tier).frozen = false := rfl
  exact LST.glue_out hP hsc
    (promote_new_ls hP htf hsc ((glue_rel (t := tier) hP).mpr hrel) ((glue_inv (t := tier) hP hsc).mpr hinv) hm hfe
      hfinv hk) hrun

/-- `promote_vg` at a frozen tier. -/
theorem promote_vg_frozen {tier st lst rm lm} {fuel : Std.U64} {g r1 tier1}
    (htf : tier.frozen = true)
    (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_vg tier st rm fuel g = ok (r1, tier1)) :
    Lockstep.LOut tier1 (fun a b => (PMemoRel a.1 b.1 ∧ b.2 = absValueGroup a.2) ∧
        tier1.frozen = true) r1 st ((promoteVG lm (absU fuel) (absValueGroup g)).run lst) := by
  have hsc := ScratchOn.of_inv hinv htf
  have hP : (standIn tier).frozen = false := rfl
  exact LST.glue_out hP hsc
    (promote_vg_ls hP htf hsc ((glue_rel (t := tier) hP).mpr hrel) ((glue_inv (t := tier) hP hsc).mpr hinv) hm g) hrun

/-! ## Phase A: the install fold -/

/-- `annot_step_other` — `annotStepGo`'s catch-all: an ordinary `checkDecl`
with no `ValueGroup`. -/
theorem annot_step_other_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_other pers st mode pins rf pd = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (do pure (← checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd), none)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step_other]
  lockstep

open Lockstep in
@[lockstep] theorem annot_step_other_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup)
      (arena.checker.annot_step_other pers st mode pins rf pd) lst
      (do pure (← checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd), none)) :=
  LS.ofSimRel₀ fun _ h => annot_step_other_refines hrel hinv hfe.rel hfe.inv h

/-- `annot_step_opaque_install` — the opaque's install half. -/
theorem annot_step_opaque_install_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_opaque_install pers st mode rf cv value = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepOpaqueInstallSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step_opaque_install, annotStepOpaqueInstallSpec]
  lockstep

open Lockstep in
@[lockstep] theorem annot_step_opaque_install_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup)
      (arena.checker.annot_step_opaque_install pers st mode rf cv value) lst
      (annotStepOpaqueInstallSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => annot_step_opaque_install_refines hrel hinv hfe.rel hfe.inv h

/-- `annot_step_opaque` — `annotStepGo`'s `.opaqueDecl` arm. -/
theorem annot_step_opaque_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_opaque pers st mode pins rf pd cv value = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepOpaqueSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd) (absIConstantVal cv) (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step_opaque, annotStepOpaqueSpec]
  lockstep

/-- `annot_step_thm` — `annotStepGo`'s `.thmDecl` arm: **a theorem installs BY
STATEMENT**, so phase A never enters a theorem's body. -/
theorem annot_step_thm_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_thm pers st mode rf cv value = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepThmSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step_thm, annotStepThmSpec]
  lockstep

/-- `annot_step_defn_install` — the definition's install half. -/
theorem annot_step_defn_install_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_defn_install pers st mode rf cv value hint
      = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepDefnInstallSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step_defn_install, annotStepDefnInstallSpec]
  lockstep

open Lockstep in
@[lockstep] theorem annot_step_defn_install_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    {hint : kernel.env.ReducibilityHint}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup)
      (arena.checker.annot_step_defn_install pers st mode rf cv value hint) lst
      (annotStepDefnInstallSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) :=
  LS.ofSimRel₀ fun _ h => annot_step_defn_install_refines hrel hinv hfe.rel hfe.inv h

/-- `annot_step_defn` — `annotStepGo`'s `.defnDecl` arm. -/
theorem annot_step_defn_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_defn pers st mode pins rf pd cv value hint
      = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepDefnSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd) (absIConstantVal cv) (absEIdx value)
        (ConRon.Refine.absHint hint)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step_defn, annotStepDefnSpec]
  lockstep

/-- **`annot_step_go` ⊑ `annotStepGo`** — phase A's step BODY: what a step
LEAVES BEHIND. -/
theorem annot_step_go_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_go pers st mode pins rf pd = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepGo (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd)) := by
  -- the port's four-way `match` is the twin's, arm for arm; the twin's
  -- catch-all is the port's `annot_step_other` at the four other kinds
  cases pd with
  | DefnDecl cv value hint =>
    have h := annot_step_defn_refines (pd := .DefnDecl cv value hint) hrel hinv hfe hfinv
      (by rw [arena.checker.annot_step_go.eq_def] at hrun; exact hrun)
    rw [show absIDeclaration (.DefnDecl cv value hint)
        = .defnDecl (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)
        from rfl, annotStepGo_defnDecl]
    exact h
  | ThmDecl cv value =>
    have h := annot_step_thm_refines hrel hinv hfe hfinv
      (by rw [arena.checker.annot_step_go.eq_def] at hrun; exact hrun)
    rw [show absIDeclaration (.ThmDecl cv value)
        = .thmDecl (absIConstantVal cv) (absEIdx value) from rfl, annotStepGo_thmDecl]
    exact h
  | OpaqueDecl cv value =>
    have h := annot_step_opaque_refines (pd := .OpaqueDecl cv value) hrel hinv hfe hfinv
      (by rw [arena.checker.annot_step_go.eq_def] at hrun; exact hrun)
    rw [show absIDeclaration (.OpaqueDecl cv value)
        = .opaqueDecl (absIConstantVal cv) (absEIdx value) from rfl, annotStepGo_opaqueDecl]
    exact h
  | AxiomDecl cv =>
    rw [annotStepGo_other _ _ _ _ (by simp [absIDeclaration]) (by simp [absIDeclaration])
      (by simp [absIDeclaration])]
    exact annot_step_other_refines hrel hinv hfe hfinv
      (by rw [arena.checker.annot_step_go.eq_def] at hrun; exact hrun)
  | BasisDecl k =>
    rw [annotStepGo_other _ _ _ _ (by simp [absIDeclaration]) (by simp [absIDeclaration])
      (by simp [absIDeclaration])]
    exact annot_step_other_refines hrel hinv hfe hfinv
      (by rw [arena.checker.annot_step_go.eq_def] at hrun; exact hrun)
  | IndDecl block n_p =>
    rw [annotStepGo_other _ _ _ _ (by simp [absIDeclaration]) (by simp [absIDeclaration])
      (by simp [absIDeclaration])]
    exact annot_step_other_refines hrel hinv hfe hfinv
      (by rw [arena.checker.annot_step_go.eq_def] at hrun; exact hrun)
  | QuotDecl k cv =>
    rw [annotStepGo_other _ _ _ _ (by simp [absIDeclaration]) (by simp [absIDeclaration])
      (by simp [absIDeclaration])]
    exact annot_step_other_refines hrel hinv hfe hfinv
      (by rw [arena.checker.annot_step_go.eq_def] at hrun; exact hrun)

/-- **`annot_step_promote` ⊑ the value-group arm of `annotStep`** — a
deferred value group is promoted, then the step's installs are promoted at the
SAME memo, so that the sharing between a header's type and its value survives
the copy — **and the tier thawed back into the store** (task #98-FREEZE: the
Rust takes the frozen tier by value and ends in `drop_scratch`).  The
hypotheses are at the tier (`htf`), the conclusion at the caller's reader
(`hpers`).  `hk` is finding C's bound, at the counter. -/
theorem annot_step_promote_refines {pers tier st lst} {rf lf}
    {i vis k : Std.U64} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {vg : arena.checker_split.ValueGroup} {o}
    (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (htf : tier.frozen = true) (hpers : pers.frozen = false)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hk : k.val ≤ rf.visible_below.val)
    (hrun : arena.checker.annot_step_promote tier st i vis k rf pend vg = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = (absPendingCheckL r.2).toArray)
      pers lst o
      (do
        let (m, vg) ← promoteVG PMemo.empty coreWalkFuel (absValueGroup vg)
        let (_, fe) ← promoteNew m coreWalkFuel (absU k) lf
        dropScratch
        pure (fe, (absPendingCheckL pend).toArray.push ⟨vg, absU i, absU vis⟩)
        : AM (IFEnv × Array PendingCheck)) := by
  rw [arena.checker.annot_step_promote] at hrun
  obtain ⟨pm, hpm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨⟨r, tier1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hV := promote_vg_frozen (lm := PMemo.empty) htf hrel hinv (pmemo_empty_refines hpm) h1
  rw [core_walk_fuel_abs] at hV
  simp only [SimRel₀, AOutRel₀]
  simp only [am_run_bind]
  cases r with
  | Err e =>
    obtain ⟨st4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    exact AErrSim.bind hV _
  | Ok p1 =>
    obtain ⟨m, vg2⟩ := p1
    obtain ⟨⟨vm, vvg⟩, lst1, hx1, ⟨⟨hvm, hvvg⟩, htf1⟩, hrel1, hinv1⟩ := hV
    simp only [hx1, except_ok_bind]
    try simp only [Aeneas.Std.uncurry] at hrun
    try dsimp only at hrun
    obtain ⟨⟨r1, tier2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hk' : absU k ≤ rf.env.consts.val.length := le_trans hk hfinv.visBound
    have hP := promote_new_drop htf1 hrel1 hinv1 hvm hfe hfinv hk' h2
    rw [core_walk_fuel_abs] at hP
    cases r1 with
    | Err e =>
      obtain ⟨st4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      exact AErrSim.bind hP _
    | Ok p2 =>
      obtain ⟨m2, fe2⟩ := p2
      try simp only [Aeneas.Std.uncurry] at hrun
      try dsimp only at hrun
      obtain ⟨st4, h5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨pend1, hpush, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      obtain ⟨w, lst4, hx4, ⟨⟨-, hw⟩, htf2⟩, hrel4, hinv4⟩ := hP
      obtain ⟨lst5, hx5, hrel5, hinv5⟩ :=
        (drop_scratch_rel hrel4 hinv4 htf2 h5 hpers).apply
      refine ⟨(w.2, (absPendingCheckL pend).toArray.push ⟨vvg, absU i, absU vis⟩), lst5,
        ?_, ⟨hw, ?_⟩, hrel5, hinv5⟩
      · simp only [hx4, except_ok_bind, hx5]
        rfl
      · simp only at hvvg ⊢
        rw [hvvg]
        simp [absPendingCheckL, ConRon.Refine.vec_push_val hpush, absPendingCheck]

/-- **`annot_step` ⊑ `annotStep`** — phase A's step, bracketed:
`flushCaches; enterScratch; <the step>; promote; dropScratch`, composed at
`SimRel₀` as `check_decl_step_refines` is.  The twin's `pend` is an `Array`
and the port's a `Vec`, and both PUSH, so the abstraction appends. -/
theorem annot_step_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.U64}
    {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step pers st mode pins i rf pend pd = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = (absPendingCheckL r.2).toArray)
      pers lst o
      (annotStep (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) (absU i) lf
        (absPendingCheckL pend).toArray (absIDeclaration pd)) := by
  rw [arena.checker.annot_step] at hrun
  obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (flush_caches_sim₀ hrel hinv h1).apply
  obtain ⟨⟨tier, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨htier, lst2, hx2, hrel2, hinv2⟩ := enter_scratch_rel hrel1 hinv1 hpers h2
  have htf : tier.frozen = true := by rw [htier]; rfl
  obtain ⟨⟨r, st3⟩, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS := annot_step_go_refines hrel2 hinv2 hfe hfinv h3
  simp only [SimRel₀, AOutRel₀] at hS ⊢
  rw [annotStep]
  simp only [am_run_bind, hx1, except_ok_bind, hx2]
  cases r with
  | Err e =>
    obtain ⟨st4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    exact AErrSim.bind hS _
  | Ok p =>
    obtain ⟨fe2, vgo⟩ := p
    obtain ⟨⟨v, lvg⟩, lst3, hx3, ⟨hv, hvg⟩, hrel3, hinv3⟩ := hS
    dsimp only at hv hvg
    simp only [hx3, except_ok_bind]
    try simp only [Aeneas.Std.uncurry] at hrun
    try dsimp only at hrun
    obtain ⟨kk, hkk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hkv : kk.val = fe2.visible_below.val - rf.visible_below.val :=
      ConRon.Refine.HashMap.uscalar_sub_eq hkk
    have hkabs : v.visibleBelow - lf.visibleBelow = absU kk := by
      rw [hv.rel.visibleBelow, hfe.visibleBelow]; simp only [absU]; omega
    subst hvg
    cases vgo with
    | none =>
      obtain ⟨pm, hpm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨⟨r1, tier1⟩, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hk : absU kk ≤ fe2.env.consts.val.length := by
        have := hv.inv.visBound; simp only [absU]; omega
      have hP := promote_new_drop (lm := PMemo.empty) htf hrel3 hinv3
        (pmemo_empty_refines hpm) hv.rel hv.inv hk h4
      rw [core_walk_fuel_abs, ← hkabs] at hP
      cases r1 with
      | Err e =>
        obtain ⟨st4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        exact AErrSim.bind hP _
      | Ok p1 =>
        obtain ⟨m1, fe3⟩ := p1
        try simp only [Aeneas.Std.uncurry] at hrun
        try dsimp only at hrun
        obtain ⟨st4, h5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        obtain ⟨w, lst4, hx4, ⟨⟨-, hw⟩, htf1⟩, hrel4, hinv4⟩ := hP
        obtain ⟨lst5, hx5, hrel5, hinv5⟩ :=
          (drop_scratch_rel hrel4 hinv4 htf1 h5 hpers).apply
        refine ⟨(w.2, (absPendingCheckL pend).toArray), lst5, ?_, ⟨hw, rfl⟩, hrel5, hinv5⟩
        simp only [Option.map, hx4, except_ok_bind, am_run_bind, hx5]
        rfl
    | some vg =>
      have hk : kk.val ≤ fe2.visible_below.val := by omega
      have hA := annot_step_promote_refines (i := i) (pend := pend) hrel3 hinv3 htf hpers
        hv.rel hv.inv hk hrun
      simp only [SimRel₀, AOutRel₀] at hA
      simpa only [Option.map, ← hkabs, ← hfe.visibleBelow] using hA

/-- **`annot_decl_step` ⊑ `annotDeclStep`** — phase A's step with the position
carried and the error tagged (finding 13's `SimFold`). -/
theorem annot_decl_step_refines {pers st lst} {lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {p : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hfe : IFEnvRel p.2.1 lf) (hfinv : IFEnvInv p.2.1)
    (hrun : arena.checker.annot_decl_step pers st mode pins p pd = ok o) :
    SimFold (fun r v => v.1 = absU r.1 ∧ IFEnvRelI r.2.1 v.2.1 ∧
        v.2.2 = (absPendingCheckL r.2.2).toArray) pers lst o
      (annotDeclStep (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absU p.1, lf, (absPendingCheckL p.2.2).toArray) (absIDeclaration pd)) := by
  obtain ⟨pi, prf, ppend⟩ := p
  rw [arena.checker.annot_decl_step] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hA := annot_step_refines (lf := lf) (i := pi) (pend := ppend) (pd := pd)
    hrel hinv hpers hfe hfinv hq
  obtain ⟨qr, qst⟩ := q
  simp only [SimRel₀, AOutRel₀, StateT.run] at hA
  simp only [SimFold, StateT.run, annotDeclStep]
  cases hqr : qr with
  | Err e =>
    rw [hqr] at hA hrun
    have ho := Result.ok_injective hrun
    subst ho
    intro k hk
    obtain ⟨le, hle, hlk⟩ := hA k hk
    exact ⟨le, AState.abandoned, by rw [hle]; try rfl, hlk⟩
  | Ok q' =>
    rw [hqr] at hA hrun
    obtain ⟨v, lst1, hx, hv, hrel1, hinv1⟩ := hA
    obtain ⟨qf, qpend⟩ := q'
    obtain ⟨v1, v2⟩ := v
    obtain ⟨hv1, hv2⟩ := hv
    subst hv2
    obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hi2v : i2.val = pi.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have ho := Result.ok_injective hrun
    subst ho
    exact ⟨(absU pi + 1, v1, (absPendingCheckL qpend).toArray), lst1,
      by rw [hx], ⟨by simp [hi2v], hv1, rfl⟩, hrel1, hinv1⟩

/-- Phase A's fold, by the cursor's measure — `check_decls_pure_go_aux`'s
shape at the other fold. -/
private theorem annot_fold_aux (n : Nat) :
    ∀ {pers st lst lf} {mode : kernel.env.CheckMode}
      {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
      {p : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck}
      {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o},
      ds.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st → pers.frozen = false →
      IFEnvRel p.2.1 lf → IFEnvInv p.2.1 →
      arena.checker.annot_fold pers st mode pins p ds i = ok o →
      SimFold (fun r v => v.1 = absU r.1 ∧ IFEnvRelI r.2.1 v.2.1 ∧
          v.2.2 = (absPendingCheckL r.2.2).toArray) pers lst o
        (annotFold (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
          (absU p.1, lf, (absPendingCheckL p.2.2).toArray) (absIDeclLFrom ds i)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st lst lf mode pins p ds i o hn hrel hinv hpers hfe hfinv hrun
    rw [arena.checker.annot_fold.eq_def] at hrun
    dsimp only at hrun
    split at hrun
    · rename_i hge
      have hlen : ds.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val ds; scalar_tac
      have ho := Result.ok_injective hrun
      subst ho
      simp only [absIDeclLFrom, List.drop_eq_nil_of_le hlen, List.map_nil,
        annotFold, SimFold]
      exact ⟨(absU p.1, lf, (absPendingCheckL p.2.2).toArray), lst, rfl,
        ⟨rfl, ⟨hfe, hfinv⟩, rfl⟩, hrel, hinv⟩
    · rename_i hge
      have hlt : i.val < ds.val.length := by
        have := alloc.vec.Vec.len_val ds; scalar_tac
      obtain ⟨d, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hd : ds.val[i.val] = d := by
        have hg := ConRon.Refine.ExprOps.vec_index_getElem? hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hA := annot_decl_step_refines (lf := lf) (p := p) (pd := d)
        hrel hinv hpers hfe hfinv hq
      obtain ⟨qr, qst⟩ := q
      simp only [SimFold] at hA ⊢
      simp only [absIDeclLFrom, List.drop_eq_getElem_cons hlt, hd, List.map_cons,
        annotFold, am_run_bind]
      cases hqr : qr with
      | Err pr =>
        rw [hqr] at hA hrun
        have ho := Result.ok_injective hrun
        subst ho
        intro k hk
        obtain ⟨le, lst1, hx, hlk⟩ := hA k hk
        exact ⟨le, lst1, by rw [hx]; rfl, hlk⟩
      | Ok q' =>
        rw [hqr] at hA hrun
        obtain ⟨v, lst1, hx, hv, hrel1, hinv1⟩ := hA
        obtain ⟨v1, v2, v3⟩ := v
        obtain ⟨hv1, hv2, hv3⟩ := hv
        subst hv1; subst hv3
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (ds.val.length - i2.val) (by omega) (i := i2) (p := q')
          (lf := v2) rfl hrel1 hinv1 hpers hv2.1 hv2.2 hrun
        simp only [SimFold, absIDeclLFrom, hi2v] at hrec
        rw [hx]
        cases hor : o.1 with
        | Err pr =>
          rw [hor] at hrec
          intro k hk
          obtain ⟨le, lst2, hy, hlk⟩ := hrec k hk
          exact ⟨le, lst2, by rw [← hy]; rfl, hlk⟩
        | Ok r =>
          rw [hor] at hrec
          obtain ⟨w, lst2, hy, hw, hrel2, hinv2⟩ := hrec
          exact ⟨w, lst2, by rw [← hy]; rfl, hw, hrel2, hinv2⟩

/-- **`annot_fold` ⊑ `annotFold`** at the cursor. -/
theorem annot_fold_refines {pers st lst} {lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {p : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hfe : IFEnvRel p.2.1 lf) (hfinv : IFEnvInv p.2.1)
    (hrun : arena.checker.annot_fold pers st mode pins p ds i = ok o) :
    SimFold (fun r v => v.1 = absU r.1 ∧ IFEnvRelI r.2.1 v.2.1 ∧
        v.2.2 = (absPendingCheckL r.2.2).toArray) pers lst o
      (annotFold (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absU p.1, lf, (absPendingCheckL p.2.2).toArray) (absIDeclLFrom ds i)) :=
  annot_fold_aux _ rfl hrel hinv hpers hfe hfinv hrun

/-! ## Phase B: the check walk

**The representation clause between records** (task #98-FREEZE): phase B's
Rust store is FROZEN for the whole walk — its tier out, its scratch tiers
on — while the twin's is scratch-OFF between two records.  `AIdle`
(`Refine2/Core/Bracket.lean`) relates the two: the Rust state is related, at
the tier, to the twin's with its scratch tier opened.  A record's bracket is
then `clear_scratch` against `enterScratch` (`enter_record_sim`) and
`clear_scratch` against `dropScratch` (`leave_record_rel`).  A record also
leaves the twin's store in the image of `dropScratch`, which is what the thaw
at the end of `install_then_check` needs. -/

/-- The outcome of one phase-B record, between two idle states. -/
def SimIdle (tier : arena.store.PersTier) (lst : AState)
    (o : core.result.Result Unit kernel.core_types.CheckError × arena.monad.AState)
    (x : AM Unit) : Prop :=
  match o.1 with
  | .Ok _ => ∃ lst', x.run lst = .ok ((), lst') ∧ AIdle tier o.2 lst' ∧
      AStateInv tier o.2 ∧ ∃ Y : EStore, lst'.store = Y.dropScratch
  | .Err e => AErrSim e (x.run lst)

/-- **`check_pending` ⊑ `checkPending`** — phase B's check of one record,
against the prefix view `fe.restrictTo pc.vis`, from a fresh memo state, on
the frozen store: `clear_scratch; check_value_group; clear_scratch` against
`enterScratch; checkValueGroup; dropScratch`.  Nothing crosses back, so there
is nothing to promote. -/
theorem check_pending_refines {tier st lst} {rf lf}
    {mode : kernel.env.CheckMode} {pc : arena.checker.PendingCheck} {o}
    (hidle : AIdle tier st lst) (hinv : AStateInv tier st) (htf : tier.frozen = true)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_pending tier st mode rf pc = ok o) :
    SimIdle tier lst o (checkPending (ConRon.Refine.absMode mode) lf (absPendingCheck pc)) := by
  rw [arena.checker.check_pending] at hrun
  obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (enter_record_sim hidle hinv h1).apply
  obtain ⟨⟨r, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS := check_value_group_refines hrel1 hinv1 hfe hfinv h2
  obtain ⟨st3, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases Result.ok_injective hrun
  simp only [Sim₀, AOut₀] at hS
  simp only [SimIdle, checkPending, am_run_bind, hx1]
  cases r with
  | Err e => exact AErrSim.bind hS _
  | Ok u =>
    obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hS
    obtain ⟨lst3, hx3, hidle3, hinv3⟩ := leave_record_rel hrel2 hinv2 htf h3
    have hd : (dropScratch : AM Unit).run lst2
        = .ok ((), { lst2 with store := lst2.store.dropScratch, caches := Caches.empty }) := rfl
    rw [hd] at hx3
    cases hx3
    refine ⟨_, ?_, hidle3, hinv3, lst2.store, rfl⟩
    have hx2' : (checkValueGroup (ConRon.Refine.absMode mode)
        (lf.restrictTo (absPendingCheck pc).vis) (absPendingCheck pc).vg).run lst1
        = .ok ((), lst2) := hx2
    simp only [hx2', except_ok_bind]
    rfl

/-! ## The error tag and the startup walk -/

/-- `intern_all_names` — the reserved names the guards compare by handle.

Glue since twin fix D5 of task #97-T2-LOCKSTEP made the twin's
`reservedBasisNames` the table read `pinReserved`, as the port's
`reserved_basis_names` is `pin_reserved` (task #97-P6-4a): two table reads
(`reserved_basis_names_refines`, `pin_sorry_ax_refines`,
`pin_quot_sound_refines` — `SimRE`, the state does not move) around three pin
walks (`nat_op_names_refines`, `nat_div_mod_names_refines`,
`reduce_op_names_refines`). -/
theorem intern_all_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_names st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o internAllNamesSpec := by
  rw [arena.checker.intern_all_names] at hrun
  unfold Sim₀
  rw [internAllNamesSpec]
  obtain ⟨r0, hr0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS0 := reserved_basis_names_refines hrel hinv hr0
  cases r0 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    refine AOut₀.err ?_
    rw [am_run_bind']
    exact AErrSim.bind hS0 _
  | Ok a0 =>
  rw [am_run_bind', SimRE.apply hS0, except_ok_bind]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := nat_op_names_refines hrel hinv hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := nat_div_mod_names_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := reduce_op_names_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨r4, hr4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS4 := pin_sorry_ax_refines hrel3 hinv3 hr4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.err (pin_err hS4)
  | Ok a4 =>
  rw [pin_ok hS4]
  obtain ⟨r5, hr5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS5 := pin_quot_sound_refines hrel3 hinv3 hr5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.err (pin_err hS5)
  | Ok a5 =>
  have ho := Result.ok_injective hrun
  subst ho
  refine AOut₀.ok ?_ hrel3 hinv3
  rw [pin_ok hS5]
  rfl

/-- `intern_all_reduce_pins` — the two reduce pins. -/
theorem intern_all_reduce_pins_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_reduce_pins pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllReducePinsSpec := by
  rw [arena.checker.intern_all_reduce_pins] at hrun
  unfold Sim₀
  rw [internAllReducePinsSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := reduce_nat_cv_a_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := reduce_bool_cv_a_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := of_reduce_nat_a_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := of_reduce_bool_a_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r5, st5⟩ := q5
  have hS5 := reduce_nat_decl_pin_refines hrel4 hinv4 hq5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS5
  | Ok u5 =>
  obtain ⟨lst5, hx5, hrel5, hinv5⟩ := Sim₀.apply hS5
  rw [run_bind_ok hx5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r6, st6⟩ := q6
  have hS6 := reduce_bool_decl_pin_refines hrel5 hinv5 hq6
  cases r6 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS6
  | Ok u6 =>
  obtain ⟨lst6, hx6, hrel6, hinv6⟩ := Sim₀.apply hS6
  rw [run_bind_ok hx6]
  have ho := Result.ok_injective hrun
  subst ho
  exact AOut₀.ok rfl hrel6 hinv6

/-- `intern_all_trust_pins` — the compiler-trust axiom pins. -/
theorem intern_all_trust_pins_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_trust_pins pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllTrustPinsSpec := by
  rw [arena.checker.intern_all_trust_pins] at hrun
  unfold Sim₀
  rw [internAllTrustPinsSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := true_cv_a_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := true_intro_cv_a_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := trust_compiler_a_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := bool_cv_a_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  exact intern_all_reduce_pins_refines hrel4 hinv4 hrun

/-- `intern_all_axiom_pins_rest` — the standard axiom pins past the `Iff`
family. -/
theorem intern_all_axiom_pins_rest_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_axiom_pins_rest pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllAxiomPinsRestSpec := by
  rw [arena.checker.intern_all_axiom_pins_rest] at hrun
  unfold Sim₀
  rw [internAllAxiomPinsRestSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := nonempty_intro_raw_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := nonempty_rec_raw_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := propext_raw_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := choice_raw_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  exact intern_all_trust_pins_refines hrel4 hinv4 hrun

/-- `intern_all_axiom_pins` — the standard axiom pins. -/
theorem intern_all_axiom_pins_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_axiom_pins pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllAxiomPinsSpec := by
  rw [arena.checker.intern_all_axiom_pins] at hrun
  unfold Sim₀
  rw [internAllAxiomPinsSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := iff_raw_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := iff_intro_raw_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := iff_rec_raw_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := nonempty_raw_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  exact intern_all_axiom_pins_rest_refines hrel4 hinv4 hrun

/-- `all_basis_kinds` is the five basis kinds in `internAllPins`' order. -/
theorem all_basis_kinds_refines {o}
    (hrun : arena.checker.all_basis_kinds = ok o) :
    o.val.map ConRon.Refine.absBasisKind =
      [.eqK, .natK, .emptyK, .falseK, .quotK] := by
  rw [arena.checker.all_basis_kinds] at hrun
  obtain ⟨k1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k2, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k3, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [ConRon.Refine.vec_push_val hrun, ConRon.Refine.vec_push_val h4, ConRon.Refine.vec_push_val h3,
    ConRon.Refine.vec_push_val h2, ConRon.Refine.vec_push_val h1,
    ConRon.Refine.ExprOps.with_capacity_val]
  rfl

/-- The cursor's measure induction behind `intern_all_basis_refines`. -/
private theorem intern_all_basis_aux {pers : arena.store.PersTier} (m : Nat) :
    ∀ {st lst} {i : Std.Usize} {o},
      5 - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st →
      arena.checker.intern_all_basis pers st i = ok o →
      Sim₀ (fun _ : Unit => ()) pers lst o
        (internAllBasisSpec
          ([ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK,
            .quotK].drop i.val)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro st lst i o hm hrel hinv hrun
    rw [arena.checker.intern_all_basis.eq_def] at hrun
    dsimp only at hrun
    obtain ⟨ks, hks, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hk := all_basis_kinds_refines hks
    have hlen5 : ks.val.length = 5 := by
      have h := congrArg List.length hk
      simpa using h
    have hl := alloc.vec.Vec.len_val ks
    unfold Sim₀
    by_cases hge : i ≥ ks.len
    · have hle : 5 ≤ i.val := by scalar_tac
      rw [if_pos hge] at hrun
      have ho := Result.ok_injective hrun
      subst ho
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      exact AOut₀.ok rfl hrel hinv
    · have hlt : i.val < ks.val.length := by scalar_tac
      rw [if_neg hge] at hrun
      obtain ⟨bk, hbk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hlt', rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hbk
      rw [← hk, ← List.map_drop, List.drop_eq_getElem_cons hlt, List.map_cons,
        internAllBasisSpec]
      obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, st1⟩ := q1
      have hS1 := basis_kind_decls_refines hrel hinv hq1
      cases r1 with
      | Err e =>
        have ho := Result.ok_injective hrun
        subst ho
        exact AOut₀.errBind hS1
      | Ok u1 =>
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
      rw [run_bind_ok hx1]
      obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r2, st2⟩ := q2
      have hS2 := basis_kind_decls_a_refines hrel1 hinv1 hq2
      cases r2 with
      | Err e =>
        have ho := Result.ok_injective hrun
        subst ho
        exact AOut₀.errBind hS2
      | Ok u2 =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
      rw [run_bind_ok hx2]
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have hrec := ih (5 - i2.val) (by omega) rfl hrel2 hinv2 hrun
      rw [← hk, ← List.map_drop, hi2v] at hrec
      exact hrec

/-- `intern_all_basis` — the five basis blocks in BOTH forms, at the cursor. -/
theorem intern_all_basis_refines {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_basis pers st i = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (internAllBasisSpec
        ([ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK,
          .quotK].drop i.val)) := by
  exact intern_all_basis_aux _ rfl hrel hinv hrun

/-- **`intern_all_pins` ⊑ the port's startup walk** — DESIGN §8.6 P2d's
one-time tree walk, as the port runs it (task #97-P5-Top): the basis blocks,
the axiom pins, the reserved names and the pin sets, four children in
sequence.  Glue: `intern_all_basis_refines`, `intern_all_axiom_pins_refines`,
`intern_all_names_refines` and `intern_pin_sets_refines`.

Since round 2's ruling (a) the twin interns the raw pins too, so
`internAllPinsPortSpec` is `internAllPins` (`internAllPinsPortSpec_eq`) and
this is the proof route of `intern_all_pins_refines` below. -/
theorem intern_all_pins_port_refines {pers st lst}
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pins.val, NatOpPinSetWF p)
    (hrun : arena.checker.intern_all_pins pers st pins = ok o) :
    Sim₀ absINatOpPinSetL pers lst o
      (internAllPinsPortSpec (ConRon.Refine.absPins pins)) := by
  rw [arena.checker.intern_all_pins] at hrun
  unfold Sim₀
  rw [internAllPinsPortSpec]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := intern_all_basis_refines (i := 0#usize) hrel hinv hq1
  simp only [List.drop_zero, show (0#usize : Std.Usize).val = 0 from rfl] at hS1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := intern_all_axiom_pins_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := intern_all_names_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  have hS4 := intern_pin_sets_refines (i := 0#usize) hrel3 hinv3 hwf hrun
  have h0 : absINatOpPinSetL (alloc.vec.Vec.new arena.nat_op_pin_set.INatOpPinSet)
      = [] := rfl
  have h1 : (pins.val.drop (0#usize : Std.Usize).val).map ConRon.Refine.absNatOpPinSet
      = ConRon.Refine.absPins pins := by
    simp [ConRon.Refine.absPins]
  simp only [h0, h1, List.nil_append] at hS4
  unfold Sim₀ at hS4
  rw [show (do pure (← internPinSets (ConRon.Refine.absPins pins)) : AM _)
      = internPinSets (ConRon.Refine.absPins pins) from bind_pure _] at hS4
  exact hS4

/-- **The port's startup walk is the twin's**: `internAllPinsPortSpec` — the
four Rust functions' transcriptions in sequence — is `internAllPins`, the flat
`do` block, re-bracketed by the monad laws.  An equation since task
#97-P5-Top round 2's ruling (a) made the twin intern the eight standard-axiom
and `ofReduce*` pins RAW, as the port does. -/
theorem internAllPinsPortSpec_eq (ps : List ConLeche.NatOpPinSet) :
    internAllPinsPortSpec ps = internAllPins ps := by
  simp only [internAllPinsPortSpec, internAllBasisSpec, internAllAxiomPinsSpec,
    internAllAxiomPinsRestSpec, internAllTrustPinsSpec, internAllReducePinsSpec,
    internAllNamesSpec, internAllPins, bind_assoc, pure_bind]

/-- **`intern_all_pins` ⊑ `internAllPins`** — what the capstone consumes.

Task #97-P5-Top found it false (the port interned eight pins raw, the twin
annotated); round 2's ruling (a) made the twin intern the raw pins
(`Arena/Checker.lean`), and it is now `intern_all_pins_port_refines` through
`internAllPinsPortSpec_eq`. -/
theorem intern_all_pins_refines {pers st lst}
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pins.val, NatOpPinSetWF p)
    (hrun : arena.checker.intern_all_pins pers st pins = ok o) :
    Sim₀ absINatOpPinSetL pers lst o
      (internAllPins (ConRon.Refine.absPins pins)) := by
  rw [← internAllPinsPortSpec_eq]
  exact intern_all_pins_port_refines hrel hinv hwf hrun


/-! ## The axiom census

**The spine is closed, leaves included** (task #97-MILESTONE, `arena`
`db1131f1`).  `install_then_check_refines` is `annot_fold_refines` and
`check_pending_list_refines` composed, `check_decls_pure_refines` is
`check_decls_pure_go_refines` at the empty environment, and the three leaves
the fold stands on — `annot_step_refines`, `check_pending_refines` and
`check_decl_step_refines` — are proved; every row below prints the three
standard axioms and nothing else.  (Until the lane Inductives Install
slice 2 and lane Inductives round 6 slice 2 landings these rows printed
`sorryAx` through the leaves' bodies; the `#guard_msgs` pins keep them from
regressing silently.) -/

/-! **Task #97-P5-Checker round 4, task #97-P5-Top.**  The two bracketed
leaves are compositions of their BODIES (`check_decl_refines`,
`annot_step_go_refines`'s arms), which are closed as well. -/

/-- info: 'ConRon.Refine2.annot_step_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annot_step_refines

/-- info: 'ConRon.Refine2.all_basis_kinds_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all_basis_kinds_refines

end ConRon.Refine2
