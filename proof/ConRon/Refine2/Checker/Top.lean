/-
# `ConRon.Refine2.Checker.Top` — Theorem 2 for `arena::checker`, and the tier's capstone

**Task #97-P5-Checker**, deliverables 2 and 3 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/checker.rs` against
`proof/ConRon/Arena/Checker.lean`: `check_decl`'s seven arms, the pure fold
`check_decls_pure`, the two-phase fold `install_then_check` that the binary
runs, and the startup walk `intern_all_pins`.

**`install_then_check_refines` and `check_decls_pure_refines` are §8.2's own
sentence**: *the Aeneas model of the Rust `check_decls` accepting implies (B)
accepting with the abstracted state/result, over the whole outcome; the port's
`Native` error claims nothing.*  The driver's fold above them is unverified
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

`checkDecl`'s `.indDecl` arm calls `Inductives.checkIndDecl`, which is
`arena::inductives::*` — 6 705 lines that are NOT this tier's.  Task
#97-P5-Checker carried that seam as a hypothesis (`hind : IndRel`) at thirteen
sites; task #97-P5-Ind proved `ind_rel : IndRel` unconditionally, and task
#97-P5-Checker-2 deleted the thirteen binders.

**That cost an import swap, and it is the right end state.**  `IndRel` used to
be declared HERE and proved in `Refine2/Inductives/Top.lean`, which imports
this file — so no proof here could reach `ind_rel`.  The structure now lives
in `Refine2/Checker/Shape.lean` (the base both tiers already import), that
file's `import ConRon.Refine2.Checker.Top` is gone, and this file imports the
Inductives tier instead.  (Task #97-T2-LOCKSTEP lane Checker round 2 deleted `IndRel` itself:
its old `AStateRel`/`SimRel` shape had no consumer once the Inductives lane
retired `ind_rel`, and `check_ind_decl_refines` is called directly.)  A capstone with no hypotheses must transitively
import every tier that discharges one.

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
closed; the `sorry`s under them are the arms' leaves.
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

/-! ## The cursor at zero, and the empty pending list

The two capstones call their folds at cursor `0`, where the `…From`
abstraction (DESIGN §3.4's `List`-as-cursor deviation) is the plain one. -/

private theorem absIDeclLFrom_zero (ds : alloc.vec.Vec arena.env.IDeclaration) :
    absIDeclLFrom ds 0#usize = absIDeclL ds := by simp

private theorem absPendingCheckLFrom_zero
    (v : alloc.vec.Vec arena.checker.PendingCheck) :
    absPendingCheckLFrom v 0#usize = absPendingCheckL v := by simp

private theorem absPendingCheckL_new :
    absPendingCheckL (alloc.vec.Vec.new arena.checker.PendingCheck) = [] := rfl

private theorem absU_zero : absU (0#u64) = 0 := rfl

private theorem absPendingCheckL_new_toArray :
    (absPendingCheckL (alloc.vec.Vec.new arena.checker.PendingCheck)).toArray
      = (#[] : Array PendingCheck) := rfl

private theorem toList_toArray' {α : Type} (l : List α) : l.toArray.toList = l := rfl

/-! ## The empty environment, on both sides

`check_decls_pure` and `install_then_check` both open with
`mk_ifenv(i_env_empty)` where the twin writes `mkIFEnv IEnv.empty`.
`arena::env` has no tier of its own — it is the record layer
`Refine2/AbsState.lean` abstracts, not a checked module — so the one fact the
two capstones need about it is proved here, where it is used. -/

/-- **`mk_ifenv (i_env_empty)` ⊑ `mkIFEnv IEnv.empty`.**  The index is the
fresh table `HashMap2::with_capacity 0` gives (`mk_ifenv_go` stops at once on
an empty `Vec`), the counter is `0`, and the twin's `mkIFEnvGo []` is
`(0, ∅)`. -/
private theorem mk_ifenv_empty_refines {e f}
    (he : arena.env.i_env_empty = ok e) (hf : arena.env.mk_ifenv e = ok f) :
    IFEnvRel f (mkIFEnv IEnv.empty) ∧ IFEnvInv f := by
  rw [arena.env.i_env_empty] at he
  have he' : e = { consts := alloc.vec.Vec.new arena.env.IConstantInfo } :=
    (Result.ok_injective he).symm
  subst he'
  rw [arena.env.mk_ifenv] at hf
  obtain ⟨hm, hhm, hf⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
  obtain ⟨hinv0, -, hnone⟩ :=
    ConRon.Refine.HashMap2.with_capacity_refines
      (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm
  obtain ⟨q, hq, hf⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
  rw [arena.env.mk_ifenv_go] at hq
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.len, ge_iff_le, le_refl, if_pos] at hq
  have hq' : q = (0#u64, hm) := (Result.ok_injective hq).symm
  subst hq'
  have hf' := (Result.ok_injective hf).symm
  subst hf'
  refine ⟨⟨rfl, ?_, rfl, fun ci h => by simp [alloc.vec.Vec.new] at h,
    fun k p hp => by rw [hnone k] at hp; exact absurd hp (by simp)⟩, hinv0, by simp, ?_⟩
  · intro n
    rw [hnone n]
    simp [mkIFEnv, mkIFEnvGo, IEnv.empty]
  · intro n p hp
    rw [hnone n] at hp
    exact absurd hp (by simp)

/-! ## The basis and quotient arms -/

/-- `check_basis_decl_install` is `checkBasisDecl`'s tail past the `Eq`-basis
requirement. -/
theorem check_basis_decl_install_refines {pers st lst} {rf lf}
    {kind : kernel.env.BasisKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_basis_decl_install pers st rf kind = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do installBasisDecls lf (← BasisKind.declsA (ConRon.Refine.absBasisKind kind))) := by
  sorry

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
  sorry

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
    (hrun : arena.checker.check_quot_decl pers st rf k cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkQuotDeclSpec lf (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_quot_decl_ls {pers st lst}
    {rf lf}
    {k : kernel.env.QuotKind}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_quot_decl pers st rf k cv) lst
      (checkQuotDeclSpec lf (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_quot_decl_refines hrel hinv hfe.rel hfe.inv h

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
then the inductive routes.  **Finding 14's `hind`.** -/
theorem check_ind_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_ind_decl pers st mode rf block n_p = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkIndDeclArmSpec (ConRon.Refine.absMode mode) lf (absICIL block)
        (absU n_p)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_ind_decl, checkIndDeclArmSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_ind_decl_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {n_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_ind_decl pers st mode rf block n_p) lst
      (checkIndDeclArmSpec (ConRon.Refine.absMode mode) lf (absICIL block)
        (absU n_p)) :=
  LS.ofSimRel₀ fun _ h => check_ind_decl_refines hrel hinv hfe.rel hfe.inv h

/-! ## The axiom arm, in five -/

/-- `check_axiom_decl_rest` — the three remaining name tests: the two standard
axioms' shape mismatch, `sorryAx` tolerated as a DECLARATION, and everything
else declined. -/
theorem check_axiom_decl_rest_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_rest st rf cv_a = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclRestSpec lf (absIConstantVal cv_a)) := by
  sorry

/-- `check_axiom_decl_of_reduce` — the `ofReduce*` arm. -/
theorem check_axiom_decl_of_reduce_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_of_reduce pers st rf cv_a = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclOfReduceSpec lf (absIConstantVal cv_a)) := by
  sorry

/-- `check_axiom_decl_trust` — the `Lean.trustCompiler` arm. -/
theorem check_axiom_decl_trust_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_trust pers st rf cv_a = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclTrustSpec lf (absIConstantVal cv_a)) := by
  sorry

/-- `check_axiom_decl_std` — the axiom arm past `Quot.sound`: the common
constant check, then the standard-axiom gate. -/
theorem check_axiom_decl_std_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_std pers st mode rf cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclStdSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_axiom_decl_std_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_axiom_decl_std pers st mode rf cv) lst
      (checkAxiomDeclStdSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_std_refines hrel hinv hfe.rel hfe.inv h

/-- `check_quot_sound_record` — **`Quot.sound` is the pinned quotient BLOCK's
own record**: the export writes it as an ordinary axiom record beside the four
`#QUOT` ones, so it arrives at the axiom arm, is compared with the pin,
installs NOTHING of its own, and DECLINES when it does not match. -/
theorem check_quot_sound_record_refines {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_quot_sound_record pers st rf cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkQuotSoundRecordSpec lf (absIConstantVal cv)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_quot_sound_record_ls {pers st lst}
    {rf lf}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_quot_sound_record pers st rf cv) lst
      (checkQuotSoundRecordSpec lf (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_quot_sound_record_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_axiom_decl` ⊑ `checkDecl`'s `.axiomDecl` arm**. -/
theorem check_axiom_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl pers st mode rf cv = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkAxiomDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_axiom_decl, checkAxiomDeclSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_axiom_decl pers st mode rf cv) lst
      (checkAxiomDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_refines hrel hinv hfe.rel hfe.inv h

/-! ## The three value arms -/

/-- `check_opaque_reduce_pin` — the compiler-trust opaques' install gate,
after the ordinary opaque check.  `k_pre` is the visibility counter the check
ran at, which the twin carries as a second environment.

**Restated by task #97-T2-LOCKSTEP lane Checker**: the old twin side ran
`checkReducePin` unconditionally, where the Rust first tests
`reduce_op_names` (`Ok fe2` for an ordinary opaque) — false as stated; the
twin side is now `checkOpaqueDeclSpec`'s own tail.  Still open on `hkpre`
(the Rust runs the gate at `restrict(fe2, k_pre)`, the twin at `fe`; see
DESIGN's lane Checker section). -/
theorem check_opaque_reduce_pin_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.checker.check_opaque_reduce_pin pers st mode rf2 k_pre n value
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do if (← reduceOpNames).contains (absNIdx n) then
            checkReducePin (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)
              (absEIdx value)
          pure lf2) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_opaque_reduce_pin]
  simp only [pure_bind]
  lockstep

open Lockstep in
@[lockstep] theorem check_opaque_reduce_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.checker.check_opaque_reduce_pin pers st mode rf2 k_pre n value) lst
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
    (hrun : arena.checker.check_opaque_decl pers st mode rf cv value = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkOpaqueDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_opaque_decl, checkOpaqueDeclSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_opaque_decl_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_opaque_decl pers st mode rf cv value) lst
      (checkOpaqueDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => check_opaque_decl_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_thm_decl` ⊑ `checkDecl`'s `.thmDecl` arm**. -/
theorem check_thm_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_thm_decl pers st mode rf cv value = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do
        let cvA ← checkConstantVal (ConRon.Refine.absMode mode) lf
          (absIConstantVal cv)
        checkThmVal (ConRon.Refine.absMode mode) lf cvA (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_thm_decl]
  lockstep

open Lockstep in
@[lockstep] theorem check_thm_decl_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_thm_decl pers st mode rf cv value) lst
      (do
        let cvA ← checkConstantVal (ConRon.Refine.absMode mode) lf
          (absIConstantVal cv)
        checkThmVal (ConRon.Refine.absMode mode) lf cvA (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => check_thm_decl_refines hrel hinv hfe.rel hfe.inv h

/-- `check_structural_nat_pin_certify` — the recurrence equations checked by
definitional equality, in the PRE-insertion environment with the operation's
self-references replaced by its stored value. -/
theorem check_structural_nat_pin_certify_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64}
    {seqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.checker.check_structural_nat_pin_certify pers st mode rf2 k_pre
      seqs = ok o) :
    SimRel₀ (fun r _ => IFEnvRelI r lf2) pers lst o
      (checkStructuralNatPinCertifySpec (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
        (absEqPairs seqs)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_structural_nat_pin_certify, checkStructuralNatPinCertifySpec]
  simp only [pure_bind, am_fail_bind]
  lockstep

open Lockstep in
@[lockstep] theorem check_structural_nat_pin_certify_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64}
    {seqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers (fun r _ => IFEnvRelI r lf2)
      (arena.checker.check_structural_nat_pin_certify pers st mode rf2 k_pre seqs) lst
      (checkStructuralNatPinCertifySpec (ConRon.Refine.absMode mode)
        (lf2.restrictTo (absU k_pre)) lf2 (absEqPairs seqs)) :=
  LS.ofSimRel₀ fun _ h => check_structural_nat_pin_certify_refines hrel hinv hfe.rel hfe.inv hk h

/-- `check_structural_nat_pin_eqs` — the operation's own equations, built. -/
theorem check_structural_nat_pin_eqs_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.checker.check_structural_nat_pin_eqs pers st mode rf2 k_pre n
      = ok o) :
    SimRel₀ (fun r _ => IFEnvRelI r lf2) pers lst o
      (checkStructuralNatPinEqsSpec (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
        (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_structural_nat_pin_eqs, checkStructuralNatPinEqsSpec_split]
  lockstep

open Lockstep in
@[lockstep] theorem check_structural_nat_pin_eqs_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers (fun r _ => IFEnvRelI r lf2)
      (arena.checker.check_structural_nat_pin_eqs pers st mode rf2 k_pre n) lst
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
    (hrun : arena.checker.check_structural_nat_pin pers st mode rf2 k_pre n = ok o) :
    SimRel₀ (fun r _ => IFEnvRelI r lf2) pers lst o
      (checkStructuralNatPinSpec (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
        (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_structural_nat_pin, checkStructuralNatPinSpec]
  simp only [pure_bind, am_fail_bind]
  lockstep

open Lockstep in
@[lockstep] theorem check_structural_nat_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers (fun r _ => IFEnvRelI r lf2)
      (arena.checker.check_structural_nat_pin pers st mode rf2 k_pre n) lst
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
    (hrun : arena.checker.check_defn_div_mod_pin pers st mode pins rf2 k_pre n
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDefnDivModPinSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_defn_div_mod_pin, checkDefnDivModPinSpec]
  simp only [pure_bind]
  lockstep

open Lockstep in
@[lockstep] theorem check_defn_div_mod_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.checker.check_defn_div_mod_pin pers st mode pins rf2 k_pre n) lst
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
    (hrun : arena.checker.check_defn_pins pers st mode pins rf2 k_pre n = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDefnPinsSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (lf2.restrictTo (absU k_pre)) lf2 (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_defn_pins, checkDefnPinsSpec]
  -- The Rust's structural gate is a state bind right after the `contains`
  -- test; the tactic decides the twin's `if` first (its `twin_bind_pure`
  -- fallback is not taken at an undecided `if`, task #97-P5-Core round 5).
  lockstep

open Lockstep in
@[lockstep] theorem check_defn_pins_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.checker.check_defn_pins pers st mode pins rf2 k_pre n) lst
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
    (hrun : arena.checker.check_defn_decl pers st mode pins rf cv value hint = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDefnDeclSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_defn_decl, checkDefnDeclSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_defn_decl_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    {hint : kernel.env.ReducibilityHint}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.checker.check_defn_decl pers st mode pins rf cv value hint) lst
      (checkDefnDeclSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) :=
  LS.ofSimRel₀ fun _ h => check_defn_decl_refines hrel hinv hfe.rel hfe.inv h

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
    (hrun : arena.checker.check_decl pers st mode pins rf d = ok o) :
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
      (arena.checker.check_decl pers st mode pins rf d) lst
      (checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) :=
  LS.ofSimRel₀ fun _ h => check_decl_refines hrel hinv hfe.rel hfe.inv h

/-! ### The bracketed step, composed (task #97-P5-Checker round 4, task #97-P5-Top)

`flush_caches ; enter_scratch ; check_decl ; promote_new ; drop_scratch` on
both sides — one `lockstep` call (task #97-T2-LOCKSTEP lane Checker).

**No frozen-tier fact is needed.**  Round 4 composed both bracketed steps
under `KeepsUnfrozen` of their bodies and `PersUnfrozen` at their entry — port
facts no refinement statement concludes.  Task #97-P5-Usize made the
`M_FROZEN` guard `Native` (a `Native` decline claims nothing), task #97-P5-Top
dropped `hfr` from the promotion lemmas, and the steps are plain
compositions. -/

/-- **`check_decl_step` ⊑ `checkDeclStep`** — one step of the pure fold,
BRACKETED: `checkDecl` inside the per-declaration scratch tier, with the
constants it installed promoted before the tier goes.  This is where
`Refine2/Promote/Promote.lean`'s `promote_new_refines` is consumed, and where
its finding C (`k ≤ n`) is discharged: `k` is `fe.visibleBelow - vis` for the
counter read before the step. -/
theorem check_decl_step_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {d : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_decl_step pers st mode pins rf d = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDeclStep (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.check_decl_step, checkDeclStep]
  lockstep

/-- The cursor's measure induction — task #97-P5-0's finding 7 shape step, at
a `Vec` rather than at a fuel: `ds.length - i` decreases and the arm's own
`i + 1` is what makes it do so. -/
private theorem check_decls_pure_go_aux (n : Nat) :
    ∀ {pers st lst rf lf} {mode : kernel.env.CheckMode}
      {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
      {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o},
      ds.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRel rf lf → IFEnvInv rf →
      arena.checker.check_decls_pure_go pers st mode pins rf ds i = ok o →
      SimRel₀ IFEnvRelI pers lst o
        (checkDeclsPureGo (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
          (absIDeclLFrom ds i)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st lst rf lf mode pins ds i o hn hrel hinv hfe hfinv hrun
    rw [arena.checker.check_decls_pure_go.eq_def] at hrun
    dsimp only at hrun
    split at hrun
    · -- the cursor is past the end: both sides stop
      rename_i hge
      have hlen : ds.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val ds; scalar_tac
      have ho := Result.ok_injective hrun
      subst ho
      simp only [absIDeclLFrom, List.drop_eq_nil_of_le hlen, List.map_nil,
        checkDeclsPureGo, SimRel₀]
      exact AOutRel₀.ok rfl ⟨hfe, hfinv⟩ hrel hinv
    · rename_i hge
      have hlt : i.val < ds.val.length := by
        have := alloc.vec.Vec.len_val ds; scalar_tac
      obtain ⟨d, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hd : ds.val[i.val] = d := by
        have hg := ConRon.Refine.ExprOps.vec_index_getElem? hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hS := check_decl_step_refines (lf := lf) (d := d) hrel hinv hfe
        hfinv hq
      obtain ⟨qr, qst⟩ := q
      simp only [SimRel₀, AOutRel₀] at hS ⊢
      simp only [absIDeclLFrom, List.drop_eq_getElem_cons hlt, hd, List.map_cons,
        checkDeclsPureGo, am_run_bind]
      cases hqr : qr with
      | Err e =>
        rw [hqr] at hS hrun
        have ho := Result.ok_injective hrun
        subst ho
        exact AErrSim.bind hS _
      | Ok fe2 =>
        rw [hqr] at hS hrun
        obtain ⟨v, lst1, hx, hv, hrel1, hinv1⟩ := hS
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (ds.val.length - i2.val) (by omega) (i := i2) (lf := v)
          rfl hrel1 hinv1 hv.1 hv.2 hrun
        simp only [SimRel₀, AOutRel₀, absIDeclLFrom, hi2v] at hrec
        rw [hx]
        cases hor : o.1 with
        | Err e => rw [hor] at hrec; exact hrec
        | Ok r =>
          rw [hor] at hrec
          obtain ⟨w, lst2, hy, hw, hrel2, hinv2⟩ := hrec
          exact ⟨w, lst2, by rw [← hy]; rfl, hw, hrel2, hinv2⟩

/-- `check_decls_pure_go` ⊑ `checkDeclsPureGo` at the cursor. -/
theorem check_decls_pure_go_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_decls_pure_go pers st mode pins rf ds i = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkDeclsPureGo (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclLFrom ds i)) :=
  check_decls_pure_go_aux _ rfl hrel hinv hfe hfinv hrun

/-- **`check_decls_pure_refines` — DESIGN §8.2's sentence at the PURE fold.**
The Aeneas model of the Rust `check_decls_pure` accepting implies (B)'s
`checkDeclsPure` accepting with the abstracted state and the related
environment, over the whole outcome; the port's `Native` error claims nothing
(`AErrSim`'s own doing) and its three mirrored kinds are claimed to be the
twin's.

This is the fold the theorem is stated at (`Arena/Checker.lean`'s module
note): one step per record, install and check together. -/
theorem check_decls_pure_refines {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.check_decls_pure pers st mode pins ds = ok o) :
    SimRel₀ (fun r v => IFEnvRel r v) pers lst o
      (checkDeclsPure (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absIDeclL ds)) := by
  rw [arena.checker.check_decls_pure] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨f, hf, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hfe, hfinv⟩ := mk_ifenv_empty_refines he hf
  have h := (check_decls_pure_go_refines hrel hinv hfe hfinv hrun).mono
    (fun _ _ hr => hr.rel)
  rw [checkDeclsPure]
  simpa using h

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

open Lockstep in
@[lockstep] theorem annot_step_opaque_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup)
      (arena.checker.annot_step_opaque pers st mode pins rf pd cv value) lst
      (annotStepOpaqueSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd) (absIConstantVal cv) (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => annot_step_opaque_refines hrel hinv hfe.rel hfe.inv h

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

open Lockstep in
@[lockstep] theorem annot_step_thm_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup)
      (arena.checker.annot_step_thm pers st mode rf cv value) lst
      (annotStepThmSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => annot_step_thm_refines hrel hinv hfe.rel hfe.inv h

/-- `kernel::env::reducibility_hint_dup` is the identity in the model
(`Refine/CoreKGuards.lean`'s `reducibility_hint_dup_eq`, which this file does
not import). -/
private theorem reducibility_hint_dup_eq' {h1 r : kernel.env.ReducibilityHint}
    (h : kernel.env.reducibility_hint_dup h1 = ok r) : r = h1 := by
  cases h1 <;> simp only [kernel.env.reducibility_hint_dup, Result.ok.injEq] at h <;>
    exact h.symm

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

open Lockstep in
@[lockstep] theorem annot_step_defn_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    {hint : kernel.env.ReducibilityHint}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup)
      (arena.checker.annot_step_defn pers st mode pins rf pd cv value hint) lst
      (annotStepDefnSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd) (absIConstantVal cv) (absEIdx value)
        (ConRon.Refine.absHint hint)) :=
  LS.ofSimRel₀ fun _ h => annot_step_defn_refines hrel hinv hfe.rel hfe.inv h

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

open Lockstep in
@[lockstep] theorem annot_step_go_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup)
      (arena.checker.annot_step_go pers st mode pins rf pd) lst
      (annotStepGo (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd)) :=
  LS.ofSimRel₀ fun _ h => annot_step_go_refines hrel hinv hfe.rel hfe.inv h

/-- `annot_step_promote` — the bracket's promotion half at a step that
produced a `ValueGroup`: the seam promoted beside the environment and at the
SAME memo, so that the sharing between a header's type and its value survives
the copy — **and the tier dropped**.

**Restated by task #97-P5-Checker round 4: the old statement was false.**  The
Rust `annot_step_promote` ends in `drop_scratch` (`checker.rs:963`); the old
twin side stopped at the promotion, so its post-states disagreed on
`scratchOn` and `AStateRel₀` failed at every success.  Putting `dropScratch` in
the twin makes the post-states agree.  Since task #97-T2-LOCKSTEP it is a
plain lockstep statement at the state it is called at (the old `lst0`/`BrOK`/
`Ext` boundary binders are gone with `Ext`), and its proof is one `lockstep`
call: `promote_vg ; promote_new ; drop_scratch ; push`.  `hk` is finding C's
bound, at the counter. -/
theorem annot_step_promote_refines {pers st lst} {rf lf}
    {i vis k : Std.U64} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {vg : arena.checker_split.ValueGroup} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hk : k.val ≤ rf.visible_below.val)
    (hrun : arena.checker.annot_step_promote pers st i vis k rf pend vg = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = (absPendingCheckL r.2).toArray)
      pers lst o
      (do
        let (m, vg) ← promoteVG PMemo.empty coreWalkFuel (absValueGroup vg)
        let (_, fe) ← promoteNew m coreWalkFuel (absU k) lf
        dropScratch
        pure (fe, (absPendingCheckL pend).toArray.push ⟨vg, absU i, absU vis⟩)
        : AM (IFEnv × Array PendingCheck)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step_promote]
  lockstep

open Lockstep in
@[lockstep] theorem annot_step_promote_ls {pers st lst}
    {rf lf}
    {i vis k : Std.U64}
    {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {vg : arena.checker_split.ValueGroup}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hk : k.val ≤ rf.visible_below.val) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = (absPendingCheckL r.2).toArray)
      (arena.checker.annot_step_promote pers st i vis k rf pend vg) lst
      (do
        let (m, vg) ← promoteVG PMemo.empty coreWalkFuel (absValueGroup vg)
        let (_, fe) ← promoteNew m coreWalkFuel (absU k) lf
        dropScratch
        pure (fe, (absPendingCheckL pend).toArray.push ⟨vg, absU i, absU vis⟩)
        : AM (IFEnv × Array PendingCheck)) :=
  LS.ofSimRel₀ fun _ h => annot_step_promote_refines hrel hinv hfe.rel hfe.inv hk h

/-- **`annot_step` ⊑ `annotStep`** — phase A's step, bracketed:
`flushCaches; enterScratch; <the step>; promote; dropScratch`.  The twin's
`pend` is an `Array` and the port's a `Vec`, and both PUSH, so the abstraction
appends. -/
theorem annot_step_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.U64}
    {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step pers st mode pins i rf pend pd = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = (absPendingCheckL r.2).toArray)
      pers lst o
      (annotStep (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) (absU i) lf
        (absPendingCheckL pend).toArray (absIDeclaration pd)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker.annot_step, annotStep]
  lockstep

open Lockstep in
@[lockstep] theorem annot_step_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {i : Std.U64}
    {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {pd : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = (absPendingCheckL r.2).toArray)
      (arena.checker.annot_step pers st mode pins i rf pend pd) lst
      (annotStep (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) (absU i) lf
        (absPendingCheckL pend).toArray (absIDeclaration pd)) :=
  LS.ofSimRel₀ fun _ h => annot_step_refines hrel hinv hfe.rel hfe.inv h

/-- **`annot_decl_step` ⊑ `annotDeclStep`** — phase A's step with the position
carried and the error tagged (finding 13's `SimFold`). -/
theorem annot_decl_step_refines {pers st lst} {lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {p : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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
    hrel hinv hfe hfinv hq
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
      AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRel p.2.1 lf → IFEnvInv p.2.1 →
      arena.checker.annot_fold pers st mode pins p ds i = ok o →
      SimFold (fun r v => v.1 = absU r.1 ∧ IFEnvRelI r.2.1 v.2.1 ∧
          v.2.2 = (absPendingCheckL r.2.2).toArray) pers lst o
        (annotFold (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
          (absU p.1, lf, (absPendingCheckL p.2.2).toArray) (absIDeclLFrom ds i)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st lst lf mode pins p ds i o hn hrel hinv hfe hfinv hrun
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
        hrel hinv hfe hfinv hq
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
          (lf := v2) rfl hrel1 hinv1 hv2.1 hv2.2 hrun
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
    (hfe : IFEnvRel p.2.1 lf) (hfinv : IFEnvInv p.2.1)
    (hrun : arena.checker.annot_fold pers st mode pins p ds i = ok o) :
    SimFold (fun r v => v.1 = absU r.1 ∧ IFEnvRelI r.2.1 v.2.1 ∧
        v.2.2 = (absPendingCheckL r.2.2).toArray) pers lst o
      (annotFold (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absU p.1, lf, (absPendingCheckL p.2.2).toArray) (absIDeclLFrom ds i)) :=
  annot_fold_aux _ rfl hrel hinv hfe hfinv hrun

/-! ## Phase B: the check walk -/

/-- **`check_pending` ⊑ `checkPending`** — phase B's check of one record,
against the prefix view `fe.restrictTo pc.vis`, from a fresh memo state, and
**inside the scratch tier**: `enterScratch; checkValueGroup; dropScratch`.
Nothing crosses back, so there is nothing to promote — which is what made
phase B the easy half. -/
theorem check_pending_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {pc : arena.checker.PendingCheck} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_pending pers st mode rf pc = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkPending (ConRon.Refine.absMode mode) lf (absPendingCheck pc)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker.check_pending, checkPending]
  lockstep

open Lockstep in
@[lockstep] theorem check_pending_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pc : arena.checker.PendingCheck}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker.check_pending pers st mode rf pc) lst
      (checkPending (ConRon.Refine.absMode mode) lf (absPendingCheck pc)) :=
  LS.ofSim₀ fun _ h => check_pending_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_pending_list` ⊑ `checkPendingList`** at the cursor — every record
checked from a fresh memo state, a failure tagged with the record's fold
position (finding 13's `SimFold`). -/
private theorem check_pending_list_aux (n : Nat) :
    ∀ {pers st lst rf lf} {mode : kernel.env.CheckMode}
      {pend : alloc.vec.Vec arena.checker.PendingCheck} {i : Std.Usize} {o},
      pend.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRel rf lf → IFEnvInv rf →
      arena.checker.check_pending_list pers st mode rf pend i = ok o →
      SimFold (fun _ : Unit => fun _ : Unit => True) pers lst o
        (checkPendingList (ConRon.Refine.absMode mode) lf
          (absPendingCheckLFrom pend i)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st lst rf lf mode pend i o hn hrel hinv hfe hfinv hrun
    rw [arena.checker.check_pending_list.eq_def] at hrun
    dsimp only at hrun
    split at hrun
    · rename_i hge
      have hlen : pend.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val pend; scalar_tac
      have ho := Result.ok_injective hrun
      subst ho
      simp only [absPendingCheckLFrom, List.drop_eq_nil_of_le hlen, List.map_nil,
        checkPendingList, SimFold]
      exact ⟨(), lst, rfl, trivial, hrel, hinv⟩
    · rename_i hge
      have hlt : i.val < pend.val.length := by
        have := alloc.vec.Vec.len_val pend; scalar_tac
      obtain ⟨pc, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hpc : pend.val[i.val] = pc := by
        have hg := ConRon.Refine.ExprOps.vec_index_getElem? hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hP := check_pending_refines (lf := lf) (pc := pc) hrel hinv hfe
        hfinv hq
      obtain ⟨qr, qst⟩ := q
      simp only [Sim₀, AOut₀, StateT.run] at hP
      simp only [absPendingCheckLFrom, List.drop_eq_getElem_cons hlt, hpc,
        List.map_cons, SimFold, StateT.run, checkPendingList]
      cases hqr : qr with
      | Err e =>
        rw [hqr] at hP hrun
        have ho := Result.ok_injective hrun
        subst ho
        intro k hk
        obtain ⟨le, hle, hlk⟩ := hP k hk
        exact ⟨le, AState.abandoned, by rw [hle]; try rfl, hlk⟩
      | Ok _ =>
        rw [hqr] at hP hrun
        obtain ⟨lst1, hx, hrel1, hinv1⟩ := hP
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (pend.val.length - i2.val) (by omega) (i := i2) (lf := lf)
          rfl hrel1 hinv1 hfe hfinv hrun
        simp only [SimFold, StateT.run, absPendingCheckLFrom, hi2v] at hrec
        cases hor : o.1 with
        | Err pr =>
          rw [hor] at hrec
          intro k hk
          obtain ⟨le, lst2, hy, hlk⟩ := hrec k hk
          exact ⟨le, lst2, by rw [hx]; exact hy, hlk⟩
        | Ok _ =>
          rw [hor] at hrec
          obtain ⟨w, lst2, hy, -, hrel2, hinv2⟩ := hrec
          exact ⟨w, lst2, by rw [hx]; exact hy, trivial, hrel2, hinv2⟩

/-- **`check_pending_list` ⊑ `checkPendingList`** at the cursor — every record
checked from a fresh memo state, a failure tagged with the record's fold
position (finding 13's `SimFold`). -/
theorem check_pending_list_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pend : alloc.vec.Vec arena.checker.PendingCheck} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_pending_list pers st mode rf pend i = ok o) :
    SimFold (fun _ : Unit => fun _ : Unit => True) pers lst o
      (checkPendingList (ConRon.Refine.absMode mode) lf
        (absPendingCheckLFrom pend i)) :=
  check_pending_list_aux _ rfl hrel hinv hfe hfinv hrun

/-! ## The capstone -/

/-- **`install_then_check_refines` — DESIGN §8.2's sentence at the fold the
binary runs.**

*The Aeneas model of the Rust `install_then_check` accepting implies (B)'s
`installThenCheck` accepting with the abstracted state and the related
environment, over the whole outcome; the port's `Native` error claims nothing.*

The error arm carries the fold POSITION (finding 13) and claims the twin
throws at the same kind AND at the same position.  Nothing is claimed about
the state there, by both sides' own design.

**Its exact hypotheses**, and they are the tier's whole ledger:

* `AStateRel₀ pers st lst` / `AStateInv pers st` — the state, related and
  well-formed on the Rust side;
and nothing else (the old `BrOK` and ruling 2's `DeclResolves` are gone with
task #97-T2-LOCKSTEP).  `KnotRel checkFuel` and `IndRel` were the other two until
task #97-P5-Checker-2; both are theorems now (`knotRel_checkFuel'`,
`ind_rel`) and the binders are gone.  The driver's fold above this is unverified and calls this
per record; `scripts/holes.sh` is where that boundary is recorded. -/
theorem install_then_check_refines {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.install_then_check pers st mode pins ds = ok o) :
    SimFold (fun r v => IFEnvRel r v) pers lst o
      (installThenCheck (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absIDeclL ds).toArray) := by
  rw [arena.checker.install_then_check] at hrun
  obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨f, hf, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hfe, hfinv⟩ := mk_ifenv_empty_refines he hf
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hA := annot_fold_refines
    (p := (0#u64, f, alloc.vec.Vec.new arena.checker.PendingCheck))
    (lf := mkIFEnv IEnv.empty) (i := 0#usize) hrel hinv hfe hfinv hq
  simp only [SimFold, absIDeclLFrom_zero, absPendingCheckL_new_toArray, absU_zero] at hA
  obtain ⟨qr, qst⟩ := q
  simp only [SimFold] at hA ⊢
  simp only [installThenCheck, am_run_bind, toList_toArray']
  cases hqr : qr with
  | Err pr =>
    rw [hqr] at hA hrun
    have ho := Result.ok_injective hrun
    subst ho
    intro k hk
    obtain ⟨le, lst', hx, hlk⟩ := hA k hk
    exact ⟨le, lst', by rw [hx]; rfl, hlk⟩
  | Ok p' =>
    rw [hqr] at hA hrun
    obtain ⟨v, lst', hx, hR, hrel1, hinv1⟩ := hA
    obtain ⟨n1, fe1, pend1⟩ := v
    obtain ⟨p1, f1, pd1⟩ := p'
    obtain ⟨hv1, hv2, hv3⟩ := hR
    subst hv3
    obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hB := check_pending_list_refines (lf := fe1)
      (pend := pd1) (i := 0#usize) hrel1 hinv1 hv2.rel hv2.inv hq2
    simp only [SimFold, absPendingCheckLFrom_zero] at hB
    obtain ⟨q2r, q2st⟩ := q2
    rw [hx]
    simp only [toList_toArray']
    cases hq2r : q2r with
    | Err pr =>
      rw [hq2r] at hB hrun
      have ho := Result.ok_injective hrun
      subst ho
      intro k hk
      obtain ⟨le, lst2, hy, hlk⟩ := hB k hk
      refine ⟨le, lst2, ?_, hlk⟩
      simp only [except_ok_bind, toList_toArray', am_run_bind, hy]
      try rfl
    | Ok _ =>
      rw [hq2r] at hB hrun
      obtain ⟨_, lst2, hy, -, hrel2, hinv2⟩ := hB
      have ho := Result.ok_injective hrun
      subst ho
      refine ⟨fe1, lst2, ?_, hv2.rel, hrel2, hinv2⟩
      simp only [except_ok_bind, toList_toArray', am_run_bind, hy]
      try rfl

/-! ## The error tag and the startup walk -/

/-- `cp_append` is `String.append` on code points. -/
theorem cp_append_refines {out s : alloc.vec.Vec Std.U32} {i : Std.Usize} {o}
    (hwf : ConRon.Refine.StrWF out) (hwf2 : ConRon.Refine.StrWF s)
    (hrun : arena.checker.cp_append out s i = ok o) :
    ConRon.Refine.absString o = ConRon.Refine.absString out ++
      String.ofList ((s.val.drop i.val).map fun c => Char.ofNat c.val) := by
  sorry

/-- `at_decl_text` renders the position into the message. -/
theorem at_decl_text_refines {w : alloc.vec.Vec Std.U32} {n : Std.U64} {o}
    (hwf : ConRon.Refine.StrWF w)
    (hrun : arena.checker.at_decl_text w n = ok o) :
    ConRon.Refine.absString o =
      s!"{ConRon.Refine.absString w} (declaration {absU n})" := by
  sorry

/-- `at_decl` ⊑ `atDecl` — the fold's failure with its POSITION in the text.
The KIND is what the refinement claims; the message is never compared
(DESIGN §3.1). -/
theorem at_decl_refines {e : kernel.core_types.CheckError} {n : Std.U64} {o}
    (hrun : arena.checker.at_decl e n = ok o) :
    ∀ le, absAErrKind e = lAErrKind le →
      absAErrKind o = lAErrKind (atDecl le (absU n)) := by
  intro le hle
  rw [arena.checker.at_decl.eq_def] at hrun
  cases e <;> cases le <;> simp only [absAErrKind, lAErrKind] at hle ⊢ <;>
    first
      | (obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
         have h2 := Result.ok_injective hrun
         subst h2
         rfl)
      | simp at hle

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

/-- `all_basis_kinds` is the six basis kinds in `internAllPins`' order. -/
theorem all_basis_kinds_refines {o}
    (hrun : arena.checker.all_basis_kinds = ok o) :
    o.val.map ConRon.Refine.absBasisKind =
      [.eqK, .natK, .punitK, .emptyK, .falseK, .quotK] := by
  rw [arena.checker.all_basis_kinds] at hrun
  obtain ⟨k1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k2, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k3, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k5, h5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [ConRon.Refine.vec_push_val hrun, ConRon.Refine.vec_push_val h5,
    ConRon.Refine.vec_push_val h4, ConRon.Refine.vec_push_val h3,
    ConRon.Refine.vec_push_val h2, ConRon.Refine.vec_push_val h1,
    ConRon.Refine.ExprOps.with_capacity_val]
  rfl

/-- The cursor's measure induction behind `intern_all_basis_refines`. -/
private theorem intern_all_basis_aux {pers : arena.store.PersTier} (m : Nat) :
    ∀ {st lst} {i : Std.Usize} {o},
      6 - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st →
      arena.checker.intern_all_basis pers st i = ok o →
      Sim₀ (fun _ : Unit => ()) pers lst o
        (internAllBasisSpec
          ([ConLeche.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK,
            .quotK].drop i.val)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro st lst i o hm hrel hinv hrun
    rw [arena.checker.intern_all_basis.eq_def] at hrun
    dsimp only at hrun
    obtain ⟨ks, hks, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hk := all_basis_kinds_refines hks
    have hlen6 : ks.val.length = 6 := by
      have h := congrArg List.length hk
      simpa using h
    have hl := alloc.vec.Vec.len_val ks
    unfold Sim₀
    by_cases hge : i ≥ ks.len
    · have hle : 6 ≤ i.val := by scalar_tac
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
      have hrec := ih (6 - i2.val) (by omega) rfl hrel2 hinv2 hrun
      rw [← hk, ← List.map_drop, hi2v] at hrec
      exact hrec

/-- `intern_all_basis` — the six basis blocks in BOTH forms, at the cursor. -/
theorem intern_all_basis_refines {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_basis pers st i = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (internAllBasisSpec
        ([ConLeche.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK,
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

**The two capstones read `sorryAx`, and that is the honest row.**  Their
proofs are complete — `install_then_check_refines` is `annot_fold_refines`
and `check_pending_list_refines` composed, `check_decls_pure_refines` is
`check_decls_pure_go_refines` at the empty environment — and what the
`sorryAx` stands for is the three LEAVES the fold stands on:
`annot_step_refines`, `check_pending_refines` and `check_decl_step_refines`.
Task #97-P5-Checker-2's section lists them.  Writing the rows out is what
keeps *"the spine is closed and its leaves are not"* visible. -/

/-- info: 'ConRon.Refine2.install_then_check_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms install_then_check_refines

/-- info: 'ConRon.Refine2.check_decls_pure_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_decls_pure_refines

/-! **Task #97-P5-Checker round 4, task #97-P5-Top.**  The two bracketed
leaves are compositions and read `sorryAx` through their
BODIES (`check_decl_refines`, `annot_step_go_refines`'s arms) and nothing
else. -/

/-- info: 'ConRon.Refine2.check_decl_step_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_decl_step_refines

/-- info: 'ConRon.Refine2.annot_step_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annot_step_refines

/-- info: 'ConRon.Refine2.at_decl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms at_decl_refines

/-- info: 'ConRon.Refine2.all_basis_kinds_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all_basis_kinds_refines

end ConRon.Refine2
