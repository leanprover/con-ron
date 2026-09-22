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
`AErrSim` on a throw) nor `SimRel`: it is **`SimFold`** below, whose error arm
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
Inductives tier instead.  A capstone with no hypotheses must transitively
import every tier that discharges one.

`KnotRel checkFuel` went the same way and needed nothing:
`Refine2/Checker/KnotHyp.lean`'s `knotRel_checkFuel'` is a theorem of task
#97-P5-Arms, so the sixty-two binders that carried it were carrying a
redundant hypothesis.

## What this file's capstone still owes

**Nothing but its own leaves.**  `install_then_check_refines` and
`check_decls_pure_refines` take `AStateRel` and `AStateInv` and no more, and
their proofs are complete: the spine is `annot_fold_refines` /
`annot_decl_step_refines` / `check_pending_list_refines` /
`check_decls_pure_go_refines`, all closed here, and the three `sorry`s under
them are `annot_step_refines`, `check_pending_refines` and
`check_decl_step_refines` — each of which is the per-declaration BRACKET and
waits on `arena::core::{flush_caches, enter_scratch, drop_scratch}`, which the
Core tier has not stated.  The axiom census at the foot of this file prints
that, rather than hiding it.
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
`Except (CheckError × Nat)` as its VALUE.  The success arm is `SimRel`'s; the
error arm compares the kind and the position and claims nothing about the
state (both sides abandon it). -/
def SimFold {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64) ×
      arena.monad.AState)
    (x : AM (Except (Arena.CheckError × Nat) β)) : Prop :=
  match o.1 with
  | .Ok r => ∃ v lst', x.run lst = .ok (.ok v, lst') ∧ R r v ∧
      AStateRel pers o.2 lst' ∧ AStateInv pers o.2 ∧ Ext lst.store lst'.store
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
  refine ⟨⟨rfl, ?_, rfl⟩, hinv0, by simp, ?_⟩
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
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_basis_decl_install pers st rf kind = ok o) :
    SimRel IFEnvRelI pers lst o
      (do installBasisDecls lf (← BasisKind.declsA (ConRon.Refine.absBasisKind kind))) := by
  sorry

/-- **`check_basis_decl` ⊑ `checkBasisDecl`** — the quotient block's types
mention the pinned equality former, which is why it requires the `Eq` basis
first. -/
theorem check_basis_decl_refines {pers st lst} {rf lf}
    {kind : kernel.env.BasisKind} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_basis_decl pers st rf kind = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkBasisDecl lf (ConRon.Refine.absBasisKind kind)) := by
  sorry

/-- `check_quot_decl` ⊑ `checkDecl`'s `.quotDecl` arm — the export writes the
quotient package as four records; each is compared with the pinned block's
constant at its own kind, and the FIRST that matches installs the pinned
block whole. -/
theorem check_quot_decl_refines {pers st lst} {rf lf}
    {k : kernel.env.QuotKind} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_quot_decl pers st rf k cv = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkQuotDeclSpec lf (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  sorry

/-- `check_ind_decl` ⊑ `checkDecl`'s `.indDecl` arm — the pinned basis blocks
recognised first (a stream's `Nat` block arrives as an ordinary `indDecl`),
then the inductive routes.  **Finding 14's `hind`.** -/
theorem check_ind_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {n_p : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_ind_decl pers st mode rf block n_p = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkIndDeclArmSpec (ConRon.Refine.absMode mode) lf (absICIL block)
        (absU n_p)) := by
  sorry

/-! ## The axiom arm, in five -/

/-- `check_axiom_decl_rest` — the three remaining name tests: the two standard
axioms' shape mismatch, `sorryAx` tolerated as a DECLARATION, and everything
else declined. -/
theorem check_axiom_decl_rest_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_rest st rf cv_a = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkAxiomDeclRestSpec lf (absIConstantVal cv_a)) := by
  sorry

/-- `check_axiom_decl_of_reduce` — the `ofReduce*` arm. -/
theorem check_axiom_decl_of_reduce_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_of_reduce pers st rf cv_a = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkAxiomDeclOfReduceSpec lf (absIConstantVal cv_a)) := by
  sorry

/-- `check_axiom_decl_trust` — the `Lean.trustCompiler` arm. -/
theorem check_axiom_decl_trust_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_trust pers st rf cv_a = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkAxiomDeclTrustSpec lf (absIConstantVal cv_a)) := by
  sorry

/-- `check_axiom_decl_std` — the axiom arm past `Quot.sound`: the common
constant check, then the standard-axiom gate. -/
theorem check_axiom_decl_std_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl_std pers st mode rf cv = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkAxiomDeclStdSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv)) := by
  sorry

/-- `check_quot_sound_record` — **`Quot.sound` is the pinned quotient BLOCK's
own record**: the export writes it as an ordinary axiom record beside the four
`#QUOT` ones, so it arrives at the axiom arm, is compared with the pin,
installs NOTHING of its own, and DECLINES when it does not match. -/
theorem check_quot_sound_record_refines {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_quot_sound_record pers st rf cv = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkQuotSoundRecordSpec lf (absIConstantVal cv)) := by
  sorry

/-- **`check_axiom_decl` ⊑ `checkDecl`'s `.axiomDecl` arm**. -/
theorem check_axiom_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_axiom_decl pers st mode rf cv = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkAxiomDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  sorry

/-! ## The three value arms -/

/-- `check_opaque_reduce_pin` — the compiler-trust opaques' install gate,
after the ordinary opaque check.  `k_pre` is the visibility counter the check
ran at, which the twin carries as a second environment. -/
theorem check_opaque_reduce_pin_refines {pers st lst} {rf2 lf2 lf}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hkpre : lf = lf2.restrictTo (absU k_pre))
    (hrun : arena.checker.check_opaque_reduce_pin pers st mode rf2 k_pre n value
      = ok o) :
    SimRel IFEnvRelI pers lst o
      (do checkReducePin (ConRon.Refine.absMode mode) lf lf2 (absNIdx n)
            (absEIdx value)
          pure lf2) := by
  sorry

/-- **`check_opaque_decl` ⊑ `checkDecl`'s `.opaqueDecl` arm**. -/
theorem check_opaque_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_opaque_decl pers st mode rf cv value = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkOpaqueDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  sorry

/-- **`check_thm_decl` ⊑ `checkDecl`'s `.thmDecl` arm**. -/
theorem check_thm_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_thm_decl pers st mode rf cv value = ok o) :
    SimRel IFEnvRelI pers lst o
      (do
        let cvA ← checkConstantVal (ConRon.Refine.absMode mode) lf
          (absIConstantVal cv)
        checkThmVal (ConRon.Refine.absMode mode) lf cvA (absEIdx value)) := by
  sorry

/-- `check_structural_nat_pin_certify` — the recurrence equations checked by
definitional equality, in the PRE-insertion environment with the operation's
self-references replaced by its stored value. -/
theorem check_structural_nat_pin_certify_refines {pers st lst} {rf2 lf2 lf}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64}
    {seqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hkpre : lf = lf2.restrictTo (absU k_pre))
    (hrun : arena.checker.check_structural_nat_pin_certify pers st mode rf2 k_pre
      seqs = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkStructuralNatPinCertifySpec (ConRon.Refine.absMode mode) lf lf2
        (absEqPairs seqs)) := by
  sorry

/-- `check_structural_nat_pin_eqs` — the operation's own equations, built. -/
theorem check_structural_nat_pin_eqs_refines {pers st lst} {rf2 lf2 lf}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hkpre : lf = lf2.restrictTo (absU k_pre))
    (hrun : arena.checker.check_structural_nat_pin_eqs pers st mode rf2 k_pre n
      = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkStructuralNatPinEqsSpec (ConRon.Refine.absMode mode) lf lf2
        (absNIdx n)) := by
  sorry

/-- `check_structural_nat_pin` — the fast-path ops must be the standard
structural recursions. -/
theorem check_structural_nat_pin_refines {pers st lst} {rf2 lf2 lf}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hkpre : lf = lf2.restrictTo (absU k_pre))
    (hrun : arena.checker.check_structural_nat_pin pers st mode rf2 k_pre n = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkStructuralNatPinSpec (ConRon.Refine.absMode mode) lf lf2
        (absNIdx n)) := by
  sorry

/-- `check_defn_div_mod_pin` — the `Nat.div`/`Nat.mod` gate at a definition. -/
theorem check_defn_div_mod_pin_refines {pers st lst} {rf2 lf2 lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hkpre : lf = lf2.restrictTo (absU k_pre))
    (hrun : arena.checker.check_defn_div_mod_pin pers st mode pins rf2 k_pre n
      = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkDefnDivModPinSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        lf lf2 (absNIdx n)) := by
  sorry

/-- `check_defn_pins` — both pin gates, in the twin's order. -/
theorem check_defn_pins_refines {pers st lst} {rf2 lf2 lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hkpre : lf = lf2.restrictTo (absU k_pre))
    (hrun : arena.checker.check_defn_pins pers st mode pins rf2 k_pre n = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkDefnPinsSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        lf lf2 (absNIdx n)) := by
  sorry

/-- **`check_defn_decl` ⊑ `checkDecl`'s `.defnDecl` arm**. -/
theorem check_defn_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {cv : arena.env.IConstantVal} {value : arena.handle.EIdx}
    {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_defn_decl pers st mode pins rf cv value hint = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkDefnDeclSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) := by
  sorry

/-! ## One declaration, and the pure fold -/

/-- **`check_decl` ⊑ `checkDecl`** — check a single declaration, extending the
environment on success.  Clause for clause; the `.indDecl` arm's route choice
is the Inductives seam (finding 14). -/
theorem check_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {d : arena.env.IDeclaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_decl pers st mode pins rf d = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) := by
  sorry

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
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_decl_step pers st mode pins rf d = ok o) :
    SimRel IFEnvRelI pers lst o
      (checkDeclStep (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) := by
  sorry

/-- The cursor's measure induction — task #97-P5-0's finding 7 shape step, at
a `Vec` rather than at a fuel: `ds.length - i` decreases and the arm's own
`i + 1` is what makes it do so. -/
private theorem check_decls_pure_go_aux (n : Nat) :
    ∀ {pers st lst rf lf} {mode : kernel.env.CheckMode}
      {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
      {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o},
      ds.val.length - i.val = n →
      AStateRel pers st lst → AStateInv pers st →
      IFEnvRel rf lf → IFEnvInv rf →
      arena.checker.check_decls_pure_go pers st mode pins rf ds i = ok o →
      SimRel IFEnvRelI pers lst o
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
        checkDeclsPureGo, SimRel, AOutRel]
      exact AOutRel.ok rfl ⟨hfe, hfinv⟩ hrel hinv (Ext.refl _)
    · rename_i hge
      have hlt : i.val < ds.val.length := by
        have := alloc.vec.Vec.len_val ds; scalar_tac
      obtain ⟨d, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hd : ds.val[i.val] = d := by
        have hg := ConRon.Refine.ExprOps.vec_index_getElem? hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hS := check_decl_step_refines (lf := lf) (d := d) hrel hinv hfe hfinv hq
      obtain ⟨qr, qst⟩ := q
      simp only [SimRel, AOutRel] at hS ⊢
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
        obtain ⟨v, lst1, hx, hv, hrel1, hinv1, hext1⟩ := hS
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (ds.val.length - i2.val) (by omega) (i := i2) (lf := v)
          rfl hrel1 hinv1 hv.1 hv.2 hrun
        simp only [SimRel, AOutRel, absIDeclLFrom, hi2v] at hrec
        rw [hx]
        cases hor : o.1 with
        | Err e => rw [hor] at hrec; exact hrec
        | Ok r =>
          rw [hor] at hrec
          obtain ⟨w, lst2, hy, hw, hrel2, hinv2, hext2⟩ := hrec
          exact ⟨w, lst2, by rw [← hy]; rfl, hw, hrel2, hinv2, Ext.trans hext1 hext2⟩

/-- `check_decls_pure_go` ⊑ `checkDeclsPureGo` at the cursor. -/
theorem check_decls_pure_go_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_decls_pure_go pers st mode pins rf ds i = ok o) :
    SimRel IFEnvRelI pers lst o
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
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.check_decls_pure pers st mode pins ds = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
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
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_other pers st mode pins rf pd = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (do pure (← checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd), none)) := by
  sorry

/-- `annot_step_opaque_install` — the opaque's install half. -/
theorem annot_step_opaque_install_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_opaque_install pers st mode rf cv value = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepOpaqueInstallSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value)) := by
  sorry

/-- `annot_step_opaque` — `annotStepGo`'s `.opaqueDecl` arm. -/
theorem annot_step_opaque_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_opaque pers st mode pins rf pd cv value = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepOpaqueSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd) (absIConstantVal cv) (absEIdx value)) := by
  sorry

/-- `annot_step_thm` — `annotStepGo`'s `.thmDecl` arm: **a theorem installs BY
STATEMENT**, so phase A never enters a theorem's body. -/
theorem annot_step_thm_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_thm pers st mode rf cv value = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepThmSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  sorry

/-- `annot_step_defn_install` — the definition's install half. -/
theorem annot_step_defn_install_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_defn_install pers st mode rf cv value hint
      = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepDefnInstallSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) := by
  sorry

/-- `annot_step_defn` — `annotStepGo`'s `.defnDecl` arm. -/
theorem annot_step_defn_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_defn pers st mode pins rf pd cv value hint
      = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepDefnSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd) (absIConstantVal cv) (absEIdx value)
        (ConRon.Refine.absHint hint)) := by
  sorry

/-- **`annot_step_go` ⊑ `annotStepGo`** — phase A's step BODY: what a step
LEAVES BEHIND. -/
theorem annot_step_go_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step_go pers st mode pins rf pd = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = r.2.map absValueGroup) pers lst o
      (annotStepGo (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration pd)) := by
  sorry

/-- `annot_step_promote` — the bracket's promotion half at a step that
produced a `ValueGroup`: the seam promoted beside the environment and at the
SAME memo, so that the sharing between a header's type and its value survives
the copy. -/
theorem annot_step_promote_refines {pers st lst} {rf lf}
    {i vis k : Std.U64} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {vg : arena.checker_split.ValueGroup} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hk : absU k ≤ rf.env.consts.val.length)
    (hrun : arena.checker.annot_step_promote pers st i vis k rf pend vg = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = absPendingCheckL r.2) pers lst o
      (do
        let (m, vg) ← promoteVG PMemo.empty coreWalkFuel (absValueGroup vg)
        let (_, fe) ← promoteNew m coreWalkFuel (absU k) lf
        pure (fe, absPendingCheckL pend ++ [⟨vg, absU i, absU vis⟩])) := by
  sorry

/-- **`annot_step` ⊑ `annotStep`** — phase A's step, bracketed:
`flushCaches; enterScratch; <the step>; promote; dropScratch`.  The twin's
`pend` is an `Array` and the port's a `Vec`, and both PUSH, so the abstraction
appends. -/
theorem annot_step_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.U64}
    {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.annot_step pers st mode pins i rf pend pd = ok o) :
    SimRel (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = (absPendingCheckL r.2).toArray)
      pers lst o
      (annotStep (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) (absU i) lf
        (absPendingCheckL pend).toArray (absIDeclaration pd)) := by
  sorry

/-- **`annot_decl_step` ⊑ `annotDeclStep`** — phase A's step with the position
carried and the error tagged (finding 13's `SimFold`). -/
theorem annot_decl_step_refines {pers st lst} {lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {p : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck}
    {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
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
  simp only [SimRel, AOutRel, StateT.run] at hA
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
    obtain ⟨v, lst1, hx, hv, hrel1, hinv1, hext1⟩ := hA
    obtain ⟨qf, qpend⟩ := q'
    obtain ⟨v1, v2⟩ := v
    obtain ⟨hv1, hv2⟩ := hv
    subst hv2
    obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hi2v : i2.val = pi.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have ho := Result.ok_injective hrun
    subst ho
    exact ⟨(absU pi + 1, v1, (absPendingCheckL qpend).toArray), lst1,
      by rw [hx], ⟨by simp [hi2v], hv1, rfl⟩, hrel1, hinv1, hext1⟩

/-- Phase A's fold, by the cursor's measure — `check_decls_pure_go_aux`'s
shape at the other fold. -/
private theorem annot_fold_aux (n : Nat) :
    ∀ {pers st lst lf} {mode : kernel.env.CheckMode}
      {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
      {p : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck}
      {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o},
      ds.val.length - i.val = n →
      AStateRel pers st lst → AStateInv pers st →
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
        ⟨rfl, ⟨hfe, hfinv⟩, rfl⟩, hrel, hinv, Ext.refl _⟩
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
        obtain ⟨v, lst1, hx, hv, hrel1, hinv1, hext1⟩ := hA
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
          obtain ⟨w, lst2, hy, hw, hrel2, hinv2, hext2⟩ := hrec
          exact ⟨w, lst2, by rw [← hy]; rfl, hw, hrel2, hinv2, Ext.trans hext1 hext2⟩

/-- **`annot_fold` ⊑ `annotFold`** at the cursor. -/
theorem annot_fold_refines {pers st lst} {lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {p : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
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
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker.check_pending pers st mode rf pc = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkPending (ConRon.Refine.absMode mode) lf (absPendingCheck pc)) := by
  sorry

/-- **`check_pending_list` ⊑ `checkPendingList`** at the cursor — every record
checked from a fresh memo state, a failure tagged with the record's fold
position (finding 13's `SimFold`). -/
private theorem check_pending_list_aux (n : Nat) :
    ∀ {pers st lst rf lf} {mode : kernel.env.CheckMode}
      {pend : alloc.vec.Vec arena.checker.PendingCheck} {i : Std.Usize} {o},
      pend.val.length - i.val = n →
      AStateRel pers st lst → AStateInv pers st →
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
      exact ⟨(), lst, rfl, trivial, hrel, hinv, Ext.refl _⟩
    · rename_i hge
      have hlt : i.val < pend.val.length := by
        have := alloc.vec.Vec.len_val pend; scalar_tac
      obtain ⟨pc, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hpc : pend.val[i.val] = pc := by
        have hg := ConRon.Refine.ExprOps.vec_index_getElem? hidx
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hP := check_pending_refines (lf := lf) (pc := pc) hrel hinv hfe hfinv hq
      obtain ⟨qr, qst⟩ := q
      simp only [Sim, AOut, StateT.run] at hP
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
        obtain ⟨lst1, hx, hrel1, hinv1, hext1, -⟩ := hP
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
          obtain ⟨w, lst2, hy, -, hrel2, hinv2, hext2⟩ := hrec
          exact ⟨w, lst2, by rw [hx]; exact hy, trivial, hrel2, hinv2,
            Ext.trans hext1 hext2⟩

/-- **`check_pending_list` ⊑ `checkPendingList`** at the cursor — every record
checked from a fresh memo state, a failure tagged with the record's fold
position (finding 13's `SimFold`). -/
theorem check_pending_list_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pend : alloc.vec.Vec arena.checker.PendingCheck} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
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

* `AStateRel pers st lst` / `AStateInv pers st` — the state, related and
  well-formed on the Rust side;

and nothing else.  `KnotRel checkFuel` and `IndRel` were the other two until
task #97-P5-Checker-2; both are theorems now (`knotRel_checkFuel'`,
`ind_rel`) and the binders are gone.  The driver's fold above this is unverified and calls this
per record; `scripts/holes.sh` is where that boundary is recorded. -/
theorem install_then_check_refines {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
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
    obtain ⟨v, lst', hx, hR, hrel1, hinv1, hext1⟩ := hA
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
      obtain ⟨_, lst2, hy, -, hrel2, hinv2, hext2⟩ := hB
      have ho := Result.ok_injective hrun
      subst ho
      refine ⟨fe1, lst2, ?_, hv2.rel, hrel2, hinv2, Ext.trans hext1 hext2⟩
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

/-- `intern_all_names` — the reserved names the guards compare by handle. -/
theorem intern_all_names_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_names st = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o internAllNamesSpec := by
  sorry

/-- `intern_all_reduce_pins` — the two reduce pins. -/
theorem intern_all_reduce_pins_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_reduce_pins pers st = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      internAllReducePinsSpec := by
  sorry

/-- `intern_all_trust_pins` — the compiler-trust axiom pins. -/
theorem intern_all_trust_pins_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_trust_pins pers st = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      internAllTrustPinsSpec := by
  sorry

/-- `intern_all_axiom_pins_rest` — the standard axiom pins past the `Iff`
family. -/
theorem intern_all_axiom_pins_rest_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_axiom_pins_rest pers st = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      internAllAxiomPinsRestSpec := by
  sorry

/-- `intern_all_axiom_pins` — the standard axiom pins. -/
theorem intern_all_axiom_pins_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_axiom_pins pers st = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      internAllAxiomPinsSpec := by
  sorry

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

/-- `intern_all_basis` — the six basis blocks in BOTH forms, at the cursor. -/
theorem intern_all_basis_refines {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_basis pers st i = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (internAllBasisSpec
        ([ConLeche.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK,
          .quotK].drop i.val)) := by
  sorry

/-- **`intern_all_pins` ⊑ `internAllPins`** — DESIGN §8.6 P2d's one-time tree
walk: every datum the checker compares a stream record against, interned into
the tier that is live at the call — which, at the driver's call, is the
PERSISTENT one, and that is what makes every pin handle survive every
`dropScratch` (`Arena/Intern.lean`'s module note). -/
theorem intern_all_pins_refines {pers st lst}
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pins.val, NatOpPinSetWF p)
    (hrun : arena.checker.intern_all_pins pers st pins = ok o) :
    Sim absINatOpPinSetL (fun _ => True) pers lst o
      (internAllPins (ConRon.Refine.absPins pins)) := by
  sorry


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

/-- info: 'ConRon.Refine2.at_decl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms at_decl_refines

/-- info: 'ConRon.Refine2.all_basis_kinds_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all_basis_kinds_refines

end ConRon.Refine2
