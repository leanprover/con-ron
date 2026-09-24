/-
# `ConRon.Refine2.Checker.DeclCheck` — Theorem 2 for `arena::decl_check`

**Task #97-P5-Checker**, deliverable 2's largest file (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/decl_check.rs` (3 005 lines, ninety-five
`pub fn`s) against `proof/ConRon/Arena/DeclCheck.lean` (659 lines,
thirty-three `def`s): the three value kinds' checks, the standard- and
compiler-trust axiom gates, the `Nat.div`/`Nat.mod` pin certification with its
variant attempt, and the basis installs.

## Finding 11 — the Rust is 2.9× the twin's granularity here, and `CertCtx` is why

Ninety-five against thirty-three.  Two thirds of the difference is one
function: `divModCertStmts`, a hundred-line `do` block over twenty-one pinned
handles, which DESIGN §3.4's rules split into **twenty-three** Rust functions
plus a record, `CertCtx`, to carry the handles between them (a `let`-bound
handle that outlives a `match` arm is a loan the Aeneas subset will not take).

`CertCtx` has NO twin and needs none: it is a bundle of twenty-one handles the
twin holds in `let`s.  So this file states the `cert_*` family **against the
twin's own sub-expressions inline** — `eqAt1 boolTy (← natAp2 bleN a b) r` for
`cert_guard`, `eqAt1 natTy (← natAp2 c x y) rhs` for `cert_eq`, and so on —
with the context's fields abstracted one at a time.  There is no
`absCertCtx`, because there is nothing to abstract it TO; the correspondence
is twenty-one field equations, and each `cert_*` statement carries the ones it
reads.  That is the same decision task #97-P5-0's finding 6 (smaller half)
made for `wscopedBGo_node`, at a record instead of a view.

## Finding 12 — `defn_value` is a reader the twin does not have

`decl_check::defn_value(vis, fe, c) -> Option<EIdx>` is `fe.find? c` matched
for `.defnInfo`, lifted out of three call sites so the borrow of `fe` is dead
before the checker recurses.  The twin writes the match inline each time.  It
is PURE on the Rust side (no state at all), which makes it the one function of
the tier whose statement is a bare equation between two `Option`s.

## What these lemmas wait on

Everything `Refine2/Checker/Base.lean` waits on, plus `Refine2/Checker/Pins.lean`'s
`pin_*` readers (which are the cheapest group of the tier and close on
`PinsRel.names` alone) and `arena::core`'s `natAp1` / `natAp2` / `constE` /
`substConst0` / `substConstAll`, which belong to P5-Core.
-/
import ConRon.Refine2.Checker.Base
import ConRon.Refine2.Inductives.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- **`arena::decl_check::CertCtx` as the twin's twenty-one `let`s**
(`Refine2/Checker/Spec.lean`'s `CertCtxA`).  It is the one record of the tier
with no twin of its own — finding 11. -/
def absCertCtx (cx : arena.decl_check.CertCtx) : CertCtxA :=
  ⟨absEIdx cx.nat_ty, absEIdx cx.x, absEIdx cx.y, absEIdx cx.one,
    absNIdx cx.ble_n, absEIdx cx.bool_ty, absEIdx cx.b_t, absEIdx cx.b_f,
    absEIdx cx.z, absEIdx cx.two, absNIdx cx.mod_n, absNIdx cx.div_n,
    absNIdx cx.add_n, absNIdx cx.mul_n, absNIdx cx.sub_n, absNIdx cx.gcd_n,
    absNIdx cx.sl_n, absNIdx cx.sr_n, absNIdx cx.land_n, absNIdx cx.lor_n,
    absNIdx cx.xor_n⟩

/-! ## Rust-only steps this file's zips meet (task #97-T2-LOCKSTEP lane Checker DeclCheck) -/

open Lockstep in
/-- `arena::env::eidx_vec_dup` is the identity on the value. -/
@[lockstep] theorem eidx_vec_dup_spec (es : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.env.eidx_vec_dup es) (fun r => absEIdxL r = absEIdxL es) :=
  fun _ h => by simp only [absEIdxL, eidx_vec_dup_val h]

open Lockstep in
/-- `arena::canon::i_constant_info_beq` is the twin's `==` (at `some`, the
shape `reduceElemOk` compares at), at canonical Rust data (`IConstantInfoWF`:
the `IndInfo` arm compares `sort_z` by representation; task #97-T2-LOCKSTEP
lane Inductives Modeled slice 2). -/
@[lockstep] theorem i_constant_info_beq_spec {a b : arena.env.IConstantInfo}
    (ha : IConstantInfoWF a) (hb : IConstantInfoWF b) :
    LSP (arena.canon.i_constant_info_beq a b)
      (fun o => o = (some (absIConstantInfo a) == some (absIConstantInfo b))) := by
  intro o h
  rw [i_constant_info_beq_refines ha hb h]
  cases h' : decide (absIConstantInfo a = absIConstantInfo b) <;> simp_all

/-! ### The pinned constants and the stored ones are canonical

The callers of `i_constant_info_beq` compare a stored constant with a pinned
one; the premises of `i_constant_info_beq_spec` come from `IFEnvRel.envWF`
and from the pins' construction (`Checker/Canon.lean`'s `eq_a_wf`/`nat_a_wf`).
These variants carry the fact in their relation; they sit in their own
namespace so a proof that `open`s it gets them before the plain pairs. -/

namespace Lockstep.CapsWF

@[lockstep] theorem eq_a_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => IConstantInfoWF a ∧ b = absIConstantInfo a)
      (arena.std_axioms.eq_a pers st) lst eqA := by
  intro o st' h
  have hs := eq_a_ls hrel hinv o st' h
  cases o with
  | Err e => exact hs
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := hs
    exact ⟨b, lst', hx, ⟨eq_a_wf h, hR⟩, h1, h2⟩

@[lockstep] theorem nat_a_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => IConstantInfoWF a ∧ b = absIConstantInfo a)
      (arena.std_axioms.nat_a pers st) lst natA := by
  intro o st' h
  have hs := nat_a_ls hrel hinv o st' h
  cases o with
  | Err e => exact hs
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := hs
    exact ⟨b, lst', hx, ⟨nat_a_wf h, hR⟩, h1, h2⟩

/-- `ifenv_find` with the found constant's `IConstantInfoWF` (`envWF`). -/
@[lockstep] theorem ifenv_find_wf {vis : Std.U64} {rf lf} (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) (n : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find vis rf n)
      (fun o => TwinEq (lf.find? (absNIdx n)) (o.map absIConstantInfo) ∧
        ∀ ci, o = some ci → IConstantInfoWF ci) :=
  fun o h => ⟨(ifenv_find_abs (IFEnvInv.coreCtx hfe.rel hfe.inv hvis) h).symm,
    fun ci hci => by subst hci; exact hfe.rel.envWF ci (Lockstep.ifenv_find_mem h)⟩

end Lockstep.CapsWF

/-! ## The standard axioms' gate

`stdAxiomOk` accepts exactly `propext` and `Classical.choice`, each against
its pinned shape and with its supporting family pinned in the environment.
The Rust splits the two arms and their "is the family pinned" prefixes. -/

open Lockstep.CapsWF in
/-- `eq_basis_pinned` — is the `Eq` basis block installed as pinned? -/
theorem eq_basis_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.eq_basis_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (eqBasisPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.eq_basis_pinned]
  try unfold eqBasisPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem eq_basis_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.eq_basis_pinned pers vis st rf) lst
      (eqBasisPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => eq_basis_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `matches_pin_of_ci` — the header of a pinned constant, matched. -/
theorem matches_pin_of_ci_refines {pers st lst} {cv : arena.env.IConstantVal}
    {pin_ci : arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.matches_pin_of_ci pers st cv pin_ci = ok o) :
    Sim₀ id pers lst o
      (do
        let pcv ← (absIConstantInfo pin_ci).toConstantVal
        (absIConstantVal cv).matchesPin pcv) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.matches_pin_of_ci]
  skip
  lockstep

open Lockstep in
@[lockstep] theorem matches_pin_of_ci_ls {pers st lst}
    {cv : arena.env.IConstantVal}
    {pin_ci : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.matches_pin_of_ci pers st cv pin_ci) lst
      (do
        let pcv ← (absIConstantInfo pin_ci).toConstantVal
        (absIConstantVal cv).matchesPin pcv) :=
  LS.ofSim₀ fun _ h => matches_pin_of_ci_refines hrel hinv h

/-- `iff_pinned` — is `Iff` installed at its pinned shape? -/
theorem iff_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.iff_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (iffPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.iff_pinned]
  try unfold iffPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem iff_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.iff_pinned pers vis st rf) lst
      (iffPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => iff_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `iff_intro_pinned`. -/
theorem iff_intro_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.iff_intro_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (iffIntroPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.iff_intro_pinned]
  try unfold iffIntroPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem iff_intro_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.iff_intro_pinned pers vis st rf) lst
      (iffIntroPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => iff_intro_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `iff_rec_pinned`. -/
theorem iff_rec_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.iff_rec_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (iffRecPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.iff_rec_pinned]
  try unfold iffRecPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem iff_rec_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.iff_rec_pinned pers vis st rf) lst
      (iffRecPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => iff_rec_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `nonempty_pinned`. -/
theorem nonempty_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.nonempty_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (nonemptyPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.nonempty_pinned]
  try unfold nonemptyPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem nonempty_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.nonempty_pinned pers vis st rf) lst
      (nonemptyPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => nonempty_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `nonempty_intro_pinned`. -/
theorem nonempty_intro_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.nonempty_intro_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (nonemptyIntroPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.nonempty_intro_pinned]
  try unfold nonemptyIntroPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem nonempty_intro_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.nonempty_intro_pinned pers vis st rf) lst
      (nonemptyIntroPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => nonempty_intro_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `nonempty_rec_pinned`. -/
theorem nonempty_rec_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.nonempty_rec_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (nonemptyRecPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.nonempty_rec_pinned]
  try unfold nonemptyRecPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem nonempty_rec_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.nonempty_rec_pinned pers vis st rf) lst
      (nonemptyRecPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => nonempty_rec_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `std_axiom_ok_propext_rest` — `propext`'s arm past its name test. -/
theorem std_axiom_ok_propext_rest_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.std_axiom_ok_propext_rest pers vis st rf cv_a = ok o) :
    Sim₀ id pers lst o
      (stdAxiomOkPropextRestSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.std_axiom_ok_propext_rest]
  try unfold stdAxiomOkPropextRestSpec
  lockstep

open Lockstep in
@[lockstep] theorem std_axiom_ok_propext_rest_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.std_axiom_ok_propext_rest pers vis st rf cv_a) lst
      (stdAxiomOkPropextRestSpec lf (absIConstantVal cv_a)) :=
  LS.ofSim₀ fun _ h => std_axiom_ok_propext_rest_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `std_axiom_ok_propext` — `propext`'s arm. -/
theorem std_axiom_ok_propext_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.std_axiom_ok_propext pers vis st rf cv_a = ok o) :
    Sim₀ id pers lst o
      (stdAxiomOkPropextSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.std_axiom_ok_propext]
  try unfold stdAxiomOkPropextSpec
  lockstep

open Lockstep in
@[lockstep] theorem std_axiom_ok_propext_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.std_axiom_ok_propext pers vis st rf cv_a) lst
      (stdAxiomOkPropextSpec lf (absIConstantVal cv_a)) :=
  LS.ofSim₀ fun _ h => std_axiom_ok_propext_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `std_axiom_ok_choice_rest` — `Classical.choice`'s arm past its name test. -/
theorem std_axiom_ok_choice_rest_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.std_axiom_ok_choice_rest pers vis st rf cv_a = ok o) :
    Sim₀ id pers lst o
      (stdAxiomOkChoiceRestSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.std_axiom_ok_choice_rest]
  try unfold stdAxiomOkChoiceRestSpec
  lockstep

open Lockstep in
@[lockstep] theorem std_axiom_ok_choice_rest_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.std_axiom_ok_choice_rest pers vis st rf cv_a) lst
      (stdAxiomOkChoiceRestSpec lf (absIConstantVal cv_a)) :=
  LS.ofSim₀ fun _ h => std_axiom_ok_choice_rest_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `std_axiom_ok_choice` — `Classical.choice`'s arm. -/
theorem std_axiom_ok_choice_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.std_axiom_ok_choice pers vis st rf cv_a = ok o) :
    Sim₀ id pers lst o
      (stdAxiomOkChoiceSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.std_axiom_ok_choice]
  try unfold stdAxiomOkChoiceSpec
  lockstep

open Lockstep in
@[lockstep] theorem std_axiom_ok_choice_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.std_axiom_ok_choice pers vis st rf cv_a) lst
      (stdAxiomOkChoiceSpec lf (absIConstantVal cv_a)) :=
  LS.ofSim₀ fun _ h => std_axiom_ok_choice_refines hrel hinv hfe.rel hfe.inv hvis h

/-- **`std_axiom_ok` ⊑ `stdAxiomOk`** — the two standard axioms, each at its
pinned shape and with its supporting family pinned. -/
theorem std_axiom_ok_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.std_axiom_ok pers vis st rf cv_a = ok o) :
    Sim₀ id pers lst o (stdAxiomOk lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.std_axiom_ok, stdAxiomOk_split]
  lockstep

open Lockstep in
@[lockstep] theorem std_axiom_ok_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.std_axiom_ok pers vis st rf cv_a) lst
      (stdAxiomOk lf (absIConstantVal cv_a)) :=
  LS.ofSim₀ fun _ h => std_axiom_ok_refines hrel hinv hfe.rel hfe.inv hvis h

/-! ## The compiler-trust axioms' gate -/

/-- `true_pinned`. -/
theorem true_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.true_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (truePinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.true_pinned]
  try unfold truePinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem true_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.true_pinned pers vis st rf) lst
      (truePinnedSpec lf) :=
  LS.ofSim₀ fun _ h => true_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `true_intro_pinned`. -/
theorem true_intro_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.true_intro_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (trueIntroPinnedSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.true_intro_pinned]
  try unfold trueIntroPinnedSpec
  lockstep

open Lockstep in
@[lockstep] theorem true_intro_pinned_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.true_intro_pinned pers vis st rf) lst
      (trueIntroPinnedSpec lf) :=
  LS.ofSim₀ fun _ h => true_intro_pinned_refines hrel hinv hfe.rel hfe.inv hvis h

/-- **`trust_compiler_ok` ⊑ `trustCompilerOk`**. -/
theorem trust_compiler_ok_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.trust_compiler_ok pers vis st rf cv_a = ok o) :
    Sim₀ id pers lst o
      (trustCompilerOk lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.trust_compiler_ok, trustCompilerOk_split]
  lockstep

open Lockstep in
@[lockstep] theorem trust_compiler_ok_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.trust_compiler_ok pers vis st rf cv_a) lst
      (trustCompilerOk lf (absIConstantVal cv_a)) :=
  LS.ofSim₀ fun _ h => trust_compiler_ok_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `reduce_elem_ok_bool` — the `Bool` element type's arm. -/
theorem reduce_elem_ok_bool_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.reduce_elem_ok_bool pers vis st rf = ok o) :
    Sim₀ id pers lst o (reduceElemOkBoolSpec lf) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.reduce_elem_ok_bool]
  try unfold reduceElemOkBoolSpec
  lockstep

open Lockstep in
@[lockstep] theorem reduce_elem_ok_bool_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.reduce_elem_ok_bool pers vis st rf) lst
      (reduceElemOkBoolSpec lf) :=
  LS.ofSim₀ fun _ h => reduce_elem_ok_bool_refines hrel hinv hfe.rel hfe.inv hvis h

open Lockstep.CapsWF in
/-- `reduce_elem_ok` ⊑ `reduceElemOk`. -/
theorem reduce_elem_ok_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.reduce_elem_ok pers vis st rf c = ok o) :
    Sim₀ id pers lst o (reduceElemOk lf (absNIdx c)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.reduce_elem_ok, reduceElemOk]
  lockstep

open Lockstep in
@[lockstep] theorem reduce_elem_ok_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.reduce_elem_ok pers vis st rf c) lst
      (reduceElemOk lf (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_elem_ok_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `reduce_stored_ok` ⊑ `reduceStoredOk`. -/
theorem reduce_stored_ok_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.reduce_stored_ok pers vis st rf c = ok o) :
    Sim₀ id pers lst o (reduceStoredOk lf (absNIdx c)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.reduce_stored_ok]
  try unfold reduceStoredOk
  lockstep

open Lockstep in
@[lockstep] theorem reduce_stored_ok_ls {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.reduce_stored_ok pers vis st rf c) lst
      (reduceStoredOk lf (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_stored_ok_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `of_reduce_ax_ok_rest` — `ofReduceAxOk`'s tail past the operation it names. -/
theorem of_reduce_ax_ok_rest_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.of_reduce_ax_ok_rest pers vis st rf cv_a c = ok o) :
    Sim₀ id pers lst o
      (ofReduceAxOkRestSpec lf (absIConstantVal cv_a) (absNIdx c)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.of_reduce_ax_ok_rest]
  try unfold ofReduceAxOkRestSpec
  lockstep

open Lockstep in
@[lockstep] theorem of_reduce_ax_ok_rest_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.of_reduce_ax_ok_rest pers vis st rf cv_a c) lst
      (ofReduceAxOkRestSpec lf (absIConstantVal cv_a) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => of_reduce_ax_ok_rest_refines hrel hinv hfe.rel hfe.inv hvis h

/-- **`of_reduce_ax_ok` ⊑ `ofReduceAxOk`**. -/
theorem of_reduce_ax_ok_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.of_reduce_ax_ok pers vis st rf cv_a = ok o) :
    Sim₀ id pers lst o (ofReduceAxOk lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.of_reduce_ax_ok, ofReduceAxOk_split]
  lockstep

open Lockstep in
@[lockstep] theorem of_reduce_ax_ok_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.of_reduce_ax_ok pers vis st rf cv_a) lst
      (ofReduceAxOk lf (absIConstantVal cv_a)) :=
  LS.ofSim₀ fun _ h => of_reduce_ax_ok_refines hrel hinv hfe.rel hfe.inv hvis h

/-! ## The reduce-operation install pin -/

/-- `ground_guards_rest` — the ground-term guards past the first. -/
theorem ground_guards_rest_refines {pers st lst} {vis : Std.U64} {rf lf}
    {p : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.ground_guards_rest pers vis st rf p = ok o) :
    Sim₀ id pers lst o (groundGuardsRestSpec lf (absEIdx p)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.ground_guards_rest, groundGuardsRestSpec]
  lockstep

open Lockstep in
@[lockstep] theorem ground_guards_rest_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {p : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.ground_guards_rest pers vis st rf p) lst
      (groundGuardsRestSpec lf (absEIdx p)) :=
  LS.ofSim₀ fun _ h => ground_guards_rest_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `ground_guards` — a pinned value is closed, free-variable-free, has no
undeclared universe parameter and resolves. -/
theorem ground_guards_refines {pers st lst} {vis : Std.U64} {rf lf}
    {p : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.ground_guards pers vis st rf p = ok o) :
    Sim₀ id pers lst o (groundGuardsSpec lf (absEIdx p)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.ground_guards, groundGuardsSpec]
  lockstep

open Lockstep in
@[lockstep] theorem ground_guards_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {p : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.ground_guards pers vis st rf p) lst
      (groundGuardsSpec lf (absEIdx p)) :=
  LS.ofSim₀ fun _ h => ground_guards_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `reduce_pin_guard` ⊑ `reducePinGuard`. -/
theorem reduce_pin_guard_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.reduce_pin_guard pers vis st rf c = ok o) :
    Sim₀ id pers lst o (reducePinGuard lf (absNIdx c)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.reduce_pin_guard]
  try unfold reducePinGuard
  lockstep

open Lockstep in
@[lockstep] theorem reduce_pin_guard_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.reduce_pin_guard pers vis st rf c) lst
      (reducePinGuard lf (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_pin_guard_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_reduce_identity` — the pinned value is the identity on its element
type, definitionally. -/
theorem check_reduce_identity_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {val_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_reduce_identity pers vis st mode rf c val_a
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkReduceIdentitySpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx val_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.check_reduce_identity]
  try unfold checkReduceIdentitySpec
  lockstep

open Lockstep in
@[lockstep] theorem check_reduce_identity_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {c : arena.handle.NIdx}
    {val_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_reduce_identity pers vis st mode rf c val_a) lst
      (checkReduceIdentitySpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx val_a)) :=
  LS.ofSim₀ fun _ h => check_reduce_identity_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_reduce_pin_value` — the install pin's value half. -/
theorem check_reduce_pin_value_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_reduce_pin_value pers vis st mode rf c value
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkReducePinValueSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.check_reduce_pin_value]
  try unfold checkReducePinValueSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_reduce_pin_value_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {c : arena.handle.NIdx}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_reduce_pin_value pers vis st mode rf c value) lst
      (checkReducePinValueSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value)) :=
  LS.ofSim₀ fun _ h => check_reduce_pin_value_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_reduce_pin_pre` — the install pin's guard prefix. -/
theorem check_reduce_pin_pre_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_reduce_pin_pre pers vis st mode rf c value
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkReducePinPreSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.check_reduce_pin_pre]
  try unfold checkReducePinPreSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_reduce_pin_pre_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_reduce_pin_pre pers vis st mode rf c value) lst
      (checkReducePinPreSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value)) :=
  LS.ofSim₀ fun _ h => check_reduce_pin_pre_refines hrel hinv hfe.rel hfe.inv hvis h

/-- **`check_reduce_pin` ⊑ `checkReducePin`**.  Task #97-P6-6b's `k_pre` is
the visibility counter the install ran at, carried beside the post-install
environment: the twin takes the two environments `fe` and `fe2`, and the port
takes `fe2` with the counter that restricts it — which is `hkpre`. -/
theorem check_reduce_pin_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {c : arena.handle.NIdx}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.decl_check.check_reduce_pin pers st mode rf2 k_pre c value = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do checkReducePin (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2 (absNIdx c)
            (absEIdx value)
          pure lf2) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_reduce_pin, checkReducePin_split]
  lockstep

open Lockstep in
@[lockstep] theorem check_reduce_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode} {k_pre : Std.U64} {c : arena.handle.NIdx}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.decl_check.check_reduce_pin pers st mode rf2 k_pre c value) lst
      (do checkReducePin (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) lf2
            (absNIdx c) (absEIdx value)
          pure lf2) :=
  LS.ofSimRel₀ fun _ h => check_reduce_pin_refines hrel hinv hfe.rel hfe.inv hk h

/-! ## The three value kinds -/

/-- **`check_defn_val` ⊑ `checkDefnVal`**.  The answer carries the index
invariant and the Rust fact that the push only raised the counter — the
next step (`check_defn_pins`) restricts the new index back to the old
counter (task #97-T2-LOCKSTEP lane Checker round 2). -/
theorem check_defn_val_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.check_defn_val pers st mode rf cv value hint = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r v ∧ rf.visible_below.val ≤ r.visible_below.val)
      pers lst o
      (checkDefnVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value) (ConRon.Refine.absHint hint)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_defn_val]
  try unfold checkDefnVal
  lockstep

open Lockstep in
@[lockstep] theorem check_defn_val_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    {hint : kernel.env.ReducibilityHint}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r v ∧ rf.visible_below.val ≤ r.visible_below.val)
      (arena.decl_check.check_defn_val pers st mode rf cv value hint) lst
      (checkDefnVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value) (ConRon.Refine.absHint hint)) :=
  LS.ofSimRel₀ fun _ h => check_defn_val_refines hrel hinv hfe.rel hfe.inv h

/-- `check_thm_val_witness` — `checkThmVal`'s tail past the proposition test. -/
theorem check_thm_val_witness_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.check_thm_val_witness pers st mode rf cv value = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkThmValWitnessSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_thm_val_witness]
  unfold checkThmValWitnessSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_thm_val_witness_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.decl_check.check_thm_val_witness pers st mode rf cv value) lst
      (checkThmValWitnessSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => check_thm_val_witness_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_thm_val` ⊑ `checkThmVal`** (lockstep: no precondition on the
twin since task #97-T2-LOCKSTEP lane Checker). -/
theorem check_thm_val_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.check_thm_val pers st mode rf cv value = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkThmVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_thm_val]
  rw [checkThmVal_split]
  lockstep

open Lockstep in
@[lockstep] theorem check_thm_val_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.decl_check.check_thm_val pers st mode rf cv value) lst
      (checkThmVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => check_thm_val_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_opaque_val` ⊑ `checkOpaqueVal`**, with `check_defn_val`'s answer
relation. -/
theorem check_opaque_val_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.check_opaque_val pers st mode rf cv value = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r v ∧ rf.visible_below.val ≤ r.visible_below.val)
      pers lst o
      (checkOpaqueVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_opaque_val]
  try unfold checkOpaqueVal
  lockstep

open Lockstep in
@[lockstep] theorem check_opaque_val_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRelI r v ∧ rf.visible_below.val ≤ r.visible_below.val)
      (arena.decl_check.check_opaque_val pers st mode rf cv value) lst
      (checkOpaqueVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) :=
  LS.ofSimRel₀ fun _ h => check_opaque_val_refines hrel hinv hfe.rel hfe.inv h

/-! ## The `Nat`-operation pin certification

DESIGN §8.3's one recovering seam sits at the end of this section
(`check_div_mod_pin_try`, which is `orElseAttempt` at a variant). -/

section NatReaders

/-! ### `arena::core`'s structural-`Nat` readers

`arena::core` functions no other tier states, reached from the pin gates
(task #97-T2-LOCKSTEP lane Checker DeclCheck).  Each is one `lockstep` zip;
the Rust helpers the twin writes inline (`bool_ty_ok`, `lp_empty`,
`nat_eq_ctx`, `nat_op_pins`, `nat_op_equations_at` and its arms) are
unfolded on the Rust side first. -/

/-- A twin `if` on `a || b` is the Rust's two tests in a row (the Rust
short-circuits with a bind between them). -/
theorem ite_bor {α : Sort _} (a b : Bool) (x y : α) :
    (if (a || b) = true then x else y) = if a = true then x else if b = true then x else y := by
  cases a <;> cases b <;> rfl

/-- The Rust's `cv.level_params.len() == 0` is the twin's `levelParams.isEmpty`. -/
theorem absIConstantVal_levelParams_isEmpty (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).levelParams.isEmpty = decide (cv.level_params.len = 0#usize) := by
  rw [Bool.eq_iff_iff]
  simp only [absIConstantVal, List.isEmpty_map, List.isEmpty_iff, decide_eq_true_eq]
  rw [← List.length_eq_zero_iff]
  have h1 := alloc.vec.Vec.len_val cv.level_params
  simp only [alloc.vec.Vec.length] at h1
  constructor <;> intro h <;> scalar_tac

/-- … and in the form the twin is in once `absIConstantVal` is unfolded. -/
theorem map_absNIdx_isEmpty (l : alloc.vec.Vec arena.handle.NIdx) :
    (l.val.map absNIdx).isEmpty = decide (l.len = 0#usize) := by
  rw [Bool.eq_iff_iff]
  simp only [List.isEmpty_map, List.isEmpty_iff, decide_eq_true_eq]
  rw [← List.length_eq_zero_iff]
  have h1 := alloc.vec.Vec.len_val l
  simp only [alloc.vec.Vec.length] at h1
  constructor <;> intro h <;> scalar_tac

attribute [local lockstep_simp] absIConstantVal_levelParams_isEmpty map_absNIdx_isEmpty

open Lockstep in
/-- `arena::core::nat_ind_ok` ⊑ `natIndOk`. -/
@[lockstep] theorem nat_ind_ok_ls {pers st lst} {ci : Option arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.core.nat_ind_ok st ci) lst
      (natIndOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | ci
  · simp only [arena.core.nat_ind_ok, Option.map_none, natIndOk]; lockstep
  · cases ci <;> simp only [arena.core.nat_ind_ok, Option.map_some, absIConstantInfo, natIndOk] <;>
      lockstep

open Lockstep in
/-- `arena::core::nat_zero_ok` ⊑ `natZeroOk`. -/
@[lockstep] theorem nat_zero_ok_ls {pers st lst} {ci : Option arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.core.nat_zero_ok pers st ci) lst
      (natZeroOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | ci
  · simp only [arena.core.nat_zero_ok, Option.map_none, natZeroOk]; lockstep
  · cases ci <;> simp only [arena.core.nat_zero_ok, Option.map_some, absIConstantInfo,
      natZeroOk] <;> lockstep

open Lockstep in
/-- `arena::core::nat_succ_ok` ⊑ `natSuccOk`. -/
@[lockstep] theorem nat_succ_ok_ls {pers st lst} {ci : Option arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.core.nat_succ_ok pers st ci) lst
      (natSuccOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | ci
  · simp only [arena.core.nat_succ_ok, Option.map_none, natSuccOk]; lockstep
  · cases ci <;> simp only [arena.core.nat_succ_ok, Option.map_some, absIConstantInfo,
      natSuccOk] <;> lockstep

open Lockstep in
/-- `arena::core::nat_lit_supported` ⊑ `natLitSupported`. -/
@[lockstep] theorem nat_lit_supported_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.core.nat_lit_supported pers vis st rf) lst
      (natLitSupported lf) := by
  rw [arena.core.nat_lit_supported, natLitSupported]
  lockstep

open Lockstep in
/-- `arena::core::nat_op_cod` ⊑ `natOpCod` (the Rust's `bool_ty_ok` is the
twin's inline `match`). -/
@[lockstep] theorem nat_op_cod_ls {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.core.nat_op_cod pers vis st rf c e) lst
      (natOpCod lf (absNIdx c) (absEIdx e)) := by
  rw [arena.core.nat_op_cod, natOpCod]
  simp only [arena.core.bool_ty_ok]
  lockstep

open Lockstep in
/-- `arena::core::nat_op_ty_pinned` ⊑ `natOpTyPinned`. -/
@[lockstep] theorem nat_op_ty_pinned_ls {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.core.nat_op_ty_pinned pers vis st rf c e) lst
      (natOpTyPinned lf (absNIdx c) (absEIdx e)) := by
  rw [arena.core.nat_op_ty_pinned, natOpTyPinned]
  lockstep

open Lockstep in
/-- `arena::core::nat_op_stored_ok` ⊑ `natOpStoredOk`. -/
@[lockstep] theorem nat_op_stored_ok_ls {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.core.nat_op_stored_ok pers vis st rf c) lst
      (natOpStoredOk lf (absNIdx c)) := by
  rw [arena.core.nat_op_stored_ok, natOpStoredOk]
  lockstep

open Lockstep in
/-- `arena::core::push_nidx` is `Vec::push`. -/
@[lockstep] theorem push_nidx_spec (out : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) :
    LSP (arena.core.push_nidx out n) (fun w => w.val = out.val ++ [n]) :=
  fun _ h => push_nidx_val h

open Lockstep in
/-- `arena::core::push_eq` is `Vec::push` of the pair. -/
@[lockstep] theorem push_eq_spec
    (out : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)) (l r : arena.handle.EIdx) :
    LSP (arena.core.push_eq out l r) (fun w => w.val = out.val ++ [(l, r)]) := by
  intro w h
  rw [arena.core.push_eq] at h
  obtain ⟨l1, hl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [dupId_eidx _ _ hl1, dupId_eidx _ _ hr1] at h
  exact ConRon.Refine.vec_push_val h

theorem absNIdxL_val (v : alloc.vec.Vec arena.handle.NIdx) :
    absNIdxL v = v.val.map absNIdx := rfl

theorem absEqPairs_val (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)) :
    absEqPairs v = v.val.map fun p => (absEIdx p.1, absEIdx p.2) := rfl

attribute [local lockstep_simp] absNIdxL_val absEqPairs_val

open Lockstep in
/-- `arena::core::nat_op_deps` ⊑ `natOpDeps` — the operation's dependency list,
pin reads only.  The Rust reads its fifteen pins through `nat_op_pins`. -/
@[lockstep] theorem nat_op_deps_ls {pers st lst} {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a)
      (arena.core.nat_op_deps st c) lst (natOpDeps (absNIdx c)) := by
  rw [arena.core.nat_op_deps, natOpDeps]
  simp only [arena.core.nat_op_pins, arena.core.nat_op_pins_rest]
  lockstep

theorem nat_op_deps_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_deps st c = ok o) :
    Sim₀ absNIdxL pers lst o (natOpDeps (absNIdx c)) :=
  Lockstep.LS.toSim₀ (nat_op_deps_ls hrel hinv) hrun

open Lockstep in
/-- `arena::core::nat_op_equations` ⊑ `natOpEquations` — the operation's
recurrence equations, built.  The twin reads all fifteen operation pins, as
the Rust's `nat_op_pins` does (fixed in the twin, this lane). -/
@[lockstep] theorem nat_op_equations_ls {pers st lst} {d : Std.U64}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEqPairs a)
      (arena.core.nat_op_equations pers st d c) lst
      (natOpEquations (absU d) (absNIdx c)) := by
  rw [arena.core.nat_op_equations, natOpEquations]
  simp only [arena.core.nat_eq_ctx, arena.core.nat_eq_ctx_rest, arena.core.nat_op_pins,
    arena.core.nat_op_pins_rest, arena.core.nat_op_equations_at, arena.core.nat_op_equations_pow,
    arena.core.nat_op_equations_beq, arena.core.nat_op_equations_ble]
  lockstep

theorem nat_op_equations_refines {pers st lst} {d : Std.U64}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_equations pers st d c = ok o) :
    Sim₀ absEqPairs pers lst o (natOpEquations (absU d) (absNIdx c)) :=
  Lockstep.LS.toSim₀ (nat_op_equations_ls hrel hinv) hrun

theorem absNIdxLFrom_cons' (v : alloc.vec.Vec arena.handle.NIdx)
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absNIdxLFrom v i = absNIdx v.val[i.val] :: (v.val.drop (i.val + 1)).map absNIdx := by
  simp only [absNIdxLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

theorem absNIdxLFrom_nil' (v : alloc.vec.Vec arena.handle.NIdx)
    (i : Std.Usize) (hi : v.val.length ≤ i.val) : absNIdxLFrom v i = [] := by
  simp only [absNIdxLFrom]; rw [List.drop_eq_nil_of_le hi]; rfl

open Lockstep in
theorem nat_op_deps_stored_aux (n : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf}
      (ns : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize),
      ns.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf → absU vis = lf.visibleBelow →
      LS pers (fun a b => b = id a)
        (arena.core.nat_op_deps_stored pers vis st rf ns i) lst
        (natOpDepsStored lf (absNIdxLFrom ns i)) := by
  induction n with
  | zero =>
    intro pers st lst vis rf lf ns i hn hrel hinv hfe hvis
    rw [arena.core.nat_op_deps_stored, absNIdxLFrom_nil' ns i (by omega), natOpDepsStored]
    have hl := alloc.vec.Vec.len_val ns
    rw [if_pos (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst vis rf lf ns i hn hrel hinv hfe hvis
    rw [arena.core.nat_op_deps_stored, absNIdxLFrom_cons' ns i (by omega), natOpDepsStored]
    have hl := alloc.vec.Vec.len_val ns
    rw [if_neg (by scalar_tac)]
    refine LSP.bind (vec_index_spec _ _) fun p ⟨_, hp⟩ => ?_
    subst hp
    simp only [absNIdxLFrom] at ih
    lockstep

open Lockstep in
/-- `arena::core::nat_op_deps_stored` ⊑ `natOpDepsStored` at the cursor. -/
@[lockstep] theorem nat_op_deps_stored_ls {pers st lst} {vis : Std.U64} {rf lf}
    {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.core.nat_op_deps_stored pers vis st rf ns i) lst
      (natOpDepsStored lf (absNIdxLFrom ns i)) :=
  nat_op_deps_stored_aux _ ns i rfl hrel hinv hfe hvis

open Lockstep in
/-- `arena::core::bool_ctors_lp_empty` ⊑ `natOpGuard`'s tail (the two `Bool`
constructors stored at no level parameters), written inline in the twin. -/
@[lockstep] theorem bool_ctors_lp_empty_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.core.bool_ctors_lp_empty pers vis st rf) lst
      (do
        let bt ← boolTrueName
        let okT ←
          match lf.find? bt with
          | some ci => do let cv ← ci.toConstantVal; pure cv.levelParams.isEmpty
          | none => pure false
        if !okT then pure false else do
          let bf ← boolFalseName
          match lf.find? bf with
          | some ci => do let cv ← ci.toConstantVal; pure cv.levelParams.isEmpty
          | none => pure false) := by
  rw [arena.core.bool_ctors_lp_empty]
  simp only [arena.core.lp_empty]
  lockstep

open Lockstep in
theorem nat_op_guard_aux {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.core.nat_op_guard pers vis st rf c) lst
      (natOpGuard lf (absNIdx c)) := by
  rw [arena.core.nat_op_guard, natOpGuard]
  simp only [ite_bor]
  lockstep

open Lockstep in
theorem nat_op_stored_ok_all_aux (n : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf}
      (ns : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize),
      ns.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf → absU vis = lf.visibleBelow →
      LS pers (fun a b => b = id a)
        (arena.decl_check.nat_op_stored_ok_all pers vis st rf ns i) lst
        (natOpStoredOkAll lf (absNIdxLFrom ns i)) := by
  induction n with
  | zero =>
    intro pers st lst vis rf lf ns i hn hrel hinv hfe hvis
    rw [arena.decl_check.nat_op_stored_ok_all, absNIdxLFrom_nil' ns i (by omega),
      natOpStoredOkAll]
    have hl := alloc.vec.Vec.len_val ns
    rw [if_pos (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst vis rf lf ns i hn hrel hinv hfe hvis
    rw [arena.decl_check.nat_op_stored_ok_all, absNIdxLFrom_cons' ns i (by omega),
      natOpStoredOkAll]
    have hl := alloc.vec.Vec.len_val ns
    rw [if_neg (by scalar_tac)]
    refine LSP.bind (vec_index_spec _ _) fun p ⟨_, hp⟩ => ?_
    subst hp
    simp only [absNIdxLFrom] at ih
    lockstep

end NatReaders

/-- `nat_op_stored_ok_all` ⊑ `natOpStoredOkAll` at the cursor. -/
theorem nat_op_stored_ok_all_refines {pers st lst} {vis : Std.U64} {rf lf}
    {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.nat_op_stored_ok_all pers vis st rf ns i = ok o) :
    Sim₀ id pers lst o
      (natOpStoredOkAll lf (absNIdxLFrom ns i)) :=
  Lockstep.LS.toSim₀ (nat_op_stored_ok_all_aux _ ns i rfl hrel hinv ⟨hfe, hfinv⟩ hvis) hrun

open Lockstep in
@[lockstep] theorem nat_op_stored_ok_all_ls {pers st lst} {vis : Std.U64} {rf lf}
    {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.nat_op_stored_ok_all pers vis st rf ns i) lst
      (natOpStoredOkAll lf (absNIdxLFrom ns i)) :=
  LS.ofSim₀ fun _ h => nat_op_stored_ok_all_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `arena::core::nat_op_guard` ⊑ `natOpGuard` — the structural pin gate's
stored-constant guard.  The function is `arena::core`'s; no tier had stated
it (task #97-T2-LOCKSTEP lane Checker round 2, for `check_structural_nat_pin`). -/
theorem nat_op_guard_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.core.nat_op_guard pers vis st rf c = ok o) :
    Sim₀ id pers lst o (natOpGuard lf (absNIdx c)) :=
  Lockstep.LS.toSim₀ (nat_op_guard_aux hrel hinv ⟨hfe, hfinv⟩ hvis) hrun

open Lockstep in
@[lockstep] theorem nat_op_guard_ls {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.core.nat_op_guard pers vis st rf c) lst
      (natOpGuard lf (absNIdx c)) :=
  LS.ofSim₀ fun _ h => nat_op_guard_refines hrel hinv hfe.rel hfe.inv hvis h

/-- **Finding 12** — `defn_value` is `fe.find? c` matched for `.defnInfo`,
lifted out of three call sites so the borrow of `fe` is dead before the
checker recurses.  PURE, and the one bare `Option` equation of the tier. -/
theorem defn_value_refines {vis : Std.U64} {rf lf} {c : arena.handle.NIdx} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.defn_value vis rf c = ok o) :
    o.map absEIdx =
      (match lf.find? (absNIdx c) with
       | some (.defnInfo _ v _) => some v
       | _ => none) := by
  rw [arena.decl_check.defn_value] at hrun
  obtain ⟨ci, hci, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hf := ifenv_find_abs (IFEnvInv.coreCtx hfe hfinv hvis) hci
  rw [← hf]
  rcases ci with _ | ci
  · obtain rfl := (Result.ok_injective hrun).symm; rfl
  · cases ci <;> simp only [absIConstantInfo, Option.map_some] at hrun ⊢ <;>
      first
      | (obtain rfl := (Result.ok_injective hrun).symm; rfl)
      | (obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
         obtain rfl := (Result.ok_injective hrun).symm
         simp [dupId_eidx _ _ he])

open Lockstep in
@[lockstep] theorem defn_value_spec {vis : Std.U64} {rf lf}
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow)
    (c : arena.handle.NIdx) :
    LSP (arena.decl_check.defn_value vis rf c)
      (fun o => TwinEq (defnValueOf lf (absNIdx c)) (o.map absEIdx)) :=
  fun _ h => (defn_value_refines hfe.rel hfe.inv hvis h).symm

theorem absEqPairsFrom_cons' (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absEqPairsFrom v i = (absEIdx v.val[i.val].1, absEIdx v.val[i.val].2) ::
      (v.val.drop (i.val + 1)).map (fun p => (absEIdx p.1, absEIdx p.2)) := by
  simp only [absEqPairsFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

theorem absEqPairsFrom_nil' (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) (hi : v.val.length ≤ i.val) : absEqPairsFrom v i = [] := by
  simp only [absEqPairsFrom]; rw [List.drop_eq_nil_of_le hi]; rfl

open Lockstep in
theorem subst_const0_aux (k : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (n : arena.handle.NIdx) (r : arena.handle.EIdx)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.core.subst_const0 pers st n r fuel h) lst
        (substConst0 (absNIdx n) (absEIdx r) k (absEIdx h)) := by
  induction k with
  | zero =>
    intro pers st lst n r fuel h hn hrel hinv
    rw [arena.core.subst_const0, substConst0]
    lockstep
  | succ m ih =>
    intro pers st lst n r fuel h hn hrel hinv
    rw [arena.core.subst_const0, substConst0]
    lockstep

open Lockstep in
/-- `arena::core::subst_const0` ⊑ `substConst0` (task #97-T2-LOCKSTEP lane
Checker DeclCheck: `arena::core`'s, stated here for its two callers). -/
@[lockstep] theorem subst_const0_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (r : arena.handle.EIdx)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.core.subst_const0 pers st n r fuel h) lst
      (substConst0 (absNIdx n) (absEIdx r) (absU fuel) (absEIdx h)) :=
  subst_const0_aux _ n r fuel h rfl hrel hinv

open Lockstep in
theorem subst_const_all_aux (k : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (n : arena.handle.NIdx) (r : arena.handle.EIdx)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.core.subst_const_all pers st n r fuel h) lst
        (substConstAll (absNIdx n) (absEIdx r) k (absEIdx h)) := by
  induction k with
  | zero =>
    intro pers st lst n r fuel h hn hrel hinv
    rw [arena.core.subst_const_all, substConstAll]
    lockstep
  | succ m ih =>
    intro pers st lst n r fuel h hn hrel hinv
    rw [arena.core.subst_const_all, substConstAll]
    lockstep

open Lockstep in
/-- `arena::core::subst_const_all` ⊑ `substConstAll` (`arena::core`'s, stated
here for its callers, the certificate guards). -/
@[lockstep] theorem subst_const_all_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (r : arena.handle.EIdx)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.core.subst_const_all pers st n r fuel h) lst
      (substConstAll (absNIdx n) (absEIdx r) (absU fuel) (absEIdx h)) :=
  subst_const_all_aux _ n r fuel h rfl hrel hinv

section SubstConst0

open Lockstep in
theorem subst_const0_list_aux (k : Nat) :
    ∀ {pers st lst} (n : arena.handle.NIdx) (r : arena.handle.EIdx)
      (hs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
      (out : alloc.vec.Vec arena.handle.EIdx),
      hs.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun v b => b = absEIdxL v)
        (arena.decl_check.subst_const0_list pers st n r hs i out) lst
        (do pure (absEIdxL out ++
          (← substConst0List (absNIdx n) (absEIdx r) (absEIdxLFrom hs i)))) := by
  induction k with
  | zero =>
    intro pers st lst n r hs i out hn hrel hinv
    have hl := alloc.vec.Vec.len_val hs
    have : absEIdxLFrom hs i = [] := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_nil_of_le (by scalar_tac)]; rfl
    rw [arena.decl_check.subst_const0_list, this, substConst0List]
    rw [if_pos (by scalar_tac)]
    lockstep
  | succ m ih =>
    intro pers st lst n r hs i out hn hrel hinv
    have hl := alloc.vec.Vec.len_val hs
    have hi : i.val < hs.val.length := by omega
    have : absEIdxLFrom hs i = absEIdx hs.val[i.val] :: (hs.val.drop (i.val + 1)).map absEIdx := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl
    rw [arena.decl_check.subst_const0_list, this, substConst0List]
    rw [if_neg (by scalar_tac)]
    simp only [absEIdxLFrom] at ih
    lockstep

open Lockstep in
theorem subst_const0_pairs_aux (k : Nat) :
    ∀ {pers st lst} (n : arena.handle.NIdx) (r : arena.handle.EIdx)
      (eqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)) (i : Std.Usize)
      (out : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)),
      eqs.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun v b => b = absEqPairs v)
        (arena.decl_check.subst_const0_pairs pers st n r eqs i out) lst
        (do pure (absEqPairs out ++
          (← substConst0Pairs (absNIdx n) (absEIdx r) (absEqPairsFrom eqs i)))) := by
  induction k with
  | zero =>
    intro pers st lst n r eqs i out hn hrel hinv
    rw [arena.decl_check.subst_const0_pairs, absEqPairsFrom_nil' eqs i (by omega),
      substConst0Pairs]
    have hl := alloc.vec.Vec.len_val eqs
    rw [if_pos (by scalar_tac)]
    lockstep
  | succ m ih =>
    intro pers st lst n r eqs i out hn hrel hinv
    rw [arena.decl_check.subst_const0_pairs, absEqPairsFrom_cons' eqs i (by omega),
      substConst0Pairs]
    have hl := alloc.vec.Vec.len_val eqs
    rw [if_neg (by scalar_tac)]
    lockstep

end SubstConst0

/-- `subst_const0_list` ⊑ `substConst0List` at the cursor. -/
theorem subst_const0_list_refines {pers st lst} {n : arena.handle.NIdx}
    {r : arena.handle.EIdx} {hs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize} {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.subst_const0_list pers st n r hs i out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← substConst0List (absNIdx n) (absEIdx r) (absEIdxLFrom hs i)))) :=
  Lockstep.LS.toSim₀ (subst_const0_list_aux _ n r hs i out rfl hrel hinv) hrun

open Lockstep in
@[lockstep] theorem subst_const0_list_ls {pers st lst}
    {n : arena.handle.NIdx}
    {r : arena.handle.EIdx}
    {hs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.decl_check.subst_const0_list pers st n r hs i out) lst
      (do pure (absEIdxL out ++
        (← substConst0List (absNIdx n) (absEIdx r) (absEIdxLFrom hs i)))) :=
  LS.ofSim₀ fun _ h => subst_const0_list_refines hrel hinv h

/-- `subst_const0_pairs` ⊑ `substConst0Pairs` at the cursor. -/
theorem subst_const0_pairs_refines {pers st lst} {n : arena.handle.NIdx}
    {r : arena.handle.EIdx}
    {eqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.subst_const0_pairs pers st n r eqs i out = ok o) :
    Sim₀ absEqPairs pers lst o
      (do pure (absEqPairs out ++
        (← substConst0Pairs (absNIdx n) (absEIdx r) (absEqPairsFrom eqs i)))) :=
  Lockstep.LS.toSim₀ (subst_const0_pairs_aux _ n r eqs i out rfl hrel hinv) hrun

open Lockstep in
/-- `subst_const0_pairs` from its entry — cursor `0`, nothing accumulated —
is `substConst0Pairs` over the whole list. -/
@[lockstep] theorem subst_const0_pairs_nil_ls {pers st lst} {n : arena.handle.NIdx}
    {r : arena.handle.EIdx}
    {eqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEqPairs a)
      (arena.decl_check.subst_const0_pairs pers st n r eqs 0#usize
        (alloc.vec.Vec.new (arena.handle.EIdx × arena.handle.EIdx))) lst
      (substConst0Pairs (absNIdx n) (absEIdx r) (absEqPairs eqs)) := by
  refine LS.ofSim₀ fun _ h => ?_
  have h1 := subst_const0_pairs_refines hrel hinv h
  have e1 : absEqPairs (alloc.vec.Vec.new (arena.handle.EIdx × arena.handle.EIdx)) = [] :=
    rfl
  have e2 : absEqPairsFrom eqs 0#usize = absEqPairs eqs := by
    simp [absEqPairsFrom, absEqPairs]
  simp only [e1, e2, List.nil_append, bind_pure] at h1
  exact h1

open Lockstep in
theorem consts_resolve_all_aux (k : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf}
      (hs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize),
      hs.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf → absU vis = lf.visibleBelow →
      LS pers (fun a b => b = id a)
        (arena.decl_check.consts_resolve_all pers vis st rf hs i) lst
        (constsResolveAll lf (absEIdxLFrom hs i)) := by
  induction k with
  | zero =>
    intro pers st lst vis rf lf hs i hn hrel hinv hfe hvis
    have hl := alloc.vec.Vec.len_val hs
    have : absEIdxLFrom hs i = [] := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [arena.decl_check.consts_resolve_all, this, constsResolveAll, if_pos (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ m ih =>
    intro pers st lst vis rf lf hs i hn hrel hinv hfe hvis
    have hl := alloc.vec.Vec.len_val hs
    have hi : i.val < hs.val.length := by omega
    have : absEIdxLFrom hs i = absEIdx hs.val[i.val] :: (hs.val.drop (i.val + 1)).map absEIdx := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl
    rw [arena.decl_check.consts_resolve_all, this, constsResolveAll, if_neg (by scalar_tac)]
    simp only [absEIdxLFrom] at ih
    lockstep

/-- `consts_resolve_all` ⊑ `constsResolveAll` at the cursor. -/
theorem consts_resolve_all_refines {pers st lst} {vis : Std.U64} {rf lf}
    {hs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.consts_resolve_all pers vis st rf hs i = ok o) :
    Sim₀ id pers lst o
      (constsResolveAll lf (absEIdxLFrom hs i)) :=
  Lockstep.LS.toSim₀ (consts_resolve_all_aux _ hs i rfl hrel hinv ⟨hfe, hfinv⟩ hvis) hrun

open Lockstep in
@[lockstep] theorem consts_resolve_all_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {hs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.consts_resolve_all pers vis st rf hs i) lst
      (constsResolveAll lf (absEIdxLFrom hs i)) :=
  LS.ofSim₀ fun _ h => consts_resolve_all_refines hrel hinv hfe.rel hfe.inv hvis h

open Lockstep in
theorem certify_nat_eqs_aux (n : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf} {mode : kernel.env.CheckMode}
      (eqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)) (i : Std.Usize),
      eqs.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf → absU vis = lf.visibleBelow →
      LS pers (fun a b => b = id a)
        (arena.decl_check.certify_nat_eqs pers vis st mode rf eqs i) lst
        (certifyNatEqs (ConRon.Refine.absMode mode) lf (absEqPairsFrom eqs i)) := by
  induction n with
  | zero =>
    intro pers st lst vis rf lf mode eqs i hn hrel hinv hfe hvis
    rw [arena.decl_check.certify_nat_eqs, absEqPairsFrom_nil' eqs i (by omega), certifyNatEqs]
    have hl := alloc.vec.Vec.len_val eqs
    rw [if_pos (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst vis rf lf mode eqs i hn hrel hinv hfe hvis
    rw [arena.decl_check.certify_nat_eqs, absEqPairsFrom_cons' eqs i (by omega), certifyNatEqs]
    have hctx := IFEnvInv.coreCtx hfe.rel hfe.inv hvis
    have hl := alloc.vec.Vec.len_val eqs
    rw [if_neg (by scalar_tac)]
    refine LSP.bind (vec_index_spec _ _) fun p ⟨_, hp⟩ => ?_
    subst hp
    generalize (↑eqs : List _)[↑i] = p
    obtain ⟨e, e1⟩ := p
    simp only [absEqPairsFrom] at ih
    lockstep

/-- `certify_nat_eqs` ⊑ `certifyNatEqs` at the cursor. -/
theorem certify_nat_eqs_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode}
    {eqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)}
    {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.certify_nat_eqs pers vis st mode rf eqs i = ok o) :
    Sim₀ id pers lst o
      (certifyNatEqs (ConRon.Refine.absMode mode) lf (absEqPairsFrom eqs i)) := by
  exact Lockstep.LS.toSim₀ (certify_nat_eqs_aux _ eqs i rfl hrel hinv ⟨hfe, hfinv⟩ hvis) hrun

open Lockstep in
@[lockstep] theorem certify_nat_eqs_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode}
    {eqs : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.certify_nat_eqs pers vis st mode rf eqs i) lst
      (certifyNatEqs (ConRon.Refine.absMode mode) lf (absEqPairsFrom eqs i)) :=
  LS.ofSim₀ fun _ h => certify_nat_eqs_refines hrel hinv hfe.rel hfe.inv hvis h

@[lockstep_simp] theorem absEqPairsFrom_zero
    (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx)) :
    absEqPairsFrom v 0#usize = absEqPairs v := by
  simp [absEqPairsFrom, absEqPairs]

/-! ### The certificate statements — the `CertCtx` family (finding 11) -/

/-- `nat_one` ⊑ `natOne` — the numeral `1` as `Nat.succ Nat.zero`. -/
theorem nat_one_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.nat_one pers st = ok o) :
    Sim₀ absEIdx pers lst o natOne := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.nat_one]
  try unfold natOne
  lockstep

open Lockstep in
@[lockstep] theorem nat_one_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.nat_one pers st) lst
      natOne :=
  LS.ofSim₀ fun _ h => nat_one_refines hrel hinv h

/-- `nat_var` ⊑ `natVar` — `fvar i` at `Nat`. -/
theorem nat_var_refines {pers st lst} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.nat_var pers st i = ok o) :
    Sim₀ absEIdx pers lst o (natVar (absU i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.nat_var]
  try unfold natVar
  lockstep

open Lockstep in
@[lockstep] theorem nat_var_ls {pers st lst}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.nat_var pers st i) lst
      (natVar (absU i)) :=
  LS.ofSim₀ fun _ h => nat_var_refines hrel hinv h

/-- `eq_at1_app` is `eq_at1`'s tail past the universe-argument list. -/
theorem eq_at1_app_refines {pers st lst} {hus : arena.handle.LsIdx}
    {ty a b : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.eq_at1_app pers st hus ty a b = ok o) :
    Sim₀ absEIdx pers lst o
      (do
        let en ← pinEq
        let e ← internE (.const en (absLsIdx hus))
        let e1 ← internE (.app e (absEIdx ty))
        let e2 ← internE (.app e1 (absEIdx a))
        internE (.app e2 (absEIdx b))) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.eq_at1_app]
  skip
  lockstep

open Lockstep in
@[lockstep] theorem eq_at1_app_ls {pers st lst}
    {hus : arena.handle.LsIdx}
    {ty a b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.eq_at1_app pers st hus ty a b) lst
      (do
        let en ← pinEq
        let e ← internE (.const en (absLsIdx hus))
        let e1 ← internE (.app e (absEIdx ty))
        let e2 ← internE (.app e1 (absEIdx a))
        internE (.app e2 (absEIdx b))) :=
  LS.ofSim₀ fun _ h => eq_at1_app_refines hrel hinv h

/-- `eq_at1` ⊑ `eqAt1` — the statements' `Eq.{1} τ a b` former. -/
theorem eq_at1_refines {pers st lst} {ty a b : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.eq_at1 pers st ty a b = ok o) :
    Sim₀ absEIdx pers lst o
      (eqAt1 (absEIdx ty) (absEIdx a) (absEIdx b)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.eq_at1]
  try unfold eqAt1
  lockstep

open Lockstep in
@[lockstep] theorem eq_at1_ls {pers st lst}
    {ty a b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.eq_at1 pers st ty a b) lst
      (eqAt1 (absEIdx ty) (absEIdx a) (absEIdx b)) :=
  LS.ofSim₀ fun _ h => eq_at1_refines hrel hinv h

/-- `cert_hyp1` is the twin's `[h]`. -/
theorem cert_hyp1_refines {h : arena.handle.EIdx} {o}
    (hrun : arena.decl_check.cert_hyp1 h = ok o) :
    absEIdxL o = [absEIdx h] := by
  rw [arena.decl_check.cert_hyp1] at hrun
  simp only [absEIdxL, ConRon.Refine.vec_push_val hrun,
    ConRon.Refine.ExprOps.with_capacity_val, List.nil_append, List.map_cons,
    List.map_nil]

/-- `cert_hyp2` is the twin's `[h₁, h₂]`. -/
theorem cert_hyp2_refines {h1 h2 : arena.handle.EIdx} {o}
    (hrun : arena.decl_check.cert_hyp2 h1 h2 = ok o) :
    absEIdxL o = [absEIdx h1, absEIdx h2] := by
  rw [arena.decl_check.cert_hyp2] at hrun
  obtain ⟨hs1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [absEIdxL, ConRon.Refine.vec_push_val hrun,
    ConRon.Refine.vec_push_val h1, ConRon.Refine.ExprOps.with_capacity_val,
    List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append]

/-- `cert_push` is one cons onto the statement list (§3.4 has no `vec!`), and
the port PUSHES where the twin conses — so the abstraction appends. -/
theorem cert_push_refines {out : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx ×
      arena.handle.EIdx)}
    {hyps : alloc.vec.Vec arena.handle.EIdx} {eq : arena.handle.EIdx} {o}
    (hrun : arena.decl_check.cert_push out hyps eq = ok o) :
    absStmts o = absStmts out ++ [(absEIdxL hyps, absEIdx eq)] := by
  rw [arena.decl_check.cert_push] at hrun
  simp only [absStmts, ConRon.Refine.vec_push_val hrun, List.map_append,
    List.map_cons, List.map_nil, absEIdxL]

open Lockstep in
@[lockstep] theorem cert_hyp1_spec (h : arena.handle.EIdx) :
    LSP (arena.decl_check.cert_hyp1 h) (fun o => absEIdxL o = [absEIdx h]) :=
  fun _ hr => cert_hyp1_refines hr

open Lockstep in
@[lockstep] theorem cert_hyp2_spec (h1 h2 : arena.handle.EIdx) :
    LSP (arena.decl_check.cert_hyp2 h1 h2)
      (fun o => absEIdxL o = [absEIdx h1, absEIdx h2]) :=
  fun _ hr => cert_hyp2_refines hr

open Lockstep in
@[lockstep] theorem cert_push_spec
    (out : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx))
    (hyps : alloc.vec.Vec arena.handle.EIdx) (eq : arena.handle.EIdx) :
    LSP (arena.decl_check.cert_push out hyps eq)
      (fun o => absStmts o = absStmts out ++ [(absEIdxL hyps, absEIdx eq)]) :=
  fun _ hr => cert_push_refines hr

@[lockstep_simp] theorem absStmts_new :
    absStmts (alloc.vec.Vec.new (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) = [] :=
  rfl

/-- `cert_guard` is the twin's `eqAt1 boolTy (← natAp2 bleN a b) r`, the guard
shape all seven branches are written with. -/
theorem cert_guard_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {a b r : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_guard pers st cx a b r = ok o) :
    Sim₀ absEIdx pers lst o
      (certGuard (absCertCtx cx) (absEIdx a) (absEIdx b) (absEIdx r)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_guard]
  try unfold certGuard
  lockstep

open Lockstep in
@[lockstep] theorem cert_guard_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {a b r : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_guard pers st cx a b r) lst
      (certGuard (absCertCtx cx) (absEIdx a) (absEIdx b) (absEIdx r)) :=
  LS.ofSim₀ fun _ h => cert_guard_refines hrel hinv h

/-- `cert_eq` is the twin's `eqAt1 natTy (← natAp2 c x y) rhs`, the
characteristic equation all seven branches are written with. -/
theorem cert_eq_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_eq pers st cx c rhs = ok o) :
    Sim₀ absEIdx pers lst o
      (certEq (absCertCtx cx) (absNIdx c) (absEIdx rhs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_eq]
  try unfold certEq
  lockstep

open Lockstep in
@[lockstep] theorem cert_eq_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    {rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_eq pers st cx c rhs) lst
      (certEq (absCertCtx cx) (absNIdx c) (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => cert_eq_refines hrel hinv h

/-- `cert_halves` is the bitwise branches' `op2 (x/2) (y/2)`, written three
times in the twin. -/
theorem cert_halves_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_halves pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o
      (certHalves (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_halves]
  try unfold certHalves
  lockstep

open Lockstep in
@[lockstep] theorem cert_halves_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_halves pers st cx c) lst
      (certHalves (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_halves_refines hrel hinv h

/-- `cert_rec_rhs` is the `div`/`mod` branch's `c (x - y) y`. -/
theorem cert_rec_rhs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_rec_rhs pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o
      (certRecRhs (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_rec_rhs]
  try unfold certRecRhs
  lockstep

open Lockstep in
@[lockstep] theorem cert_rec_rhs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_rec_rhs pers st cx c) lst
      (certRecRhs (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_rec_rhs_refines hrel hinv h

/-- `cert_lor_rhs` is `|||`'s right-hand side. -/
theorem cert_lor_rhs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_lor_rhs pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o (certLorRhs (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_lor_rhs]
  try unfold certLorRhs
  lockstep

open Lockstep in
@[lockstep] theorem cert_lor_rhs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_lor_rhs pers st cx c) lst
      (certLorRhs (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_lor_rhs_refines hrel hinv h

/-- `cert_xor_rhs` is `^^^`'s right-hand side. -/
theorem cert_xor_rhs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_xor_rhs pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o (certXorRhs (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_xor_rhs]
  try unfold certXorRhs
  lockstep

open Lockstep in
@[lockstep] theorem cert_xor_rhs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_xor_rhs pers st cx c) lst
      (certXorRhs (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_xor_rhs_refines hrel hinv h

/-- `cert_two_eqs` is the six bitwise/shift branches' shared shape: two
one-hypothesis certificates. -/
theorem cert_two_eqs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {h1 h2 r1 r2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_two_eqs pers st cx c h1 h2 r1 r2 = ok o) :
    Sim₀ absStmts pers lst o
      (certTwoEqs (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx r1) (absEIdx r2)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_two_eqs]
  try unfold certTwoEqs
  lockstep

open Lockstep in
@[lockstep] theorem cert_two_eqs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    {h1 h2 r1 r2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_two_eqs pers st cx c h1 h2 r1 r2) lst
      (certTwoEqs (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx r1) (absEIdx r2)) :=
  LS.ofSim₀ fun _ h => cert_two_eqs_refines hrel hinv h

/-- `cert_gcd` — `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`. -/
theorem cert_gcd_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_gcd pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certGcd (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_gcd]
  try unfold certGcd
  lockstep

open Lockstep in
@[lockstep] theorem cert_gcd_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_gcd pers st cx c) lst
      (certGcd (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_gcd_refines hrel hinv h

/-- `cert_shift_left` — `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`. -/
theorem cert_shift_left_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_shift_left pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certShiftLeft (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_shift_left]
  try unfold certShiftLeft
  lockstep

open Lockstep in
@[lockstep] theorem cert_shift_left_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_shift_left pers st cx c) lst
      (certShiftLeft (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_shift_left_refines hrel hinv h

/-- `cert_shift_right` — `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`. -/
theorem cert_shift_right_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_shift_right pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certShiftRight (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_shift_right]
  try unfold certShiftRight
  lockstep

open Lockstep in
@[lockstep] theorem cert_shift_right_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_shift_right pers st cx c) lst
      (certShiftRight (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_shift_right_refines hrel hinv h

/-- `cert_land` — `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`. -/
theorem cert_land_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_land pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certLand (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_land]
  try unfold certLand
  lockstep

open Lockstep in
@[lockstep] theorem cert_land_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_land pers st cx c) lst
      (certLand (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_land_refines hrel hinv h

/-- `cert_lor` — `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`. -/
theorem cert_lor_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_lor pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certLor (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_lor]
  try unfold certLor
  lockstep

open Lockstep in
@[lockstep] theorem cert_lor_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_lor pers st cx c) lst
      (certLor (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_lor_refines hrel hinv h

/-- `cert_xor` — `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`. -/
theorem cert_xor_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_xor pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certXor (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_xor]
  try unfold certXor
  lockstep

open Lockstep in
@[lockstep] theorem cert_xor_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_xor pers st cx c) lst
      (certXor (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_xor_refines hrel hinv h

/-- `cert_div_mod_eqs` — the `div`/`mod` branch's three certificates, at the
four guards already built. -/
theorem cert_div_mod_eqs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {h1 h2 h3 h4 rec_rhs base_rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_div_mod_eqs pers st cx c h1 h2 h3 h4 rec_rhs
      base_rhs = ok o) :
    Sim₀ absStmts pers lst o
      (certDivModEqs (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx h3) (absEIdx h4) (absEIdx rec_rhs) (absEIdx base_rhs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_div_mod_eqs]
  try unfold certDivModEqs
  lockstep

open Lockstep in
@[lockstep] theorem cert_div_mod_eqs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    {h1 h2 h3 h4 rec_rhs base_rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_div_mod_eqs pers st cx c h1 h2 h3 h4 rec_rhs
      base_rhs) lst
      (certDivModEqs (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx h3) (absEIdx h4) (absEIdx rec_rhs) (absEIdx base_rhs)) :=
  LS.ofSim₀ fun _ h => cert_div_mod_eqs_refines hrel hinv h

/-- `cert_div_mod_guards` — the `div`/`mod` branch's four guards. -/
theorem cert_div_mod_guards_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {rec_rhs base_rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_div_mod_guards pers st cx c rec_rhs base_rhs
      = ok o) :
    Sim₀ absStmts pers lst o
      (certDivModGuards (absCertCtx cx) (absNIdx c) (absEIdx rec_rhs) (absEIdx base_rhs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_div_mod_guards]
  try unfold certDivModGuards
  lockstep

open Lockstep in
@[lockstep] theorem cert_div_mod_guards_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    {rec_rhs base_rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_div_mod_guards pers st cx c rec_rhs base_rhs) lst
      (certDivModGuards (absCertCtx cx) (absNIdx c) (absEIdx rec_rhs) (absEIdx base_rhs)) :=
  LS.ofSim₀ fun _ h => cert_div_mod_guards_refines hrel hinv h


/-- `cert_div_mod` — the `div`/`mod` branch, whole. -/
theorem cert_div_mod_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_div_mod pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certDivMod (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_div_mod]
  unfold certDivMod
  -- the twin's `baseRhs` is a pure `if` in argument position (as the port's
  -- `let base_rhs = if …`): decided by hand after the Rust's own test
  lockstep_step
  lockstep_step
  lockstep_step
  · rw [show (absCertCtx cx).divN = absNIdx cx.div_n from rfl, if_pos ‹_›]
    lockstep
  · rw [show (absCertCtx cx).divN = absNIdx cx.div_n from rfl, if_neg ‹_›]
    lockstep

open Lockstep in
@[lockstep] theorem cert_div_mod_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_div_mod pers st cx c) lst
      (certDivMod (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_div_mod_refines hrel hinv h

/-- `div_mod_cert_stmts_at` — the seven-way dispatch over the operation name. -/
theorem div_mod_cert_stmts_at_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_cert_stmts_at pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (divModCertStmtsAt (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_stmts_at]
  try unfold divModCertStmtsAt
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_cert_stmts_at_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.div_mod_cert_stmts_at pers st cx c) lst
      (divModCertStmtsAt (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_stmts_at_refines hrel hinv h

/-- `cert_ctx_names_rest` — the context, through the five bitwise names. -/
theorem cert_ctx_names_rest_refines {pers st lst}
    {nat_ty x y one : arena.handle.EIdx} {ble_n : arena.handle.NIdx}
    {bool_ty b_t b_f z two : arena.handle.EIdx}
    {mod_n div_n add_n mul_n sub_n gcd_n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_ctx_names_rest st nat_ty x y one ble_n bool_ty
      b_t b_f z two mod_n div_n add_n mul_n sub_n gcd_n = ok o) :
    Sim₀ absCertCtx pers lst o
      (certCtxNamesRestFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y)
        (absEIdx one) (absNIdx ble_n) (absEIdx bool_ty) (absEIdx b_t)
        (absEIdx b_f) (absEIdx z) (absEIdx two) (absNIdx mod_n) (absNIdx div_n)
        (absNIdx add_n) (absNIdx mul_n) (absNIdx sub_n) (absNIdx gcd_n)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_ctx_names_rest]
  try unfold certCtxNamesRestFullSpec
  lockstep

open Lockstep in
@[lockstep] theorem cert_ctx_names_rest_ls {pers st lst}
    {nat_ty x y one : arena.handle.EIdx}
    {ble_n : arena.handle.NIdx}
    {bool_ty b_t b_f z two : arena.handle.EIdx}
    {mod_n div_n add_n mul_n sub_n gcd_n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absCertCtx a)
      (arena.decl_check.cert_ctx_names_rest st nat_ty x y one ble_n bool_ty
      b_t b_f z two mod_n div_n add_n mul_n sub_n gcd_n) lst
      (certCtxNamesRestFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y)
        (absEIdx one) (absNIdx ble_n) (absEIdx bool_ty) (absEIdx b_t)
        (absEIdx b_f) (absEIdx z) (absEIdx two) (absNIdx mod_n) (absNIdx div_n)
        (absNIdx add_n) (absNIdx mul_n) (absNIdx sub_n) (absNIdx gcd_n)) :=
  LS.ofSim₀ fun _ h => cert_ctx_names_rest_refines hrel hinv h

/-- `cert_ctx_names` — the context, through the six arithmetic names. -/
theorem cert_ctx_names_refines {pers st lst}
    {nat_ty x y one : arena.handle.EIdx} {ble_n : arena.handle.NIdx}
    {bool_ty b_t b_f z two : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_ctx_names st nat_ty x y one ble_n bool_ty b_t
      b_f z two = ok o) :
    Sim₀ absCertCtx pers lst o
      (certCtxNamesFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y) (absEIdx one)
        (absNIdx ble_n) (absEIdx bool_ty) (absEIdx b_t) (absEIdx b_f) (absEIdx z)
        (absEIdx two)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_ctx_names]
  try unfold certCtxNamesFullSpec
  lockstep

open Lockstep in
@[lockstep] theorem cert_ctx_names_ls {pers st lst}
    {nat_ty x y one : arena.handle.EIdx}
    {ble_n : arena.handle.NIdx}
    {bool_ty b_t b_f z two : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absCertCtx a)
      (arena.decl_check.cert_ctx_names st nat_ty x y one ble_n bool_ty b_t
      b_f z two) lst
      (certCtxNamesFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y) (absEIdx one)
        (absNIdx ble_n) (absEIdx bool_ty) (absEIdx b_t) (absEIdx b_f) (absEIdx z)
        (absEIdx two)) :=
  LS.ofSim₀ fun _ h => cert_ctx_names_refines hrel hinv h


/-- `cert_ctx_nums` — the context, through the numerals `0` and `2`. -/
theorem cert_ctx_nums_refines {pers st lst}
    {nat_ty x y one : arena.handle.EIdx} {ble_n : arena.handle.NIdx}
    {bool_ty b_t b_f : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_ctx_nums pers st nat_ty x y one ble_n bool_ty
      b_t b_f = ok o) :
    Sim₀ absCertCtx pers lst o
      (certCtxNumsFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y) (absEIdx one)
        (absNIdx ble_n) (absEIdx bool_ty) (absEIdx b_t) (absEIdx b_f)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_ctx_nums]
  simp only [certCtxNumsFullSpec, certCtxNumsSpec]
  lockstep

open Lockstep in
@[lockstep] theorem cert_ctx_nums_ls {pers st lst}
    {nat_ty x y one : arena.handle.EIdx}
    {ble_n : arena.handle.NIdx}
    {bool_ty b_t b_f : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absCertCtx a)
      (arena.decl_check.cert_ctx_nums pers st nat_ty x y one ble_n bool_ty
      b_t b_f) lst
      (certCtxNumsFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y) (absEIdx one)
        (absNIdx ble_n) (absEIdx bool_ty) (absEIdx b_t) (absEIdx b_f)) :=
  LS.ofSim₀ fun _ h => cert_ctx_nums_refines hrel hinv h

/-- `cert_ctx_bool` — the context, through the `Bool` type and its two
constructors. -/
theorem cert_ctx_bool_refines {pers st lst}
    {nat_ty x y one : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_ctx_bool pers st nat_ty x y one = ok o) :
    Sim₀ absCertCtx pers lst o
      (certCtxBoolFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y)
        (absEIdx one)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_ctx_bool]
  simp only [certCtxBoolFullSpec, certCtxBoolSpec]
  lockstep

open Lockstep in
@[lockstep] theorem cert_ctx_bool_ls {pers st lst}
    {nat_ty x y one : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absCertCtx a)
      (arena.decl_check.cert_ctx_bool pers st nat_ty x y one) lst
      (certCtxBoolFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y)
        (absEIdx one)) :=
  LS.ofSim₀ fun _ h => cert_ctx_bool_refines hrel hinv h

/-- `cert_ctx` — the twenty-one pinned handles `divModCertStmts` opens with,
bundled because a `let`-bound handle that outlives a `match` arm is a loan the
Aeneas subset will not take (finding 11). -/
theorem cert_ctx_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_ctx pers st = ok o) :
    Sim₀ absCertCtx pers lst o certCtxFullSpec := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_ctx]
  try unfold certCtxFullSpec
  lockstep

open Lockstep in
@[lockstep] theorem cert_ctx_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absCertCtx a)
      (arena.decl_check.cert_ctx pers st) lst
      certCtxFullSpec :=
  LS.ofSim₀ fun _ h => cert_ctx_refines hrel hinv h

/-- **`div_mod_cert_stmts` ⊑ `divModCertStmts`** — the pinned characterization
statements of a pin-certified WF-recursive op, in *open* form over
`x := fvar 0`, `y := fvar 1`.  This is the entry the whole `cert_*` family
exists to build, and the one lemma of the family a caller ever uses. -/
theorem div_mod_cert_stmts_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_cert_stmts pers st c = ok o) :
    Sim₀ absStmts pers lst o (divModCertStmts (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_stmts, divModCertStmts, ← certCtxFullSpec_eq]
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_cert_stmts_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.div_mod_cert_stmts pers st c) lst
      (divModCertStmts (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_stmts_refines hrel hinv h

/-! ### The certificates, checked -/

/-- `div_mod_cert_applied_hyps` is `divModCertApplied`'s hypothesis
application. -/
theorem div_mod_cert_applied_hyps_refines {pers st lst}
    {base : arena.handle.EIdx} {hyps : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_cert_applied_hyps pers st base hyps = ok o) :
    Sim₀ absEIdx pers lst o
      (divModCertAppliedHypsSpec (absEIdx base) (absEIdxL hyps)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_applied_hyps]
  have hl := alloc.vec.Vec.len_val hyps
  simp only [absEIdxL]
  rcases hh : hyps.val with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, r⟩⟩⟩
  all_goals simp only [alloc.vec.Vec.length, hh, List.length_cons, List.length_nil] at hl
  · rw [if_neg (by scalar_tac)]; rw [if_neg (by scalar_tac)]
    exact Lockstep.LS.pure rfl hrel hinv
  · rw [if_pos (by scalar_tac)]; simp only [List.map_cons, List.map_nil, divModCertAppliedHypsSpec]
    lockstep
  · rw [if_neg (by scalar_tac)]; rw [if_pos (by scalar_tac)]
    simp only [List.map_cons, List.map_nil, divModCertAppliedHypsSpec]
    lockstep
  · rw [if_neg (by scalar_tac)]; rw [if_neg (by scalar_tac)]
    exact Lockstep.LS.pure rfl hrel hinv

open Lockstep in
@[lockstep] theorem div_mod_cert_applied_hyps_ls {pers st lst}
    {base : arena.handle.EIdx}
    {hyps : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.div_mod_cert_applied_hyps pers st base hyps) lst
      (divModCertAppliedHypsSpec (absEIdx base) (absEIdxL hyps)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_applied_hyps_refines hrel hinv h

/-- `div_mod_cert_applied` ⊑ `divModCertApplied` — the vendored proof applied
to the statement's free variables. -/
theorem div_mod_cert_applied_refines {pers st lst}
    {proof_s : arena.handle.EIdx} {hyps : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_cert_applied pers st proof_s hyps = ok o) :
    Sim₀ absEIdx pers lst o
      (divModCertApplied (absEIdx proof_s) (absEIdxL hyps)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_applied]
  try unfold divModCertApplied
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_cert_applied_ls {pers st lst}
    {proof_s : arena.handle.EIdx}
    {hyps : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.div_mod_cert_applied pers st proof_s hyps) lst
      (divModCertApplied (absEIdx proof_s) (absEIdxL hyps)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_applied_refines hrel hinv h

/-- `div_mod_cert_guard_rest` — `divModCertGuard`'s tail past the substituted
proof's own guards. -/
theorem div_mod_cert_guard_rest_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {ann_val : arena.handle.EIdx}
    {hyps : alloc.vec.Vec arena.handle.EIdx} {eq_e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.div_mod_cert_guard_rest pers vis st rf c ann_val hyps
      eq_e = ok o) :
    Sim₀ id pers lst o
      (divModCertGuardRestSpec lf (absNIdx c) (absEIdx ann_val)
        (absEIdxL hyps) (absEIdx eq_e)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_guard_rest, divModCertGuardRestSpec]
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_cert_guard_rest_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {hyps : alloc.vec.Vec arena.handle.EIdx}
    {eq_e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.div_mod_cert_guard_rest pers vis st rf c ann_val hyps
      eq_e) lst
      (divModCertGuardRestSpec lf (absNIdx c) (absEIdx ann_val)
        (absEIdxL hyps) (absEIdx eq_e)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_guard_rest_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `div_mod_cert_guard` ⊑ `divModCertGuard`. -/
theorem div_mod_cert_guard_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {ann_val : arena.handle.EIdx}
    {hyps : alloc.vec.Vec arena.handle.EIdx} {eq_e proof : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.div_mod_cert_guard pers vis st rf c ann_val hyps eq_e
      proof = ok o) :
    Sim₀ id pers lst o
      (divModCertGuard lf (absNIdx c) (absEIdx ann_val) (absEIdxL hyps)
        (absEIdx eq_e) (absEIdx proof)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_guard, divModCertGuard]
  simp only [arena.decl_check.ground_guards, arena.decl_check.ground_guards_rest,
    arena.decl_check.div_mod_cert_guard_rest]
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_cert_guard_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {hyps : alloc.vec.Vec arena.handle.EIdx}
    {eq_e proof : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.div_mod_cert_guard pers vis st rf c ann_val hyps eq_e
      proof) lst
      (divModCertGuard lf (absNIdx c) (absEIdx ann_val) (absEIdxL hyps)
        (absEIdx eq_e) (absEIdx proof)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_guard_refines hrel hinv hfe.rel hfe.inv hvis h

attribute [local lockstep_simp] absINatOpPinSet in
/-- `div_mod_cert_proofs` ⊑ `divModCertProofs`. -/
theorem div_mod_cert_proofs_refines {pers st lst}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_cert_proofs st ps c = ok o) :
    Sim₀ absEIdxL pers lst o
      (divModCertProofs (absINatOpPinSet ps) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_proofs, divModCertProofs]
  simp only [arena.decl_check.div_mod_slot, arena.decl_check.div_mod_slot_1,
    arena.decl_check.div_mod_slot_2]
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_cert_proofs_ls {pers st lst}
    {ps : arena.nat_op_pin_set.INatOpPinSet}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.decl_check.div_mod_cert_proofs st ps c) lst
      (divModCertProofs (absINatOpPinSet ps) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_proofs_refines hrel hinv h

theorem absStmtsFrom_cons' (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absStmtsFrom v i = (v.val[i.val].1.val.map absEIdx, absEIdx v.val[i.val].2) ::
      (v.val.drop (i.val + 1)).map (fun p => (p.1.val.map absEIdx, absEIdx p.2)) := by
  simp only [absStmtsFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

theorem absEIdxLFrom_cons' (v : alloc.vec.Vec arena.handle.EIdx)
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absEIdxLFrom v i = absEIdx v.val[i.val] :: (v.val.drop (i.val + 1)).map absEIdx := by
  simp only [absEIdxLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

open Lockstep in
theorem div_mod_certs_guard_go_aux (k : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf}
      (c : arena.handle.NIdx) (ann_val : arena.handle.EIdx)
      (stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx))
      (proofs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize),
      stmts.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf → absU vis = lf.visibleBelow →
      LS pers (fun a b => b = id a)
        (arena.decl_check.div_mod_certs_guard_go pers vis st rf c ann_val stmts proofs i) lst
        (divModCertsGuardGo lf (absNIdx c) (absEIdx ann_val)
          (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) := by
  induction k with
  | zero =>
    intro pers st lst vis rf lf c ann_val stmts proofs i hn hrel hinv hfe hvis
    have hl := alloc.vec.Vec.len_val stmts
    have : absStmtsFrom stmts i = [] := by
      simp only [absStmtsFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [arena.decl_check.div_mod_certs_guard_go, this, divModCertsGuardGo]
    rw [if_pos (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ m ih =>
    intro pers st lst vis rf lf c ann_val stmts proofs i hn hrel hinv hfe hvis
    have hl := alloc.vec.Vec.len_val stmts
    have hl2 := alloc.vec.Vec.len_val proofs
    rw [arena.decl_check.div_mod_certs_guard_go, absStmtsFrom_cons' stmts i (by omega)]
    by_cases hp : i.val < proofs.val.length
    · rw [absEIdxLFrom_cons' proofs i hp, divModCertsGuardGo]
      rw [if_neg (by scalar_tac)]
      dsimp only
      rw [if_neg (by scalar_tac)]
      refine LSP.bind (vec_index_spec _ _) fun p ⟨_, hp⟩ => ?_
      subst hp
      generalize (↑stmts : List _)[↑i] = p
      obtain ⟨hy, eq⟩ := p
      simp only [absStmtsFrom, absEIdxLFrom] at ih
      lockstep
    · have : absEIdxLFrom proofs i = [] := by
        simp only [absEIdxLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
      rw [this]
      simp only [divModCertsGuardGo]
      rw [if_neg (by scalar_tac)]
      rw [if_pos (by scalar_tac)]
      exact LS.pure rfl hrel hinv

/-- `div_mod_certs_guard_go` ⊑ `divModCertsGuardGo` at the cursor. -/
theorem div_mod_certs_guard_go_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {ann_val : arena.handle.EIdx}
    {stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)}
    {proofs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.div_mod_certs_guard_go pers vis st rf c ann_val stmts
      proofs i = ok o) :
    Sim₀ id pers lst o
      (divModCertsGuardGo lf (absNIdx c) (absEIdx ann_val)
        (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) :=
  Lockstep.LS.toSim₀ (div_mod_certs_guard_go_aux _ c ann_val stmts proofs i rfl hrel hinv
    ⟨hfe, hfinv⟩ hvis) hrun

open Lockstep in
@[lockstep] theorem div_mod_certs_guard_go_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)}
    {proofs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.div_mod_certs_guard_go pers vis st rf c ann_val stmts
      proofs i) lst
      (divModCertsGuardGo lf (absNIdx c) (absEIdx ann_val)
        (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) :=
  LS.ofSim₀ fun _ h => div_mod_certs_guard_go_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `div_mod_certs_guard` ⊑ `divModCertsGuard`. -/
theorem div_mod_certs_guard_refines {pers st lst} {vis : Std.U64} {rf lf}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.div_mod_certs_guard pers vis st ps rf c ann_val = ok o) :
    Sim₀ id pers lst o
      (divModCertsGuard (absINatOpPinSet ps) lf (absNIdx c) (absEIdx ann_val)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_certs_guard]
  try unfold divModCertsGuard
  lockstep

theorem div_mod_slot_2_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_slot_2 st c = ok o) :
    Sim₀ absU pers lst o (divModSlot2Spec (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_slot_2]
  try unfold divModSlot2Spec
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_slot_2_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absU a)
      (arena.decl_check.div_mod_slot_2 st c) lst
      (divModSlot2Spec (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_slot_2_refines hrel hinv h
theorem div_mod_slot_1_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_slot_1 st c = ok o) :
    Sim₀ absU pers lst o (divModSlot1Spec (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_slot_1]
  try unfold divModSlot1Spec
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_slot_1_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absU a)
      (arena.decl_check.div_mod_slot_1 st c) lst
      (divModSlot1Spec (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_slot_1_refines hrel hinv h
/-- `div_mod_slot` / `_1` / `_2` — the operation's index in the pin record's
eight-slot family, which the twin spells as a chain of handle comparisons
inside `divModDeclPin` and `divModCertProofs`. -/
theorem div_mod_slot_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_slot st c = ok o) :
    Sim₀ absU pers lst o (divModSlotSpec (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_slot]
  try unfold divModSlotSpec
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_slot_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absU a)
      (arena.decl_check.div_mod_slot st c) lst
      (divModSlotSpec (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_slot_refines hrel hinv h




attribute [local lockstep_simp] absINatOpPinSet in
/-- `div_mod_decl_pin` ⊑ `divModDeclPin`. -/
theorem div_mod_decl_pin_refines {pers st lst}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_decl_pin st ps c = ok o) :
    Sim₀ absEIdx pers lst o
      (divModDeclPin (absINatOpPinSet ps) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_decl_pin, divModDeclPin]
  simp only [arena.decl_check.div_mod_slot, arena.decl_check.div_mod_slot_1,
    arena.decl_check.div_mod_slot_2]
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_decl_pin_ls {pers st lst}
    {ps : arena.nat_op_pin_set.INatOpPinSet}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.div_mod_decl_pin st ps c) lst
      (divModDeclPin (absINatOpPinSet ps) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_decl_pin_refines hrel hinv h

/-- `div_mod_pin_guard` ⊑ `divModPinGuard`. -/
theorem div_mod_pin_guard_refines {pers st lst} {vis : Std.U64} {rf lf}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.div_mod_pin_guard pers vis st ps rf c = ok o) :
    Sim₀ id pers lst o
      (divModPinGuard (absINatOpPinSet ps) lf (absNIdx c)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_pin_guard]
  try unfold divModPinGuard
  lockstep

/-! `check_div_mod_cert_at` / `check_div_mod_cert_tail` are the Rust's split of
one certificate's body; the certificate walk below unfolds them in place (the
twin writes the body inline in `checkDivModCerts`).  Their separate statements
were deleted: `check_div_mod_cert_at`'s named the whole `checkDivModCerts`, guard
included, where the Rust starts past the guard, and nothing else used them. -/

open Lockstep in
theorem check_div_mod_certs_aux (k : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf} {mode : kernel.env.CheckMode}
      (c : arena.handle.NIdx) (ann_val : arena.handle.EIdx)
      (stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx))
      (proofs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize),
      stmts.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf → absU vis = lf.visibleBelow →
      LS pers (fun a b => b = id a)
        (arena.decl_check.check_div_mod_certs pers vis st mode rf c ann_val stmts proofs i) lst
        (checkDivModCerts (ConRon.Refine.absMode mode) lf (absNIdx c) (absEIdx ann_val)
          (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) := by
  induction k with
  | zero =>
    intro pers st lst vis rf lf mode c ann_val stmts proofs i hn hrel hinv hfe hvis
    have hl := alloc.vec.Vec.len_val stmts
    have hl2 := alloc.vec.Vec.len_val proofs
    have : absStmtsFrom stmts i = [] := by
      simp only [absStmtsFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [arena.decl_check.check_div_mod_certs, this]
    rw [if_pos (by scalar_tac)]
    dsimp only
    by_cases hp : i.val < proofs.val.length
    · rw [absEIdxLFrom_cons' proofs i hp]
      simp only [checkDivModCerts]
      rw [if_neg (by scalar_tac), if_pos (by scalar_tac)]
      exact LS.pure rfl hrel hinv
    · have : absEIdxLFrom proofs i = [] := by
        simp only [absEIdxLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
      rw [this, checkDivModCerts, if_pos (by scalar_tac)]
      exact LS.pure rfl hrel hinv
  | succ m ih =>
    intro pers st lst vis rf lf mode c ann_val stmts proofs i hn hrel hinv hfe hvis
    have hl := alloc.vec.Vec.len_val stmts
    have hl2 := alloc.vec.Vec.len_val proofs
    rw [arena.decl_check.check_div_mod_certs, absStmtsFrom_cons' stmts i (by omega)]
    rw [if_neg (by scalar_tac)]
    dsimp only
    rw [if_neg (by scalar_tac)]
    by_cases hp : i.val < proofs.val.length
    · rw [absEIdxLFrom_cons' proofs i hp, checkDivModCerts]
      rw [if_neg (by scalar_tac)]
      refine LSP.bind (vec_index_spec _ _) fun p ⟨_, hp⟩ => ?_
      subst hp
      simp only [arena.decl_check.check_div_mod_cert_at, arena.decl_check.check_div_mod_cert_tail]
      simp only [absStmtsFrom, absEIdxLFrom] at ih
      lockstep
    · have : absEIdxLFrom proofs i = [] := by
        simp only [absEIdxLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
      rw [this]
      simp only [checkDivModCerts]
      rw [if_pos (by scalar_tac)]
      exact LS.pure rfl hrel hinv

/-- `check_div_mod_certs` ⊑ `checkDivModCerts` at the cursor. -/
theorem check_div_mod_certs_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)}
    {proofs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_div_mod_certs pers vis st mode rf c ann_val stmts
      proofs i = ok o) :
    Sim₀ id pers lst o
      (checkDivModCerts (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx ann_val) (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) :=
  Lockstep.LS.toSim₀ (check_div_mod_certs_aux _ c ann_val stmts proofs i rfl hrel hinv
    ⟨hfe, hfinv⟩ hvis) hrun

open Lockstep in
@[lockstep] theorem check_div_mod_certs_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)}
    {proofs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.check_div_mod_certs pers vis st mode rf c ann_val stmts
      proofs i) lst
      (checkDivModCerts (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx ann_val) (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) :=
  LS.ofSim₀ fun _ h => check_div_mod_certs_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_div_mod_pin_certs` — one variant's certificate half. -/
theorem check_div_mod_pin_certs_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx} {ps : arena.nat_op_pin_set.INatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_div_mod_pin_certs pers vis st mode rf c value2 ps
      = ok o) :
    Sim₀ id pers lst o
      (checkDivModPinCertsSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.check_div_mod_pin_certs]
  try unfold checkDivModPinCertsSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_div_mod_pin_certs_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {ps : arena.nat_op_pin_set.INatOpPinSet}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.check_div_mod_pin_certs pers vis st mode rf c value2 ps) lst
      (checkDivModPinCertsSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps)) :=
  LS.ofSim₀ fun _ h => check_div_mod_pin_certs_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_div_mod_pin_at` ⊑ `checkDivModPinAt` — ONE variant attempted. -/
theorem check_div_mod_pin_at_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx} {ps : arena.nat_op_pin_set.INatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_div_mod_pin_at pers vis st mode rf c value2 ps
      = ok o) :
    Sim₀ id pers lst o
      (checkDivModPinAt (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.check_div_mod_pin_at]
  try unfold checkDivModPinAt
  lockstep

open Lockstep in
@[lockstep] theorem check_div_mod_pin_at_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {ps : arena.nat_op_pin_set.INatOpPinSet}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.check_div_mod_pin_at pers vis st mode rf c value2 ps) lst
      (checkDivModPinAt (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps)) :=
  LS.ofSim₀ fun _ h => check_div_mod_pin_at_refines hrel hinv hfe.rel hfe.inv hvis h

/-- The port's four-way step against the twin's, at a returned step.  The
port never returns `Failed` as a step (`check_div_mod_pin_attempt` returns its
`Native` error instead), so that arm relates nothing; a recovered error is
related by its kind, the one thing `AErrSim` fixes. -/
def OrElseRel : arena.checker_base.OrElseStep → OrElseStep → Prop
  | .Matched, .matched => True
  | .Continued, .continued => True
  | .Recovered e, .recovered le => absAErrKind e = lAErrKind le
  | _, _ => False

/-- The attempt's own lockstep lemma, in the shape the seam consumes it: at
ANY tier and state related to the twin's pre-attempt state — the seam runs it
at the frozen tier (task #97-T2-LOCKSTEP D4c).  `check_div_mod_pin_at_refines`
is this statement. -/
def DivModPinAtSim (vis : Std.U64) (rf : arena.env.IFEnv) (lf : IFEnv)
    (mode : kernel.env.CheckMode) (c : arena.handle.NIdx) (value2 : arena.handle.EIdx)
    (ps : arena.nat_op_pin_set.INatOpPinSet) (lst : AState) : Prop :=
  ∀ (pers' : arena.store.PersTier) (st' : arena.monad.AState) o₁,
    AStateRel₀ pers' st' lst → AStateInv pers' st' →
    arena.decl_check.check_div_mod_pin_at pers' vis st' mode rf c value2 ps = ok o₁ →
    Sim₀ id pers' lst o₁
      (checkDivModPinAt (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps))

/-- **`check_div_mod_pin_attempt` ⊑ `orElseAttempt (checkDivModPinAt …)` —
the `orElseAttempt` seam, lockstep** (tasks #97-T2-LOCKSTEP D4, D4b, D4c,
#98-FREEZE).  The ONE place (B) recovers from a thrown error.  Both sides
resume a recovered attempt at the pre-attempt state: the twin because its
error arm has nothing else, the port because it copies the state
(`attempt_snapshot_eq`: the identity in the model) and on `Recovered` moves
the copy back.  The attempt runs inside a declaration bracket, whose store is
frozen and read through the bracket's tier, so the copy is of a store whose
persistent tables are that tier's and not its own — and the attempt runs at
the same tier, `pers`.  Nothing about what the Rust attempt leaves alone is
needed.

One hypothesis, about the callee: `hat`, the attempt itself, lockstep
(`DivModPinAtSim`).

The `lockstep` tactic does not apply: the two programs do the same operations
only up to the error arm, where the twin throws the state away and the port
restores it — which is exactly the step this lemma exists to prove once. -/
theorem check_div_mod_pin_attempt_refines₀ {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx} {ps : arena.nat_op_pin_set.INatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hat : DivModPinAtSim vis rf lf mode c value2 ps lst)
    (hrun : arena.decl_check.check_div_mod_pin_attempt pers vis st mode rf c value2
      ps = ok o) :
    SimRel₀ OrElseRel pers lst o
      (orElseAttempt (checkDivModPinAt (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps))) := by
  unfold arena.decl_check.check_div_mod_pin_attempt at hrun
  unfold SimRel₀ AOutRel₀
  obtain ⟨snap, hs, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := attempt_snapshot_eq hs
  obtain ⟨⟨r, st₁⟩, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hsim := hat _ _ _ hrel hinv ha
  obtain ⟨oes, hoes, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases r with
  | Ok b =>
    obtain ⟨lst', hx, hrel', hinv'⟩ := Sim₀.apply hsim
    simp only [StateT.run, id] at hx
    cases b with
    | true =>
      simp [arena.checker_base.or_else_attempt] at hoes
      subst hoes
      try dsimp only at hrun
      obtain rfl := (Result.ok_injective hrun).symm
      refine ⟨.matched, lst', ?_, trivial, hrel', hinv'⟩
      simp only [StateT.run, orElseAttempt, hx, orElseStepOf]
    | false =>
      simp [arena.checker_base.or_else_attempt] at hoes
      subst hoes
      try dsimp only at hrun
      obtain rfl := (Result.ok_injective hrun).symm
      refine ⟨.continued, lst', ?_, trivial, hrel', hinv'⟩
      simp only [StateT.run, orElseAttempt, hx, orElseStepOf]
  | Err e =>
    have herr := Sim₀.apply_err hsim
    cases e with
    | Native m =>
      simp [arena.checker_base.or_else_attempt] at hoes
      subst hoes
      try dsimp only at hrun
      obtain rfl := (Result.ok_injective hrun).symm
      exact AErrSim.native m
    | NotImplemented m | Invalid m | Internal m =>
      simp [arena.checker_base.or_else_attempt] at hoes
      subst hoes
      simp only [arena.checker_base.attempt_restore, bind_tc_ok] at hrun
      obtain rfl := (Result.ok_injective hrun).symm
      obtain ⟨le, hle, hk⟩ := herr _ rfl
      simp only [StateT.run] at hle
      refine ⟨.recovered le, lst, ?_, ?_, hrel, hinv⟩
      · show orElseAttempt _ lst = _
        unfold orElseAttempt
        rw [hle]
        cases le with
        | native _ => simp at hk
        | _ => simp only [orElseStepOf, attemptRestore_self]
      · show absAErrKind _ = lAErrKind le
        rw [hk]; rfl

/-- `orElseAttempt` never throws: its error arm is a step. -/
theorem orElseAttempt_run_ne_error {att : AM Bool} {s : AState}
    {le : Arena.CheckError} : (orElseAttempt att).run s ≠ .error le := by
  simp only [StateT.run, orElseAttempt]
  cases att s <;> simp

/-- **`check_div_mod_pin_try` — one variant's attempt, then the loop**
(restated lockstep, task #97-T2-LOCKSTEP lane Checker; proved, task
#97-T2-LOCKSTEP D4b).  The Rust function is the loop's body PAST the two
guards, so its twin is `checkDivModPinTrySpec` at the variant `variants[i]`
and the rest of the list, not the whole loop.  The attempt is
`check_div_mod_pin_attempt` (the `orElseAttempt` seam,
`check_div_mod_pin_attempt_refines₀` above), then the four-way `match`.

Two hypotheses, both about callees, so that the loop and this step — one
mutual recursion — can be proved together by an induction on the cursor:
* `hat` — the variant's attempt, lockstep at any tier (`DivModPinAtSim`,
  `check_div_mod_pin_at_refines`);
* `hloop` — the loop at the NEXT cursor, from any related state and for any
  `tried` list (the twin's `tried` is only an error message's text, which
  `AErrSim` does not compare).

The Rust passes `tried` on unchanged after `Continued` and replaces it by
the one reason after `Recovered`, where the twin appends; the list reaches
only the `NotImplemented` message, and Theorem 2 relates an error by its
kind. -/
theorem check_div_mod_pin_try_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {o} {ltried : List String}
    {ps : arena.nat_op_pin_set.INatOpPinSet}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hps : variants.val[i.val]? = some ps)
    (hat : DivModPinAtSim vis rf lf mode c value2 ps lst)
    (hloop : ∀ (st' : arena.monad.AState) (lst' : AState) (i' : Std.Usize)
        (tried' : alloc.vec.Vec Std.U32) (ltried' : List String) o',
      i'.val = i.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
      arena.decl_check.check_div_mod_pin_loop pers vis st' mode rf c value2
        variants i' tried' = ok o' →
      Sim₀ (fun _ : Unit => ()) pers lst' o'
        (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c)
          (absEIdx value2) (absINatOpPinSetLFrom variants i') ltried'))
    (hrun : arena.decl_check.check_div_mod_pin_try pers vis st mode rf c value2
      variants i tried = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkDivModPinTrySpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps)
        (absINatOpPinSetLFrom variants i).tail ltried) := by
  rw [arena.decl_check.check_div_mod_pin_try] at hrun
  obtain ⟨ps', hix, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hps' : ps' = ps := by
    rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at hix
    rw [show variants[i.val]? = variants.val[i.val]? from rfl, hps] at hix
    exact (Result.ok_injective hix).symm
  subst hps'
  obtain ⟨⟨r, st₁⟩, hatt, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hseam := check_div_mod_pin_attempt_refines₀ hrel hinv hat hatt
  unfold SimRel₀ AOutRel₀ at hseam
  have htail : ∀ i' : Std.Usize, i'.val = i.val + 1 →
      absINatOpPinSetLFrom variants i' = (absINatOpPinSetLFrom variants i).tail := by
    intro i' hi'
    simp only [absINatOpPinSetLFrom, ← List.map_tail, List.tail_drop, hi']
  cases r with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    intro k hk
    obtain ⟨le, hx, -⟩ := hseam k hk
    exact absurd hx orElseAttempt_run_ne_error
  | Ok step =>
    obtain ⟨v, lst₁, hx, hR, hrel₁, hinv₁⟩ := hseam
    unfold Sim₀ checkDivModPinTrySpec
    rw [run_bind_ok hx]
    cases step <;> cases v <;> simp only [OrElseRel] at hR
    · obtain rfl := (Result.ok_injective hrun).symm
      exact ⟨lst₁, rfl, hrel₁, hinv₁⟩
    · obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi1v : i1.val = i.val + 1 := by
        have := ConRon.Refine.HashMap.uscalar_add_eq hi1; simpa using this
      rw [← htail i1 hi1v]
      exact hloop _ _ _ _ _ _ hi1v hrel₁ hinv₁ hrun
    · obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨tv, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi1v : i1.val = i.val + 1 := by
        have := ConRon.Refine.HashMap.uscalar_add_eq hi1; simpa using this
      rw [← htail i1 hi1v]
      exact hloop _ _ _ _ _ _ hi1v hrel₁ hinv₁ hrun

open Lockstep in
@[lockstep] theorem div_mod_pin_guard_ls {pers st lst} {vis : Std.U64} {rf lf}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.div_mod_pin_guard pers vis st ps rf c) lst
      (divModPinGuard (absINatOpPinSet ps) lf (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_pin_guard_refines hrel hinv hfe.rel hfe.inv hvis h

open Lockstep in
@[lockstep] theorem div_mod_certs_guard_ls {pers st lst} {vis : Std.U64} {rf lf}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.div_mod_certs_guard pers vis st ps rf c ann_val) lst
      (divModCertsGuard (absINatOpPinSet ps) lf (absNIdx c) (absEIdx ann_val)) :=
  LS.ofSim₀ fun _ h => div_mod_certs_guard_refines hrel hinv hfe.rel hfe.inv hvis h

theorem pinSetFrom_cons (v : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absINatOpPinSetLFrom v i = absINatOpPinSet v.val[i.val] ::
      (v.val.drop (i.val + 1)).map absINatOpPinSet := by
  simp only [absINatOpPinSetLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

theorem pinSetFrom_nil (v : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (i : Std.Usize) (hi : v.val.length ≤ i.val) : absINatOpPinSetLFrom v i = [] := by
  simp only [absINatOpPinSetLFrom]; rw [List.drop_eq_nil_of_le hi]; rfl

open Lockstep in
/-- `check_div_mod_pin_try` in the loop's judgement, at the variant under the
cursor; the loop's own statement at `i + 1` is the hypothesis `hloop` (the two
are one recursion). -/
theorem check_div_mod_pin_try_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {ltried : List String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow)
    (hi : i.val < variants.val.length)
    (hloop : ∀ (st' : arena.monad.AState) (lst' : AState) (i' : Std.Usize)
        (tried' : alloc.vec.Vec Std.U32) (ltried' : List String) o',
      i'.val = i.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
      arena.decl_check.check_div_mod_pin_loop pers vis st' mode rf c value2
        variants i' tried' = ok o' →
      Sim₀ (fun _ : Unit => ()) pers lst' o'
        (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c)
          (absEIdx value2) (absINatOpPinSetLFrom variants i') ltried')) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_div_mod_pin_try pers vis st mode rf c value2
        variants i tried) lst
      (checkDivModPinTrySpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet variants.val[i.val])
        ((variants.val.drop (i.val + 1)).map absINatOpPinSet) ltried) := by
  refine LS.ofSim₀ fun _ h => ?_
  have h1 := check_div_mod_pin_try_refines (ltried := ltried) hrel hinv
    (List.getElem?_eq_getElem hi)
    (fun _ _ _ h1 h2 h3 => check_div_mod_pin_at_refines h1 h2 hfe.rel hfe.inv hvis h3)
    hloop h
  rwa [pinSetFrom_cons variants i hi, List.tail_cons] at h1

theorem checkDivModPinLoop_cons_try (mode : ConLeche.CheckMode) (fe : IFEnv) (c : NIdx)
    (v : EIdx) (ps : INatOpPinSet) (rest : List INatOpPinSet) (tried : List String) :
    checkDivModPinLoop mode fe c v (ps :: rest) tried = (do
      if (← divModPinGuard ps fe c) && (← divModCertsGuard ps fe c v) then
        checkDivModPinTrySpec mode fe c v ps rest tried
      else
        checkDivModPinLoop mode fe c v rest
          (tried ++ [s!"{ps.toolchain}: pin or certificate ground constants absent"])) := by
  rw [checkDivModPinLoop]; rfl

open Lockstep in
theorem check_div_mod_pin_loop_aux (n : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf lf} {mode : kernel.env.CheckMode}
      {c : arena.handle.NIdx} {value2 : arena.handle.EIdx}
      (variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) (i : Std.Usize)
      (tried : alloc.vec.Vec Std.U32) (ltried : List String),
      variants.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf → absU vis = lf.visibleBelow →
      LS pers (fun a b => b = (fun _ : Unit => ()) a)
        (arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2
          variants i tried) lst
        (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c)
          (absEIdx value2) (absINatOpPinSetLFrom variants i) ltried) := by
  induction n with
  | zero =>
    intro pers st lst vis rf lf mode c value2 v i tried ltried hn hrel hinv hfe hvis
    rw [arena.decl_check.check_div_mod_pin_loop, pinSetFrom_nil v i (by omega),
      checkDivModPinLoop]
    have hl := alloc.vec.Vec.len_val v
    rw [if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst vis rf lf mode c value2 v i tried ltried hn hrel hinv hfe hvis
    have hlt : i.val < v.val.length := by omega
    rw [arena.decl_check.check_div_mod_pin_loop, pinSetFrom_cons v i hlt,
      checkDivModPinLoop_cons_try]
    have hl := alloc.vec.Vec.len_val v
    rw [if_neg (by scalar_tac)]
    refine LSP.bind (vec_index_spec _ _) fun p ⟨_, hp⟩ => ?_
    subst hp
    have hT : ∀ {st lst tried ltried}, AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = (fun _ : Unit => ()) a)
          (arena.decl_check.check_div_mod_pin_try pers vis st mode rf c value2 v i tried) lst
          (checkDivModPinTrySpec (ConRon.Refine.absMode mode) lf (absNIdx c)
            (absEIdx value2) (absINatOpPinSet v.val[i.val])
            ((v.val.drop (i.val + 1)).map absINatOpPinSet) ltried) :=
      fun h1 h2 => check_div_mod_pin_try_ls h1 h2 hfe hvis hlt
        fun _ _ i' _ _ _ hi' h3 h4 h5 =>
          LS.toSim₀ (ih (mode := mode) (c := c) (value2 := value2) v i' _ _ (by omega)
            h3 h4 hfe hvis) h5
    lockstep

/-- `check_div_mod_pin_loop` ⊑ `checkDivModPinLoop` at the cursor. -/
theorem check_div_mod_pin_loop_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {o} {ltried : List String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2
      variants i tried = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSetLFrom variants i) ltried) := by
  exact Lockstep.LS.toSim₀
    (check_div_mod_pin_loop_aux _ variants i tried ltried rfl hrel hinv ⟨hfe, hfinv⟩ hvis) hrun

open Lockstep in
/-- The loop, for any twin message list `ltried` (the port's `tried` is the
decline text it extends; the messages are not compared, DESIGN §3.1): the
tactic fixes `ltried` from the goal's twin (`[]` at `checkDivModPin`'s entry),
task #97-T2-TACTIC round 2. -/
@[lockstep] theorem check_div_mod_pin_loop_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {ltried : List String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2
        variants i tried) lst
      (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSetLFrom variants i) ltried) :=
  LS.ofSim₀ fun _ h => check_div_mod_pin_loop_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `bool_ctor_typed` — is this `Bool` constructor stored at the pinned type? -/
theorem bool_ctor_typed_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.decl_check.bool_ctor_typed pers vis st rf2 n = ok o) :
    Sim₀ id pers lst o (boolCtorTypedSpec lf2 (absNIdx n)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.bool_ctor_typed]
  unfold boolCtorTypedSpec boolCtorTyped
  lockstep
  all_goals
    refine Lockstep.LSS.bind (Lockstep.i_constant_info_to_constant_val_lss ‹_› ‹_› _) ?_
      (fun e s' => Lockstep.errArm_ok) (fun a b s' lst1 hR hrel hinv => ?_)
    · rw [i_constant_info_dup_abs ‹arena.env.i_constant_info_dup _ = ok _›]; rfl
    · lockstep

open Lockstep in
@[lockstep] theorem bool_ctor_typed_ls {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.bool_ctor_typed pers vis st rf2 n) lst
      (boolCtorTypedSpec lf2 (absNIdx n)) :=
  LS.ofSim₀ fun _ h => bool_ctor_typed_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `div_mod_env_guard_rest` — `divModEnvGuard`'s tail past the operation's
own dependencies. -/
theorem div_mod_env_guard_rest_refines {pers st lst} {vis : Std.U64} {rf2 lf2} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.decl_check.div_mod_env_guard_rest pers vis st rf2 = ok o) :
    Sim₀ id pers lst o (divModEnvGuardRestSpec lf2) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_env_guard_rest, divModEnvGuardRestSpec_split]
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_env_guard_rest_ls {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.div_mod_env_guard_rest pers vis st rf2) lst
      (divModEnvGuardRestSpec lf2) :=
  LS.ofSim₀ fun _ h => div_mod_env_guard_rest_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `div_mod_env_guard` ⊑ `divModEnvGuard`. -/
theorem div_mod_env_guard_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.decl_check.div_mod_env_guard pers vis st rf2 c = ok o) :
    Sim₀ id pers lst o (divModEnvGuard lf2 (absNIdx c)) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_env_guard]
  try unfold divModEnvGuard
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_env_guard_ls {pers st lst} {vis : Std.U64} {rf2 lf2}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.div_mod_env_guard pers vis st rf2 c) lst
      (divModEnvGuard lf2 (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_env_guard_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_div_mod_pin_at_pre` — `checkDivModPin`'s body at the restricted
environment. -/
theorem check_div_mod_pin_at_pre_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {c : arena.handle.NIdx} {value2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.decl_check.check_div_mod_pin_at_pre pers st mode pins rf2 k_pre c
      value2 = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do checkDivModPinLoop (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre)) (absNIdx c)
            (absEIdx value2) (absINatOpPinSetL pins) []
          pure lf2) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_div_mod_pin_at_pre]
  lockstep

open Lockstep in
@[lockstep] theorem check_div_mod_pin_at_pre_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {c : arena.handle.NIdx} {value2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.decl_check.check_div_mod_pin_at_pre pers st mode pins rf2 k_pre c value2) lst
      (do checkDivModPinLoop (ConRon.Refine.absMode mode) (lf2.restrictTo (absU k_pre))
            (absNIdx c) (absEIdx value2) (absINatOpPinSetL pins) []
          pure lf2) :=
  LS.ofSimRel₀ fun _ h => check_div_mod_pin_at_pre_refines hrel hinv hfe.rel hfe.inv hk h

/-- **`check_div_mod_pin` ⊑ `checkDivModPin`**.  Like `check_reduce_pin`, the
port carries the post-install environment and the counter the install ran at
where the twin carries two environments. -/
theorem check_div_mod_pin_refines {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hk : k_pre.val ≤ rf2.visible_below.val)
    (hrun : arena.decl_check.check_div_mod_pin pers st mode pins rf2 k_pre c = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (do checkDivModPin (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) (lf2.restrictTo (absU k_pre)) lf2
            (absNIdx c)
          pure lf2) := by
  have hfeI : IFEnvRelI rf2 lf2 := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_div_mod_pin, checkDivModPin_split]
  lockstep

open Lockstep in
@[lockstep] theorem check_div_mod_pin_ls {pers st lst} {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {k_pre : Std.U64}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) (hk : k_pre.val ≤ rf2.visible_below.val) :
    LS pers IFEnvRelI
      (arena.decl_check.check_div_mod_pin pers st mode pins rf2 k_pre c) lst
      (do checkDivModPin (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
            (lf2.restrictTo (absU k_pre)) lf2 (absNIdx c)
          pure lf2) :=
  LS.ofSimRel₀ fun _ h => check_div_mod_pin_refines hrel hinv hfe.rel hfe.inv hk h

/-! ## The basis installs -/

/-- `install_basis_decl` ⊑ `installBasisDecl` — a basis install is `fe.push`
and a duplicate test, so the Rust takes no state at all (finding 12's
neighbour). -/
theorem install_basis_decl_refines {lst} {rf lf} {ci : arena.env.IConstantInfo} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hwf : IConstantInfoWF ci)
    (hrun : arena.decl_check.install_basis_decl rf ci = ok o) :
    SimRelR (fun r v => IFEnvRelI r v) lst o
      (installBasisDecl lf (absIConstantInfo ci)) := by
  rw [arena.decl_check.install_basis_decl] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨fo, hfo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hf := ifenv_find_abs (IFEnvInv.coreCtxSelf hfe hfinv) hfo
  have hname := i_constant_info_name_abs hn
  rw [hname] at hf
  rcases fo with _ | c
  · simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true,
      if_false] at hrun
    obtain ⟨rf', hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain rfl := (Result.ok_injective hrun).symm
    obtain ⟨h1, h2⟩ := ifenv_push_refines hfe hfinv hwf hp
    refine ⟨_, ?_, h1, h2⟩
    simp only [Option.map_none] at hf
    simp [installBasisDecl, ← hf]
    rfl
  · simp only [core.option.Option.is_some, Option.isSome_some, if_true] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hrun]
    simp only [Option.map_some] at hf
    intro k hk
    simp only [absAErrKind_invalid, Option.some.injEq] at hk
    subst hk
    refine ⟨.invalid "duplicate declaration", ?_, rfl⟩
    simp [installBasisDecl, ← hf]
    rfl

theorem install_basis_decls_aux (k : Nat) :
    ∀ {lst} {rf lf} (decls : alloc.vec.Vec arena.env.IConstantInfo) (i : Std.Usize) {o},
      decls.val.length - i.val = k → IFEnvRel rf lf → IFEnvInv rf →
      (∀ c ∈ decls.val, IConstantInfoWF c) →
      arena.decl_check.install_basis_decls rf decls i = ok o →
      SimRelR (fun r v => IFEnvRelI r v) lst o
        (installBasisDecls lf (absICILFrom decls i)) := by
  induction k with
  | zero =>
    intro lst rf lf decls i o hn hfe hfinv hwf hrun
    rw [arena.decl_check.install_basis_decls] at hrun
    have hl := alloc.vec.Vec.len_val decls
    rw [if_pos (by scalar_tac)] at hrun
    obtain rfl := (Result.ok_injective hrun).symm
    have : absICILFrom decls i = [] := by
      simp only [absICILFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [this]
    exact ⟨lf, rfl, hfe, hfinv⟩
  | succ m ih =>
    intro lst rf lf decls i o hn hfe hfinv hwf hrun
    rw [arena.decl_check.install_basis_decls] at hrun
    have hl := alloc.vec.Vec.len_val decls
    rw [if_neg (by scalar_tac)] at hrun
    obtain ⟨ii, hii, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨ii1, hii1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hi : i.val < decls.val.length := by omega
    have hx : decls.val[i.val] = ii := by
      have h1 := vec_index_some hii
      rw [List.getElem?_eq_getElem hi] at h1
      exact Option.some_inj.mp h1
    have hcons : absICILFrom decls i =
        absIConstantInfo ii :: (decls.val.drop (i.val + 1)).map absIConstantInfo := by
      simp only [absICILFrom]; rw [List.drop_eq_getElem_cons hi, hx]; rfl
    have hdup := i_constant_info_dup_abs hii1
    have h1 := install_basis_decl_refines (lst := lst) hfe hfinv
      (i_constant_info_dup_wf hii1 (hwf ii (hx ▸ List.getElem_mem hi))) hr
    rw [hdup] at h1
    rw [hcons, installBasisDecls]
    cases r with
    | Ok fe2 =>
      obtain ⟨v, hv, hrel2, hinv2⟩ := h1
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v := ConRon.Refine.Nat.uadd_val hi2
      have ih' := ih (lst := lst) decls i2 (by simp at hi2v; omega) hrel2 hinv2 hwf hrun
      have e2 : absICILFrom decls i2 = (decls.val.drop (i.val + 1)).map absIConstantInfo := by
        simp only [absICILFrom]; congr 2
      rw [e2] at ih'
      revert ih'
      cases o <;> simp only [SimRelR, StateT.run_bind, hv] <;> exact id
    | Err e =>
      obtain rfl := (Result.ok_injective hrun).symm
      intro k hk
      obtain ⟨le, hle, hk2⟩ := h1 k hk
      refine ⟨le, ?_, hk2⟩
      rw [StateT.run_bind, hle]; rfl

/-- `install_basis_decls` ⊑ `installBasisDecls` at the cursor. -/
theorem install_basis_decls_refines {lst} {rf lf}
    {decls : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hwf : ∀ c ∈ decls.val, IConstantInfoWF c)
    (hrun : arena.decl_check.install_basis_decls rf decls i = ok o) :
    SimRelR (fun r v => IFEnvRelI r v) lst o
      (installBasisDecls lf (absICILFrom decls i)) :=
  install_basis_decls_aux _ decls i rfl hfe hfinv hwf hrun


/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.check_div_mod_pin_attempt_refines₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_div_mod_pin_attempt_refines₀

/-- info: 'ConRon.Refine2.orElseAttempt_run_ne_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orElseAttempt_run_ne_error

/-- info: 'ConRon.Refine2.check_div_mod_pin_try_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_div_mod_pin_try_refines

/-- info: 'ConRon.Refine2.cert_hyp1_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cert_hyp1_refines

/-- info: 'ConRon.Refine2.cert_hyp2_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cert_hyp2_refines

/-- info: 'ConRon.Refine2.cert_push_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cert_push_refines

end ConRon.Refine2
