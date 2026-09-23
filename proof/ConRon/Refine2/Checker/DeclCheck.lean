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

/-! ## The standard axioms' gate

`stdAxiomOk` accepts exactly `propext` and `Classical.choice`, each against
its pinned shape and with its supporting family pinned in the environment.
The Rust splits the two arms and their "is the family pinned" prefixes. -/

/-- `eq_basis_pinned` — is the `Eq` basis block installed as pinned? -/
theorem eq_basis_pinned_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.eq_basis_pinned pers vis st rf = ok o) :
    Sim₀ id pers lst o (eqBasisPinnedSpec lf) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- `reduce_elem_ok` ⊑ `reduceElemOk`. -/
theorem reduce_elem_ok_refines {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.reduce_elem_ok pers vis st rf c = ok o) :
    Sim₀ id pers lst o (reduceElemOk lf (absNIdx c)) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  simp only [bind_assoc, am_ite_bind, am_fail_bind]
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
    SimRel₀ (fun r v => IFEnvRel r v) pers lst o
      (checkThmValWitnessSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx value)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_thm_val_witness_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => IFEnvRel r v)
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
  sorry

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

/-- `nat_op_stored_ok_all` ⊑ `natOpStoredOkAll` at the cursor. -/
theorem nat_op_stored_ok_all_refines {pers st lst} {vis : Std.U64} {rf lf}
    {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.nat_op_stored_ok_all pers vis st rf ns i = ok o) :
    Sim₀ id pers lst o
      (natOpStoredOkAll lf (absNIdxLFrom ns i)) := by
  sorry

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
    Sim₀ id pers lst o (natOpGuard lf (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem nat_op_guard_ls {pers st lst} {vis : Std.U64} {rf lf}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.core.nat_op_guard pers vis st rf c) lst
      (natOpGuard lf (absNIdx c)) :=
  LS.ofSim₀ fun _ h => nat_op_guard_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `arena::core::nat_op_deps` ⊑ `natOpDeps` — the operation's dependency list,
pin reads only (`arena::core`'s; stated here for the same reason). -/
theorem nat_op_deps_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_deps st c = ok o) :
    Sim₀ absNIdxL pers lst o (natOpDeps (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem nat_op_deps_ls {pers st lst} {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a)
      (arena.core.nat_op_deps st c) lst (natOpDeps (absNIdx c)) :=
  LS.ofSim₀ fun _ h => nat_op_deps_refines hrel hinv h

/-- `arena::core::nat_op_equations` ⊑ `natOpEquations` — the operation's
recurrence equations, built (`arena::core`'s; stated here for the same
reason). -/
theorem nat_op_equations_refines {pers st lst} {d : Std.U64}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_equations pers st d c = ok o) :
    Sim₀ absEqPairs pers lst o (natOpEquations (absU d) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem nat_op_equations_ls {pers st lst} {d : Std.U64}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEqPairs a)
      (arena.core.nat_op_equations pers st d c) lst
      (natOpEquations (absU d) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => nat_op_equations_refines hrel hinv h

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

/-- `subst_const0_list` ⊑ `substConst0List` at the cursor. -/
theorem subst_const0_list_refines {pers st lst} {n : arena.handle.NIdx}
    {r : arena.handle.EIdx} {hs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize} {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.subst_const0_list pers st n r hs i out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← substConst0List (absNIdx n) (absEIdx r) (absEIdxLFrom hs i)))) := by
  sorry

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
    Sim₀ (fun v => absEqPairs out ++ absEqPairs v) pers lst o
      (do pure (absEqPairs out ++
        (← substConst0Pairs (absNIdx n) (absEIdx r) (absEqPairsFrom eqs i)))) := by
  sorry

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

/-- `consts_resolve_all` ⊑ `constsResolveAll` at the cursor. -/
theorem consts_resolve_all_refines {pers st lst} {vis : Std.U64} {rf lf}
    {hs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.consts_resolve_all pers vis st rf hs i = ok o) :
    Sim₀ id pers lst o
      (constsResolveAll lf (absEIdxLFrom hs i)) := by
  sorry

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

theorem absEqPairsFrom_cons' (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absEqPairsFrom v i = (absEIdx v.val[i.val].1, absEIdx v.val[i.val].2) ::
      (v.val.drop (i.val + 1)).map (fun p => (absEIdx p.1, absEIdx p.2)) := by
  simp only [absEqPairsFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

theorem absEqPairsFrom_nil' (v : alloc.vec.Vec (arena.handle.EIdx × arena.handle.EIdx))
    (i : Std.Usize) (hi : v.val.length ≤ i.val) : absEqPairsFrom v i = [] := by
  simp only [absEqPairsFrom]; rw [List.drop_eq_nil_of_le hi]; rfl

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

/-- `div_mod_attempt_reason` ⊑ `divModAttemptReason` — the decline message of
one variant attempt, as code points.  The `ps` the twin takes is only read for
its toolchain string, which the port has already extracted. -/
theorem div_mod_attempt_reason_refines {e : kernel.core_types.CheckError} {o}
    (hrun : arena.decl_check.div_mod_attempt_reason e = ok o) :
    ∀ ps : INatOpPinSet, ∀ le : Arena.CheckError,
      absAErrKind e = lAErrKind le →
      ConRon.Refine.absString o = divModAttemptReason ps (some le) := by
  sorry

/-! ### The certificate statements — the `CertCtx` family (finding 11) -/

/-- `nat_one` ⊑ `natOne` — the numeral `1` as `Nat.succ Nat.zero`. -/
theorem nat_one_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.nat_one pers st = ok o) :
    Sim₀ absEIdx pers lst o natOne := by
  sorry

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
  sorry

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
  sorry

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

/-- `cert_guard` is the twin's `eqAt1 boolTy (← natAp2 bleN a b) r`, the guard
shape all seven branches are written with. -/
theorem cert_guard_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {a b r : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_guard pers st cx a b r = ok o) :
    Sim₀ absEIdx pers lst o
      (certGuardSpec (absCertCtx cx) (absEIdx a) (absEIdx b) (absEIdx r)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_guard_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {a b r : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_guard pers st cx a b r) lst
      (certGuardSpec (absCertCtx cx) (absEIdx a) (absEIdx b) (absEIdx r)) :=
  LS.ofSim₀ fun _ h => cert_guard_refines hrel hinv h

/-- `cert_eq` is the twin's `eqAt1 natTy (← natAp2 c x y) rhs`, the
characteristic equation all seven branches are written with. -/
theorem cert_eq_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_eq pers st cx c rhs = ok o) :
    Sim₀ absEIdx pers lst o
      (certEqSpec (absCertCtx cx) (absNIdx c) (absEIdx rhs)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_eq_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    {rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_eq pers st cx c rhs) lst
      (certEqSpec (absCertCtx cx) (absNIdx c) (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => cert_eq_refines hrel hinv h

/-- `cert_halves` is the bitwise branches' `op2 (x/2) (y/2)`, written three
times in the twin. -/
theorem cert_halves_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_halves pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o
      (certHalvesSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_halves_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_halves pers st cx c) lst
      (certHalvesSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_halves_refines hrel hinv h

/-- `cert_rec_rhs` is the `div`/`mod` branch's `c (x - y) y`. -/
theorem cert_rec_rhs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_rec_rhs pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o
      (certRecRhsSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_rec_rhs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_rec_rhs pers st cx c) lst
      (certRecRhsSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_rec_rhs_refines hrel hinv h

/-- `cert_lor_rhs` is `|||`'s right-hand side. -/
theorem cert_lor_rhs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_lor_rhs pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o (certLorRhsSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_lor_rhs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_lor_rhs pers st cx c) lst
      (certLorRhsSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_lor_rhs_refines hrel hinv h

/-- `cert_xor_rhs` is `^^^`'s right-hand side. -/
theorem cert_xor_rhs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_xor_rhs pers st cx c = ok o) :
    Sim₀ absEIdx pers lst o (certXorRhsSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_xor_rhs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.decl_check.cert_xor_rhs pers st cx c) lst
      (certXorRhsSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_xor_rhs_refines hrel hinv h

/-- `cert_two_eqs` is the six bitwise/shift branches' shared shape: two
one-hypothesis certificates. -/
theorem cert_two_eqs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {h1 h2 r1 r2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_two_eqs pers st cx c h1 h2 r1 r2 = ok o) :
    Sim₀ absStmts pers lst o
      (certTwoEqsSpec (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx r1) (absEIdx r2)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_two_eqs_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    {h1 h2 r1 r2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_two_eqs pers st cx c h1 h2 r1 r2) lst
      (certTwoEqsSpec (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx r1) (absEIdx r2)) :=
  LS.ofSim₀ fun _ h => cert_two_eqs_refines hrel hinv h

/-- `cert_gcd` — `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`. -/
theorem cert_gcd_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_gcd pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certGcdSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_gcd_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_gcd pers st cx c) lst
      (certGcdSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_gcd_refines hrel hinv h

/-- `cert_shift_left` — `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`. -/
theorem cert_shift_left_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_shift_left pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certShiftLeftSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_shift_left_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_shift_left pers st cx c) lst
      (certShiftLeftSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_shift_left_refines hrel hinv h

/-- `cert_shift_right` — `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`. -/
theorem cert_shift_right_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_shift_right pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certShiftRightSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_shift_right_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_shift_right pers st cx c) lst
      (certShiftRightSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_shift_right_refines hrel hinv h

/-- `cert_land` — `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`. -/
theorem cert_land_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_land pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certLandSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_land_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_land pers st cx c) lst
      (certLandSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_land_refines hrel hinv h

/-- `cert_lor` — `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`. -/
theorem cert_lor_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_lor pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certLorSpec (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_lor]
  try unfold certLorSpec
  lockstep

open Lockstep in
@[lockstep] theorem cert_lor_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_lor pers st cx c) lst
      (certLorSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_lor_refines hrel hinv h

/-- `cert_xor` — `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`. -/
theorem cert_xor_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_xor pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certXorSpec (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_xor]
  try unfold certXorSpec
  lockstep

open Lockstep in
@[lockstep] theorem cert_xor_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_xor pers st cx c) lst
      (certXorSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_xor_refines hrel hinv h

/-- `cert_div_mod_eqs` — the `div`/`mod` branch's three certificates, at the
four guards already built. -/
theorem cert_div_mod_eqs_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {h1 h2 h3 h4 rec_rhs base_rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_div_mod_eqs pers st cx c h1 h2 h3 h4 rec_rhs
      base_rhs = ok o) :
    Sim₀ absStmts pers lst o
      (certDivModEqsSpec (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx h3) (absEIdx h4) (absEIdx rec_rhs) (absEIdx base_rhs)) := by
  sorry

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
      (certDivModEqsSpec (absCertCtx cx) (absNIdx c) (absEIdx h1) (absEIdx h2)
        (absEIdx h3) (absEIdx h4) (absEIdx rec_rhs) (absEIdx base_rhs)) :=
  LS.ofSim₀ fun _ h => cert_div_mod_eqs_refines hrel hinv h
/-- `cert_div_mod_guards` — the `div`/`mod` branch's four guards. -/
theorem cert_div_mod_guards_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {rec_rhs base_rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_div_mod_guards pers st cx c rec_rhs base_rhs
      = ok o) :
    Sim₀ absStmts pers lst o
      (certDivModGuardsSpec (absCertCtx cx) (absNIdx c) (absEIdx rec_rhs) (absEIdx base_rhs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.cert_div_mod_guards]
  try unfold certDivModGuardsSpec
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
      (certDivModGuardsSpec (absCertCtx cx) (absNIdx c) (absEIdx rec_rhs) (absEIdx base_rhs)) :=
  LS.ofSim₀ fun _ h => cert_div_mod_guards_refines hrel hinv h


/-- `cert_div_mod` — the `div`/`mod` branch, whole. -/
theorem cert_div_mod_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_div_mod pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (certDivModSpec (absCertCtx cx) (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem cert_div_mod_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.cert_div_mod pers st cx c) lst
      (certDivModSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => cert_div_mod_refines hrel hinv h

/-- `div_mod_cert_stmts_at` — the seven-way dispatch over the operation name. -/
theorem div_mod_cert_stmts_at_refines {pers st lst} {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_cert_stmts_at pers st cx c = ok o) :
    Sim₀ absStmts pers lst o (divModCertStmtsAtSpec (absCertCtx cx) (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.div_mod_cert_stmts_at]
  try unfold divModCertStmtsAtSpec
  lockstep

open Lockstep in
@[lockstep] theorem div_mod_cert_stmts_at_ls {pers st lst}
    {cx : arena.decl_check.CertCtx}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absStmts a)
      (arena.decl_check.div_mod_cert_stmts_at pers st cx c) lst
      (divModCertStmtsAtSpec (absCertCtx cx) (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_cert_stmts_at_refines hrel hinv h

/-- `cert_ctx_bool` — the context, through the `Bool` type and its two
constructors. -/
theorem cert_ctx_bool_refines {pers st lst}
    {nat_ty x y one : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_ctx_bool pers st nat_ty x y one = ok o) :
    Sim₀ absCertCtx pers lst o
      (certCtxBoolFullSpec (absEIdx nat_ty) (absEIdx x) (absEIdx y)
        (absEIdx one)) := by
  sorry

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
  sorry

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


/-- `cert_ctx` — the twenty-one pinned handles `divModCertStmts` opens with,
bundled because a `let`-bound handle that outlives a `match` arm is a loan the
Aeneas subset will not take (finding 11). -/
theorem cert_ctx_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.cert_ctx pers st = ok o) :
    Sim₀ absCertCtx pers lst o certCtxFullSpec := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- `div_mod_cert_proofs` ⊑ `divModCertProofs`. -/
theorem div_mod_cert_proofs_refines {pers st lst}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_cert_proofs st ps c = ok o) :
    Sim₀ absEIdxL pers lst o
      (divModCertProofs (absINatOpPinSet ps) (absNIdx c)) := by
  sorry

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
        (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) := by
  sorry

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

/-- `div_mod_slot` / `_1` / `_2` — the operation's index in the pin record's
eight-slot family, which the twin spells as a chain of handle comparisons
inside `divModDeclPin` and `divModCertProofs`. -/
theorem div_mod_slot_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_slot st c = ok o) :
    Sim₀ absU pers lst o (divModSlotSpec (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem div_mod_slot_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absU a)
      (arena.decl_check.div_mod_slot st c) lst
      (divModSlotSpec (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_slot_refines hrel hinv h

theorem div_mod_slot_1_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_slot_1 st c = ok o) :
    Sim₀ absU pers lst o (divModSlot1Spec (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem div_mod_slot_1_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absU a)
      (arena.decl_check.div_mod_slot_1 st c) lst
      (divModSlot1Spec (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_slot_1_refines hrel hinv h

theorem div_mod_slot_2_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_slot_2 st c = ok o) :
    Sim₀ absU pers lst o (divModSlot2Spec (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem div_mod_slot_2_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absU a)
      (arena.decl_check.div_mod_slot_2 st c) lst
      (divModSlot2Spec (absNIdx c)) :=
  LS.ofSim₀ fun _ h => div_mod_slot_2_refines hrel hinv h


/-- `div_mod_decl_pin` ⊑ `divModDeclPin`. -/
theorem div_mod_decl_pin_refines {pers st lst}
    {ps : arena.nat_op_pin_set.INatOpPinSet} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.decl_check.div_mod_decl_pin st ps c = ok o) :
    Sim₀ absEIdx pers lst o
      (divModDeclPin (absINatOpPinSet ps) (absNIdx c)) := by
  sorry

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

/-- `check_div_mod_cert_tail` — one certificate's conversion check, past the
applied proof. -/
theorem check_div_mod_cert_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)}
    {proofs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {applied_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_div_mod_cert_tail pers vis st mode rf c ann_val
      stmts proofs i applied_a = ok o) :
    Sim₀ id pers lst o
      (checkDivModCertTailSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx ann_val) (absStmtsFrom stmts i) (absEIdxLFrom proofs i)
        (absEIdx applied_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_div_mod_cert_tail_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)}
    {proofs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {applied_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.decl_check.check_div_mod_cert_tail pers vis st mode rf c ann_val
      stmts proofs i applied_a) lst
      (checkDivModCertTailSpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx ann_val) (absStmtsFrom stmts i) (absEIdxLFrom proofs i)
        (absEIdx applied_a)) :=
  LS.ofSim₀ fun _ h => check_div_mod_cert_tail_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_div_mod_cert_at` — one certificate, whole. -/
theorem check_div_mod_cert_at_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {ann_val : arena.handle.EIdx}
    {stmts : alloc.vec.Vec (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)}
    {proofs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.decl_check.check_div_mod_cert_at pers vis st mode rf c ann_val
      stmts proofs i = ok o) :
    Sim₀ id pers lst o
      (checkDivModCerts (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx ann_val) (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_div_mod_cert_at_ls {pers st lst}
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
      (arena.decl_check.check_div_mod_cert_at pers vis st mode rf c ann_val
      stmts proofs i) lst
      (checkDivModCerts (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx ann_val) (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) :=
  LS.ofSim₀ fun _ h => check_div_mod_cert_at_refines hrel hinv hfe.rel hfe.inv hvis h

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
        (absEIdx ann_val) (absStmtsFrom stmts i) (absEIdxLFrom proofs i)) := by
  sorry

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

/-- **`check_div_mod_pin_attempt` ⊑ `orElseAttempt (checkDivModPinAt …)` —
the `orElseAttempt` seam, lockstep** (task #97-T2-LOCKSTEP D4).  The ONE place
(B) recovers from a thrown error.  Both sides resume a recovered attempt at
the same state now: the twin at the pre-attempt state, the port at the
post-attempt state with the snapshot's memos, caches and scratch tiers put
back, which `attempt_recover_refines₀` relates to it under the port's frame.

Two hypotheses, both about the callee:
* `hat` — the attempt itself, lockstep (`check_div_mod_pin_at`'s Theorem-2
  lemma, another lane's; taken in `Sim₀` form, as the `lockstep` recipe
  takes a callee from another lane);
* `hframe` — on a thrown error, the port's attempt wrote nothing outside the
  memos, the caches and the scratch tiers (`ScratchFrame`, a fact about the
  Rust alone).

The `lockstep` tactic does not apply: the two programs do the same operations
only up to the error arm, where the twin throws the state away and the port
restores it — which is exactly the step this lemma exists to prove once. -/
theorem check_div_mod_pin_attempt_refines₀ {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx} {ps : arena.nat_op_pin_set.INatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hat : ∀ o₁, arena.decl_check.check_div_mod_pin_at pers vis st mode rf c value2 ps
        = ok o₁ →
      Sim₀ id pers lst o₁
        (checkDivModPinAt (ConRon.Refine.absMode mode) lf (absNIdx c)
          (absEIdx value2) (absINatOpPinSet ps)))
    (hframe : ∀ e st₁, arena.decl_check.check_div_mod_pin_at pers vis st mode rf c
        value2 ps = ok (.Err e, st₁) → ScratchFrame st st₁)
    (hrun : arena.decl_check.check_div_mod_pin_attempt pers vis st mode rf c value2
      ps = ok o) :
    SimRel₀ OrElseRel pers lst o
      (orElseAttempt (checkDivModPinAt (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps))) := by
  unfold arena.decl_check.check_div_mod_pin_attempt at hrun
  obtain ⟨snap, hs, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hsnap := attempt_snapshot_refines₀ hrel hinv hs
  obtain ⟨⟨r, st₁⟩, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hsim := hat _ ha
  unfold SimRel₀ AOutRel₀
  cases r with
  | Ok b =>
    obtain ⟨lst', hx, hrel', hinv'⟩ := Sim₀.apply hsim
    simp only [StateT.run, id] at hx
    cases b with
    | true =>
      simp [arena.checker_base.or_else_attempt] at hrun
      subst hrun
      refine ⟨.matched, lst', ?_, trivial, hrel', hinv'⟩
      simp only [StateT.run, orElseAttempt, hx, orElseStepOf]
    | false =>
      simp [arena.checker_base.or_else_attempt] at hrun
      subst hrun
      refine ⟨.continued, lst', ?_, trivial, hrel', hinv'⟩
      simp only [StateT.run, orElseAttempt, hx, orElseStepOf]
  | Err e =>
    have herr := Sim₀.apply_err hsim
    cases e with
    | Native m =>
      simp [arena.checker_base.or_else_attempt] at hrun
      subst hrun
      exact AErrSim.native m
    | NotImplemented m | Invalid m | Internal m =>
      simp [arena.checker_base.or_else_attempt] at hrun
      obtain ⟨st₂, hr, hrun⟩ := hrun
      subst hrun
      obtain ⟨hrel₂, hinv₂⟩ :=
        attempt_recover_refines₀ hrel hinv hsnap (hframe _ _ ha) hr
      obtain ⟨le, hle, hk⟩ := herr _ rfl
      simp only [StateT.run] at hle
      refine ⟨.recovered le, lst, ?_, ?_, hrel₂, hinv₂⟩
      · show orElseAttempt _ lst = _
        unfold orElseAttempt
        rw [hle]
        cases le with
        | native _ => simp at hk
        | _ => simp only [orElseStepOf, attemptRestore_self]
      · show absAErrKind _ = lAErrKind le
        rw [hk]; rfl

/-- **`check_div_mod_pin_try` — one variant's attempt, then the loop**
(restated lockstep, task #97-T2-LOCKSTEP lane Checker).  The Rust function is
the loop's body PAST the two guards, so its twin is `checkDivModPinTrySpec`
at the variant `variants[i]` and the rest of the list, not the whole loop.
The attempt is `check_div_mod_pin_attempt` (the `orElseAttempt` seam,
`check_div_mod_pin_attempt_refines₀` above), then the four-way `match`.

**Open, and blocked on a ruling, not on work**: the seam lemma takes the
Rust attempt's `ScratchFrame` (pins, persistent tiers and flags unchanged),
which nothing proves; DESIGN's lane Checker section prices it against a Rust
change that makes it unnecessary.  The loop and this step are one mutual
recursion, proved together once that is settled. -/
theorem check_div_mod_pin_try_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {o} {ltried : List String}
    {ps : arena.nat_op_pin_set.INatOpPinSet}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hps : variants.val[i.val]? = some ps)
    (hrun : arena.decl_check.check_div_mod_pin_try pers vis st mode rf c value2
      variants i tried = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkDivModPinTrySpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet ps)
        (absINatOpPinSetLFrom variants i).tail ltried) := by
  sorry

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
@[lockstep] theorem check_div_mod_pin_try_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {ltried : List String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow)
    (hi : i.val < variants.val.length) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_div_mod_pin_try pers vis st mode rf c value2
        variants i tried) lst
      (checkDivModPinTrySpec (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSet variants.val[i.val])
        ((variants.val.drop (i.val + 1)).map absINatOpPinSet) ltried) := by
  refine LS.ofSim₀ fun _ h => ?_
  have h1 := check_div_mod_pin_try_refines (ltried := ltried) hrel hinv hfe.rel hfe.inv hvis
    (List.getElem?_eq_getElem hi) h
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
    lockstep
    all_goals
      have ha : a.val = i.val + 1 := by simpa using hP
      unfold absINatOpPinSetLFrom at ih
      rw [← ha]
      exact ih (mode := mode) (c := c) (value2 := value2) v a tried _ (by omega)
        hrel hinv hfe hvis

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
/-- The loop's entry, as `checkDivModPin` calls it: no variant tried yet (the
twin's message list is `[]`, the port's is the decline text it will extend;
the messages are not compared, DESIGN §3.1). -/
@[lockstep] theorem check_div_mod_pin_loop_nil_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx}
    {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2
        variants i tried) lst
      (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c)
        (absEIdx value2) (absINatOpPinSetLFrom variants i) []) :=
  LS.ofSim₀ fun _ h => check_div_mod_pin_loop_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `bool_ctor_typed` — is this `Bool` constructor stored at the pinned type? -/
theorem bool_ctor_typed_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf2 lf2) (hfinv : IFEnvInv rf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.decl_check.bool_ctor_typed pers vis st rf2 n = ok o) :
    Sim₀ id pers lst o (boolCtorTypedSpec lf2 (absNIdx n)) := by
  sorry

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
  sorry

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
  simp only [bind_assoc, am_ite_bind, am_fail_bind]
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
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.install_basis_decl rf ci = ok o) :
    SimRelR (fun r v => IFEnvRel r v) lst o
      (installBasisDecl lf (absIConstantInfo ci)) := by
  sorry

/-- `install_basis_decls` ⊑ `installBasisDecls` at the cursor. -/
theorem install_basis_decls_refines {lst} {rf lf}
    {decls : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.install_basis_decls rf decls i = ok o) :
    SimRelR (fun r v => IFEnvRel r v) lst o
      (installBasisDecls lf (absICILFrom decls i)) := by
  sorry


/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.cert_hyp1_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cert_hyp1_refines

/-- info: 'ConRon.Refine2.cert_hyp2_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cert_hyp2_refines

/-- info: 'ConRon.Refine2.cert_push_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cert_push_refines

end ConRon.Refine2
