/-
# `ConRon.Refine2.ExprOps.FixpointTest` — `fixpoint_induct` on a Theorem 2 walk

Task #99-PFIX's two experiments on `expr_ops::get_app_fn`, kept so that they
stay checked (DESIGN.md `### Task #99-PFIX`).  Nothing imports this file.

1. `get_app_fn_pi`: the existing fuelled lemma (`ExprOps/Read.lean`'s
   `get_app_fn_aux`) re-proved by the Rust function's own `fixpoint_induct`
   (`partial_induct`) instead of an induction on the fuel.  It works, and it
   is no shorter: the fuel is still there, so the twin still needs the
   `cases` on it; and `lockstep` files callee specs under a head CONSTANT
   (`Attr.lean`'s `rustKey?`), so the induction hypothesis, whose head is the
   local `g`, is applied by hand (`LSR.tail_ls`, one line).
2. `get_app_fn_nf*`: the Job-3 shape.  `get_app_fn_nf` is what Aeneas would
   emit if the Rust dropped the walk fuel; `get_app_fn_nf_fuel` relates it to
   the fuelled Rust at every large enough fuel (Rust to Rust, by
   `partial_induct`), and `get_app_fn_nf_refines` composes that with the
   EXISTING fuelled Theorem 2 lemma: the fuel-free Rust's answer is the
   twin's at every large enough twin fuel.
-/
import ConRon.Refine2.ExprOps.Read
import ConRon.Refine.Fixpoint

open Aeneas Aeneas.Std Result
open ConRon.Generated
namespace ConRon.Refine2.ExprOps
open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

theorem get_app_fn_pi {pers : arena.store.PersTier} {st : arena.monad.AState} :
    ∀ (n : Nat) {lst : AState} (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.get_app_fn pers st fuel h) st lst
        (getAppFn n (absEIdx h)) := by
  partial_induct arena.expr_ops.get_app_fn
  intro g ih n
  cases n with
  | zero =>
    intro lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [getAppFn]
    beta_reduce
    lockstep
  | succ m =>
    intro lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [getAppFn]
    beta_reduce
    lockstep
    exact LSR.tail_ls (ih m _ _ (by scalar_tac) ‹_› ‹_›) rfl fun _ _ h => h

/-! ### Job 3 prototype: a FUEL-FREE Rust walk (what Aeneas would emit if
`get_app_fn` dropped its fuel), related to the fuelled twin "eventually". -/

def get_app_fn_nf (pers : arena.store.PersTier) (st : arena.monad.AState)
    (h : arena.handle.EIdx) :
    Result (core.result.Result arena.handle.EIdx kernel.core_types.CheckError) := do
  let i ← arena.handle.EIdx.tag h
  if i = arena.handle.ETAG_APP
  then
    let o ← arena.monad.view_app pers st h
    match o with
    | none => arena.monad.fail_dangling_e arena.handle.EIdx
    | some p =>
      let (e, _) := p
      get_app_fn_nf pers st e
  else
    let e ← arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h
    ok (core.result.Result.Ok e)
partial_fixpoint

/-- The fuel-free Rust agrees with the fuelled Rust at every large enough
fuel: pure Rust-to-Rust, by `partial_induct`. -/
theorem get_app_fn_nf_fuel {pers : arena.store.PersTier} {st : arena.monad.AState} :
    ∀ (h : arena.handle.EIdx) o, get_app_fn_nf pers st h = ok o →
      ∃ F : Nat, ∀ fuel : Std.U64, F ≤ fuel.val →
        arena.expr_ops.get_app_fn pers st fuel h = ok o := by
  partial_induct get_app_fn_nf
  intro g ih h o hrun
  beta_reduce at hrun
  obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  by_cases hti : i = arena.handle.ETAG_APP
  · rw [ite_eq_left hti] at hrun
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases v with
    | none =>
      refine ⟨1, fun fuel hf => ?_⟩
      rw [arena.expr_ops.get_app_fn]
      have : fuel ≠ 0#u64 := by intro h0; subst h0; simp at hf
      simp only [this, ite_false, hi, hti, ite_true, hv, bind_tc_ok]
      exact hrun
    | some p =>
      obtain ⟨e, x⟩ := p
      obtain ⟨F, hF⟩ := ih e o hrun
      refine ⟨F + 1, fun fuel hf => ?_⟩
      rw [arena.expr_ops.get_app_fn]
      have : fuel ≠ 0#u64 := by intro h0; subst h0; simp at hf
      simp only [this, ite_false, hi, hti, ite_true, hv, bind_tc_ok]
      obtain ⟨i1, hi1⟩ : ∃ i1, fuel - 1#u64 = ok i1 ∧ i1.val = fuel.val - 1 := by
        obtain ⟨w, h1, h2⟩ :=
          WP.spec_imp_exists (Std.U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
        exact ⟨w, h1, by scalar_tac⟩
      rw [hi1.1, bind_tc_ok]
      exact hF i1 (by omega)
  · rw [ite_eq_right hti] at hrun
    refine ⟨1, fun fuel hf => ?_⟩
    rw [arena.expr_ops.get_app_fn]
    have : fuel ≠ 0#u64 := by intro h0; subst h0; simp at hf
    simp only [this, ite_false, hi, hti, bind_tc_ok]
    exact hrun

/-- **The Job-3 statement shape**, composed from the rust-to-rust lemma and
the EXISTING fuelled Theorem 2 lemma: the fuel-free Rust's answer is the
twin's at every large enough fuel. -/
theorem get_app_fn_nf_refines {pers : arena.store.PersTier} {st : arena.monad.AState}
    (h : arena.handle.EIdx) o (hrun : get_app_fn_nf pers st h = ok o) :
    ∃ N : Nat, ∀ n, N ≤ n → n < 2 ^ 64 → ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LOut pers (fun a b => b = absEIdx a) o st ((getAppFn n (absEIdx h)).run lst) := by
  obtain ⟨F, hF⟩ := get_app_fn_nf_fuel h o hrun
  refine ⟨F, fun n hn hlt lst hrel hinv => ?_⟩
  have hfu := hF ⟨BitVec.ofNat 64 n⟩ (by simp [UScalar.val]; omega)
  have := get_app_fn_ls hrel hinv ⟨BitVec.ofNat 64 n⟩ h o hfu
  have hv : absU (⟨BitVec.ofNat 64 n⟩ : Std.U64) = n := by
    simp [absU, UScalar.val]; omega
  rwa [hv] at this

end ConRon.Refine2.ExprOps
