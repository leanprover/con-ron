/-
# `ConRon.Refine2.Checker.Base` — Theorem 2 for `arena::checker_base` and `arena::checker_split`

**Task #97-P5-Checker**, deliverable 2 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{checker_base,checker_split}.rs` against
`proof/ConRon/Arena/{CheckerBase,CheckerSplit}.lean`: the declaration
checker's common ground — the per-declaration constant check, the two
memoised guard walks, the declared parameter count — and the install/check
seam of a value declaration.

## Finding 10 — `vis` out of the index is a hypothesis at seventy-one sites

Task #97-P6-6b took the visibility counter OUT of the environment record's
read path: `ifenv_find(vis, fe, n)` takes `vis : u64` beside `fe`, because
reading `fe.visible_below` inside the call forced a copy of the record.  The
twin's `IFEnv.find?` reads `fe.visibleBelow`.  So every statement whose Rust
takes a `vis` parameter carries

    

and it is discharged at the top by `IFEnvRel.visibleBelow` — the call sites
all pass `fe.visible_below` — but must be threaded through the tier, because
inside it `vis` is an ordinary argument.  **Seventy-one statements of this
tier carry it**, and like task #97-P5-0's finding 3
it is a fact about the port's own calling convention rather than a
divergence.

## Where `hvis` is FALSE, and the nine statements that dropped it

**Task #97-P5-Bracket's finding 3, repaired by task #97-P5-Checker round 3.**
*"The call sites all pass `fe.visible_below`"* is true of phase A and false of
phase B.  `arena::checker::check_pending` (`checker.rs:1229`) passes
`pc.vis` — the counter the pending declaration was installed at — against the
WHOLE environment phase A ended with, and that difference is the entire point
of phase B.  Paired with `hfe : IFEnvRel rf lf`, whose third clause is
`lf.visibleBelow = absU rf.visible_below`, the `hvis` above forces
`vis = rf.visible_below`: the statement is then satisfiable nowhere on phase
B's path, and `check_pending_refines` has nothing to be proved from.

The repair moves the restriction from the hypothesis to the CONCLUSION:
`hfe` stays at the unrestricted environment, `hvis` goes, and the twin is
called at `lf.restrictTo (absU vis)` — which is what the twin's own
`checkValueGroup mode (fe.restrictTo pc.vis) pc.vg` says anyway.  The old form
is recovered at a phase-A call site by rewriting with `IFEnvRel.visibleBelow`,
since `lf.restrictTo lf.visibleBelow = lf`.

**Which nine.**  Exactly the functions the port can reach from
`check_value_group` while still threading that `vis`, computed from the Rust
call graph and no wider: `check_value_group`, `check_value_group_value`,
`check_value_group_tail`, `install_value_guards`, `install_value_guards_tail`
(`arena::checker_split`) and `consts_resolve_f_{go,node,two,fast}`
(`arena::checker_base`).  The rest of the closure is `arena::core`'s, where
the same repair is `Refine2/Core/KnotRel.lean`'s `CoreCtx` (lookups only, through the
layer and the tier, so the counter is the `vis` clause's business alone) — and
`arena::prop_read`'s five readers and `arena::env::ifenv_find_proj`, which take the general
form.

Every OTHER `hvis` of this tier and of `Refine2/Checker/DeclCheck.lean` is
sound as it stands: those functions are phase A's, where the port really is
only ever called at `fe.visible_below`.

## What these lemmas wait on

`Refine2/Specs.lean`'s `view`/`intern_e` family, `Refine2/ExprOps/**`
(statements only when this was written; all closed now) and
`Refine2/Core/**` — P5-Core's tier, which is where `annotateCore`,
`inferTypeCore`, `isDefEqCore` and `ensureSortCore` live.  `KnotRel` carries
them here (`Refine2/Checker/KnotHyp.lean`).
-/
import ConRon.Refine2.Checker.Axioms
import ConRon.Refine2.Checker.Spec
import ConRon.Refine2.Checker.Leaves

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (NameWF NamesWF ExprWF)

/-! ## The name-shape tests

`ConLeche/Kernel/Level.lean`'s three `Name` predicates: the declaration front
door is their only reader.  Each is a handle comparison or one `viewN`. -/

private theorem nidx_contains_from_aux (m : Nat) :
    ∀ {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} {n : arena.handle.NIdx}
      {o : Bool}, ns.val.length - i.val = m →
      arena.checker_base.nidx_contains_from ns i n = ok o →
      o = (absNIdxLFrom ns i).contains (absNIdx n) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro ns i n o hm hrun
    rw [arena.checker_base.nidx_contains_from.eq_def] at hrun
    dsimp only at hrun
    have hl := alloc.vec.Vec.len_val ns
    by_cases hge : i ≥ ns.len
    · have hle : ns.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absNIdxLFrom, List.drop_eq_nil_of_le hle]
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [ite_eq_right hge] at hrun
      obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hlt', rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn1
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := nidx_eq2_abs hb
      have hcons : absNIdxLFrom ns i = absNIdx ns.val[i.val] :: (ns.val.drop (i.val + 1)).map absNIdx := by
        simp only [absNIdxLFrom, List.drop_eq_getElem_cons hlt, List.map_cons]
      rw [hcons, List.contains_cons]
      by_cases hc : b = true
      · rw [ite_eq_left hc] at hrun
        rw [← Result.ok_injective hrun]
        subst hc
        have heq : (absNIdx ns.val[i.val] == absNIdx n) = true := hbv.symm
        rw [BEq.comm] at heq
        simp [heq]
      · rw [ite_eq_right hc] at hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (ns.val.length - i2.val) (by omega) rfl hrun
        have hbf : b = false := by simpa using hc
        subst hbf
        have hne : (absNIdx ns.val[i.val] == absNIdx n) = false := hbv.symm
        rw [BEq.comm] at hne
        rw [hrec, hne]
        simp [absNIdxLFrom, hi2v]

/-- `nidx_contains_from` is `ns.contains n` from the cursor on. -/
theorem nidx_contains_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {n : arena.handle.NIdx} {o : Bool}
    (hrun : arena.checker_base.nidx_contains_from ns i n = ok o) :
    o = (absNIdxLFrom ns i).contains (absNIdx n) :=
  nidx_contains_from_aux _ rfl hrun

/-- `arena::core::nat_op_names` ⊑ `natOpNames` — the seven structural `Nat`
operations, as seven pin reads (task #97-P5-Top: a child of
`install_step_defn_refines`; the function is `arena::core`'s, but no tier had
stated it). -/
theorem nat_op_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_names st = ok o) :
    Sim₀ absNIdxL pers lst o natOpNames := by
  unfold natOpNames
  rw [arena.core.nat_op_names] at hrun
  unfold Sim₀
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_pred_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_nat_pred_refines hrel hinv hr0
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natPredName) hS0)
  | Ok a0 =>
  rw [pin_ok (tw := natPredName) hS0]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_add_name] at hq1
  obtain ⟨r1, hr1, hq1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq1
  have hS1 := pin_nat_add_refines hrel hinv hr1
  obtain rfl := (Result.ok_injective hq1).symm
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natAddName) hS1)
  | Ok a1 =>
  rw [pin_ok (tw := natAddName) hS1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_sub_name] at hq2
  obtain ⟨r2, hr2, hq2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq2
  have hS2 := pin_nat_sub_refines hrel hinv hr2
  obtain rfl := (Result.ok_injective hq2).symm
  cases r2 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natSubName) hS2)
  | Ok a2 =>
  rw [pin_ok (tw := natSubName) hS2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_mul_name] at hq3
  obtain ⟨r3, hr3, hq3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq3
  have hS3 := pin_nat_mul_refines hrel hinv hr3
  obtain rfl := (Result.ok_injective hq3).symm
  cases r3 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natMulName) hS3)
  | Ok a3 =>
  rw [pin_ok (tw := natMulName) hS3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_pow_name] at hq4
  obtain ⟨r4, hr4, hq4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq4
  have hS4 := pin_nat_pow_refines hrel hinv hr4
  obtain rfl := (Result.ok_injective hq4).symm
  cases r4 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natPowName) hS4)
  | Ok a4 =>
  rw [pin_ok (tw := natPowName) hS4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_beq_name] at hq5
  obtain ⟨r5, hr5, hq5⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq5
  have hS5 := pin_nat_beq_refines hrel hinv hr5
  obtain rfl := (Result.ok_injective hq5).symm
  cases r5 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natBeqName) hS5)
  | Ok a5 =>
  rw [pin_ok (tw := natBeqName) hS5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_ble_name] at hq6
  obtain ⟨r6, hr6, hq6⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq6
  have hS6 := pin_nat_ble_refines hrel hinv hr6
  obtain rfl := (Result.ok_injective hq6).symm
  cases r6 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natBleName) hS6)
  | Ok a6 =>
  rw [pin_ok (tw := natBleName) hS6]
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w1, hw1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w2, hw2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w3, hw3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w4, hw4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w5, hw5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w6, hw6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have hv : w6.val = [a0, a1, a2, a3, a4, a5, a6] := by
    rw [push_nidx_val hw6, push_nidx_val hw5, push_nidx_val hw4, push_nidx_val hw3, push_nidx_val hw2, push_nidx_val hw1, push_nidx_val hw0]
    rfl
  refine ⟨lst, ?_, hrel, hinv⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

/-- `arena::core::nat_div_mod_names` ⊑ `natDivModNames` — the eight pinned
well-founded operations, as eight pin reads (task #97-P5-Top, as above). -/
theorem nat_div_mod_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_div_mod_names st = ok o) :
    Sim₀ absNIdxL pers lst o natDivModNames := by
  unfold natDivModNames
  rw [arena.core.nat_div_mod_names] at hrun
  unfold Sim₀
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_div_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_nat_div_refines hrel hinv hr0
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natDivName) hS0)
  | Ok a0 =>
  rw [pin_ok (tw := natDivName) hS0]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_mod_name] at hq1
  obtain ⟨r1, hr1, hq1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq1
  have hS1 := pin_nat_mod_refines hrel hinv hr1
  obtain rfl := (Result.ok_injective hq1).symm
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natModName) hS1)
  | Ok a1 =>
  rw [pin_ok (tw := natModName) hS1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_gcd_name] at hq2
  obtain ⟨r2, hr2, hq2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq2
  have hS2 := pin_nat_gcd_refines hrel hinv hr2
  obtain rfl := (Result.ok_injective hq2).symm
  cases r2 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natGcdName) hS2)
  | Ok a2 =>
  rw [pin_ok (tw := natGcdName) hS2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_land_name] at hq3
  obtain ⟨r3, hr3, hq3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq3
  have hS3 := pin_nat_land_refines hrel hinv hr3
  obtain rfl := (Result.ok_injective hq3).symm
  cases r3 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natLandName) hS3)
  | Ok a3 =>
  rw [pin_ok (tw := natLandName) hS3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_lor_name] at hq4
  obtain ⟨r4, hr4, hq4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq4
  have hS4 := pin_nat_lor_refines hrel hinv hr4
  obtain rfl := (Result.ok_injective hq4).symm
  cases r4 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natLorName) hS4)
  | Ok a4 =>
  rw [pin_ok (tw := natLorName) hS4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_xor_name] at hq5
  obtain ⟨r5, hr5, hq5⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq5
  have hS5 := pin_nat_xor_refines hrel hinv hr5
  obtain rfl := (Result.ok_injective hq5).symm
  cases r5 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natXorName) hS5)
  | Ok a5 =>
  rw [pin_ok (tw := natXorName) hS5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_shift_left_name] at hq6
  obtain ⟨r6, hr6, hq6⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq6
  have hS6 := pin_nat_shift_left_refines hrel hinv hr6
  obtain rfl := (Result.ok_injective hq6).symm
  cases r6 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natShiftLeftName) hS6)
  | Ok a6 =>
  rw [pin_ok (tw := natShiftLeftName) hS6]
  obtain ⟨q7, hq7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_shift_right_name] at hq7
  obtain ⟨r7, hr7, hq7⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq7
  have hS7 := pin_nat_shift_right_refines hrel hinv hr7
  obtain rfl := (Result.ok_injective hq7).symm
  cases r7 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natShiftRightName) hS7)
  | Ok a7 =>
  rw [pin_ok (tw := natShiftRightName) hS7]
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w1, hw1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w2, hw2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w3, hw3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w4, hw4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w5, hw5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w6, hw6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w7, hw7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have hv : w7.val = [a0, a1, a2, a3, a4, a5, a6, a7] := by
    rw [push_nidx_val hw7, push_nidx_val hw6, push_nidx_val hw5, push_nidx_val hw4, push_nidx_val hw3, push_nidx_val hw2, push_nidx_val hw1, push_nidx_val hw0]
    rfl
  refine ⟨lst, ?_, hrel, hinv⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

private theorem name_nodup_from_aux {ns : alloc.vec.Vec arena.handle.NIdx} (m : Nat) :
    ∀ {i : Std.Usize} {o : Bool}, ns.val.length - i.val = m →
      arena.checker_base.name_nodup_from ns i = ok o →
      o = nameNodup (absNIdxLFrom ns i) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i o hm hrun
    rw [arena.checker_base.name_nodup_from.eq_def] at hrun
    dsimp only at hrun
    have hl := alloc.vec.Vec.len_val ns
    by_cases hge : i ≥ ns.len
    · have hle : ns.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absNIdxLFrom, List.drop_eq_nil_of_le hle, nameNodup]
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [ite_eq_right hge] at hrun
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      obtain ⟨c, hc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨_, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hc
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := nidx_contains_from_refines hb
      have hcons : absNIdxLFrom ns i = absNIdx ns.val[i.val] :: absNIdxLFrom ns i2 := by
        simp only [absNIdxLFrom, List.drop_eq_getElem_cons hlt, List.map_cons, hi2v]
      rw [hcons, nameNodup, ← hbv]
      by_cases hbt : b = true
      · rw [ite_eq_left hbt] at hrun
        rw [← Result.ok_injective hrun, hbt]
        rfl
      · rw [ite_eq_right hbt] at hrun
        have hrec := ih (ns.val.length - i2.val) (by omega) rfl hrun
        have hbf : b = false := by simpa using hbt
        rw [hrec, hbf]
        rfl

/-- `name_nodup_from` ⊑ `nameNodup` from the cursor on. -/
theorem name_nodup_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.checker_base.name_nodup_from ns i = ok o) :
    o = nameNodup (absNIdxLFrom ns i) :=
  name_nodup_from_aux _ rfl hrun

/-- `name_nodup` ⊑ `nameNodup` — no duplicates in a list of name HANDLES.  A
name comparison is a handle comparison, which is sound because `denoteN` is
injective (DESIGN §8.3 makes exactness a soundness obligation for exactly this
reason). -/
theorem name_nodup_refines {ns : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (hrun : arena.checker_base.name_nodup ns = ok o) :
    o = nameNodup (absNIdxL ns) := by
  rw [arena.checker_base.name_nodup] at hrun
  have := name_nodup_from_refines hrun
  simpa [absNIdxLFrom, absNIdxL] using this


/-! ## `arena::core::consts_resolve` — the plain walk the guard walk's leaves call

No tier had stated `arena::core::consts_resolve` (the Core knot does not call
it; the checker's guard walk hands its leaf arms to it).  The Rust splits the
two literal arms into `nat_trio_stored`/`str_support_stored`, the twin writes
their pin reads inline: the SAME reads in the same order, so the twin side is
two transcriptions (`natTrioStoredSpec`, `strSupportStoredSpec`) and one
equation (`constsResolve_succ`) — a factoring difference, not a divergence. -/

/-- The `Nat` literal arm's three pin reads and probes. -/
def natTrioStoredSpec (fe : IFEnv) : AM Bool := do
  let nt ← pinNat
  let nz ← pinNatZero
  let ns ← pinNatSucc
  pure ((fe.find? nt).isSome && (fe.find? nz).isSome && (fe.find? ns).isSome)

/-- The `String` literal arm's seven further pin reads and probes. -/
def strSupportStoredSpec (fe : IFEnv) : AM Bool := do
  let st ← pinString
  let sl ← pinStringOfList
  let li ← pinList
  let ln ← pinListNil
  let lc ← pinListCons
  let ch ← pinChar
  let co ← pinCharOfNat
  pure ((fe.find? st).isSome && (fe.find? sl).isSome && (fe.find? li).isSome &&
    (fe.find? ln).isSome && (fe.find? lc).isSome && (fe.find? ch).isSome &&
    (fe.find? co).isSome)

/-- `constsResolve` one step in, with the literal arms as the two transcriptions. -/
theorem constsResolve_succ (fe : IFEnv) (fuel : Nat) (h : EIdx) :
    constsResolve fe (fuel + 1) h = (do
      match ← view h with
      | .bvar _ | .sort _ => pure true
      | .lit (.natVal _) => natTrioStoredSpec fe
      | .lit (.strVal _) => do
        let x ← natTrioStoredSpec fe
        let y ← strSupportStoredSpec fe
        pure (x && y)
      | .const n _ => pure (fe.find? n).isSome
      | .fvar _ ty => constsResolve fe fuel ty
      | .app f a => do
        let x ← constsResolve fe fuel f
        if x then constsResolve fe fuel a else pure false
      | .lam ty body | .forallE ty body => do
        let x ← constsResolve fe fuel ty
        if x then constsResolve fe fuel body else pure false
      | .letE ty val body => do
        let x ← constsResolve fe fuel ty
        if !x then pure false else do
          let y ← constsResolve fe fuel val
          if y then constsResolve fe fuel body else pure false
      | .proj s _ sub => do
        if (fe.find? s).isSome then constsResolve fe fuel sub else pure false) := by
  rw [constsResolve]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro v
  cases v with
  | lit l =>
    cases l with
    | natVal _ => rfl
    | strVal _ =>
      simp only [natTrioStoredSpec, strSupportStoredSpec, bind_assoc, pure_bind,
        Bool.and_assoc]
  | _ => rfl

namespace Lockstep

/-- `arena::core::stored` is an index probe: the twin's `find?` test. -/
@[lockstep] theorem stored_spec {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (n : arena.handle.NIdx) (hctx : CoreCtx pers rf lf) :
    LSP (arena.core.stored pers rf n)
      (fun b => TwinEq ((lf.find? (absNIdx n)).isSome) b) := by
  intro b h
  rw [arena.core.stored] at h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hf := ifenv_find_abs hctx ho
  show (lf.find? (absNIdx n)).isSome = b
  rw [← hf]
  cases o with
  | none => simp only [Result.ok.injEq] at h; subst h; rfl
  | some _ => simp only [Result.ok.injEq] at h; subst h; rfl

@[lockstep] theorem nat_trio_stored_ls {pers st lst} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers rf lf) :
    LS pers (fun a b => b = id a) (arena.core.nat_trio_stored pers st rf) lst
      (natTrioStoredSpec lf) := by
  rw [arena.core.nat_trio_stored, natTrioStoredSpec]
  lockstep

@[lockstep] theorem str_support_stored_ls {pers st lst} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers rf lf) :
    LS pers (fun a b => b = id a) (arena.core.str_support_stored pers st rf) lst
      (strSupportStoredSpec lf) := by
  rw [arena.core.str_support_stored, strSupportStoredSpec]
  lockstep

end Lockstep

theorem consts_resolve_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {rf : arena.env.IFEnv} {lf : IFEnv}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → CoreCtx pers rf lf → AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a) (arena.core.consts_resolve pers st rf fuel h)
        lst (constsResolve lf n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rf lf fuel h hn hctx hrel hinv
    rw [arena.core.consts_resolve, constsResolve]
    lockstep
  | succ m ih =>
    intro pers st lst rf lf fuel h hn hctx hrel hinv
    rw [arena.core.consts_resolve, constsResolve_succ, strSupportStoredSpec]
    lockstep

/-- **`arena::core::consts_resolve` ⊑ `constsResolve`**. -/
@[lockstep] theorem Lockstep.consts_resolve_ls {pers st lst} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers rf lf) (fuel : Std.U64) (h : arena.handle.EIdx) :
    Lockstep.LS pers (fun a b => b = id a) (arena.core.consts_resolve pers st rf fuel h)
      lst (constsResolve lf (absU fuel) (absEIdx h)) :=
  consts_resolve_aux _ fuel h rfl hctx hrel hinv

/-! ## The two memoised guard walks

Both thread a `HashMap2<EIdx, bool>` BESIDE the `Result` (`(Result bool,
AState, memo)` / `(Result bool, memo)`): the shared tactic's `LSM` (state walk)
and `LSRM` (reader) judgements, at `BoolMemoR` — the answer equal, the memos
related.  Each is a fuel induction whose two cases are one `lockstep` each,
the port's node/two/binder helpers unfolded in place (task #97-T2-LOCKSTEP
lane Checker Base/Top round 2). -/

namespace Lockstep

/-- The answer-and-memo relation of the tier's `Bool`-memo walks. -/
abbrev BoolMemoR (p : Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (b : Bool × Std.HashMap EIdx Bool) : Prop :=
  b.1 = p.1 ∧ ExprOps.LMemoRel p.2 b.2

end Lockstep

section MemoWalks
open Lockstep

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

@[lockstep] theorem memo_b_get_twin {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {k : arena.handle.EIdx} (hm : ExprOps.LMemoRel rm lm) :
    LSP (arena.checker_base.memo_b_get rm k) (fun o => TwinEq (lm[absEIdx k]?) o) :=
  fun _ h => (memo_b_get_refines hm h).symm

/-- `consts_resolve_f_go` ⊑ `constsResolveFGo`, by induction on the fuel, at
any twin environment the port's `(vis, rf)` is a `CoreCtx` of (finding 10's
`vis`: the caller passes `lf.restrictTo (absU vis)`). -/
theorem consts_resolve_f_go_aux (n : Nat) :
    ∀ {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (lm : Std.HashMap EIdx Bool)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers rf lf →
      ExprOps.LMemoRel rm lm →
      LSM pers BoolMemoR (arena.checker_base.consts_resolve_f_go pers st rf rm fuel h) lst
        (constsResolveFGo lf lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rf lf rm lm fuel h hn hrel hinv hctx hm
    rw [arena.checker_base.consts_resolve_f_go, constsResolveFGo]
    lockstep
  | succ m ih =>
    intro pers st lst rf lf rm lm fuel h hn hrel hinv hctx hm
    rw [arena.checker_base.consts_resolve_f_go, constsResolveFGo]
    unfold arena.checker_base.consts_resolve_f_node arena.checker_base.consts_resolve_f_two
    lockstep

@[lockstep] theorem consts_resolve_f_go_ls {pers st lst} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx pers rf lf)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSM pers BoolMemoR (arena.checker_base.consts_resolve_f_go pers st rf rm fuel h) lst
      (constsResolveFGo lf lm (absU fuel) (absEIdx h)) :=
  consts_resolve_f_go_aux _ rm lm fuel h rfl hrel hinv hctx hm

/-- **`arena::core_state::take_walk_memo`** (task #97-PERF-WALKMEMO): the
table it hands the walk is empty and well formed — the twin's `∅` — and the
one it leaves in the state's slot is well formed.  Either branch of nanoda's
guard: a fresh `HashMap::new()`, or the parked table through `reset_map`. -/
theorem take_walk_memo_spec {K V : Type} [DecidableEq K]
    {HashableInst : ron.hashmap.Hashable K} {slot m slot' : ron.hashmap2.HashMap2 K V}
    (hinv : ConRon.Refine.HashMap2.Inv HashableInst slot)
    (h : arena.core_state.take_walk_memo slot = ok (m, slot')) :
    ConRon.Refine.HashMap2.Inv HashableInst m ∧ (∀ k, ConRon.Refine.HashMap2.toFun m k = none) ∧ ConRon.Refine.HashMap2.Inv HashableInst slot' := by
  rw [arena.core_state.take_walk_memo] at h
  obtain ⟨hm, hnew, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hi, -, hn⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := HashableInst) hnew
  simp only [core.mem.replace] at h
  obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    exact ⟨hi, hn, hi⟩
  · obtain ⟨m1, hm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    rw [arena.core_state.reset_map] at hm1
    obtain ⟨hi1, -, hn1⟩ := ConRon.Refine.HashMap2.clear_fit_refines hinv hm1
    exact ⟨hi1, hn1, hi⟩

/-- The walk's starting memo, from `take_walk_memo`: related to the twin's `∅`. -/
theorem take_walk_memo_lmemo {slot m slot' : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    (hinv : ConRon.Refine.HashMap2.Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable slot)
    (h : arena.core_state.take_walk_memo slot = ok (m, slot')) :
    ExprOps.LMemoRel m ∅ ∧ ConRon.Refine.HashMap2.Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable slot' :=
  have H := take_walk_memo_spec hinv h
  ⟨⟨ConRon.Refine.HashMap2.RelOn_empty H.2.1, H.1⟩, H.2.2⟩

/-- The twin's `pure (← w).1`, run: the walk's run, its memo dropped. -/
theorem run_fst_eq {β M : Type} (w : AM (β × M)) (lst : AState) :
    (do pure (← w).1 : AM β).run lst = (w.run lst) >>= fun p => .ok (p.1.1, p.2) := by
  simp only [StateT.run_bind, StateT.run_pure]
  rcases w.run lst with _ | ⟨⟨b, mm⟩, l⟩ <;> rfl

/-- `consts_resolve_f_fast` ⊑ `constsResolveFFast` — one memoised DAG walk,
which is what every front door below calls.  The walk's memo is the state's
parked `crf_c` table, moved out and emptied by `take_walk_memo` and put back
afterwards (task #97-PERF-WALKMEMO); `MemosRel` has no clause for it, so the
two state updates are invisible to `AStateRel₀`, and `MemosInv.crfC` is
carried by the walk's own memo relation. -/
@[lockstep] theorem consts_resolve_f_fast_ls {pers st lst}
    {rf lf}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.consts_resolve_f_fast pers st rf e) lst
      (constsResolveFFast lf (absEIdx e)) := by
  have hctx := IFEnvInv.coreCtx hfe.rel hfe.inv
  intro o st' hrun
  rw [arena.checker_base.consts_resolve_f_fast] at hrun
  obtain ⟨⟨m, hm⟩, htake, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hml, hhm⟩ := take_walk_memo_lmemo hinv.memos.crfC htake
  obtain ⟨⟨r, st1, m1⟩, hgo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
  have hw := LSM.apply (consts_resolve_f_go_ls
    (st := { st with memos := { st.memos with crf_c := hm } })
    ⟨hrel.store, { hrel.memos with }, hrel.caches, hrel.pins⟩
    ⟨hinv.store, { hinv.memos with crfC := hhm }, hinv.caches⟩ hctx hml
    arena.core.CORE_WALK_FUEL e) hgo
  rw [core_walk_fuel_abs] at hw
  rw [constsResolveFFast, run_fst_eq]
  cases r with
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h3, h4⟩ := hw
    exact ⟨b.1, lst', by rw [hx]; rfl, hR.1, ⟨h3.store, { h3.memos with }, h3.caches, h3.pins⟩,
      ⟨h4.store, { h4.memos with crfC := hR.2.2 }, h4.caches⟩⟩
  | Err err =>
    exact AErrSim.trans hw (fun le hle => by rw [hle]; rfl)

@[lockstep] theorem level_all_params_defined_twin {params : alloc.vec.Vec kernel.name.Name}
    {l : kernel.level.Level} (hp : NamesWF params) (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.all_params_defined params l)
      (fun b => TwinEq (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params)
        (ConRon.Refine.absLevel l)) b) :=
  fun b h => (ConRon.Refine.ExprOps.all_params_defined_refines hp l hl b h).symm

theorem all_params_defined_list_aux {params : alloc.vec.Vec kernel.name.Name}
    {ls : alloc.vec.Vec kernel.level.Level} (hp : NamesWF params) (hl : ConRon.Refine.LevelsWF ls) :
    ∀ (k : Nat) (i : Std.Usize) (o : Bool), ls.val.length - i.val = k →
      arena.checker_base.all_params_defined_list params ls i = ok o →
      o = (absLevelLFrom ls i).all
        (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params)) := by
  intro k
  induction k with
  | zero =>
    intro i o hk h
    rw [arena.checker_base.all_params_defined_list] at h
    have := alloc.vec.Vec.len_val ls
    rw [ite_eq_left (by scalar_tac)] at h
    rw [← Result.ok_injective h, absLevelLFrom, List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ k ih =>
    intro i o hk h
    rw [arena.checker_base.all_params_defined_list] at h
    have := alloc.vec.Vec.len_val ls
    rw [ite_eq_right (by scalar_tac)] at h
    have hlt : i.val < ls.val.length := by omega
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hxv⟩ := ExprOps.vecIndexAt hx
    obtain ⟨b, hbv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hxw : ConRon.Refine.LevelWF x := hxv ▸ hl _ (List.getElem_mem hb)
    have e1 := ConRon.Refine.ExprOps.all_params_defined_refines hp x hxw b hbv
    have hdrop : absLevelLFrom ls i = ConRon.Refine.absLevel x :: (ls.val.drop (i.val + 1)).map ConRon.Refine.absLevel := by
      rw [absLevelLFrom, List.drop_eq_getElem_cons hb, hxv]; rfl
    rw [hdrop, List.all_cons, ← e1]
    cases b with
    | false => simp only [Bool.false_eq_true, ite_false, Result.ok.injEq] at h; rw [← h]; rfl
    | true =>
      simp only [ite_true] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      rw [ih i2 o (by omega) h, absLevelLFrom, hi2v]; rfl

@[lockstep] theorem all_params_defined_list_twin {params : alloc.vec.Vec kernel.name.Name}
    {ls : alloc.vec.Vec kernel.level.Level} (hp : NamesWF params) (hl : ConRon.Refine.LevelsWF ls) :
    LSP (arena.checker_base.all_params_defined_list params ls 0#usize)
      (fun o => TwinEq ((ConRon.Refine.absLevels ls).all
        (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params))) o) := by
  intro o h
  rw [all_params_defined_list_aux hp hl _ 0#usize o rfl h]
  simp [TwinEq, absLevelLFrom, ConRon.Refine.absLevels]

theorem all_level_params_defined_go_aux (n : Nat) :
    ∀ {pers st lst} (params : alloc.vec.Vec kernel.name.Name)
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (lm : Std.HashMap EIdx Bool)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → NamesWF params →
      ExprOps.LMemoRel rm lm →
      LSRM pers BoolMemoR (arena.checker_base.all_level_params_defined_go pers st params rm fuel h) st lst
        (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst params rm lm fuel h hn hrel hinv hp hm
    rw [arena.checker_base.all_level_params_defined_go, allLevelParamsDefinedGo]
    lockstep
  | succ m ih =>
    intro pers st lst params rm lm fuel h hn hrel hinv hp hm
    rw [arena.checker_base.all_level_params_defined_go, allLevelParamsDefinedGo]
    unfold arena.checker_base.all_level_params_defined_node arena.checker_base.all_level_params_defined_binder
    lockstep

@[lockstep] theorem all_level_params_defined_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {params : alloc.vec.Vec kernel.name.Name} (hp : NamesWF params)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSRM pers BoolMemoR (arena.checker_base.all_level_params_defined_go pers st params rm fuel h) st lst
      (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm (absU fuel) (absEIdx h)) :=
  all_level_params_defined_go_aux _ params rm lm fuel h rfl hrel hinv hp hm

/-- `all_level_params_defined` ⊑ `allLevelParamsDefined` — one memoised DAG
walk, at the parameter list read back once.  A STATE step since task
#97-PERF-WALKMEMO: the walk's memo is the state's parked `lp_def_c` table,
moved out and emptied by `take_walk_memo` and put back afterwards — the
twin's `∅`, and invisible to `AStateRel₀` (`MemosRel` has no clause for it). -/
@[lockstep] theorem all_level_params_defined_ls {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.all_level_params_defined pers st lps e) lst
      (allLevelParamsDefined (absNIdxL lps) (absEIdx e)) := by
  intro o st' hrun
  rw [arena.checker_base.all_level_params_defined] at hrun
  obtain ⟨r0, hr0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hrn := read_names_ls hrel hinv lps r0 hr0
  rw [allLevelParamsDefined, StateT.run_bind]
  cases r0 with
  | Err err =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    exact AErrSim.bind hrn _
  | Ok ks =>
    obtain ⟨ks', lst1, hx1, ⟨hks, rfl⟩, hrel1, hinv1⟩ := hrn
    obtain ⟨⟨m, hm⟩, htake, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨hml, hhm⟩ := take_walk_memo_lmemo hinv.memos.lpDefC htake
    obtain ⟨⟨r, m1⟩, hgo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    have hw := LSRM.apply (all_level_params_defined_go_ls
      (st := { st with memos := { st.memos with lp_def_c := hm } })
      ⟨hrel1.store, { hrel1.memos with }, hrel1.caches, hrel1.pins⟩
      ⟨hinv.store, { hinv.memos with lpDefC := hhm }, hinv.caches⟩ hks hml
      arena.core.CORE_WALK_FUEL e) hgo
    rw [core_walk_fuel_abs] at hw
    rw [show absNIdxL lps = lps.val.map absNIdx from rfl, hx1]
    show LOut pers _ _ _ ((do pure (← allLevelParamsDefinedGo _ ∅ coreWalkFuel _).1 : AM Bool).run lst1)
    rw [run_fst_eq]
    cases r with
    | Ok a =>
      obtain ⟨b, lst', hx, hR, h3, h4⟩ := hw
      exact ⟨b.1, lst', by rw [hx]; rfl, hR.1, ⟨h3.store, { h3.memos with }, h3.caches, h3.pins⟩,
        ⟨hinv.store, { hinv.memos with lpDefC := hR.2.2 }, hinv.caches⟩⟩
    | Err err =>
      exact AErrSim.trans hw (fun le hle => by rw [hle]; rfl)

end MemoWalks

/-! ## The front door's verdict at an unresolved constant -/

/-- `unresolved_consts_error` by `lockstep`, with its walk `mentions_const` as a
hypothesis: that walk's statement (`mentions_const_ls`) is
`Refine2/Inductives/StructParts.lean`'s, a module ABOVE this one (the
Inductives tier imports the checker's base), so it cannot be named here. -/
theorem unresolved_consts_error_of {pers st lst} {e : arena.handle.EIdx} {o}
    {w : String}
    (hM : ∀ {st lst} (t : arena.handle.NIdx), AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a)
        (arena.inductives.struct_parts.mentions_const pers st t e) lst
        (mentionsConst (absNIdx t) (absEIdx e)))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.unresolved_consts_error pers st e = ok o) :
    SimRel₀ (fun r v => absAErrKind r = lAErrKind v) pers lst o
      (unresolvedConstsError w (absEIdx e)) := by
  have hS : ∀ {st lst}, AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_sorry_ax st) st lst
        pinSorryAx :=
    fun hrel hinv => Lockstep.LSR.ofSimRE hrel hinv fun _ h => pin_sorry_ax_refines hrel hinv h
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker_base.unresolved_consts_error, unresolvedConstsError]
  lockstep

/-- `unresolved_consts_error` ⊑ `unresolvedConstsError`.  The result is a
CheckError, so it is a `SimRel₀` at the kind: a term that mentions `sorryAx`
DECLINES (`notImplemented`) and anything else REJECTS (`invalid`), and the
claim is that the two agree on WHICH — messages are never compared
(DESIGN §3.1).  `unresolved_consts_error_of` at `mentions_const_ls`
(`Checker/Leaves.lean`, moved down from `Inductives/StructParts.lean`). -/
theorem unresolved_consts_error_refines {pers st lst} {e : arena.handle.EIdx} {o}
    {w : String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.unresolved_consts_error pers st e = ok o) :
    SimRel₀ (fun r v => absAErrKind r = lAErrKind v) pers lst o
      (unresolvedConstsError w (absEIdx e)) :=
  unresolved_consts_error_of (fun _ hrel hinv => mentions_const_ls hrel hinv) hrel hinv hrun

open Lockstep in
@[lockstep] theorem unresolved_consts_error_ls {pers st lst}
    {e : arena.handle.EIdx}
    {w : String}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e) lst
      (unresolvedConstsError w (absEIdx e)) :=
  LS.ofSimRel₀ fun _ h => unresolved_consts_error_refines hrel hinv h

/-! ## The string-literal guard ahead of the verdict (task #119)

con-leche's task #342 moved the annotate pass's string-literal guard into
`unresolvedConstsErrorL`: a string literal DECLINES before resolution when the
String support declarations are absent.  Its walk `has_str_lit_go` is a
memoised reader (`LSRM` at `BoolMemoR`, the memo's key set being con-leche's
visited set); the node and pair fragments are unfolded in place, as
`all_level_params_defined_go`'s are. -/

open Lockstep in
theorem has_str_lit_go_aux (n : Nat) :
    ∀ {pers st lst} (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      (lm : Std.HashMap EIdx Bool) (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      ExprOps.LMemoRel rm lm →
      LSRM pers BoolMemoR (arena.checker_base.has_str_lit_go pers st rm fuel h) st lst
        (hasStrLitGo lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel h hn hrel hinv hm
    rw [arena.checker_base.has_str_lit_go, hasStrLitGo]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm fuel h hn hrel hinv hm
    rw [arena.checker_base.has_str_lit_go, hasStrLitGo]
    unfold arena.checker_base.has_str_lit_node arena.checker_base.has_str_lit_two
    lockstep

open Lockstep in
@[lockstep] theorem has_str_lit_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LSRM pers BoolMemoR (arena.checker_base.has_str_lit_go pers st rm fuel h) st lst
      (hasStrLitGo lm (absU fuel) (absEIdx h)) :=
  has_str_lit_go_aux _ rm lm fuel h rfl hrel hinv hm

open Lockstep in
/-- `unresolved_consts_error_l` ⊑ `unresolvedConstsErrorL` — the string-literal
guard (at a fresh memo) ahead of `unresolved_consts_error`, at the kind. -/
@[lockstep] theorem unresolved_consts_error_l_ls {pers st lst}
    {e : arena.handle.EIdx} {strOk : Bool} {w : String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error_l pers st strOk e) lst
      (unresolvedConstsErrorL strOk w (absEIdx e)) := by
  rw [arena.checker_base.unresolved_consts_error_l, unresolvedConstsErrorL]
  lockstep

open Lockstep in
/-- `unresolved_consts_fail` ⊑ `throw (unresolvedConstsErrorL (strLitSupported
fe) where_ e)` — the failing arm every front door spells, the support test
read first. -/
@[lockstep] theorem unresolved_consts_fail_ls {α β : Type} {R : α → β → Prop}
    {pers st lst} {rf lf} {e : arena.handle.EIdx} {w : String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers rf lf) :
    LS pers R (arena.checker_base.unresolved_consts_fail α pers st rf e) lst
      (unresolvedConstsFailSpec (α := β) lf w (absEIdx e)) := by
  rw [arena.checker_base.unresolved_consts_fail, unresolvedConstsFailSpec]
  lockstep

/-! ### Twin readers leave the state alone

The twin's pin reads (`natOpNames`, `natDivModNames`, `reduceOpNames`) read
the pin table and write nothing — a fact about the twin alone, which the
parser tier's `is_nat_op_record_refines` uses to keep its old-shape
statement across a lockstep reader. -/

/-- **`ifenv_find` ⊑ `IFEnv.find?`**, filed as a Rust-only step whose answer
rewrites the twin (task #97-T2-LOCKSTEP lane Checker round 2): the index read
is pure on both sides, `ifenv_find_abs` is the correspondence. -/
@[lockstep] theorem Lockstep.ifenv_find_spec {pers : arena.store.PersTier} {rf lf} (hfe : IFEnvRelI pers rf lf)
    (n : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find pers rf n)
      (fun o => TwinEq (lf.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (ifenv_find_abs (IFEnvInv.coreCtx hfe.rel hfe.inv) h).symm

@[lockstep_simp] theorem absIConstantVal_name (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).name = absNIdx cv.name := rfl

attribute [lockstep_simp] Lockstep.PC1.absIConstantVal_type

attribute [lockstep_simp] core.option.Option.is_some Option.isSome_map ite_true ite_false

namespace Lockstep

@[lockstep] theorem nidx_contains_from_spec (ns : alloc.vec.Vec arena.handle.NIdx)
    (i : Std.Usize) (n : arena.handle.NIdx) :
    LSP (arena.checker_base.nidx_contains_from ns i n)
      (fun o => o = (absNIdxLFrom ns i).contains (absNIdx n)) :=
  fun _ h => nidx_contains_from_refines h

/-- `ifenv_push`: the constant pushed onto the layer. -/
@[lockstep] theorem ifenv_push_spec {pers : arena.store.PersTier} {rf lf} (hfe : IFEnvRelI pers rf lf)
    (ci : arena.env.IConstantInfo) :
    LSP (arena.env.ifenv_push rf ci)
      (fun r => IFEnvRelI pers r (lf.push (absIConstantInfo ci))) :=
  fun _ h => ifenv_push_refines hfe.rel hfe.inv h

/-- `ifenv_push_table`: a table pushed onto the layer. -/
@[lockstep] theorem ifenv_push_table_spec {pers : arena.store.PersTier} {rf lf}
    (hfe : IFEnvRelI pers rf lf) (t : arena.env.IProjTable) :
    LSP (arena.env.ifenv_push_table rf t)
      (fun r => IFEnvRelI pers r (lf.pushTable (absIProjTable t))) :=
  fun _ h => ifenv_push_table_refines hfe.rel hfe.inv h

/-! ### A temporary push and its pop (con-leche's `FEnv.overlay`)

The pinned gates read the environment with the declared constant on it and then
without: the Rust pushes in place and pops (`ifenv_push_temp`, `ifenv_pop_temp`),
the twin pushes and puts the displaced own row back (`IFEnv.popTemp`).  Between
the two the Rust only reads the layer. -/

/-- **`ifenv_push_temp` ⊑ `IFEnv.push`**, with what it displaced: the slot of the
row it overwrote, which the pop puts back. -/
theorem ifenv_push_temp_refines {pers : arena.store.PersTier} {rf rf1 : arena.env.IFEnv}
    {lf : IFEnv} {ci : arena.env.IConstantInfo} {prev : Option Std.U64}
    (hfe : IFEnvRelI pers rf lf)
    (h : arena.env.ifenv_push_temp rf ci = ok (prev, rf1)) :
    IFEnvRelI pers rf1 (lf.push (absIConstantInfo ci)) ∧
    ∃ n, arena.env.i_constant_info_name ci = ok n ∧
      prev = ConRon.Refine.HashMap2.toFun rf.idx n ∧
      rf1.env.consts.val = rf.env.consts.val ++ [ci] ∧
      (∃ s : Std.U64, s.val = rf.env.consts.val.length ∧
        ConRon.Refine.HashMap2.toFun rf1.idx =
          Function.update (ConRon.Refine.HashMap2.toFun rf.idx) n (some s)) ∧
      rf1.env.tables = rf.env.tables ∧ rf1.tbls = rf.tbls ∧
      rf1.base_below = rf.base_below ∧ rf1.base_below_rec = rf.base_below_rec := by
  sorry -- T143-STUB

/-- **`ifenv_pop_temp` after `ifenv_push_temp` ⊑ `IFEnv.popTemp` after `IFEnv.push`**:
the layer the push started from, on both sides — the twin's displaced own row is
the one read before the push. -/
theorem ifenv_pop_temp_refines {pers : arena.store.PersTier} {rf rf1 rf2 : arena.env.IFEnv}
    {lf : IFEnv} {ci : arena.env.IConstantInfo} {prev : Option Std.U64}
    {n : arena.handle.NIdx}
    (hfe : IFEnvRelI pers rf lf) (hn : absNIdx n = (absIConstantInfo ci).name)
    (h1 : arena.env.ifenv_push_temp rf ci = ok (prev, rf1))
    (h2 : arena.env.ifenv_pop_temp rf1 n prev = ok rf2) :
    IFEnvRelI pers rf2
      ((lf.push (absIConstantInfo ci)).popTemp (absNIdx n) lf.idx[absNIdx n]?) := by
  sorry -- T143-STUB

attribute [lockstep_simp] absIConstantInfo Option.map_some Option.map_none

end Lockstep

/-! ## The per-declaration constant check -/

@[lockstep_simp] theorem absIConstantVal_levelParams (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).levelParams = cv.level_params.val.map absNIdx := rfl

open Lockstep in
@[lockstep] theorem name_nodup_spec (ns : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.checker_base.name_nodup ns)
      (fun o => TwinEq (nameNodup (ns.val.map absNIdx)) o) :=
  fun _ h => (name_nodup_refines h).symm

/-- `arena::core::nat_op_name` ⊑ `natOpName`: the name among the seven structural
operations, else among the WF-recursive ones. -/
@[lockstep] theorem base_nat_op_name_ls {pers st lst} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    Lockstep.LS pers (fun a b => b = id a) (arena.core.nat_op_name st n) lst
      (natOpName (absNIdx n)) := by
  rw [arena.core.nat_op_name, natOpName]
  lockstep

/-- `check_constant_val_guards_rest` is `check_constant_val_guards`'s tail past
the operation-name test (extraction rule 5): the literal shape, then the three
syntactic tests on the type.  One `lockstep` call. -/
theorem check_constant_val_guards_rest_refines {pers st lst}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.check_constant_val_guards_rest pers st cv = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkConstantValGuardsRestSpec (absIConstantVal cv)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val_guards_rest, checkConstantValGuardsRestSpec]
  simp only [am_fail_bind]
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_guards_rest_ls {pers st lst}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_constant_val_guards_rest pers st cv) lst
      (checkConstantValGuardsRestSpec (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_constant_val_guards_rest_refines hrel hinv h

/-- `check_constant_val_guards` is `checkConstantVal`'s guard prefix — the
syntactic tests, the operation name allowed only at a definition. -/
theorem check_constant_val_guards_refines {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {allowOp : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_base.check_constant_val_guards pers st rf cv allowOp = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkConstantValGuardsSpec lf (absIConstantVal cv) allowOp) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val_guards]
  try unfold checkConstantValGuardsSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_guards_ls {pers st lst}
    {rf lf}
    {cv : arena.env.IConstantVal} {allowOp : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_constant_val_guards pers st rf cv allowOp) lst
      (checkConstantValGuardsSpec lf (absIConstantVal cv) allowOp) :=
  LS.ofSim₀ fun _ h => check_constant_val_guards_refines hrel hinv hfe.rel hfe.inv h

/-- `check_constant_val_tail` is `checkConstantVal`'s tail: the level-parameter
test and the constant-resolution test on the declared type. -/
theorem check_constant_val_tail_refines {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_base.check_constant_val_tail pers st rf cv = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkConstantValTailSpec lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val_tail]
  try unfold checkConstantValTailSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_tail_ls {pers st lst}
    {rf lf}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_constant_val_tail pers st rf cv) lst
      (checkConstantValTailSpec lf (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_constant_val_tail_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_constant_val` ⊑ `checkConstantVal`** — the common per-declaration
constant check, whole, at the caller's `allowOp`. -/
theorem check_constant_val_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {allowOp : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_base.check_constant_val pers st mode rf cv allowOp = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv) allowOp) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val]
  rw [checkConstantVal_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal} {allowOp : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_constant_val pers st mode rf cv allowOp) lst
      (checkConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv) allowOp) :=
  LS.ofSim₀ fun _ h => check_constant_val_refines hrel hinv hfe.rel hfe.inv h

/-! ## The free variables' types -/

open Lockstep in
/-- `fvar_type_ds` ⊑ `fvarTypeDs` at the cursor — `xs.map Expr.fvarTypeD`,
with DESIGN §3.4's closure-free `List` recursion; the port pushes onto `out`
before it recurses, so the relation carries `out` in front of the twin's
answer. -/
theorem fvar_type_ds_aux {pers st} (hs : alloc.vec.Vec arena.handle.EIdx) (k : Nat) :
    ∀ {lst} (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx), hs.val.length - i.val = k →
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => absEIdxL a = absEIdxL out ++ b)
        (arena.checker_base.fvar_type_ds pers st hs i out) st lst
        (fvarTypeDs (absEIdxLFrom hs i)) := by
  induction k with
  | zero =>
    intro lst i out hk hrel hinv
    apply LSR.of_LS
    rw [arena.checker_base.fvar_type_ds]
    have hl := alloc.vec.Vec.len_val hs
    rw [ite_eq_left (by scalar_tac)]
    have : absEIdxLFrom hs i = [] := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [this, fvarTypeDs]
    lockstep
  | succ k ih =>
    intro lst i out hk hrel hinv
    apply LSR.of_LS
    rw [arena.checker_base.fvar_type_ds]
    have hl := alloc.vec.Vec.len_val hs
    rw [ite_eq_right (by scalar_tac)]
    have hlt : i.val < hs.val.length := by omega
    have : absEIdxLFrom hs i = absEIdx hs.val[i.val] :: (hs.val.drop (i.val + 1)).map absEIdx := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_getElem_cons hlt]; rfl
    rw [this, fvarTypeDs]
    lockstep

open Lockstep in
@[lockstep] theorem fvar_type_ds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hs : alloc.vec.Vec arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdxL a)
      (arena.checker_base.fvar_type_ds pers st hs 0#usize (alloc.vec.Vec.new _)) st lst
      (fvarTypeDs (absEIdxL hs)) := by
  have H := fvar_type_ds_aux hs _ 0#usize (alloc.vec.Vec.new _) rfl hrel hinv
  have e0 : absEIdxLFrom hs 0#usize = absEIdxL hs := by simp [absEIdxLFrom, absEIdxL]
  rw [e0] at H
  intro o ho
  have := H o ho
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := this
    refine ⟨b, lst', hx, ?_, h1, h2⟩
    show b = absEIdxL a
    rw [hR]; simp [absEIdxL, alloc.vec.Vec.new]

/-! ## The block's declared parameter count -/

/-- The block's cursor at a position inside it: the element, then the rest. -/
theorem absICILFrom_cons {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    (hlt : i.val < block.val.length) :
    absICILFrom block i
      = absIConstantInfo block.val[i.val] :: (block.val.drop (i.val + 1)).map absIConstantInfo := by
  simp only [absICILFrom, List.drop_eq_getElem_cons hlt, List.map_cons]

open Lockstep in
/-- `arena::env::pi_sort_tele_len` as a store read (`Checker/Leaves.lean`'s
`env_pi_sort_tele_len_run`). -/
@[lockstep] theorem pi_sort_tele_len_ls {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = Option.map absU a)
      (arena.env.pi_sort_tele_len pers st.store fuel h) st lst
      (piSortTeleLen? (absU fuel) (absEIdx h)) :=
  LSR.ofSimRE hrel hinv fun _ hr => Frontend.env_pi_sort_tele_len_run hrel hinv hr

/-- A `u64` handle-free comparison, read back. -/
@[lockstep_simp] theorem absU_beq_u64 (a b : Std.U64) :
    (absU a == absU b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : absU a ≠ absU b := fun e => h (Std.UScalar.eq_of_val_eq e)
    simp [h, this]

/-- `≤` on `u64`, read back. -/
@[lockstep_simp] theorem absU_le_u64 (a b : Std.U64) :
    decide (absU a ≤ absU b) = decide (a ≤ b) := by
  simp only [absU]; rfl

/-- `ind_params_ok_at` is `ind_params_ok`'s per-member test. -/
theorem ind_params_ok_at_refines {pers st lst} {n_p : Std.U64}
    {ci : arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.ind_params_ok_at pers st n_p ci = ok o) :
    Sim₀ id pers lst o
      (indParamsOkAtSpec (absU n_p) (absIConstantInfo ci)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  cases ci <;> (rw [arena.checker_base.ind_params_ok_at]; simp only [absIConstantInfo,
    indParamsOkAtSpec]) <;> lockstep

open Lockstep in
@[lockstep] theorem ind_params_ok_at_ls {pers st lst}
    {n_p : Std.U64}
    {ci : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.ind_params_ok_at pers st n_p ci) lst
      (indParamsOkAtSpec (absU n_p) (absIConstantInfo ci)) :=
  LS.ofSim₀ fun _ h => ind_params_ok_at_refines hrel hinv h

theorem ind_params_ok_aux {n_p : Std.U64} {block : alloc.vec.Vec arena.env.IConstantInfo}
    (m : Nat) : ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (i : Std.Usize), block.val.length - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a)
        (arena.checker_base.ind_params_ok pers st n_p block i) lst
        (indParamsOk (absU n_p) (absICILFrom block i)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro pers st lst i hm hrel hinv
    have hl := alloc.vec.Vec.len_val block
    by_cases hge : i ≥ block.len
    · have hle : block.val.length ≤ i.val := by scalar_tac
      have hnil : absICILFrom block i = [] := by
        simp [absICILFrom, List.drop_eq_nil_of_le hle]
      rw [arena.checker_base.ind_params_ok, hnil, indParamsOk]
      lockstep
    · have hlt : i.val < block.val.length := by scalar_tac
      have ih' : ∀ (i2 : Std.Usize), i2.val = i.val + 1 → ∀ {st lst},
          AStateRel₀ pers st lst → AStateInv pers st →
          Lockstep.LS pers (fun a b => b = id a)
            (arena.checker_base.ind_params_ok pers st n_p block i2) lst
            (indParamsOk (absU n_p) ((block.val.drop (i.val + 1)).map absIConstantInfo)) := by
        intro i2 hi2 st lst hrel hinv
        have e : (block.val.drop (i.val + 1)).map absIConstantInfo = absICILFrom block i2 := by
          simp [absICILFrom, hi2]
        rw [e]
        exact ih _ (by omega) i2 rfl hrel hinv
      rw [arena.checker_base.ind_params_ok, absICILFrom_cons hlt, indParamsOk_unfold]
      lockstep

/-- `ind_params_ok` ⊑ `indParamsOk` from the cursor on — **the stream's
declared parameter count, checked as official checks it** (con-leche's task
#228).  Both halves are one-sided on purpose: `false` means official
rejects. -/
theorem ind_params_ok_refines {pers st lst} {n_p : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.ind_params_ok pers st n_p block i = ok o) :
    Sim₀ id pers lst o
      (indParamsOk (absU n_p) (absICILFrom block i)) :=
  Lockstep.LS.toSim₀ (ind_params_ok_aux _ i rfl hrel hinv) hrun

open Lockstep in
@[lockstep] theorem ind_params_ok_ls {pers st lst}
    {n_p : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.ind_params_ok pers st n_p block i) lst
      (indParamsOk (absU n_p) (absICILFrom block i)) :=
  LS.ofSim₀ fun _ h => ind_params_ok_refines hrel hinv h

/-! ## A value's syntactic guards (`arena::decl_check::value_guards`)

The three value checks spell the value's guards alike; the Rust splits them past
the two scope tests (`value_guards_tail`).  They sit here, below the value checks
(`Refine2/Checker/DeclCheck.lean`), with the other guard walks. -/

/-- `value_guards_tail` is `valueGuards`' tail past the two scope tests. -/
theorem value_guards_tail_refines {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.value_guards_tail pers st rf cv value = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (valueGuardsTailSpec lf (absIConstantVal cv) (absEIdx value)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.value_guards_tail]
  try unfold valueGuardsTailSpec
  lockstep

open Lockstep in
@[lockstep] theorem value_guards_tail_ls {pers st lst}
    {rf lf}
    {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.value_guards_tail pers st rf cv value) lst
      (valueGuardsTailSpec lf (absIConstantVal cv) (absEIdx value)) :=
  LS.ofSim₀ fun _ h => value_guards_tail_refines hrel hinv hfe.rel hfe.inv h

/-- **`value_guards` ⊑ `valueGuards`**: no loose bound variable, no free
variable, declared universe parameters, resolving constants.  One `lockstep`
call. -/
theorem value_guards_refines {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.value_guards pers st rf cv value = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (valueGuards lf (absIConstantVal cv) (absEIdx value)) := by
  have hctx := IFEnvInv.coreCtx hfe hfinv
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.decl_check.value_guards, valueGuards_unfold]
  simp only [am_fail_bind]
  lockstep

@[lockstep] theorem Lockstep.value_guards_ls {pers st lst} {rf lf}
    {cv : arena.env.IConstantVal} {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.value_guards pers st rf cv value) lst
      (valueGuards lf (absIConstantVal cv) (absEIdx value)) :=
  LS.ofSim₀ fun _ h => value_guards_refines hrel hinv hfe.rel hfe.inv h

/-! ## The checker's glue callees as `@[lockstep]` specs (task #97-T2-LOCKSTEP lane Checker)

Each is its `_refines` lemma (or a Rust-only value step) in the judgement the
`lockstep` tactic zips with; the environment arguments come as `IFEnvRelI`,
which is what a fold step has in hand. -/

namespace Lockstep

@[lockstep] theorem reduce_op_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.trust_axioms.reduce_op_names st) lst
      reduceOpNames :=
  LS.ofSim₀ fun _ h => reduce_op_names_refines hrel hinv h

@[lockstep] theorem flush_caches_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.flush_caches st) lst flushCaches :=
  LSW.ofSimS₀ fun _ h => flush_caches_sim₀ hrel hinv h

end Lockstep

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.memo_b_get_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_b_get_refines

/-- info: 'ConRon.Refine2.consts_resolve_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consts_resolve_aux

/-- info: 'ConRon.Refine2.name_nodup_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms name_nodup_refines

end ConRon.Refine2
