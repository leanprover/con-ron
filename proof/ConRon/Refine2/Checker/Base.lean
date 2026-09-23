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
`check_value_group_tail`, `install_value`, `install_value_tail`
(`arena::checker_split`) and `consts_resolve_f_{go,node,two,fast}`
(`arena::checker_base`).  The rest of the closure is `arena::core`'s, where
the same repair is `Refine2/Core/KnotRel.lean`'s `CoreCtx` (its `fenv` clause
is now `IFEnvRel fe (lfe.restrictTo (absU fe.visible_below))`, so the counter
is the `vis` clause's business alone) — and `arena::prop_read`'s five readers
and `arena::env::ifenv_find_proj`, which have no `Refine2` tier yet and must
take the general form when they get one.

Every OTHER `hvis` of this tier and of `Refine2/Checker/DeclCheck.lean` is
sound as it stands: those functions are phase A's, where the port really is
only ever called at `fe.visible_below`.

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
      rw [if_pos hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absNIdxLFrom, List.drop_eq_nil_of_le hle]
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [if_neg hge] at hrun
      obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hlt', rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn1
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := nidx_eq2_abs hb
      have hcons : absNIdxLFrom ns i = absNIdx ns.val[i.val] :: (ns.val.drop (i.val + 1)).map absNIdx := by
        simp only [absNIdxLFrom, List.drop_eq_getElem_cons hlt, List.map_cons]
      rw [hcons, List.contains_cons]
      by_cases hc : b = true
      · rw [if_pos hc] at hrun
        rw [← Result.ok_injective hrun]
        subst hc
        have heq : (absNIdx ns.val[i.val] == absNIdx n) = true := hbv.symm
        rw [BEq.comm] at heq
        simp [heq]
      · rw [if_neg hc] at hrun
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
`annot_step_defn_refines`; the function is `arena::core`'s, but no tier had
stated it). -/
theorem nat_op_names_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_names st = ok o) :
    Sim absNIdxL (fun _ => True) pers lst o natOpNames := by
  unfold natOpNames
  rw [arena.core.nat_op_names] at hrun
  unfold Sim
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_pred_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_nat_pred_refines hrel hinv hr0
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut.err (pin_err (tw := natPredName) hS0)
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
    exact AOut.err (pin_err (tw := natAddName) hS1)
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
    exact AOut.err (pin_err (tw := natSubName) hS2)
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
    exact AOut.err (pin_err (tw := natMulName) hS3)
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
    exact AOut.err (pin_err (tw := natPowName) hS4)
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
    exact AOut.err (pin_err (tw := natBeqName) hS5)
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
    exact AOut.err (pin_err (tw := natBleName) hS6)
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
  refine ⟨lst, ?_, hrel, hinv, Ext.refl _, trivial⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

/-- `arena::core::nat_div_mod_names` ⊑ `natDivModNames` — the eight pinned
well-founded operations, as eight pin reads (task #97-P5-Top, as above). -/
theorem nat_div_mod_names_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_div_mod_names st = ok o) :
    Sim absNIdxL (fun _ => True) pers lst o natDivModNames := by
  unfold natDivModNames
  rw [arena.core.nat_div_mod_names] at hrun
  unfold Sim
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_div_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_nat_div_refines hrel hinv hr0
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut.err (pin_err (tw := natDivName) hS0)
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
    exact AOut.err (pin_err (tw := natModName) hS1)
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
    exact AOut.err (pin_err (tw := natGcdName) hS2)
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
    exact AOut.err (pin_err (tw := natLandName) hS3)
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
    exact AOut.err (pin_err (tw := natLorName) hS4)
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
    exact AOut.err (pin_err (tw := natXorName) hS5)
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
    exact AOut.err (pin_err (tw := natShiftLeftName) hS6)
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
    exact AOut.err (pin_err (tw := natShiftRightName) hS7)
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
  refine ⟨lst, ?_, hrel, hinv, Ext.refl _, trivial⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

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
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.consts_resolve_f_go pers vis st rf rm fuel h = ok o) :
    SimBM id pers lst o
      (constsResolveFGo (lf.restrictTo (absU vis)) lm (absU fuel) (absEIdx h)) := by
  sorry

/-- `consts_resolve_f_node` is `consts_resolve_f_go`'s miss arm past the
`view` (extraction rule 5), stated against the twin's arm at that view. -/
theorem consts_resolve_f_node_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {v : arena.store.ENodeView} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hm : ExprOps.LMemoRel rm lm)
    (hview : lst.store.view (absEIdx h) = some (absENodeView v))
    (hrun : arena.checker_base.consts_resolve_f_node pers vis st rf rm fuel v = ok o) :
    SimBM id pers lst o
      (constsResolveFNodeSpec (lf.restrictTo (absU vis)) lm (absU fuel) (absEIdx h)
        (absENodeView v)) := by
  sorry

/-- `consts_resolve_f_two` is the two-child arms' pair, in the twin's order
and WITHOUT a short-circuit (the twin's `.app` arm walks both and `&&`s). -/
theorem consts_resolve_f_two_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {a b : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.consts_resolve_f_two pers vis st rf rm fuel a b = ok o) :
    SimBM id pers lst o
      (do
        let (b₁, memo) ←
          constsResolveFGo (lf.restrictTo (absU vis)) lm (absU fuel) (absEIdx a)
        let (b₂, memo) ←
          constsResolveFGo (lf.restrictTo (absU vis)) memo (absU fuel) (absEIdx b)
        pure (b₁ && b₂, memo)) := by
  sorry

/-- `consts_resolve_f_fast` ⊑ `constsResolveFFast` — one memoised DAG walk,
which is what every front door below calls. -/
theorem consts_resolve_f_fast_refines {pers st lst} {vis : Std.U64} {rf lf}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_base.consts_resolve_f_fast pers vis st rf e = ok o) :
    Sim id (fun _ => True) pers lst o
      (constsResolveFFast (lf.restrictTo (absU vis)) (absEIdx e)) := by
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

/-! ## `DeclResolves` — the declaration's handles and the Core answers resolve

**Task #97-P5-Top round 2, ruling 2.**  The Core entries carry task #97-P5-0's
finding 3 (`EResolves` of the handle they dispatch on: the port reads the
handle's TAG, the twin its VIEW) and task #97-P5-Arms' finding 14
(`AnswerResolves` of a callee's answer).  Nothing in `AStateRel`/`AStateInv`
says a handle resolves — the Rust invariant does not constrain cache contents,
so a universally quantified "every answer resolves" would be FALSE — and the
fact is Theorem 1's ("the checker never holds a dangling handle", its
`StateOK`).  So it enters Theorem 2 as a precondition, in the form Theorem 1
can discharge:

* `Good : IFEnv → AState → Prop` is Theorem 1's twin-state invariant, ABSTRACT
  here (`Refine2` does not import `Bridge`);
* `ResolveInv mode Good` is what Theorem 2 consumes of it: the Core answers
  resolve from `Good` states, and `Good` survives the twin steps the glue
  walks over — each field a twin-only statement over `Good` states;
* `HandlesResolve Good hs` / `VGResolves Good fe g` — the declaration's (the
  value group's) handles resolve in every `Good` state.

The capstone (`ConRon/Capstone.lean`, the one module that sees both theorems)
supplies `Good` and the facts from Theorem 1, the way it supplies `BrOK`. -/

/-- The expression handles a stored constant carries. -/
def ciHandles : IConstantInfo → List EIdx
  | .axiomInfo cv => [cv.type]
  | .defnInfo cv v _ => [cv.type, v]
  | .thmInfo cv v => [cv.type, v]
  | .indInfo cv _ => [cv.type]
  | .ctorInfo cv _ _ => [cv.type]
  | .recInfo cv _ _ rules => cv.type :: rules.map (·.rhs)
  | .projInfo t => t.bodies.toList

/-- The expression handles a declaration record carries. -/
def declHandles : IDeclaration → List EIdx
  | .axiomDecl cv => [cv.type]
  | .defnDecl cv v _ => [cv.type, v]
  | .thmDecl cv v => [cv.type, v]
  | .opaqueDecl cv v => [cv.type, v]
  | .basisDecl _ => []
  | .indDecl block _ => block.flatMap ciHandles
  | .quotDecl _ cv => [cv.type]

/-- **The handles resolve in every `Good` state at `fe`.** -/
def ResolvesAt (Good : IFEnv → AState → Prop) (fe : IFEnv) (hs : List EIdx) : Prop :=
  ∀ s, Good fe s → ∀ h ∈ hs, ExprOps.EResolves s h

theorem ResolvesAt.sub {Good : IFEnv → AState → Prop} {fe : IFEnv} {hs hs' : List EIdx}
    (h : ResolvesAt Good fe hs) (hsub : ∀ x ∈ hs', x ∈ hs) : ResolvesAt Good fe hs' :=
  fun s hg x hx => h s hg x (hsub x hx)

/-- **The handles resolve in every `Good` state** — a stream declaration's
handles are persistent, so Theorem 1's invariant carries them whatever the
environment. -/
def HandlesResolve (Good : IFEnv → AState → Prop) (hs : List EIdx) : Prop :=
  ∀ fe, ResolvesAt Good fe hs

/-- **A value group's handles resolve** in every `Good` state at the
environment phase B checks it against (phase A made them; they are that
environment's constant's type and value). -/
def VGResolves (Good : IFEnv → AState → Prop) (fe : IFEnv) (g : ValueGroup) :
    Prop :=
  ∀ s, Good fe s → ExprOps.EResolves s g.cvA.type ∧ ExprOps.EResolves s g.jv

/-- **What Theorem 2 consumes of Theorem 1's invariant `Good`** (ruling 2).
Every field is a statement about the TWIN alone, over `Good` states: the Core
answers resolve, and `Good` survives the twin steps the refinement's glue
walks over.  Fields are added as the leaves below are proved; each is a
Theorem-1 run lemma's frame. -/
structure ResolveInv (mode : ConLeche.CheckMode) (Good : IFEnv → AState → Prop) : Prop where
  /-- `inferTypeCore` answers a resolving handle, and keeps `Good`. -/
  infer : ∀ {fe : IFEnv} {v d : Nat} {e w : EIdx} {s s' : AState}, Good fe s →
    ExprOps.EResolves s e →
    inferTypeCore mode (fe.restrictTo v) checkFuel d e s = .ok (w, s') →
    ExprOps.EResolves s' w ∧ Good fe s'
  /-- `whnf` answers a resolving handle. -/
  whnf : ∀ {fe : IFEnv} {v d : Nat} {e w : EIdx} {s s' : AState}, Good fe s →
    ExprOps.EResolves s e →
    Arena.whnf mode (fe.restrictTo v) checkFuel d e s = .ok (w, s') →
    ExprOps.EResolves s' w
  /-- `ensureSortCore` keeps `Good`. -/
  ensureSort : ∀ {fe : IFEnv} {v d : Nat} {e : EIdx} {u : LIdx} {s s' : AState},
    Good fe s → ExprOps.EResolves s e →
    ensureSortCore mode (fe.restrictTo v) checkFuel d e s = .ok (u, s') → Good fe s'
  /-- `enterScratch` (phase B's bracket opened) keeps `Good`. -/
  enterScratch : ∀ {fe : IFEnv} {s : AState}, Good fe s →
    Good fe { s with store := s.store.enableScratch, memos := Memos.empty }
  /-- `flushCaches; enterScratch` (a fold step's bracket opened) keeps `Good`. -/
  flushEnter : ∀ {fe : IFEnv} {s : AState}, Good fe s →
    Good fe ({ s with caches := Caches.empty, store := s.store.enableScratch,
                      memos := Memos.empty } : AState)
  /-- phase B's step keeps `Good`. -/
  checkPending : ∀ {fe : IFEnv} {pc : PendingCheck} {s s' : AState}, Good fe s →
    checkPending mode fe pc s = .ok ((), s') → Good fe s'
  /-- phase A's step keeps `Good`, at the environment it hands on. -/
  annotDeclStep : ∀ {pins : List INatOpPinSet} {p : Nat × IFEnv × Array PendingCheck}
    {pd : IDeclaration} {p' : Nat × IFEnv × Array PendingCheck} {s s' : AState},
    Good p.2.1 s → annotDeclStep mode pins p pd s = .ok (.ok p', s') → Good p'.2.1 s'
  /-- the pure fold's step keeps `Good`, at the environment it hands on. -/
  checkDeclStep : ∀ {pins : List INatOpPinSet} {fe fe' : IFEnv} {d : IDeclaration}
    {s s' : AState}, Good fe s → checkDeclStep mode pins fe d s = .ok (fe', s') →
    Good fe' s'
  /-- `installConstantVal` keeps `Good`. -/
  installConstantVal : ∀ {fe : IFEnv} {cv c : IConstantVal} {s s' : AState},
    Good fe s → installConstantVal mode fe cv s = .ok (c, s') → Good fe s'
  /-- `checkConstantVal` keeps `Good`, and its annotated type resolves. -/
  checkConstantVal : ∀ {fe : IFEnv} {cv c : IConstantVal} {s s' : AState},
    Good fe s → checkConstantVal mode fe cv s = .ok (c, s') →
    Good fe s' ∧ ExprOps.EResolves s' c.type

/-! ### Twin readers leave the state alone

The glue carries `Good` across the twin's pin reads (`natOpNames`,
`natDivModNames`, `reduceOpNames`), which read the pin table and write
nothing. -/

/-- A twin action that never changes the state it succeeds from. -/
def AMReads {α : Type} (x : AM α) : Prop :=
  ∀ (s : AState) (v : α) (s' : AState), x.run s = .ok (v, s') → s' = s

theorem AMReads.pure' {α : Type} (a : α) : AMReads (pure a : AM α) := by
  intro s v s' h
  have h' : (Except.ok (a, s) : Except Arena.CheckError (α × AState)) = .ok (v, s') := h
  cases h'
  rfl

theorem AMReads.bind' {α β : Type} {x : AM α} {f : α → AM β} (hx : AMReads x)
    (hf : ∀ a, AMReads (f a)) : AMReads (x >>= f) := by
  intro s v s' h
  rw [am_run_bind'] at h
  cases hx' : x.run s with
  | error e => rw [hx'] at h; cases h
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [hx', except_ok_bind] at h
    rw [hf a s1 v s' h, hx s a s1 hx']

theorem pinAt_reads (i : Nat) : AMReads (pinAt i) := by
  intro s v s' h
  by_cases hi : i < s.pins.names.size
  · have h2 : (Arena.pinAt i).run s = .ok (s.pins.names[i], s) := by
      show (Arena.pinAt i) s = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, dif_pos hi]
    rw [h2] at h
    cases h
    rfl
  · have h2 : (Arena.pinAt i).run s
        = .error (Arena.CheckError.internal "arena: reserved-name pins not interned") := by
      show (Arena.pinAt i) s = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, dif_neg hi,
        Arena.fail, throwThe, MonadExceptOf.throw,
        Function.comp_apply, StateT.lift]
    rw [h2] at h
    cases h

theorem natOpNames_reads : AMReads natOpNames := by
  unfold natOpNames
  repeat (first | exact AMReads.pure' _ | refine AMReads.bind' (pinAt_reads _) fun _ => ?_)

theorem natDivModNames_reads : AMReads natDivModNames := by
  unfold natDivModNames
  repeat (first | exact AMReads.pure' _ | refine AMReads.bind' (pinAt_reads _) fun _ => ?_)

theorem reduceOpNames_reads : AMReads reduceOpNames := by
  unfold reduceOpNames
  repeat (first | exact AMReads.pure' _ | refine AMReads.bind' (pinAt_reads _) fun _ => ?_)

/-- A continuation-passing `SimRel` composition that hands the continuation
the twin's own run of the first half — which a `Good`-carrying glue step
needs to move `Good` across it (ruling 2). -/
theorem SimRel.of_sim_bind_run {α β γ δ : Type} {A : α → β} {R : γ → δ → Prop}
    {pers : arena.store.PersTier} {lst : AState} {x : AM β} {f : β → AM δ}
    {r : α} {st1 : arena.monad.AState}
    {o : core.result.Result γ kernel.core_types.CheckError × arena.monad.AState}
    (h1 : Sim A (fun _ => True) pers lst (.Ok r, st1) x)
    (h2 : ∀ lst1, x.run lst = .ok (A r, lst1) → AStateRel pers st1 lst1 →
      AStateInv pers st1 → SimRel R pers lst1 o (f (A r))) :
    SimRel R pers lst o (x >>= f) := by
  obtain ⟨lst1, hx, hrel1, hinv1, hext1, -⟩ := Sim.apply h1
  have h := h2 lst1 hx hrel1 hinv1
  unfold SimRel AOutRel at h ⊢
  rw [am_run_bind', hx, except_ok_bind]
  revert h
  cases o.1 with
  | Err e => exact id
  | Ok r' =>
    rintro ⟨v, lst2, hy, hr, hrel2, hinv2, hext2⟩
    exact ⟨v, lst2, hy, hr, hrel2, hinv2, Ext.trans hext1 hext2⟩

/-! ### `EResolves` is a fact about the Rust state

`AStateRel` pins the twin store's node arrays down exactly (`TblRel.nodes`),
and `EStore.view` reads nothing else, so two twin states related to the same
Rust state resolve the same handles.  This is what turns a twin-side
"the answer resolves" into the Core entries' `AnswerResolves`, which
quantifies over every twin state related to the Rust post-state. -/

/-- A table with everything but its node array erased. -/
def tblSkel {α ι δ : Type} [BEq α] [Hashable α] (t : Tbl α ι δ) : Tbl α ι δ :=
  ⟨t.nodes, #[], ∅⟩

/-- An expression tier with everything `EStore.view` does not read erased. -/
def eTablesSkel (t : ETables) : ETables :=
  ⟨tblSkel t.bvars, tblSkel t.fvars, tblSkel t.sorts, tblSkel t.consts,
    tblSkel t.apps, tblSkel t.lams, tblSkel t.foralls, tblSkel t.lets,
    tblSkel t.lits, tblSkel t.projs, tblSkel t.bms⟩

theorem estore_view_skel (st : EStore) (h : EIdx) :
    st.view h = (EStore.mk default (eTablesSkel st.pers) (eTablesSkel st.scr)
      st.scratchOn).view h := rfl

private theorem tbl_nodes_eq {A I D α ι δ ω : Type} [DecidableEq A] [BEq α]
    [Hashable α] {P : A → Prop} {absA : A → α} {absI : I → ι} {absD : D → δ}
    {obsD : δ → ω} {rt : arena.store.Tbl A I D} {la lb : Tbl α ι δ}
    (ha : TblRel P absA absI absD obsD rt la) (hb : TblRel P absA absI absD obsD rt lb) :
    tblSkel la = tblSkel lb := by
  have : la.nodes = lb.nodes := Array.toList_inj.mp (ha.nodes.trans hb.nodes.symm)
  simp only [tblSkel, this]

private theorem etables_skel_eq {rt : arena.store.ETables} {la lb : ETables}
    (ha : ETablesRel rt la) (hb : ETablesRel rt lb) :
    eTablesSkel la = eTablesSkel lb := by
  simp only [eTablesSkel, tbl_nodes_eq ha.bvars hb.bvars, tbl_nodes_eq ha.fvars hb.fvars,
    tbl_nodes_eq ha.sorts hb.sorts, tbl_nodes_eq ha.consts hb.consts,
    tbl_nodes_eq ha.apps hb.apps, tbl_nodes_eq ha.lams hb.lams,
    tbl_nodes_eq ha.foralls hb.foralls, tbl_nodes_eq ha.lets hb.lets,
    tbl_nodes_eq ha.lits hb.lits, tbl_nodes_eq ha.projs hb.projs,
    tbl_nodes_eq ha.bms hb.bms]

/-- **Two twin states related to one Rust state view every handle alike.** -/
theorem view_of_rel {pers : arena.store.PersTier} {st : arena.monad.AState}
    {la lb : AState} (ha : AStateRel pers st la) (hb : AStateRel pers st lb)
    (h : EIdx) : la.store.view h = lb.store.view h := by
  rw [estore_view_skel la.store, estore_view_skel lb.store,
    etables_skel_eq ha.store.perst hb.store.perst,
    etables_skel_eq ha.store.scrt hb.store.scrt,
    ha.store.scratchOn, hb.store.scratchOn]

/-- `EResolves` transported between two twin states related to one Rust
state. -/
theorem EResolves.of_rel {pers : arena.store.PersTier} {st : arena.monad.AState}
    {la lb : AState} {h : EIdx} (ha : AStateRel pers st la)
    (hb : AStateRel pers st lb) (hr : ExprOps.EResolves la h) :
    ExprOps.EResolves lb h := by
  unfold ExprOps.EResolves at hr ⊢
  rw [← view_of_rel ha hb h]
  exact hr

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
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o} {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hR : ResolveInv (ConRon.Refine.absMode mode) Good) (hg : Good lf lst)
    (hcv : ResolvesAt Good lf [absEIdx cv.ty])
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
    SimRE absEIdxL lst o
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

/-! ## `arena::core::lvl_eq` — the cached level comparison (task #97-P5-Top round 3)

`check_value_group_value`'s theorem arm asks `lvl_eq u zero`, and no tier had
stated `lvl_eq` against `lvlEq?`: the Core knot's own level comparisons go
through `lvls_eq`, and the Inductives tier's are inside sorried shapes.  The
proof is `Refine2/Core/Probes.lean`'s probe/write pair at the `lvlEqC` table
(key `LIdxPair`, value `Bool`, so no value abstraction), around
`read_level_m_run` twice and the old tier's `Level.is_equiv_refines`. -/

private theorem absLIdx_surj' : Function.Surjective absLIdx := by
  intro i
  obtain ⟨w⟩ := i
  obtain ⟨x, hx⟩ := absU32_surj w
  exact ⟨⟨x⟩, by simp [absLIdx, hx]⟩

theorem absLIdxPair_surj : Function.Surjective absLIdxPair := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := absLIdx_surj' a
  obtain ⟨y, hy⟩ := absLIdx_surj' b
  exact ⟨⟨x, y⟩, by simp [absLIdxPair, hx, hy]⟩

theorem absLIdxPair_inj : Function.Injective absLIdxPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [absLIdxPair, Prod.mk.injEq] at h
  simp [absLIdx_inj h.1, absLIdx_inj h.2]

/-- `arena::core::lvl_eq_probe` against `lst.caches.lvlEqC[·]?`. -/
theorem lvl_eq_probe_abs {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {k : arena.core_state.LIdxPair} {o : Option Bool}
    (hrun : arena.core.lvl_eq_probe st k = ok o) :
    o = lst.caches.lvlEqC[absLIdxPair k]? := by
  rw [arena.core.lvl_eq_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidxPair_eq2 hinv.caches.lvlEqC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.lvlEqC k trivial
  have ho : o = r := by
    cases r with
    | none => exact (Result.ok_injective hrun).symm
    | some _ => exact (Result.ok_injective hrun).symm
  rw [ho, ← hrelk, ← hto]
  simp

/-- The twin's cache hit. -/
theorem lvlEq?_hit {u v : LIdx} {lst : AState} {r : Bool}
    (h : lst.caches.lvlEqC[(u, v)]? = some r) :
    (lvlEq? u v).run lst = .ok (some r, lst) := by
  show (lvlEq? u v) lst = _
  simp only [lvlEq?, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Pure.pure, StateT.pure, Except.bind, Except.pure, h]

/-- The twin's cache miss: the two reads, the verdict, and the capped write. -/
theorem lvlEq?_miss {u v : LIdx} {lst : AState}
    (h : lst.caches.lvlEqC[(u, v)]? = none) :
    (lvlEq? u v).run lst = (do
      let lu ← readLevelM u
      let lv ← readLevelM v
      match ConLeche.Level.isEquiv lu lv with
      | some r => do
        let s ← get
        let mp := if s.caches.lvlEqC.size < cacheCap then s.caches.lvlEqC else ∅
        set { s with caches := { s.caches with lvlEqC := mp.insert (u, v) r } }
        pure (some r)
      | none => pure none : AM (Option Bool)).run lst := by
  show (lvlEq? u v) lst = _
  simp only [lvlEq?, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Pure.pure, Except.bind, Except.pure, h]
  rfl

/-- **`lvl_eq` ⊑ `lvlEq?`** — the cached universe comparison. -/
theorem lvl_eq_refines {pers st lst} (hrel : AStateRel pers st lst)
    (hinv : AStateInv pers st) {u v : arena.handle.LIdx} {o}
    (hrun : arena.core.lvl_eq pers st u v = ok o) :
    Sim id (fun _ => True) pers lst o (lvlEq? (absLIdx u) (absLIdx v)) := by
  rw [arena.core.lvl_eq] at hrun
  obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hkv : absLIdxPair k = (absLIdx u, absLIdx v) := by
    rw [arena.core_state.lidx_pair] at hk
    obtain ⟨a, ha, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk
    obtain ⟨b, hb, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk
    have hk' := (Result.ok_injective hk).symm
    subst hk'
    simp [absLIdxPair, dupId_lidx _ _ ha, dupId_lidx _ _ hb]
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hpe := lvl_eq_probe_abs hrel hinv hp
  rw [hkv] at hpe
  unfold Sim
  cases p with
  | some r =>
    have ho := (Result.ok_injective hrun).symm
    subst ho
    exact AOut.ok (lvlEq?_hit hpe.symm) hrel hinv (Ext.refl _) trivial
  | none =>
  rw [lvlEq?_miss hpe.symm]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hwf1 := (read_level_m_wf hinv hq1).1
  have hS1 := read_level_m_run hrel hinv hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS1
  | Ok lu =>
  obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := Sim.apply hS1
  rw [run_bind_ok hx1]
  refine AOut.rebase hext1 ?_
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hwf2 := (read_level_m_wf hinv1 hq2).1
  have hS2 := read_level_m_run hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS2
  | Ok lv =>
  obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := Sim.apply hS2
  rw [run_bind_ok hx2]
  refine AOut.rebase hext2 ?_
  obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have heq := ConRon.Refine.Level.is_equiv_refines (hwf1 lu rfl) (hwf2 lv rfl) ho1
  simp only at heq ⊢
  rw [heq]
  cases o1 with
  | none =>
    have ho := (Result.ok_injective hrun).symm
    subst ho
    exact AOut.ok rfl hrel2 hinv2 (Ext.refl _) trivial
  | some r =>
  obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have ho := (Result.ok_injective hrun).symm
  subst ho
  rw [arena.core.lvl_eq_set] at hst3
  obtain ⟨n, hn, hst3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst3
  obtain ⟨hm, hfit, hst3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst3
  obtain ⟨pp, hpp, hst3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst3
  obtain ⟨old, hm2⟩ := pp
  have hst : st3 = { st2 with caches := { st2.caches with lvl_eq_c := hm2 } } :=
    (Result.ok_injective hst3).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step lidxPair_eq2 absLIdxPair_surj absLIdxPair_inj
    hinv2.caches.lvlEqC hrel2.caches.lvlEqC hn hfit hpp
  rw [hkv] at h1
  let mp0 := if lst2.caches.lvlEqC.size < cacheCap then lst2.caches.lvlEqC else ∅
  let mp2 := mp0.insert (absLIdx u, absLIdx v) r
  exact AOut.ok (lst' := { lst2 with caches := { lst2.caches with lvlEqC := mp2 } }) rfl
    { hrel2 with caches := { hrel2.caches with lvlEqC := h1 } }
    { hinv2 with caches := { hinv2.caches with lvlEqC := h2 } } (Ext.refl _) trivial

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
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o} {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hR : ResolveInv (ConRon.Refine.absMode mode) Good) (hg : Good lf lst)
    (hcv : ResolvesAt Good lf [absEIdx cv.ty])
    (hrun : arena.checker_split.install_constant_val pers vis st mode rf cv = ok o) :
    Sim absIConstantVal (fun _ => True) pers lst o
      (installConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  sorry

/-- `install_value_tail` is `install_value`'s tail past the annotation. -/
theorem install_value_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {value_a : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.install_value_tail pers vis st rf cv value_a = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (installValueTailSpec (lf.restrictTo (absU vis)) (absIConstantVal cv)
        (absEIdx value_a)) := by
  sorry

/-- **`install_value` ⊑ `installValue`** — the value half of
`check{Defn,Thm,Opaque}Val` minus its inference. -/
theorem install_value_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o} {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hR : ResolveInv (ConRon.Refine.absMode mode) Good) (hg : Good lf lst)
    (hv : ResolvesAt Good lf [absEIdx value])
    (hrun : arena.checker_split.install_value pers vis st mode rf cv value = ok o) :
    Sim absEIdx (fun _ => True) pers lst o
      (installValue (ConRon.Refine.absMode mode) (lf.restrictTo (absU vis))
        (absIConstantVal cv) (absEIdx value)) := by
  sorry

/-- `check_value_group_value` is `check_value_group`'s middle: the theorem's
is-a-proposition test and, for a theorem, the value's guards and annotation.

**Open, and stopped on a divergence** (task #97-P5-Top round 3).  The glue is
written in the round-3 log (`is_thm ; zero_level ; lvl_eq ; lift_fueled ;
install_value ; check_value_group_tail`, with `lvl_eq_refines` above), but it
closes only with three clauses the statement does not have and, by the
coordinator's round-3 rule, must not grow:

* the NOT-A-PROPOSITION decline: the Rust fails with the constant message
  `M_THM_NOT_PROP`, the twin with `s!"… {← readName g.cvA.name} …"` — a store
  READ on the twin side only, which throws `.internal` where the name does not
  decode, so the kinds differ there (the same divergence as `checkDecl`'s
  `.defnDecl` arm, round 4 §4);
* `Good` across `lvlEq?` and `installValue` (two `ResolveInv` fields), needed
  only because `install_value_refines` and the tail's Core front door take
  `Good`/`EResolves` — the front doors' tag-versus-view divergence (task
  #97-P5-0's finding 3). -/
theorem check_value_group_value_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    {u : arena.handle.LIdx} {o} {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hR : ResolveInv (ConRon.Refine.absMode mode) Good) (hg : Good lf lst)
    (hvg : VGResolves Good lf (absValueGroup g))
    (hrun : arena.checker_split.check_value_group_value pers vis st mode rf g u
      = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkValueGroupValueSpec (ConRon.Refine.absMode mode)
        (lf.restrictTo (absU vis)) (absValueGroup g) (absLIdx u)) := by
  sorry

/-- `check_value_group_tail` is `check_value_group`'s tail: the value's type
against the declared one.

**Open, and stopped on a divergence** (task #97-P5-Top round 3): the
type-mismatch decline is `Invalid (value_kind_word g.kind)` in the Rust and
`s!"type mismatch in {g.kind.word} {← readName g.cvA.name}"` in the twin — a
twin-only store read that throws `.internal` at a dangling name.  Everything
else composes from the statement's own hypotheses (`infer_type_core`,
`is_def_eq_core` at the prefix view, `ResolveInv.infer`, `VGResolves`). -/
theorem check_value_group_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    {jv : arena.handle.EIdx} {o} {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hR : ResolveInv (ConRon.Refine.absMode mode) Good) (hg : Good lf lst)
    (hvg : VGResolves Good lf (absValueGroup g))
    (hjv : ExprOps.EResolves lst (absEIdx jv))
    (hrun : arena.checker_split.check_value_group_tail pers vis st mode rf g jv
      = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkValueGroupTailSpec (ConRon.Refine.absMode mode)
        (lf.restrictTo (absU vis)) (absValueGroup g) (absEIdx jv)) := by
  sorry

/-- **`check_value_group` ⊑ `checkValueGroup`** — the check half of a value
declaration, at the environment the constant was installed at.

**PROVED** (task #97-P5-Top round 2), under ruling 2's precondition:
`infer_type_core ; ensure_sort_core ; check_value_group_value`, the first two
through `Refine2/Core`'s front doors at the prefix view `CoreCtx vis rf
(lf.restrictTo (absU vis))` (`IFEnvInv.coreCtxAt`) and the knot at
`checkFuel` (`knotRel_checkFuel'`).  The Core entries' own side conditions
come from the precondition: `EResolves` of the declared type (task #97-P5-0's
finding 3) is `VGResolves` at the entry state; the inferred type resolves by
`ResolveInv.infer` at the twin's own run; and `ensure_sort_core`'s
`AnswerResolves` of the whnf answer (task #97-P5-Arms' finding 14) is
`ResolveInv.whnf` at the twin run `KnotRel.whnf` produces, carried to every
twin state related to the Rust post-state by `EResolves.of_rel`. -/
theorem check_value_group_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup} {o}
    {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hR : ResolveInv (ConRon.Refine.absMode mode) Good) (hg : Good lf lst)
    (hvg : VGResolves Good lf (absValueGroup g))
    (hrun : arena.checker_split.check_value_group pers vis st mode rf g = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o
      (checkValueGroup (ConRon.Refine.absMode mode) (lf.restrictTo (absU vis))
        (absValueGroup g)) := by
  have hctx := IFEnvInv.coreCtxAt vis hfe hfinv
  have hres : ExprOps.EResolves lst (absEIdx g.cv_a.ty) := (hvg lst hg).1
  rw [arena.checker_split.check_value_group] at hrun
  unfold Sim
  rw [checkValueGroup_unfold,
    show (absValueGroup g).cvA.type = absEIdx g.cv_a.ty from rfl]
  have h0 : absU (0#u64) = 0 := rfl
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := infer_type_core_refines knotRel_checkFuel' hrel hinv hctx hrel.storeWF
    hres check_fuel_abs hq1
  rw [h0] at hS1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS1
  | Ok stype =>
  obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := Sim.apply hS1
  obtain ⟨hres1, hg1⟩ := hR.infer hg hres hx1
  -- the whnf answer `ensure_sort_core` dispatches on resolves: the twin's does
  -- (`ResolveInv.whnf`), and every twin state related to the Rust's views alike
  have hwhnf : ∀ p, arena.core.knot_whnf pers vis st1 mode arena.core.LANE_FULL
      arena.core.CHECK_FUEL rf 0#u64 stype = ok p → AnswerResolves pers p := by
    intro p hp w hw lst' hrel'
    have hW := knotRel_checkFuel'.whnf hrel1 hinv1 hctx hrel1.storeWF hres1
      check_fuel_abs hp
    rw [laneKnot_full, h0] at hW
    obtain ⟨p1, p2⟩ := p
    simp only at hw
    subst hw
    obtain ⟨lst2, hx2, hrel2, -, -, -⟩ := Sim.apply hW
    exact EResolves.of_rel hrel2 hrel' (hR.whnf hg1 hres1 hx2)
  rw [run_bind_ok hx1]
  refine AOut.rebase hext1 ?_
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := ensure_sort_core_refines knotRel_checkFuel' hrel1 hinv1 hctx hrel1.storeWF
    hres1 check_fuel_abs hwhnf hq2
  rw [h0] at hS2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS2
  | Ok u =>
  obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := Sim.apply hS2
  have hg2 := hR.ensureSort hg1 hres1 hx2
  rw [run_bind_ok hx2]
  refine AOut.rebase hext2 ?_
  exact check_value_group_value_refines hrel2 hinv2 hfe hfinv hR hg2 hvg hrun


/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.or_else_attempt_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms or_else_attempt_refines

/-- info: 'ConRon.Refine2.is_rec_info_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_rec_info_refines

/-- info: 'ConRon.Refine2.memo_b_get_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_b_get_refines

/-- info: 'ConRon.Refine2.is_thm_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_thm_refines

/-- info: 'ConRon.Refine2.lvl_eq_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lvl_eq_refines

end ConRon.Refine2
