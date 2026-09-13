import ConRon.Refine.TypeChecker
import ConRon.Refine.CheckerC
import ConRon.Refine.Pins
import ConRon.Refine.CoreKNatOps
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKLits
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsMeta
import ConLeche.Kernel.DeclCheck

/-! # `kernel::checker`'s pin gate — the checker's one error-recovery point

`CORE_PLAN.md` step 7 (task #56), `crates/con-ron-core/src/kernel/checker.rs`
lines 365-1232: the `Nat.div`/`Nat.mod` pin-certification gate
(`ConLeche/Kernel/Checker.lean:122-380`) and the `Lean.reduceNat` /
`Lean.reduceBool` identity gate (`:382-417`).  Forty-three Rust functions, all
covered below.  `checker.rs:92-363` is `Refine/Checker.lean`'s and
`:1234-end` the driver's; neither is touched here.

Four things make this file the interesting one of the task.

## 1. The loop, and `orElse`

`check_div_mod_pin_loop` (`checkDivModPinLoop`, `Checker.lean:338-360`;
`checkDivModPinLoopF`, `DeclCheck.lean:887-901`) is the **only** place the
checker recovers from a thrown error.  The Rust is an index recursion over the
`Vec<NatOpPinSet>` `check_decls` was given, the Lean a list recursion over the
global `natOpPinSets`, so the statement is about `(absPins pins).drop i`
(`absPins`/`absNatOpPinSet` are `Refine/Pins.lean`'s, task #43 — nothing new is
defined for them here), in the index-vs-list shape `Refine/FEnv.lean`'s
`absPrefixIdx` and `Refine/CoreKVec.lean`'s walks already use.

The per-variant attempt goes through `CheckerOps.orElse`, whose three run
lemmas and whose port-side decision are `Refine/CheckerC.lean`'s.  Its error
arm hands the continuation the **pre-attempt** state where the port's
`&mut CState` hands it the post-attempt one — task #24's flagged memo-policy
deviation.  `CheckerC.OrElseErrorStateSound` names exactly the missing fact,
and `check_div_mod_pin_loop_refines` **takes it as a hypothesis** rather than
weakening the statement, exactly as `Refine/CheckerC.lean`'s module note says
it must.  Nothing else about the loop is weakened.

`divModAttemptReason` and the `tried : List String` accumulator are not ported
(task #24, point 4: message rendering).  The Lean's `tried` is therefore
universally quantified in the loop's statement — on the success path it is
dead, and on the decline path nothing is claimed.

## 2. The pre-insertion environment is a visibility bound

Task #24's note: `check_div_mod_pin` and `check_reduce_pin` return the index
where the Lean returns `Unit`, because the two environments con-leche holds at
once (`env` pre-insertion, `env2` extended) are one index at two bounds.  Both
statements below are therefore about `checkDivModPinF ops fe fe2 c` /
`checkReducePinF ops fe fe2 c value` with `fe := lfe.restrictTo k_pre` and
`fe2 := lfe`, and both conclude `FEnvRel fe' lfe` — the bound restored.  That
goes through `Refine/FEnv.lean`'s `restrict_to_refines`/`restrict_to_wf`.
The `ops` record is at the **pre-insertion** index, because that is the index
the port hands `type_checker`.

## 3. The thirteen `cert_*` builders

Task #24's point 3: `divModCertStmts`' local `let`-bound builders are named
functions (§3.4 forbids closures), so each is a closed `Expr` equality in the
`Refine/BasisTables.lean` spirit — a value, not a walk.  `core_k::nat_eq_ap2`
is reused and is already refined (`Refine/CoreKLits.lean`).

## 4. What travels as a hypothesis

Task #56's files are written in parallel, so — as `Refine/TrustAxioms.lean`
and the eleven task-#49 `CoreK*` files do — a sibling's refinement lemma is an
explicit hypothesis here, never re-proved:

* `EqBasisPinnedSpec` — `basis_pins::eq_basis_pinned` (`Refine/BasisPins.lean`);
* `TrustGuardsSpec` / `TrustPinsSpec` — `trust_axioms::reduce_stored_ok`,
  `reduce_elem_ok`, `reduce_pin_guard`, `reduce_decl_pin`, `reduce_cert_var`
  (`Refine/TrustAxioms.lean`);
* the knot, as `Core.Wrappers mode fuel` with `core_k.check_fuel = ok fuel`
  (task #55), on every lemma that runs a core entry point.

`std_axioms::one_level` is another task-#56 file's too; as in
`Refine/TrustAxioms.lean` it is small enough to be proved here as a step.

## Deviations found, beyond DESIGN.md's task-#24 list

**`div_mod_env_guard`'s dependency clause is weaker than `divModEnvGuardF`'s.**
The Lean is `(natOpDeps c).all (natOpStoredOkF fe2)`
(`DeclCheck.lean:233-238`), whose per-dependency test is "stored as a
level-monomorphic definition **and** at the pinned type (`natOpTyPinnedF`)".
The port calls `core_k::deps_all_stored` (`core_k.rs:1645`), whose
per-dependency test is `core_k::defn_lp_empty` — the
level-monomorphic-definition half only.  `core_k::nat_op_stored_ok`
(`core_k.rs:1827`) is the faithful spelling and is *already in the port*; it is
simply not the one `checker::div_mod_env_guard` calls.  The direction is the
dangerous one — the port's gate passes streams con-leche's declines — so this
is recorded rather than papered over: `div_mod_env_guard_refines` carries
`DepsTyPinned` (the exact missing conjunct) as a named hypothesis, the way
`OrElseErrorStateSound` carries task #24's state gap, and the fix is a
one-call change in `checker.rs`.

## What is proved and what is stated

Everything in `checker.rs:365-1232` is covered, and everything *pure* is
proved: the two eight-way variant dispatches (`div_mod_decl_pin`,
`div_mod_cert_proofs`), all twenty-two closed `cert_*` builders, the two
`Vec`-literal helpers, `div_mod_cert_applied`, the whole guard cascade
(`div_mod_cert_guard`, `hyps_resolve`, `hyps_subst(_from)`,
`div_mod_pin_guard`, `div_mod_certs_guard(_from)`, `bool_ctor_typed`,
`div_mod_env_guard`), and the one stateful leaf whose only core call is a
single `isDefEq` (`check_reduce_identity`).

The eight open ones are stated exactly and each carries a one-line note: the
closed statement table `div_mod_cert_stmts`, the two `check_div_mod_certs`
recursions, the per-variant attempt, **the loop**, and the three install
gates.  All but the first are stateful walks over the knot's entry points; the
first is long rather than hard.

`sorry` count in this file: 8.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.CheckerPins

/-! ## Abstractions this file needs

`absPins`/`absNatOpPinSet` are `Refine/Pins.lean`'s and are reused unchanged.
What is missing is the *well-formedness* of a pin variant and the abstraction
of `divModCertStmts`' result type, a `Vec<(Vec<Expr>, Expr)>`. -/

/-- One pinned open statement: the hypothesis types and the characteristic
equation.  **To be unified into `Abs.lean`.** -/
def absStmt (p : alloc.vec.Vec expr.Expr × expr.Expr) :
    List ConLeche.Expr × ConLeche.Expr :=
  (absExprs p.1, absExpr p.2)

/-- `div_mod_cert_stmts`' result as the cited `List (List Expr × Expr)`, in
`Vec` order.  **To be unified into `Abs.lean`.** -/
def absStmts (v : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)) :
    List (List ConLeche.Expr × ConLeche.Expr) :=
  v.val.map absStmt

/-- Every component of a pinned statement list is a well-formed term.
**To be unified into `Abs.lean`.** -/
def StmtsWF (v : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)) : Prop :=
  ∀ p ∈ v.val, ExprsWF p.1 ∧ ExprWF p.2

/-- A pin variant's seventeen fields are well formed.  **To be unified into
`Abs.lean`** (beside `absNatOpPinSet`, `Refine/Pins.lean`). -/
structure NatOpPinSetWF (s : nat_op_pins.NatOpPinSet) : Prop where
  toolchain : StrWF s.toolchain
  divPin : ExprWF s.div_pin
  modPin : ExprWF s.mod_pin
  gcdPin : ExprWF s.gcd_pin
  landPin : ExprWF s.land_pin
  lorPin : ExprWF s.lor_pin
  xorPin : ExprWF s.xor_pin
  shiftLeftPin : ExprWF s.shift_left_pin
  shiftRightPin : ExprWF s.shift_right_pin
  divProofs : ExprsWF s.div_proofs
  modProofs : ExprsWF s.mod_proofs
  gcdProofs : ExprsWF s.gcd_proofs
  landProofs : ExprsWF s.land_proofs
  lorProofs : ExprsWF s.lor_proofs
  xorProofs : ExprsWF s.xor_proofs
  shiftLeftProofs : ExprsWF s.shift_left_proofs
  shiftRightProofs : ExprsWF s.shift_right_proofs

/-- Every variant of a pin list is well formed. -/
def PinsWF (ps : alloc.vec.Vec nat_op_pins.NatOpPinSet) : Prop :=
  ∀ s ∈ ps.val, NatOpPinSetWF s

/-! ## The imported siblings' statements -/

/-- **Imported** (`Refine/BasisPins.lean`, task #56's sibling):
`basis_pins::eq_basis_pinned` is the exact `ConstantInfo` comparison
`decide (fe.find? eqName = some eqA)` of `divModEnvGuard`'s third clause. -/
def EqBasisPinnedSpec (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  ∀ r : Bool, basis_pins.eq_basis_pinned fe = ok r →
    r = decide (lfe.find? ConLeche.eqName = some ConLeche.eqA)

/-- **Imported** (`Refine/TrustAxioms.lean`, task #56's sibling): the three
environment guards of the compiler-trust opaque gate, at the index
(`DeclCheck.lean:272-308`). -/
structure TrustGuardsSpec (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop where
  storedOk : ∀ (c : name.Name) (r : Bool), NameWF c →
    trust_axioms.reduce_stored_ok fe c = ok r →
      r = ConLeche.reduceStoredOkF lfe (absName c)
  elemOk : ∀ (c : name.Name) (r : Bool), NameWF c →
    trust_axioms.reduce_elem_ok fe c = ok r →
      r = ConLeche.reduceElemOkF lfe (absName c)
  pinGuard : ∀ (c : name.Name) (r : Bool), NameWF c →
    trust_axioms.reduce_pin_guard fe c = ok r →
      r = ConLeche.reducePinGuardF lfe (absName c)

/-- **Imported** (`Refine/TrustAxioms.lean`): the two hand-pinned values of
`ConLeche/Kernel/TrustPins.lean` the reduce gate compares against. -/
structure TrustPinsSpec : Prop where
  declPin : ∀ (c : name.Name) (e : expr.Expr), NameWF c →
    trust_axioms.reduce_decl_pin c = ok e →
      absExpr e = ConLeche.reduceDeclPin (absName c) ∧ ExprWF e
  certVar : ∀ (c : name.Name) (e : expr.Expr), NameWF c →
    trust_axioms.reduce_cert_var c = ok e →
      absExpr e = ConLeche.reduceCertVar (absName c) ∧ ExprWF e

/-- **The deviation found here, named** (module note).  The port's
`div_mod_env_guard` tests each dependency of `c` with `core_k::defn_lp_empty`
(`CoreKNatOps`' `natOpDepStored`) where `divModEnvGuardF` tests it with
`natOpStoredOkF`, which additionally demands the pinned type.  This says the
two verdicts coincide at `c` in `lfe` — the exact conjunct the port drops, and
the only thing `div_mod_env_guard_refines` needs beyond the sibling lemmas.
The port-side fix is to call `core_k::nat_op_stored_ok`, which exists. -/
def DepsTyPinned (lfe : ConLeche.FEnv) (c : ConLeche.Name) : Prop :=
  (ConLeche.natOpDeps c).all (CoreK.natOpDepStored lfe)
    = (ConLeche.natOpDeps c).all (ConLeche.natOpStoredOkF lfe)

/-! ## `std_axioms::one_level`, as a step

Another task-#56 file's (`Refine/StdAxioms.lean`); proved here as a step, as
`Refine/TrustAxioms.lean` does, so that nothing in this file imports a
sibling. -/

/-- `std_axioms::one_level` — `[.succ .zero]`, the universe argument every
`Eq` application in this family carries (`StdAxioms.lean:408-412 oneLevel`). -/
theorem one_level_step {v : alloc.vec.Vec level.Level}
    (h : std_axioms.one_level = ok v) :
    absLevels v = [.succ .zero] ∧ LevelsWF v := by
  rw [std_axioms.one_level] at h
  obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  have hval : v.val = [s] := by rw [vec_push_val h]; simp
  refine ⟨?_, ?_⟩
  · rw [absLevels, hval]
    simp only [List.map_cons, List.map_nil, Level.succ_refines hs,
      Level.zero_refines hz]
  · intro u hu
    rw [hval] at hu
    simp only [List.mem_singleton] at hu
    rw [hu]; exact LevelWF.succ (LevelWF.zero hz) hs

/-! ## The name test, factored

Every dispatch in this file is the same `if name::beq(c, &pin) then … else …`
against the cited `if c = pin then … else …`.  One lemma turns a Rust step into
the two Lean branches. -/

/-- One arm of a `name::beq` dispatch: the Rust `if` and the Lean `if` agree. -/
theorem beq_branch {c n : name.Name} {ln : ConLeche.Name} {α : Type}
    {b : Bool} {x y : Result α} {r : α} (hc : NameWF c)
    (hn : absName n = ln ∧ NameWF n) (hb : name.beq c n = ok b)
    (h : (if b then x else y) = ok r) :
    (absName c = ln ∧ x = ok r) ∨ (absName c ≠ ln ∧ y = ok r) := by
  rw [Name.beq_refines hc hn.2 hb, hn.1] at h
  by_cases hq : absName c = ln
  · exact Or.inl ⟨hq, by simpa [hq] using h⟩
  · exact Or.inr ⟨hq, by simpa [hq] using h⟩

/-! ## The variant's pin and proofs (`Checker.lean:122-142`) -/

/-- `ConLeche/Kernel/Checker.lean:122-130 divModDeclPin` —
`checker::div_mod_decl_pin` refines it: the pinned defining expression of a
pin-certified WF-recursive op in one pin variant. -/
theorem div_mod_decl_pin_refines {ps : nat_op_pins.NatOpPinSet} {c : name.Name}
    {e : expr.Expr} (hps : NatOpPinSetWF ps) (hc : NameWF c)
    (h : checker.div_mod_decl_pin ps c = ok e) :
    absExpr e = ConLeche.divModDeclPin (absNatOpPinSet ps) (absName c) ∧ ExprWF e := by
  rw [checker.div_mod_decl_pin] at h
  rw [ConLeche.divModDeclPin]
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_div_name_refines hn) hb h with ⟨hq, h⟩ | ⟨hq, h⟩
  · rw [if_pos hq, Expr.dup_eq h]; exact ⟨rfl, hps.divPin⟩
  rw [if_neg hq]
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_gcd_name_refines hn1) hb1 h with ⟨hq1, h⟩ | ⟨hq1, h⟩
  · rw [if_pos hq1, Expr.dup_eq h]; exact ⟨rfl, hps.gcdPin⟩
  rw [if_neg hq1]
  obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_land_name_refines hn2) hb2 h with ⟨hq2, h⟩ | ⟨hq2, h⟩
  · rw [if_pos hq2, Expr.dup_eq h]; exact ⟨rfl, hps.landPin⟩
  rw [if_neg hq2]
  obtain ⟨n3, hn3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_lor_name_refines hn3) hb3 h with ⟨hq3, h⟩ | ⟨hq3, h⟩
  · rw [if_pos hq3, Expr.dup_eq h]; exact ⟨rfl, hps.lorPin⟩
  rw [if_neg hq3]
  obtain ⟨n4, hn4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_xor_name_refines hn4) hb4 h with ⟨hq4, h⟩ | ⟨hq4, h⟩
  · rw [if_pos hq4, Expr.dup_eq h]; exact ⟨rfl, hps.xorPin⟩
  rw [if_neg hq4]
  obtain ⟨n5, hn5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_shift_left_name_refines hn5) hb5 h with ⟨hq5, h⟩ | ⟨hq5, h⟩
  · rw [if_pos hq5, Expr.dup_eq h]; exact ⟨rfl, hps.shiftLeftPin⟩
  rw [if_neg hq5]
  obtain ⟨n6, hn6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_shift_right_name_refines hn6) hb6 h with ⟨hq6, h⟩ | ⟨hq6, h⟩
  · rw [if_pos hq6, Expr.dup_eq h]; exact ⟨rfl, hps.shiftRightPin⟩
  rw [if_neg hq6, Expr.dup_eq h]; exact ⟨rfl, hps.modPin⟩

/-- `ConLeche/Kernel/Checker.lean:132-142 divModCertProofs` —
`checker::div_mod_cert_proofs` refines it: the variant's certificate proof
terms, one per statement of `divModCertStmts`. -/
theorem div_mod_cert_proofs_refines {ps : nat_op_pins.NatOpPinSet} {c : name.Name}
    {v : alloc.vec.Vec expr.Expr} (hps : NatOpPinSetWF ps) (hc : NameWF c)
    (h : checker.div_mod_cert_proofs ps c = ok v) :
    absExprs v = ConLeche.divModCertProofs (absNatOpPinSet ps) (absName c) ∧ ExprsWF v := by
  have copy : ∀ {es r : alloc.vec.Vec expr.Expr}, ExprsWF es →
      env.exprs_copy es = ok r → absExprs r = absExprs es ∧ ExprsWF r := by
    intro es r hes hcp
    have hv : r.val = es.val := CoreK.env_exprs_copy_val hcp
    exact ⟨by rw [absExprs, absExprs, hv],
      by intro x hx; exact hes x (by rw [← hv]; exact hx)⟩
  rw [checker.div_mod_cert_proofs] at h
  rw [ConLeche.divModCertProofs]
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_div_name_refines hn) hb h with ⟨hq, h⟩ | ⟨hq, h⟩
  · rw [if_pos hq]; exact copy hps.divProofs h
  rw [if_neg hq]
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_gcd_name_refines hn1) hb1 h with ⟨hq1, h⟩ | ⟨hq1, h⟩
  · rw [if_pos hq1]; exact copy hps.gcdProofs h
  rw [if_neg hq1]
  obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_land_name_refines hn2) hb2 h with ⟨hq2, h⟩ | ⟨hq2, h⟩
  · rw [if_pos hq2]; exact copy hps.landProofs h
  rw [if_neg hq2]
  obtain ⟨n3, hn3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_lor_name_refines hn3) hb3 h with ⟨hq3, h⟩ | ⟨hq3, h⟩
  · rw [if_pos hq3]; exact copy hps.lorProofs h
  rw [if_neg hq3]
  obtain ⟨n4, hn4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_xor_name_refines hn4) hb4 h with ⟨hq4, h⟩ | ⟨hq4, h⟩
  · rw [if_pos hq4]; exact copy hps.xorProofs h
  rw [if_neg hq4]
  obtain ⟨n5, hn5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_shift_left_name_refines hn5) hb5 h with ⟨hq5, h⟩ | ⟨hq5, h⟩
  · rw [if_pos hq5]; exact copy hps.shiftLeftProofs h
  rw [if_neg hq5]
  obtain ⟨n6, hn6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_shift_right_name_refines hn6) hb6 h with ⟨hq6, h⟩ | ⟨hq6, h⟩
  · rw [if_pos hq6]; exact copy hps.shiftRightProofs h
  rw [if_neg hq6]; exact copy hps.modProofs h

/-! ## The thirteen local builders (`Checker.lean:144-222 divModCertStmts`)

Task #24's point 3.  Each is a closed `Expr`, so each lemma is a closed
equality against the cited `let`-bound local — the `Refine/BasisTables.lean`
idiom, with `core_k::nat_eq_ap2` (`Refine/CoreKLits.lean`) doing the
application spines. -/

/-- The local `natTy : Expr := .const natName []`. -/
theorem cert_nat_ty_refines {e : expr.Expr} (h : checker.cert_nat_ty = ok e) :
    absExpr e = .const ConLeche.natName [] ∧ ExprWF e := by
  rw [checker.cert_nat_ty] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := BasisNames.nat_name_refines hn
  exact ⟨by rw [Expr.mk_const_refines h, habs, CoreK.absLevels_new],
    ExprWF.mk_const hwf CoreK.levelsWF_new h⟩

/-- The local `x : Expr := .fvar 0 natTy`. -/
theorem cert_x_refines {e : expr.Expr} (h : checker.cert_x = ok e) :
    absExpr e = .fvar 0 (.const ConLeche.natName []) ∧ ExprWF e := by
  rw [checker.cert_x] at h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨htabs, htwf⟩ := cert_nat_ty_refines ht
  exact ⟨by rw [Expr.fvar_refines h, htabs]; rfl, ExprWF.fvar htwf h⟩

/-- The local `y : Expr := .fvar 1 natTy`. -/
theorem cert_y_refines {e : expr.Expr} (h : checker.cert_y = ok e) :
    absExpr e = .fvar 1 (.const ConLeche.natName []) ∧ ExprWF e := by
  rw [checker.cert_y] at h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨htabs, htwf⟩ := cert_nat_ty_refines ht
  exact ⟨by rw [Expr.fvar_refines h, htabs]; rfl, ExprWF.fvar htwf h⟩

/-- The local `z := Nat.zero`. -/
theorem cert_zero_refines {e : expr.Expr} (h : checker.cert_zero = ok e) :
    absExpr e = .const ConLeche.natZeroName [] ∧ ExprWF e := by
  rw [checker.cert_zero] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := BasisNames.nat_zero_name_refines hn
  exact ⟨by rw [Expr.mk_const_refines h, habs, CoreK.absLevels_new],
    ExprWF.mk_const hwf CoreK.levelsWF_new h⟩

/-- The local `one := Nat.succ Nat.zero` — a literal is never used, so that the
model side consumes the statements through `NatOpsOk`'s literal semantics. -/
theorem cert_one_refines {e : expr.Expr} (h : checker.cert_one = ok e) :
    absExpr e = .app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName [])
      ∧ ExprWF e := by
  rw [checker.cert_one] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := BasisNames.nat_zero_name_refines hn
  have hzwf : ExprWF z := ExprWF.mk_const hwf CoreK.levelsWF_new hz
  obtain ⟨hsabs, hswf⟩ :=
    CoreK.nat_eq_s_refines hzwf (fun n hn => BasisNames.nat_succ_name_refines hn) h
  refine ⟨?_, hswf⟩
  rw [hsabs, Expr.mk_const_refines hz, habs, CoreK.absLevels_new]

/-- The local `two := Nat.succ one`. -/
theorem cert_two_refines {e : expr.Expr} (h : checker.cert_two = ok e) :
    absExpr e = .app (.const ConLeche.natSuccName [])
        (.app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName []))
      ∧ ExprWF e := by
  rw [checker.cert_two] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := cert_one_refines ho
  obtain ⟨hsabs, hswf⟩ :=
    CoreK.nat_eq_s_refines howf (fun n hn => BasisNames.nat_succ_name_refines hn) h
  exact ⟨by rw [hsabs, hoabs], hswf⟩

/-- The local `bT := Bool.true`. -/
theorem cert_b_true_refines {e : expr.Expr} (h : checker.cert_b_true = ok e) :
    absExpr e = .const ConLeche.boolTrueName [] ∧ ExprWF e := by
  rw [checker.cert_b_true] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.bool_true_name_refines hn
  exact ⟨by rw [Expr.mk_const_refines h, habs, CoreK.absLevels_new],
    ExprWF.mk_const hwf CoreK.levelsWF_new h⟩

/-- The local `bF := Bool.false`. -/
theorem cert_b_false_refines {e : expr.Expr} (h : checker.cert_b_false = ok e) :
    absExpr e = .const ConLeche.boolFalseName [] ∧ ExprWF e := by
  rw [checker.cert_b_false] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.bool_false_name_refines hn
  exact ⟨by rw [Expr.mk_const_refines h, habs, CoreK.absLevels_new],
    ExprWF.mk_const hwf CoreK.levelsWF_new h⟩

/-- The local `ble2 a b := Nat.ble a b` — the guards are spelled with the
already-certified `Nat.ble`, never the `Nat.le`/`Nat.lt` `Prop` inductives. -/
theorem cert_ble2_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_ble2 a b = ok e) :
    absExpr e = .app (.app (.const ConLeche.natBleName []) (absExpr a)) (absExpr b)
      ∧ ExprWF e := by
  rw [checker.cert_ble2] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.nat_ble_name_refines hn
  obtain ⟨hab, hwf2⟩ := CoreK.nat_eq_ap2_refines hwf ha hb h
  exact ⟨by rw [hab, habs], hwf2⟩

/-- The local `sub2 a b := Nat.sub a b`. -/
theorem cert_sub2_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_sub2 a b = ok e) :
    absExpr e = .app (.app (.const ConLeche.natSubName []) (absExpr a)) (absExpr b)
      ∧ ExprWF e := by
  rw [checker.cert_sub2] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.nat_sub_name_refines hn
  obtain ⟨hab, hwf2⟩ := CoreK.nat_eq_ap2_refines hwf ha hb h
  exact ⟨by rw [hab, habs], hwf2⟩

/-- The local `mod2 a b := Nat.mod a b`. -/
theorem cert_mod2_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_mod2 a b = ok e) :
    absExpr e = .app (.app (.const ConLeche.natModName []) (absExpr a)) (absExpr b)
      ∧ ExprWF e := by
  rw [checker.cert_mod2] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.nat_mod_name_refines hn
  obtain ⟨hab, hwf2⟩ := CoreK.nat_eq_ap2_refines hwf ha hb h
  exact ⟨by rw [hab, habs], hwf2⟩

/-- The local `div2 a b := Nat.div a b`. -/
theorem cert_div2_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_div2 a b = ok e) :
    absExpr e = .app (.app (.const ConLeche.natDivName []) (absExpr a)) (absExpr b)
      ∧ ExprWF e := by
  rw [checker.cert_div2] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.nat_div_name_refines hn
  obtain ⟨hab, hwf2⟩ := CoreK.nat_eq_ap2_refines hwf ha hb h
  exact ⟨by rw [hab, habs], hwf2⟩

/-- The local `add2 a b := Nat.add a b`. -/
theorem cert_add2_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_add2 a b = ok e) :
    absExpr e = .app (.app (.const ConLeche.natAddName []) (absExpr a)) (absExpr b)
      ∧ ExprWF e := by
  rw [checker.cert_add2] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.nat_add_name_refines hn
  obtain ⟨hab, hwf2⟩ := CoreK.nat_eq_ap2_refines hwf ha hb h
  exact ⟨by rw [hab, habs], hwf2⟩

/-- The local `mul2 a b := Nat.mul a b`. -/
theorem cert_mul2_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_mul2 a b = ok e) :
    absExpr e = .app (.app (.const ConLeche.natMulName []) (absExpr a)) (absExpr b)
      ∧ ExprWF e := by
  rw [checker.cert_mul2] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := CoreK.nat_mul_name_refines hn
  obtain ⟨hab, hwf2⟩ := CoreK.nat_eq_ap2_refines hwf ha hb h
  exact ⟨by rw [hab, habs], hwf2⟩

/-- The local `op2 a b := c a b` — the op's self-reference is `.const c []`,
substituted with the stored annotated value before checking. -/
theorem cert_op2_refines {c : name.Name} {a b e : expr.Expr} (hc : NameWF c)
    (ha : ExprWF a) (hb : ExprWF b) (h : checker.cert_op2 c a b = ok e) :
    absExpr e = .app (.app (.const (absName c) []) (absExpr a)) (absExpr b)
      ∧ ExprWF e := by
  rw [checker.cert_op2] at h
  exact CoreK.nat_eq_ap2_refines hc ha hb h

/-- The local `eqB a b := Eq.{1} Bool a b`. -/
theorem cert_eq_b_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_eq_b a b = ok e) :
    absExpr e = .app (.app (.app (.const ConLeche.eqName [.succ .zero])
        (.const ConLeche.boolName [])) (absExpr a)) (absExpr b) ∧ ExprWF e := by
  rw [checker.cert_eq_b] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := BasisNames.eq_name_refines hn
  obtain ⟨hvabs, hvwf⟩ := one_level_step hv
  obtain ⟨hn1abs, hn1wf⟩ := CoreK.bool_name_refines hn1
  have h0wf : ExprWF e0 := ExprWF.mk_const hnwf hvwf he0
  have h1wf : ExprWF e1 := ExprWF.mk_const hn1wf CoreK.levelsWF_new he1
  have h2wf : ExprWF e2 := ExprWF.app h0wf h1wf he2
  have h3wf : ExprWF e3 := ExprWF.app h2wf ha he3
  refine ⟨?_, ExprWF.app h3wf hb h⟩
  rw [Expr.app_refines h, Expr.app_refines he3, Expr.app_refines he2,
    Expr.mk_const_refines he0, Expr.mk_const_refines he1, hnabs, hvabs, hn1abs,
    CoreK.absLevels_new]

/-- The local `eqN a b := Eq.{1} Nat a b`. -/
theorem cert_eq_n_refines {a b e : expr.Expr} (ha : ExprWF a) (hb : ExprWF b)
    (h : checker.cert_eq_n a b = ok e) :
    absExpr e = .app (.app (.app (.const ConLeche.eqName [.succ .zero])
        (.const ConLeche.natName [])) (absExpr a)) (absExpr b) ∧ ExprWF e := by
  rw [checker.cert_eq_n] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := BasisNames.eq_name_refines hn
  obtain ⟨hvabs, hvwf⟩ := one_level_step hv
  obtain ⟨h1abs, h1wf⟩ := cert_nat_ty_refines he1
  have h0wf : ExprWF e0 := ExprWF.mk_const hnwf hvwf he0
  have h2wf : ExprWF e2 := ExprWF.app h0wf h1wf he2
  have h3wf : ExprWF e3 := ExprWF.app h2wf ha he3
  refine ⟨?_, ExprWF.app h3wf hb h⟩
  rw [Expr.app_refines h, Expr.app_refines he3, Expr.app_refines he2,
    Expr.mk_const_refines he0, hnabs, hvabs, h1abs]

/-- `op2 (div2 x two) (div2 y two)` — the bitwise certificates' recursive call
on the halves, written three times in the cited block. -/
theorem cert_halves_refines {c : name.Name} {e : expr.Expr} (hc : NameWF c)
    (h : checker.cert_halves c = ok e) :
    absExpr e = .app (.app (.const (absName c) [])
        (.app (.app (.const ConLeche.natDivName [])
          (.fvar 0 (.const ConLeche.natName [])))
          (.app (.const ConLeche.natSuccName [])
            (.app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName [])))))
        (.app (.app (.const ConLeche.natDivName [])
          (.fvar 1 (.const ConLeche.natName [])))
          (.app (.const ConLeche.natSuccName [])
            (.app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName []))))
      ∧ ExprWF e := by
  rw [checker.cert_halves] at h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨d1, hd1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨d2, hd2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxabs, hxwf⟩ := cert_x_refines hx
  obtain ⟨htabs, htwf⟩ := cert_two_refines ht
  obtain ⟨hyabs, hywf⟩ := cert_y_refines hy
  obtain ⟨hd1abs, hd1wf⟩ := cert_div2_refines hxwf htwf hd1
  obtain ⟨hd2abs, hd2wf⟩ := cert_div2_refines hywf htwf hd2
  obtain ⟨habs, hwf⟩ := cert_op2_refines hc hd1wf hd2wf h
  exact ⟨by rw [habs, hd1abs, hd2abs, hxabs, hyabs, htabs], hwf⟩

/-- The local `recRhs`: `Nat.succ (c (x - y) y)` for `Nat.div`, `c (x - y) y`
for `Nat.mod`. -/
theorem cert_rec_rhs_refines {c : name.Name} {e : expr.Expr} (hc : NameWF c)
    (h : checker.cert_rec_rhs c = ok e) :
    absExpr e =
        (if absName c = ConLeche.natDivName then
           .app (.const ConLeche.natSuccName [])
             (.app (.app (.const (absName c) [])
               (.app (.app (.const ConLeche.natSubName [])
                 (.fvar 0 (.const ConLeche.natName [])))
                 (.fvar 1 (.const ConLeche.natName []))))
               (.fvar 1 (.const ConLeche.natName [])))
         else
           .app (.app (.const (absName c) [])
             (.app (.app (.const ConLeche.natSubName [])
               (.fvar 0 (.const ConLeche.natName [])))
               (.fvar 1 (.const ConLeche.natName []))))
             (.fvar 1 (.const ConLeche.natName [])))
      ∧ ExprWF e := by
  rw [checker.cert_rec_rhs] at h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨st, hst, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxabs, hxwf⟩ := cert_x_refines hx
  obtain ⟨hyabs, hywf⟩ := cert_y_refines hy
  obtain ⟨hsabs, hswf⟩ := cert_sub2_refines hxwf hywf hs
  obtain ⟨hstabs, hstwf⟩ := cert_op2_refines hc hswf hywf hst
  rcases beq_branch hc (CoreK.nat_div_name_refines hn) hb h with ⟨hq, h⟩ | ⟨hq, h⟩
  · rw [if_pos hq]
    obtain ⟨hab, hwf⟩ :=
      CoreK.nat_eq_s_refines hstwf (fun n hn => BasisNames.nat_succ_name_refines hn) h
    exact ⟨by rw [hab, hstabs, hsabs, hxabs, hyabs], hwf⟩
  · rw [if_neg hq, ← Result.ok_injective h]
    exact ⟨by rw [hstabs, hsabs, hxabs, hyabs], hstwf⟩

/-- The local `baseRhs`: `Nat.zero` for `Nat.div`, `x` for `Nat.mod`. -/
theorem cert_base_rhs_refines {c : name.Name} {e : expr.Expr} (hc : NameWF c)
    (h : checker.cert_base_rhs c = ok e) :
    absExpr e = (if absName c = ConLeche.natDivName then
        .const ConLeche.natZeroName [] else .fvar 0 (.const ConLeche.natName []))
      ∧ ExprWF e := by
  rw [checker.cert_base_rhs] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_div_name_refines hn) hb h with ⟨hq, h⟩ | ⟨hq, h⟩
  · rw [if_pos hq]; exact cert_zero_refines h
  · rw [if_neg hq]; exact cert_x_refines h

/-- `con-leche: none` — the one-element hypothesis list `[h]` of
`divModCertStmts` (a `Vec` literal needs a push, task #18's point 10). -/
theorem cert_hyp1_refines {h1 : expr.Expr} {v : alloc.vec.Vec expr.Expr}
    (hh : ExprWF h1) (h : checker.cert_hyp1 h1 = ok v) :
    absExprs v = [absExpr h1] ∧ ExprsWF v := by
  rw [checker.cert_hyp1] at h
  have hval : v.val = [h1] := by rw [vec_push_val h]; simp
  refine ⟨by rw [absExprs, hval]; simp, ?_⟩
  intro x hx; rw [hval] at hx; simp only [List.mem_singleton] at hx
  rw [hx]; exact hh

/-- `con-leche: none` — the two-element hypothesis list `[h1, h2]`. -/
theorem cert_hyp2_refines {h1 h2 : expr.Expr} {v : alloc.vec.Vec expr.Expr}
    (hh1 : ExprWF h1) (hh2 : ExprWF h2) (h : checker.cert_hyp2 h1 h2 = ok v) :
    absExprs v = [absExpr h1, absExpr h2] ∧ ExprsWF v := by
  rw [checker.cert_hyp2] at h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  have hwval : w.val = [h1] := by rw [vec_push_val hw]; simp
  have hval : v.val = [h1, h2] := by rw [vec_push_val h, hwval]; simp
  refine ⟨by rw [absExprs, hval]; simp, ?_⟩
  intro x hx
  rw [hval] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  exacts [hh1, hh2]

/-! ## The statement table (`Checker.lean:144-222 divModCertStmts`) -/

/-- `ConLeche/Kernel/Checker.lean:144-222 divModCertStmts` —
`checker::div_mod_cert_stmts` refines it: the pinned characterization
statements of a pin-certified WF-recursive op, in *open* form over
`x := fvar 0`, `y := fvar 1`, per certificate a list of hypothesis types and
the characteristic equation `Eq Nat lhs rhs`. -/
theorem div_mod_cert_stmts_refines {c : name.Name}
    {v : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)} (hc : NameWF c)
    (h : checker.div_mod_cert_stmts c = ok v) :
    absStmts v = ConLeche.divModCertStmts (absName c) ∧ StmtsWF v := by
  -- `sorry`: eight `beq_branch` arms, each a forward chain through the
  -- builders above and two or three `Vec::push`es; mechanical, long.
  sorry

/-! ## The list plumbing, and `hyps_resolve`/`hyps_subst`

Out of `checker.rs` order on purpose: `div_mod_cert_guard` (next section)
*calls* `hyps_resolve`, so its lemma needs this one first.  Everything here is
the index-vs-list bookkeeping the three index recursions of the file share. -/

/-- The empty `Vec<Name>` is the empty list of level parameters (the guards
below all run `allLevelParamsDefined []`). -/
private theorem absNames_new : absNames (alloc.vec.Vec.new name.Name) = [] := rfl

/-- …and is well formed. -/
private theorem namesWF_new : NamesWF (alloc.vec.Vec.new name.Name) := by
  intro n hn; simp [alloc.vec.Vec.new] at hn

/-- The `u64` zero the field guards are called at. -/
private theorem u64_zero_val : ((0#u64 : Std.U64)).val = 0 := rfl

/-! ### The index-vs-list plumbing

The three index recursions below (`hyps_resolve`, `hyps_subst_from`,
`div_mod_certs_guard_from`) all read `hyps[i]` and step to `i + 1`, against a
Lean `List.all`/`List.map` of the *dropped tail*.  These four facts are what
turns one into the other; they are the `Refine/CoreKGuards.lean`
`env_exprs_copy_from_val` shape, restated for `absExprs`. -/

/-- A successful `Vec::index` is in range. -/
private theorem vec_index_lt {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length := by
  have hg := ExprOps.vec_index_getElem? h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at hg
  simp at hg

/-- …and answers the entry at that index. -/
private theorem vec_index_val {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x)
    (hlt : i.val < v.val.length) : v.val[i.val] = x := by
  have hg := ExprOps.vec_index_getElem? h
  rw [List.getElem?_eq_getElem hlt] at hg
  exact Option.some_injective _ hg

/-- Past the end, the abstracted statement tail is empty. -/
private theorem drop_absStmts_nil
    {v : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)} {k : Nat}
    (h : v.val.length ≤ k) : (absStmts v).drop k = [] := by
  rw [absStmts]
  exact List.drop_eq_nil_of_le (by simpa using h)

/-- In range, the abstracted statement tail peels off the indexed entry. -/
private theorem drop_absStmts_cons
    {v : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)} {k : Nat}
    {x : alloc.vec.Vec expr.Expr × expr.Expr} (hlt : k < v.val.length)
    (hx : v.val[k] = x) :
    (absStmts v).drop k = absStmt x :: (absStmts v).drop (k + 1) := by
  have hlt' : k < (absStmts v).length := by rw [absStmts, List.length_map]; exact hlt
  rw [List.drop_eq_getElem_cons hlt']
  congr 1
  simp only [absStmts, List.getElem_map, hx]

/-- Past the end, the abstracted tail is empty. -/
private theorem drop_absExprs_nil {v : alloc.vec.Vec expr.Expr} {k : Nat}
    (h : v.val.length ≤ k) : (absExprs v).drop k = [] := by
  rw [absExprs]
  exact List.drop_eq_nil_of_le (by simpa using h)

/-- In range, the abstracted tail peels off the indexed entry. -/
private theorem drop_absExprs_cons {v : alloc.vec.Vec expr.Expr} {k : Nat}
    {x : expr.Expr} (hlt : k < v.val.length) (hx : v.val[k] = x) :
    (absExprs v).drop k = absExpr x :: (absExprs v).drop (k + 1) := by
  have hlt' : k < (absExprs v).length := by rw [absExprs, List.length_map]; exact hlt
  rw [List.drop_eq_getElem_cons hlt']
  congr 1
  simp only [absExprs, List.getElem_map, hx]

/-- `ConLeche/Kernel/Checker.lean:239-250 divModCertGuard` —
`checker::hyps_resolve` refines the cited
`(hyps.map (Expr.substConst0 c annVal)).all (·.constsResolve env)`, as an index
recursion with the substitution fused in: from index `i` on it is the
`List.all` of the dropped tail. -/
theorem hyps_resolve_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lenv : ConLeche.Env} {c : name.Name} {ann_val : expr.Expr}
    {hyps : alloc.vec.Vec expr.Expr} {i : Std.Usize} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (henv : ∀ n : ConLeche.Name, lfe.find? n = lenv.find? n)
    (hc : NameWF c) (hav : ExprWF ann_val) (hh : ExprsWF hyps)
    (h : checker.hyps_resolve fe c ann_val hyps i = ok r) :
    r = (((absExprs hyps).drop i.val).map
          (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))).all
        (fun e => e.constsResolve lenv) := by
  suffices hs : ∀ (N : Nat) (i : Std.Usize) (r : Bool),
      hyps.val.length - i.val = N →
      checker.hyps_resolve fe c ann_val hyps i = ok r →
      r = (((absExprs hyps).drop i.val).map
            (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))).all
          (fun e => e.constsResolve lenv) by
    exact hs _ i r rfl h
  clear h
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i r hN h
    rw [checker.hyps_resolve.eq_def] at h
    dsimp only at h
    split at h
    · have hlen : hyps.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val hyps; scalar_tac
      rw [drop_absExprs_nil hlen]
      simpa using (Result.ok_injective h).symm
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, e1, hsc, b, hb, h⟩ := h
      have hlt := vec_index_lt hidx
      have hx := vec_index_val hidx hlt
      have hxwf : ExprWF x := hh x (by rw [← hx]; exact List.getElem_mem hlt)
      obtain ⟨he1abs, he1wf⟩ := CoreK.subst_const0_refines hc hav hxwf e1 hsc
      have hbv := CoreK.consts_resolve_refines hp hfe henv he1wf b hb
      rw [drop_absExprs_cons hlt hx]
      simp only [List.map_cons, List.all_cons, ← he1abs, ← hbv]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h]; rfl
      | true =>
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        rw [ih (hyps.val.length - i2.val) (by omega) i2 r rfl h, hi2v]
        simp

/-- `con-leche: none` — `hyps.map (Expr.substConst0 c annVal)` of
`checkDivModCerts`; §3.4 forbids the closure, so the port names the map.
`checker::hyps_subst_from` is its index recursion, the accumulator passed by
value and returned. -/
theorem hyps_subst_from_refines {c : name.Name} {ann_val : expr.Expr}
    {hyps out r : alloc.vec.Vec expr.Expr} {i : Std.Usize} (hc : NameWF c)
    (hav : ExprWF ann_val) (hh : ExprsWF hyps) (hout : ExprsWF out)
    (h : checker.hyps_subst_from c ann_val hyps i out = ok r) :
    absExprs r = absExprs out ++
        ((absExprs hyps).drop i.val).map
          (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))
      ∧ ExprsWF r := by
  suffices hs : ∀ (N : Nat) (i : Std.Usize) (out r : alloc.vec.Vec expr.Expr),
      ExprsWF out → hyps.val.length - i.val = N →
      checker.hyps_subst_from c ann_val hyps i out = ok r →
      absExprs r = absExprs out ++
          ((absExprs hyps).drop i.val).map
            (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))
        ∧ ExprsWF r by
    exact hs _ i out r hout rfl h
  clear h hout
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i out r hout hN h
    rw [checker.hyps_subst_from.eq_def] at h
    dsimp only at h
    split at h
    · have hlen : hyps.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val hyps; scalar_tac
      rw [← Result.ok_injective h, drop_absExprs_nil hlen]
      exact ⟨by simp, hout⟩
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, e1, hsc, out1, hpush, i2, hi2, h⟩ := h
      have hlt := vec_index_lt hidx
      have hx := vec_index_val hidx hlt
      have hxwf : ExprWF x := hh x (by rw [← hx]; exact List.getElem_mem hlt)
      obtain ⟨he1abs, he1wf⟩ := CoreK.subst_const0_refines hc hav hxwf e1 hsc
      have hout1v : out1.val = out.val ++ [e1] := vec_push_val hpush
      have hout1 : ExprsWF out1 := by
        intro z hz
        rw [hout1v] at hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        · exact hout z hz
        · rw [hz]; exact he1wf
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ :=
        ih (hyps.val.length - i2.val) (by omega) i2 out1 r hout1 rfl h
      refine ⟨?_, hwf⟩
      rw [habs, hi2v, drop_absExprs_cons hlt hx, absExprs, hout1v]
      simp [absExprs, he1abs]

/-- `con-leche: none` — `checker::hyps_subst` is the cited `List.map`. -/
theorem hyps_subst_refines {c : name.Name} {ann_val : expr.Expr}
    {hyps r : alloc.vec.Vec expr.Expr} (hc : NameWF c) (hav : ExprWF ann_val)
    (hh : ExprsWF hyps) (h : checker.hyps_subst c ann_val hyps = ok r) :
    absExprs r = (absExprs hyps).map
        (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))
      ∧ ExprsWF r := by
  rw [checker.hyps_subst] at h
  have hnew : ExprsWF (alloc.vec.Vec.new expr.Expr) := by
    intro x hx; simp [alloc.vec.Vec.new] at hx
  obtain ⟨habs, hwf⟩ := hyps_subst_from_refines hc hav hh hnew h
  refine ⟨?_, hwf⟩
  rw [habs, show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero]
  simp [absExprs, alloc.vec.Vec.new]


/-! ## The applied proof and the syntactic guards -/

/-- `ConLeche/Kernel/Checker.lean:224-237 divModCertApplied` —
`checker::div_mod_cert_applied` refines it: the vendored proof applied to the
statement's free variables, each hypothesis `fvar` carrying the hypothesis
type as its annotation. -/
theorem div_mod_cert_applied_refines {proof_s : expr.Expr}
    {hyps : alloc.vec.Vec expr.Expr} {e : expr.Expr} (hp : ExprWF proof_s)
    (hh : ExprsWF hyps) (h : checker.div_mod_cert_applied proof_s hyps = ok e) :
    absExpr e = ConLeche.divModCertApplied (absExpr proof_s) (absExprs hyps)
      ∧ ExprWF e := by
  rw [checker.div_mod_cert_applied] at h
  obtain ⟨p, hdp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨base, hbase, h⟩ := bind_eq_ok_iff.mp h
  have hpv : p = proof_s := Expr.dup_eq hdp
  obtain ⟨hxabs, hxwf⟩ := cert_x_refines hx
  obtain ⟨hyabs, hywf⟩ := cert_y_refines hy
  have hpwf : ExprWF p := by rw [hpv]; exact hp
  have hbwf : ExprWF base := ExprWF.app (ExprWF.app hpwf hxwf he2) hywf hbase
  have hbabs : absExpr base
      = .app (.app (absExpr proof_s) (.fvar 0 (.const ConLeche.natName [])))
          (.fvar 1 (.const ConLeche.natName [])) := by
    rw [Expr.app_refines hbase, Expr.app_refines he2, hxabs, hyabs, hpv]
  have hlen := alloc.vec.Vec.len_val hyps
  dsimp only at h
  split at h
  · -- one hypothesis: the cited `[h1]` arm
    rename_i h1
    have hl1 : hyps.val.length = 1 := by scalar_tac
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl1
    simp only [bind_eq_ok_iff] at h
    obtain ⟨e4, h4, e5, h5, e6, h6, h⟩ := h
    have hlt : (0#usize : Std.Usize).val < hyps.val.length := by rw [hl1]; norm_num
    have h4v := vec_index_val h4 hlt
    simp only [ha] at h4v
    have hae : e4 = a := by simpa using h4v.symm
    have hawf : ExprWF a := hh a (by rw [ha]; simp)
    have h5v : e5 = e4 := Expr.dup_eq h5
    have h6wf : ExprWF e6 := ExprWF.fvar (by rw [h5v, hae]; exact hawf) h6
    have habs : absExprs hyps = [absExpr a] := by rw [absExprs, ha]; simp
    refine ⟨?_, ExprWF.app hbwf h6wf h⟩
    rw [habs]
    simp only [ConLeche.divModCertApplied]
    rw [Expr.app_refines h, hbabs, Expr.fvar_refines h6, h5v, hae]
    rfl
  · split at h
    · -- two hypotheses: the cited `[h1, h2]` arm
      rename_i h2
      have hl2 : hyps.val.length = 2 := by scalar_tac
      obtain ⟨a, b, ha⟩ := List.length_eq_two.mp hl2
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, e10, h10, h⟩ := h
      have hlt0 : (0#usize : Std.Usize).val < hyps.val.length := by rw [hl2]; norm_num
      have hlt1 : (1#usize : Std.Usize).val < hyps.val.length := by rw [hl2]; norm_num
      have h4v := vec_index_val h4 hlt0
      have h8v := vec_index_val h8 hlt1
      simp only [ha] at h4v h8v
      have hae : e4 = a := by simpa using h4v.symm
      have hbe : e8 = b := by simpa using h8v.symm
      have hawf : ExprWF a := hh a (by rw [ha]; simp)
      have hbwf2 : ExprWF b := hh b (by rw [ha]; simp)
      have h5v : e5 = e4 := Expr.dup_eq h5
      have h9v : e9 = e8 := Expr.dup_eq h9
      have h6wf : ExprWF e6 := ExprWF.fvar (by rw [h5v, hae]; exact hawf) h6
      have h10wf : ExprWF e10 := ExprWF.fvar (by rw [h9v, hbe]; exact hbwf2) h10
      have h7wf : ExprWF e7 := ExprWF.app hbwf h6wf h7
      have habs : absExprs hyps = [absExpr a, absExpr b] := by rw [absExprs, ha]; simp
      refine ⟨?_, ExprWF.app h7wf h10wf h⟩
      rw [habs]
      simp only [ConLeche.divModCertApplied]
      rw [Expr.app_refines h, Expr.app_refines h7, hbabs, Expr.fvar_refines h6,
        Expr.fvar_refines h10, h5v, h9v, hae, hbe]
      rfl
    · -- neither: the cited `_` arm, i.e. no hypothesis or more than two
      rename_i h1 h2
      have hne1 : hyps.val.length ≠ 1 := fun hc => h1 (by scalar_tac)
      have hne2 : hyps.val.length ≠ 2 := fun hc => h2 (by scalar_tac)
      rw [← Result.ok_injective h]
      refine ⟨?_, hbwf⟩
      rcases hv : hyps.val with _ | ⟨a, l⟩
      · rw [show absExprs hyps = [] by rw [absExprs, hv]; simp]
        simp only [ConLeche.divModCertApplied]
        exact hbabs
      · rcases l with _ | ⟨b, l2⟩
        · exact absurd (show hyps.val.length = 1 by rw [hv]; simp) hne1
        · rcases l2 with _ | ⟨c2, l3⟩
          · exact absurd (show hyps.val.length = 2 by rw [hv]; simp) hne2
          · rw [show absExprs hyps
                  = absExpr a :: absExpr b :: absExpr c2 :: l3.map absExpr by
              rw [absExprs, hv]; simp]
            simp only [ConLeche.divModCertApplied]
            exact hbabs

/-- `ConLeche/Kernel/Checker.lean:239-250 divModCertGuard`,
`ConLeche/Kernel/DeclCheck.lean:321-330 divModCertGuardF` —
`checker::div_mod_cert_guard` refines it exactly.  The port substitutes once
where the Lean recomputes `Expr.substConstAll c annVal proof` four times (a
`@[simp]`-transparent common subexpression); `henv` is
`Refine/CoreKSupport.lean`'s `consts_resolve` hypothesis, the `F`-twin's
clauses being the same. -/
theorem div_mod_cert_guard_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lenv : ConLeche.Env} {c : name.Name} {ann_val eq_e proof : expr.Expr}
    {hyps : alloc.vec.Vec expr.Expr} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (henv : ∀ n : ConLeche.Name, lfe.find? n = lenv.find? n)
    (hc : NameWF c) (hav : ExprWF ann_val) (hh : ExprsWF hyps)
    (heq : ExprWF eq_e) (hpf : ExprWF proof)
    (h : checker.div_mod_cert_guard fe c ann_val hyps eq_e proof = ok r) :
    r = ConLeche.divModCertGuard lenv (absName c) (absExpr ann_val)
      (absExprs hyps) (absExpr eq_e) (absExpr proof) := by
  rw [checker.div_mod_cert_guard] at h
  obtain ⟨p, hp0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpabs, hpwf⟩ := CoreK.subst_const_all_refines hc hav hpf p hp0
  rw [ConLeche.divModCertGuard, ← hpabs]
  have hbv := ExprOps.loose_bvars_bounded_refines hpwf hb
  rw [u64_zero_val] at hbv
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← hbv]; simp
  | true =>
    simp only [if_true, bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    have hb1v := ExprOps.has_fvar_refines hpwf hb1
    cases b1 with
    | true =>
      simp only [if_true, Result.ok.injEq] at h
      rw [← h, ← hbv, ← hb1v]; simp
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      have hb2v := ExprOps.all_level_params_defined_fast_refines namesWF_new hpwf hb2
      rw [absNames_new] at hb2v
      cases b2 with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← hbv, ← hb1v, ← hb2v]; simp
      | true =>
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨b3, hb3, h⟩ := h
        have hb3v := CoreK.consts_resolve_refines hp hfe henv hpwf b3 hb3
        cases b3 with
        | false =>
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          rw [← h, ← hbv, ← hb1v, ← hb2v, ← hb3v]; simp
        | true =>
          simp only [if_true, bind_eq_ok_iff] at h
          obtain ⟨b4, hb4, h⟩ := h
          have hb4v := hyps_resolve_refines hp hfe henv hc hav hh hb4
          rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hb4v
          cases b4 with
          | false =>
            simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
            rw [← h, ← hbv, ← hb1v, ← hb2v, ← hb3v, ← hb4v]; simp
          | true =>
            simp only [if_true, bind_eq_ok_iff] at h
            obtain ⟨e, he, h⟩ := h
            obtain ⟨heabs, hewf⟩ := CoreK.subst_const0_refines hc hav heq e he
            rw [← hbv, ← hb1v, ← hb2v, ← hb3v, ← hb4v,
              CoreK.consts_resolve_refines hp hfe henv hewf r h, heabs]
            simp
/-! ## The certificate check (`Checker.lean:252-275 checkDivModCerts`) -/

/-- `ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts`,
`ConLeche/Kernel/DeclCheck.lean:861-875 checkDivModCertsF` —
`checker::check_div_mod_certs_from` refines it from index `i` on: the cited
two-list recursion is one index recursion (task #24's point 5), so the
statement is about the two dropped tails.  The checks run in the
*pre-insertion* environment, with the op's self-references replaced by the
stored annotated value; nothing is installed. -/
theorem check_div_mod_certs_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {c : name.Name}
    {ann_val : expr.Expr}
    {stmts : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)}
    {proofs : alloc.vec.Vec expr.Expr} {i : Std.Usize} {r : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hav : ExprWF ann_val)
    (hst : StmtsWF stmts) (hpr : ExprsWF proofs)
    (h : checker.check_div_mod_certs_from mode st fe c ann_val stmts proofs i
      = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDivModCertsF (TypeChecker.lops mode lfe) lfe
            (absName c) (absExpr ann_val) ((absStmts stmts).drop i.val)
            ((absExprs proofs).drop i.val)).run lst = .ok (r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `sorry`: the index-vs-list induction (fuel = length - i) with the three
  -- entry-point lemmas of `Refine/TypeChecker.lean` at each step.
  sorry

/-- `ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts` —
`checker::check_div_mod_certs` is the recursion at index 0. -/
theorem check_div_mod_certs_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {c : name.Name}
    {ann_val : expr.Expr}
    {stmts : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)}
    {proofs : alloc.vec.Vec expr.Expr} {r : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hav : ExprWF ann_val)
    (hst : StmtsWF stmts) (hpr : ExprsWF proofs)
    (h : checker.check_div_mod_certs mode st fe c ann_val stmts proofs
      = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDivModCertsF (TypeChecker.lops mode lfe) lfe
            (absName c) (absExpr ann_val) (absStmts stmts)
            (absExprs proofs)).run lst = .ok (r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `sorry`: `check_div_mod_certs_from_refines` at `i = 0` (`List.drop_zero`).
  sorry

/-! ## The environment guards (`Checker.lean:277-306`) -/

/-- The type a stored constant carries is a well-formed term: the six
`ConstantVal` arms read `cv.ty`, the table's header the closed `Sort 1`.
(`Refine/Env.lean` proves the *value*; this is the `ExprWF` half its
`constant_info_type_refines` does not claim.) -/
private theorem constant_info_type_wf {c : env.ConstantInfo} {t : expr.Expr}
    (hc : ConstantInfoWF c) (h : env.constant_info_type c = ok t) : ExprWF t := by
  cases c with
  | AxiomInfo v =>
    simp only [env.constant_info_type] at h; rw [Expr.dup_eq h]; exact hc.2.2
  | DefnInfo v val hint =>
    simp only [env.constant_info_type] at h; rw [Expr.dup_eq h]; exact hc.1.2.2
  | ThmInfo v val =>
    simp only [env.constant_info_type] at h; rw [Expr.dup_eq h]; exact hc.1.2.2
  | IndInfo v caps =>
    simp only [env.constant_info_type] at h; rw [Expr.dup_eq h]; exact hc.1.2.2
  | CtorInfo v np nf =>
    simp only [env.constant_info_type] at h; rw [Expr.dup_eq h]; exact hc.2.2
  | RecInfo v mi rp rs =>
    simp only [env.constant_info_type] at h; rw [Expr.dup_eq h]; exact hc.1.2.2
  | ProjInfo tbl =>
    simp only [env.constant_info_type, bind_eq_ok_iff] at h
    obtain ⟨l, hl, l1, hl1, he⟩ := h
    exact ExprWF.sort (LevelWF.succ (LevelWF.zero hl) hl1) he

/-- `ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard`,
`ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF` — the cited
`match env2.find? boolTrueName with | some ci => ci.toConstantVal.type
== .const boolName [] | none => false`, which `checker::bool_ctor_typed` is
(the Lean spells it twice; task #14's borrow rule factors it out). -/
theorem bool_ctor_typed_refines {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} {r : Bool} (hfe : FindAgree fe2 lfe)
    (hwf : FindWF fe2) (hn : NameWF n)
    (h : checker.bool_ctor_typed fe2 n = ok r) :
    r = (match lfe.find? (absName n) with
      | some ci => ci.toConstantVal.type == ConLeche.Expr.const ConLeche.boolName []
      | none => false) := by
  rw [checker.bool_ctor_typed] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  cases o with
  | none => rw [hfe.find_none hn ho]; simpa using (Result.ok_injective h).symm
  | some ci =>
    rw [hfe.find_some hn ho]
    obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hn1abs, hn1wf⟩ := CoreK.bool_name_refines hn1
    have htwf : ExprWF t := constant_info_type_wf (hwf n ci hn ho) ht
    have he1wf : ExprWF e1 := ExprWF.mk_const hn1wf CoreK.levelsWF_new he1
    rw [Expr.beq_refines htwf he1wf h, ConRon.Refine.Env.constant_info_type_refines ht,
      Expr.mk_const_refines he1, hn1abs, CoreK.absLevels_new]
    rfl

/-- `ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard`,
`ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF` —
`checker::div_mod_env_guard` refines it: dependency guard, pinned
dependencies, the pinned `Eq` basis, and the `Bool` constructors stored at the
type `Bool` itself.  `DepsTyPinned` is the module note's deviation, named:
the port's second clause tests `core_k::defn_lp_empty` where the Lean tests
`natOpStoredOkF`. -/
theorem div_mod_env_guard_refines {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {r : Bool} (hfe : FindAgree fe2 lfe)
    (hwf : FindWF fe2) (hc : NameWF c)
    (hnls : CoreK.NatLitSupportedSpec fe2 lfe) (hlp : CoreK.LpEmptySpec fe2 lfe)
    (hnod : PinnedNames (core_k.nat_op_deps c) (ConLeche.natOpDeps (absName c)))
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hdmn : PinnedNames core_k.nat_div_mod_names ConLeche.natDivModNames)
    (hbt : PinnedName core_k.bool_true_name ConLeche.boolTrueName)
    (hbf : PinnedName core_k.bool_false_name ConLeche.boolFalseName)
    (heq : EqBasisPinnedSpec fe2 lfe) (hdep : DepsTyPinned lfe (absName c))
    (h : checker.div_mod_env_guard fe2 c = ok r) :
    r = ConLeche.divModEnvGuardF lfe (absName c) := by
  rw [checker.div_mod_env_guard] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := CoreK.nat_op_guard_refines hfe hc hnls hlp hnod hbeq hble hdmn hbt hbf hb
  rw [ConLeche.divModEnvGuardF, ← hbv]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]; simp
  | true =>
    simp only [if_true, bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨hvabs, hvwf⟩ := hnod v hv
    obtain ⟨b1, hb1, h⟩ := h
    have hb1v := CoreK.deps_all_stored_refines hfe hvwf hb1
    rw [hvabs, hdep] at hb1v
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      rw [← h, ← hb1v]; simp
    | true =>
      simp only [if_true, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      have hb2v := heq b2 hb2
      -- `basis_pins` decides the equality; the cited guard spells it `==`.
      rw [show decide (lfe.find? ConLeche.eqName = some ConLeche.eqA)
            = (lfe.find? ConLeche.eqName == some ConLeche.eqA) by
          by_cases hq : lfe.find? ConLeche.eqName = some ConLeche.eqA
          · simp [hq]
          · simp [hq]] at hb2v
      cases b2 with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← hb1v, ← hb2v]; simp
      | true =>
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨n, hn, h⟩ := h
        obtain ⟨hnabs, hnwf⟩ := hbt n hn
        obtain ⟨b3, hb3, h⟩ := h
        have hb3v := bool_ctor_typed_refines hfe hwf hnwf hb3
        rw [hnabs] at hb3v
        -- the two `Bool`-constructor clauses are `match`es on the lookup, and
        -- the port's spelling and the cited one compile to *different*
        -- matcher auxiliaries, so the lookup is destructed rather than
        -- rewritten under.
        cases b3 with
        | false =>
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          cases hft : lfe.find? ConLeche.boolTrueName with
          | none => rw [← h, ← hb1v, ← hb2v]; simp [hft]
          | some ci =>
            simp only [hft] at hb3v
            rw [← h, ← hb1v, ← hb2v]
            simp [hft, ← hb3v]
        | true =>
          simp only [if_true, bind_eq_ok_iff] at h
          obtain ⟨n1, hn1, h⟩ := h
          obtain ⟨hn1abs, hn1wf⟩ := hbf n1 hn1
          have hrv := bool_ctor_typed_refines hfe hwf hn1wf h
          rw [hn1abs] at hrv
          rw [← hb1v, ← hb2v]
          cases hft : lfe.find? ConLeche.boolTrueName with
          | none => simp only [hft] at hb3v; simp at hb3v
          | some ci =>
            simp only [hft] at hb3v
            cases hff : lfe.find? ConLeche.boolFalseName with
            | none => simp only [hff] at hrv; simp [hft, hff, hrv]
            | some ci2 =>
              simp only [hff] at hrv
              simp [hft, hff, ← hb3v, hrv]

/-- `ConLeche/Kernel/Checker.lean:292-297 divModPinGuard`,
`ConLeche/Kernel/DeclCheck.lean:332-336 divModPinGuardF` —
`checker::div_mod_pin_guard` refines it: the syntactic guards on one variant's
pin, checked once at install rather than proven about the blob. -/
theorem div_mod_pin_guard_refines {ps : nat_op_pins.NatOpPinSet} {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} {lenv : ConLeche.Env} {c : name.Name} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (henv : ∀ n : ConLeche.Name, lfe.find? n = lenv.find? n)
    (hps : NatOpPinSetWF ps) (hc : NameWF c)
    (h : checker.div_mod_pin_guard ps fe c = ok r) :
    r = ConLeche.divModPinGuard (absNatOpPinSet ps) lenv (absName c) := by
  rw [checker.div_mod_pin_guard] at h
  obtain ⟨pin, hpin, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpabs, hpwf⟩ := div_mod_decl_pin_refines hps hc hpin
  rw [ConLeche.divModPinGuard, ← hpabs]
  have hbv := ExprOps.loose_bvars_bounded_refines hpwf hb
  rw [u64_zero_val] at hbv
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← hbv]; simp
  | true =>
    simp only [if_true, bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    have hb1v := ExprOps.has_fvar_refines hpwf hb1
    cases b1 with
    | true =>
      simp only [if_true, Result.ok.injEq] at h
      rw [← h, ← hbv, ← hb1v]; simp
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      have hb2v := ExprOps.all_level_params_defined_fast_refines namesWF_new hpwf hb2
      rw [absNames_new] at hb2v
      cases b2 with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← hbv, ← hb1v, ← hb2v]; simp
      | true =>
        simp only [if_true] at h
        rw [← hbv, ← hb1v, ← hb2v,
          CoreK.consts_resolve_refines hp hfe henv hpwf r h]
        simp

/-- `ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard` —
`checker::div_mod_certs_guard_from` refines the cited
`((divModCertStmts c).zip (divModCertProofs ps c)).all` from index `i` on: a
`zip` stops at the shorter list, so the bound is the minimum. -/
theorem div_mod_certs_guard_from_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lenv : ConLeche.Env} {c : name.Name} {ann_val : expr.Expr}
    {stmts : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)}
    {proofs : alloc.vec.Vec expr.Expr} {i : Std.Usize} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (henv : ∀ n : ConLeche.Name, lfe.find? n = lenv.find? n)
    (hc : NameWF c) (hav : ExprWF ann_val) (hst : StmtsWF stmts)
    (hpr : ExprsWF proofs)
    (h : checker.div_mod_certs_guard_from stmts proofs fe c ann_val i = ok r) :
    r = (((absStmts stmts).drop i.val).zip ((absExprs proofs).drop i.val)).all
        (fun p => ConLeche.divModCertGuard lenv (absName c) (absExpr ann_val)
          p.1.1 p.1.2 p.2) := by
  suffices hs : ∀ (N : Nat) (i : Std.Usize) (r : Bool),
      stmts.val.length - i.val = N →
      checker.div_mod_certs_guard_from stmts proofs fe c ann_val i = ok r →
      r = (((absStmts stmts).drop i.val).zip ((absExprs proofs).drop i.val)).all
          (fun p => ConLeche.divModCertGuard lenv (absName c) (absExpr ann_val)
            p.1.1 p.1.2 p.2) by
    exact hs _ i r rfl h
  clear h
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i r hN h
    rw [checker.div_mod_certs_guard_from.eq_def] at h
    dsimp only at h
    split at h
    · have hl : stmts.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val stmts; scalar_tac
      rw [drop_absStmts_nil hl]
      simpa using (Result.ok_injective h).symm
    · split at h
      · have hl : proofs.val.length ≤ i.val := by
          have := alloc.vec.Vec.len_val proofs; scalar_tac
        rw [drop_absExprs_nil hl]
        simpa using (Result.ok_injective h).symm
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨p, hidx, h⟩ := h
        obtain ⟨v, eq_e⟩ := p
        -- the pattern-`let` Aeneas emits for the pair: only the *unifier* sees
        -- through it, so it goes by ascription (task #16's hard spot 1).
        have h2 : (do
            let e1 ← alloc.vec.Vec.index
              (core.slice.index.SliceIndexUsizeSlice expr.Expr) proofs i
            let b ← checker.div_mod_cert_guard fe c ann_val v eq_e e1
            if b then do
              let i3 ← i + 1#usize
              checker.div_mod_certs_guard_from stmts proofs fe c ann_val i3
            else ok false) = ok r := h
        clear h
        simp only [bind_eq_ok_iff] at h2
        obtain ⟨pf, hpidx, b, hb, h⟩ := h2
        have hlt := vec_index_lt hidx
        have hx := vec_index_val hidx hlt
        have hltp := vec_index_lt hpidx
        have hxp := vec_index_val hpidx hltp
        have hvwf : ExprsWF v ∧ ExprWF eq_e :=
          hst (v, eq_e) (by rw [← hx]; exact List.getElem_mem hlt)
        have hpwf : ExprWF pf := hpr pf (by rw [← hxp]; exact List.getElem_mem hltp)
        have hbv := div_mod_cert_guard_refines hp hfe henv hc hav hvwf.1 hvwf.2 hpwf hb
        rw [drop_absStmts_cons hlt hx, drop_absExprs_cons hltp hxp]
        simp only [List.zip_cons_cons, List.all_cons, absStmt, ← hbv]
        cases b with
        | false =>
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          rw [← h]; rfl
        | true =>
          simp only [if_true] at h
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          rw [ih (stmts.val.length - i2.val) (by omega) i2 r rfl h, hi2v]
          simp

/-- `ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard`,
`ConLeche/Kernel/DeclCheck.lean:338-342 divModCertsGuardF` —
`checker::div_mod_certs_guard` refines it: all of one variant's certificates'
syntactic guards at once, checked *before* the pin comparison so that a stream
stopping short of a variant's constants moves on to the next variant. -/
theorem div_mod_certs_guard_refines {ps : nat_op_pins.NatOpPinSet}
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {lenv : ConLeche.Env}
    {c : name.Name} {ann_val : expr.Expr} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (henv : ∀ n : ConLeche.Name, lfe.find? n = lenv.find? n)
    (hps : NatOpPinSetWF ps) (hc : NameWF c) (hav : ExprWF ann_val)
    (h : checker.div_mod_certs_guard ps fe c ann_val = ok r) :
    r = ConLeche.divModCertsGuard (absNatOpPinSet ps) lenv (absName c)
      (absExpr ann_val) := by
  rw [checker.div_mod_certs_guard] at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvabs, hvwf⟩ := div_mod_cert_stmts_refines hc hv
  obtain ⟨h1abs, h1wf⟩ := div_mod_cert_proofs_refines hps hc hv1
  rw [ConLeche.divModCertsGuard, ← hvabs, ← h1abs,
    div_mod_certs_guard_from_refines hp hfe henv hc hav hvwf h1wf h,
    show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero, List.drop_zero]

/-! ## One variant's attempt (`Checker.lean:308-328 checkDivModPinAt`) -/

/-- `ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt`,
`ConLeche/Kernel/DeclCheck.lean:877-885 checkDivModPinAtF` —
`checker::check_div_mod_pin_at` refines it: the stored value against the
variant's pin by definitional equality, and on a match the variant's
certificates.  `true` = matched; `false` = the pin is not definitionally equal,
or a certificate did not check; the third outcome is an error thrown from
inside, which `or_else_step` turns into "this variant does not match". -/
theorem check_div_mod_pin_at_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {c : name.Name}
    {value2 : expr.Expr} {ps : nat_op_pins.NatOpPinSet} {r : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hv : ExprWF value2)
    (hps : NatOpPinSetWF ps)
    (h : checker.check_div_mod_pin_at mode st fe c value2 ps = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDivModPinAtF (TypeChecker.lops mode lfe) lfe
            (absName c) (absExpr value2) (absNatOpPinSet ps)).run lst
          = .ok (r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `sorry`: `div_mod_decl_pin_refines`, then `annotate_core_refines` and
  -- `is_def_eq_core_refines` (`Refine/TypeChecker.lean`) and, on a match,
  -- `check_div_mod_certs_refines`.
  sorry

/-! ## The variant loop — the port's one error-recovery point

`ConLeche/Kernel/Checker.lean:338-360 checkDivModPinLoop`,
`ConLeche/Kernel/DeclCheck.lean:887-901 checkDivModPinLoopF`.  Three things
are stated here and none is weakened:

* the **index-vs-list** shape: the Rust recurses on `i` over the `Vec`
  `check_decls` was given (task #31's deviation — con-leche reads the global
  `natOpPinSets`), the Lean on the list, so the statement is about
  `(absPins variants).drop i.val`;
* **`tried`**: not ported (task #24's point 4), hence universally quantified —
  it only ever reaches a decline message, and nothing is claimed on a decline;
* **`OrElseErrorStateSound`**: the hypothesis, one per variant, that a *failed*
  attempt's memo writes leave the abstract state where it was.  con-leche's
  `orElse` hands the continuation the pre-attempt state and the port's
  `&mut CState` hands it the post-attempt one; `Refine/CheckerC.lean` names the
  gap and this is the lemma that consumes it. -/

/-- `checker::check_div_mod_pin_loop` refines `checkDivModPinLoopF` from index
`i` on: the first variant whose guards pass and whose attempt succeeds enables
the fast path; every other outcome moves on, and when none is left the stream
declines. -/
theorem check_div_mod_pin_loop_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {c : name.Name}
    {value2 : expr.Expr} {variants : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {i : Std.Usize}
    (hoe : ∀ ps : nat_op_pins.NatOpPinSet, CheckerC.OrElseErrorStateSound
      (fun s => checker.check_div_mod_pin_at mode s fe c value2 ps))
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hv : ExprWF value2)
    (hvar : PinsWF variants)
    (h : checker.check_div_mod_pin_loop mode st fe c value2 variants i
      = ok (.Ok (), st')) :
    ∀ lst lfe (tried : List String), StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDivModPinLoopF (TypeChecker.lops mode lfe) lfe
            (absName c) (absExpr value2) ((absPins variants).drop i.val)
            tried).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `sorry`: the index-vs-list induction (fuel = length - i) over
  -- `div_mod_pin_guard_refines`, `div_mod_certs_guard_refines`,
  -- `check_div_mod_pin_at_refines` and `Refine/CheckerC.lean`'s three
  -- `orElse_run_*` arms; `hoe` discharges the error arm's state.
  sorry

/-! ## The two install gates (`Checker.lean:362-417`)

Task #24's "the pre-insertion environment is a visibility bound": both take the
index in at the *extended* bound and hand it back there, where the Lean returns
`Unit`.  The Lean's two environments are `fe := lfe.restrictTo k_pre` (the
pre-insertion view every check runs in) and `fe2 := lfe` (the extended one the
guards read); `Refine/FEnv.lean`'s `restrict_to_refines`/`restrict_to_wf` are
the bridge, and the `ops` record is at the pre-insertion index because that is
the index the port hands `type_checker`. -/

/-- `ConLeche/Kernel/Checker.lean:362-380 checkDivModPin`,
`ConLeche/Kernel/DeclCheck.lean:903-912 checkDivModPinF` —
`checker::check_div_mod_pin` refines it: the dependency and pinned-`Eq` guards
at the extended environment, then the pin variants in `natOpPinSets` order at
the pre-insertion one.  No variant matching is a decline, never a silent
accept.

Two deviations are in the statement rather than glossed: the index comes in at
the extended bound and goes back out there (`fe'` is related to `lfe`, not to
the restricted view), and **`pins` is a parameter** (DESIGN.md §3.6, task #31),
so `hpins : absPins pins = ConLeche.natOpPinSets` says the list the driver
threads is the global the cited code reads. -/
theorem check_div_mod_pin_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {k_pre : Std.U64}
    {c : name.Name}
    (hoe : ∀ (fp : fenv.FEnv) (v : expr.Expr) (ps : nat_op_pins.NatOpPinSet),
      CheckerC.OrElseErrorStateSound
        (fun s => checker.check_div_mod_pin_at mode s fp c v ps))
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hvar : PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    (h : checker.check_div_mod_pin mode pins st fe k_pre c = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDivModPinF
            (TypeChecker.lops mode (lfe.restrictTo k_pre.val))
            (lfe.restrictTo k_pre.val) lfe (absName c)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  -- `sorry`: `div_mod_env_guard_refines`, `defn_probe_refines`, the two
  -- `restrict_to` lemmas around `check_div_mod_pin_loop_refines`.
  sorry

/-- `ConLeche/Kernel/Checker.lean:382-417 checkReducePin` —
`checker::check_reduce_identity` refines the cited identity certificate
`ops.isDefEq env 1 (.app valA x) x` at `x := reduceCertVar c`, which is what
the model consumes (`EnvModel.reduce_ops`): on success it answered `true`, and
a failure after the pin matched is an internal inconsistency because the pin
*is* the identity function. -/
theorem check_reduce_identity_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (htp : TrustPinsSpec)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {c : name.Name}
    {val_a : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hva : ExprWF val_a)
    (h : checker.check_reduce_identity mode st fe c val_a = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.Cached.opB (absMode mode) lfe 1
            (.app (absExpr val_a) (ConLeche.reduceCertVar (absName c)))
            (ConLeche.reduceCertVar (absName c))).run lst = .ok (true, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker.check_reduce_identity] at h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨applied, happ, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxabs, hxwf⟩ := htp.certVar c x hc hx
  have he0v : e0 = val_a := Expr.dup_eq he0
  have he1v : e1 = x := Expr.dup_eq he1
  have hawf : ExprWF applied :=
    ExprWF.app (by rw [he0v]; exact hva) (by rw [he1v]; exact hxwf) happ
  have haabs : absExpr applied
      = .app (absExpr val_a) (ConLeche.reduceCertVar (absName c)) := by
    rw [Expr.app_refines happ, he0v, he1v, hxabs]
  simp only [bind_eq_ok_iff] at h
  obtain ⟨q, hq, h⟩ := h
  obtain ⟨res, st1⟩ := q
  cases res with
  | Err er => exact absurd h (by simp)
  | Ok ok1 =>
    cases ok1 with
    | false => exact absurd h (by simp)
    | true =>
      simp at h
      obtain ⟨lst', hrun, hsr', hsw'⟩ :=
        (TypeChecker.is_def_eq_core_refines hfuel hk) st fe 1#u64 applied x true st1
          hsw hfw hawf hxwf hq lst lfe hsr hfr
      rw [h] at hsr' hsw'
      refine ⟨lst', ?_, hsr', hsw'⟩
      rw [haabs, hxabs] at hrun
      exact hrun

/-- `ConLeche/Kernel/Checker.lean:382-417 checkReducePin`,
`ConLeche/Kernel/DeclCheck.lean:914-933 checkReducePinF` —
`checker::check_reduce_pin_pre` refines `checkReducePinF`'s body at the
pre-insertion view: the element guard, the pin's own syntactic guards, the
definitional comparison of the witness against the build-time pin, and the
identity certificate.  The port tests `reduceStoredOkF` at the extended bound
in the caller, so the cited first conjunct arrives here as `hstored`. -/
theorem check_reduce_pin_pre_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (htp : TrustPinsSpec)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {lfe2 : ConLeche.FEnv}
    {c : name.Name} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hval : ExprWF value)
    (hstored : ConLeche.reduceStoredOkF lfe2 (absName c) = true)
    (h : checker.check_reduce_pin_pre mode st fe c value = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → TrustGuardsSpec fe lfe →
      ∃ lst', (ConLeche.checkReducePinF (TypeChecker.lops mode lfe) lfe lfe2
            (absName c) (absExpr value)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- `sorry`: the two guard hypotheses, `annotate_core_refines` twice,
  -- `is_def_eq_core_refines`, then `check_reduce_identity_refines`.
  sorry

/-- `ConLeche/Kernel/Checker.lean:382-417 checkReducePin`,
`ConLeche/Kernel/DeclCheck.lean:914-933 checkReducePinF` —
`checker::check_reduce_pin` refines it: the `Lean.reduceNat`/`Lean.reduceBool`
install gate.  As `check_div_mod_pin`, the index comes in at the extended bound
and goes back out there (task #24's visibility-bound note). -/
theorem check_reduce_pin_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (htp : TrustPinsSpec)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {k_pre : Std.U64}
    {c : name.Name} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hval : ExprWF value)
    (h : checker.check_reduce_pin mode st fe k_pre c value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      TrustGuardsSpec fe lfe →
      (∀ fp : fenv.FEnv, FEnvRel fp (lfe.restrictTo k_pre.val) →
        TrustGuardsSpec fp (lfe.restrictTo k_pre.val)) →
      ∃ lst', (ConLeche.checkReducePinF
            (TypeChecker.lops mode (lfe.restrictTo k_pre.val))
            (lfe.restrictTo k_pre.val) lfe (absName c) (absExpr value)).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  -- `sorry`: `TrustGuardsSpec.storedOk`, the two `restrict_to` lemmas around
  -- `check_reduce_pin_pre_refines`.
  sorry

end ConRon.Refine.CheckerPins
