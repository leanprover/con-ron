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

`sorry` count in this file: 16.
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
  -- `sorry`: the cited `match hyps with | [h1] | [h1, h2] | _` against the
  -- port's `len() == 1` / `== 2` test, plus three `app` chains.
  sorry

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
  -- `sorry`: `subst_const_all_refines` once, then the four `expr_ops` field
  -- guards and `consts_resolve_refines`; the `&&` chain against the port's
  -- `if` nest as in `nat_op_guard_refines`.
  sorry

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
  -- `sorry`: the `deps_all_stored_from` induction shape (fuel = length - i),
  -- with `subst_const0_refines` and `consts_resolve_refines` at each step.
  sorry

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
  -- `sorry`: the accumulator induction, `vec_push_val` at each step.
  sorry

/-- `con-leche: none` — `checker::hyps_subst` is the cited `List.map`. -/
theorem hyps_subst_refines {c : name.Name} {ann_val : expr.Expr}
    {hyps r : alloc.vec.Vec expr.Expr} (hc : NameWF c) (hav : ExprWF ann_val)
    (hh : ExprsWF hyps) (h : checker.hyps_subst c ann_val hyps = ok r) :
    absExprs r = (absExprs hyps).map
        (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))
      ∧ ExprsWF r := by
  -- `sorry`: `hyps_subst_from_refines` at `i = 0`, empty accumulator.
  sorry

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
  -- `sorry`: `find_refines`, `env::constant_info_type` (`Refine/Env.lean`) and
  -- `expr::beq`'s exactness (`Refine/Expr.lean`); the one missing step is the
  -- `ExprWF` of the stored type, which is `FindWF`'s record read through
  -- `ConstantInfoWF`.
  sorry

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
  -- `sorry`: `nat_op_guard_refines`, `deps_all_stored_refines` (through
  -- `DepsTyPinned`), `EqBasisPinnedSpec` and `bool_ctor_typed_refines` twice,
  -- the port's `if` nest against the Lean's `&&` chain.
  sorry

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
  -- `sorry`: `div_mod_decl_pin_refines` once (the Lean rebuilds the pin four
  -- times), then the three `expr_ops` guards and `consts_resolve_refines`.
  sorry

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
  -- `sorry`: the index-vs-list induction over the minimum of the two lengths,
  -- `div_mod_cert_guard_refines` at each step.
  sorry

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
  -- `sorry`: `div_mod_cert_stmts_refines`, `div_mod_cert_proofs_refines` and
  -- `div_mod_certs_guard_from_refines` at `i = 0`.
  sorry

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
  -- `sorry`: `TrustPinsSpec.certVar`, `Expr.app_refines`, then
  -- `is_def_eq_core_refines` (`Refine/TypeChecker.lean`).
  sorry

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
