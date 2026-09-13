import ConRon.Refine.TypeChecker
import ConRon.Refine.CheckerC
import ConRon.Refine.Pins
import ConRon.Refine.CoreKNatOps
import ConRon.Refine.CoreKPinned
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKLits
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsMeta
import ConLeche.Kernel.DeclCheck
import ConLeche.Verify.Cached.KnotCongr

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
lemmas and whose port-side decision are `Refine/CheckerC.lean`'s.  Task #65
rules the port's third arm: a thrown attempt is the pin check's **verdict**,
not a fallback, so only `Ok false` reaches the next variant — con-leche's
`false` arm, with the attempt's state on both sides.  The error arm is then
unreachable from an accept, and tasks #24/#58's two hypotheses
(`OrElseErrorStateSound`, `OrElseErrorDeclines`) are gone.  Nothing about the
loop is weakened; the price is the accept-direction deviation documented in
`Refine/CheckerC.lean`'s module note and DESIGN.md §3.

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

**`div_mod_env_guard`'s dependency clause was weaker than `divModEnvGuardF`'s
— fixed in the port (task #58).**  The Lean is
`(natOpDeps c).all (natOpStoredOkF fe2)` (`DeclCheck.lean:233-238`), whose
per-dependency test is "stored as a level-monomorphic definition **and** at
the pinned type (`natOpTyPinnedF`)".  Task #56 found the port calling
`core_k::deps_all_stored` (`core_k.rs:1645`) instead, whose per-dependency
test is `core_k::defn_lp_empty` — the level-monomorphic-definition half only —
and the direction was the dangerous one: the port's gate passed streams
con-leche's declines, which §1 does not permit.  It carried the missing
conjunct as a hypothesis `DepsTyPinned` rather than papering over it.  Task
#58 changed the two call sites (`div_mod_env_guard` and
`check_structural_nat_pin`) to `checker::deps_all_stored_ok`, the index
recursion over `core_k::nat_op_stored_ok` that is the cited `.all`, so the
hypothesis is gone and `div_mod_env_guard_refines` is the plain statement.

## What is proved and what is stated

Everything in `checker.rs:365-1232` is covered, and everything *pure* is
proved: the two eight-way variant dispatches (`div_mod_decl_pin`,
`div_mod_cert_proofs`), all twenty-two closed `cert_*` builders, the two
`Vec`-literal helpers, `div_mod_cert_applied`, the whole guard cascade
(`div_mod_cert_guard`, `hyps_resolve`, `hyps_subst(_from)`,
`div_mod_pin_guard`, `div_mod_certs_guard(_from)`, `bool_ctor_typed`,
`div_mod_env_guard`), and the one stateful leaf whose only core call is a
single `isDefEq` (`check_reduce_identity`).

Task #58 closed the eight that task #56 left open, as stated: the closed
statement table `div_mod_cert_stmts`, the two `check_div_mod_certs`
recursions, the per-variant attempt, **the loop**, and the three install
gates.  All but the first are stateful walks over the knot's entry points; the
first is long rather than hard.  Nothing was weakened; the two statements that
gained a hypothesis are named below.

## The `F`-twins of the guard cascade (task #58)

The *stateful* shapes are `DeclCheck.lean`'s `F`-twins — `checkDivModCertsF`,
`checkDivModPinLoopF` — and those read `Expr.constsResolveF fe` where
`Checker.lean`'s pure twins read `Expr.constsResolve env`.  For a general
`FEnv` there need be no `Env` whose `find?` agrees with it (the index is
visibility-bounded), so the `lenv`-shaped guard lemmas above do **not**
specialise to the `F`-twins: each of the five needs an index-side copy.  They
are `consts_resolve_f_step`, `hyps_resolve_f_step`, `div_mod_cert_guard_f_step`,
`div_mod_certs_guard_from_f_step`, `div_mod_certs_guard_f_step` and
`div_mod_pin_guard_f_step`, the same proofs with `core_k::consts_resolve`'s
*indexed* refinement in place of its `Env` one.  The first is a step copy of
`Refine/DeclCheck.lean`'s `consts_resolve_f_refines` (that file is being
rewritten in parallel and may not be imported); when the two files next meet
they should all move there.

## The one statement that gained a hypothesis (task #58)

* **`check_div_mod_pin_refines` takes `EqBasisPinnedSpec fe lfe`** (inside its
  `∀ lst lfe`, beside `StateRel`/`FEnvRel`, as `check_reduce_pin_refines`
  already takes `TrustGuardsSpec`).  It runs `div_mod_env_guard`, whose lemma
  has carried that sibling's statement as a hypothesis since task #56 (§4
  above); `Refine/BasisPins.lean` proves it but still through one `sorry`
  (`basis_decls_a_wf`), so importing it would put `sorryAx` in this file's
  axiom census.  Nothing about the conclusion is weakened.

## Round 2 (task #58): what `Refine/CheckerDecl.lean` consumes

Four things the declaration driver needs and task #56's split did not leave
here.

1. **`check_reduce_pin_refines`'s `TrustGuardsSpec` hypothesis gained
   `FEnvWF fp`.**  It reads `∀ fp, FEnvRel fp (lfe.restrictTo k_pre) →
   FEnvWF fp → TrustGuardsSpec fp …`; every route to `TrustGuardsSpec`
   (`Refine/TrustAxioms.lean`'s) goes through `FindWF`, i.e. `FEnvWF fp`, which
   the old shape did not offer, so the hypothesis was not dischargeable.  A
   hypothesis with an extra antecedent is a *weaker* hypothesis and the lemma
   is therefore *stronger*: nothing is weakened.
2. **The index congruences.**  `checkDeclC` hands both gates the
   *pre-insertion* index, where the statements here are about
   `lfe.restrictTo k_pre` — same `find?`, different `.env`.
   `ConLeche/Verify/Cached/KnotCongr.lean` stops at `sharedOpsC_congr`, so
   `constsResolveF_congr` … `checkDivModPinF_congr`/`checkReducePinF_congr` are
   proved here, and `check_div_mod_pin_refines_at_view` /
   `check_reduce_pin_refines_at_view` are the transported shapes to call.
3. **`checker.rs`'s pin dispatch** (`:1299-1400`), which nothing covered:
   `nat_eqs_subst`, `check_structural_nat_pin`, `check_defn_div_mod_pin` and
   `check_defn_pins`.  `check_structural_nat_pin` has no con-leche sibling —
   it is `checkDecl`'s inlined block — so its conclusion is that block's three
   facts.  Since task #58 it reads `checker::deps_all_stored_ok`, so
   `deps_all_stored_ok_refines` above is what its dependency clause needs.
4. `hpins` stays a caller obligation, threaded unchanged through
   `check_defn_div_mod_pin_refines` and `check_defn_pins_refines`; task #58's
   two `orElse` obligations travelled with it until task #65 removed them.

`sorry` count in this file: 0.
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

/-! ## The thrown-error tails, factored

Every `throw` in this family is the same three steps — a `&str`'s code points,
a `CheckError` constructor, and the pair — and every forward proof meets it in
a branch it must discharge as impossible.  One lemma does that. -/

/-- `Except.ok`'s `bind`, as a rewrite: what `StateT.run_bind` leaves behind
once a step's `run` is known. -/
private theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- A thrown-error tail never answers `.Ok`. -/
private theorem err_tail_ne_ok {α A B : Type} {x : Result A} {f : A → Result B}
    {g : B → Result core_types.CheckError} {y : α}
    {st st' : cached.state_c.CState}
    (h : (do let a ← x
             let b ← f a
             let ce ← g b
             ok ((core.result.Result.Err ce : core.result.Result α core_types.CheckError),
               st)) = ok (.Ok y, st')) : False := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨_, -, _, -, _, -, h⟩ := h
  simp at h

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

/-! ### The table's rows, pushed

`div_mod_cert_stmts` builds its answer by two or three `Vec::push`es onto the
empty `Vec` (§3.4 forbids the literal, task #18's point 10).  Two lemmas turn
that into the cited list. -/

/-- A two-row statement table. -/
private theorem stmts2 {a b : alloc.vec.Vec expr.Expr × expr.Expr}
    {o1 r : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)}
    (h1 : alloc.vec.Vec.push
      (alloc.vec.Vec.new (alloc.vec.Vec expr.Expr × expr.Expr)) a = ok o1)
    (h2 : alloc.vec.Vec.push o1 b = ok r)
    (ha : ExprsWF a.1 ∧ ExprWF a.2) (hb : ExprsWF b.1 ∧ ExprWF b.2) :
    absStmts r = [absStmt a, absStmt b] ∧ StmtsWF r := by
  have ho1 : o1.val = [a] := by rw [vec_push_val h1]; simp
  have hrv : r.val = [a, b] := by rw [vec_push_val h2, ho1]; simp
  refine ⟨by rw [absStmts, hrv]; simp, ?_⟩
  intro p hp
  rw [hrv] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  exacts [ha, hb]

/-- A three-row statement table (`Nat.div`/`Nat.mod`). -/
private theorem stmts3 {a b d : alloc.vec.Vec expr.Expr × expr.Expr}
    {o1 o2 r : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)}
    (h1 : alloc.vec.Vec.push
      (alloc.vec.Vec.new (alloc.vec.Vec expr.Expr × expr.Expr)) a = ok o1)
    (h2 : alloc.vec.Vec.push o1 b = ok o2)
    (h3 : alloc.vec.Vec.push o2 d = ok r)
    (ha : ExprsWF a.1 ∧ ExprWF a.2) (hb : ExprsWF b.1 ∧ ExprWF b.2)
    (hd : ExprsWF d.1 ∧ ExprWF d.2) :
    absStmts r = [absStmt a, absStmt b, absStmt d] ∧ StmtsWF r := by
  have ho1 : o1.val = [a] := by rw [vec_push_val h1]; simp
  have ho2 : o2.val = [a, b] := by rw [vec_push_val h2, ho1]; simp
  have hrv : r.val = [a, b, d] := by rw [vec_push_val h3, ho2]; simp
  refine ⟨by rw [absStmts, hrv]; simp, ?_⟩
  intro p hp
  rw [hrv] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  exacts [ha, hb, hd]

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
  rw [checker.div_mod_cert_stmts] at h
  simp only [ConLeche.divModCertStmts]
  obtain ⟨n0, hn0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_gcd_name_refines hn0) hb0 h with ⟨hq0, h⟩ | ⟨hq0, h⟩
  · rw [if_pos hq0]
    obtain ⟨t0, ht0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at0, wt0⟩ := cert_one_refines ht0
    obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at1, wt1⟩ := cert_x_refines ht1
    obtain ⟨t2, ht2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at2, wt2⟩ := cert_ble2_refines wt0 wt1 ht2
    obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at3, wt3⟩ := cert_b_true_refines ht3
    obtain ⟨t4, ht4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at4, wt4⟩ := cert_eq_b_refines wt2 wt3 ht4
    obtain ⟨t5, ht5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at5, wt5⟩ := cert_hyp1_refines wt4 ht5
    obtain ⟨t6, ht6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at6, wt6⟩ := cert_y_refines ht6
    obtain ⟨t7, ht7, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at7, wt7⟩ := cert_op2_refines hc wt1 wt6 ht7
    obtain ⟨t8, ht8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at8, wt8⟩ := cert_mod2_refines wt6 wt1 ht8
    obtain ⟨t9, ht9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at9, wt9⟩ := cert_op2_refines hc wt8 wt1 ht9
    obtain ⟨t10, ht10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at10, wt10⟩ := cert_eq_n_refines wt7 wt9 ht10
    obtain ⟨t11, ht11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t12, ht12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at12, wt12⟩ := cert_ble2_refines wt0 wt1 ht12
    obtain ⟨t13, ht13, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at13, wt13⟩ := cert_b_false_refines ht13
    obtain ⟨t14, ht14, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at14, wt14⟩ := cert_eq_b_refines wt12 wt13 ht14
    obtain ⟨t15, ht15, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at15, wt15⟩ := cert_hyp1_refines wt14 ht15
    obtain ⟨t16, ht16, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at16, wt16⟩ := cert_op2_refines hc wt1 wt6 ht16
    obtain ⟨t17, ht17, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at17, wt17⟩ := cert_eq_n_refines wt16 wt6 ht17
    obtain ⟨habs, hwf⟩ := stmts2 ht11 h ⟨wt5, wt10⟩ ⟨wt15, wt17⟩
    refine ⟨?_, hwf⟩
    rw [habs]
    simp only [absStmt, at0, at1, at2, at3, at4, at5, at6, at7, at8, at9,
      at10, at12, at13, at14, at15, at16, at17]
  rw [if_neg hq0]
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_shift_left_name_refines hn1) hb1 h with ⟨hq1, h⟩ | ⟨hq1, h⟩
  · rw [if_pos hq1]
    obtain ⟨t0, ht0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at0, wt0⟩ := cert_one_refines ht0
    obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at1, wt1⟩ := cert_y_refines ht1
    obtain ⟨t2, ht2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at2, wt2⟩ := cert_ble2_refines wt0 wt1 ht2
    obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at3, wt3⟩ := cert_b_true_refines ht3
    obtain ⟨t4, ht4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at4, wt4⟩ := cert_eq_b_refines wt2 wt3 ht4
    obtain ⟨t5, ht5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at5, wt5⟩ := cert_hyp1_refines wt4 ht5
    obtain ⟨t6, ht6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at6, wt6⟩ := cert_x_refines ht6
    obtain ⟨t7, ht7, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at7, wt7⟩ := cert_op2_refines hc wt6 wt1 ht7
    obtain ⟨t8, ht8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at8, wt8⟩ := cert_two_refines ht8
    obtain ⟨t9, ht9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at9, wt9⟩ := cert_mul2_refines wt8 wt6 ht9
    obtain ⟨t10, ht10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at10, wt10⟩ := cert_sub2_refines wt1 wt0 ht10
    obtain ⟨t11, ht11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at11, wt11⟩ := cert_op2_refines hc wt9 wt10 ht11
    obtain ⟨t12, ht12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at12, wt12⟩ := cert_eq_n_refines wt7 wt11 ht12
    obtain ⟨t13, ht13, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t14, ht14, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at14, wt14⟩ := cert_ble2_refines wt0 wt1 ht14
    obtain ⟨t15, ht15, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at15, wt15⟩ := cert_b_false_refines ht15
    obtain ⟨t16, ht16, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at16, wt16⟩ := cert_eq_b_refines wt14 wt15 ht16
    obtain ⟨t17, ht17, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at17, wt17⟩ := cert_hyp1_refines wt16 ht17
    obtain ⟨t18, ht18, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at18, wt18⟩ := cert_op2_refines hc wt6 wt1 ht18
    obtain ⟨t19, ht19, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at19, wt19⟩ := cert_eq_n_refines wt18 wt6 ht19
    obtain ⟨habs, hwf⟩ := stmts2 ht13 h ⟨wt5, wt12⟩ ⟨wt17, wt19⟩
    refine ⟨?_, hwf⟩
    rw [habs]
    simp only [absStmt, at0, at1, at2, at3, at4, at5, at6, at7, at8, at9,
      at10, at11, at12, at14, at15, at16, at17, at18, at19]
  rw [if_neg hq1]
  obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_shift_right_name_refines hn2) hb2 h with ⟨hq2, h⟩ | ⟨hq2, h⟩
  · rw [if_pos hq2]
    obtain ⟨t0, ht0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at0, wt0⟩ := cert_one_refines ht0
    obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at1, wt1⟩ := cert_y_refines ht1
    obtain ⟨t2, ht2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at2, wt2⟩ := cert_ble2_refines wt0 wt1 ht2
    obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at3, wt3⟩ := cert_b_true_refines ht3
    obtain ⟨t4, ht4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at4, wt4⟩ := cert_eq_b_refines wt2 wt3 ht4
    obtain ⟨t5, ht5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at5, wt5⟩ := cert_hyp1_refines wt4 ht5
    obtain ⟨t6, ht6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at6, wt6⟩ := cert_x_refines ht6
    obtain ⟨t7, ht7, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at7, wt7⟩ := cert_op2_refines hc wt6 wt1 ht7
    obtain ⟨t8, ht8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at8, wt8⟩ := cert_sub2_refines wt1 wt0 ht8
    obtain ⟨t9, ht9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at9, wt9⟩ := cert_op2_refines hc wt6 wt8 ht9
    obtain ⟨t10, ht10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at10, wt10⟩ := cert_two_refines ht10
    obtain ⟨t11, ht11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at11, wt11⟩ := cert_div2_refines wt9 wt10 ht11
    obtain ⟨t12, ht12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at12, wt12⟩ := cert_eq_n_refines wt7 wt11 ht12
    obtain ⟨t13, ht13, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t14, ht14, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at14, wt14⟩ := cert_ble2_refines wt0 wt1 ht14
    obtain ⟨t15, ht15, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at15, wt15⟩ := cert_b_false_refines ht15
    obtain ⟨t16, ht16, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at16, wt16⟩ := cert_eq_b_refines wt14 wt15 ht16
    obtain ⟨t17, ht17, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at17, wt17⟩ := cert_hyp1_refines wt16 ht17
    obtain ⟨t18, ht18, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at18, wt18⟩ := cert_op2_refines hc wt6 wt1 ht18
    obtain ⟨t19, ht19, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at19, wt19⟩ := cert_eq_n_refines wt18 wt6 ht19
    obtain ⟨habs, hwf⟩ := stmts2 ht13 h ⟨wt5, wt12⟩ ⟨wt17, wt19⟩
    refine ⟨?_, hwf⟩
    rw [habs]
    simp only [absStmt, at0, at1, at2, at3, at4, at5, at6, at7, at8, at9,
      at10, at11, at12, at14, at15, at16, at17, at18, at19]
  rw [if_neg hq2]
  obtain ⟨n3, hn3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_land_name_refines hn3) hb3 h with ⟨hq3, h⟩ | ⟨hq3, h⟩
  · rw [if_pos hq3]
    obtain ⟨t0, ht0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at0, wt0⟩ := cert_one_refines ht0
    obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at1, wt1⟩ := cert_x_refines ht1
    obtain ⟨t2, ht2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at2, wt2⟩ := cert_ble2_refines wt0 wt1 ht2
    obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at3, wt3⟩ := cert_b_true_refines ht3
    obtain ⟨t4, ht4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at4, wt4⟩ := cert_eq_b_refines wt2 wt3 ht4
    obtain ⟨t5, ht5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at5, wt5⟩ := cert_hyp1_refines wt4 ht5
    obtain ⟨t6, ht6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at6, wt6⟩ := cert_y_refines ht6
    obtain ⟨t7, ht7, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at7, wt7⟩ := cert_op2_refines hc wt1 wt6 ht7
    obtain ⟨t8, ht8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at8, wt8⟩ := cert_two_refines ht8
    obtain ⟨t9, ht9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at9, wt9⟩ := cert_halves_refines hc ht9
    obtain ⟨t10, ht10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at10, wt10⟩ := cert_mul2_refines wt8 wt9 ht10
    obtain ⟨t11, ht11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at11, wt11⟩ := cert_mod2_refines wt1 wt8 ht11
    obtain ⟨t12, ht12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at12, wt12⟩ := cert_mod2_refines wt6 wt8 ht12
    obtain ⟨t13, ht13, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at13, wt13⟩ := cert_mul2_refines wt11 wt12 ht13
    obtain ⟨t14, ht14, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at14, wt14⟩ := cert_add2_refines wt10 wt13 ht14
    obtain ⟨t15, ht15, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at15, wt15⟩ := cert_eq_n_refines wt7 wt14 ht15
    obtain ⟨t16, ht16, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t17, ht17, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at17, wt17⟩ := cert_ble2_refines wt0 wt1 ht17
    obtain ⟨t18, ht18, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at18, wt18⟩ := cert_b_false_refines ht18
    obtain ⟨t19, ht19, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at19, wt19⟩ := cert_eq_b_refines wt17 wt18 ht19
    obtain ⟨t20, ht20, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at20, wt20⟩ := cert_hyp1_refines wt19 ht20
    obtain ⟨t21, ht21, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at21, wt21⟩ := cert_op2_refines hc wt1 wt6 ht21
    obtain ⟨t22, ht22, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at22, wt22⟩ := cert_zero_refines ht22
    obtain ⟨t23, ht23, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at23, wt23⟩ := cert_eq_n_refines wt21 wt22 ht23
    obtain ⟨habs, hwf⟩ := stmts2 ht16 h ⟨wt5, wt15⟩ ⟨wt20, wt23⟩
    refine ⟨?_, hwf⟩
    rw [habs]
    simp only [absStmt, at0, at1, at2, at3, at4, at5, at6, at7, at8, at9,
      at10, at11, at12, at13, at14, at15, at17, at18, at19, at20, at21,
      at22, at23]
  rw [if_neg hq3]
  obtain ⟨n4, hn4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_lor_name_refines hn4) hb4 h with ⟨hq4, h⟩ | ⟨hq4, h⟩
  · rw [if_pos hq4]
    obtain ⟨t0, ht0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at0, wt0⟩ := cert_one_refines ht0
    obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at1, wt1⟩ := cert_x_refines ht1
    obtain ⟨t2, ht2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at2, wt2⟩ := cert_ble2_refines wt0 wt1 ht2
    obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at3, wt3⟩ := cert_b_true_refines ht3
    obtain ⟨t4, ht4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at4, wt4⟩ := cert_eq_b_refines wt2 wt3 ht4
    obtain ⟨t5, ht5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at5, wt5⟩ := cert_hyp1_refines wt4 ht5
    obtain ⟨t6, ht6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at6, wt6⟩ := cert_y_refines ht6
    obtain ⟨t7, ht7, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at7, wt7⟩ := cert_op2_refines hc wt1 wt6 ht7
    obtain ⟨t8, ht8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at8, wt8⟩ := cert_two_refines ht8
    obtain ⟨t9, ht9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at9, wt9⟩ := cert_halves_refines hc ht9
    obtain ⟨t10, ht10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at10, wt10⟩ := cert_mul2_refines wt8 wt9 ht10
    obtain ⟨t11, ht11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at11, wt11⟩ := cert_mod2_refines wt1 wt8 ht11
    obtain ⟨t12, ht12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at12, wt12⟩ := cert_mod2_refines wt6 wt8 ht12
    obtain ⟨t13, ht13, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at13, wt13⟩ := cert_add2_refines wt11 wt12 ht13
    obtain ⟨t14, ht14, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at14, wt14⟩ := cert_mod2_refines wt1 wt8 ht14
    obtain ⟨t15, ht15, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at15, wt15⟩ := cert_mod2_refines wt6 wt8 ht15
    obtain ⟨t16, ht16, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at16, wt16⟩ := cert_mul2_refines wt14 wt15 ht16
    obtain ⟨t17, ht17, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at17, wt17⟩ := cert_sub2_refines wt13 wt16 ht17
    obtain ⟨t18, ht18, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at18, wt18⟩ := cert_add2_refines wt10 wt17 ht18
    obtain ⟨t19, ht19, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at19, wt19⟩ := cert_eq_n_refines wt7 wt18 ht19
    obtain ⟨t20, ht20, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t21, ht21, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at21, wt21⟩ := cert_ble2_refines wt0 wt1 ht21
    obtain ⟨t22, ht22, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at22, wt22⟩ := cert_b_false_refines ht22
    obtain ⟨t23, ht23, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at23, wt23⟩ := cert_eq_b_refines wt21 wt22 ht23
    obtain ⟨t24, ht24, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at24, wt24⟩ := cert_hyp1_refines wt23 ht24
    obtain ⟨t25, ht25, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at25, wt25⟩ := cert_op2_refines hc wt1 wt6 ht25
    obtain ⟨t26, ht26, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at26, wt26⟩ := cert_eq_n_refines wt25 wt6 ht26
    obtain ⟨habs, hwf⟩ := stmts2 ht20 h ⟨wt5, wt19⟩ ⟨wt24, wt26⟩
    refine ⟨?_, hwf⟩
    rw [habs]
    simp only [absStmt, at0, at1, at2, at3, at4, at5, at6, at7, at8, at9,
      at10, at11, at12, at13, at14, at15, at16, at17, at18, at19, at21,
      at22, at23, at24, at25, at26]
  rw [if_neg hq4]
  obtain ⟨n5, hn5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
  rcases beq_branch hc (CoreK.nat_xor_name_refines hn5) hb5 h with ⟨hq5, h⟩ | ⟨hq5, h⟩
  · rw [if_pos hq5]
    obtain ⟨t0, ht0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at0, wt0⟩ := cert_one_refines ht0
    obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at1, wt1⟩ := cert_x_refines ht1
    obtain ⟨t2, ht2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at2, wt2⟩ := cert_ble2_refines wt0 wt1 ht2
    obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at3, wt3⟩ := cert_b_true_refines ht3
    obtain ⟨t4, ht4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at4, wt4⟩ := cert_eq_b_refines wt2 wt3 ht4
    obtain ⟨t5, ht5, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at5, wt5⟩ := cert_hyp1_refines wt4 ht5
    obtain ⟨t6, ht6, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at6, wt6⟩ := cert_y_refines ht6
    obtain ⟨t7, ht7, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at7, wt7⟩ := cert_op2_refines hc wt1 wt6 ht7
    obtain ⟨t8, ht8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at8, wt8⟩ := cert_two_refines ht8
    obtain ⟨t9, ht9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at9, wt9⟩ := cert_halves_refines hc ht9
    obtain ⟨t10, ht10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at10, wt10⟩ := cert_mul2_refines wt8 wt9 ht10
    obtain ⟨t11, ht11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at11, wt11⟩ := cert_mod2_refines wt1 wt8 ht11
    obtain ⟨t12, ht12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at12, wt12⟩ := cert_mod2_refines wt6 wt8 ht12
    obtain ⟨t13, ht13, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at13, wt13⟩ := cert_add2_refines wt11 wt12 ht13
    obtain ⟨t14, ht14, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at14, wt14⟩ := cert_mod2_refines wt13 wt8 ht14
    obtain ⟨t15, ht15, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at15, wt15⟩ := cert_add2_refines wt10 wt14 ht15
    obtain ⟨t16, ht16, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at16, wt16⟩ := cert_eq_n_refines wt7 wt15 ht16
    obtain ⟨t17, ht17, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t18, ht18, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at18, wt18⟩ := cert_ble2_refines wt0 wt1 ht18
    obtain ⟨t19, ht19, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at19, wt19⟩ := cert_b_false_refines ht19
    obtain ⟨t20, ht20, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at20, wt20⟩ := cert_eq_b_refines wt18 wt19 ht20
    obtain ⟨t21, ht21, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at21, wt21⟩ := cert_hyp1_refines wt20 ht21
    obtain ⟨t22, ht22, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at22, wt22⟩ := cert_op2_refines hc wt1 wt6 ht22
    obtain ⟨t23, ht23, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨at23, wt23⟩ := cert_eq_n_refines wt22 wt6 ht23
    obtain ⟨habs, hwf⟩ := stmts2 ht17 h ⟨wt5, wt16⟩ ⟨wt21, wt23⟩
    refine ⟨?_, hwf⟩
    rw [habs]
    simp only [absStmt, at0, at1, at2, at3, at4, at5, at6, at7, at8, at9,
      at10, at11, at12, at13, at14, at15, at16, at18, at19, at20, at21,
      at22, at23]
  rw [if_neg hq5]
  obtain ⟨t0, ht0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at0, wt0⟩ := cert_y_refines ht0
  obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at1, wt1⟩ := cert_x_refines ht1
  obtain ⟨t2, ht2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at2, wt2⟩ := cert_ble2_refines wt0 wt1 ht2
  obtain ⟨t3, ht3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at3, wt3⟩ := cert_b_true_refines ht3
  obtain ⟨t4, ht4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at4, wt4⟩ := cert_eq_b_refines wt2 wt3 ht4
  obtain ⟨t5, ht5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at5, wt5⟩ := cert_one_refines ht5
  obtain ⟨t6, ht6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at6, wt6⟩ := cert_ble2_refines wt5 wt0 ht6
  obtain ⟨t7, ht7, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at7, wt7⟩ := cert_eq_b_refines wt6 wt3 ht7
  obtain ⟨t8, ht8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at8, wt8⟩ := cert_hyp2_refines wt4 wt7 ht8
  obtain ⟨t9, ht9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at9, wt9⟩ := cert_op2_refines hc wt1 wt0 ht9
  obtain ⟨t10, ht10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at10, wt10⟩ := cert_rec_rhs_refines hc ht10
  obtain ⟨t11, ht11, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at11, wt11⟩ := cert_eq_n_refines wt9 wt10 ht11
  obtain ⟨t12, ht12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t13, ht13, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at13, wt13⟩ := cert_ble2_refines wt0 wt1 ht13
  obtain ⟨t14, ht14, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at14, wt14⟩ := cert_b_false_refines ht14
  obtain ⟨t15, ht15, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at15, wt15⟩ := cert_eq_b_refines wt13 wt14 ht15
  obtain ⟨t16, ht16, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at16, wt16⟩ := cert_hyp1_refines wt15 ht16
  obtain ⟨t17, ht17, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at17, wt17⟩ := cert_op2_refines hc wt1 wt0 ht17
  obtain ⟨t18, ht18, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at18, wt18⟩ := cert_base_rhs_refines hc ht18
  obtain ⟨t19, ht19, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at19, wt19⟩ := cert_eq_n_refines wt17 wt18 ht19
  obtain ⟨t20, ht20, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t21, ht21, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at21, wt21⟩ := cert_ble2_refines wt5 wt0 ht21
  obtain ⟨t22, ht22, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at22, wt22⟩ := cert_eq_b_refines wt21 wt14 ht22
  obtain ⟨t23, ht23, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at23, wt23⟩ := cert_hyp1_refines wt22 ht23
  obtain ⟨t24, ht24, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at24, wt24⟩ := cert_op2_refines hc wt1 wt0 ht24
  obtain ⟨t25, ht25, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨at25, wt25⟩ := cert_eq_n_refines wt24 wt18 ht25
  obtain ⟨habs, hwf⟩ := stmts3 ht12 ht20 h ⟨wt8, wt11⟩ ⟨wt16, wt19⟩ ⟨wt23, wt25⟩
  refine ⟨?_, hwf⟩
  rw [habs]
  simp only [absStmt, at0, at1, at2, at3, at4, at5, at6, at7, at8, at9,
    at10, at11, at13, at14, at15, at16, at17, at18, at19, at21, at22,
    at23, at24, at25]

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

/-- In range, the abstracted pin tail peels off the indexed variant. -/
private theorem drop_absPins_cons {v : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {k : Nat} {x : nat_op_pins.NatOpPinSet} (hlt : k < v.val.length)
    (hx : v.val[k] = x) :
    (absPins v).drop k = absNatOpPinSet x :: (absPins v).drop (k + 1) := by
  have hlt' : k < (absPins v).length := by rw [absPins, List.length_map]; exact hlt
  rw [List.drop_eq_getElem_cons hlt']
  congr 1
  simp only [absPins, List.getElem_map, hx]

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
/-! ## The same guards at the index (`DeclCheck.lean`'s `F`-twins)

`checkDivModCertsF` and `checkDivModPinLoopF` — the shapes the *executed*
checker runs, and the ones the statements below are about — read
`Expr.constsResolveF fe` where `Checker.lean`'s pure twins read
`Expr.constsResolve env`; the two Lean definitions have the same clauses with
`env.find?` replaced by `fe.find?`.  The port has **one** spelling,
`core_k::consts_resolve`, so each guard above has an index-side twin with the
same proof and no `henv` bridge — there is no `Env` in sight.

`Refine/DeclCheck.lean` proves `consts_resolve_f_refines`; that file is being
rewritten in parallel and this one may not import it, so it is re-proved here
as a **step**, exactly as `one_level_step` above is.  When the two files next
meet, these five are its clients and should move there. -/

/-- `ConLeche/Kernel/DeclCheck.lean:37-58 Expr.constsResolveF` —
**`core_k::consts_resolve` refines the indexed walk**, with no `Env` in sight.
A step copy of `Refine/DeclCheck.lean`'s `consts_resolve_f_refines`. -/
theorem consts_resolve_f_step {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ c, core_k.consts_resolve fe e = ok c →
      c = ConLeche.Expr.constsResolveF lfe (absExpr e) := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolveF]
  | @sort u e hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolveF]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨o, ho, h⟩ := h
    rw [← h, CoreK.find_isSome hfe hn ho]
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [ih c h]; simp [ConLeche.Expr.constsResolveF]
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    cases l with
    | NatVal k =>
      rw [CoreK.nat_trio_stored_refines hp hfe h]
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
    | StrVal sv =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, h⟩ := h
      have g1 := CoreK.nat_trio_stored_refines hp hfe hb
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← g1]; simp
      | true =>
        simp only [if_true] at h
        rw [CoreK.str_support_stored_refines hp hfe h, ← g1]; simp
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (ihf b1 hb1) h (fun c' h' => iha c' h')
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @let_e ty v bo e hty hv hbo h1 iht ihv ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF,
      Bool.and_assoc]
    refine CoreK.and_step (iht b1 hb1) h ?_
    intro c' h'
    obtain ⟨b2, hb2, h'⟩ := bind_eq_ok_iff.mp h'
    exact CoreK.and_step (ihv b2 hb2) h' (fun c'' h'' => ihb c'' h'')
  | @proj sn i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (by rw [CoreK.find_isSome hfe hs ho]) h (fun c' h' => ih c' h')

/-- `ConLeche/Kernel/DeclCheck.lean:321-330 divModCertGuardF` —
`checker::hyps_resolve` at the index: the cited
`(hyps.map (Expr.substConst0 c annVal)).all (·.constsResolveF fe)` from index
`i` on.  `hyps_resolve_refines` at `Expr.constsResolveF`. -/
theorem hyps_resolve_f_step {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {ann_val : expr.Expr}
    {hyps : alloc.vec.Vec expr.Expr} {i : Std.Usize} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (hc : NameWF c) (hav : ExprWF ann_val) (hh : ExprsWF hyps)
    (h : checker.hyps_resolve fe c ann_val hyps i = ok r) :
    r = (((absExprs hyps).drop i.val).map
          (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))).all
        (fun e => e.constsResolveF lfe) := by
  suffices hs : ∀ (N : Nat) (i : Std.Usize) (r : Bool),
      hyps.val.length - i.val = N →
      checker.hyps_resolve fe c ann_val hyps i = ok r →
      r = (((absExprs hyps).drop i.val).map
            (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))).all
          (fun e => e.constsResolveF lfe) by
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
      have hbv := consts_resolve_f_step hp hfe he1wf b hb
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

/-- `ConLeche/Kernel/DeclCheck.lean:321-330 divModCertGuardF` —
`checker::div_mod_cert_guard` refines the `F`-twin exactly.
`div_mod_cert_guard_refines` at `Expr.constsResolveF`. -/
theorem div_mod_cert_guard_f_step {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {ann_val eq_e proof : expr.Expr}
    {hyps : alloc.vec.Vec expr.Expr} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (hc : NameWF c) (hav : ExprWF ann_val) (hh : ExprsWF hyps)
    (heq : ExprWF eq_e) (hpf : ExprWF proof)
    (h : checker.div_mod_cert_guard fe c ann_val hyps eq_e proof = ok r) :
    r = ConLeche.divModCertGuardF lfe (absName c) (absExpr ann_val)
      (absExprs hyps) (absExpr eq_e) (absExpr proof) := by
  rw [checker.div_mod_cert_guard] at h
  obtain ⟨p, hp0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpabs, hpwf⟩ := CoreK.subst_const_all_refines hc hav hpf p hp0
  rw [ConLeche.divModCertGuardF, ← hpabs]
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
        have hb3v := consts_resolve_f_step hp hfe hpwf b3 hb3
        cases b3 with
        | false =>
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          rw [← h, ← hbv, ← hb1v, ← hb2v, ← hb3v]; simp
        | true =>
          simp only [if_true, bind_eq_ok_iff] at h
          obtain ⟨b4, hb4, h⟩ := h
          have hb4v := hyps_resolve_f_step hp hfe hc hav hh hb4
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
              consts_resolve_f_step hp hfe hewf r h, heabs]
            simp

/-! ## The certificate check (`Checker.lean:252-275 checkDivModCerts`) -/

/-- The tail fold with an explicit bound to recurse on (the port's index
against the cited two-list recursion). -/
private theorem check_div_mod_certs_from_val {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {fe : fenv.FEnv} {c : name.Name} {ann_val : expr.Expr}
    {stmts : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)}
    {proofs : alloc.vec.Vec expr.Expr}
    (hfw : FEnvWF fe) (hc : NameWF c) (hav : ExprWF ann_val)
    (hst : StmtsWF stmts) (hpr : ExprsWF proofs) (n : Nat) :
    ∀ (st st' : cached.state_c.CState) (i : Std.Usize) (r : Bool),
      stmts.val.length - i.val ≤ n → StateWF st →
      checker.check_div_mod_certs_from mode st fe c ann_val stmts proofs i
        = ok (.Ok r, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkDivModCertsF (TypeChecker.lops mode lfe) lfe
              (absName c) (absExpr ann_val) ((absStmts stmts).drop i.val)
              ((absExprs proofs).drop i.val)).run lst = .ok (r, lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  have hlenS := alloc.vec.Vec.len_val stmts
  have hlenP := alloc.vec.Vec.len_val proofs
  -- the statement list is exhausted: `[]` against `[]` or against a cons
  have exhausted : ∀ (st st' : cached.state_c.CState) (i : Std.Usize) (r : Bool),
      stmts.val.length ≤ i.val → StateWF st →
      checker.check_div_mod_certs_from mode st fe c ann_val stmts proofs i
        = ok (.Ok r, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkDivModCertsF (TypeChecker.lops mode lfe) lfe
              (absName c) (absExpr ann_val) ((absStmts stmts).drop i.val)
              ((absExprs proofs).drop i.val)).run lst = .ok (r, lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
    intro st st' i r hle hsw h lst lfe hsr hfr
    rw [checker.check_div_mod_certs_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len stmts by scalar_tac)] at h
    have hS : (absStmts stmts).drop i.val = [] := drop_absStmts_nil hle
    by_cases hp2 : proofs.val.length ≤ i.val
    · rw [if_pos (show i >= alloc.vec.Vec.len proofs by scalar_tac)] at h
      have hbs : r = true ∧ st = st' := by simpa using h
      obtain ⟨rfl, rfl⟩ := hbs
      exact ⟨lst, by rw [hS, drop_absExprs_nil hp2]; rfl, hsr, hsw⟩
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len proofs) by scalar_tac),
        if_pos (show i >= alloc.vec.Vec.len stmts by scalar_tac)] at h
      have hbs : r = false ∧ st = st' := by simpa using h
      obtain ⟨rfl, rfl⟩ := hbs
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [hS, drop_absExprs_cons (show i.val < proofs.val.length by omega) rfl]
      rfl
  induction n with
  | zero =>
    intro st st' i r hle hsw h lst lfe hsr hfr
    exact exhausted st st' i r (by omega) hsw h lst lfe hsr hfr
  | succ n ih =>
    intro st st' i r hle hsw h lst lfe hsr hfr
    by_cases hge : stmts.val.length ≤ i.val
    · exact exhausted st st' i r hge hsw h lst lfe hsr hfr
    · have hlt : i.val < stmts.val.length := by omega
      rw [checker.check_div_mod_certs_from] at h
      rw [if_neg (show ¬ (i >= alloc.vec.Vec.len stmts) by scalar_tac)] at h
      rw [if_neg (show ¬ (i >= alloc.vec.Vec.len stmts) by scalar_tac)] at h
      by_cases hpge : proofs.val.length ≤ i.val
      · rw [if_pos (show i >= alloc.vec.Vec.len proofs by scalar_tac)] at h
        have hbs : r = false ∧ st = st' := by simpa using h
        obtain ⟨rfl, rfl⟩ := hbs
        refine ⟨lst, ?_, hsr, hsw⟩
        rw [drop_absStmts_cons hlt rfl, drop_absExprs_nil hpge]
        rfl
      · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len proofs) by scalar_tac)] at h
        have hltp : i.val < proofs.val.length := by omega
        simp only [bind_eq_ok_iff] at h
        obtain ⟨pr, hidx, h⟩ := h
        obtain ⟨v, eq_e⟩ := pr
        simp at h
        obtain ⟨pf, hpidx, harm⟩ := h
        have hpidx' : alloc.vec.Vec.index
            (core.slice.index.SliceIndexUsizeSlice expr.Expr) proofs i = ok pf := hpidx
        have hfa : FindAgree fe lfe := FindAgree.of_rel hfr hfw
        have hxs := vec_index_val hidx hlt
        have hxp := vec_index_val hpidx' hltp
        have hvwf : ExprsWF v ∧ ExprWF eq_e :=
          hst (v, eq_e) (by rw [← hxs]; exact List.getElem_mem hlt)
        have hpfwf : ExprWF pf := hpr pf (by rw [← hxp]; exact List.getElem_mem hltp)
        have hdS : (absStmts stmts).drop i.val
            = (absExprs v, absExpr eq_e) :: (absStmts stmts).drop (i.val + 1) :=
          drop_absStmts_cons hlt hxs
        have hdP : (absExprs proofs).drop i.val
            = absExpr pf :: (absExprs proofs).drop (i.val + 1) :=
          drop_absExprs_cons hltp hxp
        rcases harm with ⟨hg, rfl, rfl⟩ | ⟨hg, e2, he2, v1, hv1, applied, happ, a, b, hann, harm⟩
        · have hgv := div_mod_cert_guard_f_step CoreK.pinnedBasisNames hfa hc hav
            hvwf.1 hvwf.2 hpfwf hg
          refine ⟨lst, ?_, hsr, hsw⟩
          rw [hdS, hdP]
          simp only [ConLeche.checkDivModCertsF, ← hgv, Bool.false_eq_true,
            if_false]
          rfl
        · have hgv := div_mod_cert_guard_f_step CoreK.pinnedBasisNames hfa hc hav
            hvwf.1 hvwf.2 hpfwf hg
          obtain ⟨he2abs, he2wf⟩ := CoreK.subst_const_all_refines hc hav hpfwf e2 he2
          obtain ⟨hv1abs, hv1wf⟩ := hyps_subst_refines hc hav hvwf.1 hv1
          obtain ⟨happabs, happwf⟩ := div_mod_cert_applied_refines he2wf hv1wf happ
          cases a with
          | Err er => simp at harm
          | Ok applied_a =>
            obtain ⟨lst1, hrunA, hsr1, hsw1, haawf⟩ :=
              ((TypeChecker.annotate_core_refines hfuel hk).ok) st fe 4#u64 applied
                applied_a b hsw hfw happwf hann lst lfe hsr hfr
            have hrunA' : (ConLeche.Cached.opE (absMode mode) lfe (·.annotate) 4
                (ConLeche.divModCertApplied
                  (ConLeche.Expr.substConstAll (absName c) (absExpr ann_val)
                    (absExpr pf))
                  ((absExprs v).map
                    (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val))))).run lst
                  = .ok (absExpr applied_a, lst1) := by
              rw [← he2abs, ← hv1abs, ← happabs]; exact hrunA
            simp at harm
            obtain ⟨a1, b1, hinf, harm⟩ := harm
            cases a1 with
            | Err er => simp at harm
            | Ok tp =>
              obtain ⟨lst2, hrunI, hsr2, hsw2, htpwf⟩ :=
                ((TypeChecker.infer_type_core_refines hfuel hk).ok) b fe 4#u64 applied_a
                  tp b1 hsw1 hfw haawf hinf lst1 lfe hsr1 hfr
              have hrunI' : (ConLeche.Cached.opE (absMode mode) lfe (·.infer) 4
                  (absExpr applied_a)).run lst1 = .ok (absExpr tp, lst2) := hrunI
              simp at harm
              obtain ⟨target, htgt, a2, b2, hdef, harm⟩ := harm
              obtain ⟨htabs, htwf⟩ :=
                CoreK.subst_const0_refines hc hav hvwf.2 target htgt
              cases a2 with
              | Err er => simp at harm
              | Ok ok1 =>
                obtain ⟨lst3, hrunD, hsr3, hsw3⟩ :=
                  ((TypeChecker.is_def_eq_core_refines hfuel hk).ok) b1 fe 4#u64 tp target
                    ok1 b2 hsw2 hfw htpwf htwf hdef lst2 lfe hsr2 hfr
                have hrunD' : (ConLeche.Cached.opB (absMode mode) lfe 4 (absExpr tp)
                    (ConLeche.Expr.substConst0 (absName c) (absExpr ann_val)
                      (absExpr eq_e))).run lst2 = .ok (ok1, lst3) := by
                  rw [← htabs]; exact hrunD
                cases ok1 with
                | false =>
                  simp at harm
                  obtain ⟨rfl, rfl⟩ := harm
                  refine ⟨lst3, ?_, hsr3, hsw3⟩
                  rw [hdS, hdP]
                  simp only [ConLeche.checkDivModCertsF, ← hgv, if_true,
                    StateT.run_bind, except_ok_bind,
                    TypeChecker.sharedOpsC_annotate, TypeChecker.sharedOpsC_inferType,
                    TypeChecker.sharedOpsC_isDefEq, hrunA', hrunI', hrunD']
                  rfl
                | true =>
                  simp at harm
                  obtain ⟨i4, hi4, harm⟩ := harm
                  have hi4v : i4.val = i.val + 1 := HashMap.uscalar_add_eq hi4
                  obtain ⟨lst4, hrun4, hsr4, hsw4⟩ :=
                    ih b2 st' i4 r (by omega) hsw3 harm lst3 lfe hsr3 hfr
                  rw [hi4v] at hrun4
                  refine ⟨lst4, ?_, hsr4, hsw4⟩
                  rw [hdS, hdP]
                  simp only [ConLeche.checkDivModCertsF, ← hgv, if_true,
                    StateT.run_bind, except_ok_bind,
                    TypeChecker.sharedOpsC_annotate, TypeChecker.sharedOpsC_inferType,
                    TypeChecker.sharedOpsC_isDefEq, hrunA', hrunI', hrunD']
                  exact hrun4

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
  intro lst lfe hsr hfr
  exact check_div_mod_certs_from_val hfuel hk hfw hc hav hst hpr
    stmts.val.length st st' i r (by omega) hsw h lst lfe hsr hfr

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
  intro lst lfe hsr hfr
  rw [checker.check_div_mod_certs] at h
  obtain ⟨lst', hrun, rest⟩ :=
    check_div_mod_certs_from_refines hfuel hk hsw hfw hc hav hst hpr h lst lfe hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

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

/-! ### `checker::deps_all_stored_ok` — the cited `.all` (task #58)

`divModEnvGuardF`'s second conjunct is `(natOpDeps c).all (natOpStoredOkF fe2)`
and `checkDecl`'s structural-`Nat` gate spells the same `.all`.  The port's
index recursion over `core_k::nat_op_stored_ok` is
`checker::deps_all_stored_ok` and it lives in `checker.rs` — *not*
`core_k::deps_all_stored`, which is `natOpGuard`'s own, weaker `.all`
(`Refine/CoreKNatOps.lean`'s `deps_all_stored_refines`).  The module note above
has the story; the two differ exactly by `natOpTyPinnedF`. -/

/-- The index recursion behind `checker::deps_all_stored_ok`: from index `i`
on it is the `List.all` of the dropped tail. -/
theorem deps_all_stored_ok_from {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (hdp : CoreK.DefnProbeSpec fe lfe)
    (hpred : PinnedName core_k.nat_pred_name ConLeche.natPredName)
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName)
    (hnatn : PinnedName basis_names.nat_name ConLeche.natName)
    (htcv : CoreK.ToConstantValSpec)
    {deps : alloc.vec.Vec name.Name} (hdeps : NamesWF deps) :
    ∀ k (i : Std.Usize), deps.val.length - i.val ≤ k → ∀ b : Bool,
      checker.deps_all_stored_ok fe deps i = ok b →
      b = ((deps.val.drop i.val).map absName).all (ConLeche.natOpStoredOkF lfe) := by
  intro k
  induction k with
  | zero =>
    intro i hk b h
    rw [checker.deps_all_stored_ok.eq_def] at h
    simp only [] at h
    rw [if_pos (by have := alloc.vec.Vec.len_val deps; scalar_tac)] at h
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simpa using h.symm
  | succ k ih =>
    intro i hk b h
    rw [checker.deps_all_stored_ok.eq_def] at h
    simp only [] at h
    split at h
    · rw [List.drop_eq_nil_of_le
        (by have := alloc.vec.Vec.len_val deps; scalar_tac)]
      simpa using h.symm
    · rename_i hlt
      have hb : i.val < deps.val.length := by
        have := alloc.vec.Vec.len_val deps; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hx, b1, hb1, h⟩ := h
      have hxv : deps.val[i.val] = x := by
        have hg := ExprOps.vec_index_getElem? hx
        rw [List.getElem?_eq_getElem hb] at hg
        exact Option.some_injective _ hg
      have hxwf : NameWF x := hdeps x (by rw [← hxv]; exact List.getElem_mem hb)
      have he1 := CoreK.nat_op_stored_ok_refines hfe hwf hxwf hdp hpred hbeq hble
        hbn hnatn htcv hb1
      rw [List.drop_eq_getElem_cons hb, hxv]
      simp only [List.map_cons, List.all_cons]
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← he1]; rfl
      | true =>
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨w, hw, h⟩ := h
        have hwv : w.val = i.val + 1 := HashMap.uscalar_add_eq hw
        rw [ih w (by scalar_tac) b h, hwv, ← he1]
        simp

/-- **`checker::deps_all_stored_ok` refines `(natOpDeps c).all
(natOpStoredOkF fe2)`** (`ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard`,
`ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF`). -/
theorem deps_all_stored_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {deps : alloc.vec.Vec name.Name} {b : Bool}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) (hdp : CoreK.DefnProbeSpec fe lfe)
    (hpred : PinnedName core_k.nat_pred_name ConLeche.natPredName)
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName)
    (hnatn : PinnedName basis_names.nat_name ConLeche.natName)
    (htcv : CoreK.ToConstantValSpec) (hdeps : NamesWF deps)
    (h : checker.deps_all_stored_ok fe deps 0#usize = ok b) :
    b = (absNames deps).all (ConLeche.natOpStoredOkF lfe) := by
  have hz : (0#usize : Std.Usize).val = 0 := rfl
  rw [deps_all_stored_ok_from hfe hwf hdp hpred hbeq hble hbn hnatn htcv hdeps
    deps.val.length 0#usize (by scalar_tac) b h, hz, List.drop_zero, absNames]

/-- `ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard`,
`ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF` —
`checker::div_mod_env_guard` refines it: dependency guard, pinned
dependencies, the pinned `Eq` basis, and the `Bool` constructors stored at the
type `Bool` itself.  Since task #58 the second clause is
`checker::deps_all_stored_ok`, the cited `(natOpDeps c).all (natOpStoredOkF
fe2)`, so the statement is unconditional — the module note has the story. -/
theorem div_mod_env_guard_refines {fe2 : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {r : Bool} (hfe : FindAgree fe2 lfe)
    (hwf : FindWF fe2) (hc : NameWF c)
    (hnls : CoreK.NatLitSupportedSpec fe2 lfe) (hlp : CoreK.LpEmptySpec fe2 lfe)
    (hnod : PinnedNames (core_k.nat_op_deps c) (ConLeche.natOpDeps (absName c)))
    (hdp : CoreK.DefnProbeSpec fe2 lfe)
    (hpred : PinnedName core_k.nat_pred_name ConLeche.natPredName)
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName)
    (hnatn : PinnedName basis_names.nat_name ConLeche.natName)
    (htcv : CoreK.ToConstantValSpec)
    (hdmn : PinnedNames core_k.nat_div_mod_names ConLeche.natDivModNames)
    (hbt : PinnedName core_k.bool_true_name ConLeche.boolTrueName)
    (hbf : PinnedName core_k.bool_false_name ConLeche.boolFalseName)
    (heq : EqBasisPinnedSpec fe2 lfe)
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
    have hb1v := deps_all_stored_ok_refines hfe hwf hdp hpred hbeq hble hbn
      hnatn htcv hvwf hb1
    rw [hvabs] at hb1v
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
          | none => rw [← h, ← hb1v, ← hb2v]; simp
          | some ci =>
            simp only [hft] at hb3v
            rw [← h, ← hb1v, ← hb2v]
            simp [← hb3v]
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
            | none => simp only [hff] at hrv; simp [hrv]
            | some ci2 =>
              simp only [hff] at hrv
              simp [← hb3v, hrv]

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

/-! ### …and the two variant guards at the index -/

/-- `ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard` at the index:
`div_mod_certs_guard_from_refines` at `Expr.constsResolveF`. -/
theorem div_mod_certs_guard_from_f_step {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {ann_val : expr.Expr}
    {stmts : alloc.vec.Vec (alloc.vec.Vec expr.Expr × expr.Expr)}
    {proofs : alloc.vec.Vec expr.Expr} {i : Std.Usize} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (hc : NameWF c) (hav : ExprWF ann_val) (hst : StmtsWF stmts)
    (hpr : ExprsWF proofs)
    (h : checker.div_mod_certs_guard_from stmts proofs fe c ann_val i = ok r) :
    r = (((absStmts stmts).drop i.val).zip ((absExprs proofs).drop i.val)).all
        (fun p => ConLeche.divModCertGuardF lfe (absName c) (absExpr ann_val)
          p.1.1 p.1.2 p.2) := by
  suffices hs : ∀ (N : Nat) (i : Std.Usize) (r : Bool),
      stmts.val.length - i.val = N →
      checker.div_mod_certs_guard_from stmts proofs fe c ann_val i = ok r →
      r = (((absStmts stmts).drop i.val).zip ((absExprs proofs).drop i.val)).all
          (fun p => ConLeche.divModCertGuardF lfe (absName c) (absExpr ann_val)
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
        have hbv := div_mod_cert_guard_f_step hp hfe hc hav hvwf.1 hvwf.2 hpwf hb
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

/-- `ConLeche/Kernel/DeclCheck.lean:338-342 divModCertsGuardF` —
`checker::div_mod_certs_guard` refines it.  `div_mod_certs_guard_refines` at
`Expr.constsResolveF`. -/
theorem div_mod_certs_guard_f_step {ps : nat_op_pins.NatOpPinSet}
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} 
    {c : name.Name} {ann_val : expr.Expr} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (hps : NatOpPinSetWF ps) (hc : NameWF c) (hav : ExprWF ann_val)
    (h : checker.div_mod_certs_guard ps fe c ann_val = ok r) :
    r = ConLeche.divModCertsGuardF (absNatOpPinSet ps) lfe (absName c)
      (absExpr ann_val) := by
  rw [checker.div_mod_certs_guard] at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvabs, hvwf⟩ := div_mod_cert_stmts_refines hc hv
  obtain ⟨h1abs, h1wf⟩ := div_mod_cert_proofs_refines hps hc hv1
  rw [ConLeche.divModCertsGuardF, ← hvabs, ← h1abs,
    div_mod_certs_guard_from_f_step hp hfe hc hav hvwf h1wf h,
    show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero, List.drop_zero]

/-- `ConLeche/Kernel/DeclCheck.lean:332-336 divModPinGuardF` —
`checker::div_mod_pin_guard` refines it.  `div_mod_pin_guard_refines` at
`Expr.constsResolveF`. -/
theorem div_mod_pin_guard_f_step {ps : nat_op_pins.NatOpPinSet} {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} {c : name.Name} {r : Bool}
    (hp : CoreK.PinnedBasisNames) (hfe : FindAgree fe lfe)
    (hps : NatOpPinSetWF ps) (hc : NameWF c)
    (h : checker.div_mod_pin_guard ps fe c = ok r) :
    r = ConLeche.divModPinGuardF (absNatOpPinSet ps) lfe (absName c) := by
  rw [checker.div_mod_pin_guard] at h
  obtain ⟨pin, hpin, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpabs, hpwf⟩ := div_mod_decl_pin_refines hps hc hpin
  rw [ConLeche.divModPinGuardF, ← hpabs]
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
          consts_resolve_f_step hp hfe hpwf r h]
        simp

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
  intro lst lfe hsr hfr
  rw [checker.check_div_mod_pin_at] at h
  obtain ⟨pin, hpin, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpabs, hpwf⟩ := div_mod_decl_pin_refines hps hc hpin
  simp at h
  obtain ⟨a, b, hann, h⟩ := h
  cases a with
  | Err er => simp at h
  | Ok pin_a =>
    obtain ⟨lst1, hrunA, hsr1, hsw1, hpawf⟩ :=
      ((TypeChecker.annotate_core_refines hfuel hk).ok) st fe 0#u64 pin pin_a b
        hsw hfw hpwf hann lst lfe hsr hfr
    have hrunA' : (ConLeche.Cached.opE (absMode mode) lfe (·.annotate) 0
        (ConLeche.divModDeclPin (absNatOpPinSet ps) (absName c))).run lst
          = .ok (absExpr pin_a, lst1) := by rw [← hpabs]; exact hrunA
    simp at h
    obtain ⟨a1, b1, hdef, h⟩ := h
    cases a1 with
    | Err er => simp at h
    | Ok ok_pin =>
      obtain ⟨lst2, hrunD, hsr2, hsw2⟩ :=
        ((TypeChecker.is_def_eq_core_refines hfuel hk).ok) b fe 0#u64 value2 pin_a
          ok_pin b1 hsw1 hfw hv hpawf hdef lst1 lfe hsr1 hfr
      have hrunD' : (ConLeche.Cached.opB (absMode mode) lfe 0 (absExpr value2)
          (absExpr pin_a)).run lst1 = .ok (ok_pin, lst2) := hrunD
      cases ok_pin with
      | false =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨lst2, ?_, hsr2, hsw2⟩
        simp only [ConLeche.checkDivModPinAtF, StateT.run_bind, except_ok_bind,
          TypeChecker.sharedOpsC_annotate, TypeChecker.sharedOpsC_isDefEq,
          hrunA', hrunD', Bool.false_eq_true, if_false]
        rfl
      | true =>
        simp at h
        obtain ⟨sv, hsv, pv, hpv, h⟩ := h
        obtain ⟨hsvabs, hsvwf⟩ := div_mod_cert_stmts_refines hc hsv
        obtain ⟨hpvabs, hpvwf⟩ := div_mod_cert_proofs_refines hps hc hpv
        obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
          check_div_mod_certs_refines hfuel hk hsw2 hfw hc hv hsvwf hpvwf h
            lst2 lfe hsr2 hfr
        rw [hsvabs, hpvabs] at hrun3
        refine ⟨lst3, ?_, hsr3, hsw3⟩
        simp only [ConLeche.checkDivModPinAtF, StateT.run_bind, except_ok_bind,
          TypeChecker.sharedOpsC_annotate, TypeChecker.sharedOpsC_isDefEq,
          hrunA', hrunD', if_true]
        exact hrun3

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
* **the error arm is unreachable** (task #65): the port's `orElse` makes a
  thrown attempt the pin check's verdict, so a port-side accept means every
  earlier attempt answered `Ok false` — con-leche's own `false` arm, with the
  attempt's state on both sides.  Tasks #24/#58's two hypotheses
  (`OrElseErrorStateSound`, `OrElseErrorDeclines`) are gone with it; the
  deviation they priced is documented in `Refine/CheckerC.lean`'s module note
  and DESIGN.md §3. -/

/-- The variant loop with an explicit bound to recurse on. -/
private theorem check_div_mod_pin_loop_val {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {fe : fenv.FEnv} {c : name.Name} {value2 : expr.Expr}
    {variants : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hfw : FEnvWF fe) (hc : NameWF c) (hv : ExprWF value2)
    (hvar : PinsWF variants) (n : Nat) :
    ∀ (st st' : cached.state_c.CState) (i : Std.Usize),
      variants.val.length - i.val ≤ n → StateWF st →
      checker.check_div_mod_pin_loop mode st fe c value2 variants i
        = ok (.Ok (), st') →
      ∀ lst lfe (tried : List String), StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkDivModPinLoopF (TypeChecker.lops mode lfe) lfe
              (absName c) (absExpr value2) ((absPins variants).drop i.val)
              tried).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  have hlenV := alloc.vec.Vec.len_val variants
  induction n with
  | zero =>
    intro st st' i hle hsw h lst lfe tried hsr hfr
    rw [checker.check_div_mod_pin_loop] at h
    rw [if_pos (show i >= alloc.vec.Vec.len variants by scalar_tac)] at h
    exact (err_tail_ne_ok h).elim
  | succ n ih =>
    intro st st' i hle hsw h lst lfe tried hsr hfr
    rw [checker.check_div_mod_pin_loop] at h
    by_cases hge : variants.val.length ≤ i.val
    · rw [if_pos (show i >= alloc.vec.Vec.len variants by scalar_tac)] at h
      exact (err_tail_ne_ok h).elim
    · have hlt : i.val < variants.val.length := by omega
      rw [if_neg (show ¬ (i >= alloc.vec.Vec.len variants) by scalar_tac)] at h
      obtain ⟨nops, hidx, h⟩ := bind_eq_ok_iff.mp h
      have hx := vec_index_val hidx hlt
      have hnwf : NatOpPinSetWF nops :=
        hvar nops (by rw [← hx]; exact List.getElem_mem hlt)
      have hfa : FindAgree fe lfe := FindAgree.of_rel hfr hfw
      have hdrop : (absPins variants).drop i.val
          = absNatOpPinSet nops :: (absPins variants).drop (i.val + 1) :=
        drop_absPins_cons hlt hx
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hbv := div_mod_pin_guard_f_step CoreK.pinnedBasisNames hfa hnwf hc hb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        rw [hdrop]
        simp only [ConLeche.checkDivModPinLoopF, ← hbv, Bool.false_eq_true,
          Bool.false_and, if_false, ← hi2v]
        exact ih st st' i2 (by omega) hsw h lst lfe _ hsr hfr
      | true =>
        simp only [if_true] at h
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1v := div_mod_certs_guard_f_step CoreK.pinnedBasisNames hfa hnwf hc hv hb1
        cases b1 with
        | false =>
          simp only [Bool.false_eq_true, if_false] at h
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          rw [hdrop]
          simp only [ConLeche.checkDivModPinLoopF, ← hbv, ← hb1v,
            Bool.and_false, Bool.false_eq_true, if_false, ← hi2v]
          exact ih st st' i2 (by omega) hsw h lst lfe _ hsr hfr
        | true =>
          simp only [if_true] at h
          obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨attempt, st1⟩ := q
          cases attempt with
          | Ok ok1 =>
            obtain ⟨lst1, hxrun, hsr1, hsw1⟩ :=
              check_div_mod_pin_at_refines hfuel hk hsw hfw hc hv hnwf hq
                lst lfe hsr hfr
            cases ok1 with
            | true =>
              simp at h
              subst h
              refine ⟨lst1, ?_, hsr1, hsw1⟩
              rw [hdrop]
              simp only [ConLeche.checkDivModPinLoopF, ← hbv, ← hb1v,
                Bool.and_self, if_true]
              exact CheckerC.orElse_run_matched hxrun
            | false =>
              simp at h
              obtain ⟨i2, hi2, h⟩ := h
              have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
              rw [hdrop]
              simp only [ConLeche.checkDivModPinLoopF, ← hbv, ← hb1v,
                Bool.and_self, if_true]
              rw [CheckerC.orElse_run_declined hxrun, ← hi2v]
              exact ih st1 st' i2 (by omega) hsw1 h lst1 lfe _ hsr1 hfr
          | Err e =>
            -- task #65: a thrown attempt is the pin check's verdict, so this
            -- branch is not an accept at all
            simp at h

/-- `checker::check_div_mod_pin_loop` refines `checkDivModPinLoopF` from index
`i` on: the first variant whose guards pass and whose attempt succeeds enables
the fast path; every other outcome moves on, and when none is left the stream
declines.

**Lost two hypotheses (task #65)**: tasks #24/#58's `hoe`
(`CheckerC.OrElseErrorStateSound`) and `hoeL` (`OrElseErrorDeclines`).  The
port's `orElse` no longer continues after a thrown attempt — it declines with
that error — so a port-side accept at variant `j` means every attempt before
it answered `Ok false`, which is con-leche's `false` arm with the attempt's
state on both sides, and the error arm is unreachable here.  The deviation
that buys this is `Refine/CheckerC.lean`'s module note and DESIGN.md §3. -/
theorem check_div_mod_pin_loop_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {c : name.Name}
    {value2 : expr.Expr} {variants : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {i : Std.Usize}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hv : ExprWF value2)
    (hvar : PinsWF variants)
    (h : checker.check_div_mod_pin_loop mode st fe c value2 variants i
      = ok (.Ok (), st')) :
    ∀ lst lfe (tried : List String), StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDivModPinLoopF (TypeChecker.lops mode lfe) lfe
            (absName c) (absExpr value2) ((absPins variants).drop i.val)
            tried).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe tried hsr hfr
  exact check_div_mod_pin_loop_val hfuel hk hfw hc hv hvar
    variants.val.length st st' i (by omega) hsw h lst lfe tried hsr hfr

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
threads is the global the cited code reads.

**Gained one hypothesis (task #58)**, a sibling's statement travelling rather
than a weakening of the conclusion: `EqBasisPinnedSpec fe lfe`, which
`div_mod_env_guard_refines` has taken since task #56 and which
`Refine/BasisPins.lean` proves only through its remaining `sorry`.  The
loop's two `orElse` obligations travelled here too until task #65 removed
them. -/
theorem check_div_mod_pin_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {k_pre : Std.U64}
    {c : name.Name}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hvar : PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    (h : checker.check_div_mod_pin mode pins st fe k_pre c = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → EqBasisPinnedSpec fe lfe →
      ∃ lst', (ConLeche.checkDivModPinF
            (TypeChecker.lops mode (lfe.restrictTo k_pre.val))
            (lfe.restrictTo k_pre.val) lfe (absName c)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lst lfe hsr hfr heqb
  rw [checker.check_div_mod_pin] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hfa : FindAgree fe lfe := FindAgree.of_rel hfr hfw
  have hfwf : FindWF fe := FindWF.of_wf hfw
  have hbv := div_mod_env_guard_refines hfa hfwf hc
    (CoreK.natLitSupportedSpec hfa hfwf) (CoreK.lpEmptySpec hfa)
    (fun _ hv => CoreK.nat_op_deps_refines hc hv) (CoreK.defnProbeSpec hfa hfwf)
    CoreK.pinned_nat_pred_name CoreK.pinned_nat_beq_name CoreK.pinned_nat_ble_name
    CoreK.pinned_bool_name CoreK.pinned_nat_name CoreK.toConstantValSpec
    CoreK.pinned_nat_div_mod_names CoreK.pinned_bool_true_name
    CoreK.pinned_bool_false_name heqb hb
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    exact (err_tail_ne_ok h).elim
  | true =>
    have hgv : ConLeche.divModEnvGuardF lfe (absName c) = true := hbv.symm
    simp only [if_true] at h
    obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hpabs, hpwf⟩ := CoreK.defn_probe_refines hfa hfwf hc hprobe
    cases o with
    | none => exact (err_tail_ne_ok h).elim
    | some t =>
      obtain ⟨cv, value2, hint⟩ := t
      obtain ⟨-, hvwf⟩ := hpwf cv value2 hint rfl
      -- the probe read back: the stored constant is a definition, and its
      -- value is the one the loop is run on.
      have hfind : lfe.find? (absName c)
          = some (.defnInfo (absConstantVal cv) (absExpr value2) (absHint hint)) := by
        simp only [Option.map_some] at hpabs
        cases hf : lfe.find? (absName c) with
        | none => rw [hf] at hpabs; simp [CoreK.defnOf] at hpabs
        | some ci =>
          rw [hf] at hpabs
          cases ci with
          | defnInfo cv1 v1 h1 =>
            simp only [CoreK.defnOf, Option.some.injEq, Prod.mk.injEq] at hpabs
            rw [hpabs.1, hpabs.2.1, hpabs.2.2]
          | _ => simp [CoreK.defnOf] at hpabs
      simp at h
      obtain ⟨fp, hfp, res, st1, hq, h⟩ := h
      have hfprel : FEnvRel fp (lfe.restrictTo k_pre.val) := restrict_to_refines hfr hfp
      have hfpwf : FEnvWF fp := restrict_to_wf hfw hfp
      cases res with
      | Err e => simp at h
      | Ok u =>
        obtain ⟨lst1, hrun, hsr1, hsw1⟩ :=
          check_div_mod_pin_loop_refines hfuel hk
            hsw hfpwf hc hvwf hvar (by cases u; exact hq) lst
            (lfe.restrictTo k_pre.val) [] hsr hfprel
        rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero,
          hpins] at hrun
        simp at h
        obtain ⟨hf, rfl⟩ := h
        rw [fenv.restrict_to, Result.ok.injEq] at hfp
        subst hfp
        rw [fenv.restrict_to, Result.ok.injEq] at hf
        subst hf
        refine ⟨lst1, ?_, hsr1, hsw1, hfr, hfw⟩
        simp only [ConLeche.checkDivModPinF, hgv, if_true, hfind]
        exact hrun

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
        ((TypeChecker.is_def_eq_core_refines hfuel hk).ok) st fe 1#u64 applied x true st1
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
  intro lst lfe hsr hfr htg
  rw [checker.check_reduce_pin_pre] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := htg.elemOk c b hc hb
  cases b with
  | false => simp at h
  | true =>
    have helem : ConLeche.reduceElemOkF lfe (absName c) = true := hbv.symm
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := htg.pinGuard c b1 hc hb1
    cases b1 with
    | false => simp at h
    | true =>
      have hguard : ConLeche.reducePinGuardF lfe (absName c) = true := hb1v.symm
      simp only [if_true] at h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨res, st1⟩ := q
      cases res with
      | Err e => simp at h
      | Ok val_a =>
        obtain ⟨lst1, hrun1, hsr1, hsw1, hvawf⟩ :=
          ((TypeChecker.annotate_core_refines hfuel hk).ok) st fe 0#u64 value val_a st1
            hsw hfw hval hq lst lfe hsr hfr
        have hrun1' : (ConLeche.Cached.opE (absMode mode) lfe (·.annotate) 0
            (absExpr value)).run lst = .ok (absExpr val_a, lst1) := hrun1
        simp at h
        obtain ⟨pin, hpin, res2, st2, hq2, h⟩ := h
        obtain ⟨hpinabs, hpinwf⟩ := htp.declPin c pin hc hpin
        cases res2 with
        | Err e => simp at h
        | Ok pin_a =>
          obtain ⟨lst2, hrun2, hsr2, hsw2, hpawf⟩ :=
            ((TypeChecker.annotate_core_refines hfuel hk).ok) st1 fe 0#u64 pin pin_a st2
              hsw1 hfw hpinwf hq2 lst1 lfe hsr1 hfr
          have hrun2' : (ConLeche.Cached.opE (absMode mode) lfe (·.annotate) 0
              (ConLeche.reduceDeclPin (absName c))).run lst1
                = .ok (absExpr pin_a, lst2) := by rw [← hpinabs]; exact hrun2
          simp at h
          obtain ⟨res3, st3, hq3, h⟩ := h
          cases res3 with
          | Err e => simp at h
          | Ok ok_pin =>
            obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
              ((TypeChecker.is_def_eq_core_refines hfuel hk).ok) st2 fe 0#u64 val_a pin_a
                ok_pin st3 hsw2 hfw hvawf hpawf hq3 lst2 lfe hsr2 hfr
            have hrun3' : (ConLeche.Cached.opB (absMode mode) lfe 0
                (absExpr val_a) (absExpr pin_a)).run lst2 = .ok (ok_pin, lst3) :=
              hrun3
            cases ok_pin with
            | false => simp at h
            | true =>
              simp at h
              obtain ⟨lst4, hrun4, hsr4, hsw4⟩ :=
                check_reduce_identity_refines hfuel hk htp hsw3 hfw hc hvawf h
                  lst3 lfe hsr3 hfr
              refine ⟨lst4, ?_, hsr4, hsw4⟩
              simp only [ConLeche.checkReducePinF, hstored, helem, Bool.and_self,
                if_true, hguard, StateT.run_bind, except_ok_bind,
                TypeChecker.sharedOpsC_annotate, TypeChecker.sharedOpsC_isDefEq,
                hrun1', hrun2', hrun3', hrun4]
              rfl

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
      (∀ fp : fenv.FEnv, FEnvRel fp (lfe.restrictTo k_pre.val) → FEnvWF fp →
        TrustGuardsSpec fp (lfe.restrictTo k_pre.val)) →
      ∃ lst', (ConLeche.checkReducePinF
            (TypeChecker.lops mode (lfe.restrictTo k_pre.val))
            (lfe.restrictTo k_pre.val) lfe (absName c) (absExpr value)).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lst lfe hsr hfr htg htgp
  rw [checker.check_reduce_pin] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := htg.storedOk c b hc hb
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    exact (err_tail_ne_ok h).elim
  | true =>
    have hstored : ConLeche.reduceStoredOkF lfe (absName c) = true := hbv.symm
    simp only [if_true] at h
    obtain ⟨fp, hfp, h⟩ := bind_eq_ok_iff.mp h
    have hfprel : FEnvRel fp (lfe.restrictTo k_pre.val) := restrict_to_refines hfr hfp
    have hfpwf : FEnvWF fp := restrict_to_wf hfw hfp
    obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨res, st1⟩ := q
    cases res with
    | Err e => simp at h
    | Ok u =>
    obtain ⟨lst', hrun, hsr', hsw'⟩ :=
      check_reduce_pin_pre_refines (lfe2 := lfe) hfuel hk htp hsw hfpwf hc hval
        hstored (by cases u; exact hq) lst (lfe.restrictTo k_pre.val) hsr hfprel
        (htgp fp hfprel hfpwf)
    simp at h
    obtain ⟨hf, rfl⟩ := h
    -- `restrict_to` is a field update, so the round trip is the record it
    -- started from: the pre-insertion view handed back at the extended bound.
    rw [fenv.restrict_to, Result.ok.injEq] at hfp
    subst hfp
    rw [fenv.restrict_to, Result.ok.injEq] at hf
    subst hf
    exact ⟨lst', hrun, hsr', hsw', hfr, hfw⟩

/-! ## The index congruences (task #58, round 2)

`ConLeche/Cached/ParsedC.lean`'s `checkDeclC` hands the two install gates the
**pre-insertion index** `fe`, where the two statements above are about
`lfe.restrictTo k_pre` — the *extended* index at the pre-insertion bound.  The
two agree on `find?` and differ on `.env`, and everything either gate reads the
index for goes through `find?`: `ConLeche/Verify/Cached/KnotCongr.lean` says so
for the knot (`coreKnotI_congr`, `sharedOpsC_congr`) but stops there, so the
gates' own congruences are proved here.  `sharedOpsC`'s five slots ignore their
`Env` argument (task #24's note 3), which is what makes the `.env` difference
invisible; `sharedOpsC_annotate'`/`_inferType'`/`_isDefEq'` are that fact.

The two `*_at_view` corollaries at the end are the shapes
`Refine/CheckerDecl.lean` should use. -/

/-- `sharedOpsC`'s `annotate` slot ignores its `Env` argument. -/
private theorem sharedOpsC_annotate' (lmode : ConLeche.CheckMode)
    (feO : ConLeche.FEnv) (lenv : ConLeche.Env) (d : Nat) (e : ConLeche.Expr) :
    (ConLeche.Cached.sharedOpsC lmode feO).annotate lenv d e
      = ConLeche.Cached.opE lmode feO (·.annotate) d e := rfl

/-- …and so does `inferType`. -/
private theorem sharedOpsC_inferType' (lmode : ConLeche.CheckMode)
    (feO : ConLeche.FEnv) (lenv : ConLeche.Env) (d : Nat) (e : ConLeche.Expr) :
    (ConLeche.Cached.sharedOpsC lmode feO).inferType lenv d e
      = ConLeche.Cached.opE lmode feO (·.infer) d e := rfl

/-- …and so does `isDefEq`. -/
private theorem sharedOpsC_isDefEq' (lmode : ConLeche.CheckMode)
    (feO : ConLeche.FEnv) (lenv : ConLeche.Env) (d : Nat) (a b : ConLeche.Expr) :
    (ConLeche.Cached.sharedOpsC lmode feO).isDefEq lenv d a b
      = ConLeche.Cached.opB lmode feO d a b := rfl

/-- `Expr.constsResolveF` reads the index only through `find?`.  (The cached
twin `constsResolveFC_congr` is `KnotCongr.lean`'s; the pure walk's is not.) -/
theorem constsResolveF_congr {fe₁ fe₂ : ConLeche.FEnv}
    (hfe : fe₁.find? = fe₂.find?) (e : ConLeche.Expr) :
    e.constsResolveF fe₁ = e.constsResolveF fe₂ := by
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | const n us => simp only [ConLeche.Expr.constsResolveF, hfe]
  | fvar _ ty ih => simp only [ConLeche.Expr.constsResolveF, ih]
  | app f a ihf iha => simp only [ConLeche.Expr.constsResolveF, ihf, iha]
  | lam ty b m iht ihb => simp only [ConLeche.Expr.constsResolveF, iht, ihb]
  | forallE ty b m iht ihb => simp only [ConLeche.Expr.constsResolveF, iht, ihb]
  | letE ty v b iht ihv ihb =>
    simp only [ConLeche.Expr.constsResolveF, iht, ihv, ihb]
  | lit l => cases l <;> simp only [ConLeche.Expr.constsResolveF, hfe]
  | proj sn i e ih => simp only [ConLeche.Expr.constsResolveF, hfe, ih]

/-- `reduceElemOkF` reads the index only through `find?`. -/
theorem reduceElemOkF_congr {fe₁ fe₂ : ConLeche.FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : ConLeche.Name) :
    ConLeche.reduceElemOkF fe₁ c = ConLeche.reduceElemOkF fe₂ c := by
  simp only [ConLeche.reduceElemOkF, hfe]

/-- `reduceStoredOkF` reads the index only through `find?`. -/
theorem reduceStoredOkF_congr {fe₁ fe₂ : ConLeche.FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : ConLeche.Name) :
    ConLeche.reduceStoredOkF fe₁ c = ConLeche.reduceStoredOkF fe₂ c := by
  simp only [ConLeche.reduceStoredOkF, hfe]

/-- `reducePinGuardF` reads the index only through `find?`. -/
theorem reducePinGuardF_congr {fe₁ fe₂ : ConLeche.FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : ConLeche.Name) :
    ConLeche.reducePinGuardF fe₁ c = ConLeche.reducePinGuardF fe₂ c := by
  simp only [ConLeche.reducePinGuardF, constsResolveF_congr hfe]

/-- `divModCertGuardF` reads the index only through `find?`. -/
theorem divModCertGuardF_congr {fe₁ fe₂ : ConLeche.FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : ConLeche.Name)
    (annVal : ConLeche.Expr) (hyps : List ConLeche.Expr)
    (eqE proof : ConLeche.Expr) :
    ConLeche.divModCertGuardF fe₁ c annVal hyps eqE proof
      = ConLeche.divModCertGuardF fe₂ c annVal hyps eqE proof := by
  simp only [ConLeche.divModCertGuardF, constsResolveF_congr hfe]

/-- `divModPinGuardF` reads the index only through `find?`. -/
theorem divModPinGuardF_congr {fe₁ fe₂ : ConLeche.FEnv}
    (hfe : fe₁.find? = fe₂.find?) (ps : ConLeche.NatOpPinSet)
    (c : ConLeche.Name) :
    ConLeche.divModPinGuardF ps fe₁ c = ConLeche.divModPinGuardF ps fe₂ c := by
  simp only [ConLeche.divModPinGuardF, constsResolveF_congr hfe]

/-- `divModCertsGuardF` reads the index only through `find?`. -/
theorem divModCertsGuardF_congr {fe₁ fe₂ : ConLeche.FEnv}
    (hfe : fe₁.find? = fe₂.find?) (ps : ConLeche.NatOpPinSet)
    (c : ConLeche.Name) (annVal : ConLeche.Expr) :
    ConLeche.divModCertsGuardF ps fe₁ c annVal
      = ConLeche.divModCertsGuardF ps fe₂ c annVal := by
  simp only [ConLeche.divModCertsGuardF, divModCertGuardF_congr hfe]

/-- `checkDivModCertsF` reads its index only through `find?` (the operation
record is a third, independent index — `sharedOpsC_congr` moves that one). -/
theorem checkDivModCertsF_congr {lmode : ConLeche.CheckMode}
    {feO fe₁ fe₂ : ConLeche.FEnv} (hfe : fe₁.find? = fe₂.find?)
    (c : ConLeche.Name) (annVal : ConLeche.Expr) :
    ∀ (S : List (List ConLeche.Expr × ConLeche.Expr)) (P : List ConLeche.Expr),
      ConLeche.checkDivModCertsF (ConLeche.Cached.sharedOpsC lmode feO) fe₁ c
          annVal S P
        = ConLeche.checkDivModCertsF (ConLeche.Cached.sharedOpsC lmode feO) fe₂ c
          annVal S P := by
  intro S
  induction S with
  | nil => intro P; cases P <;> rfl
  | cons st S ih =>
    intro P
    cases P with
    | nil => rfl
    | cons p P =>
      obtain ⟨hyps, eqE⟩ := st
      simp only [ConLeche.checkDivModCertsF, divModCertGuardF_congr hfe,
        sharedOpsC_annotate', sharedOpsC_inferType', sharedOpsC_isDefEq', ih]

/-- `checkDivModPinAtF` reads its index only through `find?`. -/
theorem checkDivModPinAtF_congr {lmode : ConLeche.CheckMode}
    {feO fe₁ fe₂ : ConLeche.FEnv} (hfe : fe₁.find? = fe₂.find?)
    (c : ConLeche.Name) (value' : ConLeche.Expr) (ps : ConLeche.NatOpPinSet) :
    ConLeche.checkDivModPinAtF (ConLeche.Cached.sharedOpsC lmode feO) fe₁ c
        value' ps
      = ConLeche.checkDivModPinAtF (ConLeche.Cached.sharedOpsC lmode feO) fe₂ c
        value' ps := by
  simp only [ConLeche.checkDivModPinAtF, sharedOpsC_annotate',
    sharedOpsC_isDefEq', checkDivModCertsF_congr hfe]

/-- `checkDivModPinLoopF` reads its index only through `find?`. -/
theorem checkDivModPinLoopF_congr {lmode : ConLeche.CheckMode}
    {feO fe₁ fe₂ : ConLeche.FEnv} (hfe : fe₁.find? = fe₂.find?)
    (c : ConLeche.Name) (value' : ConLeche.Expr) :
    ∀ (vs : List ConLeche.NatOpPinSet) (tried : List String),
      ConLeche.checkDivModPinLoopF (ConLeche.Cached.sharedOpsC lmode feO) fe₁ c
          value' vs tried
        = ConLeche.checkDivModPinLoopF (ConLeche.Cached.sharedOpsC lmode feO) fe₂
          c value' vs tried := by
  intro vs
  induction vs with
  | nil => intro tried; rfl
  | cons ps rest ih =>
    intro tried
    simp only [ConLeche.checkDivModPinLoopF, divModPinGuardF_congr hfe,
      divModCertsGuardF_congr hfe, checkDivModPinAtF_congr hfe, ih]

/-- **`checkDivModPinF` reads its pre-insertion index only through `find?`**:
the `.defnDecl` arm may hand it any index that agrees with the view the
statement above is about. -/
theorem checkDivModPinF_congr {lmode : ConLeche.CheckMode}
    {fe₁ fe₂ fe2 : ConLeche.FEnv} (hfe : fe₁.find? = fe₂.find?)
    (c : ConLeche.Name) :
    ConLeche.checkDivModPinF (ConLeche.Cached.sharedOpsC lmode fe₁) fe₁ fe2 c
      = ConLeche.checkDivModPinF (ConLeche.Cached.sharedOpsC lmode fe₂) fe₂ fe2 c := by
  rw [ConLeche.Cached.sharedOpsC_congr hfe]
  simp only [ConLeche.checkDivModPinF, checkDivModPinLoopF_congr hfe]

/-- **`checkReducePinF` reads its pre-insertion index only through `find?`** —
the congruence the `.opaqueDecl` arm needs. -/
theorem checkReducePinF_congr {lmode : ConLeche.CheckMode}
    {fe₁ fe₂ fe2 : ConLeche.FEnv} (hfe : fe₁.find? = fe₂.find?)
    (c : ConLeche.Name) (value : ConLeche.Expr) :
    ConLeche.checkReducePinF (ConLeche.Cached.sharedOpsC lmode fe₁) fe₁ fe2 c value
      = ConLeche.checkReducePinF (ConLeche.Cached.sharedOpsC lmode fe₂) fe₂ fe2 c
        value := by
  rw [ConLeche.Cached.sharedOpsC_congr hfe]
  simp only [ConLeche.checkReducePinF, reduceElemOkF_congr hfe,
    reducePinGuardF_congr hfe, sharedOpsC_annotate', sharedOpsC_isDefEq']

/-- `certifyNatEqs`' `Env` argument is dead at `sharedOpsC` (task #24's note 3):
the slots ignore it.  What lets `check_structural_nat_pin_refines` quantify it
universally. -/
theorem certifyNatEqs_env_congr {lmode : ConLeche.CheckMode}
    {feO : ConLeche.FEnv} (lenv lenv' : ConLeche.Env)
    (eqs : List (ConLeche.Expr × ConLeche.Expr)) :
    ConLeche.certifyNatEqs (ConLeche.Cached.sharedOpsC lmode feO) lenv eqs
      = ConLeche.certifyNatEqs (ConLeche.Cached.sharedOpsC lmode feO) lenv' eqs := by
  induction eqs with
  | nil => rfl
  | cons e es ih =>
    simp only [ConLeche.certifyNatEqs, sharedOpsC_isDefEq', ih]

/-! ### The two gates at an arbitrary pre-insertion view

What `Refine/CheckerDecl.lean` should call: the statements above transported by
the congruences to whatever index the caller actually holds, which need only
agree with `lfe.restrictTo k_pre` on `find?`.  Nothing is weakened — each is
its own lemma at `lfp := lfe.restrictTo k_pre.val`, `hlfp := rfl`. -/

/-- `check_div_mod_pin_refines` at any `find?`-agreeing pre-insertion index. -/
theorem check_div_mod_pin_refines_at_view {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {k_pre : Std.U64}
    {c : name.Name}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hvar : PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    (h : checker.check_div_mod_pin mode pins st fe k_pre c = ok (.Ok fe', st')) :
    ∀ lst lfe (lfp : ConLeche.FEnv), StateRel st lst → FEnvRel fe lfe →
      EqBasisPinnedSpec fe lfe →
      lfp.find? = (lfe.restrictTo k_pre.val).find? →
      ∃ lst', (ConLeche.checkDivModPinF (TypeChecker.lops mode lfp) lfp lfe
            (absName c)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lst lfe lfp hsr hfr heqb hlfp
  rw [checkDivModPinF_congr hlfp]
  exact check_div_mod_pin_refines hfuel hk hsw hfw hc hvar hpins h
    lst lfe hsr hfr heqb

/-- `check_reduce_pin_refines` at any `find?`-agreeing pre-insertion index. -/
theorem check_reduce_pin_refines_at_view {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (htp : TrustPinsSpec)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {k_pre : Std.U64}
    {c : name.Name} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hc : NameWF c) (hval : ExprWF value)
    (h : checker.check_reduce_pin mode st fe k_pre c value = ok (.Ok fe', st')) :
    ∀ lst lfe (lfp : ConLeche.FEnv), StateRel st lst → FEnvRel fe lfe →
      TrustGuardsSpec fe lfe →
      (∀ fp : fenv.FEnv, FEnvRel fp (lfe.restrictTo k_pre.val) → FEnvWF fp →
        TrustGuardsSpec fp (lfe.restrictTo k_pre.val)) →
      lfp.find? = (lfe.restrictTo k_pre.val).find? →
      ∃ lst', (ConLeche.checkReducePinF (TypeChecker.lops mode lfp) lfp lfe
            (absName c) (absExpr value)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lst lfe lfp hsr hfr htg htgp hlfp
  rw [checkReducePinF_congr hlfp]
  exact check_reduce_pin_refines hfuel hk htp hsw hfw hc hval h lst lfe hsr hfr
    htg htgp

/-! ## `checker.rs`'s pin dispatch (`:1299-1400`, task #58 round 2)

Task #56's split left the `.defnDecl` arm's two pinned-`Nat` gates uncovered:
`check_defn_pins`, `check_defn_div_mod_pin`, `check_structural_nat_pin` and its
helper `nat_eqs_subst`.  They are the pin gate and belong beside
`check_div_mod_pin_refines`.

`check_structural_nat_pin` is the one with no con-leche sibling at all: it is
`checkDecl`'s **inlined** structural-`Nat` block (`Checker.lean:419-562`,
`Cached/ParsedC.lean:164-181` at the index), so its statement is the
conjunction of the three facts that block needs — the guard, the stored
definition, and the certification run — rather than one function's refinement.
Task #58 changed its dependency clause to `checker::deps_all_stored_ok`, the
cited `(natOpDeps c).all (natOpStoredOkF fe2)`, so `deps_all_stored_ok_refines`
above is what discharges it.

`certifyNatEqs`' refinement is `Refine/Checker.lean`'s; that file is being
rewritten in parallel and this one may not import it, so it is re-proved here
as a **step**, as `one_level_step` and `consts_resolve_f_step` are. -/

private theorem certify_nat_eqs_val_step {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {fe : fenv.FEnv} {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (hfw : FEnvWF fe) (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2) (n : Nat) :
    ∀ (st st' : cached.state_c.CState) (i : Std.Usize) (b : Bool),
      eqs.val.length - i.val ≤ n → StateWF st →
      kernel.checker.certify_nat_eqs_from mode st fe eqs i = ok (.Ok b, st') →
      ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
        ∃ lst',
          (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
              ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst
            = .ok (b, lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  induction n with
  | zero =>
    intro st st' i b hb hsw h lst lfe lenv hsr hfr
    rw [kernel.checker.certify_nat_eqs_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len eqs by
      have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
    have hbs : b = true ∧ st = st' := by simpa using h
    obtain ⟨rfl, rfl⟩ := hbs
    refine ⟨lst, ?_, hsr, hsw⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro st st' i b hb hsw h lst lfe lenv hsr hfr
    rw [kernel.checker.certify_nat_eqs_from] at h
    by_cases hge : i.val >= eqs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len eqs by
        have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
      have hbs : b = true ∧ st = st' := by simpa using h
      obtain ⟨rfl, rfl⟩ := hbs
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len eqs) by
        have := alloc.vec.Vec.len_val eqs; scalar_tac)] at h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, e2⟩ := q
      have hmem : (e1, e2) ∈ eqs.val :=
        List.mem_of_getElem? (ExprOps.vec_index_getElem? hq)
      obtain ⟨hw1, hw2⟩ := heq (e1, e2) hmem
      obtain ⟨q2, hdef, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q2
      cases r with
      | Err e => simp at h
      | Ok ok1 =>
        obtain ⟨lst1, hrun, hsr1, hsw1⟩ :=
          (TypeChecker.is_def_eq_core_refines hfuel hk).ok st fe 2#u64 e1 e2 ok1 st1
            hsw hfw hw1 hw2 hdef lst lfe hsr hfr
        have hrun2 : (ConLeche.Cached.opB (absMode mode) lfe 2
            (absExpr e1) (absExpr e2)).run lst = .ok (ok1, lst1) := hrun
        have hlen : i.val < eqs.val.length := by omega
        have hdrop : eqs.val.drop i.val = (e1, e2) :: eqs.val.drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons hlen]
          congr 1
          have h1 : eqs.val[i.val]? = some (e1, e2) := ExprOps.vec_index_getElem? hq
          rw [List.getElem?_eq_getElem hlen] at h1
          exact Option.some_inj.mp h1
        have hstep : (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
              ((eqs.val.drop i.val).map (fun p => (absExpr p.1, absExpr p.2)))).run lst
            = (if ok1 then
                (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
                  ((eqs.val.drop (i.val + 1)).map (fun p => (absExpr p.1, absExpr p.2)))).run lst1
              else .ok (false, lst1)) := by
          simp only [hdrop, List.map_cons, ConLeche.certifyNatEqs, StateT.run_bind,
            TypeChecker.sharedOpsC_isDefEq, hrun2]
          cases ok1 <;> simp [List.map_drop] <;> rfl
        cases ok1 with
        | false =>
          have hbs : b = false ∧ st1 = st' := by simpa using h
          obtain ⟨rfl, rfl⟩ := hbs
          exact ⟨lst1, by rw [hstep]; simp, hsr1, hsw1⟩
        | true =>
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := by
            have he := Std.UScalar.add_equiv i 1#usize
            rw [hi2] at he
            simpa using he.2.1
          obtain ⟨lst', hrun', hsr', hsw'⟩ :=
            ih st1 st' i2 b (by omega) hsw1 h lst1 lfe lenv hsr1 hfr
          rw [hi2v] at hrun'
          exact ⟨lst', by rw [hstep]; simpa using hrun', hsr', hsw'⟩

/-- `checker::certify_nat_eqs` refines `certifyNatEqs` on the whole list
(`Checker.lean:108-116`).  A step copy of `Refine/Checker.lean`'s
`certify_nat_eqs_refines`. -/
private theorem certify_nat_eqs_step {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)} {b : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe)
    (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2)
    (h : checker.certify_nat_eqs mode st fe eqs = ok (.Ok b, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lenv
            (eqs.val.map (fun p => (absExpr p.1, absExpr p.2)))).run lst
          = .ok (b, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe lenv hsr hfr
  rw [checker.certify_nat_eqs] at h
  obtain ⟨lst', hrun, rest⟩ :=
    certify_nat_eqs_val_step hfuel hk hfw heq eqs.val.length st st' 0#usize b
      (by omega) hsw h lst lfe lenv hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

/-! ### `checker::nat_eqs_subst` — the cited `List.map` -/

/-- `con-leche: none` — the equation table's substitution
(`(natOpEquations 0 c).map fun eq => (substConst0 c value' eq.1, …)`); §3.4
forbids the closure, so the port names the map, and `nat_eqs_subst_from` is its
index recursion with the accumulator passed by value. -/
private theorem nat_eqs_subst_from_refines {n : name.Name} {value2 : expr.Expr}
    (hn : NameWF n) (hv : ExprWF value2)
    {eqs : alloc.vec.Vec (expr.Expr × expr.Expr)}
    (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2) (k : Nat) :
    ∀ (i : Std.Usize) (out r : alloc.vec.Vec (expr.Expr × expr.Expr)),
      eqs.val.length - i.val ≤ k →
      (∀ p ∈ out.val, ExprWF p.1 ∧ ExprWF p.2) →
      checker.nat_eqs_subst_from n value2 eqs i out = ok r →
      r.val.map (fun p => (absExpr p.1, absExpr p.2))
          = out.val.map (fun p => (absExpr p.1, absExpr p.2))
            ++ (eqs.val.drop i.val).map (fun p =>
                 (ConLeche.Expr.substConst0 (absName n) (absExpr value2) (absExpr p.1),
                  ConLeche.Expr.substConst0 (absName n) (absExpr value2) (absExpr p.2)))
        ∧ ∀ p ∈ r.val, ExprWF p.1 ∧ ExprWF p.2 := by
  have hlen := alloc.vec.Vec.len_val eqs
  induction k with
  | zero =>
    intro i out r hk hout h
    rw [checker.nat_eqs_subst_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len eqs by scalar_tac)] at h
    rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by omega)]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out r hk hout h
    rw [checker.nat_eqs_subst_from] at h
    by_cases hge : eqs.val.length ≤ i.val
    · rw [if_pos (show i >= alloc.vec.Vec.len eqs by scalar_tac)] at h
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by omega)]
      exact ⟨by simp, hout⟩
    · have hlt : i.val < eqs.val.length := by omega
      rw [if_neg (show ¬ (i >= alloc.vec.Vec.len eqs) by scalar_tac)] at h
      obtain ⟨q, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a, b⟩ := q
      have hx : eqs.val[i.val] = (a, b) := vec_index_val hidx hlt
      have hab : ExprWF a ∧ ExprWF b :=
        heq (a, b) (by rw [← hx]; exact List.getElem_mem hlt)
      simp at h
      obtain ⟨a1, ha1, b1, hb1, out1, hout1, i2, hi2, h⟩ := h
      obtain ⟨ha1abs, ha1wf⟩ := CoreK.subst_const0_refines hn hv hab.1 a1 ha1
      obtain ⟨hb1abs, hb1wf⟩ := CoreK.subst_const0_refines hn hv hab.2 b1 hb1
      have hout1v : out1.val = out.val ++ [(a1, b1)] := vec_push_val hout1
      have hout1wf : ∀ p ∈ out1.val, ExprWF p.1 ∧ ExprWF p.2 := by
        intro p hp
        rw [hout1v] at hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hout p hp
        · exact ⟨ha1wf, hb1wf⟩
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ := ih i2 out1 r (by omega) hout1wf h
      refine ⟨?_, hwf⟩
      rw [habs, hi2v, List.drop_eq_getElem_cons hlt, hx, hout1v]
      simp [ha1abs, hb1abs]

/-- `con-leche: none` — `checker::nat_eqs_subst` is the cited `List.map`. -/
theorem nat_eqs_subst_refines {n : name.Name} {value2 : expr.Expr}
    {eqs r : alloc.vec.Vec (expr.Expr × expr.Expr)} (hn : NameWF n)
    (hv : ExprWF value2) (heq : ∀ p ∈ eqs.val, ExprWF p.1 ∧ ExprWF p.2)
    (h : checker.nat_eqs_subst n value2 eqs = ok r) :
    r.val.map (fun p => (absExpr p.1, absExpr p.2))
        = eqs.val.map (fun p =>
            (ConLeche.Expr.substConst0 (absName n) (absExpr value2) (absExpr p.1),
             ConLeche.Expr.substConst0 (absName n) (absExpr value2) (absExpr p.2)))
      ∧ ∀ p ∈ r.val, ExprWF p.1 ∧ ExprWF p.2 := by
  rw [checker.nat_eqs_subst] at h
  obtain ⟨habs, hwf⟩ :=
    nat_eqs_subst_from_refines hn hv heq eqs.val.length 0#usize
      (alloc.vec.Vec.new (expr.Expr × expr.Expr)) r (by omega)
      (by intro p hp; simp [alloc.vec.Vec.new] at hp) h
  refine ⟨?_, hwf⟩
  rw [habs, show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero]
  simp [alloc.vec.Vec.new]

/-! ### The structural-`Nat` gate (`checker.rs:1359-1393`) -/

/-- `ConLeche/Kernel/Checker.lean:419-562 checkDecl`'s inlined structural-`Nat`
block, `ConLeche/Cached/ParsedC.lean:164-181` at the index —
**`checker::check_structural_nat_pin` refines it**: the operation and its
dependencies are stored in the pinned shapes, and its recurrence equations
certify by definitional equality in the *pre-insertion* view with the
operation's self-references replaced by its stored value.

The cited Lean has no function of its own for this (it is three statements
inlined in `checkDecl`), so the conclusion is the conjunction of the three
facts that block needs.  The certification runs at
`lfe.restrictTo k_pre`; `ConLeche.Cached.sharedOpsC_congr` moves it to whatever
`find?`-agreeing pre-insertion index the caller holds, and `lenv` is
universally quantified because `certifyNatEqs`' `Env` argument is dead
(task #24's note 3).  The last conjunct, `fe' = fe2`, is the `restrict_to`
round trip: the gate hands the index back exactly as it got it (§2's
visibility-bound note), which is what lets a caller carry a `*Spec` about
`fe2` past it. -/
theorem check_structural_nat_pin_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe2 fe' : fenv.FEnv} {k_pre : Std.U64}
    {n : name.Name}
    (hsw : StateWF st) (hfw : FEnvWF fe2) (hn : NameWF n)
    (h : checker.check_structural_nat_pin mode st fe2 k_pre n
      = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ConLeche.natOpGuardF lfe (absName n) = true
      ∧ ((ConLeche.natOpDeps (absName n)).all
          (ConLeche.natOpStoredOkF lfe)) = true
      ∧ (∃ (cvL : ConLeche.ConstantVal) (value' : ConLeche.Expr)
           (hintL : ConLeche.ReducibilityHint) (lst' : ConLeche.Cached.CState),
          lfe.find? (absName n) = some (.defnInfo cvL value' hintL)
          ∧ (∀ lenv : ConLeche.Env,
              (ConLeche.certifyNatEqs
                  (TypeChecker.lops mode (lfe.restrictTo k_pre.val)) lenv
                  ((ConLeche.natOpEquations 0 (absName n)).map fun eq =>
                    (ConLeche.Expr.substConst0 (absName n) value' eq.1,
                     ConLeche.Expr.substConst0 (absName n) value' eq.2))).run lst
                = .ok (true, lst'))
          ∧ StateRel st' lst' ∧ StateWF st')
      ∧ FEnvRel fe' lfe ∧ FEnvWF fe' ∧ fe' = fe2 := by
  intro lst lfe hsr hfr
  have hfa : FindAgree fe2 lfe := FindAgree.of_rel hfr hfw
  have hfwf : FindWF fe2 := FindWF.of_wf hfw
  rw [checker.check_structural_nat_pin] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := CoreK.nat_op_guard_refines hfa hn
    (CoreK.natLitSupportedSpec hfa hfwf) (CoreK.lpEmptySpec hfa)
    (fun _ hv => CoreK.nat_op_deps_refines hn hv)
    CoreK.pinned_nat_beq_name CoreK.pinned_nat_ble_name
    CoreK.pinned_nat_div_mod_names CoreK.pinned_bool_true_name
    CoreK.pinned_bool_false_name hb
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    exact (err_tail_ne_ok h).elim
  | true =>
    simp only [if_true] at h
    obtain ⟨deps, hdeps, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hdabs, hdwf⟩ := CoreK.nat_op_deps_refines hn hdeps
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := deps_all_stored_ok_refines hfa hfwf (CoreK.defnProbeSpec hfa hfwf)
      CoreK.pinned_nat_pred_name CoreK.pinned_nat_beq_name
      CoreK.pinned_nat_ble_name CoreK.pinned_bool_name CoreK.pinned_nat_name
      CoreK.toConstantValSpec hdwf hb1
    rw [hdabs] at hb1v
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      exact (err_tail_ne_ok h).elim
    | true =>
      simp only [if_true] at h
      obtain ⟨o, hprobe, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hpabs, hpwf⟩ := CoreK.defn_probe_refines hfa hfwf hn hprobe
      cases o with
      | none => exact (err_tail_ne_ok h).elim
      | some t =>
        obtain ⟨cv, value2, hint⟩ := t
        obtain ⟨-, hvwf⟩ := hpwf cv value2 hint rfl
        have hfind : lfe.find? (absName n)
            = some (.defnInfo (absConstantVal cv) (absExpr value2)
              (absHint hint)) := by
          simp only [Option.map_some] at hpabs
          cases hf : lfe.find? (absName n) with
          | none => rw [hf] at hpabs; simp [CoreK.defnOf] at hpabs
          | some ci =>
            rw [hf] at hpabs
            cases ci with
            | defnInfo cv1 v1 h1 =>
              simp only [CoreK.defnOf, Option.some.injEq, Prod.mk.injEq] at hpabs
              rw [hpabs.1, hpabs.2.1, hpabs.2.2]
            | _ => simp [CoreK.defnOf] at hpabs
        simp at h
        obtain ⟨eqt, heqt, eqv, heqv, fp, hfp, res, st1, hcert, fe3, hfe3, h⟩ := h
        obtain ⟨heqtabs, heqtwf⟩ :=
          CoreK.nat_op_equations_refines hn CoreK.natOpPinned CoreK.pinned_nat_name
            CoreK.pinned_nat_zero_name CoreK.pinned_nat_succ_name heqt
        obtain ⟨heqvabs, heqvwf⟩ := nat_eqs_subst_refines hn hvwf heqtwf heqv
        have hfprel : FEnvRel fp (lfe.restrictTo k_pre.val) := restrict_to_refines hfr hfp
        have hfpwf : FEnvWF fp := restrict_to_wf hfw hfp
        cases res with
        | Err e => simp at h
        | Ok ok1 =>
          cases ok1 with
          | false => simp at h
          | true =>
            obtain ⟨lstC, hrunC, hsrC, hswC⟩ :=
              certify_nat_eqs_step hfuel hk hsw hfpwf heqvwf hcert lst
                (lfe.restrictTo k_pre.val) lfe.env hsr hfprel
            have hmap : eqv.val.map (fun q => (absExpr q.1, absExpr q.2))
                = (ConLeche.natOpEquations 0 (absName n)).map (fun eq =>
                    (ConLeche.Expr.substConst0 (absName n) (absExpr value2) eq.1,
                     ConLeche.Expr.substConst0 (absName n) (absExpr value2) eq.2)) := by
              rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at heqtabs
              rw [heqvabs, ← heqtabs, List.map_map]; rfl
            rw [hmap] at hrunC
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hround : FEnvRel fe3 lfe ∧ FEnvWF fe3 ∧ fe3 = fe2 := by
              rw [fenv.restrict_to, Result.ok.injEq] at hfp
              subst hfp
              rw [fenv.restrict_to, Result.ok.injEq] at hfe3
              subst hfe3
              exact ⟨hfr, hfw, rfl⟩
            exact ⟨hbv.symm, hb1v.symm,
              ⟨absConstantVal cv, absExpr value2, absHint hint, lstC, hfind,
                fun lenv => by
                  rw [certifyNatEqs_env_congr lenv lfe.env]; exact hrunC,
                hsrC, hswC⟩,
              hround.1, hround.2.1, hround.2.2⟩

/-! ### The `.defnDecl` arm's dispatch (`checker.rs:1319-1353`) -/

/-- `ConLeche/Kernel/Checker.lean:459-460 checkDecl`,
`ConLeche/Cached/ParsedC.lean:182-183` — **`checker::check_defn_div_mod_pin`
refines the cited `if natDivModNames.contains cv.name then checkDivModPinF …`**.
A name outside the table is the `else` arm's `pure ()`, and the index comes
back unchanged. -/
theorem check_defn_div_mod_pin_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe2 fe' : fenv.FEnv} {k_pre : Std.U64}
    {n : name.Name}
    (hsw : StateWF st) (hfw : FEnvWF fe2) (hn : NameWF n) (hvar : PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    (h : checker.check_defn_div_mod_pin mode pins st fe2 k_pre n
      = ok (.Ok fe', st')) :
    ∀ lst lfe (lfp : ConLeche.FEnv), StateRel st lst → FEnvRel fe2 lfe →
      EqBasisPinnedSpec fe2 lfe →
      lfp.find? = (lfe.restrictTo k_pre.val).find? →
      ∃ lst', ((if ConLeche.natDivModNames.contains (absName n) then
            ConLeche.checkDivModPinF (TypeChecker.lops mode lfp) lfp lfe
              (absName n)
          else pure ()) : ConLeche.Cached.CheckCM Unit).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lst lfe lfp hsr hfr heqb hlfp
  rw [checker.check_defn_div_mod_pin] at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvabs, hvwf⟩ := CoreK.pinned_nat_div_mod_names v hv
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := Name.contains_refines hvwf hn hb
  rw [hvabs] at hbv
  cases b with
  | false =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, by rw [← hbv]; simp only [Bool.false_eq_true, if_false]; rfl,
      hsr, hsw, hfr, hfw⟩
  | true =>
    simp only [if_true] at h
    obtain ⟨lst', hrun, hsr', hsw', hfr', hfw'⟩ :=
      check_div_mod_pin_refines_at_view hfuel hk hsw hfw hn hvar hpins h
        lst lfe lfp hsr hfr heqb hlfp
    exact ⟨lst', by rw [← hbv]; simpa using hrun, hsr', hsw', hfr', hfw'⟩

/-- `ConLeche/Cached/ParsedC.lean:164-183` — **`checker::check_defn_pins`
refines the `.defnDecl` arm's two pinned-`Nat` gates**, in order: the
structural-`Nat` block when the name is one of `natOpNames`, then the
`Nat.div`/`Nat.mod` gate when it is one of `natDivModNames`.

The cited Lean inlines the first block, so the conclusion hands its three
facts back separately (`check_structural_nat_pin_refines`) and names the
intermediate model state `lst1` the second gate runs from; when the name is not
a structural op nothing runs and `lst1 = lst`.  Both halves are stated at an
arbitrary `find?`-agreeing pre-insertion index `lfp`, which is the index
`checkDeclC` actually hands them. -/
theorem check_defn_pins_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe2 fe' : fenv.FEnv} {k_pre : Std.U64}
    {n : name.Name}
    (hsw : StateWF st) (hfw : FEnvWF fe2) (hn : NameWF n) (hvar : PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    (h : checker.check_defn_pins mode pins st fe2 k_pre n = ok (.Ok fe', st')) :
    ∀ lst lfe (lfp : ConLeche.FEnv), StateRel st lst → FEnvRel fe2 lfe →
      EqBasisPinnedSpec fe2 lfe →
      lfp.find? = (lfe.restrictTo k_pre.val).find? →
      ∃ lst1 lst' : ConLeche.Cached.CState,
        (ConLeche.natOpNames.contains (absName n) = true →
          ConLeche.natOpGuardF lfe (absName n) = true
          ∧ ((ConLeche.natOpDeps (absName n)).all
              (ConLeche.natOpStoredOkF lfe)) = true
          ∧ ∃ (cvL : ConLeche.ConstantVal) (value' : ConLeche.Expr)
              (hintL : ConLeche.ReducibilityHint),
              lfe.find? (absName n) = some (.defnInfo cvL value' hintL)
              ∧ ∀ lenv : ConLeche.Env,
                  (ConLeche.certifyNatEqs (TypeChecker.lops mode lfp) lenv
                      ((ConLeche.natOpEquations 0 (absName n)).map fun eq =>
                        (ConLeche.Expr.substConst0 (absName n) value' eq.1,
                         ConLeche.Expr.substConst0 (absName n) value' eq.2))).run lst
                    = .ok (true, lst1))
        ∧ (ConLeche.natOpNames.contains (absName n) = false → lst1 = lst)
        ∧ ((if ConLeche.natDivModNames.contains (absName n) then
              ConLeche.checkDivModPinF (TypeChecker.lops mode lfp) lfp lfe
                (absName n)
            else pure ()) : ConLeche.Cached.CheckCM Unit).run lst1 = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lst lfe lfp hsr hfr heqb hlfp
  rw [checker.check_defn_pins] at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hvabs, hvwf⟩ := CoreK.pinned_nat_op_names v hv
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := Name.contains_refines hvwf hn hb
  rw [hvabs] at hbv
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨lst', hrun, hsr', hsw', hfr', hfw'⟩ :=
      check_defn_div_mod_pin_refines hfuel hk hsw hfw hn hvar hpins h
        lst lfe lfp hsr hfr heqb hlfp
    exact ⟨lst, lst', fun hc => absurd hc (by rw [← hbv]; simp),
      fun _ => rfl, hrun, hsr', hsw', hfr', hfw'⟩
  | true =>
    simp only [if_true] at h
    obtain ⟨q, hq, h2⟩ := bind_eq_ok_iff.mp h
    obtain ⟨res, st1⟩ := q
    cases res with
    | Err e => simp at h2
    | Ok fe3 =>
      obtain ⟨hg, hd, ⟨cvL, value', hintL, lstC, hfindL, hcertL, hsrC, hswC⟩,
        hfr3, hfw3, rfl⟩ :=
        check_structural_nat_pin_refines hfuel hk hsw hfw hn hq lst lfe hsr hfr
      simp at h2
      obtain ⟨lst', hrun, hsr', hsw', hfr', hfw'⟩ :=
        check_defn_div_mod_pin_refines hfuel hk hswC hfw hn hvar hpins h2
          lstC lfe lfp hsrC hfr heqb hlfp
      refine ⟨lstC, lst', fun _ => ⟨hg, hd, cvL, value', hintL, hfindL, ?_⟩,
        fun hc => absurd hc (by rw [← hbv]; simp), hrun, hsr', hsw', hfr', hfw'⟩
      intro lenv
      rw [TypeChecker.lops, ConLeche.Cached.sharedOpsC_congr hlfp]
      exact hcertL lenv

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.CheckerPins.div_mod_cert_stmts_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms div_mod_cert_stmts_refines

/--
info: 'ConRon.Refine.CheckerPins.check_div_mod_certs_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_div_mod_certs_refines

/--
info: 'ConRon.Refine.CheckerPins.check_div_mod_pin_loop_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_div_mod_pin_loop_refines

/--
info: 'ConRon.Refine.CheckerPins.check_reduce_pin_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_reduce_pin_refines

/--
info: 'ConRon.Refine.CheckerPins.checkReducePinF_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkReducePinF_congr

/--
info: 'ConRon.Refine.CheckerPins.checkDivModPinF_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkDivModPinF_congr

/--
info: 'ConRon.Refine.CheckerPins.check_structural_nat_pin_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_structural_nat_pin_refines

/--
info: 'ConRon.Refine.CheckerPins.check_defn_pins_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_defn_pins_refines

end ConRon.Refine.CheckerPins
