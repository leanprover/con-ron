/-
`CORE_PLAN.md` step 4 (task #49), the `prop_read` slice: the refinement of all
eleven `pub fn` of `crates/con-ron-core/src/kernel/prop_read.rs` against
`vendor/con-leche/ConLeche/Kernel/PropRead.lean` (con-leche's task #168), on
the generated model `ConRon.Generated.kernel.prop_read.*`.

The module is two three-valued readers -- "is this type a proposition?"
(`typeSortPW`) and "is this term a proof?" (`proofPW`) -- off the head symbol,
the arity and the validated `pw` annotations, plus the four small pieces they
share (`peelNeverPis`, `numArgs`, `residualPW`, `isProp`) and the two Boolean
verdicts (`notProofFast`, `isProofFast`).  Statements are
exact-result-on-success (DESIGN.md §3.5): an `Option`-returning reader gets an
`Option.map absPropWhen` equation -- so the `none` ("unknown, fall back to
inference") case is a claim too -- plus `PropWhenWF` of the datum, which the
callers store.

**The one standing deviation** (the Rust module note): the cited Lean abstracts
every reader over `find? : Name → Option ConstantInfo` so that the pure
`Env.find?` and the interned `FEnv.find?` share one body.  The port has a
single environment on the checker's path, `fe: &FEnv` with `fenv::find`, so
every reader that takes `fe` is stated with `(hfe : FindAgree fe lfe)` (and
`(hwf : FindWF fe)`, because what a lookup hands back is used as a term) and
against the cited Lean **instantiated at `lfe.find?`**.

Three things shaped the proofs:

* `peel_never_pis` is a `u64`-counted recursion under `partial_fixpoint`, whose
  only induction principle is `fixpoint_induct` (admissible motive, no
  `partial_correctness` over `Result`), so it is the task-#5 shape: a `(N : Nat)`
  lemma with `k.val = N`, inducted on `k` (`Nat.strong_induction_on`), and the
  wrapper is the corollary.  Every other reader here is structurally flat --
  one `match` on the head node -- so its proof is a `cases` on the `ExprWF`
  derivation, not an induction.
* `stored_cv_at` is a *port-invented factorization*: it is the `some ci => if
  ci.isTowerEntry then none else …` prefix that `headTypePW` and `headProofPW`
  both open with, pulled out as a probe (task #14's rule).  It has no cited
  Lean definition of its own, so `storedCVAt` below is that prefix written out
  once on the con-leche side, and the two head readers rewrite with it.
* `env::is_tower_entry` and `env::to_constant_val` belong to `kernel::env`
  (task #46's `Refine/Env.lean`), but `stored_cv_at` cannot be stated without
  them; they are proved here, locally, and should move.  `to_constant_val`'s
  refinement is stated on `absConstantVal` rather than on the `ConstantVal`
  record itself: the port's `ProjInfo` arm *builds* a value where Lean shares
  one, and the `Vec<Name>` copy of the other arms is equal only up to `.val`.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.PropRead

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PropRead

/-! ## `kernel::env`'s two `ConstantInfo` readers (they belong to task #46) -/

/-! ## `stored_cv_at`, the shared prefix of the two head readers -/

/-! ## `peel_never_pis` and `num_args` -/

/-! ## `residual_pw` and `head_type_pw` -/

/-! ## `type_sort_pw` -/

/-! ## `head_proof_pw`, `proof_pw` and the two verdicts -/

/-- `prop_read::is_prop` refines `PropWhen.isProp` (`PropRead.lean:136-139`):
the cited `pw == (.ifAllZero [])` goes through the port's `prop_when::beq`,
whose exactness on well-formed data is `PropWhen.beq_refines`. -/
theorem is_prop_refines {pw : prop_when.PropWhen} {b : Bool} (hpw : PropWhenWF pw)
    (h : prop_read.is_prop pw = ok b) :
    b = ConLeche.PropWhen.isProp (absPropWhen pw) := by
  rw [prop_read.is_prop] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pw1, hpw1, hb⟩ := h
  have hnames : NamesWF (alloc.vec.Vec.new name.Name) := by
    intro q hq; simp [alloc.vec.Vec.new] at hq
  have hbeq : ∀ x y : ConLeche.PropWhen, decide (x = y) = (x == y) := by
    intro x y; rw [Bool.eq_iff_iff]; simp
  rw [PropWhen.beq_refines hpw (PropWhen.if_all_zero_wf hnames hpw1) hb,
    PropWhen.if_all_zero_refines hnames hpw1]
  simp [ConLeche.PropWhen.isProp, absNames, alloc.vec.Vec.new, hbeq]

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`is_proof_fast_refines` is the top of the file: it depends on every lemma here
except `not_proof_fast_refines`, on `FindAgree`/`FindWF` from `CoreKBase.lean`, and
on the `Expr`/`Level`/`PropWhen` tiers underneath.  No `sorry`, nothing from
Aeneas's library beyond the pointer model, no `import all`. -/

end ConRon.Refine.PropRead
