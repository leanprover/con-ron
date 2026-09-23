/-
# `ConRon.Refine2.Checker.Axioms` — Theorem 2 for the three PIN modules

**Task #97-P5-Checker**, deliverable 2 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{basis,std_axioms,trust_axioms}.rs` against
`proof/ConRon/Arena/{Basis,StdAxioms,TrustAxioms}.lean`: the basis blocks, the
standard axioms' pinned shapes and the compiler-trust axioms' — all of them
con-leche's own data, which DESIGN §8.7 rules (B) IMPORTS rather than copies.

## Why fifty-eight lemmas and almost no new ideas

`Arena/Intern.lean`'s module note is the whole story: *a handle twin of one of
these would be the same tree spelled with `internE` instead of `Expr.app`, and
nothing would be gained*, so every twin here is **one line — the con-leche
constant, interned** — and every lemma is `Refine2/Promote/Intern.lean`'s
`intern_ci` / `intern_cv` / `intern_expr` / `intern_ci_list` at a named
constant, with the con-leche value's `ConstantInfoWF` / `ConstantValWF` /
`ExprWF` coming from `Refine/{BasisTables,StdAxioms,TrustAxioms,Pins*}.lean`,
where the pinned-data tier already proved it.

**That is the deliberate dividend of the 47 surviving `Refine` modules** (task
#97-SWAP §5): their SUBJECT survived the arena swap because the pins did, and
this file is where the arena tower collects the interest.

## The three that are not one-liners

* `erase_pw_eq` — con-leche's structural equality **up to the `pw` datum**,
  the one thing the erasure forgives (`StdAxioms.lean`'s "task #161 P5" note).
  Ten arms and a fuel peel, `SimRE` because it only `view`s.
* `i_constant_val_matches_pin` — exact name, level parameters and counts, type
  up to `pw`.  A name comparison is a HANDLE comparison (DESIGN §8.3:
  `denoteN` is injective, so index inequality IS structural inequality), which
  is the one place this file leans on exactness.
* `basis_pin_hit_go` — con-leche's task-#215 NAME pre-filter in front of
  `canonEqList`, and `find?`'s semantics spelled as a helper (DESIGN §3.4
  forbids the closure): a name match that then fails the canonical comparison
  is `none`, **not** "try the next kind".

## What these lemmas wait on

`Refine2/Promote/Intern.lean`'s four entries, and through them `Specs.lean`'s
`intern_e` family (task #97-P5-1 §8's twenty-four still open).  Nothing here
waits on an idea.
-/
import ConRon.Refine2.Checker.Canon
import ConRon.Refine.BasisPins
import ConRon.Refine.BasisRaw

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The pinned constants, interned (task #97-T2-LOCKSTEP lane Checker round 2)

Each Rust pin reader is `let c ← kernel::…::pin; intern_*(c)` and each twin
is `intern* ConLeche.pin`: the pinned-data tier (`Refine/{StdAxioms,
TrustAxioms,BasisPins,BasisRaw,BasisTables}.lean`) says the Rust pin
abstracts to con-leche's with its `*WF`, and `Refine2/Promote/Intern.lean`'s
four intern entries do the rest.  These four helpers are that composition. -/

theorem sim_intern_ci_of {pers st lst} {m : Result kernel.env.ConstantInfo}
    {C : ConLeche.ConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ∀ c, m = ok c →
      ConRon.Refine.absConstantInfo c = C ∧ ConRon.Refine.ConstantInfoWF c)
    (hrun : (m >>= fun c => arena.intern.intern_ci pers st c) = ok o) :
    Sim₀ absIConstantInfo pers lst o (internCI C) := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ha, hw⟩ := hm c hc
  rw [← ha]; exact intern_ci_refines hrel hinv hw h

theorem sim_intern_cv_of {pers st lst} {m : Result kernel.env.ConstantVal}
    {C : ConLeche.ConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ∀ c, m = ok c →
      ConRon.Refine.absConstantVal c = C ∧ ConRon.Refine.ConstantValWF c)
    (hrun : (m >>= fun c => arena.intern.intern_cv pers st c) = ok o) :
    Sim₀ absIConstantVal pers lst o (internCV C) := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ha, hw⟩ := hm c hc
  rw [← ha]; exact intern_cv_refines hrel hinv hw h

theorem sim_intern_expr_of {pers st lst} {m : Result kernel.expr.Expr}
    {C : ConLeche.Expr} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ∀ c, m = ok c → ConRon.Refine.absExpr c = C ∧ ConRon.Refine.ExprWF c)
    (hrun : (m >>= fun c => arena.intern.intern_expr pers st c) = ok o) :
    Sim₀ absEIdx pers lst o (internExpr C) := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ha, hw⟩ := hm c hc
  rw [← ha]; exact intern_expr_refines hrel hinv hw h

theorem sim_intern_ci_list_of {pers st lst}
    {m : Result (alloc.vec.Vec kernel.env.ConstantInfo)}
    {C : List ConLeche.ConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ∀ c, m = ok c →
      ConRon.Refine.absConstantInfos c = C ∧ ConRon.Refine.ConstantInfosWF c)
    (hrun : (m >>= fun c => arena.intern.intern_ci_list pers st c) = ok o) :
    Sim₀ absICIL pers lst o (internCIList C) := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ha, hw⟩ := hm c hc
  rw [← ha]; exact intern_ci_list_refines hrel hinv hw h

/-! ## `erase_pw_eq`'s node transcription

The twin's `match ← view a, ← view b with` body, past the two `view`s —
`Refine2/Checker/Canon.lean`'s `canonExprEqAtSpec` at another comparison. -/

/-- `erasePwEq`'s ten matching arms and its catch-all. -/
def erasePwEqAtSpec (fuel : Nat) : ENodeView → ENodeView → AM Bool
  | .bvar i, .bvar j => pure (i == j)
  | .fvar i t, .fvar j t' =>
    if i == j then erasePwEq fuel t t' else pure false
  | .sort u, .sort v => pure (u == v)
  | .const n us, .const n' us' => pure (n == n' && us == us')
  | .app f x, .app f' x' => do
    if ← erasePwEq fuel f f' then erasePwEq fuel x x' else pure false
  | .lam t bd _, .lam t' bd' _ => do
    if ← erasePwEq fuel t t' then erasePwEq fuel bd bd' else pure false
  | .forallE t bd _, .forallE t' bd' _ => do
    if ← erasePwEq fuel t t' then erasePwEq fuel bd bd' else pure false
  | .letE t v bd, .letE t' v' bd' => do
    if ← erasePwEq fuel t t' then
      if ← erasePwEq fuel v v' then erasePwEq fuel bd bd' else pure false
    else pure false
  | .lit l, .lit l' => pure (l == l')
  | .proj s i e, .proj s' i' e' =>
    if s == s' && i == i' then erasePwEq fuel e e' else pure false
  | _, _ => pure false

/-- `erasePwEq` in terms of its transcription. -/
theorem erasePwEq_unfold (fuel : Nat) (a b : EIdx) :
    erasePwEq (fuel + 1) a b =
      (do erasePwEqAtSpec fuel (← view a) (← view b)) := by
  sorry

/-! ## `arena::basis` — the pinned blocks -/

/-- `basis_kind_decls` ⊑ `BasisKind.decls` — the RAW constants of one basis block, in dependency order, interned. -/
theorem basis_kind_decls_refines {pers st lst} {k : kernel.env.BasisKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_kind_decls pers st k = ok o) :
    Sim₀ absICIL pers lst o
      (BasisKind.decls (ConRon.Refine.absBasisKind k)) := by
  rw [arena.basis.basis_kind_decls] at hrun
  exact sim_intern_ci_list_of hrel hinv (fun _ h => ConRon.Refine.BasisRaw.basis_kind_decls_refines h) hrun

/-- `basis_kind_decls_a` ⊑ `BasisKind.declsA` — the ANNOTATED constants, which is what `checkBasisDecl` installs. -/
theorem basis_kind_decls_a_refines {pers st lst} {k : kernel.env.BasisKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_kind_decls_a pers st k = ok o) :
    Sim₀ absICIL pers lst o
      (BasisKind.declsA (ConRon.Refine.absBasisKind k)) := by
  rw [arena.basis.basis_kind_decls_a] at hrun
  refine sim_intern_ci_list_of hrel hinv (fun v h => ⟨?_, ConRon.Refine.BasisPins.basis_decls_a_wf h⟩) hrun
  obtain ⟨v', hv', habs⟩ := Aeneas.Std.WP.spec_imp_exists (ConRon.Refine.basis_decls_a_refines k)
  rw [h] at hv'
  obtain rfl := Result.ok_injective hv'
  exact habs

/-- `block_names` ⊑ `blockNames` at the cursor — `IConstantInfo.name` is pure (task #97e), so the twin is a plain `List.map`. -/
theorem block_names_refines  {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.basis.block_names block i out = ok o) :
    absNIdxL o = absNIdxL out ++ blockNames (absICILFrom block i) := by
  sorry

/-- `basis_pin_hit_go` ⊑ `basisPinHitGo` at the cursor — con-leche's task-#215 NAME pre-filter in front of the canonical comparison. -/
theorem basis_pin_hit_go_refines {pers st lst} {block : alloc.vec.Vec arena.env.IConstantInfo} {ks : alloc.vec.Vec kernel.env.BasisKind} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_pin_hit_go pers st block ks i = ok o) :
    Sim₀ (Option.map ConRon.Refine.absBasisKind) pers lst o
      (basisPinHitGo (absICIL block) (absBasisKindLFrom ks i)) := by
  sorry

/-- `basis_pin_hit` ⊑ `basisPinHit` — the five pinned blocks, in con-leche's order; `.quotK` is deliberately not among them. -/
theorem basis_pin_hit_refines {pers st lst} {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_pin_hit pers st block = ok o) :
    Sim₀ (Option.map ConRon.Refine.absBasisKind) pers lst o
      (basisPinHit (absICIL block)) := by
  sorry

/-- `quot_pin_hit` ⊑ `quotPinHit` — the record is the pinned package's constant at the slot it declares itself at, compared at `toConstantVal`. -/
theorem quot_pin_hit_refines {pers st lst} {k : kernel.env.QuotKind} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.quot_pin_hit pers st k cv = ok o) :
    Sim₀ id pers lst o
      (quotPinHit (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  sorry

/-- `propext_name` ⊑ `propextName`, off the pin table. -/
theorem propext_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.propext_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (propextName) := by
  rw [arena.std_axioms.propext_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_propext_refines hrel hinv h) hrun

/-- `choice_name` ⊑ `choiceName`, off the pin table. -/
theorem choice_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.choice_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (choiceName) := by
  rw [arena.std_axioms.choice_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_choice_refines hrel hinv h) hrun

/-- `iff_name` ⊑ `iffName`, off the pin table. -/
theorem iff_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (iffName) := by
  rw [arena.std_axioms.iff_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_iff_refines hrel hinv h) hrun

/-- `iff_intro_name` ⊑ `iffIntroName`, off the pin table. -/
theorem iff_intro_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_intro_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (iffIntroName) := by
  rw [arena.std_axioms.iff_intro_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_iff_intro_refines hrel hinv h) hrun

/-- `iff_rec_name` ⊑ `iffRecName`, off the pin table. -/
theorem iff_rec_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_rec_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (iffRecName) := by
  rw [arena.std_axioms.iff_rec_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_iff_rec_refines hrel hinv h) hrun

/-- `nonempty_name` ⊑ `nonemptyName`, off the pin table. -/
theorem nonempty_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (nonemptyName) := by
  rw [arena.std_axioms.nonempty_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_nonempty_refines hrel hinv h) hrun

/-- `nonempty_intro_name` ⊑ `nonemptyIntroName`, off the pin table. -/
theorem nonempty_intro_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_intro_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (nonemptyIntroName) := by
  rw [arena.std_axioms.nonempty_intro_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_nonempty_intro_refines hrel hinv h) hrun

/-- `nonempty_rec_name` ⊑ `nonemptyRecName`, off the pin table. -/
theorem nonempty_rec_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_rec_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (nonemptyRecName) := by
  rw [arena.std_axioms.nonempty_rec_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_nonempty_rec_refines hrel hinv h) hrun

/-- `erase_pw_eq` ⊑ `erasePwEq` — structural equality up to the `pw` datum, which is exactly what the erasure forgives. -/
theorem erase_pw_eq_refines {pers st lst} {fuel : Std.U64} {a : arena.handle.EIdx} {b : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.erase_pw_eq pers st fuel a b = ok o) :
    SimRE id lst o
      (erasePwEq (absU fuel) (absEIdx a) (absEIdx b)) := by
  sorry

/-- `erase_pw_eq_at` is `erase_pw_eq`'s body past the two `view`s (extraction rule 5), stated against the transcription above. -/
theorem erase_pw_eq_at_refines {pers st lst} {fuel : Std.U64} {va : arena.store.ENodeView} {vb : arena.store.ENodeView} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.erase_pw_eq_at pers st fuel va vb = ok o) :
    SimRE id lst o
      (erasePwEqAtSpec (absU fuel) (absENodeView va) (absENodeView vb)) := by
  sorry

/-- `erase_pw_eq_two` is the two-child arms' pair of descents, in the twin's order and with its short-circuit. -/
theorem erase_pw_eq_two_refines {pers st lst} {fuel : Std.U64} {a : arena.handle.EIdx} {a2 : arena.handle.EIdx} {b : arena.handle.EIdx} {b2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.erase_pw_eq_two pers st fuel a a2 b b2 = ok o) :
    SimRE id lst o
      ((do
        if ← erasePwEq (absU fuel) (absEIdx a) (absEIdx b) then
          erasePwEq (absU fuel) (absEIdx a2) (absEIdx b2)
        else pure false)) := by
  sorry

/-- `i_constant_val_matches_pin` ⊑ `IConstantVal.matchesPin` — exact name, level parameters and counts, type up to the `pw` datum. -/
theorem i_constant_val_matches_pin_refines {pers st lst} {cv : arena.env.IConstantVal} {pin : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.i_constant_val_matches_pin pers st cv pin = ok o) :
    SimRE id lst o
      ((absIConstantVal cv).matchesPin (absIConstantVal pin)) := by
  sorry

/-- `iff_raw` ⊑ `iffRaw` — the con-leche constant, interned. -/
theorem iff_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffRaw) := by
  rw [arena.std_axioms.iff_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_raw_refines h) hrun

/-- `iff_intro_raw` ⊑ `iffIntroRaw` — the con-leche constant, interned. -/
theorem iff_intro_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_intro_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffIntroRaw) := by
  rw [arena.std_axioms.iff_intro_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_intro_raw_refines h) hrun

/-- `iff_rec_intro` ⊑ `iffRecIntro` — the con-leche constant, interned. -/
theorem iff_rec_intro_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_rec_intro pers st = ok o) :
    Sim₀ absEIdx pers lst o
      (iffRecIntro) := by
  rw [arena.std_axioms.iff_rec_intro] at hrun
  exact sim_intern_expr_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_rec_intro_refines h) hrun

/-- `iff_rec_raw` ⊑ `iffRecRaw` — the con-leche constant, interned. -/
theorem iff_rec_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_rec_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffRecRaw) := by
  rw [arena.std_axioms.iff_rec_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_rec_raw_refines h) hrun

/-- `iff_family` ⊑ `iffFamily` — the con-leche constant, interned. -/
theorem iff_family_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_family pers st = ok o) :
    Sim₀ absICIL pers lst o
      (iffFamily) := by
  rw [arena.std_axioms.iff_family] at hrun
  exact sim_intern_ci_list_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_family_refines h) hrun

/-- `propext_raw` ⊑ `propextRaw` — the con-leche constant, interned. -/
theorem propext_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.propext_raw pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (propextRaw) := by
  rw [arena.std_axioms.propext_raw] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.propext_raw_refines h) hrun

/-- `nonempty_raw` ⊑ `nonemptyRaw` — the con-leche constant, interned. -/
theorem nonempty_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyRaw) := by
  rw [arena.std_axioms.nonempty_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_raw_refines h) hrun

/-- `nonempty_intro_raw` ⊑ `nonemptyIntroRaw` — the con-leche constant, interned. -/
theorem nonempty_intro_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_intro_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyIntroRaw) := by
  rw [arena.std_axioms.nonempty_intro_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_intro_raw_refines h) hrun

/-- `nonempty_rec_raw` ⊑ `nonemptyRecRaw` — the con-leche constant, interned. -/
theorem nonempty_rec_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_rec_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyRecRaw) := by
  rw [arena.std_axioms.nonempty_rec_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_rec_raw_refines h) hrun

/-- `nonempty_family` ⊑ `nonemptyFamily` — the con-leche constant, interned. -/
theorem nonempty_family_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_family pers st = ok o) :
    Sim₀ absICIL pers lst o
      (nonemptyFamily) := by
  rw [arena.std_axioms.nonempty_family] at hrun
  exact sim_intern_ci_list_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_family_refines h) hrun

/-- `choice_raw` ⊑ `choiceRaw` — the con-leche constant, interned. -/
theorem choice_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.choice_raw pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (choiceRaw) := by
  rw [arena.std_axioms.choice_raw] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.choice_raw_refines h) hrun

/-- `eq_a` ⊑ `eqA` — the con-leche constant, interned. -/
theorem eq_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.eq_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (eqA) := by
  rw [arena.std_axioms.eq_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.BasisPins.eq_a_refines h) hrun

/-- `nat_a` ⊑ `natA` — the con-leche constant, interned. -/
theorem nat_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nat_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (natA) := by
  rw [arena.std_axioms.nat_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.BasisPins.nat_a_refines h) hrun

/-- `true_name` ⊑ `trueName`, off the pin table. -/
theorem true_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (trueName) := by
  rw [arena.trust_axioms.true_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_true_refines hrel hinv h) hrun

/-- `true_intro_name` ⊑ `trueIntroName`, off the pin table. -/
theorem true_intro_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_intro_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (trueIntroName) := by
  rw [arena.trust_axioms.true_intro_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_true_intro_refines hrel hinv h) hrun

/-- `trust_compiler_name` ⊑ `trustCompilerName`, off the pin table. -/
theorem trust_compiler_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.trust_compiler_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (trustCompilerName) := by
  rw [arena.trust_axioms.trust_compiler_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_trust_compiler_refines hrel hinv h) hrun

/-- `reduce_nat_name` ⊑ `reduceNatName`, off the pin table. -/
theorem reduce_nat_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_nat_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (reduceNatName) := by
  rw [arena.trust_axioms.reduce_nat_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_reduce_nat_refines hrel hinv h) hrun

/-- `reduce_bool_name` ⊑ `reduceBoolName`, off the pin table. -/
theorem reduce_bool_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_bool_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (reduceBoolName) := by
  rw [arena.trust_axioms.reduce_bool_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_reduce_bool_refines hrel hinv h) hrun

/-- `of_reduce_nat_name` ⊑ `ofReduceNatName`, off the pin table. -/
theorem of_reduce_nat_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_nat_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (ofReduceNatName) := by
  rw [arena.trust_axioms.of_reduce_nat_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_of_reduce_nat_refines hrel hinv h) hrun

/-- `of_reduce_bool_name` ⊑ `ofReduceBoolName`, off the pin table. -/
theorem of_reduce_bool_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_bool_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (ofReduceBoolName) := by
  rw [arena.trust_axioms.of_reduce_bool_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_of_reduce_bool_refines hrel hinv h) hrun

/-- `reduce_op_names` ⊑ `reduceOpNames` — the reduce operations pinned at their `opaque` install. -/
theorem reduce_op_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_op_names st = ok o) :
    Sim₀ absNIdxL pers lst o
      (reduceOpNames) := by
  unfold reduceOpNames
  rw [arena.trust_axioms.reduce_op_names] at hrun
  unfold Sim₀
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.trust_axioms.reduce_nat_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_reduce_nat_refines hrel hinv hr0
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := reduceNatName) hS0)
  | Ok a0 =>
  rw [pin_ok (tw := reduceNatName) hS0]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.trust_axioms.reduce_bool_name] at hq1
  obtain ⟨r1, hr1, hq1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq1
  have hS1 := pin_reduce_bool_refines hrel hinv hr1
  obtain rfl := (Result.ok_injective hq1).symm
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := reduceBoolName) hS1)
  | Ok a1 =>
  rw [pin_ok (tw := reduceBoolName) hS1]
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w1, hw1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have hv : w1.val = [a0, a1] := by
    rw [ConRon.Refine.vec_push_val hw1, ConRon.Refine.vec_push_val hw0,
      ConRon.Refine.ExprOps.with_capacity_val]
    rfl
  refine ⟨lst, ?_, hrel, hinv⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

/-- `of_reduce_op` ⊑ `ofReduceOp` — the reduce operation an `ofReduce*` axiom speaks about; con-leche's name test is a handle comparison here. -/
theorem of_reduce_op_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_op st n = ok o) :
    Sim₀ absNIdx pers lst o
      (ofReduceOp (absNIdx n)) := by
  sorry

/-- `true_cv_a` ⊑ `trueCvA`. -/
theorem true_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (trueCvA) := by
  rw [arena.trust_axioms.true_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.true_cv_a_refines h) hrun

/-- `true_intro_cv_a` ⊑ `trueIntroCvA`. -/
theorem true_intro_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_intro_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (trueIntroCvA) := by
  rw [arena.trust_axioms.true_intro_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.true_intro_cv_a_refines h) hrun

/-- `trust_compiler_a` ⊑ `trustCompilerA`. -/
theorem trust_compiler_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.trust_compiler_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (trustCompilerA) := by
  rw [arena.trust_axioms.trust_compiler_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.trust_compiler_a_refines h) hrun

/-- `bool_cv_a` ⊑ `boolCvA`. -/
theorem bool_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.bool_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (boolCvA) := by
  rw [arena.trust_axioms.bool_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.bool_cv_a_refines h) hrun

/-- `reduce_elem_name` ⊑ `reduceElemName`. -/
theorem reduce_elem_name_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_elem_name st c = ok o) :
    Sim₀ absNIdx pers lst o
      (reduceElemName (absNIdx c)) := by
  sorry

/-- `reduce_elem_ty` ⊑ `reduceElemTy`. -/
theorem reduce_elem_ty_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_elem_ty pers st c = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceElemTy (absNIdx c)) := by
  sorry

/-- `reduce_op_raw` ⊑ `reduceOpRaw`. -/
theorem reduce_op_raw_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_op_raw pers st c = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceOpRaw (absNIdx c)) := by
  sorry

/-- `of_reduce_raw` ⊑ `ofReduceRaw`. -/
theorem of_reduce_raw_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_raw pers st n = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReduceRaw (absNIdx n)) := by
  sorry

/-- `reduce_nat_cv_a` ⊑ `reduceNatCvA`. -/
theorem reduce_nat_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_nat_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceNatCvA) := by
  rw [arena.trust_axioms.reduce_nat_cv_a] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hna, hnw⟩ := ConRon.Refine.TrustAxioms.reduce_nat_name_refines hn
  refine sim_intern_cv_of hrel hinv (fun _ h => ?_) hrun
  obtain ⟨ha, hw⟩ := ConRon.Refine.TrustAxioms.reduce_op_cv_a_refines hnw h
  refine ⟨?_, hw⟩
  rw [ha, hna]
  rfl

/-- `reduce_bool_cv_a` ⊑ `reduceBoolCvA`. -/
theorem reduce_bool_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_bool_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceBoolCvA) := by
  rw [arena.trust_axioms.reduce_bool_cv_a] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hna, hnw⟩ := ConRon.Refine.TrustAxioms.reduce_bool_name_refines hn
  refine sim_intern_cv_of hrel hinv (fun _ h => ?_) hrun
  obtain ⟨ha, hw⟩ := ConRon.Refine.TrustAxioms.reduce_op_cv_a_refines hnw h
  refine ⟨?_, hw⟩
  rw [ha, hna]
  rfl

/-- `of_reduce_nat_a` ⊑ `ofReduceNatA` — the RAW pin `ofReduceRaw ofReduceNatName`,
interned.

Task #97-P5-Top found the old statement false (the twin interned con-leche's
annotated `ofReduceNatA`, the port the raw pin); round 2's ruling (a) moved
the twin's slot to the raw pin (`Arena/TrustAxioms.lean`), so the statement is
the port's again. -/
theorem of_reduce_nat_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_nat_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReduceNatA) := by
  rw [arena.trust_axioms.of_reduce_nat_a] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hna, hnw⟩ := ConRon.Refine.TrustAxioms.of_reduce_nat_name_refines hn
  refine sim_intern_cv_of hrel hinv (fun _ h => ?_) hrun
  obtain ⟨ha, hw⟩ := ConRon.Refine.TrustAxioms.of_reduce_pin_a_refines hnw h
  refine ⟨?_, hw⟩
  rw [ha, hna]
  rfl

/-- `of_reduce_bool_a` ⊑ `ofReduceBoolA` — the RAW pin `ofReduceRaw ofReduceBoolName`,
interned.

Task #97-P5-Top found the old statement false (the twin interned con-leche's
annotated `ofReduceBoolA`, the port the raw pin); round 2's ruling (a) moved
the twin's slot to the raw pin (`Arena/TrustAxioms.lean`), so the statement is
the port's again. -/
theorem of_reduce_bool_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_bool_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReduceBoolA) := by
  rw [arena.trust_axioms.of_reduce_bool_a] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hna, hnw⟩ := ConRon.Refine.TrustAxioms.of_reduce_bool_name_refines hn
  refine sim_intern_cv_of hrel hinv (fun _ h => ?_) hrun
  obtain ⟨ha, hw⟩ := ConRon.Refine.TrustAxioms.of_reduce_pin_a_refines hnw h
  refine ⟨?_, hw⟩
  rw [ha, hna]
  rfl

/-- `reduce_op_cv_a` ⊑ `reduceOpCvA`. -/
theorem reduce_op_cv_a_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_op_cv_a pers st c = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceOpCvA (absNIdx c)) := by
  sorry

/-- `of_reduce_pin_a` ⊑ `ofReducePinA`. -/
theorem of_reduce_pin_a_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_pin_a pers st n = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReducePinA (absNIdx n)) := by
  sorry

/-- `reduce_bool_decl_pin` ⊑ `reduceBoolDeclPin`. -/
theorem reduce_bool_decl_pin_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_bool_decl_pin pers st = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceBoolDeclPin) := by
  rw [arena.trust_axioms.reduce_bool_decl_pin] at hrun
  exact sim_intern_expr_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.reduce_bool_decl_pin_refines h) hrun

/-- `reduce_nat_decl_pin` ⊑ `reduceNatDeclPin`. -/
theorem reduce_nat_decl_pin_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_nat_decl_pin pers st = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceNatDeclPin) := by
  rw [arena.trust_axioms.reduce_nat_decl_pin] at hrun
  exact sim_intern_expr_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.reduce_nat_decl_pin_refines h) hrun

/-- `reduce_decl_pin` ⊑ `reduceDeclPin`. -/
theorem reduce_decl_pin_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_decl_pin pers st c = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceDeclPin (absNIdx c)) := by
  sorry

/-- `reduce_cert_var` ⊑ `reduceCertVar`. -/
theorem reduce_cert_var_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_cert_var pers st c = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceCertVar (absNIdx c)) := by
  sorry

end ConRon.Refine2
