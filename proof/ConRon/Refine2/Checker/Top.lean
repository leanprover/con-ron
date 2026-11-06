/-
# `ConRon.Refine2.Checker.Top` — Theorem 2 for `arena::check_decl` and what remains of `arena::checker`

**Task #97-P5-Checker**, deliverables 2 and 3 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{check_decl,checker}.rs` against
`proof/ConRon/Arena/{CheckDecl,Checker}.lean`: `check_decl`'s six arms, the
fold's `And` pin (`and_pin_ok`), and the startup walk `intern_all_pins`.  A
record's job (`stream_index::record_check`, `checker::run_job`) is
`Refine2/Checker/Jobs.lean`'s.

Every kind is checked in its arm.  A value arm checks the value returning the
record unpushed (`Refine2/Checker/DeclCheck.lean`), runs its pinned gates, which
read the environment with the record pushed and hand it back popped
(`gate_push_refines`, `SimEnv`), and pushes last.  A pinned block and a quotient
record are compared with their pins and installed at the names they declare.

## Finding 14 — `check_ind_decl` is the Inductives tier's

`arena::check_decl::check_ind_decl` is the pinned-basis test, the declared
parameter count, the recogniser and ONE route: the uniform install
`check_block` or the decline `check_shapeless`.  The route's stages are
`arena::inductives::*`, not this tier's, and `Refine2/Inductives/Top.lean`
exports them as `@[lockstep]` lemmas over this tier's base
(`Checker/Base.lean`); `check_ind_decl_refines` is one `lockstep` call over
them.

The statements take `AStateRel₀` and `AStateInv` and nothing else: lockstep,
with no precondition on the twin.
-/
import ConRon.Refine2.Checker.DeclCheck
import ConRon.Refine2.Checker.Basis
import ConRon.Refine2.Inductives.Top

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The arms' remaining callees in the judgements `lockstep` zips with

`DeclCheck.lean` files the `*_ok` gates' `_ls`; the Rust-only copy is here. -/

namespace Lockstep

@[lockstep] theorem top_i_constant_info_dup_spec (c : arena.env.IConstantInfo) :
    LSP (arena.env.i_constant_info_dup c)
      (fun o => absIConstantInfo o = absIConstantInfo c) :=
  fun _ h => i_constant_info_dup_abs h

end Lockstep

/-! ## The pinned `And` (con-leche's ANDPIN, task #106) -/

/-- `and_pin_decls` ⊑ `andPinDecls` — the pinned `And` block, interned. -/
theorem and_pin_decls_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.and_pin_decls pers st = ok o) :
    Sim₀ absICIL pers lst o andPinDecls := by
  rw [arena.basis.and_pin_decls] at hrun
  exact sim_intern_ci_list_of hrel hinv
    (fun _ h => ConRon.Refine.BasisRaw.and_pin_refines h) hrun

open Lockstep in
@[lockstep] theorem and_pin_decls_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a) (arena.basis.and_pin_decls pers st) lst
      andPinDecls :=
  LS.ofSim₀ fun _ h => and_pin_decls_refines hrel hinv h

/-- `and_pin_name_hs` ⊑ `andPinNameHs` — the three slot reads, as a handle
list; a pin read moves neither state, so neither does the list. -/
theorem and_pin_name_hs_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.and_pin_name_hs st = ok o) :
    Lockstep.PA1.PinRE absNIdxList lst o andPinNameHs := by
  rw [arena.basis.and_pin_name_hs] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have h1 := Lockstep.PA1.pin_and_run₀ hrel hinv hr
  simp only [andPinNameHs, Lockstep.PA1.PinRE, StateT.run_bind] at h1 ⊢
  cases r with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    exact AErrSim.bind h1 _
  | Ok a =>
    simp only at hrun h1
    rw [h1]
    obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := Lockstep.PA1.pin_and_intro_run₀ hrel hinv hr1
    simp only [Lockstep.PA1.PinRE] at h2
    cases r1 with
    | Err e =>
      obtain rfl := (Result.ok_injective hrun).symm
      exact AErrSim.bind h2 _
    | Ok i =>
      simp only at hrun h2
      dsimp only [Bind.bind, Except.bind]
      rw [h2]
      obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have h3 := Lockstep.PA1.pin_and_rec_run₀ hrel hinv hr2
      simp only [Lockstep.PA1.PinRE] at h3
      cases r2 with
      | Err e =>
        obtain rfl := (Result.ok_injective hrun).symm
        exact AErrSim.bind h3 _
      | Ok r3 =>
        simp only at hrun h3
        dsimp only [Bind.bind, Except.bind]
        rw [h3]
        obtain ⟨hs, hhs, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨hs1, hhs1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨hs2, hhs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain rfl := (Result.ok_injective hrun).symm
        have e2 := ConRon.Refine.vec_push_val hhs2
        have e1 := ConRon.Refine.vec_push_val hhs1
        have e0 := ConRon.Refine.vec_push_val hhs
        simp [absNIdxList, e2, e1, e0, alloc.vec.Vec.new]
        rfl

open Lockstep in
@[lockstep] theorem and_pin_name_hs_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxList a) (arena.basis.and_pin_name_hs st) st lst
      andPinNameHs :=
  PA1.pinRE_lsr hrel hinv fun _ h => and_pin_name_hs_run₀ hrel hinv h

/-- `block_and_named` ⊑ `blockAndNamed` at the cursor. -/
theorem block_and_named_aux (k : Nat) :
    ∀ (block : alloc.vec.Vec arena.env.IConstantInfo)
      (hs : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {o},
      block.val.length - i.val = k →
      arena.basis.block_and_named block hs i = ok o →
      o = blockAndNamed (absNIdxList hs) (absICILFrom block i) := by
  induction k with
  | zero =>
    intro block hs i o hn h
    rw [arena.basis.block_and_named] at h
    have hl := alloc.vec.Vec.len_val block
    rw [ite_eq_left (by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    have : absICILFrom block i = [] := by
      simp only [absICILFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [this]; rfl
  | succ m ih =>
    intro block hs i o hn h
    rw [arena.basis.block_and_named] at h
    have hl := alloc.vec.Vec.len_val block
    rw [ite_eq_right (by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi : i.val < block.val.length := by omega
    have hx : block.val[i.val] = ii := by
      have h1 := vec_index_some hii
      rw [List.getElem?_eq_getElem hi] at h1
      exact Option.some_inj.mp h1
    have hbv : b = (absNIdxList hs).contains (absNIdx n) :=
      Lockstep.nidx_vec_contains_spec hs n b hb
    have hcons : absICILFrom block i =
        absIConstantInfo ii :: (block.val.drop (i.val + 1)).map absIConstantInfo := by
      simp only [absICILFrom]; rw [List.drop_eq_getElem_cons hi, hx]; rfl
    rw [hcons, blockAndNamed, ← i_constant_info_name_abs hn2, ← hbv]
    cases b with
    | true =>
      rw [ite_eq_left rfl] at h
      exact (Result.ok_injective h).symm
    | false =>
      rw [ite_eq_right (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v := ConRon.Refine.Nat.uadd_val hi2
      rw [ih block hs i2 (by simp at hi2v; omega) h, Bool.false_or]
      simp only [absICILFrom]
      simp at hi2v; rw [hi2v]

open Lockstep in
/-- `block_and_named` from its entry. -/
@[lockstep] theorem block_and_named_spec (block : alloc.vec.Vec arena.env.IConstantInfo)
    (hs : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.basis.block_and_named block hs 0#usize)
      (fun o => o = blockAndNamed (absNIdxList hs) (absICIL block)) := by
  intro o h
  have := block_and_named_aux _ block hs 0#usize rfl h
  simpa [absICILFrom, absICIL] using this

open Lockstep in
/-- `and_pin_name_free` ⊑ `andPinNameFree` — a one-constant record's arm. -/
@[lockstep] theorem and_pin_name_free_ls {pers st lst} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a) (arena.basis.and_pin_name_free st n) st lst
      (andPinNameFree (absNIdx n)) := by
  apply LSR.of_LS
  rw [arena.basis.and_pin_name_free, andPinNameFree]
  lockstep

/-- `and_pin_ok` ⊑ `andPinOk` — **the fold's `And` pin**: the record declares
none of the pinned `And` block's names, or it is that block. -/
theorem and_pin_ok_refines {pers st lst} {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.and_pin_ok pers st pd = ok o) :
    Sim₀ id pers lst o (andPinOk (absIDeclaration pd)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  have hcanon : ∀ {st lst} (xs ys : alloc.vec.Vec arena.env.IConstantInfo),
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a) (arena.canon.canon_eq_list pers st xs ys 0#usize) lst
        (canonEqList (absICIL xs) (absICIL ys)) := by
    intro st lst xs ys hrel hinv
    refine Lockstep.LS.ofSim₀ fun _ h => ?_
    have := canon_eq_list_refines hrel hinv h
    simpa [absICILFrom, absICIL] using this
  cases pd <;> unfold arena.basis.and_pin_ok <;>
    simp only [absIDeclaration, andPinOk] <;> lockstep

/-! ## The axiom arm, in five -/

/-- `check_axiom_decl_rest` — the three remaining name tests: the two standard
axioms' shape mismatch, `sorryAx` tolerated as a DECLARATION, and everything
else declined. -/
theorem check_axiom_decl_rest_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_rest pers st rf cv_a = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkAxiomDeclRestSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_rest]
  try unfold checkAxiomDeclRestSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_rest_ls {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers) (arena.check_decl.check_axiom_decl_rest pers st rf cv_a) lst
      (checkAxiomDeclRestSpec lf (absIConstantVal cv_a)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_rest_refines hrel hinv hfe.rel hfe.inv h

/-- `check_axiom_decl_of_reduce` — the `ofReduce*` arm. -/
theorem check_axiom_decl_of_reduce_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_of_reduce pers st rf cv_a = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkAxiomDeclOfReduceSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_of_reduce, checkAxiomDeclOfReduceSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_of_reduce_ls {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers) (arena.check_decl.check_axiom_decl_of_reduce pers st rf cv_a) lst
      (checkAxiomDeclOfReduceSpec lf (absIConstantVal cv_a)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_of_reduce_refines hrel hinv hfe.rel hfe.inv h

/-- `check_axiom_decl_trust` — the `Lean.trustCompiler` arm. -/
theorem check_axiom_decl_trust_refines {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_trust pers st rf cv_a = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkAxiomDeclTrustSpec lf (absIConstantVal cv_a)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_trust, checkAxiomDeclTrustSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_trust_ls {pers st lst} {rf lf}
    {cv_a : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers) (arena.check_decl.check_axiom_decl_trust pers st rf cv_a) lst
      (checkAxiomDeclTrustSpec lf (absIConstantVal cv_a)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_trust_refines hrel hinv hfe.rel hfe.inv h

/-- `check_axiom_decl_std` — the axiom arm past `Quot.sound`: the common
constant check, then the standard-axiom gate. -/
theorem check_axiom_decl_std_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl_std pers st mode rf cv = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkAxiomDeclStdSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl_std, checkAxiomDeclStdSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_axiom_decl_std_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers)
      (arena.check_decl.check_axiom_decl_std pers st mode rf cv) lst
      (checkAxiomDeclStdSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_axiom_decl_std_refines hrel hinv hfe.rel hfe.inv h

@[lockstep_simp] theorem absICIL_length (v : alloc.vec.Vec arena.env.IConstantInfo) :
    (absICIL v).length = v.val.length := by simp [absICIL]

/-- **`check_quot_record` ⊑ `checkQuotRecord`**: a quotient record compared with its
slot's pin, the slots it needs stored, and installed at its own names. -/
theorem check_quot_record_refines {pers st lst} {rf lf}
    {k : kernel.env.QuotKind} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.check_quot_record pers st rf k cv = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkQuotRecord lf (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_quot_record]
  unfold checkQuotRecord
  lockstep

open Lockstep in
@[lockstep] theorem check_quot_record_ls {pers st lst}
    {rf lf}
    {k : kernel.env.QuotKind} {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers)
      (arena.decl_check.check_quot_record pers st rf k cv) lst
      (checkQuotRecord lf (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) :=
  LS.ofSimRel₀ fun _ h => check_quot_record_refines hrel hinv hfe.rel hfe.inv h

/-- **`check_basis_block` ⊑ `checkBasisBlock`**: a pinned block's records compared
with the pin, and each pin installed at the names its record declares. -/
theorem check_basis_block_refines {pers st lst} {rf lf}
    {kind : kernel.env.BasisKind} {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.decl_check.check_basis_block pers st rf kind block = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkBasisBlock lf (ConRon.Refine.absBasisKind kind) (absICIL block)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.decl_check.check_basis_block]
  unfold checkBasisBlock
  lockstep

open Lockstep in
@[lockstep] theorem check_basis_block_ls {pers st lst}
    {rf lf}
    {kind : kernel.env.BasisKind} {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers)
      (arena.decl_check.check_basis_block pers st rf kind block) lst
      (checkBasisBlock lf (ConRon.Refine.absBasisKind kind) (absICIL block)) :=
  LS.ofSimRel₀ fun _ h => check_basis_block_refines hrel hinv hfe.rel hfe.inv h

/-- `check_ind_decl` ⊑ `checkDecl`'s `.indDecl` arm — the pinned basis blocks
recognised first (a stream's `Nat` block arrives as an ordinary `indDecl`),
then the declared parameter count, the recogniser and the one uniform route
(finding 14). -/
theorem check_ind_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_ind_decl pers st mode rf block n_p = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkIndDeclArmSpec (ConRon.Refine.absMode mode) lf (absICIL block)
        (absU n_p)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_ind_decl, checkIndDeclArmSpec]
  lockstep

/-- **`check_axiom_decl` ⊑ `checkDecl`'s `.axiomDecl` arm**. -/
theorem check_axiom_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_axiom_decl pers st mode rf cv = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkAxiomDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_axiom_decl, checkAxiomDeclSpec]
  lockstep

/-! ## A pinned gate, then the push

The two value arms' tails share one shape: a name list read, membership, the gate
(which hands its environment back), and the record pushed onto whichever
environment came back.  `gate_push_refines` is that shape once. -/

theorem gate_push_refines {pers lst} {rf lf} {ci : arena.env.IConstantInfo}
    {n : arena.handle.NIdx}
    {names : Result (core.result.Result (alloc.vec.Vec arena.handle.NIdx)
      kernel.core_types.CheckError × arena.monad.AState)}
    {namesT : AM (List NIdx)}
    {gate : arena.monad.AState → Result (core.result.Result Unit kernel.core_types.CheckError ×
      arena.monad.AState × arena.env.IFEnv)}
    {gateT : AM IFEnv} {o}
    (hfe : IFEnvRelI pers rf lf)
    (hnames : ∀ o, names = ok o → Sim₀ absNIdxL pers lst o namesT)
    (hgate : ∀ {st1 lst1} o, AStateRel₀ pers st1 lst1 → AStateInv pers st1 →
      gate st1 = ok o → SimEnv pers lst1 o gateT)
    (hrun : (do
      let (r, st1) ← names
      match r with
      | core.result.Result.Ok ns =>
        let b ← arena.checker_base.nidx_contains_from ns 0#usize n
        if b then
          let (r1, st2, fe1) ← gate st1
          match r1 with
          | core.result.Result.Ok _ =>
            let i ← arena.env.ifenv_push fe1 ci
            ok (core.result.Result.Ok i, st2)
          | core.result.Result.Err e => ok (core.result.Result.Err e, st2)
        else
          let i ← arena.env.ifenv_push rf ci
          ok (core.result.Result.Ok i, st1)
      | core.result.Result.Err e => ok (core.result.Result.Err e, st1)) = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o (do
      let fe' ← if (← namesT).contains (absNIdx n) then gateT else pure lf
      pure (fe'.push (absIConstantInfo ci))) := by
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hN := hnames _ h1
  simp only [SimRel₀]
  cases r with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind hN _
  | Ok ns =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hN.apply
    obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hbv := nidx_contains_from_refines hb
    have hb' : b = (absNIdxL ns).contains (absNIdx n) := by
      rw [hbv]; simp [absNIdxLFrom, absNIdxL]
    rw [Lockstep.run_bind_ok hx1]
    simp only [← hb']
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrun ⊢
      obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain rfl := (Result.ok_injective hrun).symm
      exact ⟨_, lst1, rfl, ifenv_push_refines hfe.rel hfe.inv hi, hrel1, hinv1⟩
    | true =>
      simp only [↓reduceIte] at hrun ⊢
      obtain ⟨⟨r1, st2, fe1⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hG := hgate _ hrel1 hinv1 h2
      simp only [SimEnv] at hG
      cases r1 with
      | Err e =>
        obtain rfl := (Result.ok_injective hrun).symm
        show AErrSim e _
        rw [StateT.run_bind]; exact AErrSim.bind hG _
      | Ok u =>
        obtain ⟨lf', lst2, hx2, hfe2, hrel2, hinv2⟩ := hG
        obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain rfl := (Result.ok_injective hrun).symm
        rw [Lockstep.run_bind_ok hx2]
        exact ⟨_, lst2, rfl, ifenv_push_refines hfe2.rel hfe2.inv hi, hrel2, hinv2⟩

/-! ## The structural-`Nat` gate -/

/-- `check_structural_nat_pin_at_fe2` ⊑ `checkStructuralNatPinAtFe2`. -/
theorem check_structural_nat_pin_at_fe2_refines {pers st lst} {rf2 lf2}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf2 lf2) (hfinv : IFEnvInv rf2)
    (hrun : arena.check_decl.check_structural_nat_pin_at_fe2 pers st rf2 n = ok o) :
    Sim₀ absEIdx pers lst o (checkStructuralNatPinAtFe2 lf2 (absNIdx n)) := by
  have hfeI : IFEnvRelI pers rf2 lf2 := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.check_decl.check_structural_nat_pin_at_fe2, checkStructuralNatPinAtFe2_split]
  lockstep

/-- `check_structural_nat_pin_eqs` ⊑ the certification at the environment without
the definition. -/
theorem check_structural_nat_pin_eqs_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {n : arena.handle.NIdx} {value2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_structural_nat_pin_eqs pers st mode rf n value2 = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkStructuralNatPinEqsSpec (ConRon.Refine.absMode mode) lf (absNIdx n)
        (absEIdx value2)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.check_decl.check_structural_nat_pin_eqs]
  unfold checkStructuralNatPinEqsSpec
  lockstep

/-- **`check_structural_nat_pin` ⊑ `checkStructuralNatPin`**: the reads at the
environment with the definition pushed, then the certification at the
environment without it.  `hname`: the caller passes the definition's own name. -/
theorem check_structural_nat_pin_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {ci : arena.env.IConstantInfo} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hname : absNIdx n = (absIConstantInfo ci).name)
    (hrun : arena.check_decl.check_structural_nat_pin pers st mode rf ci n = ok o) :
    SimEnv pers lst o
      (checkStructuralNatPin (ConRon.Refine.absMode mode) lf (absIConstantInfo ci)
        (absNIdx n)) := by
  rw [arena.check_decl.check_structural_nat_pin] at hrun
  obtain ⟨ii, hii, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hdup := i_constant_info_dup_abs hii
  obtain ⟨⟨prev, fe1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hfe1 := (ifenv_push_temp_refines hfeI h1).1
  rw [hdup] at hfe1
  obtain ⟨⟨at2, st1⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS := check_structural_nat_pin_at_fe2_refines hrel hinv hfe1.rel hfe1.inv h2
  obtain ⟨fe2, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hfe2 := ifenv_pop_temp_refines hfeI (by rw [hdup]; exact hname) h1 h3
  rw [hdup] at hfe2
  simp only [SimEnv, checkStructuralNatPin_split]
  cases at2 with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    show AErrSim e _
    rw [StateT.run_bind]; exact AErrSim.bind hS _
  | Ok value2 =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hS.apply
    rw [Lockstep.run_bind_ok hx1]
    obtain ⟨⟨r, st2⟩, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain rfl := (Result.ok_injective hrun).symm
    have hP := check_structural_nat_pin_eqs_refines hrel1 hinv1 hfe2.rel hfe2.inv h4
    cases r with
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]; exact AErrSim.bind hP _
    | Ok u =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hP.apply
      exact ⟨_, lst2, by rw [StateT.run_bind, hx2]; rfl, hfe2, hrel2, hinv2⟩

/-! ## The three value arms

Each checks the value returning the record unpushed, runs its pinned gates
(which push the record for their reads at the environment with it and pop it,
handing the environment back) and pushes last.  The gates pop at the declared
name, so these tails take `hname`: the record's own name, which the value check
returned it at (`check_opaque_val_name`, `check_defn_val_name`). -/

/-- `check_opaque_reduce_pin` — the reduce-operation gate, then the push. -/
theorem check_opaque_reduce_pin_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {ci : arena.env.IConstantInfo}
    {n : arena.handle.NIdx} {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hname : absNIdx n = (absIConstantInfo ci).name)
    (hrun : arena.check_decl.check_opaque_reduce_pin pers st mode rf ci n value = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkOpaqueReducePinSpec (ConRon.Refine.absMode mode) lf (absIConstantInfo ci)
        (absNIdx n) (absEIdx value)) := by
  rw [arena.check_decl.check_opaque_reduce_pin] at hrun
  unfold checkOpaqueReducePinSpec
  exact gate_push_refines (gate := fun s =>
      arena.decl_check.check_reduce_pin pers s mode rf ci n value) ⟨hfe, hfinv⟩
    (fun _ h => reduce_op_names_refines hrel hinv h)
    (fun _ hr hi h => check_reduce_pin_refines hr hi hfe hfinv hname h) hrun

/-- `check_defn_div_mod_pin` — the `Nat.div`/`Nat.mod` gate at a definition, then
the push. -/
theorem check_defn_div_mod_pin_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ci : arena.env.IConstantInfo} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hname : absNIdx n = (absIConstantInfo ci).name)
    (hrun : arena.check_decl.check_defn_div_mod_pin pers st mode pins rf ci n = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkDefnDivModPinSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIConstantInfo ci) (absNIdx n)) := by
  rw [arena.check_decl.check_defn_div_mod_pin] at hrun
  unfold checkDefnDivModPinSpec
  exact gate_push_refines (gate := fun s =>
      arena.decl_check.check_div_mod_pin pers s mode pins rf ci n) ⟨hfe, hfinv⟩
    (fun _ h => nat_div_mod_names_refines hrel hinv h)
    (fun _ hr hi h => check_div_mod_pin_refines hr hi hfe hfinv hname h) hrun

/-- `check_defn_pins` — both pin gates, in the twin's order: the structural gate
hands its environment to the `div`/`mod` gate. -/
theorem check_defn_pins_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ci : arena.env.IConstantInfo} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hname : absNIdx n = (absIConstantInfo ci).name)
    (hrun : arena.check_decl.check_defn_pins pers st mode pins rf ci n = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkDefnPinsSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIConstantInfo ci) (absNIdx n)) := by
  rw [arena.check_decl.check_defn_pins] at hrun
  unfold checkDefnPinsSpec
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hN := nat_op_names_refines hrel hinv h1
  simp only [SimRel₀]
  cases r with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind hN _
  | Ok ns =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hN.apply
    obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hbv := nidx_contains_from_refines hb
    have hb' : b = (absNIdxL ns).contains (absNIdx n) := by
      rw [hbv]; simp [absNIdxLFrom, absNIdxL]
    rw [Lockstep.run_bind_ok hx1]
    simp only [← hb']
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrun ⊢
      exact check_defn_div_mod_pin_refines hrel1 hinv1 hfe hfinv hname hrun
    | true =>
      simp only [↓reduceIte] at hrun ⊢
      obtain ⟨⟨r1, st2, fe1⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hG := check_structural_nat_pin_refines hrel1 hinv1 hfe hfinv hname h2
      simp only [SimEnv] at hG
      cases r1 with
      | Err e =>
        obtain rfl := (Result.ok_injective hrun).symm
        show AErrSim e _
        rw [StateT.run_bind]; exact AErrSim.bind hG _
      | Ok u =>
        obtain ⟨lf', lst2, hx2, hfe2, hrel2, hinv2⟩ := hG
        rw [Lockstep.run_bind_ok hx2]
        exact check_defn_div_mod_pin_refines hrel2 hinv2 hfe2.rel hfe2.inv hname hrun

/-- **`check_opaque_decl` ⊑ `checkDecl`'s `.opaqueDecl` arm**: the constant, the
value, the reduce-operation gate and the push. -/
theorem check_opaque_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_opaque_decl pers st mode rf cv value = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkOpaqueDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  rw [arena.check_decl.check_opaque_decl] at hrun
  unfold checkOpaqueDeclSpec
  simp only [SimRel₀]
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hC := check_constant_val_refines hrel hinv hfe hfinv h1
  cases r with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    show AErrSim e _
    rw [StateT.run_bind]; exact AErrSim.bind hC _
  | Ok u =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hC.apply
    rw [Lockstep.run_bind_ok hx1]
    obtain ⟨⟨r1, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hV := check_opaque_val_refines hrel1 hinv1 hfe hfinv h2
    cases r1 with
    | Err e =>
      obtain rfl := (Result.ok_injective hrun).symm
      show AErrSim e _
      rw [StateT.run_bind]; exact AErrSim.bind hV _
    | Ok ci =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hV.apply
      rw [Lockstep.run_bind_ok hx2]
      have hname : absNIdx cv.name = (absIConstantInfo ci).name :=
        (check_opaque_val_name h2).symm
      exact check_opaque_reduce_pin_refines hrel2 hinv2 hfe hfinv hname hrun

/-- **`check_thm_decl` ⊑ `checkDecl`'s `.thmDecl` arm**: the constant, the theorem's
value, the push. -/
theorem check_thm_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_thm_decl pers st mode rf cv value = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkThmDeclSpec (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  have hfeI : IFEnvRelI pers rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.check_decl.check_thm_decl]
  unfold checkThmDeclSpec
  lockstep

/-- **`check_defn_decl` ⊑ `checkDecl`'s `.defnDecl` arm**: the constant (a
certified operation's name allowed), the value, both pin gates and the push. -/
theorem check_defn_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {cv : arena.env.IConstantVal} {value : arena.handle.EIdx}
    {hint : kernel.env.ReducibilityHint} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_defn_decl pers st mode pins rf cv value hint = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkDefnDeclSpec (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIConstantVal cv) (absEIdx value) (ConRon.Refine.absHint hint)) := by
  rw [arena.check_decl.check_defn_decl] at hrun
  unfold checkDefnDeclSpec
  simp only [SimRel₀]
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hC := check_constant_val_refines hrel hinv hfe hfinv h1
  cases r with
  | Err e =>
    obtain rfl := (Result.ok_injective hrun).symm
    show AErrSim e _
    rw [StateT.run_bind]; exact AErrSim.bind hC _
  | Ok u =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hC.apply
    rw [Lockstep.run_bind_ok hx1]
    obtain ⟨⟨r1, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hV := check_defn_val_refines hrel1 hinv1 hfe hfinv h2
    cases r1 with
    | Err e =>
      obtain rfl := (Result.ok_injective hrun).symm
      show AErrSim e _
      rw [StateT.run_bind]; exact AErrSim.bind hV _
    | Ok ci =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hV.apply
      rw [Lockstep.run_bind_ok hx2]
      have hname : absNIdx cv.name = (absIConstantInfo ci).name :=
        (check_defn_val_name h2).symm
      exact check_defn_pins_refines hrel2 hinv2 hfe hfinv hname hrun

/-! ## One declaration -/

/-- **`check_decl` ⊑ `checkDecl`** — check a single declaration, extending the
environment on success.  Arm for arm; the `.indDecl` arm's route is the
Inductives seam (finding 14). -/
theorem check_decl_refines {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {d : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel pers rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.check_decl.check_decl pers st mode pins rf d = ok o) :
    SimRel₀ (IFEnvRelI pers) pers lst o
      (checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) := by
  cases d with
  | AxiomDecl cv =>
    rw [absIDeclaration, checkDecl_axiomDecl]
    exact check_axiom_decl_refines hrel hinv hfe hfinv hrun
  | DefnDecl cv value hint =>
    rw [absIDeclaration, checkDecl_defnDecl]
    exact check_defn_decl_refines hrel hinv hfe hfinv hrun
  | ThmDecl cv value =>
    rw [absIDeclaration, checkDecl_thmDecl]
    exact check_thm_decl_refines hrel hinv hfe hfinv hrun
  | OpaqueDecl cv value =>
    rw [absIDeclaration, checkDecl_opaqueDecl]
    exact check_opaque_decl_refines hrel hinv hfe hfinv hrun
  | IndDecl block n_p =>
    rw [absIDeclaration, checkDecl_indDecl]
    exact check_ind_decl_refines hrel hinv hfe hfinv hrun
  | QuotDecl k cv =>
    rw [absIDeclaration, checkDecl_quotDecl]
    exact check_quot_record_refines hrel hinv hfe hfinv hrun

open Lockstep in
@[lockstep] theorem check_decl_ls {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {d : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers)
      (arena.check_decl.check_decl pers st mode pins rf d) lst
      (checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf
        (absIDeclaration d)) :=
  LS.ofSimRel₀ fun _ h => check_decl_refines hrel hinv hfe.rel hfe.inv h

/-! ## The error tag and the startup walk -/

/-- `intern_all_names` — the reserved names the guards compare by handle.

Glue since twin fix D5 of task #97-T2-LOCKSTEP made the twin's
`reservedBasisNames` the table read `pinReserved`, as the port's
`reserved_basis_names` is `pin_reserved` (task #97-P6-4a): two table reads
(`reserved_basis_names_refines`, `pin_sorry_ax_refines`,
`pin_quot_sound_refines` — `SimRE`, the state does not move) around three pin
walks (`nat_op_names_refines`, `nat_div_mod_names_refines`,
`reduce_op_names_refines`). -/
theorem intern_all_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_names st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o internAllNamesSpec := by
  rw [arena.checker.intern_all_names] at hrun
  unfold Sim₀
  rw [internAllNamesSpec]
  obtain ⟨r0, hr0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS0 := reserved_basis_names_refines hrel hinv hr0
  cases r0 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    refine AOut₀.err ?_
    rw [am_run_bind']
    exact AErrSim.bind hS0 _
  | Ok a0 =>
  rw [am_run_bind', SimRE.apply hS0, except_ok_bind]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := nat_op_names_refines hrel hinv hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := nat_div_mod_names_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := reduce_op_names_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨r4, hr4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS4 := pin_sorry_ax_refines hrel3 hinv3 hr4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.err (pin_err hS4)
  | Ok a4 =>
  rw [pin_ok hS4]
  obtain ⟨r5, hr5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS5 := pin_quot_sound_refines hrel3 hinv3 hr5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.err (pin_err hS5)
  | Ok a5 =>
  have ho := Result.ok_injective hrun
  subst ho
  refine AOut₀.ok ?_ hrel3 hinv3
  rw [pin_ok hS5]
  rfl

/-- `intern_all_reduce_pins` — the two reduce pins. -/
theorem intern_all_reduce_pins_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_reduce_pins pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllReducePinsSpec := by
  rw [arena.checker.intern_all_reduce_pins] at hrun
  unfold Sim₀
  rw [internAllReducePinsSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := reduce_nat_cv_a_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := reduce_bool_cv_a_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := of_reduce_nat_a_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := of_reduce_bool_a_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r5, st5⟩ := q5
  have hS5 := reduce_nat_decl_pin_refines hrel4 hinv4 hq5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS5
  | Ok u5 =>
  obtain ⟨lst5, hx5, hrel5, hinv5⟩ := Sim₀.apply hS5
  rw [run_bind_ok hx5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r6, st6⟩ := q6
  have hS6 := reduce_bool_decl_pin_refines hrel5 hinv5 hq6
  cases r6 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS6
  | Ok u6 =>
  obtain ⟨lst6, hx6, hrel6, hinv6⟩ := Sim₀.apply hS6
  rw [run_bind_ok hx6]
  have ho := Result.ok_injective hrun
  subst ho
  exact AOut₀.ok rfl hrel6 hinv6

/-- `intern_all_trust_pins` — the compiler-trust axiom pins. -/
theorem intern_all_trust_pins_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_trust_pins pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllTrustPinsSpec := by
  rw [arena.checker.intern_all_trust_pins] at hrun
  unfold Sim₀
  rw [internAllTrustPinsSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := true_cv_a_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := true_intro_cv_a_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := trust_compiler_a_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := bool_cv_a_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  exact intern_all_reduce_pins_refines hrel4 hinv4 hrun

/-- `intern_all_axiom_pins_rest` — the standard axiom pins past the `Iff`
family. -/
theorem intern_all_axiom_pins_rest_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_axiom_pins_rest pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllAxiomPinsRestSpec := by
  rw [arena.checker.intern_all_axiom_pins_rest] at hrun
  unfold Sim₀
  rw [internAllAxiomPinsRestSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := nonempty_intro_a_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := nonempty_rec_a_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := propext_a_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := choice_a_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  exact intern_all_trust_pins_refines hrel4 hinv4 hrun

/-- `intern_all_axiom_pins` — the standard axiom pins. -/
theorem intern_all_axiom_pins_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_axiom_pins pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      internAllAxiomPinsSpec := by
  rw [arena.checker.intern_all_axiom_pins] at hrun
  unfold Sim₀
  rw [internAllAxiomPinsSpec]
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := iff_a_refines hrel0 hinv0 hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := iff_intro_a_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := iff_rec_a_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := nonempty_a_refines hrel3 hinv3 hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  exact intern_all_axiom_pins_rest_refines hrel4 hinv4 hrun

/-- `all_basis_kinds` is the five basis kinds in `internAllPins`' order. -/
theorem all_basis_kinds_refines {o}
    (hrun : arena.checker.all_basis_kinds = ok o) :
    o.val.map ConRon.Refine.absBasisKind =
      [.eqK, .natK, .emptyK, .falseK, .quotK] := by
  rw [arena.checker.all_basis_kinds] at hrun
  obtain ⟨k1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k2, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k3, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨k4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [ConRon.Refine.vec_push_val hrun, ConRon.Refine.vec_push_val h4, ConRon.Refine.vec_push_val h3,
    ConRon.Refine.vec_push_val h2, ConRon.Refine.vec_push_val h1,
    ConRon.Refine.ExprOps.with_capacity_val]
  rfl

/-- The cursor's measure induction behind `intern_all_basis_refines`. -/
private theorem intern_all_basis_aux {pers : arena.store.PersTier} (m : Nat) :
    ∀ {st lst} {i : Std.Usize} {o},
      5 - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st →
      arena.checker.intern_all_basis pers st i = ok o →
      Sim₀ (fun _ : Unit => ()) pers lst o
        (internAllBasisSpec
          ([ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK,
            .quotK].drop i.val)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro st lst i o hm hrel hinv hrun
    rw [arena.checker.intern_all_basis.eq_def] at hrun
    dsimp only at hrun
    obtain ⟨ks, hks, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hk := all_basis_kinds_refines hks
    have hlen5 : ks.val.length = 5 := by
      have h := congrArg List.length hk
      simpa using h
    have hl := alloc.vec.Vec.len_val ks
    unfold Sim₀
    by_cases hge : i ≥ ks.len
    · have hle : 5 ≤ i.val := by scalar_tac
      rw [ite_eq_left hge] at hrun
      have ho := Result.ok_injective hrun
      subst ho
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      exact AOut₀.ok rfl hrel hinv
    · have hlt : i.val < ks.val.length := by scalar_tac
      rw [ite_eq_right hge] at hrun
      obtain ⟨bk, hbk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hlt', rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hbk
      rw [← hk, ← List.map_drop, List.drop_eq_getElem_cons hlt, List.map_cons,
        internAllBasisSpec]
      obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, st1⟩ := q1
      have hS1 := basis_kind_decls_refines hrel hinv hq1
      cases r1 with
      | Err e =>
        have ho := Result.ok_injective hrun
        subst ho
        exact AOut₀.errBind hS1
      | Ok u1 =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS1
      rw [run_bind_ok hx2]
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have hrec := ih (5 - i2.val) (by omega) rfl hrel2 hinv2 hrun
      rw [← hk, ← List.map_drop, hi2v] at hrec
      exact hrec

/-- `intern_all_basis` — the five basis blocks in BOTH forms, at the cursor. -/
theorem intern_all_basis_refines {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker.intern_all_basis pers st i = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (internAllBasisSpec
        ([ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK,
          .quotK].drop i.val)) := by
  exact intern_all_basis_aux _ rfl hrel hinv hrun

/-- **`intern_all_pins` ⊑ the port's startup walk** — DESIGN §8.6 P2d's
one-time tree walk, as the port runs it (task #97-P5-Top): the basis blocks,
the axiom pins, the reserved names and the pin sets, four children in
sequence.  Glue: `intern_all_basis_refines`, `intern_all_axiom_pins_refines`,
`intern_all_names_refines` and `intern_pin_sets_refines`.

Since round 2's ruling (a) the twin interns the raw pins too, so
`internAllPinsPortSpec` is `internAllPins` (`internAllPinsPortSpec_eq`) and
this is the proof route of `intern_all_pins_refines` below. -/
theorem intern_all_pins_port_refines {pers st lst}
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pins.val, NatOpPinSetWF p)
    (hrun : arena.checker.intern_all_pins pers st pins = ok o) :
    Sim₀ absINatOpPinSetL pers lst o
      (internAllPinsPortSpec (ConRon.Refine.absPins pins)) := by
  rw [arena.checker.intern_all_pins] at hrun
  unfold Sim₀
  rw [internAllPinsPortSpec]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := intern_all_basis_refines (i := 0#usize) hrel hinv hq1
  simp only [List.drop_zero, show (0#usize : Std.Usize).val = 0 from rfl] at hS1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := intern_all_axiom_pins_refines hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := intern_all_names_refines hrel2 hinv2 hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  have hS4 := intern_pin_sets_refines (i := 0#usize) hrel3 hinv3 hwf hrun
  have h0 : absINatOpPinSetL (alloc.vec.Vec.new arena.nat_op_pin_set.INatOpPinSet)
      = [] := rfl
  have h1 : (pins.val.drop (0#usize : Std.Usize).val).map ConRon.Refine.absNatOpPinSet
      = ConRon.Refine.absPins pins := by
    simp [ConRon.Refine.absPins]
  simp only [h0, h1, List.nil_append] at hS4
  unfold Sim₀ at hS4
  rw [show (do pure (← internPinSets (ConRon.Refine.absPins pins)) : AM _)
      = internPinSets (ConRon.Refine.absPins pins) from bind_pure _] at hS4
  exact hS4

/-- **The port's startup walk is the twin's**: `internAllPinsPortSpec` — the
four Rust functions' transcriptions in sequence — is `internAllPins`, the flat
`do` block, re-bracketed by the monad laws.  Both intern con-leche's plain
pins (task #119: the raw/annotated pair is gone). -/
theorem internAllPinsPortSpec_eq (ps : List ConLeche.NatOpPinSet) :
    internAllPinsPortSpec ps = internAllPins ps := by
  simp only [internAllPinsPortSpec, internAllBasisSpec, internAllAxiomPinsSpec,
    internAllAxiomPinsRestSpec, internAllTrustPinsSpec, internAllReducePinsSpec,
    internAllNamesSpec, internAllPins, bind_assoc, pure_bind]

/-- **`intern_all_pins` ⊑ `internAllPins`** — what the capstone consumes.

It is `intern_all_pins_port_refines` through `internAllPinsPortSpec_eq`. -/
theorem intern_all_pins_refines {pers st lst}
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pins.val, NatOpPinSetWF p)
    (hrun : arena.checker.intern_all_pins pers st pins = ok o) :
    Sim₀ absINatOpPinSetL pers lst o
      (internAllPins (ConRon.Refine.absPins pins)) := by
  rw [← internAllPinsPortSpec_eq]
  exact intern_all_pins_port_refines hrel hinv hwf hrun

/-! ## The axiom census

**The spine is closed, leaves included** (task #97-MILESTONE, `arena`
`db1131f1`; the whole-list folds it then also covered went with task #105).
The leaves the folds stand on — `install_step_refines` and
`check_pending_refines` — are proved; every row below prints the three
standard axioms and nothing else.  (Until the lane Inductives Install
slice 2 and lane Inductives round 6 slice 2 landings these rows printed
`sorryAx` through the leaves' bodies; the `#guard_msgs` pins keep them from
regressing silently.) -/

/-- info: 'ConRon.Refine2.all_basis_kinds_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all_basis_kinds_refines

end ConRon.Refine2
