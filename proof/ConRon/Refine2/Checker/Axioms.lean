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

## The two that are not one-liners

* `i_constant_val_matches_pin` — exact name, level parameters and type (plain
  equality since con-leche's task #342: there is no binder datum left to
  forgive, so the old `erase_pw_eq` walk is gone).  A comparison of names or
  terms is a HANDLE comparison (DESIGN §8.3: `denoteN`/`denoteE` are
  injective, so index inequality IS structural inequality), which is the one
  place this file leans on exactness.  The Rust is a pure function, the twin a
  `pure`: a Rust-only `LSP` step.
* `basis_pin_hit_go` — con-leche's task-#215 NAME pre-filter in front of
  `canonEqList`, and `find?`'s semantics spelled as a helper (DESIGN §3.4
  forbids the closure): a name match that then fails the canonical comparison
  is `none`, **not** "try the next kind".

## What these lemmas wait on

`Refine2/Promote/Intern.lean`'s four entries, and through them `Specs.lean`'s
`intern_e` family (task #97-P5-1 §8's twenty-four, open when this was
written).  All closed since: nothing here waits any more.
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
    (hrun : (Std.bind m fun c => arena.intern.intern_ci pers st c) = ok o) :
    Sim₀ absIConstantInfo pers lst o (internCI C) := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ha, hw⟩ := hm c hc
  rw [← ha]; exact intern_ci_refines hrel hinv hw h

theorem sim_intern_cv_of {pers st lst} {m : Result kernel.env.ConstantVal}
    {C : ConLeche.ConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ∀ c, m = ok c →
      ConRon.Refine.absConstantVal c = C ∧ ConRon.Refine.ConstantValWF c)
    (hrun : (Std.bind m fun c => arena.intern.intern_cv pers st c) = ok o) :
    Sim₀ absIConstantVal pers lst o (internCV C) := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ha, hw⟩ := hm c hc
  rw [← ha]; exact intern_cv_refines hrel hinv hw h

theorem sim_intern_expr_of {pers st lst} {m : Result kernel.expr.Expr}
    {C : ConLeche.Expr} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ∀ c, m = ok c → ConRon.Refine.absExpr c = C ∧ ConRon.Refine.ExprWF c)
    (hrun : (Std.bind m fun c => arena.intern.intern_expr pers st c) = ok o) :
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
    (hrun : (Std.bind m fun c => arena.intern.intern_ci_list pers st c) = ok o) :
    Sim₀ absICIL pers lst o (internCIList C) := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ha, hw⟩ := hm c hc
  rw [← ha]; exact intern_ci_list_refines hrel hinv hw h

/-! ## `arena::basis` — the pinned blocks -/

/-- `basis_kind_decls` ⊑ `BasisKind.decls` — the RAW constants of one basis block, in dependency order, interned. -/
theorem basis_kind_decls_refines {pers st lst} {k : kernel.env.BasisKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_kind_decls pers st k = ok o) :
    Sim₀ absICIL pers lst o
      (BasisKind.decls (ConRon.Refine.absBasisKind k)) := by
  rw [arena.basis.basis_kind_decls] at hrun
  exact sim_intern_ci_list_of hrel hinv (fun _ h => ConRon.Refine.BasisRaw.basis_kind_decls_refines h) hrun

open Lockstep in
@[lockstep] theorem basis_kind_decls_ls {pers st lst}
    {k : kernel.env.BasisKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a)
      (arena.basis.basis_kind_decls pers st k) lst
      (BasisKind.decls (ConRon.Refine.absBasisKind k)) :=
  LS.ofSim₀ fun _ h => basis_kind_decls_refines hrel hinv h

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

theorem block_names_aux (k : Nat) :
    ∀ (block : alloc.vec.Vec arena.env.IConstantInfo) (i : Std.Usize)
      (out : alloc.vec.Vec arena.handle.NIdx) {o},
      block.val.length - i.val = k →
      arena.basis.block_names block i out = ok o →
      absNIdxL o = absNIdxL out ++ blockNames (absICILFrom block i) := by
  induction k with
  | zero =>
    intro block i out o hn h
    rw [arena.basis.block_names] at h
    have hl := alloc.vec.Vec.len_val block
    rw [ite_eq_left (by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    have : absICILFrom block i = [] := by
      simp only [absICILFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [this]; simp [blockNames]
  | succ m ih =>
    intro block i out o hn h
    rw [arena.basis.block_names] at h
    have hl := alloc.vec.Vec.len_val block
    rw [ite_eq_right (by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi : i.val < block.val.length := by omega
    have hx : block.val[i.val] = ii := by
      have h1 := vec_index_some hii
      rw [List.getElem?_eq_getElem hi] at h1
      exact Option.some_inj.mp h1
    have hi2v := ConRon.Refine.Nat.uadd_val hi2
    have h3 := ih block i2 out1 (by simp at hi2v; omega) h
    have hcons : absICILFrom block i = absIConstantInfo ii :: absICILFrom block i2 := by
      simp only [absICILFrom]; rw [List.drop_eq_getElem_cons hi, hx]
      simp at hi2v; rw [hi2v]; rfl
    rw [h3, hcons, absNIdxL, absNIdxL, ConRon.Refine.vec_push_val hout1]
    simp [blockNames, i_constant_info_name_abs hn2]

/-- `block_names` ⊑ `blockNames` at the cursor — `IConstantInfo.name` is pure (task #97e), so the twin is a plain `List.map`. -/
theorem block_names_refines  {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.basis.block_names block i out = ok o) :
    absNIdxL o = absNIdxL out ++ blockNames (absICILFrom block i) :=
  block_names_aux _ block i out rfl hrun

open Lockstep in
/-- `block_names` from its entry. -/
@[lockstep] theorem block_names_spec (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LSP (arena.basis.block_names block 0#usize (alloc.vec.Vec.new arena.handle.NIdx))
      (fun o => o.val.map absNIdx = blockNames (absICIL block)) := by
  intro o h
  have := block_names_refines h
  simpa [absNIdxL, absICILFrom, absICIL] using this

open Lockstep in
/-- `arena::canon::nidx_vec_beq` from the start is the twin's `==` on the two
handle lists. -/
@[lockstep] theorem nidx_vec_beq_spec (a b : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.canon.nidx_vec_beq a b 0#usize)
      (fun o => o = (a.val.map absNIdx == b.val.map absNIdx)) := by
  intro o h
  rw [nidx_vec_beq_refines h]
  have e : ∀ v : alloc.vec.Vec arena.handle.NIdx, absNIdxLFrom v 0#usize = v.val.map absNIdx := by
    intro v; simp [absNIdxLFrom]
  rw [e, e]
  cases h' : decide (a.val.map absNIdx = b.val.map absNIdx) <;> simp_all

open Lockstep in
theorem basis_pin_hit_go_aux (k : Nat) :
    ∀ {pers st lst} (block : alloc.vec.Vec arena.env.IConstantInfo)
      (ks : alloc.vec.Vec kernel.env.BasisKind) (i : Std.Usize),
      ks.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (Option.map ConRon.Refine.absBasisKind) a)
        (arena.basis.basis_pin_hit_go pers st block ks i) lst
        (basisPinHitGo (absICIL block) (absBasisKindLFrom ks i)) := by
  induction k with
  | zero =>
    intro pers st lst block ks i hn hrel hinv
    have hl := alloc.vec.Vec.len_val ks
    have : absBasisKindLFrom ks i = [] := by
      simp only [absBasisKindLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [arena.basis.basis_pin_hit_go, this, basisPinHitGo, ite_eq_left (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ m ih =>
    intro pers st lst block ks i hn hrel hinv
    have hl := alloc.vec.Vec.len_val ks
    have hi : i.val < ks.val.length := by omega
    have hcons : absBasisKindLFrom ks i = ConRon.Refine.absBasisKind ks.val[i.val] ::
        (ks.val.drop (i.val + 1)).map ConRon.Refine.absBasisKind := by
      simp only [absBasisKindLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl
    rw [arena.basis.basis_pin_hit_go, hcons, basisPinHitGo, ite_eq_right (by scalar_tac)]
    have hcanon : ∀ {st lst} (xs ys : alloc.vec.Vec arena.env.IConstantInfo),
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = id a) (arena.canon.canon_eq_list pers st xs ys 0#usize) lst
          (canonEqList (absICIL xs) (absICIL ys)) := by
      intro st lst xs ys hrel hinv
      refine LS.ofSim₀ fun _ h => ?_
      have := canon_eq_list_refines hrel hinv h
      simpa [absICILFrom, absICIL] using this
    simp only [absBasisKindLFrom] at ih
    lockstep

/-- `basis_pin_hit` ⊑ `basisPinHit` — the four pinned inductive blocks, in con-leche's order; `.quotK` is deliberately not among them. -/
theorem basis_pin_hit_refines {pers st lst} {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_pin_hit pers st block = ok o) :
    Sim₀ (Option.map ConRon.Refine.absBasisKind) pers lst o
      (basisPinHit (absICIL block)) := by
  rw [arena.basis.basis_pin_hit] at hrun
  obtain ⟨ks, hks, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hk := ConRon.Refine.BasisRaw.block_pin_kinds_refines hks
  have h := Lockstep.LS.toSim₀ (basis_pin_hit_go_aux _ block ks 0#usize rfl hrel hinv) hrun
  have e : absBasisKindLFrom ks 0#usize =
      [ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK] := by
    simp only [absBasisKindLFrom]; rw [← hk]; rfl
  rw [e] at h
  exact h

open Lockstep in
@[lockstep] theorem quot_kind_slot_spec (k : kernel.env.QuotKind) :
    LSP (kernel.env.quot_kind_slot k) (fun i => i.val = (ConRon.Refine.absQuotKind k).slot) :=
  fun _ h => ConRon.Refine.BasisRaw.quot_kind_slot_refines h

theorem quotPinHit_split (k : ConLeche.QuotKind) (cv : ConRon.Arena.IConstantVal) :
    quotPinHit k cv = (do
      let blk ← ConRon.Arena.BasisKind.decls .quotK
      if h : k.slot < blk.length then cv.canonEq blk[k.slot].toConstantVal
      else pure false) := by
  unfold quotPinHit
  congr 1; funext blk
  by_cases h : k.slot < blk.length
  · rw [dite_eq_left h, List.getElem?_eq_getElem h]
  · rw [dite_eq_right h, List.getElem?_eq_none (by omega)]

-- the twin's bound `dite` is split although no branch is ruled out at once
-- (the bounds contradiction needs `len_val`, below)
set_option lockstep.twinSplit true in
/-- `quot_pin_hit` ⊑ `quotPinHit` — the record is the pinned package's constant at the slot it declares itself at, compared at `toConstantVal`. -/
theorem quot_pin_hit_refines {pers st lst} {k : kernel.env.QuotKind} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.quot_pin_hit pers st k cv = ok o) :
    Sim₀ id pers lst o
      (quotPinHit (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  have hcanon : ∀ {st lst} (cv cv2 : arena.env.IConstantVal),
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a) (arena.canon.i_constant_val_canon_eq pers st cv cv2) lst
        ((absIConstantVal cv).canonEq (absIConstantVal cv2)) :=
    fun cv cv2 hrel hinv => Lockstep.LS.ofSim₀ fun _ h => i_constant_val_canon_eq_refines hrel hinv h
  rw [arena.basis.quot_pin_hit, quotPinHit_split]
  lockstep
  -- the shared tactic splits the twin's bound `dite` (`lockstep.twinSplit`,
  -- task #97-T2-TACTIC round 2); what is left is the bounds contradiction and the index read
  all_goals first
    | (exfalso
       have := alloc.vec.Vec.len_val ‹alloc.vec.Vec arena.env.IConstantInfo›
       simp only [absICIL, List.length_map] at *; scalar_tac)
    | (generalize hblk : ‹alloc.vec.Vec arena.env.IConstantInfo› = blk at *
       generalize hix : ‹Std.Usize› = ix at *
       have hl := alloc.vec.Vec.len_val blk
       have hia : ix.val = (ConRon.Refine.absQuotKind k).slot := by
         obtain h | h := ‹_ ∨ Usize.max < _› <;> scalar_tac
       have e : (absICIL blk)[(ConRon.Refine.absQuotKind k).slot]'(by
           simp only [absICIL, List.length_map]; omega) =
           absIConstantInfo (↑blk : List _)[ix.val] := by
         simp only [absICIL, List.getElem_map]; congr 1; simp [hia]
       rw [e, show (absIConstantInfo (↑blk : List _)[ix.val]).toConstantVal = _ from
         ‹Lockstep.TwinEq _ _›]
       exact hcanon _ _ ‹_› ‹_›)

open Lockstep in
@[lockstep] theorem quot_pin_hit_ls {pers st lst}
    {k : kernel.env.QuotKind}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.basis.quot_pin_hit pers st k cv) lst
      (quotPinHit (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => quot_pin_hit_refines hrel hinv h

/-- `propext_name` ⊑ `propextName`, off the pin table. -/
theorem propext_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.propext_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (propextName) := by
  rw [arena.std_axioms.propext_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_propext_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem propext_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.propext_name st) lst
      (propextName) :=
  LS.ofSim₀ fun _ h => propext_name_refines hrel hinv h

/-- `choice_name` ⊑ `choiceName`, off the pin table. -/
theorem choice_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.choice_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (choiceName) := by
  rw [arena.std_axioms.choice_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_choice_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem choice_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.choice_name st) lst
      (choiceName) :=
  LS.ofSim₀ fun _ h => choice_name_refines hrel hinv h

/-- `iff_name` ⊑ `iffName`, off the pin table. -/
theorem iff_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (iffName) := by
  rw [arena.std_axioms.iff_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_iff_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem iff_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.iff_name st) lst
      (iffName) :=
  LS.ofSim₀ fun _ h => iff_name_refines hrel hinv h

/-- `iff_intro_name` ⊑ `iffIntroName`, off the pin table. -/
theorem iff_intro_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_intro_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (iffIntroName) := by
  rw [arena.std_axioms.iff_intro_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_iff_intro_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem iff_intro_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.iff_intro_name st) lst
      (iffIntroName) :=
  LS.ofSim₀ fun _ h => iff_intro_name_refines hrel hinv h

/-- `iff_rec_name` ⊑ `iffRecName`, off the pin table. -/
theorem iff_rec_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_rec_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (iffRecName) := by
  rw [arena.std_axioms.iff_rec_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_iff_rec_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem iff_rec_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.iff_rec_name st) lst
      (iffRecName) :=
  LS.ofSim₀ fun _ h => iff_rec_name_refines hrel hinv h

/-- `nonempty_name` ⊑ `nonemptyName`, off the pin table. -/
theorem nonempty_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (nonemptyName) := by
  rw [arena.std_axioms.nonempty_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_nonempty_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem nonempty_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.nonempty_name st) lst
      (nonemptyName) :=
  LS.ofSim₀ fun _ h => nonempty_name_refines hrel hinv h

/-- `nonempty_intro_name` ⊑ `nonemptyIntroName`, off the pin table. -/
theorem nonempty_intro_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_intro_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (nonemptyIntroName) := by
  rw [arena.std_axioms.nonempty_intro_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_nonempty_intro_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem nonempty_intro_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.nonempty_intro_name st) lst
      (nonemptyIntroName) :=
  LS.ofSim₀ fun _ h => nonempty_intro_name_refines hrel hinv h

/-- `nonempty_rec_name` ⊑ `nonemptyRecName`, off the pin table. -/
theorem nonempty_rec_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_rec_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (nonemptyRecName) := by
  rw [arena.std_axioms.nonempty_rec_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_nonempty_rec_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem nonempty_rec_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.std_axioms.nonempty_rec_name st) lst
      (nonemptyRecName) :=
  LS.ofSim₀ fun _ h => nonempty_rec_name_refines hrel hinv h

/-! ### `i_constant_val_matches_pin` -/

open Lockstep in
/-- `i_constant_val_matches_pin` ⊑ `IConstantVal.matchesPin` — exact name,
level parameters and type, compared as handles.  The Rust is a pure function
of its two records and the twin a `pure` (`IConstantVal.matchesPin_eq`), so the
statement is a Rust-only `LSP` step whose answer is the twin's value. -/
@[lockstep] theorem i_constant_val_matches_pin_spec
    (cv pin : arena.env.IConstantVal) :
    LSP (arena.std_axioms.i_constant_val_matches_pin cv pin)
      (fun a => a = ((absIConstantVal cv).name == (absIConstantVal pin).name &&
        (absIConstantVal cv).levelParams == (absIConstantVal pin).levelParams &&
        (absIConstantVal cv).type == (absIConstantVal pin).type)) := by
  intro a ha
  rw [arena.std_axioms.i_constant_val_matches_pin] at ha
  obtain ⟨b, hb, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
  have hb' := nidx_eq2_abs hb
  subst hb'
  simp only [absIConstantVal]
  cases hn : (absNIdx cv.name == absNIdx pin.name)
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at ha
    cases Result.ok_injective ha
    simp
  · simp only [hn, ↓reduceIte] at ha
    obtain ⟨b1, hb1, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
    have hb1' := nidx_vec_beq_spec _ _ b1 hb1
    subst hb1'
    cases hl : (cv.level_params.val.map absNIdx == pin.level_params.val.map absNIdx)
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at ha
      cases Result.ok_injective ha
      simp
    · simp only [hl, ↓reduceIte] at ha
      have ht := eidx_eq2_abs ha
      subst ht
      simp

/-- `iff_a` ⊑ `iffA` — the con-leche pin, interned. -/
theorem iff_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffA) := by
  rw [arena.std_axioms.iff_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_a_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.iff_a pers st) lst
      (iffA) :=
  LS.ofSim₀ fun _ h => iff_a_refines hrel hinv h

/-- `iff_intro_a` ⊑ `iffIntroA` — the con-leche pin, interned. -/
theorem iff_intro_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_intro_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffIntroA) := by
  rw [arena.std_axioms.iff_intro_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_intro_a_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_intro_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.iff_intro_a pers st) lst
      (iffIntroA) :=
  LS.ofSim₀ fun _ h => iff_intro_a_refines hrel hinv h

/-- `iff_rec_a` ⊑ `iffRecA` — the con-leche pin, interned. -/
theorem iff_rec_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_rec_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffRecA) := by
  rw [arena.std_axioms.iff_rec_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_rec_a_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_rec_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.iff_rec_a pers st) lst
      (iffRecA) :=
  LS.ofSim₀ fun _ h => iff_rec_a_refines hrel hinv h

/-- `propext_a` ⊑ `propextA` — the con-leche pin, interned. -/
theorem propext_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.propext_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (propextA) := by
  rw [arena.std_axioms.propext_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.propext_a_refines h) hrun

open Lockstep in
@[lockstep] theorem propext_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.std_axioms.propext_a pers st) lst
      (propextA) :=
  LS.ofSim₀ fun _ h => propext_a_refines hrel hinv h

/-- `nonempty_a` ⊑ `nonemptyA` — the con-leche pin, interned. -/
theorem nonempty_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyA) := by
  rw [arena.std_axioms.nonempty_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_a_refines h) hrun

open Lockstep in
@[lockstep] theorem nonempty_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.nonempty_a pers st) lst
      (nonemptyA) :=
  LS.ofSim₀ fun _ h => nonempty_a_refines hrel hinv h

/-- `nonempty_intro_a` ⊑ `nonemptyIntroA` — the con-leche pin, interned. -/
theorem nonempty_intro_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_intro_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyIntroA) := by
  rw [arena.std_axioms.nonempty_intro_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_intro_a_refines h) hrun

open Lockstep in
@[lockstep] theorem nonempty_intro_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.nonempty_intro_a pers st) lst
      (nonemptyIntroA) :=
  LS.ofSim₀ fun _ h => nonempty_intro_a_refines hrel hinv h

/-- `nonempty_rec_a` ⊑ `nonemptyRecA` — the con-leche pin, interned. -/
theorem nonempty_rec_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_rec_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyRecA) := by
  rw [arena.std_axioms.nonempty_rec_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_rec_a_refines h) hrun

open Lockstep in
@[lockstep] theorem nonempty_rec_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.nonempty_rec_a pers st) lst
      (nonemptyRecA) :=
  LS.ofSim₀ fun _ h => nonempty_rec_a_refines hrel hinv h

/-- `choice_a` ⊑ `choiceA` — the con-leche pin, interned. -/
theorem choice_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.choice_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (choiceA) := by
  rw [arena.std_axioms.choice_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.choice_a_refines h) hrun

open Lockstep in
@[lockstep] theorem choice_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.std_axioms.choice_a pers st) lst
      (choiceA) :=
  LS.ofSim₀ fun _ h => choice_a_refines hrel hinv h

/-- `eq_a` ⊑ `eqA` — the con-leche constant, interned. -/
theorem eq_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.eq_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (eqA) := by
  rw [arena.std_axioms.eq_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.BasisPins.eq_a_refines h) hrun

open Lockstep in
@[lockstep] theorem eq_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.eq_a pers st) lst
      (eqA) :=
  LS.ofSim₀ fun _ h => eq_a_refines hrel hinv h

/-- `nat_a` ⊑ `natA` — the con-leche constant, interned. -/
theorem nat_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nat_a pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (natA) := by
  rw [arena.std_axioms.nat_a] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.BasisPins.nat_a_refines h) hrun

open Lockstep in
@[lockstep] theorem nat_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.nat_a pers st) lst
      (natA) :=
  LS.ofSim₀ fun _ h => nat_a_refines hrel hinv h

/-- `true_name` ⊑ `trueName`, off the pin table. -/
theorem true_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (trueName) := by
  rw [arena.trust_axioms.true_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_true_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem true_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.true_name st) lst
      (trueName) :=
  LS.ofSim₀ fun _ h => true_name_refines hrel hinv h

/-- `true_intro_name` ⊑ `trueIntroName`, off the pin table. -/
theorem true_intro_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_intro_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (trueIntroName) := by
  rw [arena.trust_axioms.true_intro_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_true_intro_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem true_intro_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.true_intro_name st) lst
      (trueIntroName) :=
  LS.ofSim₀ fun _ h => true_intro_name_refines hrel hinv h

/-- `trust_compiler_name` ⊑ `trustCompilerName`, off the pin table. -/
theorem trust_compiler_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.trust_compiler_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (trustCompilerName) := by
  rw [arena.trust_axioms.trust_compiler_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_trust_compiler_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem trust_compiler_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.trust_compiler_name st) lst
      (trustCompilerName) :=
  LS.ofSim₀ fun _ h => trust_compiler_name_refines hrel hinv h

/-- `reduce_nat_name` ⊑ `reduceNatName`, off the pin table. -/
theorem reduce_nat_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_nat_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (reduceNatName) := by
  rw [arena.trust_axioms.reduce_nat_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_reduce_nat_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem reduce_nat_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.reduce_nat_name st) lst
      (reduceNatName) :=
  LS.ofSim₀ fun _ h => reduce_nat_name_refines hrel hinv h

/-- `reduce_bool_name` ⊑ `reduceBoolName`, off the pin table. -/
theorem reduce_bool_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_bool_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (reduceBoolName) := by
  rw [arena.trust_axioms.reduce_bool_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_reduce_bool_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem reduce_bool_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.reduce_bool_name st) lst
      (reduceBoolName) :=
  LS.ofSim₀ fun _ h => reduce_bool_name_refines hrel hinv h

/-- `of_reduce_nat_name` ⊑ `ofReduceNatName`, off the pin table. -/
theorem of_reduce_nat_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_nat_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (ofReduceNatName) := by
  rw [arena.trust_axioms.of_reduce_nat_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_of_reduce_nat_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem of_reduce_nat_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.of_reduce_nat_name st) lst
      (ofReduceNatName) :=
  LS.ofSim₀ fun _ h => of_reduce_nat_name_refines hrel hinv h

/-- `of_reduce_bool_name` ⊑ `ofReduceBoolName`, off the pin table. -/
theorem of_reduce_bool_name_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_bool_name st = ok o) :
    Sim₀ absNIdx pers lst o
      (ofReduceBoolName) := by
  rw [arena.trust_axioms.of_reduce_bool_name] at hrun
  exact name_read_sim hrel hinv (fun _ h => pin_of_reduce_bool_refines hrel hinv h) hrun

open Lockstep in
@[lockstep] theorem of_reduce_bool_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.of_reduce_bool_name st) lst
      (ofReduceBoolName) :=
  LS.ofSim₀ fun _ h => of_reduce_bool_name_refines hrel hinv h

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
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.trust_axioms.of_reduce_op]
  try unfold ofReduceOp
  lockstep

open Lockstep in
@[lockstep] theorem of_reduce_op_ls {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.of_reduce_op st n) lst
      (ofReduceOp (absNIdx n)) :=
  LS.ofSim₀ fun _ h => of_reduce_op_refines hrel hinv h

/-- `true_cv_a` ⊑ `trueCvA`. -/
theorem true_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (trueCvA) := by
  rw [arena.trust_axioms.true_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.true_cv_a_refines h) hrun

open Lockstep in
@[lockstep] theorem true_cv_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.true_cv_a pers st) lst
      (trueCvA) :=
  LS.ofSim₀ fun _ h => true_cv_a_refines hrel hinv h

/-- `true_intro_cv_a` ⊑ `trueIntroCvA`. -/
theorem true_intro_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.true_intro_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (trueIntroCvA) := by
  rw [arena.trust_axioms.true_intro_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.true_intro_cv_a_refines h) hrun

open Lockstep in
@[lockstep] theorem true_intro_cv_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.true_intro_cv_a pers st) lst
      (trueIntroCvA) :=
  LS.ofSim₀ fun _ h => true_intro_cv_a_refines hrel hinv h

/-- `trust_compiler_a` ⊑ `trustCompilerA`. -/
theorem trust_compiler_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.trust_compiler_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (trustCompilerA) := by
  rw [arena.trust_axioms.trust_compiler_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.trust_compiler_a_refines h) hrun

open Lockstep in
@[lockstep] theorem trust_compiler_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.trust_compiler_a pers st) lst
      (trustCompilerA) :=
  LS.ofSim₀ fun _ h => trust_compiler_a_refines hrel hinv h

/-- `bool_cv_a` ⊑ `boolCvA`. -/
theorem bool_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.bool_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (boolCvA) := by
  rw [arena.trust_axioms.bool_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.bool_cv_a_refines h) hrun

open Lockstep in
@[lockstep] theorem bool_cv_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.bool_cv_a pers st) lst
      (boolCvA) :=
  LS.ofSim₀ fun _ h => bool_cv_a_refines hrel hinv h

/-- `reduce_elem_name` ⊑ `reduceElemName`. -/
theorem reduce_elem_name_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_elem_name st c = ok o) :
    Sim₀ absNIdx pers lst o
      (reduceElemName (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.trust_axioms.reduce_elem_name]
  try unfold reduceElemName
  lockstep

open Lockstep in
@[lockstep] theorem reduce_elem_name_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.trust_axioms.reduce_elem_name st c) lst
      (reduceElemName (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_elem_name_refines hrel hinv h

/-- `reduce_elem_ty` ⊑ `reduceElemTy`. -/
theorem reduce_elem_ty_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_elem_ty pers st c = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceElemTy (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.trust_axioms.reduce_elem_ty]
  try unfold reduceElemTy
  lockstep

open Lockstep in
@[lockstep] theorem reduce_elem_ty_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.trust_axioms.reduce_elem_ty pers st c) lst
      (reduceElemTy (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_elem_ty_refines hrel hinv h

/-- `reduce_nat_cv_a` ⊑ `reduceNatCvA` — the con-leche pin, interned (a plain value since
task #119: no raw/annotated pair). -/
theorem reduce_nat_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_nat_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceNatCvA) := by
  rw [arena.trust_axioms.reduce_nat_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.reduce_nat_cv_a_refines h) hrun

open Lockstep in
@[lockstep] theorem reduce_nat_cv_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.reduce_nat_cv_a pers st) lst
      (reduceNatCvA) :=
  LS.ofSim₀ fun _ h => reduce_nat_cv_a_refines hrel hinv h

/-- `reduce_bool_cv_a` ⊑ `reduceBoolCvA` — the con-leche pin, interned (a plain value since
task #119: no raw/annotated pair). -/
theorem reduce_bool_cv_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_bool_cv_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceBoolCvA) := by
  rw [arena.trust_axioms.reduce_bool_cv_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.reduce_bool_cv_a_refines h) hrun

open Lockstep in
@[lockstep] theorem reduce_bool_cv_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.reduce_bool_cv_a pers st) lst
      (reduceBoolCvA) :=
  LS.ofSim₀ fun _ h => reduce_bool_cv_a_refines hrel hinv h

/-- `of_reduce_nat_a` ⊑ `ofReduceNatA` — the con-leche pin, interned (a plain value since
task #119: no raw/annotated pair). -/
theorem of_reduce_nat_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_nat_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReduceNatA) := by
  rw [arena.trust_axioms.of_reduce_nat_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.of_reduce_nat_a_refines h) hrun

open Lockstep in
@[lockstep] theorem of_reduce_nat_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.of_reduce_nat_a pers st) lst
      (ofReduceNatA) :=
  LS.ofSim₀ fun _ h => of_reduce_nat_a_refines hrel hinv h

/-- `of_reduce_bool_a` ⊑ `ofReduceBoolA` — the con-leche pin, interned (a plain value since
task #119: no raw/annotated pair). -/
theorem of_reduce_bool_a_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_bool_a pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReduceBoolA) := by
  rw [arena.trust_axioms.of_reduce_bool_a] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.of_reduce_bool_a_refines h) hrun

open Lockstep in
@[lockstep] theorem of_reduce_bool_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.of_reduce_bool_a pers st) lst
      (ofReduceBoolA) :=
  LS.ofSim₀ fun _ h => of_reduce_bool_a_refines hrel hinv h

/-- `reduce_op_cv_a` ⊑ `reduceOpCvA`. -/
theorem reduce_op_cv_a_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_op_cv_a pers st c = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceOpCvA (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.trust_axioms.reduce_op_cv_a]
  try unfold reduceOpCvA
  lockstep

open Lockstep in
@[lockstep] theorem reduce_op_cv_a_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.reduce_op_cv_a pers st c) lst
      (reduceOpCvA (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_op_cv_a_refines hrel hinv h

/-- `of_reduce_pin_a` ⊑ `ofReducePinA`. -/
theorem of_reduce_pin_a_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_pin_a pers st n = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReducePinA (absNIdx n)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.trust_axioms.of_reduce_pin_a]
  try unfold ofReducePinA
  lockstep

open Lockstep in
@[lockstep] theorem of_reduce_pin_a_ls {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.of_reduce_pin_a pers st n) lst
      (ofReducePinA (absNIdx n)) :=
  LS.ofSim₀ fun _ h => of_reduce_pin_a_refines hrel hinv h

/-- `reduce_bool_decl_pin` ⊑ `reduceBoolDeclPin`. -/
theorem reduce_bool_decl_pin_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_bool_decl_pin pers st = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceBoolDeclPin) := by
  rw [arena.trust_axioms.reduce_bool_decl_pin] at hrun
  exact sim_intern_expr_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.reduce_bool_decl_pin_refines h) hrun

open Lockstep in
@[lockstep] theorem reduce_bool_decl_pin_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.trust_axioms.reduce_bool_decl_pin pers st) lst
      (reduceBoolDeclPin) :=
  LS.ofSim₀ fun _ h => reduce_bool_decl_pin_refines hrel hinv h

/-- `reduce_nat_decl_pin` ⊑ `reduceNatDeclPin`. -/
theorem reduce_nat_decl_pin_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_nat_decl_pin pers st = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceNatDeclPin) := by
  rw [arena.trust_axioms.reduce_nat_decl_pin] at hrun
  exact sim_intern_expr_of hrel hinv (fun _ h => ConRon.Refine.TrustAxioms.reduce_nat_decl_pin_refines h) hrun

open Lockstep in
@[lockstep] theorem reduce_nat_decl_pin_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.trust_axioms.reduce_nat_decl_pin pers st) lst
      (reduceNatDeclPin) :=
  LS.ofSim₀ fun _ h => reduce_nat_decl_pin_refines hrel hinv h

/-- `reduce_decl_pin` ⊑ `reduceDeclPin`. -/
theorem reduce_decl_pin_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_decl_pin pers st c = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceDeclPin (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.trust_axioms.reduce_decl_pin]
  try unfold reduceDeclPin
  lockstep

open Lockstep in
@[lockstep] theorem reduce_decl_pin_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.trust_axioms.reduce_decl_pin pers st c) lst
      (reduceDeclPin (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_decl_pin_refines hrel hinv h

/-- `reduce_cert_var` ⊑ `reduceCertVar`. -/
theorem reduce_cert_var_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_cert_var pers st c = ok o) :
    Sim₀ absEIdx pers lst o
      (reduceCertVar (absNIdx c)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.trust_axioms.reduce_cert_var]
  try unfold reduceCertVar
  lockstep

open Lockstep in
@[lockstep] theorem reduce_cert_var_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.trust_axioms.reduce_cert_var pers st c) lst
      (reduceCertVar (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_cert_var_refines hrel hinv h

end ConRon.Refine2
