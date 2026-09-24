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
  rw [erasePwEq]
  congr 1

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

open Lockstep in
@[lockstep] theorem basis_kind_decls_a_ls {pers st lst}
    {k : kernel.env.BasisKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a)
      (arena.basis.basis_kind_decls_a pers st k) lst
      (BasisKind.declsA (ConRon.Refine.absBasisKind k)) :=
  LS.ofSim₀ fun _ h => basis_kind_decls_a_refines hrel hinv h

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
    rw [if_pos (by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    have : absICILFrom block i = [] := by
      simp only [absICILFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [this]; simp [blockNames]
  | succ m ih =>
    intro block i out o hn h
    rw [arena.basis.block_names] at h
    have hl := alloc.vec.Vec.len_val block
    rw [if_neg (by scalar_tac)] at h
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
    rw [arena.basis.basis_pin_hit_go, this, basisPinHitGo, if_pos (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ m ih =>
    intro pers st lst block ks i hn hrel hinv
    have hl := alloc.vec.Vec.len_val ks
    have hi : i.val < ks.val.length := by omega
    have hcons : absBasisKindLFrom ks i = ConRon.Refine.absBasisKind ks.val[i.val] ::
        (ks.val.drop (i.val + 1)).map ConRon.Refine.absBasisKind := by
      simp only [absBasisKindLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl
    rw [arena.basis.basis_pin_hit_go, hcons, basisPinHitGo, if_neg (by scalar_tac)]
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

/-- `basis_pin_hit_go` ⊑ `basisPinHitGo` at the cursor — con-leche's task-#215 NAME pre-filter in front of the canonical comparison. -/
theorem basis_pin_hit_go_refines {pers st lst} {block : alloc.vec.Vec arena.env.IConstantInfo} {ks : alloc.vec.Vec kernel.env.BasisKind} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_pin_hit_go pers st block ks i = ok o) :
    Sim₀ (Option.map ConRon.Refine.absBasisKind) pers lst o
      (basisPinHitGo (absICIL block) (absBasisKindLFrom ks i)) :=
  Lockstep.LS.toSim₀ (basis_pin_hit_go_aux _ block ks i rfl hrel hinv) hrun

open Lockstep in
@[lockstep] theorem basis_pin_hit_go_ls {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {ks : alloc.vec.Vec kernel.env.BasisKind}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map ConRon.Refine.absBasisKind) a)
      (arena.basis.basis_pin_hit_go pers st block ks i) lst
      (basisPinHitGo (absICIL block) (absBasisKindLFrom ks i)) :=
  LS.ofSim₀ fun _ h => basis_pin_hit_go_refines hrel hinv h

/-- `basis_pin_hit` ⊑ `basisPinHit` — the five pinned blocks, in con-leche's order; `.quotK` is deliberately not among them. -/
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
      [ConLeche.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK] := by
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
      if h : k.slot < blk.length then do
        let pcv ← blk[k.slot].toConstantVal
        cv.canonEq pcv
      else pure false) := by
  unfold quotPinHit
  congr 1; funext blk
  by_cases h : k.slot < blk.length
  · rw [dif_pos h, List.getElem?_eq_getElem h]
  · rw [dif_neg h, List.getElem?_eq_none (by omega)]

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
  -- the shared tactic decides the twin's bound `dite` itself (task #97-T2-TACTIC
  -- round 2); what is left is the bounds contradiction and the index read
  all_goals first
    | (exfalso
       have := alloc.vec.Vec.len_val ‹alloc.vec.Vec arena.env.IConstantInfo›
       simp only [absICIL, List.length_map] at *; scalar_tac)
    | (generalize hblk : ‹alloc.vec.Vec arena.env.IConstantInfo› = blk at *
       have hl := alloc.vec.Vec.len_val blk
       have hia : a.val = (ConRon.Refine.absQuotKind k).slot := by
         obtain h | h := ‹_ ∨ Usize.max < _› <;> scalar_tac
       have e : (absICIL blk)[(ConRon.Refine.absQuotKind k).slot]'(by
           simp only [absICIL, List.length_map]; omega) =
           absIConstantInfo (↑blk : List _)[a.val] := by
         simp only [absICIL, List.getElem_map]; congr 1; simp [hia]
       rw [e]
       refine Lockstep.LSS.bind (Lockstep.i_constant_info_to_constant_val_lss ‹_› ‹_› _) ?_
         (fun e s' => Lockstep.errArm_ok) (fun a b s' lst1 hR hrel hinv => ?_)
       · rfl
       · lockstep)

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

/-! ### `erase_pw_eq` — a read-only walk, by `lockstep`

The Rust walk reads the store only (`&AState`), so its statements are `LSR`
(task #97-T2-LOCKSTEP lane Checker DeclCheck: the old `SimRE` forms were
`sorry`; the walk and its two fragments are one fuel induction).  The node
fragment `erase_pw_eq_at` takes its two views as values, so it owes their
`EViewMetaWF` (the literal arm's `literal_beq` is exact only on well-formed
literals; the views come from `view_ls`, which supplies it).  The pair
fragment's statement compared `a` with `b` where the Rust compares `a` with
`a2` (its callers pass `(f, f2, x, x2)`); corrected. -/

open Lockstep in
/-- `kernel::expr::literal_beq` is the twin's `==` on well-formed literals. -/
@[lockstep] theorem literal_beq_spec {a b : kernel.expr.Literal}
    (ha : ConRon.Refine.LiteralWF a) (hb : ConRon.Refine.LiteralWF b) :
    LSP (kernel.expr.literal_beq a b)
      (fun c => c = (ConRon.Refine.absLiteral a == ConRon.Refine.absLiteral b)) := by
  intro c h
  rw [ConRon.Refine.Expr.literal_beq_refines ha hb h]
  cases h' : decide (ConRon.Refine.absLiteral a = ConRon.Refine.absLiteral b) <;> simp_all

theorem u64_decide_eq_val_beq (a b : Std.U64) : decide (a = b) = (a.val == b.val) := by
  cases h : decide (a = b) <;> simp_all [UScalar.eq_equiv]

open Lockstep in
/-- The three statements of the walk at fuel `k`, for every related state. -/
def ErasePwEqAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (fuel : Std.U64) (a b : arena.handle.EIdx), fuel.val = k →
      LSR pers (fun a b => b = id a) (arena.std_axioms.erase_pw_eq pers st fuel a b) st lst
        (erasePwEq k (absEIdx a) (absEIdx b))

open Lockstep in
def ErasePwEqTwoAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (fuel : Std.U64) (a a2 b b2 : arena.handle.EIdx), fuel.val = k →
      LSR pers (fun a b => b = id a)
        (arena.std_axioms.erase_pw_eq_two pers st fuel a a2 b b2) st lst
        (do
          if ← erasePwEq k (absEIdx a) (absEIdx a2) then
            erasePwEq k (absEIdx b) (absEIdx b2)
          else pure false)

open Lockstep in
def ErasePwEqNodeAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (fuel : Std.U64) (va vb : arena.store.ENodeView), fuel.val = k →
      EViewMetaWF va → EViewMetaWF vb →
      LSR pers (fun a b => b = id a)
        (arena.std_axioms.erase_pw_eq_at pers st fuel va vb) st lst
        (erasePwEqAtSpec k (absENodeView va) (absENodeView vb))

open Lockstep in
theorem erase_pw_eq_two_of {k : Nat} (h1 : ErasePwEqAt k) : ErasePwEqTwoAt k := by
  intro pers st lst hrel hinv fuel a a2 b b2 hn
  have h1' := @h1 pers
  apply LSR.of_LS
  rw [arena.std_axioms.erase_pw_eq_two]
  lockstep

open Lockstep in
set_option maxHeartbeats 2000000 in
theorem erase_pw_eq_node_of {k : Nat} (h1 : ErasePwEqAt k) : ErasePwEqNodeAt k := by
  have h2 : ErasePwEqTwoAt k := erase_pw_eq_two_of h1
  intro pers st lst hrel hinv fuel va vb hn hva hvb
  have h1' := @h1 pers
  have h2' := @h2 pers
  apply LSR.of_LS
  cases va <;> cases vb <;> simp only [arena.std_axioms.erase_pw_eq_at, absENodeView,
    erasePwEqAtSpec, ← u64_decide_eq_val_beq] at hva hvb ⊢ <;> lockstep

open Lockstep in
theorem erase_pw_eq_aux (k : Nat) : ErasePwEqAt k := by
  induction k with
  | zero =>
    intro pers st lst hrel hinv fuel a b hn
    apply LSR.of_LS
    rw [arena.std_axioms.erase_pw_eq, erasePwEq]
    lockstep
  | succ m ih =>
    have ih' : ErasePwEqNodeAt m := erase_pw_eq_node_of ih
    intro pers st lst hrel hinv fuel a b hn
    have ih'' := @ih' pers
    apply LSR.of_LS
    rw [arena.std_axioms.erase_pw_eq, erasePwEq_unfold]
    lockstep

open Lockstep in
/-- `erase_pw_eq` ⊑ `erasePwEq` — structural equality up to the `pw` datum,
which is exactly what the erasure forgives. -/
@[lockstep] theorem erase_pw_eq_ls {pers st lst}
    {fuel : Std.U64}
    {a : arena.handle.EIdx}
    {b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.std_axioms.erase_pw_eq pers st fuel a b) st lst
      (erasePwEq (absU fuel) (absEIdx a) (absEIdx b)) :=
  erase_pw_eq_aux _ hrel hinv fuel a b rfl

open Lockstep in
/-- `erase_pw_eq_at` is `erase_pw_eq`'s body past the two `view`s (extraction
rule 5), stated against the transcription above, at well-formed views. -/
@[lockstep] theorem erase_pw_eq_at_ls {pers st lst}
    {fuel : Std.U64}
    {va : arena.store.ENodeView}
    {vb : arena.store.ENodeView}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hva : EViewMetaWF va) (hvb : EViewMetaWF vb) :
    LSR pers (fun a b => b = id a)
      (arena.std_axioms.erase_pw_eq_at pers st fuel va vb) st lst
      (erasePwEqAtSpec (absU fuel) (absENodeView va) (absENodeView vb)) :=
  erase_pw_eq_node_of (erase_pw_eq_aux _) hrel hinv fuel va vb rfl hva hvb

open Lockstep in
/-- `erase_pw_eq_two` is the two-child arms' pair of descents, in the twin's
order and with its short-circuit. -/
@[lockstep] theorem erase_pw_eq_two_ls {pers st lst}
    {fuel : Std.U64}
    {a : arena.handle.EIdx}
    {a2 : arena.handle.EIdx}
    {b : arena.handle.EIdx}
    {b2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.std_axioms.erase_pw_eq_two pers st fuel a a2 b b2) st lst
      ((do
        if ← erasePwEq (absU fuel) (absEIdx a) (absEIdx a2) then
          erasePwEq (absU fuel) (absEIdx b) (absEIdx b2)
        else pure false)) :=
  erase_pw_eq_two_of (erase_pw_eq_aux _) hrel hinv fuel a a2 b b2 rfl

open Lockstep in
/-- `i_constant_val_matches_pin` ⊑ `IConstantVal.matchesPin` — exact name,
level parameters and counts, type up to the `pw` datum. -/
@[lockstep] theorem i_constant_val_matches_pin_ls {pers st lst}
    {cv : arena.env.IConstantVal}
    {pin : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.std_axioms.i_constant_val_matches_pin pers st cv pin) st lst
      ((absIConstantVal cv).matchesPin (absIConstantVal pin)) := by
  apply LSR.of_LS
  rw [arena.std_axioms.i_constant_val_matches_pin, IConstantVal.matchesPin]
  simp only [absIConstantVal, ← core_walk_fuel_abs]
  lockstep

/-- `iff_raw` ⊑ `iffRaw` — the con-leche constant, interned. -/
theorem iff_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffRaw) := by
  rw [arena.std_axioms.iff_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.iff_raw pers st) lst
      (iffRaw) :=
  LS.ofSim₀ fun _ h => iff_raw_refines hrel hinv h

/-- `iff_intro_raw` ⊑ `iffIntroRaw` — the con-leche constant, interned. -/
theorem iff_intro_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_intro_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffIntroRaw) := by
  rw [arena.std_axioms.iff_intro_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_intro_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_intro_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.iff_intro_raw pers st) lst
      (iffIntroRaw) :=
  LS.ofSim₀ fun _ h => iff_intro_raw_refines hrel hinv h

/-- `iff_rec_intro` ⊑ `iffRecIntro` — the con-leche constant, interned. -/
theorem iff_rec_intro_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_rec_intro pers st = ok o) :
    Sim₀ absEIdx pers lst o
      (iffRecIntro) := by
  rw [arena.std_axioms.iff_rec_intro] at hrun
  exact sim_intern_expr_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_rec_intro_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_rec_intro_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.std_axioms.iff_rec_intro pers st) lst
      (iffRecIntro) :=
  LS.ofSim₀ fun _ h => iff_rec_intro_refines hrel hinv h

/-- `iff_rec_raw` ⊑ `iffRecRaw` — the con-leche constant, interned. -/
theorem iff_rec_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_rec_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (iffRecRaw) := by
  rw [arena.std_axioms.iff_rec_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_rec_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_rec_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.iff_rec_raw pers st) lst
      (iffRecRaw) :=
  LS.ofSim₀ fun _ h => iff_rec_raw_refines hrel hinv h

/-- `iff_family` ⊑ `iffFamily` — the con-leche constant, interned. -/
theorem iff_family_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.iff_family pers st = ok o) :
    Sim₀ absICIL pers lst o
      (iffFamily) := by
  rw [arena.std_axioms.iff_family] at hrun
  exact sim_intern_ci_list_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.iff_family_refines h) hrun

open Lockstep in
@[lockstep] theorem iff_family_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a)
      (arena.std_axioms.iff_family pers st) lst
      (iffFamily) :=
  LS.ofSim₀ fun _ h => iff_family_refines hrel hinv h

/-- `propext_raw` ⊑ `propextRaw` — the con-leche constant, interned. -/
theorem propext_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.propext_raw pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (propextRaw) := by
  rw [arena.std_axioms.propext_raw] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.propext_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem propext_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.std_axioms.propext_raw pers st) lst
      (propextRaw) :=
  LS.ofSim₀ fun _ h => propext_raw_refines hrel hinv h

/-- `nonempty_raw` ⊑ `nonemptyRaw` — the con-leche constant, interned. -/
theorem nonempty_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyRaw) := by
  rw [arena.std_axioms.nonempty_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem nonempty_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.nonempty_raw pers st) lst
      (nonemptyRaw) :=
  LS.ofSim₀ fun _ h => nonempty_raw_refines hrel hinv h

/-- `nonempty_intro_raw` ⊑ `nonemptyIntroRaw` — the con-leche constant, interned. -/
theorem nonempty_intro_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_intro_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyIntroRaw) := by
  rw [arena.std_axioms.nonempty_intro_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_intro_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem nonempty_intro_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.nonempty_intro_raw pers st) lst
      (nonemptyIntroRaw) :=
  LS.ofSim₀ fun _ h => nonempty_intro_raw_refines hrel hinv h

/-- `nonempty_rec_raw` ⊑ `nonemptyRecRaw` — the con-leche constant, interned. -/
theorem nonempty_rec_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_rec_raw pers st = ok o) :
    Sim₀ absIConstantInfo pers lst o
      (nonemptyRecRaw) := by
  rw [arena.std_axioms.nonempty_rec_raw] at hrun
  exact sim_intern_ci_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_rec_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem nonempty_rec_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.std_axioms.nonempty_rec_raw pers st) lst
      (nonemptyRecRaw) :=
  LS.ofSim₀ fun _ h => nonempty_rec_raw_refines hrel hinv h

/-- `nonempty_family` ⊑ `nonemptyFamily` — the con-leche constant, interned. -/
theorem nonempty_family_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.nonempty_family pers st = ok o) :
    Sim₀ absICIL pers lst o
      (nonemptyFamily) := by
  rw [arena.std_axioms.nonempty_family] at hrun
  exact sim_intern_ci_list_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.nonempty_family_refines h) hrun

open Lockstep in
@[lockstep] theorem nonempty_family_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a)
      (arena.std_axioms.nonempty_family pers st) lst
      (nonemptyFamily) :=
  LS.ofSim₀ fun _ h => nonempty_family_refines hrel hinv h

/-- `choice_raw` ⊑ `choiceRaw` — the con-leche constant, interned. -/
theorem choice_raw_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.std_axioms.choice_raw pers st = ok o) :
    Sim₀ absIConstantVal pers lst o
      (choiceRaw) := by
  rw [arena.std_axioms.choice_raw] at hrun
  exact sim_intern_cv_of hrel hinv (fun _ h => ConRon.Refine.StdAxioms.choice_raw_refines h) hrun

open Lockstep in
@[lockstep] theorem choice_raw_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.std_axioms.choice_raw pers st) lst
      (choiceRaw) :=
  LS.ofSim₀ fun _ h => choice_raw_refines hrel hinv h

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

/-- `reduce_op_raw` ⊑ `reduceOpRaw`. -/
theorem reduce_op_raw_refines {pers st lst} {c : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.reduce_op_raw pers st c = ok o) :
    Sim₀ absIConstantVal pers lst o
      (reduceOpRaw (absNIdx c)) := by
  sorry

open Lockstep in
@[lockstep] theorem reduce_op_raw_ls {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.reduce_op_raw pers st c) lst
      (reduceOpRaw (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_op_raw_refines hrel hinv h

/-- `of_reduce_raw` ⊑ `ofReduceRaw`. -/
theorem of_reduce_raw_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.trust_axioms.of_reduce_raw pers st n = ok o) :
    Sim₀ absIConstantVal pers lst o
      (ofReduceRaw (absNIdx n)) := by
  sorry

open Lockstep in
@[lockstep] theorem of_reduce_raw_ls {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.of_reduce_raw pers st n) lst
      (ofReduceRaw (absNIdx n)) :=
  LS.ofSim₀ fun _ h => of_reduce_raw_refines hrel hinv h

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

open Lockstep in
@[lockstep] theorem reduce_nat_cv_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.reduce_nat_cv_a pers st) lst
      (reduceNatCvA) :=
  LS.ofSim₀ fun _ h => reduce_nat_cv_a_refines hrel hinv h

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

open Lockstep in
@[lockstep] theorem reduce_bool_cv_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.reduce_bool_cv_a pers st) lst
      (reduceBoolCvA) :=
  LS.ofSim₀ fun _ h => reduce_bool_cv_a_refines hrel hinv h

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

open Lockstep in
@[lockstep] theorem of_reduce_nat_a_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.trust_axioms.of_reduce_nat_a pers st) lst
      (ofReduceNatA) :=
  LS.ofSim₀ fun _ h => of_reduce_nat_a_refines hrel hinv h

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
