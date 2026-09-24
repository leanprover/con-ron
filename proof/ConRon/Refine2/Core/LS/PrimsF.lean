/-
# `ConRon.Refine2.Core.LS.PrimsF` — region F's primitive pairs

Task #97-P5-Core round 5, region F (the `defeq` loop).  The `@[lockstep]`
pairs the `defeq` bodies need that no other file has: handle equality, the
tag tests in `!=` form, the literal and bignum steps of the literal arms, and
`view_wf_ls` — the `view` read carrying the node's well-formedness, which the
literal and binder-datum comparisons need to be exact.
-/
import ConRon.Refine2.Core.LS.Prims

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PF

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

attribute [local lockstep_simp] absConstT

/-! ## Handle equality: the port's `eq2` is the twin's `==`/`=`

Every handle kind is a word; `eq2` compares the words, and the abstraction is
injective.  The conclusions are in `decide` form, and the twin's `==` on a
handle (a `LawfulBEq`) is `decide` by `idx_beq_decide`. -/

theorem idx_beq_decide {k : IdxKind} (a b : Idx k) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

-- local: globally it rewrites other tiers' twins off their definitions
-- (`Inductives/SumInstall`'s `checkSumIndAtSpec`); `Core/LS/Defeq` re-declares it
attribute [local lockstep_simp] idx_beq_decide

private theorem word_decide {k : IdxKind} {α : Type} (w : α → Std.U32)
    (A : α → Idx k) (hA : ∀ x, A x = ⟨absU32 (w x)⟩) (a b : α) :
    decide (w a = w b) = decide (A a = A b) := by
  simp only [decide_eq_decide, hA]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg Idx.word h
    exact absU32_inj this

@[lockstep] theorem eidx_eq2_ls (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absEIdx a = absEIdx b)) := by
  intro r h
  rw [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.EIdx.word absEIdx (fun _ => rfl) a b

@[lockstep] theorem lsidx_eq2_ls (a b : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absLsIdx a = absLsIdx b)) := by
  intro r h
  rw [arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.LsIdx.word absLsIdx (fun _ => rfl) a b

@[lockstep] theorem bmidx_eq2_ls (a b : arena.handle.BMIdx) :
    LSP (arena.handle.BMIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absBMIdx a = absBMIdx b)) := by
  intro r h
  rw [arena.handle.BMIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.BMIdx.word absBMIdx (fun _ => rfl) a b

/-! ## Tag tests in `bne` form

The peel tests tags with `!=` on both sides (`ta != b.tag`, `ta !=
ETAG_LAM`); these put the two in the same `decide` form. -/

@[local lockstep_simp] theorem absU32_bne (x y : Std.U32) :
    (absU32 x != absU32 y) = !(decide (x = y)) := by
  by_cases h : x = y
  · subst h; simp
  · have : absU32 x ≠ absU32 y := fun hc => h (absU32_inj hc)
    simp [h, this]

@[local lockstep_simp] theorem u32_bne (x y : Std.U32) : (x != y) = !(decide (x = y)) := by
  by_cases h : x = y <;> simp [h]

attribute [local lockstep_simp] ETag.isBind Bool.or_eq_true Bool.not_eq_true' Bool.not_true
  false_or or_false true_or or_true false_and and_false Bool.not_eq_false Bool.not_eq_true
  Bool.true_or Bool.false_or Bool.or_true Bool.or_false Bool.true_and Bool.and_true Bool.false_and
  Bool.and_false Bool.and_eq_true decide_not ite_true ite_false and_self

/-- A tag equality on the twin's word, as the port's scalar test . -/
theorem absU32_eq_absU32 (t c : Std.U32) : (absU32 t = absU32 c) = (t = c) := by
  apply propext; constructor
  · intro h; exact absU32_inj h
  · intro h; rw [h]

@[local lockstep_simp] theorem absU32_eq_lam (t : Std.U32) :
    (absU32 t = ETag.lam) = (t = arena.handle.ETAG_LAM) := by
  rw [← etag_lam_abs, absU32_eq_absU32]

@[local lockstep_simp] theorem absU32_eq_forallE (t : Std.U32) :
    (absU32 t = ETag.forallE) = (t = arena.handle.ETAG_FORALL_E) := by
  rw [← etag_forallE_abs, absU32_eq_absU32]

@[local lockstep_simp] theorem etag_forallE_ne_lam : (ETag.forallE = ETag.lam) = False := by
  simp [ETag.forallE, ETag.lam]

@[local lockstep_simp] theorem etag_lam_ne_forallE : (ETag.lam = ETag.forallE) = False := by
  simp [ETag.forallE, ETag.lam]

@[local lockstep_simp] theorem etag_FORALL_ne_LAM :
    (arena.handle.ETAG_FORALL_E = arena.handle.ETAG_LAM) = False := by
  apply propext; constructor
  · intro h
    have := congrArg absU32 h
    rw [etag_forallE_abs, etag_lam_abs] at this
    exact absurd this (by simp [ETag.forallE, ETag.lam])
  · intro h; exact h.elim

@[local lockstep_simp] theorem etag_LAM_ne_FORALL :
    (arena.handle.ETAG_LAM = arena.handle.ETAG_FORALL_E) = False := by
  apply propext; constructor
  · intro h
    have := congrArg absU32 h
    rw [etag_forallE_abs, etag_lam_abs] at this
    exact absurd this (by simp [ETag.forallE, ETag.lam])
  · intro h; exact h.elim

@[local lockstep_simp] theorem absU32_eq_const (t : Std.U32) :
    (absU32 t = ETag.const) = (t = arena.handle.ETAG_CONST) := by
  rw [← etag_const_abs, absU32_eq_absU32]

/-! ## Reducibility hints -/

@[lockstep] theorem reducibility_hint_lt_ls (a b : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_lt a b)
      (fun r => r = ConLeche.ReducibilityHint.lt (ConRon.Refine.absHint a)
        (ConRon.Refine.absHint b)) := by
  intro r h
  cases a <;> cases b <;>
    simp only [kernel.env.reducibility_hint_lt, Result.ok.injEq] at h <;> subst h <;>
    simp [ConLeche.ReducibilityHint.lt, ConRon.Refine.absHint]

@[lockstep] theorem reducibility_hint_same_regular_ls (a b : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_same_regular a b)
      (fun r => r = ConLeche.ReducibilityHint.sameRegular (ConRon.Refine.absHint a)
        (ConRon.Refine.absHint b)) := by
  intro r h
  cases a <;> cases b <;>
    simp only [kernel.env.reducibility_hint_same_regular, Result.ok.injEq] at h <;> subst h <;>
    simp [ConLeche.ReducibilityHint.sameRegular, ConRon.Refine.absHint]
  rename_i x y
  by_cases h : x = y
  · subst h; simp
  · have : x.val ≠ y.val := fun e => h (UScalar.eq_imp x y e)
    simp [h, this]

@[local lockstep_simp] theorem internLitE_eq (l : ConLeche.Literal) :
    Arena.internLitE l = Arena.internE (.lit l) := rfl

/-! ## The accumulated free variables -/

/-- The port pushes onto its `Vec`, the twin onto its `Array`: the push
step stated in the twin's shape.  Not `@[lockstep]` (the generic
`vec_push_spec` is registered first); the proofs that need it take it as a
local hypothesis, which `lockstep` tries before the registered lemmas. -/
theorem vec_push_eidx_ls (v : alloc.vec.Vec arena.handle.EIdx) (x : arena.handle.EIdx) :
    LSP (alloc.vec.Vec.push v x) (fun w => absEIdxArr w = (absEIdxArr v).push (absEIdx x)) := by
  intro w h
  have := ConRon.Refine.vec_push_val h
  simp [absEIdxArr, this]

@[local lockstep_simp] theorem absBinderMeta_pw (m : kernel.expr.BinderMeta) :
    (ConRon.Refine.absBinderMeta m).pw = ConRon.Refine.absPropWhen m.pw := rfl

@[local lockstep_simp] theorem absEIdxArr_new :
    absEIdxArr (alloc.vec.Vec.new arena.handle.EIdx) = #[] := rfl

@[local lockstep_simp] theorem arr_empty_push (x : EIdx) : (#[] : Array EIdx).push x = #[x] := rfl

@[local lockstep_simp] theorem peel_fuel_val : (arena.core.PEEL_FUEL).val = peelFuel := by
  rw [arena.core.PEEL_FUEL]; rfl

/-! ## Spine lengths -/

@[local lockstep_simp] theorem absEIdxList_length' (v : alloc.vec.Vec arena.handle.EIdx) :
    (ExprOps.absEIdxList v).length = v.val.length := by
  simp [ExprOps.absEIdxList]

@[local lockstep_simp] theorem vec_len_eq_iff {α : Type} (v w : alloc.vec.Vec α) :
    (v.len = w.len) = (v.val.length = w.val.length) := by
  apply propext
  constructor
  · intro h
    have := congrArg UScalar.val h
    simpa [alloc.vec.Vec.len_val] using this
  · intro h
    apply Aeneas.Std.UScalar.eq_imp
    simpa [alloc.vec.Vec.len_val] using h

/-! ## Literals and binder data: exact comparisons on well-formed values -/

/-- `==` at a type whose `BEq` is its `DecidableEq` (`ConLeche.Literal`,
`ConLeche.PropWhen`) is `decide`. -/
theorem beq_of_decEq {α : Type} [DecidableEq α] (a b : α) :
    (@BEq.beq α instBEqOfDecidableEq a b) = decide (a = b) := rfl

-- local: globally it rewrites other tiers' twins off their definitions
-- (`Inductives/SumInstall`'s `checkSumIndAtSpec`); `Core/LS/Defeq` re-declares it
attribute [local lockstep_simp] beq_of_decEq

@[lockstep] theorem arc_deref_ls {T : Type} (A : Type) (x : alloc.sync.Arc T) :
    LSP (alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x) (fun y => y = x) :=
  fun _ h => (Result.ok_injective h).symm

@[lockstep] theorem nat_is_zero_ls (n : ron.nat.Nat) (hn : ConRon.Refine.Nat.NatWF n) :
    LSP (ron.nat.is_zero n) (fun b => b = decide (ConRon.Refine.Nat.toNat n = 0)) :=
  fun _ h => ConRon.Refine.Nat.is_zero_refines hn h

@[lockstep] theorem nat_pred_ls (n : ron.nat.Nat) (hn : ConRon.Refine.Nat.NatWF n) :
    LSP (ron.nat.pred n)
      (fun c => ConRon.Refine.Nat.NatWF c ∧
        ConRon.Refine.Nat.toNat c = ConRon.Refine.Nat.toNat n - 1) :=
  fun _ h => let r := ConRon.Refine.Nat.pred_refines hn h; ⟨r.2, r.1⟩

theorem natWF_of_limbs {m n : ron.nat.Nat} (h : m.limbs.val = n.limbs.val)
    (hn : ConRon.Refine.Nat.NatWF n) : ConRon.Refine.Nat.NatWF m := by
  unfold ConRon.Refine.Nat.NatWF; rw [h]; exact hn

@[lockstep] theorem nat_clone_ls (n : ron.nat.Nat) (hn : ConRon.Refine.Nat.NatWF n) :
    LSP (ron.nat.clone n)
      (fun m => ConRon.Refine.Nat.NatWF m ∧
        ConRon.Refine.Nat.toNat m = ConRon.Refine.Nat.toNat n) :=
  fun _ h => let r := ConRon.Refine.Nat.clone_refines h; ⟨natWF_of_limbs r.1 hn, r.2⟩

theorem nat_beq_decide' (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

-- local: globally it rewrites other tiers' twins off their definitions
-- (`Inductives/SumInstall`'s `checkSumIndAtSpec`); `Core/LS/Defeq` re-declares it
attribute [local lockstep_simp] nat_beq_decide'

attribute [local lockstep_simp] ConRon.Refine.absLiteral ConRon.Refine.LiteralWF

@[lockstep] theorem literal_nat_ls (k : ron.nat.Nat) :
    LSP (kernel.expr.literal_nat k) (fun l => l = .NatVal k) := by
  intro l h
  rw [kernel.expr.literal_nat, ConRon.Refine.ptr_new_eq, bind_tc_ok] at h
  exact (Result.ok_injective h).symm

@[lockstep] theorem str_copy_ls (v : alloc.vec.Vec Std.U32) :
    LSP (kernel.expr.str_copy v) (fun r => r = v) :=
  fun _ h => ConRon.Refine.Expr.str_copy_eq h

@[lockstep] theorem literal_beq_ls (a b : kernel.expr.Literal)
    (ha : ConRon.Refine.LiteralWF a) (hb : ConRon.Refine.LiteralWF b) :
    LSP (kernel.expr.literal_beq a b)
      (fun c => c = decide (ConRon.Refine.absLiteral a = ConRon.Refine.absLiteral b)) :=
  fun _ h => ConRon.Refine.Expr.literal_beq_refines ha hb h

/-! ## What a `view` read: a well-formed node

The port's `view` returns a node whose literal payload and binder datum are
well formed (`StoreInv`'s node columns, `tbl_node_wf`).  The `defeq` arms
compare literals (`literal_beq`, `nat::is_zero`) and binder data
(`prop_when::beq`), which are exact only on well-formed values, so the
`defeq` proofs use `view_wf_ls` (a local hypothesis, tried before the global
`view_ls`), which carries `ENodeViewWF` in its relation. -/

theorem etables_get_bm_wf {rt} (hinv : ETablesInv rt) {i : arena.handle.BMIdx}
    {o : Option kernel.expr.BinderMeta}
    (h : arena.store.ETables.get_bm rt i = ok o) :
    ∀ m, o = some m → ConRon.Refine.PropWhenWF m.pw := by
  rw [arena.store.ETables.get_bm] at h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hw := tbl_node_wf hinv.bms hp
  cases hpc : p with
  | none =>
    rw [hpc] at h; intro m hm; rw [← Result.ok_injective h] at hm; simp at hm
  | some r =>
    rw [hpc] at h
    obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    intro m hm
    rw [← Result.ok_injective h] at hm
    cases Option.some.inj hm
    rw [kernel.expr.binder_meta] at hbm
    cases Result.ok_injective hbm
    show ConRon.Refine.PropWhenWF pw
    rw [ConRon.Refine.PropWhen.dup_eq hpw]
    exact hw r hpc

theorem estore_view_bm_wf {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.BMIdx}
    {o : Option kernel.expr.BinderMeta}
    (h : arena.store.EStore.view_bm rs pers i = ok o) :
    ∀ m, o = some m → ConRon.Refine.PropWhenWF m.pw := by
  rw [arena.store.EStore.view_bm] at h
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · rw [arena.store.EStore.pers_get_bm] at h
    have hp := hinv.perst
    rw [rPersE] at hp
    split at h <;> rename_i hs
    · rw [if_pos hs] at hp; exact etables_get_bm_wf hp h
    · rw [if_neg hs] at hp; exact etables_get_bm_wf hp h
  · split at h
    · exact etables_get_bm_wf hinv.scrt h
    · intro m hm; rw [← Result.ok_injective h] at hm; simp at hm

theorem etables_get_wf {rt} (hinv : ETablesInv rt) {i : arena.handle.EIdx}
    {o : Option arena.store.ENodeView}
    (h : arena.store.ETables.get rt i = ok o) :
    ∀ v, o = some v → ENodeViewWF v := by
  rw [arena.store.ETables.get] at h
  intro v hv
  repeat' (first
    | (split at h)
    | (obtain ⟨_, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h))
  all_goals (first
    | (rw [← Result.ok_injective h] at hv; simp at hv; done)
    | (rw [← Result.ok_injective h] at hv; cases Option.some.inj hv; trivial)
    | skip)
  -- the literal arm: the node column's record is well formed
  rename_i r hn _ w hd
  rw [← Result.ok_injective h] at hv
  cases Option.some.inj hv
  show ConRon.Refine.LiteralWF w
  rw [ConRon.Refine.Expr.literal_dup_eq hd]
  exact tbl_node_wf hinv.lits hn r rfl

theorem estore_view_bind_wf {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.EIdx}
    {o : Option (arena.handle.EIdx × arena.handle.EIdx × kernel.expr.BinderMeta)}
    (h : arena.store.EStore.view_bind rs pers i = ok o) :
    ∀ t, o = some t → ConRon.Refine.PropWhenWF t.2.2.pw := by
  rw [arena.store.EStore.view_bind] at h
  obtain ⟨q, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  intro t ht
  cases q with
  | none => rw [← Result.ok_injective h] at ht; simp at ht
  | some q =>
    obtain ⟨e, e1, b⟩ := q
    obtain ⟨o1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases o1 with
    | none => rw [← Result.ok_injective h] at ht; simp at ht
    | some m =>
      rw [← Result.ok_injective h] at ht
      cases Option.some.inj ht
      exact estore_view_bm_wf hinv h1 m rfl

theorem estore_view_wf {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.EIdx}
    {o : Option arena.store.ENodeView}
    (h : arena.store.EStore.view rs pers i = ok o) :
    ∀ v, o = some v → ENodeViewWF v := by
  rw [arena.store.EStore.view] at h
  obtain ⟨t, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bb, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    intro v hv
    cases q with
    | none => rw [← Result.ok_injective h] at hv; simp at hv
    | some q =>
      obtain ⟨e, e1, m⟩ := q
      have hm := estore_view_bind_wf hinv hq _ rfl
      obtain ⟨ev, hev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h] at hv
      cases Option.some.inj hv
      rw [arena.store.e_bind_view] at hev
      split at hev <;> (cases Result.ok_injective hev; exact hm)
  · obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h
    · rw [arena.store.EStore.pers_get] at h
      have hp := hinv.perst
      rw [rPersE] at hp
      split at h <;> rename_i hs
      · rw [if_pos hs] at hp; exact etables_get_wf hp h
      · rw [if_neg hs] at hp; exact etables_get_wf hp h
    · split at h
      · exact etables_get_wf hinv.scrt h
      · intro v hv; rw [← Result.ok_injective h] at hv; simp at hv

attribute [local lockstep_simp] ENodeViewWF

/-- `arena::monad::view` against `Arena.view`, carrying the port's own
representation fact about what it read: the viewed node is well formed
(`StoreInv`'s node columns) — what the `defeq` arms' literal and binder-datum
comparisons need to be exact. -/
theorem view_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => ENodeViewWF a ∧ b = absENodeView a) (arena.monad.view pers st h) st lst
      (Arena.view (absEIdx h)) := by
  intro o hrun
  have hv := view_ls hrel hinv h o hrun
  cases o with
  | Err e => exact hv
  | Ok v =>
    obtain ⟨b, lst', h1, h2, h3, h4⟩ := hv
    refine ⟨b, lst', h1, ⟨?_, h2.2⟩, h3, h4⟩
    rw [arena.monad.view] at hrun
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases q with
    | none =>
      obtain ⟨s, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [arena.monad.fail] at hrun
      cases Result.ok_injective hrun
    | some v' =>
      cases Result.ok_injective hrun
      exact estore_view_wf hinv.store hq v rfl

end ConRon.Refine2.Lockstep.PF

/-! The region's `lockstep_simp` rules, registered `scoped` (task #97-P5-Core
round 5): active under `open scoped ConRon.Refine2.Lockstep.PF.CoreLSReg` only, so that they
stay out of the other tiers' `lockstep` runs (the Checker lane imports the
knot since task #97-T2-LOCKSTEP lane Checker DeclCheck). -/
namespace ConRon.Refine2.Lockstep.PF.CoreLSReg
open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep
attribute [scoped lockstep_simp] absConstT absU32_bne u32_bne ETag.isBind Bool.or_eq_true Bool.not_eq_true' Bool.not_true false_or or_false true_or or_true false_and and_false Bool.not_eq_false Bool.not_eq_true Bool.true_or Bool.false_or Bool.or_true Bool.or_false Bool.true_and Bool.and_true Bool.false_and Bool.and_false Bool.and_eq_true decide_not ite_true ite_false and_self absU32_eq_lam absU32_eq_forallE etag_forallE_ne_lam etag_lam_ne_forallE etag_FORALL_ne_LAM etag_LAM_ne_FORALL absU32_eq_const internLitE_eq absBinderMeta_pw absEIdxArr_new arr_empty_push peel_fuel_val absEIdxList_length' vec_len_eq_iff ConRon.Refine.absLiteral ConRon.Refine.LiteralWF ENodeViewWF
end ConRon.Refine2.Lockstep.PF.CoreLSReg
