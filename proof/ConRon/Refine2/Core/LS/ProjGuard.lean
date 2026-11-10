/-
# `ConRon.Refine2.Core.LS.ProjGuard` — the projection guard and the former's sort, at use

The official `infer_proj` restriction (con-leche task #480) is computed at each use
from the stored structure and constructor types (`check_proj_guard`), and the
sort a family's former reaches is walked to at the use's levels
(`former_sort_loop`).  This file is the Theorem-2 lockstep lemmas of that part of
`arena::core`: the loose-bound-variable walk (`has_loose_bvar_b_*`), the field
use test (`struct_used_later`), the telescope opening (`open_pis_at_fvars*`), the
rows (`proj_guard_rows*`), the guard sort (`proj_guard_sort`), the rows' check
(`check_guard_rows`) and the two level predicates they read
(`kernel::level::is_always_zero`, `zero_where_zero`).

**The loose-bound-variable walk is transcribed.**  The Rust splits the walk's
node arms into `has_loose_bvar_b_node` and probes the memo in each arm that
recurses; the twin probes once past the leaf arms.  `hasLooseBVarBGo_succ_split`
is the twin's clause at `fuel + 1` in the Rust's shape (the probe and the
insertion repeated per arm, `hlbNodeT` the node), so the walk is zipped arm by
arm.
-/
import ConRon.Refine2.Core.LS.Lits
import ConRon.Refine2.Core.LS.Shapes

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-! ## The two level predicates -/

/-- `kernel::level::is_always_zero` is `Level.isAlwaysZero` of the abstraction. -/
theorem is_always_zero_abs {l : kernel.level.Level} (hl : ConRon.Refine.LevelWF l) {b : Bool}
    (h : kernel.level.is_always_zero l = ok b) :
    b = ConLeche.Level.isAlwaysZero (ConRon.Refine.absLevel l) := by
  rw [kernel.level.is_always_zero] at h
  obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨habs, -⟩ := ConRon.Refine.ExprOps.zeroness_of_refines hl pw hpw
  rw [ConLeche.Level.isAlwaysZero, ← habs]
  cases pw with
  | Never => cases Result.ok_injective h; rfl
  | IfAllZero ps =>
    cases Result.ok_injective h
    simp only [ConRon.Refine.absPropWhen, ConRon.Refine.absNames]
    rcases hps : ps.val with _ | ⟨p, ps'⟩
    · have : alloc.vec.Vec.len ps = 0#usize := by
        apply Std.UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len, hps]
      simp [this]
    · have : alloc.vec.Vec.len ps ≠ 0#usize := by
        intro h0; have := congrArg Std.UScalar.val h0; simp [alloc.vec.Vec.len, hps] at this
      simp [this]

theorem names_all_in_from_abs {qs ps : alloc.vec.Vec kernel.name.Name}
    (hqs : ConRon.Refine.NamesWF qs) (hps : ConRon.Refine.NamesWF ps) :
    ∀ (k : Nat) (i : Std.Usize) (b : Bool), qs.val.length - i.val = k →
      kernel.level.names_all_in_from qs ps i = ok b →
      b = ((ConRon.Refine.absNames qs).drop i.val).all (ConRon.Refine.absNames ps).contains := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [kernel.level.names_all_in_from] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len qs by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by simp [ConRon.Refine.absNames]; omega)]
    rfl
  | succ k ih =>
    intro i b hk h
    have hlt : i.val < qs.val.length := by omega
    rw [kernel.level.names_all_in_from] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len qs by scalar_tac)] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, rfl⟩ := ExprOps.vecIndexAt hn
    have hcv := ConRon.Refine.Name.contains_refines hps (hqs _ (List.getElem_mem hlt)) hc
    have hdrop : (ConRon.Refine.absNames qs).drop i.val =
        ConRon.Refine.absName qs.val[i.val] :: (ConRon.Refine.absNames qs).drop (i.val + 1) := by
      simp only [ConRon.Refine.absNames]
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [hdrop, List.all_cons, ← hcv]
    cases c with
    | false =>
      rw [ite_eq_right (by simp)] at h
      cases Result.ok_injective h
      rfl
    | true =>
      rw [ite_eq_left (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi2
      rw [Bool.true_and, ih i2 b (by omega) h, hi2v]

/-- `kernel::level::zero_where_zero` is `Level.zeroWhereZero` of the abstractions. -/
theorem zero_where_zero_abs {s u : kernel.level.Level} (hs : ConRon.Refine.LevelWF s)
    (hu : ConRon.Refine.LevelWF u) {b : Bool} (h : kernel.level.zero_where_zero s u = ok b) :
    b = ConLeche.Level.zeroWhereZero (ConRon.Refine.absLevel s) (ConRon.Refine.absLevel u) := by
  rw [kernel.level.zero_where_zero] at h
  obtain ⟨zs, hzs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨zu, hzu, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hAs, ws⟩ := ConRon.Refine.ExprOps.zeroness_of_refines hs zs hzs
  obtain ⟨hAu, wu⟩ := ConRon.Refine.ExprOps.zeroness_of_refines hu zu hzu
  rw [ConLeche.Level.zeroWhereZero, ← hAs, ← hAu]
  cases zs with
  | Never => cases Result.ok_injective h; rfl
  | IfAllZero ps =>
    cases zu with
    | Never => cases Result.ok_injective h; rfl
    | IfAllZero qs =>
      simp only at h
      have := names_all_in_from_abs wu ws _ 0#usize b rfl h
      simpa [ConRon.Refine.absPropWhen] using this

/-! ## The loose-bound-variable walk -/

/-- The node arms of `hasLooseBVarBGo`, as the Rust's `has_loose_bvar_b_node`. -/
def hlbNodeT (memo : Std.HashMap (EIdx × Nat) Bool) (i fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | .app f a => do
    match ← hasLooseBVarBGo memo i fuel f with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarBGo memo i fuel a
  | .lam ty b => do
    match ← hasLooseBVarBGo memo i fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
  | .forallE ty b => do
    match ← hasLooseBVarBGo memo i fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
  | .letE t v b => do
    match ← hasLooseBVarBGo memo i fuel t with
    | (true, memo) => pure (true, memo)
    | (false, memo) => do
      match ← hasLooseBVarBGo memo i fuel v with
      | (true, memo) => pure (true, memo)
      | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
  | .proj _ _ sub => hasLooseBVarBGo memo i fuel sub
  | _ => pure (false, memo)

/-- A recursing arm: the memo probe, then the node and the insertion. -/
def hlbArmT (memo : Std.HashMap (EIdx × Nat) Bool) (i fuel : Nat) (h : EIdx)
    (v : ENodeView) : AM (Bool × Std.HashMap (EIdx × Nat) Bool) :=
  match memo[(h, i)]? with
  | none => do
    let r ← hlbNodeT memo i fuel v
    pure (hasLooseBVarBIns h i r)
  | some r => pure (r, memo)

/-- `hasLooseBVarBGo` at `fuel + 1` in the Rust's shape: the probe repeated in
each recursing arm. -/
theorem hasLooseBVarBGo_succ_split (memo : Std.HashMap (EIdx × Nat) Bool) (i fuel : Nat)
    (h : EIdx) :
    hasLooseBVarBGo memo i (fuel + 1) h = (do
      let bb ← bvarB fuel h
      if bb ≤ i then pure (false, memo) else
      match ← view h with
      | .bvar j => pure (i == j, memo)
      | .fvar _ _ => pure (false, memo)
      | .sort _ => pure (false, memo)
      | .const _ _ => pure (false, memo)
      | .app f a => hlbArmT memo i fuel h (.app f a)
      | .lam ty b => hlbArmT memo i fuel h (.lam ty b)
      | .forallE ty b => hlbArmT memo i fuel h (.forallE ty b)
      | .letE t v b => hlbArmT memo i fuel h (.letE t v b)
      | .lit _ => pure (false, memo)
      | .proj s k sub => hlbArmT memo i fuel h (.proj s k sub)) := by
  rw [hasLooseBVarBGo]
  refine congrArg _ (funext fun bb => ?_)
  split
  · rfl
  · refine congrArg _ (funext fun v => ?_)
    cases v <;> try rfl
    all_goals
      cases hm : memo[(h, i)]? <;>
        simp only [hlbArmT, hlbNodeT, hm, bind_assoc, pure_bind]
      all_goals
        refine congrArg _ (funext fun x => ?_)
        rcases x with ⟨_ | _, m⟩ <;> simp only [pure_bind, bind_assoc]
      all_goals
        refine congrArg _ (funext fun y => ?_)
        rcases y with ⟨_ | _, m'⟩ <;> simp only [pure_bind]

/-- `hlb_probe` is the memo's lookup. -/
@[lockstep] theorem hlb_probe_ls {memo : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : ExprOps.WMemoRel memo lm)
    (k : arena.monad.EIdxNat) :
    LSP (arena.core.hlb_probe memo k) (fun o => o = lm[absEIdxNat k]?) := by
  intro o h
  have h' : arena.expr_ops.wscoped_memo_get memo k = ok o := by
    rw [arena.expr_ops.wscoped_memo_get]; rw [arena.core.hlb_probe] at h; exact h
  exact (ExprOps.wscoped_memo_get_refines hm.2 ConRon.Refine.HashMap2.KeysOk_true hm.1 h').symm

/-- `has_loose_bvar_b_ins` records the answer: `hasLooseBVarBIns`. -/
@[lockstep] theorem has_loose_bvar_b_ins_ls {r : Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : ExprOps.WMemoRel r.2 lm)
    (e : arena.handle.EIdx) (i : Std.U64) :
    LSP (arena.core.has_loose_bvar_b_ins e i r)
      (fun p => ∃ m', ExprOps.WMemoRel p.2 m' ∧
        hasLooseBVarBIns (absEIdx e) (absU i) (r.1, lm) = (p.1, m')) := by
  intro p h
  obtain ⟨b, memo⟩ := r
  rw [arena.core.has_loose_bvar_b_ins] at h
  obtain ⟨en, hen, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨old, m1⟩ := q
  cases Result.ok_injective h
  have hset : arena.expr_ops.wscoped_memo_set memo en b = ok m1 := by
    rw [arena.expr_ops.wscoped_memo_set, hq, bind_ok]; rfl
  obtain ⟨h1, h2, -⟩ :=
    ExprOps.wscoped_memo_set_refines hm.2 ConRon.Refine.HashMap2.KeysOk_true hm.1 hset
  refine ⟨_, ⟨h1, h2⟩, ?_⟩
  simp only [hasLooseBVarBIns, eidx_nat_key_abs hen]

section hlb
attribute [local lockstep_simp] hlbArmT hlbNodeT

theorem has_loose_bvar_b_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool) (lm : Std.HashMap (EIdx × Nat) Bool)
      (i fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → ExprOps.WMemoRel rm lm →
      LS pers (fun a b => ∃ m', ExprOps.WMemoRel a.2 m' ∧ b = (a.1, m'))
        (arena.core.has_loose_bvar_b_go pers st rm i fuel h) lst
        (hasLooseBVarBGo lm (absU i) n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm i fuel h hn hrel hinv hm
    rw [arena.core.has_loose_bvar_b_go, hasLooseBVarBGo]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm i fuel h hn hrel hinv hm
    rw [arena.core.has_loose_bvar_b_go, hasLooseBVarBGo_succ_split]
    unfold arena.core.has_loose_bvar_b_node
    lockstep
    all_goals
      intro o st' hh
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hh)
      refine ⟨_, _, rfl, ⟨_, hm, ?_⟩, by assumption, by assumption⟩
      simp only [Prod.mk.injEq, and_true]
      by_cases hij : i = ‹Std.U64›
      · subst hij; simp
      · have : (i : Std.U64).val ≠ (‹Std.U64› : Std.U64).val := fun hv => hij (UScalar.eq_of_val_eq hv)
        simp [hij, this]

end hlb

@[lockstep] theorem has_loose_bvar_b_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : ExprOps.WMemoRel rm lm) (i fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LS pers (fun a b => ∃ m', ExprOps.WMemoRel a.2 m' ∧ b = (a.1, m'))
      (arena.core.has_loose_bvar_b_go pers st rm i fuel h) lst
      (hasLooseBVarBGo lm (absU i) (absU fuel) (absEIdx h)) :=
  has_loose_bvar_b_go_aux _ rm lm i fuel h rfl hrel hinv hm

/-- `has_loose_bvar_b_fast` ⊑ `hasLooseBVarBFast`: one memoised walk from the
empty memo. -/
@[lockstep] theorem has_loose_bvar_b_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (arena.core.has_loose_bvar_b_fast pers st i e) lst
      (hasLooseBVarBFast (absU i) (absEIdx e)) := by
  rw [arena.core.has_loose_bvar_b_fast, hasLooseBVarBFast]
  lockstep

/-- `struct_used_later` ⊑ `structUsedLater`: field `j` is used by a later field. -/
@[lockstep] theorem struct_used_later_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cty : arena.handle.EIdx) (n_p j : Std.U64) :
    LS pers (fun a b => b = a) (arena.core.struct_used_later pers st cty n_p j) lst
      (structUsedLater (absEIdx cty) (absU n_p) (absU j)) := by
  rw [arena.core.struct_used_later, structUsedLater]
  lockstep

/-! ## The window query -/

/-- The node arms of `hasLooseBVarInGo`, as the Rust's `has_loose_bvar_in_node`. -/
def hlbiNodeT (memo : Std.HashMap (EIdx × Nat) Bool) (w d fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | .app f a => do
    match ← hasLooseBVarInGo memo w d fuel f with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarInGo memo w d fuel a
  | .lam ty b => do
    match ← hasLooseBVarInGo memo w d fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarInGo memo w (d + 1) fuel b
  | .forallE ty b => do
    match ← hasLooseBVarInGo memo w d fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarInGo memo w (d + 1) fuel b
  | .letE t v b => do
    match ← hasLooseBVarInGo memo w d fuel t with
    | (true, memo) => pure (true, memo)
    | (false, memo) => do
      match ← hasLooseBVarInGo memo w d fuel v with
      | (true, memo) => pure (true, memo)
      | (false, memo) => hasLooseBVarInGo memo w (d + 1) fuel b
  | .proj _ _ sub => hasLooseBVarInGo memo w d fuel sub
  | _ => pure (false, memo)

/-- A recursing arm of the window walk: the memo probe, then the node and the
insertion. -/
def hlbiArmT (memo : Std.HashMap (EIdx × Nat) Bool) (w d fuel : Nat) (h : EIdx)
    (v : ENodeView) : AM (Bool × Std.HashMap (EIdx × Nat) Bool) :=
  match memo[(h, d)]? with
  | none => do
    let r ← hlbiNodeT memo w d fuel v
    pure (hasLooseBVarBIns h d r)
  | some r => pure (r, memo)

/-- `hasLooseBVarInGo` at `fuel + 1` in the Rust's shape: the probe repeated in
each recursing arm. -/
theorem hasLooseBVarInGo_succ_split (memo : Std.HashMap (EIdx × Nat) Bool) (w d fuel : Nat)
    (h : EIdx) :
    hasLooseBVarInGo memo w d (fuel + 1) h = (do
      let bb ← bvarB fuel h
      if bb ≤ d then pure (false, memo) else
      match ← view h with
      | .bvar j => pure (decide (d ≤ j) && decide (j - d < w), memo)
      | .fvar _ _ => pure (false, memo)
      | .sort _ => pure (false, memo)
      | .const _ _ => pure (false, memo)
      | .app f a => hlbiArmT memo w d fuel h (.app f a)
      | .lam ty b => hlbiArmT memo w d fuel h (.lam ty b)
      | .forallE ty b => hlbiArmT memo w d fuel h (.forallE ty b)
      | .letE t v b => hlbiArmT memo w d fuel h (.letE t v b)
      | .lit _ => pure (false, memo)
      | .proj s k sub => hlbiArmT memo w d fuel h (.proj s k sub)) := by
  rw [hasLooseBVarInGo]
  refine congrArg _ (funext fun bb => ?_)
  split
  · rfl
  · refine congrArg _ (funext fun v => ?_)
    cases v <;> try rfl
    all_goals
      cases hm : memo[(h, d)]? <;>
        simp only [hlbiArmT, hlbiNodeT, hm, bind_assoc, pure_bind]
      all_goals
        refine congrArg _ (funext fun x => ?_)
        rcases x with ⟨_ | _, m⟩ <;> simp only [pure_bind, bind_assoc]
      all_goals
        refine congrArg _ (funext fun y => ?_)
        rcases y with ⟨_ | _, m'⟩ <;> simp only [pure_bind]

section hlbi
attribute [local lockstep_simp] hlbiArmT hlbiNodeT

theorem has_loose_bvar_in_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool) (lm : Std.HashMap (EIdx × Nat) Bool)
      (w d fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → ExprOps.WMemoRel rm lm →
      LS pers (fun a b => ∃ m', ExprOps.WMemoRel a.2 m' ∧ b = (a.1, m'))
        (arena.core.has_loose_bvar_in_go pers st rm w d fuel h) lst
        (hasLooseBVarInGo lm (absU w) (absU d) n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm w d fuel h hn hrel hinv hm
    rw [arena.core.has_loose_bvar_in_go, hasLooseBVarInGo]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm w d fuel h hn hrel hinv hm
    rw [arena.core.has_loose_bvar_in_go, hasLooseBVarInGo_succ_split]
    unfold arena.core.has_loose_bvar_in_node
    lockstep

end hlbi

@[lockstep] theorem has_loose_bvar_in_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lm : Std.HashMap (EIdx × Nat) Bool} (hm : ExprOps.WMemoRel rm lm) (w d fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LS pers (fun a b => ∃ m', ExprOps.WMemoRel a.2 m' ∧ b = (a.1, m'))
      (arena.core.has_loose_bvar_in_go pers st rm w d fuel h) lst
      (hasLooseBVarInGo lm (absU w) (absU d) (absU fuel) (absEIdx h)) :=
  has_loose_bvar_in_go_aux _ rm lm w d fuel h rfl hrel hinv hm

/-- **`arena::core_state::take_walk_memo` at the window walk's table** (the
`EIdxNat`-keyed instance of `Checker/Base.lean`'s `take_walk_memo_spec`, which
sits above this module): the table it hands the walk is empty and well formed
— the twin's `∅` — and the one it leaves in the slot is well formed. -/
theorem take_walk_memo_wmemo {slot m slot' : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    (hinv : ConRon.Refine.HashMap2.Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable slot)
    (h : arena.core_state.take_walk_memo slot = ok (m, slot')) :
    ExprOps.WMemoRel m ∅ ∧
      ConRon.Refine.HashMap2.Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable slot' := by
  rw [arena.core_state.take_walk_memo] at h
  obtain ⟨hm, hnew, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hi, -, hn⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable) hnew
  simp only [core.mem.replace] at h
  obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    exact ⟨⟨ConRon.Refine.HashMap2.RelOn_empty hn, hi⟩, hi⟩
  · obtain ⟨m1, hm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    rw [arena.core_state.reset_map] at hm1
    obtain ⟨hi1, -, hn1⟩ := ConRon.Refine.HashMap2.clear_fit_refines hinv hm1
    exact ⟨⟨ConRon.Refine.HashMap2.RelOn_empty hn1, hi1⟩, hi⟩

/-- The twin's `pure (← w).1`, run: the walk's run, its memo dropped
(`Checker/Base.lean`'s `run_fst_eq`, which sits above this module). -/
theorem run_fst_eq_core {β M : Type} (w : AM (β × M)) (lst : AState) :
    (do pure (← w).1 : AM β).run lst = (w.run lst) >>= fun p => .ok (p.1.1, p.2) := by
  simp only [StateT.run_bind, StateT.run_pure]
  rcases w.run lst with _ | ⟨⟨b, mm⟩, l⟩ <;> rfl

/-- `has_loose_bvar_in` ⊑ `hasLooseBVarIn`: the window query, one memoised walk.
The walk's memo is the state's parked `hlbi_c` table, moved out and emptied by
`take_walk_memo` and put back afterwards; `MemosRel` has no clause for it, so
the two state updates are invisible to `AStateRel₀`, and `MemosInv.hlbiC` is
carried by the walk's own memo relation. -/
@[lockstep] theorem has_loose_bvar_in_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d w : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (arena.core.has_loose_bvar_in pers st d w e) lst
      (hasLooseBVarIn (absU d) (absU w) (absEIdx e)) := by
  intro o st' hrun
  rw [arena.core.has_loose_bvar_in] at hrun
  rw [hasLooseBVarIn]
  by_cases hw : w = 0#u64
  · rw [if_pos hw] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    have : (absU w == 0) = true := by subst hw; rfl
    simp only [this, ite_true]
    exact ⟨false, lst, rfl, rfl, hrel, hinv⟩
  · rw [if_neg hw] at hrun
    have hw' : (absU w == 0) = false := by
      have : w.val ≠ 0 := fun h0 => hw (UScalar.eq_of_val_eq (by simpa using h0))
      simpa [absU] using this
    simp only [hw', Bool.false_eq_true, ite_false]
    obtain ⟨⟨m, hm⟩, htake, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨hml, hhm⟩ := take_walk_memo_wmemo hinv.memos.hlbiC htake
    obtain ⟨⟨r, st1⟩, hgo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hw2 := has_loose_bvar_in_go_ls
      (st := { st with memos := { st.memos with hlbi_c := hm } })
      ⟨hrel.store, { hrel.memos with }, hrel.caches, hrel.pins⟩
      ⟨hinv.store, { hinv.memos with hlbiC := hhm }, hinv.caches⟩ hml
      w d arena.core.CORE_WALK_FUEL e _ _ hgo
    rw [core_walk_fuel_abs] at hw2
    rw [run_fst_eq_core]
    cases r with
    | Ok a =>
      obtain ⟨a1, a2⟩ := a
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
      obtain ⟨b, lst', hx, ⟨m', hR, hb⟩, h3, h4⟩ := hw2
      subst hb
      exact ⟨a1, lst', by rw [hx]; rfl, rfl,
        ⟨h3.store, { h3.memos with }, h3.caches, h3.pins⟩,
        ⟨h4.store, { h4.memos with hlbiC := hR.2 }, h4.caches⟩⟩
    | Err err =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
      exact AErrSim.trans hw2 (fun le hle => by rw [hle]; rfl)

/-! ## Opening a telescope at fresh free variables -/

theorem open_pis_at_fvars_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (nn : Std.U64) (h : arena.handle.EIdx) (i : Std.U64),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map fun p => (absEIdxList p.1, absEIdx p.2))
        (arena.core.open_pis_at_fvars pers st nn h i) lst
        (openPisAtFvars n (absEIdx h) (absU i)) := by
  induction n with
  | zero =>
    intro pers st lst nn h i hn hrel hinv
    rw [arena.core.open_pis_at_fvars, openPisAtFvars]
    lockstep
  | succ m ih =>
    intro pers st lst nn h i hn hrel hinv
    rw [arena.core.open_pis_at_fvars, openPisAtFvars]
    lockstep

/-- `open_pis_at_fvars` ⊑ `openPisAtFvars`. -/
@[lockstep] theorem open_pis_at_fvars_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : Std.U64) (h : arena.handle.EIdx) (i : Std.U64) :
    LS pers (fun a b => b = a.map fun p => (absEIdxList p.1, absEIdx p.2))
      (arena.core.open_pis_at_fvars pers st n h i) lst
      (openPisAtFvars n.val (absEIdx h) (absU i)) :=
  open_pis_at_fvars_aux _ n h i rfl hrel hinv

theorem open_pis_raw_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (acc : alloc.vec.Vec arena.handle.EIdx) (nn : Std.U64) (h : arena.handle.EIdx)
      (i : Std.U64),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map fun p => (absEIdxList p.1, absEIdxArr p.2.1, absEIdx p.2.2))
        (arena.core.open_pis_raw_go pers st acc nn h i) lst
        (openPisRawGo (absEIdxArr acc) n (absEIdx h) (absU i)) := by
  induction n with
  | zero =>
    intro pers st lst acc nn h i hn hrel hinv
    rw [arena.core.open_pis_raw_go, openPisRawGo]
    lockstep
  | succ m ih =>
    intro pers st lst acc nn h i hn hrel hinv
    rw [arena.core.open_pis_raw_go, openPisRawGo]
    lockstep

/-- `open_pis_raw_go` ⊑ `openPisRawGo`: the one-pass opening, the residual left
raw. -/
@[lockstep] theorem open_pis_raw_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (acc : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64)
    (h : arena.handle.EIdx) (i : Std.U64) :
    LS pers (fun a b => b = a.map fun p => (absEIdxList p.1, absEIdxArr p.2.1, absEIdx p.2.2))
      (arena.core.open_pis_raw_go pers st acc n h i) lst
      (openPisRawGo (absEIdxArr acc) n.val (absEIdx h) (absU i)) :=
  open_pis_raw_go_aux _ acc n h i rfl hrel hinv

/-- `open_pis_at_fvars_f` ⊑ `openPisAtFvarsF`: the raw opening, then the residual
in one pass. -/
@[lockstep] theorem open_pis_at_fvars_f_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : Std.U64) (e : arena.handle.EIdx) (i : Std.U64) :
    LS pers (fun a b => b = a.map fun p => (absEIdxList p.1, absEIdx p.2))
      (arena.core.open_pis_at_fvars_f pers st n e i) lst
      (openPisAtFvarsF n.val (absEIdx e) (absU i)) := by
  rw [arena.core.open_pis_at_fvars_f, openPisAtFvarsF]
  have hgo := open_pis_raw_go_aux n.val (alloc.vec.Vec.new _) n e i rfl hrel hinv
  have h0 : absEIdxArr (alloc.vec.Vec.new arena.handle.EIdx) = #[] := by
    simp [absEIdxArr, alloc.vec.Vec.new]
  rw [h0] at hgo
  lockstep

/-! ## The rows -/

/-- A row vector `(depth, type)`, as the twin's array. -/
def absRows (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) : Array (Nat × EIdx) :=
  (v.val.map fun q => (absU q.1, absEIdx q.2)).toArray


theorem absRows_push {v w : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {x : Std.U64 × arena.handle.EIdx} (h : w.val = v.val ++ [x]) :
    absRows w = (absRows v).push (absU x.1, absEIdx x.2) := by
  simp [absRows, h]

theorem proj_guard_rows_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k d : Std.U64) (h : arena.handle.EIdx)
      (out : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) (x : Nat) (lout : Array (Nat × EIdx)),
      k.val = n → absU d = x → absRows out = lout → AStateRel₀ pers st lst →
      AStateInv pers st →
      LS pers (fun a b => b = a.map absRows)
        (arena.core.proj_guard_rows_go pers st k d h out) lst
        (projGuardRowsGo n x (absEIdx h) lout) := by
  induction n with
  | zero =>
    intro pers st lst k d h out x lout hk hx hout hrel hinv
    subst hout hx
    rw [arena.core.proj_guard_rows_go, projGuardRowsGo]
    lockstep
    all_goals
      refine LS.pure ?_ ‹_› ‹_›
      simp only [Option.map_some, absRows_push ‹_ = _ ++ _›]
  | succ m ih =>
    intro pers st lst k d h out x lout hk hx hout hrel hinv
    subst hout hx
    rw [arena.core.proj_guard_rows_go, projGuardRowsGo]
    lockstep
    all_goals
      refine ih _ _ _ _ _ _ ?_ ?_ ?_ ‹_› ‹_›
      all_goals first
        | (simp only [absU] at *; scalar_tac)
        | simp [absRows, absU, ‹_ = _ ++ _›]

/-- `proj_guard_rows_go` ⊑ `projGuardRowsGo`: the field loop of the official
`infer_proj`, the rows in push order. -/
@[lockstep] theorem proj_guard_rows_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k d : Std.U64) (h : arena.handle.EIdx)
    (out : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    LS pers (fun a b => b = a.map absRows)
      (arena.core.proj_guard_rows_go pers st k d h out) lst
      (projGuardRowsGo k.val (absU d) (absEIdx h) (absRows out)) :=
  proj_guard_rows_go_aux _ k d h out _ _ rfl rfl rfl hrel hinv

theorem proj_guard_fast_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k j : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.core.proj_guard_fast pers st k j h) lst
        (projGuardFast n (absU j) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst k j h hk hrel hinv
    rw [arena.core.proj_guard_fast, projGuardFast]
    lockstep
  | succ m ih =>
    intro pers st lst k j h hk hrel hinv
    rw [arena.core.proj_guard_fast, projGuardFast]
    lockstep

/-- `proj_guard_fast` ⊑ `projGuardFast`: the guard's fast case, read off the raw
telescope. -/
@[lockstep] theorem proj_guard_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k j : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.core.proj_guard_fast pers st k j h) lst
      (projGuardFast k.val (absU j) (absEIdx h)) :=
  proj_guard_fast_aux _ k j h rfl hrel hinv

/-- `proj_guard_rows_at` ⊑ `projGuardRowsAt`: the rows past the parameters' raw
opening. -/
@[lockstep] theorem proj_guard_rows_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (entry : arena.env.IProjEntry)
    (acc : alloc.vec.Vec arena.handle.EIdx) (r : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absRows)
      (arena.core.proj_guard_rows_at pers st entry acc r) lst
      (projGuardRowsAt (absIProjEntry entry) (absEIdxArr acc) (absEIdx r)) := by
  rw [arena.core.proj_guard_rows_at, projGuardRowsAt]
  lockstep
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    simp only [Option.map_some, absRows_push ‹_ = _ ++ _›, Option.some.injEq]
    simp [absRows, alloc.vec.Vec.new, absU, *]

/-- `proj_guard_rows` ⊑ `projGuardRows`: what a `.proj` use on a structure that
may be a proposition must show. -/
@[lockstep] theorem proj_guard_rows_ls {pers st fe lfe lst} (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx pers fe lfe)
    (entry : arena.env.IProjEntry) (us : arena.handle.LsIdx) :
    LS pers (fun a b => b = a.map absRows) (arena.core.proj_guard_rows pers st fe entry us) lst
      (projGuardRows lfe (absIProjEntry entry) (absLsIdx us)) := by
  rw [arena.core.proj_guard_rows, projGuardRows]
  lockstep

/-! ## The former's sort, and the guard sort -/

/-- `former_res_sort` ⊑ `formerResSort`: the sort a stored type ends in, if it is
syntactically one. -/
@[lockstep] theorem former_res_sort_ls {pers st ty lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = a.map absLIdx) (arena.core.former_res_sort pers st ty) st lst
      (formerResSort (absEIdx ty)) := by
  apply LSR.of_LS
  rw [arena.core.former_res_sort, formerResSort]
  lockstep

theorem former_sort_loop_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers st mode eager lane fu fe lfe lst} (d nn : Std.U64) (e : arena.handle.EIdx),
      nn.val = n → ExprOpsHyp pers →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe → absU fu = f →
      LS pers (fun a b => b = a.map absLIdx)
        (arena.core.former_sort_loop pers st mode eager lane fu fe d nn e) lst
        (formerSortLoop (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) (absU d) n
          (absEIdx e)) := by
  induction n with
  | zero =>
    intro pers st mode eager lane fu fe lfe lst d nn e hn hx hrel hinv hctx hf
    rw [arena.core.former_sort_loop, formerSortLoop]
    lockstep
  | succ m ih =>
    intro pers st mode eager lane fu fe lfe lst d nn e hn hx hrel hinv hctx hf
    rw [arena.core.former_sort_loop, formerSortLoop]
    lockstep

/-- `former_sort_loop` ⊑ `formerSortLoop`: the sort a type reaches past `n`
binders, head-normalising at each step. -/
@[lockstep] theorem former_sort_loop_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe d n e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = a.map absLIdx)
      (arena.core.former_sort_loop pers st mode eager lane fu fe d n e) lst
      (formerSortLoop (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) (absU d) n.val
        (absEIdx e)) :=
  former_sort_loop_aux hk _ d n e rfl hx hrel hinv hctx hf

@[lockstep] theorem is_always_zero_ls {l : kernel.level.Level} (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.is_always_zero l)
      (fun b => TwinEq (ConLeche.Level.isAlwaysZero (ConRon.Refine.absLevel l)) b) :=
  fun _ h => (is_always_zero_abs hl h).symm

@[lockstep] theorem zero_where_zero_ls {s u : kernel.level.Level} (hs : ConRon.Refine.LevelWF s)
    (hu : ConRon.Refine.LevelWF u) :
    LSP (kernel.level.zero_where_zero s u)
      (fun b => TwinEq (ConLeche.Level.zeroWhereZero (ConRon.Refine.absLevel s)
        (ConRon.Refine.absLevel u)) b) :=
  fun _ h => (zero_where_zero_abs hs hu h).symm

/-- The twin's `pure (if c then a else b)` as the Rust's branch. -/
theorem pure_ite_am {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (pure (if c then a else b) : AM α) = if c then pure a else pure b := by
  split <;> rfl

attribute [local lockstep_simp] pure_ite_am

/-- `proj_guard_sort` ⊑ `projGuardSort`: the sort a projection's rows answer to. -/
@[lockstep] theorem proj_guard_sort_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe cvt caps us lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => (∀ l, a = some l → ConRon.Refine.LevelWF l) ∧
        b = a.map ConRon.Refine.absLevel)
      (arena.core.proj_guard_sort pers st mode eager lane fu fe cvt caps us) lst
      (projGuardSort (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f)
        (absIConstantVal cvt) (absIIndCaps caps) (absLsIdx us)) := by
  rw [arena.core.proj_guard_sort, projGuardSort]
  lockstep
  all_goals
    rename_i hwf
    obtain ⟨heq, -⟩ := ConRon.Refine.ExprOps.zeroness_of_refines hwf _ hf
    rw [heq] at hc
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
    intro o st' hh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hh)
    exact ⟨_, _, rfl, ⟨by simp_all, by simp⟩, hrel, hinv⟩

@[simp] theorem absRows_size (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    (absRows v).size = v.val.length := by simp [absRows]

theorem absRows_getElem (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) (i : Nat)
    (h : i < (absRows v).size) :
    (absRows v)[i] = (absU (v.val[i]'(by simpa using h)).1, absEIdx (v.val[i]'(by simpa using h)).2) := by
  simp [absRows]

attribute [local lockstep_simp] absRows_size absRows_getElem

theorem check_guard_rows_aux {f : Nat} (hk : KnotRel f) (k : Nat) :
    ∀ {pers st mode eager lane fu fe lfe lst} (g : kernel.level.Level)
      (rows : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) (i : Std.Usize),
      rows.val.length - i.val = k → ConRon.Refine.LevelWF g → ExprOpsHyp pers →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe → absU fu = f →
      LS pers (fun a b => b = a)
        (arena.core.check_guard_rows pers st mode eager lane fu fe g rows i) lst
        (checkGuardRows (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f)
          (ConRon.Refine.absLevel g) (absRows rows) i.val) := by
  induction k with
  | zero =>
    intro pers st mode eager lane fu fe lfe lst g rows i hk' hg hx hrel hinv hctx hf
    rw [arena.core.check_guard_rows, checkGuardRows]
    lockstep
  | succ m ih =>
    intro pers st mode eager lane fu fe lfe lst g rows i hk' hg hx hrel hinv hctx hf
    rw [arena.core.check_guard_rows, checkGuardRows]
    lockstep

/-- `check_guard_rows` ⊑ `checkGuardRows`: each row's domain, inferred at the io
grade and head-normalised, has a sort zero wherever the guard sort is. -/
@[lockstep] theorem check_guard_rows_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe lst} {g : kernel.level.Level}
    (hg : ConRon.Refine.LevelWF g) (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f)
    (rows : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) (i : Std.Usize) :
    LS pers (fun a b => b = a)
      (arena.core.check_guard_rows pers st mode eager lane fu fe g rows i) lst
      (checkGuardRows (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f)
        (ConRon.Refine.absLevel g) (absRows rows) (absSz i)) :=
  check_guard_rows_aux hk _ g rows i rfl hg hx hrel hinv hctx hf

end ConRon.Refine2.Lockstep
