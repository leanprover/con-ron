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

theorem open_pis_at_fvars_f_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (acc : alloc.vec.Vec arena.handle.EIdx) (nn : Std.U64) (h : arena.handle.EIdx)
      (i : Std.U64),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map fun p => (absEIdxList p.1, absEIdx p.2))
        (arena.core.open_pis_at_fvars_f_go pers st acc nn h i) lst
        (openPisAtFvarsFGo (absEIdxArr acc) n (absEIdx h) (absU i)) := by
  induction n with
  | zero =>
    intro pers st lst acc nn h i hn hrel hinv
    rw [arena.core.open_pis_at_fvars_f_go, openPisAtFvarsFGo]
    lockstep
  | succ m ih =>
    intro pers st lst acc nn h i hn hrel hinv
    rw [arena.core.open_pis_at_fvars_f_go, openPisAtFvarsFGo]
    lockstep

/-- `open_pis_at_fvars_f` ⊑ `openPisAtFvarsF`: the one-pass opening, the plain one
as its fallback. -/
@[lockstep] theorem open_pis_at_fvars_f_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : Std.U64) (e : arena.handle.EIdx) (i : Std.U64) :
    LS pers (fun a b => b = a.map fun p => (absEIdxList p.1, absEIdx p.2))
      (arena.core.open_pis_at_fvars_f pers st n e i) lst
      (openPisAtFvarsF n.val (absEIdx e) (absU i)) := by
  rw [arena.core.open_pis_at_fvars_f, openPisAtFvarsF]
  have hgo := open_pis_at_fvars_f_go_aux n.val (alloc.vec.Vec.new _) n e i rfl hrel hinv
  have h0 : absEIdxArr (alloc.vec.Vec.new arena.handle.EIdx) = #[] := by
    simp [absEIdxArr, alloc.vec.Vec.new]
  rw [h0] at hgo
  lockstep

/-! ## The rows -/

/-- A row vector `(depth, type)`, as the twin's array. -/
def absRows (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) : Array (Nat × EIdx) :=
  (v.val.map fun q => (absU q.1, absEIdx q.2)).toArray

theorem absRows_push {v v' : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {q : Std.U64 × arena.handle.EIdx} (h : alloc.vec.Vec.push v q = ok v') :
    absRows v' = (absRows v).push (absU q.1, absEIdx q.2) := by
  simp [absRows, ConRon.Refine.vec_push_val h]

attribute [local lockstep_simp] absRows_push

theorem proj_guard_rows_at_aux (k : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (cty : arena.handle.EIdx) (n_p idx : Std.U64) (fvs : alloc.vec.Vec arena.handle.EIdx)
      (j : Std.U64) (out : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
      (lout : Array (Nat × EIdx)),
      idx.val + 1 - j.val = k → absRows out = lout → AStateRel₀ pers st lst →
      AStateInv pers st →
      LS pers (fun a b => b = absRows a)
        (arena.core.proj_guard_rows_at pers st cty n_p idx fvs j out) lst
        (projGuardRowsAt (absEIdx cty) (absU n_p) (absU idx) (absEIdxList fvs) (absU j)
          lout) := by
  induction k with
  | zero =>
    intro pers st lst cty n_p idx fvs j out lout hk hout hrel hinv
    subst hout
    rw [arena.core.proj_guard_rows_at, projGuardRowsAt]
    lockstep
  | succ m ih =>
    intro pers st lst cty n_p idx fvs j out lout hk hout hrel hinv
    subst hout
    rw [arena.core.proj_guard_rows_at, projGuardRowsAt]
    lockstep
    all_goals
      rename_i a1 hP1 a2 hP2 hw v hdisc
      have hlen : fvs.val.length ≤ Std.Usize.max := fvs.property
      have haa : a.val = n_p.val + j.val := by
        rcases hP with h | h
        · omega
        · exfalso
          have := (Std.UScalar.lt_equiv _ _).mp hc
          rw [alloc.vec.Vec.len_val] at hP2
          have : fvs.length = fvs.val.length := rfl
          omega
      have hv : v = absEIdx (fvs.val[a.val]'hw) := by
        rw [List.getElem?_map, ← haa, List.getElem?_eq_getElem hw] at hdisc
        simp only [Option.map_some, Option.some.injEq] at hdisc
        exact hdisc.symm
      subst hv
      lockstep
      all_goals
        rename_i ty out1 hout1
        have hj : (j.val : Nat) + 1 = absU a := by simp [absU, hP]
        rw [hj]
        exact ih _ _ _ _ _ _ _ (by simp only [absU] at *; omega)
          (by simp [absRows, hout1, absU, hP1]) ‹_› ‹_›

/-- `proj_guard_rows_at` ⊑ `projGuardRowsAt`: the rows of an opened telescope. -/
@[lockstep] theorem proj_guard_rows_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cty : arena.handle.EIdx) (n_p idx : Std.U64)
    (fvs : alloc.vec.Vec arena.handle.EIdx) (j : Std.U64)
    (out : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    LS pers (fun a b => b = absRows a)
      (arena.core.proj_guard_rows_at pers st cty n_p idx fvs j out) lst
      (projGuardRowsAt (absEIdx cty) (absU n_p) (absU idx) (absEIdxList fvs) (absU j)
        (absRows out)) :=
  proj_guard_rows_at_aux _ cty n_p idx fvs j out _ rfl rfl hrel hinv

theorem absRows_new : absRows (alloc.vec.Vec.new (Std.U64 × arena.handle.EIdx)) = #[] := by
  simp [absRows, alloc.vec.Vec.new]

attribute [local lockstep_simp] absRows_new

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
