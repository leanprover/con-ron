/-
# `ConRon.Refine2.Core.LS.WhnfCore` — region D: the `whnfCore` body, the batched β spine

Task #97-P5-Core round 5, region D; task #119 (con-leche's task #342 R2, the
`WhnfStep` loops).  The lockstep lemmas of `arena::core::beta_peel` and
`whnf_app` (the batched β spine: each RETURNS its continuation, a
`WhnfStep`), `reduce_proj_core` (`Arena.reduceProjCore`, the projection rule,
shared with the defeq tier's `lazy_delta_proj_fields`; its fragments
`reduce_proj_core_at`, `reduce_proj_core_fire` are inlined), the step
`whnf_core_step` (with `whnf_core_step_proj`), and the loop
`whnf_core_loop_loop` / `whnf_core_loop` / `whnf_core_body` (`BodyRel`'s
`whnfCore` field) — Aeneas's `-loops-to-rec` spelling of the Rust loop, one
induction on the step budget against the twin's `whnfCoreLoop`.  The
official kernel's `cheap_proj` flag (task #109) is an argument on both sides
and is threaded unchanged.
-/
import ConRon.Refine2.Core.LS.PrimsD
import ConRon.Refine2.Core.LS.Shapes
import ConRon.Refine2.Core.LS.Iota

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg ConRon.Refine2.Lockstep.PC1.CoreLSReg ConRon.Refine2.Lockstep.PC2.CoreLSReg ConRon.Refine2.Lockstep.PD.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `PrimsB`/`PrimsE` unfold the record abstraction only locally now (the
-- Checker lane reads it folded); the Core region files read it unfolded
attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PD

/-! ## The step's answer -/

/-- `arena::core::WhnfStep` as the twin's `WhnfStep`, constructor for
constructor. -/
def absWhnfStep : arena.core.WhnfStep → WhnfStep
  | .Done e => .done (absEIdx e)
  | .Cont e => .cont (absEIdx e)

attribute [local lockstep_simp] absWhnfStep

attribute [lockstep_inline] arena.core.reduce_proj_core_at arena.core.reduce_proj_core_fire
  arena.core.intern_app

/-! ## The batched β spine: `beta_peel` / `whnf_app`

Each on the spine's remaining length `args.size - i` (the twin's
`termination_by args.size - i`); `beta_peel` no longer calls back into
`whnf_app` (a finished peel returns `.cont`), so the two inductions are
separate. -/

section spine

theorem map_getElem!_absEIdx (l : List arena.handle.EIdx) (i : Nat) (h : i < l.length) :
    (l.map absEIdx).toArray[i]! = absEIdx l[i] := by
  rw [getElem!_pos (l.map absEIdx).toArray i (by simpa using h)]
  simp

attribute [local lockstep_simp] absEIdxArr ExprOps.absEIdxL List.push_toArray
  List.map_append List.map_cons List.map_nil List.nil_append List.size_toArray
  List.length_map List.getElem_toArray List.getElem_map map_getElem!_absEIdx

theorem beta_peel_aux (n : Nat) :
    ∀ {pers st t acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absWhnfStep a)
        (arena.core.beta_peel pers st t acc args i) lst
        (betaPeel (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers st t acc args i lst hx hn hrel hinv
    rw [arena.core.beta_peel, betaPeel]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
  | succ k ih =>
    intro pers st t acc args i lst hx hn hrel hinv
    rw [arena.core.beta_peel, betaPeel]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core

@[lockstep] theorem beta_peel_ls {pers st t acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.beta_peel pers st t acc args i) lst
      (betaPeel (absEIdx t) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  beta_peel_aux _ hx rfl hrel hinv

theorem whnf_app_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers st mode eager lane fu fe lfe depth v hd vargs same args nodes i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe → absU fu = f →
      LS pers (fun a b => b = absWhnfStep a)
        (arena.core.whnf_app pers st mode eager lane fu fe depth v hd vargs same args nodes i) lst
        (whnfApp (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f)
          lfe (absU depth) (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
          (absEIdxArr nodes) (absSz i)) := by
  induction n with
  | zero =>
    intro pers st mode eager lane fu fe lfe depth v hd vargs same args nodes i lst hx hn hrel
      hinv hctx hf
    rw [arena.core.whnf_app, whnfApp]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
  | succ k ih =>
    intro pers st mode eager lane fu fe lfe depth v hd vargs same args nodes i lst hx hn hrel
      hinv hctx hf
    rw [arena.core.whnf_app, whnfApp]
    by_cases hi : i.val < args.val.length
    · rw [dite_eq_left (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core
    · rw [dite_eq_right (by simpa [absEIdxArr, ExprOps.absEIdxL] using hi)]
      lockstep_core

/-- `arena::core::whnf_app` against `Arena.whnfApp`. -/
@[lockstep] theorem whnf_app_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe depth v hd vargs same args nodes i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_app pers st mode eager lane fu fe depth v hd vargs same args nodes i) lst
      (whnfApp (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f)
        lfe (absU depth) (absEIdx v) (absEIdx hd) (absEIdxArr vargs) same (absEIdxArr args)
        (absEIdxArr nodes) (absSz i)) :=
  whnf_app_aux hk _ hx rfl hrel hinv hctx hf

end spine

/-! ## The projection rule: `reduce_proj_core` -/

@[lockstep] theorem reduce_proj_core_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe depth sn i c lst}
    (_hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.reduce_proj_core pers st mode eager lane fu fe depth sn i c) lst
      (reduceProjCore (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe (absU depth) (absNIdx sn)
        (absU i) (absEIdx c)) := by
  rw [arena.core.reduce_proj_core, reduceProjCore]
  lockstep_core

/-! ## The stuck spine: `is_stuck_head`, `iota_target`, `whnf_stuck` -/

attribute [lockstep_inline] arena.core.is_stuck_head

attribute [local lockstep_simp] isStuckHead

@[lockstep] theorem iota_target_ls {pers st fe lfe h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) :
    LSR pers (fun a b => b = a.map absU)
      (arena.core.iota_target pers st fe h) st lst (iotaTarget lfe (absEIdx h)) := by
  apply LSR.of_LS
  rw [arena.core.iota_target, iotaTarget]
  lockstep_c2

@[lockstep] theorem whnf_stuck_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe depth h e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_stuck pers st mode eager lane fu fe depth h e) lst
      (whnfStuck (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe (absU depth) (absEIdx h)
        (absEIdx e)) := by
  rw [arena.core.whnf_stuck, whnfStuck]
  lockstep_core
  -- glue: the ι target's `u64 as usize` cast keeps its value, the target being
  -- at most the spine's length
  rcases hP with hP | hP
  · rw [← hP]
    lockstep_core
  · exfalso
    scalar_tac

@[lockstep] theorem whnf_core_step_app_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe cheap depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_core_step_app pers st mode eager lane fu fe cheap depth e) lst
      (whnfCoreStepApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe cheap (absU depth)
        (absEIdx e)) := by
  rw [arena.core.whnf_core_step_app, whnfCoreStepApp]
  lockstep_core

/-! ## The memo policy: the keys, the pending vectors, the chain store, the lookup -/

section policy

attribute [lockstep_inline] arena.core.whnf_core_store_keys arena.core.whnf_core_store_cheap_keys


/-- The loop's easy-case test against the twin's, off the tag. -/
theorem whnf_core_stuck_tag_abs {e : arena.handle.EIdx} {b : Bool}
    (h : arena.core.whnf_core_stuck_tag e = ok b) :
    b = whnfCoreStuckTag (absEIdx e) := by
  rw [arena.core.whnf_core_stuck_tag] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [whnfCoreStuckTag, eidx_tag_abs ht]
  by_cases h1 : t = arena.handle.ETAG_APP
  · rw [ite_eq_left h1] at h
    rw [ite_eq_left ((etag_dec etag_app_abs).mpr h1)]
    exact (Result.ok_injective h).symm
  · rw [ite_eq_right h1] at h
    rw [ite_eq_right (fun hx => h1 ((etag_dec etag_app_abs).mp hx))]
    by_cases h2 : t = arena.handle.ETAG_PROJ
    · rw [ite_eq_left h2] at h
      rw [ite_eq_left ((etag_dec etag_proj_abs).mpr h2)]
      exact (Result.ok_injective h).symm
    · rw [ite_eq_right h2] at h
      rw [ite_eq_right (fun hx => h2 ((etag_dec etag_proj_abs).mp hx))]
      by_cases h3 : t = arena.handle.ETAG_LET_E
      · rw [ite_eq_left h3] at h
        rw [ite_eq_left ((etag_dec etag_letE_abs).mpr h3)]
        exact (Result.ok_injective h).symm
      · rw [ite_eq_right h3] at h
        rw [ite_eq_right (fun hx => h3 ((etag_dec etag_letE_abs).mp hx))]
        by_cases h4 : t = arena.handle.ETAG_BVAR
        · rw [ite_eq_left h4] at h
          rw [ite_eq_left ((etag_dec etag_bvar_abs).mpr h4)]
          exact (Result.ok_injective h).symm
        · rw [ite_eq_right h4] at h
          rw [ite_eq_right (fun hx => h4 ((etag_dec etag_bvar_abs).mp hx))]
          exact (Result.ok_injective h).symm

theorem is_stuck_head_eq {h : arena.handle.EIdx} {b : Bool}
    (hb : arena.core.is_stuck_head h = ok b) : b = isStuckHead (absEIdx h) := by
  rw [arena.core.is_stuck_head] at hb
  obtain ⟨t, ht, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
  simp only [isStuckHead, eidx_tag_abs ht]
  simp only [← etag_dec etag_sort_abs, ← etag_dec etag_fvar_abs, ← etag_dec etag_forallE_abs,
    ← etag_dec etag_const_abs, ← etag_dec etag_lit_abs] at hb
  split_ifs at hb ⊢ <;> exact (Result.ok_injective hb).symm

/-- `arena::core::whnf_core_key` against `whnfCoreKey`. -/
@[lockstep] theorem whnf_core_key_ls (h e : arena.handle.EIdx) :
    LSP (arena.core.whnf_core_key h e) (fun b => b = whnfCoreKey (absEIdx h) (absEIdx e)) := by
  intro b hb
  rw [arena.core.whnf_core_key] at hb
  obtain ⟨t, ht, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
  simp only [whnfCoreKey, eidx_tag_abs ht]
  simp only [← etag_dec etag_app_abs, ← etag_dec etag_proj_abs, ← etag_dec etag_letE_abs] at hb
  split_ifs at hb ⊢
  · obtain ⟨c, hc, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
    rw [← is_stuck_head_eq hc]
    exact (Result.ok_injective hb).symm
  all_goals exact (Result.ok_injective hb).symm

/-- `arena::core::whnf_core_cheap_safe` against `whnfCoreCheapSafe`. -/
@[lockstep] theorem whnf_core_cheap_safe_ls (h e : arena.handle.EIdx) :
    LSP (arena.core.whnf_core_cheap_safe h e)
      (fun b => b = whnfCoreCheapSafe (absEIdx h) (absEIdx e)) := by
  intro b hb
  rw [arena.core.whnf_core_cheap_safe] at hb
  obtain ⟨t, ht, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
  simp only [← etag_dec etag_app_abs, ← etag_dec etag_letE_abs] at hb
  by_cases h1 : (absU32 t == ETag.app) = true
  · rw [ite_eq_left h1] at hb
    obtain ⟨u, hu, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
    simp only [← etag_dec etag_lam_abs] at hb
    simp only [whnfCoreCheapSafe, eidx_tag_abs ht, eidx_tag_abs hu, h1, ite_true]
    by_cases h2 : (absU32 u == ETag.lam) = true
    · rw [ite_eq_left h2] at hb
      rw [ite_eq_left h2]
      exact (Result.ok_injective hb).symm
    · rw [ite_eq_right h2] at hb
      rw [ite_eq_right h2]
      exact is_stuck_head_eq hb
  · rw [ite_eq_right h1] at hb
    simp only [whnfCoreCheapSafe, eidx_tag_abs ht, h1, Bool.false_eq_true, ite_false]
    split_ifs at hb ⊢ <;> exact (Result.ok_injective hb).symm

/-- `arena::core::whnf_core_stores_done` against `whnfCoreStoresDone`. -/
@[lockstep] theorem whnf_core_stores_done_ls (key : Bool) (e v : arena.handle.EIdx) :
    LSP (arena.core.whnf_core_stores_done key e v)
      (fun b => b = whnfCoreStoresDone key (absEIdx e) (absEIdx v)) := by
  intro b hb
  rw [arena.core.whnf_core_stores_done] at hb
  obtain ⟨t, ht, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
  simp only [whnfCoreStoresDone, eidx_tag_abs ht]
  simp only [← etag_dec etag_app_abs] at hb
  split_ifs at hb ⊢
  · obtain ⟨c, hc, hb⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
    rw [eidx_eq2_ls v e c hc] at hb
    cases Result.ok_injective hb
    by_cases hq : absEIdx v = absEIdx e <;> simp [hq]
  all_goals exact (Result.ok_injective hb).symm

theorem push_key_eq {b : Bool} {e : arena.handle.EIdx} {pend a : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.core.push_key b e pend = ok a) :
    pushKey b (absEIdx e) (absEIdxArr pend) = absEIdxArr a := by
  rw [arena.core.push_key] at h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    cases Result.ok_injective h
    rfl
  | true =>
    simp only [ite_true] at h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hv := ConRon.Refine.vec_push_val h
    rw [dupId_eidx _ _ he1] at hv
    simp [ConRon.Arena.pushKey, absEIdxArr, hv]

theorem push_cheap_key_eq {safe b : Bool} {e : arena.handle.EIdx}
    {pend a : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.core.push_cheap_key safe b e pend = ok a) :
    pushCheapKey safe b (absEIdx e) (absEIdxArr pend) = absEIdxArr a := by
  rw [arena.core.push_cheap_key] at h
  cases safe with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    cases Result.ok_injective h
    rfl
  | true =>
    simp only [ite_true] at h
    exact push_key_eq h

/-- A Rust `Bool` read whose every answer is `c`, then the rest. -/
theorem LS.bind_bool {γ δ : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    {f : Result Bool}
    {k : Bool → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {c : Bool} {lst : AState} {x : AM δ}
    (hf : ∀ b, f = ok b → b = c) (hk : LS pers R (k c) lst x) :
    LS pers R (Std.bind f k) lst x := by
  intro o st' hm
  obtain ⟨b, hb, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  rw [hf b hb] at hk1
  exact hk o st' hk1

theorem store_run_bind {α β : Type} (m : AM α) (k : α → AM β) (lst : AState) :
    ((m >>= k)).run lst = (m.run lst) >>= fun p => (k p.1).run p.2 := rfl

theorem lsw_ok_pure {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (ok st) lst (pure ()) := by
  intro st' h
  cases Result.ok_injective h
  exact ⟨(), lst, rfl, trivial, hrel, hinv⟩

theorem LSW.seq {pers : arena.store.PersTier} {f : Result arena.monad.AState}
    {k : arena.monad.AState → Result arena.monad.AState} {lst : AState} {x y : AM Unit}
    (hf : LSW pers f lst x)
    (hk : ∀ st1 lst1, AStateRel₀ pers st1 lst1 → AStateInv pers st1 → LSW pers (k st1) lst1 y) :
    LSW pers (Std.bind f k) lst (x >>= fun _ => y) := by
  intro st' h
  obtain ⟨st1, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, lst1, hx1, -, hrel, hinv⟩ := hf st1 h1
  rw [store_run_bind, hx1]
  exact hk st1 lst1 hrel hinv st' h2

theorem whnf_core_store_keys_loop_aux (n : Nat) :
    ∀ {pers st pend v j lst},
      pend.val.length - (j : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LSW pers (arena.core.whnf_core_store_keys_loop st pend v j) lst
        (whnfCoreStoreKeys (absEIdxArr pend) (absSz j) (absEIdx v)) := by
  induction n with
  | zero =>
    intro pers st pend v j lst hn hrel hinv
    have hi : ¬ j.val < pend.val.length := by omega
    rw [arena.core.whnf_core_store_keys_loop, whnfCoreStoreKeys]
    rw [dite_eq_right (by simpa [absEIdxArr] using hi), ite_eq_left (by scalar_tac)]
    intro st' h
    cases Result.ok_injective h
    exact ⟨(), lst, rfl, trivial, hrel, hinv⟩
  | succ k ih =>
    intro pers st pend v j lst hn hrel hinv
    have hi : j.val < pend.val.length := by omega
    rw [arena.core.whnf_core_store_keys_loop, whnfCoreStoreKeys]
    rw [dite_eq_left (by simpa [absEIdxArr] using hi), ite_eq_right (by scalar_tac)]
    intro st' h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨st1, hs1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hx⟩ := ExprOps.vecIndexAt he
    obtain ⟨lst1, hset, hrel1, hinv1⟩ := SimS₀.apply (whnf_core_set_run hrel hinv hs1)
    have hj1v := absSz_add_one hj1
    have hrec := ih (j := j1) (by simp only [absSz] at hj1v; omega) hrel1 hinv1 st' h
    have hex : (absEIdxArr pend)[absSz j]'(by simpa [absEIdxArr] using hi) = absEIdx e := by
      simp [absEIdxArr, hx]
    rw [hex, store_run_bind, hset, ← hj1v]
    exact hrec

@[lockstep] theorem whnf_core_store_keys_loop_ls {pers st pend v j lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.whnf_core_store_keys_loop st pend v j) lst
      (whnfCoreStoreKeys (absEIdxArr pend) (absSz j) (absEIdx v)) :=
  whnf_core_store_keys_loop_aux _ rfl hrel hinv

theorem whnf_core_store_cheap_keys_loop_aux (n : Nat) :
    ∀ {pers st pend v j lst},
      pend.val.length - (j : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LSW pers (arena.core.whnf_core_store_cheap_keys_loop st pend v j) lst
        (whnfCoreStoreCheapKeys (absEIdxArr pend) (absSz j) (absEIdx v)) := by
  induction n with
  | zero =>
    intro pers st pend v j lst hn hrel hinv
    have hi : ¬ j.val < pend.val.length := by omega
    rw [arena.core.whnf_core_store_cheap_keys_loop, whnfCoreStoreCheapKeys]
    rw [dite_eq_right (by simpa [absEIdxArr] using hi), ite_eq_left (by scalar_tac)]
    intro st' h
    cases Result.ok_injective h
    exact ⟨(), lst, rfl, trivial, hrel, hinv⟩
  | succ k ih =>
    intro pers st pend v j lst hn hrel hinv
    have hi : j.val < pend.val.length := by omega
    rw [arena.core.whnf_core_store_cheap_keys_loop, whnfCoreStoreCheapKeys]
    rw [dite_eq_left (by simpa [absEIdxArr] using hi), ite_eq_right (by scalar_tac)]
    intro st' h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨st1, hs1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hx⟩ := ExprOps.vecIndexAt he
    obtain ⟨lst1, hset, hrel1, hinv1⟩ := SimS₀.apply (whnf_core_cheap_set_run hrel hinv hs1)
    have hj1v := absSz_add_one hj1
    have hrec := ih (j := j1) (by simp only [absSz] at hj1v; omega) hrel1 hinv1 st' h
    have hex : (absEIdxArr pend)[absSz j]'(by simpa [absEIdxArr] using hi) = absEIdx e := by
      simp [absEIdxArr, hx]
    rw [hex, store_run_bind, hset, ← hj1v]
    exact hrec

@[lockstep] theorem whnf_core_store_cheap_keys_loop_ls {pers st pend v j lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.whnf_core_store_cheap_keys_loop st pend v j) lst
      (whnfCoreStoreCheapKeys (absEIdxArr pend) (absSz j) (absEIdx v)) :=
  whnf_core_store_cheap_keys_loop_aux _ rfl hrel hinv

@[lockstep] theorem whnf_core_store_chain_ls {pers st cheap pend pend_c v lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.whnf_core_store_chain st cheap pend pend_c v) lst
      (whnfCoreStoreChain cheap (absEIdxArr pend) (absEIdxArr pend_c) (absEIdx v)) := by
  rw [arena.core.whnf_core_store_chain, whnfCoreStoreChain]
  cases cheap with
  | true =>
    simp only [ite_true]
    exact lsw_ok_pure hrel hinv
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    by_cases h0 : pend.val.length = 0
    · rw [ite_eq_left (by scalar_tac), ite_eq_left (by simpa [absEIdxArr] using h0)]
      exact lsw_ok_pure hrel hinv
    · rw [ite_eq_right (by scalar_tac), ite_eq_right (by simpa [absEIdxArr] using h0)]
      exact LSW.seq (whnf_core_store_keys_loop_ls hrel hinv)
        (fun _ _ h1 h2 => whnf_core_store_cheap_keys_loop_ls h1 h2)

/-- `arena::core::whnf_core_lookup` against `Arena.whnfCoreLookup`: the
mode's table, read. -/
@[lockstep] theorem whnf_core_lookup_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cheap : Bool) (e : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absEIdx a)
      (arena.core.whnf_core_lookup st cheap e) st lst
      (whnfCoreLookup cheap (absEIdx e)) := by
  intro o hrun
  rw [arena.core.whnf_core_lookup] at hrun
  cases cheap with
  | true =>
    simp only [ite_true] at hrun
    have h := whnf_core_cheap_probe_abs hrel hinv hrun
    have hr : (whnfCoreLookup true (absEIdx e)).run lst =
        .ok (lst.caches.whnfCoreCheapC[absEIdx e]?, lst) := rfl
    exact ⟨_, lst, hr, h.symm, hrel, hinv⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hrun
    have h := whnf_core_probe_abs hrel hinv hrun
    have hr : (whnfCoreLookup false (absEIdx e)).run lst =
        .ok (lst.caches.whnfCoreC[absEIdx e]?, lst) := rfl
    exact ⟨_, lst, hr, h.symm, hrel, hinv⟩

/-- `arena::core::whnf_core_lookup_at` against `Arena.whnfCoreLookupAt`: the
mode's table at a key, nothing elsewhere. -/
@[lockstep] theorem whnf_core_lookup_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (key cheap : Bool) (e : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absEIdx a)
      (arena.core.whnf_core_lookup_at st key cheap e) st lst
      (whnfCoreLookupAt key cheap (absEIdx e)) := by
  rw [arena.core.whnf_core_lookup_at, whnfCoreLookupAt]
  cases key with
  | true =>
    simp only [ite_true]
    exact whnf_core_lookup_ls hrel hinv cheap e
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    intro o hrun
    cases Result.ok_injective hrun
    exact ⟨none, lst, rfl, rfl, hrel, hinv⟩

end policy

/-! ## The step: `whnf_core_step` (fragment `whnf_core_step_proj`) -/

@[lockstep] theorem whnf_core_step_proj_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe cheap depth e sn i pe lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_core_step_proj pers st mode eager lane fu fe cheap depth e sn i pe) lst
      (whnfCoreStepProj (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe cheap (absU depth) (absEIdx e)
        (absNIdx sn) (absU i) (absEIdx pe)) := by
  rw [arena.core.whnf_core_step_proj, whnfCoreStepProj]
  lockstep_core

@[lockstep] theorem whnf_core_step_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe cheap depth h e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absWhnfStep a)
      (arena.core.whnf_core_step pers st mode eager lane fu fe cheap depth h e) lst
      (whnfCoreStep (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f)
        lfe cheap (absU depth) (absEIdx h) (absEIdx e)) := by
  rw [arena.core.whnf_core_step, whnfCoreStep]
  lockstep_core

/-! ## The loop: `whnf_core_loop_loop` / `whnf_core_loop` / `whnf_core_body` -/

set_option maxHeartbeats 4000000 in
theorem whnf_core_loop_loop_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers st mode eager lane fu fe lfe cheap depth k cur pend pend_c lst},
      ExprOpsHyp pers → (k : Std.U64).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx pers fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.whnf_core_loop_loop pers st mode eager lane fu fe cheap depth k cur pend
          pend_c) lst
        (whnfCoreLoop (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe cheap (absU depth) n
          (absEIdx cur) (absEIdxArr pend) (absEIdxArr pend_c)) := by
  induction n with
  | zero =>
    intro pers st mode eager lane fu fe lfe cheap depth k cur pend pend_c lst hx hn hrel hinv
      hctx hf
    rw [arena.core.whnf_core_loop_loop, whnfCoreLoop, ite_eq_left (by scalar_tac)]
    lockstep_core
  | succ m ih =>
    intro pers st mode eager lane fu fe lfe cheap depth k cur pend pend_c lst hx hn hrel hinv
      hctx hf
    rw [arena.core.whnf_core_loop_loop, whnfCoreLoop, ite_eq_right (by scalar_tac)]
    -- the easy-case test, read off the tag by hand (`whnf_core_stuck_tag_abs`)
    refine LS.bind_bool (fun b hb => whnf_core_stuck_tag_abs hb) ?_
    by_cases hs : whnfCoreStuckTag (absEIdx cur) = true
    · rw [ite_eq_left hs, ite_eq_left hs]
      lockstep_core
    · rw [ite_eq_right hs, ite_eq_right hs]
      lockstep_core
      -- the pending vectors: the twin's `pushKey`/`pushCheapKey` values are the
      -- port's vectors (`push_key_ls`, `push_cheap_key_ls`)
      all_goals
        rw [push_key_eq ‹arena.core.push_key _ _ _ = ok _›,
          push_cheap_key_eq ‹arena.core.push_cheap_key _ _ _ _ = ok _›]
        lockstep_core

@[lockstep] theorem whnf_core_loop_loop_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe cheap depth k cur pend pend_c lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_core_loop_loop pers st mode eager lane fu fe cheap depth k cur pend
        pend_c) lst
      (whnfCoreLoop (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe cheap (absU depth) (absU k)
        (absEIdx cur) (absEIdxArr pend) (absEIdxArr pend_c)) :=
  whnf_core_loop_loop_aux hk _ hx rfl hrel hinv hctx hf

@[local lockstep_simp] theorem whnf_core_loop_fuel_abs :
    absU arena.core.WHNF_CORE_LOOP_FUEL = whnfCoreLoopFuel := by
  rw [arena.core.WHNF_CORE_LOOP_FUEL, whnfCoreLoopFuel]; rfl

attribute [lockstep_inline] arena.core.whnf_core_loop

/-- **`BodyRel.whnfCore`**, in lockstep: the loop at its own step budget. -/
theorem whnf_core_body_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe cheap depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.whnf_core_body pers st mode eager lane fu fe cheap depth e) lst
      (whnfCoreBody (ConRon.Refine.absMode mode) (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f)
        lfe cheap (absU depth) (absEIdx e)) := by
  rw [arena.core.whnf_core_body, whnfCoreBody]
  lockstep_core

end ConRon.Refine2.Lockstep
