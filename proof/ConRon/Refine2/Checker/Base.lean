/-
# `ConRon.Refine2.Checker.Base` — Theorem 2 for `arena::checker_base` and `arena::checker_split`

**Task #97-P5-Checker**, deliverable 2 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{checker_base,checker_split}.rs` against
`proof/ConRon/Arena/{CheckerBase,CheckerSplit}.lean`: the declaration
checker's common ground — the per-declaration constant check, the two
memoised guard walks, the declared parameter count, the attempt bracket — and
the install/check seam of a value declaration.

## The attempt seam is lockstep (tasks #97-T2-LOCKSTEP D4, D4b)

`orElseAttempt` (DESIGN §8.3 and task #97-LC's ledger row) used to be the one
seam where (B) and (C) were not the same state: the port restored the memos
and the caches and KEPT the store, while the twin's error arm (a throw in
`StateT AState (Except ε)` carries no state) resumes at the pre-attempt
state.  The kept scratch nodes lengthened the port's scratch tier, so every
later scratch handle had a different word — no relation short of a renaming
absorbs that, and it is why `Refine2/Shape.lean`'s old `AOut` carried `Ext`.

The maintainer's rulings moved the Rust: D4 restored the scratch tiers too,
which is the whole state only given a frame over the attempt (the old
`ScratchFrame`: pins, persistent tiers and flags untouched — a statement over
the attempt's 1 187-function closure); D4b made `attempt_snapshot` a FULL
copy of the state and `attempt_restore` a move of it back; D4c moved the
persistent tier aside around that copy; task #98-FREEZE made opening the
declaration bracket the freeze, so the attempt, which runs inside it, copies
a frozen store and moves nothing itself.  So the snapshot is the identity in
the model (`attempt_snapshot_eq`, from the `dup` lemmas below),
`attempt_restore` is `ok snap`, and all of it is lockstep with no hypothesis
about the attempt.  The seam itself is `Refine2/Checker/DeclCheck.lean`'s
`check_div_mod_pin_attempt_refines₀`.

## Finding 10 — `vis` out of the index is a hypothesis at seventy-one sites

Task #97-P6-6b took the visibility counter OUT of the environment record's
read path: `ifenv_find(vis, fe, n)` takes `vis : u64` beside `fe`, because
reading `fe.visible_below` inside the call forced a copy of the record.  The
twin's `IFEnv.find?` reads `fe.visibleBelow`.  So every statement whose Rust
takes a `vis` parameter carries

    hvis : absU vis = lf.visibleBelow

and it is discharged at the top by `IFEnvRel.visibleBelow` — the call sites
all pass `fe.visible_below` — but must be threaded through the tier, because
inside it `vis` is an ordinary argument.  **Seventy-one statements of this
tier carry it**, and like task #97-P5-0's finding 3
it is a fact about the port's own calling convention rather than a
divergence.

## Where `hvis` is FALSE, and the nine statements that dropped it

**Task #97-P5-Bracket's finding 3, repaired by task #97-P5-Checker round 3.**
*"The call sites all pass `fe.visible_below`"* is true of phase A and false of
phase B.  `arena::checker::check_pending` (`checker.rs:1229`) passes
`pc.vis` — the counter the pending declaration was installed at — against the
WHOLE environment phase A ended with, and that difference is the entire point
of phase B.  Paired with `hfe : IFEnvRel rf lf`, whose third clause is
`lf.visibleBelow = absU rf.visible_below`, the `hvis` above forces
`vis = rf.visible_below`: the statement is then satisfiable nowhere on phase
B's path, and `check_pending_refines` has nothing to be proved from.

The repair moves the restriction from the hypothesis to the CONCLUSION:
`hfe` stays at the unrestricted environment, `hvis` goes, and the twin is
called at `lf.restrictTo (absU vis)` — which is what the twin's own
`checkValueGroup mode (fe.restrictTo pc.vis) pc.vg` says anyway.  The old form
is recovered at a phase-A call site by rewriting with `IFEnvRel.visibleBelow`,
since `lf.restrictTo lf.visibleBelow = lf`.

**Which nine.**  Exactly the functions the port can reach from
`check_value_group` while still threading that `vis`, computed from the Rust
call graph and no wider: `check_value_group`, `check_value_group_value`,
`check_value_group_tail`, `install_value`, `install_value_tail`
(`arena::checker_split`) and `consts_resolve_f_{go,node,two,fast}`
(`arena::checker_base`).  The rest of the closure is `arena::core`'s, where
the same repair is `Refine2/Core/KnotRel.lean`'s `CoreCtx` (its `fenv` clause
is now `IFEnvRel fe (lfe.restrictTo (absU fe.visible_below))`, so the counter
is the `vis` clause's business alone) — and `arena::prop_read`'s five readers
and `arena::env::ifenv_find_proj`, which have no `Refine2` tier yet and must
take the general form when they get one.

Every OTHER `hvis` of this tier and of `Refine2/Checker/DeclCheck.lean` is
sound as it stands: those functions are phase A's, where the port really is
only ever called at `fe.visible_below`.

## What these lemmas wait on

`Refine2/Specs.lean`'s `view`/`intern_e` family, `Refine2/ExprOps/**`
(statements only when this was written; all closed now) and
`Refine2/Core/**` — P5-Core's tier, which is where `annotateCore`,
`inferTypeCore`, `isDefEqCore` and `ensureSortCore` live.  `KnotRel` carries
them here (`Refine2/Checker/KnotHyp.lean`).
-/
import ConRon.Refine2.Checker.Axioms
import ConRon.Refine2.Checker.Spec
import ConRon.Refine2.Checker.Leaves

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (NameWF NamesWF ExprWF)

/-! ## The attempt bracket — lockstep since task #97-T2-LOCKSTEP D4b -/

/-! ### The copies are the identity

Every `Dup` dictionary the snapshot copies with returns its argument in the
model: the handles, `u64`, `LDer` and the node records by `Refine2/Inv.lean`
and `Refine2/Specs.lean`; the key records, `bool`, and task #97-T2-LOCKSTEP
D4's `Level`/`Name`/`Vec<Level>` here.  `HashMap2::dup` is then the identity
(`Refine/HashMap2.lean`'s `dup_spec`), `Tbl::dup`'s halved row walk copies
row by row (`tbl_dup_rows_spec`, the shape of `HashMap2`'s `dup_slots_spec`),
and each `dup` is literally `o = input`; `vec_dup`'s halved walk
(`vec_dup_range_spec`) likewise, and so the four stores' `dup`, `pins_dup` and
the whole-state `attempt_snapshot` (task #97-T2-LOCKSTEP D4b). -/

section DupCopies

open ConRon.Refine.HashMap (DupId)

theorem dupId_bool : DupId Bool.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm
theorem dupId_eidxNat : DupId arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2, bind_tc_ok, ok.injEq] at h
  exact h.symm
theorem dupId_eidxPair : DupId arena.core_state.EIdxPair.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [arena.core_state.EIdxPair.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2, bind_tc_ok, ok.injEq] at h
  exact h.symm
theorem dupId_lidxPair : DupId arena.core_state.LIdxPair.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [arena.core_state.LIdxPair.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2, bind_tc_ok, ok.injEq] at h
  exact h.symm
theorem dupId_lsidxPair : DupId arena.core_state.LsIdxPair.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [arena.core_state.LsIdxPair.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2, bind_tc_ok, ok.injEq] at h
  exact h.symm
theorem dupId_nlsKey : DupId arena.core_state.NLsKey.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [arena.core_state.NLsKey.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2, bind_tc_ok, ok.injEq] at h
  exact h.symm
theorem dupId_nnlsKey : DupId arena.core_state.NNLsKey.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [arena.core_state.NNLsKey.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2, bind_tc_ok, ok.injEq] at h
  exact h.symm
theorem dupId_level : DupId kernel.level.Level.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [kernel.level.Level.Insts.Con_ron_coreRonHashmapDup.dup2,
    ConRon.Refine.level_dup_eq, ok.injEq] at h
  exact h.symm
theorem dupId_name : DupId kernel.name.Name.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  simp only [kernel.name.Name.Insts.Con_ron_coreRonHashmapDup.dup2,
    ConRon.Refine.name_dup_eq, ok.injEq] at h
  exact h.symm
theorem dupId_vecLevel : DupId alloc.vec.VecLevel.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h
  exact alloc.vec.Vec.ext _ _ (level_list_dup_val h)

open ConRon.Refine.HashMap (take_one_drop uscalar_sub_eq uscalar_div_eq uscalar_add_eq vec_push_eq)

/-- `Tbl::dup_rows` copies `src[lo..hi]` onto `out`, halving as
`HashMap2::dup_slots` does; under `DupId` on both columns each row is itself. -/
theorem tbl_dup_rows_spec {A I D : Type} {HA : ron.hashmap.Hashable A}
    {EA : ron.hashmap.Eq2 A} {DA : ron.hashmap.Dup A} {DI : ron.hashmap.Dup I}
    {DD : ron.hashmap.Dup D} {DDef : arena.store.DerDefault D}
    (hA : DupId DA) (hD : DupId DD) (N : Nat) :
    ∀ (src out out' : alloc.vec.Vec (A × D)) (lo hi : Std.Usize),
      hi.val - lo.val = N → hi.val ≤ src.val.length →
      arena.store.Tbl.dup_rows HA EA DA DI DD DDef src out lo hi = ok out' →
      out'.val = out.val ++ (src.val.drop lo.val).take (hi.val - lo.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro src out out' lo hi hN hhi h
    rw [arena.store.Tbl.dup_rows.eq_def] at h
    split at h
    · rename_i hgt
      have hlt : lo.val < hi.val := by scalar_tac
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · rename_i h1
        have hn1 : hi.val = lo.val + 1 := by
          have : n.val = 1 := by scalar_tac
          omega
        have hlo : lo.val < src.val.length := by omega
        have : Inhabited (A × D) := ⟨src.val[lo.val]⟩
        obtain ⟨⟨a, d⟩, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨-, hx⟩ := ConRon.Refine.HashMap.vec_index_eq ha
        obtain ⟨a', ha', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨d', hd', hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [hA _ _ ha', hD _ _ hd'] at hp
        rw [vec_push_eq hp, hn1, show lo.val + 1 - lo.val = 1 by omega,
          take_one_drop hlo, hx]
      · rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          omega
        obtain ⟨i, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨mid, hmid, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨out1, hs1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hiv : i.val = n.val / 2 := by
          rw [uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv : mid.val = lo.val + i.val := uscalar_add_eq hmid
        have e1 := ih (mid.val - lo.val) (by omega) src out out1 lo mid rfl (by omega) hs1
        have e2 := ih (hi.val - mid.val) (by omega) src out1 out' mid hi rfl hhi h2
        rw [e2, e1, List.append_assoc,
          show hi.val - lo.val = (mid.val - lo.val) + (hi.val - mid.val) by omega,
          List.take_add, List.drop_drop,
          show lo.val + (mid.val - lo.val) = mid.val by omega]
    · rename_i hgt
      have hle : hi.val ≤ lo.val := by scalar_tac
      rw [← Result.ok_injective h, show hi.val - lo.val = 0 by omega]
      simp

/-- **`Tbl::dup` is the identity**: the row column by `dup_rows`, the cons
table by `HashMap2::dup`. -/
theorem tbl_dup_eq {A I D : Type} {HA : ron.hashmap.Hashable A}
    {EA : ron.hashmap.Eq2 A} {DA : ron.hashmap.Dup A} {DI : ron.hashmap.Dup I}
    {DD : ron.hashmap.Dup D} {DDef : arena.store.DerDefault D}
    (hA : DupId DA) (hI : DupId DI) (hD : DupId DD) {t o : arena.store.Tbl A I D}
    (h : arena.store.Tbl.dup HA EA DA DI DD DDef t = ok o) : o = t := by
  rw [arena.store.Tbl.dup] at h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hr := tbl_dup_rows_spec hA hD _ t.rows _ v1 0#usize (alloc.vec.Vec.len t.rows) rfl
    (by simp) hv1
  have hc := ConRon.Refine.HashMap2.dup_spec hA hI hhm
  rw [← Result.ok_injective h, hc]
  obtain ⟨rows, cons⟩ := t
  simp only at hr ⊢
  congr
  exact alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.with_capacity] using hr)


/-- Discharges a `DupId` goal at every dictionary the snapshot copies with. -/
local macro "dup_id" : tactic => `(tactic| first
  | exact dupId_eidx | exact dupId_nidx | exact dupId_lidx | exact dupId_lsidx
  | exact dupId_bmidx | exact dupId_u64 | exact dupId_bool | exact dupId_lder
  | exact dupId_eidxNat | exact dupId_eidxPair | exact dupId_lidxPair
  | exact dupId_lsidxPair | exact dupId_nlsKey | exact dupId_nnlsKey
  | exact dupId_level | exact dupId_name | exact dupId_vecLevel
  | exact dupId_bvarnode | exact dupId_fvarnode | exact dupId_sortnode
  | exact dupId_constnode | exact dupId_appnode | exact dupId_projnode
  | exact dupId_letnode | exact dupId_bindnode | exact dupId_litnode
  | exact dupId_bmnode | exact dupId_anonnode | exact dupId_strnode
  | exact dupId_numnode | exact dupId_zeronode | exact dupId_succnode
  | exact dupId_binlnode | exact dupId_paramnode | exact dupId_listnode)

-- One copy step of a `dup` chain: the copied field is the field.
set_option hygiene false in
local macro "dup_step" : tactic => `(tactic|
  (obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
   first
   | obtain rfl := ConRon.Refine.HashMap2.dup_spec (by dup_id) (by dup_id) hx
   | obtain rfl := tbl_dup_eq (by dup_id) (by dup_id) (by dup_id) hx))

theorem memos_dup_eq {rm o : arena.monad.Memos}
    (h : arena.checker_base.memos_dup rm = ok o) : o = rm := by
  unfold arena.checker_base.memos_dup at h
  repeat dup_step
  rw [← Result.ok_injective h]

theorem caches_dup_eq {rc o : arena.core_state.Caches}
    (h : arena.checker_base.caches_dup rc = ok o) : o = rc := by
  unfold arena.checker_base.caches_dup at h
  repeat dup_step
  rw [← Result.ok_injective h]

theorem etables_dup_eq {rt o : arena.store.ETables}
    (h : arena.store.ETables.dup rt = ok o) : o = rt := by
  unfold arena.store.ETables.dup at h
  repeat dup_step
  rw [← Result.ok_injective h]

theorem lstables_dup_eq {rt o : arena.store.LsTables}
    (h : arena.store.LsTables.dup rt = ok o) : o = rt := by
  unfold arena.store.LsTables.dup at h
  repeat dup_step
  rw [← Result.ok_injective h]

theorem ltables_dup_eq {rt o : arena.store.LTables}
    (h : arena.store.LTables.dup rt = ok o) : o = rt := by
  unfold arena.store.LTables.dup at h
  repeat dup_step
  rw [← Result.ok_injective h]

theorem ntables_dup_eq {rt o : arena.store.NTables}
    (h : arena.store.NTables.dup rt = ok o) : o = rt := by
  unfold arena.store.NTables.dup at h
  repeat dup_step
  rw [← Result.ok_injective h]

/-- `checker_base::vec_dup_range` copies `xs[lo..hi]` onto `out`, halving as
`Tbl::dup_rows` does; under `DupId` each element is itself. -/
theorem vec_dup_range_spec {T : Type} {DT : ron.hashmap.Dup T} (hT : DupId DT)
    (N : Nat) :
    ∀ (xs out out' : alloc.vec.Vec T) (lo hi : Std.Usize),
      hi.val - lo.val = N → hi.val ≤ xs.val.length →
      arena.checker_base.vec_dup_range DT xs out lo hi = ok out' →
      out'.val = out.val ++ (xs.val.drop lo.val).take (hi.val - lo.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs out out' lo hi hN hhi h
    rw [arena.checker_base.vec_dup_range.eq_def] at h
    split at h
    · rename_i hgt
      have hlt : lo.val < hi.val := by scalar_tac
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnv : n.val = hi.val - lo.val := uscalar_sub_eq hn
      split at h
      · rename_i h1
        have hn1 : hi.val = lo.val + 1 := by
          have : n.val = 1 := by scalar_tac
          omega
        have hlo : lo.val < xs.val.length := by omega
        have : Inhabited T := ⟨xs.val[lo.val]⟩
        obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨-, hx⟩ := ConRon.Refine.HashMap.vec_index_eq ht
        obtain ⟨t', ht', hp⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [hT _ _ ht'] at hp
        rw [vec_push_eq hp, hn1, show lo.val + 1 - lo.val = 1 by omega,
          take_one_drop hlo, hx]
      · rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          omega
        obtain ⟨i, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨mid, hmid, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨out1, hs1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hiv : i.val = n.val / 2 := by
          rw [uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv : mid.val = lo.val + i.val := uscalar_add_eq hmid
        have e1 := ih (mid.val - lo.val) (by omega) xs out out1 lo mid rfl (by omega) hs1
        have e2 := ih (hi.val - mid.val) (by omega) xs out1 out' mid hi rfl hhi h2
        rw [e2, e1, List.append_assoc,
          show hi.val - lo.val = (mid.val - lo.val) + (hi.val - mid.val) by omega,
          List.take_add, List.drop_drop,
          show lo.val + (mid.val - lo.val) = mid.val by omega]
    · rename_i hgt
      have hle : hi.val ≤ lo.val := by scalar_tac
      rw [← Result.ok_injective h, show hi.val - lo.val = 0 by omega]
      simp

/-- **`checker_base::vec_dup` is the identity.** -/
theorem vec_dup_eq {T : Type} {DT : ron.hashmap.Dup T} (hT : DupId DT)
    {xs o : alloc.vec.Vec T} (h : arena.checker_base.vec_dup DT xs = ok o) :
    o = xs := by
  rw [arena.checker_base.vec_dup] at h
  have hr := vec_dup_range_spec hT _ xs _ o 0#usize (alloc.vec.Vec.len xs) rfl
    (by simp) h
  exact alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.with_capacity] using hr)

/-- `pins_dup` is the identity: two `vec_dup`s and three handle copies. -/
theorem pins_dup_eq {p o : arena.pins.Pins}
    (h : arena.checker_base.pins_dup p = ok o) : o = p := by
  unfold arena.checker_base.pins_dup at h
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := vec_dup_eq dupId_nidx hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := vec_dup_eq dupId_nidx hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := dupId_lsidx _ _ hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := dupId_lidx _ _ hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := dupId_eidx _ _ hx
  rw [← Result.ok_injective h]

theorem nstore_dup_eq {s o : arena.store.NStore}
    (h : arena.store.NStore.dup s = ok o) : o = s := by
  unfold arena.store.NStore.dup at h
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := ntables_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := ntables_dup_eq hx
  rw [← Result.ok_injective h]

theorem lstore_dup_eq {s o : arena.store.LStore}
    (h : arena.store.LStore.dup s = ok o) : o = s := by
  unfold arena.store.LStore.dup at h
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := nstore_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := ltables_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := ltables_dup_eq hx
  rw [← Result.ok_injective h]

theorem lsstore_dup_eq {s o : arena.store.LsStore}
    (h : arena.store.LsStore.dup s = ok o) : o = s := by
  unfold arena.store.LsStore.dup at h
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := lstore_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := lstables_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := lstables_dup_eq hx
  rw [← Result.ok_injective h]

theorem estore_dup_eq {s o : arena.store.EStore}
    (h : arena.store.EStore.dup s = ok o) : o = s := by
  unfold arena.store.EStore.dup at h
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := lsstore_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := etables_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := etables_dup_eq hx
  rw [← Result.ok_injective h]

/-- **`attempt_snapshot` is the identity in the model** (task #97-T2-LOCKSTEP
D4b): the store, the memos, the caches and the pins, each copied by a `dup`
that returns its argument. -/
theorem attempt_snapshot_eq {st o : arena.monad.AState}
    (h : arena.checker_base.attempt_snapshot st = ok o) : o = st := by
  unfold arena.checker_base.attempt_snapshot at h
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := estore_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := memos_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := caches_dup_eq hx
  obtain ⟨_, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := pins_dup_eq hx
  rw [← Result.ok_injective h]

end DupCopies

/-- The twin's restore of its own snapshot is the identity — what makes its
error arm "resume at the pre-attempt state". -/
@[simp] theorem attemptRestore_self (s : AState) :
    attemptRestore s (attemptSnapshot s) = s := rfl

/-! ## The name-shape tests

`ConLeche/Kernel/Level.lean`'s three `Name` predicates: the declaration front
door is their only reader.  Each is a handle comparison or one `viewN`. -/

private theorem nidx_contains_from_aux (m : Nat) :
    ∀ {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} {n : arena.handle.NIdx}
      {o : Bool}, ns.val.length - i.val = m →
      arena.checker_base.nidx_contains_from ns i n = ok o →
      o = (absNIdxLFrom ns i).contains (absNIdx n) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro ns i n o hm hrun
    rw [arena.checker_base.nidx_contains_from.eq_def] at hrun
    dsimp only at hrun
    have hl := alloc.vec.Vec.len_val ns
    by_cases hge : i ≥ ns.len
    · have hle : ns.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absNIdxLFrom, List.drop_eq_nil_of_le hle]
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [ite_eq_right hge] at hrun
      obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hlt', rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn1
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := nidx_eq2_abs hb
      have hcons : absNIdxLFrom ns i = absNIdx ns.val[i.val] :: (ns.val.drop (i.val + 1)).map absNIdx := by
        simp only [absNIdxLFrom, List.drop_eq_getElem_cons hlt, List.map_cons]
      rw [hcons, List.contains_cons]
      by_cases hc : b = true
      · rw [ite_eq_left hc] at hrun
        rw [← Result.ok_injective hrun]
        subst hc
        have heq : (absNIdx ns.val[i.val] == absNIdx n) = true := hbv.symm
        rw [BEq.comm] at heq
        simp [heq]
      · rw [ite_eq_right hc] at hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (ns.val.length - i2.val) (by omega) rfl hrun
        have hbf : b = false := by simpa using hc
        subst hbf
        have hne : (absNIdx ns.val[i.val] == absNIdx n) = false := hbv.symm
        rw [BEq.comm] at hne
        rw [hrec, hne]
        simp [absNIdxLFrom, hi2v]

/-- `nidx_contains_from` is `ns.contains n` from the cursor on. -/
theorem nidx_contains_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {n : arena.handle.NIdx} {o : Bool}
    (hrun : arena.checker_base.nidx_contains_from ns i n = ok o) :
    o = (absNIdxLFrom ns i).contains (absNIdx n) :=
  nidx_contains_from_aux _ rfl hrun

/-- `arena::core::nat_op_names` ⊑ `natOpNames` — the seven structural `Nat`
operations, as seven pin reads (task #97-P5-Top: a child of
`annot_step_defn_refines`; the function is `arena::core`'s, but no tier had
stated it). -/
theorem nat_op_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_names st = ok o) :
    Sim₀ absNIdxL pers lst o natOpNames := by
  unfold natOpNames
  rw [arena.core.nat_op_names] at hrun
  unfold Sim₀
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_pred_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_nat_pred_refines hrel hinv hr0
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natPredName) hS0)
  | Ok a0 =>
  rw [pin_ok (tw := natPredName) hS0]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_add_name] at hq1
  obtain ⟨r1, hr1, hq1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq1
  have hS1 := pin_nat_add_refines hrel hinv hr1
  obtain rfl := (Result.ok_injective hq1).symm
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natAddName) hS1)
  | Ok a1 =>
  rw [pin_ok (tw := natAddName) hS1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_sub_name] at hq2
  obtain ⟨r2, hr2, hq2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq2
  have hS2 := pin_nat_sub_refines hrel hinv hr2
  obtain rfl := (Result.ok_injective hq2).symm
  cases r2 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natSubName) hS2)
  | Ok a2 =>
  rw [pin_ok (tw := natSubName) hS2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_mul_name] at hq3
  obtain ⟨r3, hr3, hq3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq3
  have hS3 := pin_nat_mul_refines hrel hinv hr3
  obtain rfl := (Result.ok_injective hq3).symm
  cases r3 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natMulName) hS3)
  | Ok a3 =>
  rw [pin_ok (tw := natMulName) hS3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_pow_name] at hq4
  obtain ⟨r4, hr4, hq4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq4
  have hS4 := pin_nat_pow_refines hrel hinv hr4
  obtain rfl := (Result.ok_injective hq4).symm
  cases r4 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natPowName) hS4)
  | Ok a4 =>
  rw [pin_ok (tw := natPowName) hS4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_beq_name] at hq5
  obtain ⟨r5, hr5, hq5⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq5
  have hS5 := pin_nat_beq_refines hrel hinv hr5
  obtain rfl := (Result.ok_injective hq5).symm
  cases r5 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natBeqName) hS5)
  | Ok a5 =>
  rw [pin_ok (tw := natBeqName) hS5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_ble_name] at hq6
  obtain ⟨r6, hr6, hq6⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq6
  have hS6 := pin_nat_ble_refines hrel hinv hr6
  obtain rfl := (Result.ok_injective hq6).symm
  cases r6 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natBleName) hS6)
  | Ok a6 =>
  rw [pin_ok (tw := natBleName) hS6]
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w1, hw1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w2, hw2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w3, hw3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w4, hw4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w5, hw5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w6, hw6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have hv : w6.val = [a0, a1, a2, a3, a4, a5, a6] := by
    rw [push_nidx_val hw6, push_nidx_val hw5, push_nidx_val hw4, push_nidx_val hw3, push_nidx_val hw2, push_nidx_val hw1, push_nidx_val hw0]
    rfl
  refine ⟨lst, ?_, hrel, hinv⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

/-- `arena::core::nat_div_mod_names` ⊑ `natDivModNames` — the eight pinned
well-founded operations, as eight pin reads (task #97-P5-Top, as above). -/
theorem nat_div_mod_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_div_mod_names st = ok o) :
    Sim₀ absNIdxL pers lst o natDivModNames := by
  unfold natDivModNames
  rw [arena.core.nat_div_mod_names] at hrun
  unfold Sim₀
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_div_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_nat_div_refines hrel hinv hr0
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natDivName) hS0)
  | Ok a0 =>
  rw [pin_ok (tw := natDivName) hS0]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_mod_name] at hq1
  obtain ⟨r1, hr1, hq1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq1
  have hS1 := pin_nat_mod_refines hrel hinv hr1
  obtain rfl := (Result.ok_injective hq1).symm
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natModName) hS1)
  | Ok a1 =>
  rw [pin_ok (tw := natModName) hS1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_gcd_name] at hq2
  obtain ⟨r2, hr2, hq2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq2
  have hS2 := pin_nat_gcd_refines hrel hinv hr2
  obtain rfl := (Result.ok_injective hq2).symm
  cases r2 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natGcdName) hS2)
  | Ok a2 =>
  rw [pin_ok (tw := natGcdName) hS2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_land_name] at hq3
  obtain ⟨r3, hr3, hq3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq3
  have hS3 := pin_nat_land_refines hrel hinv hr3
  obtain rfl := (Result.ok_injective hq3).symm
  cases r3 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natLandName) hS3)
  | Ok a3 =>
  rw [pin_ok (tw := natLandName) hS3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_lor_name] at hq4
  obtain ⟨r4, hr4, hq4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq4
  have hS4 := pin_nat_lor_refines hrel hinv hr4
  obtain rfl := (Result.ok_injective hq4).symm
  cases r4 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natLorName) hS4)
  | Ok a4 =>
  rw [pin_ok (tw := natLorName) hS4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_xor_name] at hq5
  obtain ⟨r5, hr5, hq5⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq5
  have hS5 := pin_nat_xor_refines hrel hinv hr5
  obtain rfl := (Result.ok_injective hq5).symm
  cases r5 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natXorName) hS5)
  | Ok a5 =>
  rw [pin_ok (tw := natXorName) hS5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_shift_left_name] at hq6
  obtain ⟨r6, hr6, hq6⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq6
  have hS6 := pin_nat_shift_left_refines hrel hinv hr6
  obtain rfl := (Result.ok_injective hq6).symm
  cases r6 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natShiftLeftName) hS6)
  | Ok a6 =>
  rw [pin_ok (tw := natShiftLeftName) hS6]
  obtain ⟨q7, hq7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_shift_right_name] at hq7
  obtain ⟨r7, hr7, hq7⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq7
  have hS7 := pin_nat_shift_right_refines hrel hinv hr7
  obtain rfl := (Result.ok_injective hq7).symm
  cases r7 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natShiftRightName) hS7)
  | Ok a7 =>
  rw [pin_ok (tw := natShiftRightName) hS7]
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w1, hw1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w2, hw2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w3, hw3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w4, hw4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w5, hw5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w6, hw6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w7, hw7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have hv : w7.val = [a0, a1, a2, a3, a4, a5, a6, a7] := by
    rw [push_nidx_val hw7, push_nidx_val hw6, push_nidx_val hw5, push_nidx_val hw4, push_nidx_val hw3, push_nidx_val hw2, push_nidx_val hw1, push_nidx_val hw0]
    rfl
  refine ⟨lst, ?_, hrel, hinv⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

private theorem name_nodup_from_aux {ns : alloc.vec.Vec arena.handle.NIdx} (m : Nat) :
    ∀ {i : Std.Usize} {o : Bool}, ns.val.length - i.val = m →
      arena.checker_base.name_nodup_from ns i = ok o →
      o = nameNodup (absNIdxLFrom ns i) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i o hm hrun
    rw [arena.checker_base.name_nodup_from.eq_def] at hrun
    dsimp only at hrun
    have hl := alloc.vec.Vec.len_val ns
    by_cases hge : i ≥ ns.len
    · have hle : ns.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absNIdxLFrom, List.drop_eq_nil_of_le hle, nameNodup]
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [ite_eq_right hge] at hrun
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      obtain ⟨c, hc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨_, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hc
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := nidx_contains_from_refines hb
      have hcons : absNIdxLFrom ns i = absNIdx ns.val[i.val] :: absNIdxLFrom ns i2 := by
        simp only [absNIdxLFrom, List.drop_eq_getElem_cons hlt, List.map_cons, hi2v]
      rw [hcons, nameNodup, ← hbv]
      by_cases hbt : b = true
      · rw [ite_eq_left hbt] at hrun
        rw [← Result.ok_injective hrun, hbt]
        rfl
      · rw [ite_eq_right hbt] at hrun
        have hrec := ih (ns.val.length - i2.val) (by omega) rfl hrun
        have hbf : b = false := by simpa using hbt
        rw [hrec, hbf]
        rfl

/-- `name_nodup_from` ⊑ `nameNodup` from the cursor on. -/
theorem name_nodup_from_refines {ns : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.checker_base.name_nodup_from ns i = ok o) :
    o = nameNodup (absNIdxLFrom ns i) :=
  name_nodup_from_aux _ rfl hrun

/-- `name_nodup` ⊑ `nameNodup` — no duplicates in a list of name HANDLES.  A
name comparison is a handle comparison, which is sound because `denoteN` is
injective (DESIGN §8.3 makes exactness a soundness obligation for exactly this
reason). -/
theorem name_nodup_refines {ns : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (hrun : arena.checker_base.name_nodup ns = ok o) :
    o = nameNodup (absNIdxL ns) := by
  rw [arena.checker_base.name_nodup] at hrun
  have := name_nodup_from_refines hrun
  simpa [absNIdxLFrom, absNIdxL] using this


/-- `viewN` in `run` form: a read of the name store, the state unchanged. -/
theorem viewN_run (h : NIdx) (lst : AState) :
    (viewN h).run lst = match lst.store.ns.view h with
      | some x => .ok (x, lst)
      | none => .error (.internal "arena: dangling name handle") := by
  show (match lst.store.ns.view h with
        | some v => (pure v : AM _)
        | none => Arena.fail (.internal "arena: dangling name handle")).run lst = _
  cases lst.store.ns.view h <;> rfl

/-- The Rust name view as a `SimRE` read, with the view's well-formedness. -/
theorem view_n_simre {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.view_n pers st h = ok o) :
    SimRE absNNodeView lst o (viewN (absNIdx h)) ∧
      ∀ v, o = .Ok v → NNodeViewWF v := by
  have hA := view_n_run₀ hrel hinv hrun
  refine ⟨?_, ?_⟩
  · cases o with
    | Err e => exact hA
    | Ok v =>
      obtain ⟨lst', hx, -, -⟩ := hA
      show (viewN (absNIdx h)).run lst = .ok (absNNodeView v, lst)
      rw [hx]
      rw [viewN_run] at hx
      split at hx
      · cases hx; rfl
      · cases hx
  · intro v hv
    subst hv
    obtain ⟨_, _, _, ⟨_, hwf⟩, _⟩ := Lockstep.view_n_ls hrel hinv h (.Ok v) hrun
    exact hwf

/-- A code-point literal, read back. -/
theorem lit_abs {k : Std.Usize} {M : Std.Array Std.U32 k} {sl : Slice Std.U32}
    (hs : lift (Std.Array.to_slice M) = ok sl) {v : alloc.vec.Vec Std.U32}
    (hv : kernel.core_types.code_points sl = ok v) : v.val = M.val := by
  simp only [lift, Result.ok.injEq] at hs
  subst hs
  rw [ConRon.Refine.Env.code_points_val hv, Std.Array.val_to_slice]

/-- `nidx_is_proj_fn_shape` ⊑ `NIdx.isProjFnShape`. -/
theorem nidx_is_proj_fn_shape_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.nidx_is_proj_fn_shape pers st n = ok o) :
    SimRE id lst o (NIdx.isProjFnShape (absNIdx n)) := by
  rw [arena.checker_base.nidx_is_proj_fn_shape] at hrun
  obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have htag := nidx_tag_abs ht
  unfold SimRE
  rw [NIdx.isProjFnShape, htag]
  by_cases hnum : t = arena.handle.NTAG_NUM
  · rw [ite_eq_left hnum] at hrun
    rw [ite_eq_left (by rw [hnum, ntag_num_abs]; exact beq_self_eq_true _)]
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨hV, -⟩ := view_n_simre hrel hinv hr
    cases r with
    | Err e =>
      obtain rfl := (Result.ok_injective hrun).symm
      rw [am_run_bind']
      exact AErrSim.bind hV _
    | Ok nv =>
      have hV' : (viewN (absNIdx n)).run lst = .ok (absNNodeView nv, lst) := hV
      rw [Lockstep.run_bind_ok hV']
      cases nv with
      | Anonymous => obtain rfl := (Result.ok_injective hrun).symm; rfl
      | Str _ _ => obtain rfl := (Result.ok_injective hrun).symm; rfl
      | Num p _ =>
        simp only [absNNodeView]
        obtain ⟨t1, ht1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have htag1 := nidx_tag_abs ht1
        rw [htag1]
        by_cases hstr : t1 = arena.handle.NTAG_STR
        · rw [ite_eq_left hstr] at hrun
          rw [ite_eq_left (by rw [hstr, ntag_str_abs]; exact beq_self_eq_true _)]
          obtain ⟨r1, hr1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨hV1, hwf1⟩ := view_n_simre hrel hinv hr1
          cases r1 with
          | Err e =>
            obtain rfl := (Result.ok_injective hrun).symm
            rw [am_run_bind']
            exact AErrSim.bind hV1 _
          | Ok nv1 =>
            have hV1' : (viewN (absNIdx p)).run lst = .ok (absNNodeView nv1, lst) := hV1
            rw [Lockstep.run_bind_ok hV1']
            cases nv1 with
            | Anonymous => obtain rfl := (Result.ok_injective hrun).symm; rfl
            | Num _ _ => obtain rfl := (Result.ok_injective hrun).symm; rfl
            | Str _ sv =>
              have hswf : ConRon.Refine.StrWF sv := hwf1 _ rfl
              simp only [absNNodeView]
              obtain ⟨sl, hsl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have hvv := lit_abs hsl hv
              rw [arena.checker_base.nidx_is_proj_fn_shape.P, Std.Array.make_val] at hvv
              have hvwf : ConRon.Refine.StrWF v := by
                intro c hc; rw [hvv] at hc; fin_cases hc <;> decide
              have hvabs : ConRon.Refine.absString v = "proj" := by
                rw [ConRon.Refine.absString, hvv]; rfl
              obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
              have hbv := ConRon.Refine.Name.str_eq_refines hswf hvwf hb
              rw [hvabs] at hbv
              by_cases hbt : b = true
              · rw [ite_eq_left hbt] at hrun
                obtain rfl := (Result.ok_injective hrun).symm
                have : ConRon.Refine.absString sv = "proj" := by simpa [hbt] using hbv
                show Except.ok _ = Except.ok _
                simp [this]
              · rw [ite_eq_right hbt] at hrun
                obtain ⟨sl2, hsl2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                obtain ⟨v2, hv2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have hvv2 := lit_abs hsl2 hv2
                rw [arena.checker_base.nidx_is_proj_fn_shape.T, Std.Array.make_val] at hvv2
                have hvwf2 : ConRon.Refine.StrWF v2 := by
                  intro c hc; rw [hvv2] at hc; fin_cases hc <;> decide
                have hvabs2 : ConRon.Refine.absString v2 = "projTable" := by
                  rw [ConRon.Refine.absString, hvv2]; rfl
                obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
                have hbv1 := ConRon.Refine.Name.str_eq_refines hswf hvwf2 hb1
                rw [hvabs2] at hbv1
                obtain rfl := (Result.ok_injective hrun).symm
                have hne : ConRon.Refine.absString sv ≠ "proj" := by
                  intro h; apply hbt; rw [hbv, h]; rfl
                show Except.ok _ = Except.ok _
                have h1 : (ConRon.Refine.absString sv == "proj") = false := by simp [hne]
                simp only [h1, Bool.false_or, hbv1, id]
                cases h : (ConRon.Refine.absString sv == "projTable") <;> simp_all
        · rw [ite_eq_right hstr] at hrun
          rw [ite_eq_right (by
            rw [ntag_str_abs.symm.trans rfl] at *
            intro hx
            exact hstr (absU32_inj (by simpa using hx)))]
          obtain rfl := (Result.ok_injective hrun).symm
          rfl
  · rw [ite_eq_right hnum] at hrun
    rw [ite_eq_right (by
      rw [← ntag_num_abs]
      intro hx
      exact hnum (absU32_inj (by simpa using hx)))]
    obtain rfl := (Result.ok_injective hrun).symm
    rfl

/-! ## `arena::core::consts_resolve` — the plain walk the guard walk's leaves call

No tier had stated `arena::core::consts_resolve` (the Core knot does not call
it; the checker's guard walk hands its leaf arms to it).  The Rust splits the
two literal arms into `nat_trio_stored`/`str_support_stored`, the twin writes
their pin reads inline: the SAME reads in the same order, so the twin side is
two transcriptions (`natTrioStoredSpec`, `strSupportStoredSpec`) and one
equation (`constsResolve_succ`) — a factoring difference, not a divergence. -/

/-- The `Nat` literal arm's three pin reads and probes. -/
def natTrioStoredSpec (fe : IFEnv) : AM Bool := do
  let nt ← pinNat
  let nz ← pinNatZero
  let ns ← pinNatSucc
  pure ((fe.find? nt).isSome && (fe.find? nz).isSome && (fe.find? ns).isSome)

/-- The `String` literal arm's seven further pin reads and probes. -/
def strSupportStoredSpec (fe : IFEnv) : AM Bool := do
  let st ← pinString
  let sl ← pinStringOfList
  let li ← pinList
  let ln ← pinListNil
  let lc ← pinListCons
  let ch ← pinChar
  let co ← pinCharOfNat
  pure ((fe.find? st).isSome && (fe.find? sl).isSome && (fe.find? li).isSome &&
    (fe.find? ln).isSome && (fe.find? lc).isSome && (fe.find? ch).isSome &&
    (fe.find? co).isSome)

/-- `constsResolve` one step in, with the literal arms as the two transcriptions. -/
theorem constsResolve_succ (fe : IFEnv) (fuel : Nat) (h : EIdx) :
    constsResolve fe (fuel + 1) h = (do
      match ← view h with
      | .bvar _ | .sort _ => pure true
      | .lit (.natVal _) => natTrioStoredSpec fe
      | .lit (.strVal _) => do
        let x ← natTrioStoredSpec fe
        let y ← strSupportStoredSpec fe
        pure (x && y)
      | .const n _ => pure (fe.find? n).isSome
      | .fvar _ ty => constsResolve fe fuel ty
      | .app f a => do
        let x ← constsResolve fe fuel f
        if x then constsResolve fe fuel a else pure false
      | .lam ty body _ | .forallE ty body _ => do
        let x ← constsResolve fe fuel ty
        if x then constsResolve fe fuel body else pure false
      | .letE ty val body => do
        let x ← constsResolve fe fuel ty
        if !x then pure false else do
          let y ← constsResolve fe fuel val
          if y then constsResolve fe fuel body else pure false
      | .proj s _ sub => do
        if (fe.find? s).isSome then constsResolve fe fuel sub else pure false) := by
  rw [constsResolve]
  refine ConRon.Refine2.am_bind_congr _ ?_
  intro v
  cases v with
  | lit l =>
    cases l with
    | natVal _ => rfl
    | strVal _ =>
      simp only [natTrioStoredSpec, strSupportStoredSpec, bind_assoc, pure_bind,
        Bool.and_assoc]
  | _ => rfl

namespace Lockstep

/-- `arena::core::stored` is an index probe: the twin's `find?` test. -/
@[lockstep] theorem stored_spec {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (n : arena.handle.NIdx) (hctx : CoreCtx vis rf lf) :
    LSP (arena.core.stored vis rf n)
      (fun b => TwinEq ((lf.find? (absNIdx n)).isSome) b) := by
  intro b h
  rw [arena.core.stored] at h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hf := ifenv_find_abs hctx ho
  show (lf.find? (absNIdx n)).isSome = b
  rw [← hf]
  cases o with
  | none => simp only [Result.ok.injEq] at h; subst h; rfl
  | some _ => simp only [Result.ok.injEq] at h; subst h; rfl

@[lockstep] theorem nat_trio_stored_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis rf lf) :
    LS pers (fun a b => b = id a) (arena.core.nat_trio_stored vis st rf) lst
      (natTrioStoredSpec lf) := by
  rw [arena.core.nat_trio_stored, natTrioStoredSpec]
  lockstep

@[lockstep] theorem str_support_stored_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis rf lf) :
    LS pers (fun a b => b = id a) (arena.core.str_support_stored vis st rf) lst
      (strSupportStoredSpec lf) := by
  rw [arena.core.str_support_stored, strSupportStoredSpec]
  lockstep

end Lockstep

theorem consts_resolve_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → CoreCtx vis rf lf → AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a) (arena.core.consts_resolve pers vis st rf fuel h)
        lst (constsResolve lf n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst vis rf lf fuel h hn hctx hrel hinv
    rw [arena.core.consts_resolve, constsResolve]
    lockstep
  | succ m ih =>
    intro pers st lst vis rf lf fuel h hn hctx hrel hinv
    rw [arena.core.consts_resolve, constsResolve_succ]
    lockstep

/-- **`arena::core::consts_resolve` ⊑ `constsResolve`**. -/
@[lockstep] theorem Lockstep.consts_resolve_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis rf lf) (fuel : Std.U64) (h : arena.handle.EIdx) :
    Lockstep.LS pers (fun a b => b = id a) (arena.core.consts_resolve pers vis st rf fuel h)
      lst (constsResolve lf (absU fuel) (absEIdx h)) :=
  consts_resolve_aux _ fuel h rfl hctx hrel hinv

/-! ## The two memoised guard walks

Both thread a `HashMap2<EIdx, bool>` BESIDE the `Result` (`(Result bool,
AState, memo)` / `(Result bool, memo)`): the shared tactic's `LSM` (state walk)
and `LSRM` (reader) judgements, at `BoolMemoR` — the answer equal, the memos
related.  Each is a fuel induction whose two cases are one `lockstep` each,
the port's node/two/binder helpers unfolded in place (task #97-T2-LOCKSTEP
lane Checker Base/Top round 2). -/

namespace Lockstep

/-- The answer-and-memo relation of the tier's `Bool`-memo walks. -/
abbrev BoolMemoR (p : Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (b : Bool × Std.HashMap EIdx Bool) : Prop :=
  b.1 = p.1 ∧ ExprOps.LMemoRel p.2 b.2

end Lockstep

section MemoWalks
open Lockstep

/-- `memo_b_get` is the walk's `memo[h]?` — extraction rule 5's own function. -/
theorem memo_b_get_refines {rm lm} {k : arena.handle.EIdx} {o}
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.memo_b_get rm k = ok o) :
    o = lm[absEIdx k]? := by
  rw [arena.checker_base.memo_b_get] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hmr, hminv⟩ := hm
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hminv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hmr k trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Bool) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    have h2 : some r = o := Result.ok_injective hrun
    subst h2
    rfl

@[lockstep] theorem memo_b_get_twin {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {k : arena.handle.EIdx} (hm : ExprOps.LMemoRel rm lm) :
    LSP (arena.checker_base.memo_b_get rm k) (fun o => TwinEq (lm[absEIdx k]?) o) :=
  fun _ h => (memo_b_get_refines hm h).symm

/-- `consts_resolve_f_go` ⊑ `constsResolveFGo`, by induction on the fuel, at
any twin environment the port's `(vis, rf)` is a `CoreCtx` of (finding 10's
`vis`: the caller passes `lf.restrictTo (absU vis)`). -/
theorem consts_resolve_f_go_aux (n : Nat) :
    ∀ {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (lm : Std.HashMap EIdx Bool)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis rf lf →
      ExprOps.LMemoRel rm lm →
      LSM pers BoolMemoR (arena.checker_base.consts_resolve_f_go pers vis st rf rm fuel h) lst
        (constsResolveFGo lf lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst vis rf lf rm lm fuel h hn hrel hinv hctx hm
    rw [arena.checker_base.consts_resolve_f_go, constsResolveFGo]
    lockstep
  | succ m ih =>
    intro pers st lst vis rf lf rm lm fuel h hn hrel hinv hctx hm
    rw [arena.checker_base.consts_resolve_f_go, constsResolveFGo]
    unfold arena.checker_base.consts_resolve_f_node arena.checker_base.consts_resolve_f_two
    lockstep

@[lockstep] theorem consts_resolve_f_go_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSM pers BoolMemoR (arena.checker_base.consts_resolve_f_go pers vis st rf rm fuel h) lst
      (constsResolveFGo lf lm (absU fuel) (absEIdx h)) :=
  consts_resolve_f_go_aux _ rm lm fuel h rfl hrel hinv hctx hm

/-- **`arena::core_state::take_walk_memo`** (task #97-PERF-WALKMEMO): the
table it hands the walk is empty and well formed — the twin's `∅` — and the
one it leaves in the state's slot is well formed.  Either branch of nanoda's
guard: a fresh `HashMap::new()`, or the parked table through `reset_map`. -/
theorem take_walk_memo_spec {K V : Type} [DecidableEq K]
    {HashableInst : ron.hashmap.Hashable K} {slot m slot' : ron.hashmap2.HashMap2 K V}
    (hinv : ConRon.Refine.HashMap2.Inv HashableInst slot)
    (h : arena.core_state.take_walk_memo slot = ok (m, slot')) :
    ConRon.Refine.HashMap2.Inv HashableInst m ∧ (∀ k, ConRon.Refine.HashMap2.toFun m k = none) ∧ ConRon.Refine.HashMap2.Inv HashableInst slot' := by
  rw [arena.core_state.take_walk_memo] at h
  obtain ⟨hm, hnew, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hi, -, hn⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := HashableInst) hnew
  simp only [core.mem.replace] at h
  obtain ⟨i, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    exact ⟨hi, hn, hi⟩
  · obtain ⟨m1, hm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    rw [arena.core_state.reset_map] at hm1
    obtain ⟨hi1, -, hn1⟩ := ConRon.Refine.HashMap2.clear_fit_refines hinv hm1
    exact ⟨hi1, hn1, hi⟩

/-- The walk's starting memo, from `take_walk_memo`: related to the twin's `∅`. -/
theorem take_walk_memo_lmemo {slot m slot' : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    (hinv : ConRon.Refine.HashMap2.Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable slot)
    (h : arena.core_state.take_walk_memo slot = ok (m, slot')) :
    ExprOps.LMemoRel m ∅ ∧ ConRon.Refine.HashMap2.Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable slot' :=
  have H := take_walk_memo_spec hinv h
  ⟨⟨ConRon.Refine.HashMap2.RelOn_empty H.2.1, H.1⟩, H.2.2⟩

/-- The twin's `pure (← w).1`, run: the walk's run, its memo dropped. -/
theorem run_fst_eq {β M : Type} (w : AM (β × M)) (lst : AState) :
    (do pure (← w).1 : AM β).run lst = (w.run lst) >>= fun p => .ok (p.1.1, p.2) := by
  simp only [StateT.run_bind, StateT.run_pure]
  rcases w.run lst with _ | ⟨⟨b, mm⟩, l⟩ <;> rfl

/-- `consts_resolve_f_fast` ⊑ `constsResolveFFast` — one memoised DAG walk,
which is what every front door below calls.  The walk's memo is the state's
parked `crf_c` table, moved out and emptied by `take_walk_memo` and put back
afterwards (task #97-PERF-WALKMEMO); `MemosRel` has no clause for it, so the
two state updates are invisible to `AStateRel₀`, and `MemosInv.crfC` is
carried by the walk's own memo relation. -/
@[lockstep] theorem consts_resolve_f_fast_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.consts_resolve_f_fast pers vis st rf e) lst
      (constsResolveFFast (lf.restrictTo (absU vis)) (absEIdx e)) := by
  have hctx := IFEnvInv.coreCtxAt vis hfe.rel hfe.inv
  intro o st' hrun
  rw [arena.checker_base.consts_resolve_f_fast] at hrun
  obtain ⟨⟨m, hm⟩, htake, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hml, hhm⟩ := take_walk_memo_lmemo hinv.memos.crfC htake
  obtain ⟨⟨r, st1, m1⟩, hgo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
  have hw := LSM.apply (consts_resolve_f_go_ls
    (st := { st with memos := { st.memos with crf_c := hm } })
    ⟨hrel.store, { hrel.memos with }, hrel.caches, hrel.pins⟩
    ⟨hinv.store, { hinv.memos with crfC := hhm }, hinv.caches⟩ hctx hml
    arena.core.CORE_WALK_FUEL e) hgo
  rw [core_walk_fuel_abs] at hw
  rw [constsResolveFFast, run_fst_eq]
  cases r with
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h3, h4⟩ := hw
    exact ⟨b.1, lst', by rw [hx]; rfl, hR.1, ⟨h3.store, { h3.memos with }, h3.caches, h3.pins⟩,
      ⟨h4.store, { h4.memos with crfC := hR.2.2 }, h4.caches⟩⟩
  | Err err =>
    exact AErrSim.trans hw (fun le hle => by rw [hle]; rfl)

@[lockstep] theorem level_all_params_defined_twin {params : alloc.vec.Vec kernel.name.Name}
    {l : kernel.level.Level} (hp : NamesWF params) (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.all_params_defined params l)
      (fun b => TwinEq (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params)
        (ConRon.Refine.absLevel l)) b) :=
  fun b h => (ConRon.Refine.ExprOps.all_params_defined_refines hp l hl b h).symm

@[lockstep] theorem prop_when_params_defined_twin {params : alloc.vec.Vec kernel.name.Name}
    {pw : kernel.prop_when.PropWhen} (hp : NamesWF params) (hpw : ConRon.Refine.PropWhenWF pw) :
    LSP (kernel.prop_when.params_defined params pw)
      (fun b => TwinEq (ConLeche.PropWhen.paramsDefined (ConRon.Refine.absNames params)
        (ConRon.Refine.absPropWhen pw)) b) :=
  fun _b h => (ConRon.Refine.PropWhen.params_defined_refines hp hpw h).symm

theorem all_params_defined_list_aux {params : alloc.vec.Vec kernel.name.Name}
    {ls : alloc.vec.Vec kernel.level.Level} (hp : NamesWF params) (hl : ConRon.Refine.LevelsWF ls) :
    ∀ (k : Nat) (i : Std.Usize) (o : Bool), ls.val.length - i.val = k →
      arena.checker_base.all_params_defined_list params ls i = ok o →
      o = (absLevelLFrom ls i).all
        (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params)) := by
  intro k
  induction k with
  | zero =>
    intro i o hk h
    rw [arena.checker_base.all_params_defined_list] at h
    have := alloc.vec.Vec.len_val ls
    rw [ite_eq_left (by scalar_tac)] at h
    rw [← Result.ok_injective h, absLevelLFrom, List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ k ih =>
    intro i o hk h
    rw [arena.checker_base.all_params_defined_list] at h
    have := alloc.vec.Vec.len_val ls
    rw [ite_eq_right (by scalar_tac)] at h
    have hlt : i.val < ls.val.length := by omega
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hxv⟩ := ExprOps.vecIndexAt hx
    obtain ⟨b, hbv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hxw : ConRon.Refine.LevelWF x := hxv ▸ hl _ (List.getElem_mem hb)
    have e1 := ConRon.Refine.ExprOps.all_params_defined_refines hp x hxw b hbv
    have hdrop : absLevelLFrom ls i = ConRon.Refine.absLevel x :: (ls.val.drop (i.val + 1)).map ConRon.Refine.absLevel := by
      rw [absLevelLFrom, List.drop_eq_getElem_cons hb, hxv]; rfl
    rw [hdrop, List.all_cons, ← e1]
    cases b with
    | false => simp only [Bool.false_eq_true, ite_false, Result.ok.injEq] at h; rw [← h]; rfl
    | true =>
      simp only [ite_true] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      rw [ih i2 o (by omega) h, absLevelLFrom, hi2v]; rfl

@[lockstep] theorem all_params_defined_list_twin {params : alloc.vec.Vec kernel.name.Name}
    {ls : alloc.vec.Vec kernel.level.Level} (hp : NamesWF params) (hl : ConRon.Refine.LevelsWF ls) :
    LSP (arena.checker_base.all_params_defined_list params ls 0#usize)
      (fun o => TwinEq ((ConRon.Refine.absLevels ls).all
        (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params))) o) := by
  intro o h
  rw [all_params_defined_list_aux hp hl _ 0#usize o rfl h]
  simp [TwinEq, absLevelLFrom, ConRon.Refine.absLevels]

theorem all_level_params_defined_go_aux (n : Nat) :
    ∀ {pers st lst} (params : alloc.vec.Vec kernel.name.Name)
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (lm : Std.HashMap EIdx Bool)
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → NamesWF params →
      ExprOps.LMemoRel rm lm →
      LSRM pers BoolMemoR (arena.checker_base.all_level_params_defined_go pers st params rm fuel h) st lst
        (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst params rm lm fuel h hn hrel hinv hp hm
    rw [arena.checker_base.all_level_params_defined_go, allLevelParamsDefinedGo]
    lockstep
  | succ m ih =>
    intro pers st lst params rm lm fuel h hn hrel hinv hp hm
    rw [arena.checker_base.all_level_params_defined_go, allLevelParamsDefinedGo]
    unfold arena.checker_base.all_level_params_defined_node arena.checker_base.all_level_params_defined_binder
    lockstep

@[lockstep] theorem all_level_params_defined_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {params : alloc.vec.Vec kernel.name.Name} (hp : NamesWF params)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSRM pers BoolMemoR (arena.checker_base.all_level_params_defined_go pers st params rm fuel h) st lst
      (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm (absU fuel) (absEIdx h)) :=
  all_level_params_defined_go_aux _ params rm lm fuel h rfl hrel hinv hp hm

/-- `all_level_params_defined` ⊑ `allLevelParamsDefined` — one memoised DAG
walk, at the parameter list read back once.  A STATE step since task
#97-PERF-WALKMEMO: the walk's memo is the state's parked `lp_def_c` table,
moved out and emptied by `take_walk_memo` and put back afterwards — the
twin's `∅`, and invisible to `AStateRel₀` (`MemosRel` has no clause for it). -/
@[lockstep] theorem all_level_params_defined_ls {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.all_level_params_defined pers st lps e) lst
      (allLevelParamsDefined (absNIdxL lps) (absEIdx e)) := by
  intro o st' hrun
  rw [arena.checker_base.all_level_params_defined] at hrun
  obtain ⟨r0, hr0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hrn := read_names_ls hrel hinv lps r0 hr0
  rw [allLevelParamsDefined, StateT.run_bind]
  cases r0 with
  | Err err =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    exact AErrSim.bind hrn _
  | Ok ks =>
    obtain ⟨ks', lst1, hx1, ⟨hks, rfl⟩, hrel1, hinv1⟩ := hrn
    obtain ⟨⟨m, hm⟩, htake, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨hml, hhm⟩ := take_walk_memo_lmemo hinv.memos.lpDefC htake
    obtain ⟨⟨r, m1⟩, hgo, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    have hw := LSRM.apply (all_level_params_defined_go_ls
      (st := { st with memos := { st.memos with lp_def_c := hm } })
      ⟨hrel1.store, { hrel1.memos with }, hrel1.caches, hrel1.pins⟩
      ⟨hinv.store, { hinv.memos with lpDefC := hhm }, hinv.caches⟩ hks hml
      arena.core.CORE_WALK_FUEL e) hgo
    rw [core_walk_fuel_abs] at hw
    rw [show absNIdxL lps = lps.val.map absNIdx from rfl, hx1]
    show LOut pers _ _ _ ((do pure (← allLevelParamsDefinedGo _ ∅ coreWalkFuel _).1 : AM Bool).run lst1)
    rw [run_fst_eq]
    cases r with
    | Ok a =>
      obtain ⟨b, lst', hx, hR, h3, h4⟩ := hw
      exact ⟨b.1, lst', by rw [hx]; rfl, hR.1, ⟨h3.store, { h3.memos with }, h3.caches, h3.pins⟩,
        ⟨hinv.store, { hinv.memos with lpDefC := hR.2.2 }, hinv.caches⟩⟩
    | Err err =>
      exact AErrSim.trans hw (fun le hle => by rw [hle]; rfl)

end MemoWalks

/-! ## The front door's verdict at an unresolved constant -/

/-- `unresolved_consts_error` by `lockstep`, with its walk `mentions_const` as a
hypothesis: that walk's statement (`mentions_const_ls`) is
`Refine2/Inductives/StructParts.lean`'s, a module ABOVE this one (the
Inductives tier imports the checker's base), so it cannot be named here. -/
theorem unresolved_consts_error_of {pers st lst} {e : arena.handle.EIdx} {o}
    {w : String}
    (hM : ∀ {st lst} (t : arena.handle.NIdx), AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a)
        (arena.inductives.struct_parts.mentions_const pers st t e) lst
        (mentionsConst (absNIdx t) (absEIdx e)))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.unresolved_consts_error pers st e = ok o) :
    SimRel₀ (fun r v => absAErrKind r = lAErrKind v) pers lst o
      (unresolvedConstsError w (absEIdx e)) := by
  have hS : ∀ {st lst}, AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_sorry_ax st) st lst
        pinSorryAx :=
    fun hrel hinv => Lockstep.LSR.ofSimRE hrel hinv fun _ h => pin_sorry_ax_refines hrel hinv h
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.checker_base.unresolved_consts_error, unresolvedConstsError]
  lockstep

/-- `unresolved_consts_error` ⊑ `unresolvedConstsError`.  The result is a
CheckError, so it is a `SimRel₀` at the kind: a term that mentions `sorryAx`
DECLINES (`notImplemented`) and anything else REJECTS (`invalid`), and the
claim is that the two agree on WHICH — messages are never compared
(DESIGN §3.1).  `unresolved_consts_error_of` at `mentions_const_ls`
(`Checker/Leaves.lean`, moved down from `Inductives/StructParts.lean`). -/
theorem unresolved_consts_error_refines {pers st lst} {e : arena.handle.EIdx} {o}
    {w : String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.unresolved_consts_error pers st e = ok o) :
    SimRel₀ (fun r v => absAErrKind r = lAErrKind v) pers lst o
      (unresolvedConstsError w (absEIdx e)) :=
  unresolved_consts_error_of (fun _ hrel hinv => mentions_const_ls hrel hinv) hrel hinv hrun

open Lockstep in
@[lockstep] theorem unresolved_consts_error_ls {pers st lst}
    {e : arena.handle.EIdx}
    {w : String}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e) lst
      (unresolvedConstsError w (absEIdx e)) :=
  LS.ofSimRel₀ fun _ h => unresolved_consts_error_refines hrel hinv h

/-! ### Twin readers leave the state alone

The twin's pin reads (`natOpNames`, `natDivModNames`, `reduceOpNames`) read
the pin table and write nothing — a fact about the twin alone, which the
parser tier's `is_nat_op_record_refines` uses to keep its old-shape
statement across a lockstep reader. -/

/-- **`ifenv_find` ⊑ `IFEnv.find?`**, filed as a Rust-only step whose answer
rewrites the twin (task #97-T2-LOCKSTEP lane Checker round 2): the index read
is pure on both sides, `ifenv_find_abs` is the correspondence. -/
@[lockstep] theorem Lockstep.ifenv_find_spec {vis : Std.U64} {rf lf} (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) (n : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find vis rf n)
      (fun o => TwinEq (lf.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (ifenv_find_abs (IFEnvInv.coreCtx hfe.rel hfe.inv hvis) h).symm

@[lockstep_simp] theorem absIConstantVal_name (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).name = absNIdx cv.name := rfl

attribute [lockstep_simp] Lockstep.PC1.absIConstantVal_type

attribute [lockstep_simp] core.option.Option.is_some Option.isSome_map ite_true ite_false

/-! ## The erased-subtype invariant at its sources

`IFEnvRel.envWF` needs every pushed constant to be canonical Rust data
(`IConstantInfoWF`: an inductive's zero-ness `PropWhen` satisfies the
invariant Charon erased).  These are its sources, facts about the Rust
alone: an interned kernel constant (`intern_ci_list`, the basis's
`basis_kind_decls_a`) and a copy (`i_constant_info_dup`). -/

/-- `intern_caps` copies the zero-ness datum. -/
theorem intern_ci_go_wf {pers st m c ci st' m'} (hwf : ConRon.Refine.ConstantInfoWF c)
    (h : arena.intern.intern_ci_go pers st m c = ok (.Ok ci, st', m')) : IConstantInfoWF ci := by
  cases c with
  | IndInfo v c2 =>
    rw [arena.intern.intern_ci_go] at h
    obtain ⟨⟨r, st1, m1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e => simp at h
    | Ok cv =>
      obtain ⟨⟨r2, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => simp at h
      | Ok caps =>
        obtain ⟨⟨rfl⟩, -⟩ := Prod.mk.inj (Result.ok_injective h)
        show ConRon.Refine.PropWhenWF caps.sort_z
        rw [intern_caps_sort_z h2]; exact hwf.2.2.1
  | _ =>
    rcases ci with _ | _ | _ | ⟨cv, caps⟩ | _ | _ | _ <;> try trivial
    rw [arena.intern.intern_ci_go] at h
    repeat (first
      | (obtain ⟨⟨r, _, _⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; rcases r with r | r)
      | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h))
    all_goals simp at h

theorem intern_ci_list_go_wf (n : Nat) : ∀ {pers st m} (es : alloc.vec.Vec kernel.env.ConstantInfo)
    (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantInfo) {r st' m'},
    es.val.length - i.val = n → (∀ x ∈ es.val, ConRon.Refine.ConstantInfoWF x) →
    (∀ c ∈ out.val, IConstantInfoWF c) →
    arena.intern.intern_ci_list_go pers st m es i out = ok (.Ok r, st', m') →
    ∀ c ∈ r.val, IConstantInfoWF c := by
  induction n with
  | zero =>
    intro pers st m es i out r st' m' hn hP hout h
    rw [arena.intern.intern_ci_list_go] at h
    have hl := alloc.vec.Vec.len_val es
    rw [ite_eq_left (by scalar_tac)] at h
    obtain ⟨⟨rfl⟩, -⟩ := Prod.mk.inj (Result.ok_injective h)
    exact hout
  | succ k ih =>
    intro pers st m es i out r st' m' hn hP hout h
    rw [arena.intern.intern_ci_list_go] at h
    have hl := alloc.vec.Vec.len_val es
    rw [ite_eq_right (by scalar_tac)] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r1, st1, m1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rcases r1 with ci | e
    · obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      obtain ⟨hb, hxv⟩ := ExprOps.vecIndexAt hx
      refine ih es i2 out1 (by omega) hP ?_ h
      rw [ConRon.Refine.vec_push_val hout1]
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hout c hc
      · rw [List.mem_singleton.mp hc]
        exact intern_ci_go_wf (hP x (hxv ▸ List.getElem_mem hb)) h1
    · simp at h

/-- **`intern_ci_list` keeps the erased-subtype invariant**: a well-formed
kernel constant interns to an `IConstantInfoWF` one (an inductive's zero-ness
datum is copied by `prop_when::dup`).  A fact about the Rust alone. -/
theorem intern_ci_list_wf {pers st} {cs : alloc.vec.Vec kernel.env.ConstantInfo} {r st'}
    (hwf : ConRon.Refine.ConstantInfosWF cs)
    (h : arena.intern.intern_ci_list pers st cs = ok (.Ok r, st')) :
    ∀ c ∈ r.val, IConstantInfoWF c := by
  rw [arena.intern.intern_ci_list] at h
  obtain ⟨m, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r1, st1, m1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Result.ok_injective h)
  exact intern_ci_list_go_wf _ cs 0#usize _ rfl hwf (by simp [alloc.vec.Vec.new]) h1

/-- The basis's annotated constants are `IConstantInfoWF`. -/
theorem basis_kind_decls_a_wf {pers st} {k : kernel.env.BasisKind} {r st'}
    (h : arena.basis.basis_kind_decls_a pers st k = ok (.Ok r, st')) :
    ∀ c ∈ r.val, IConstantInfoWF c := by
  rw [arena.basis.basis_kind_decls_a] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact intern_ci_list_wf (ConRon.Refine.BasisPins.basis_decls_a_wf hv) h

/-- `i_constant_info_dup` keeps `IConstantInfoWF` (`prop_when::dup` is the
identity). -/
theorem i_constant_info_dup_wf {c o : arena.env.IConstantInfo}
    (h : arena.env.i_constant_info_dup c = ok o) (hc : IConstantInfoWF c) :
    IConstantInfoWF o := by
  rw [arena.env.i_constant_info_dup.eq_def] at h
  cases c with
  | IndInfo cv caps =>
    obtain ⟨iv, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ic, hic, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    rw [arena.env.i_ind_caps_dup] at hic
    obtain ⟨n, _, hic⟩ := ConRon.Refine.bind_eq_ok_iff.mp hic
    obtain ⟨pw, hpw, hic⟩ := ConRon.Refine.bind_eq_ok_iff.mp hic
    obtain ⟨_, _, hic⟩ := ConRon.Refine.bind_eq_ok_iff.mp hic
    obtain ⟨_, _, hic⟩ := ConRon.Refine.bind_eq_ok_iff.mp hic
    rw [← Result.ok_injective hic]
    show ConRon.Refine.PropWhenWF pw
    rw [ConRon.Refine.PropWhen.dup_eq hpw]; exact hc
  | _ =>
    rcases o with _ | _ | _ | ⟨cv, caps⟩ | _ | _ | _ <;> try trivial
    repeat (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
    all_goals simp at h

namespace Lockstep

@[lockstep] theorem nidx_contains_from_spec (ns : alloc.vec.Vec arena.handle.NIdx)
    (i : Std.Usize) (n : arena.handle.NIdx) :
    LSP (arena.checker_base.nidx_contains_from ns i n)
      (fun o => o = (absNIdxLFrom ns i).contains (absNIdx n)) :=
  fun _ h => nidx_contains_from_refines h

/-- **`ifenv_restrict_to` is a field update** (task #97-T2-LOCKSTEP lane
Checker round 2), filed as a Rust-only step whose answer the tactic
substitutes: the twin's partner is the pure `IFEnv.restrictTo` at the call
site, and `IFEnvRelI.restrict` below relates the two. -/
@[lockstep] theorem ifenv_restrict_to_spec (rf : arena.env.IFEnv) (k : Std.U64) :
    LSP (arena.env.ifenv_restrict_to rf k)
      (fun r => r = { rf with visible_below := k }) := by
  intro r h
  simp only [arena.env.ifenv_restrict_to, Result.ok.injEq] at h
  exact h.symm

/-- **The restricted index is related to the restricted twin index** — the
invariant's counter bound is the one thing that needs the new counter to fit
the constant list. -/
theorem IFEnvRelI.restrict {rf : arena.env.IFEnv} {lf : IFEnv}
    (h : IFEnvRelI rf lf) {k : Std.U64}
    (hk : k.val ≤ rf.env.consts.val.length) :
    IFEnvRelI { rf with visible_below := k } (lf.restrictTo (absU k)) :=
  ⟨⟨h.rel.env, h.rel.idx, rfl, h.rel.envWF, h.rel.keys⟩, ⟨h.inv.1, hk, h.inv.2.2⟩⟩

/-- The side tier's extension for the pin gates' pre-insertion view: a
restricted index against the restricted twin index, its bound by `omega` over
the context's counters. -/
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (apply IFEnvRelI.restrict (by assumption); (checker_env_facts; (try simp only at *); omega)))

/-- `ifenv_push` raises the counter by one. -/
theorem ifenv_push_vis {rf rf' : arena.env.IFEnv} {ci : arena.env.IConstantInfo}
    (h : arena.env.ifenv_push rf ci = ok rf') :
    rf'.visible_below.val = rf.visible_below.val + 1 := by
  rw [arena.env.ifenv_push] at h
  obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨q, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := (Result.ok_injective h).symm
  exact ConRon.Refine.Nat.uadd_val hc1

/-- `ifenv_push` at a constant the checker built: `hwf` is the pushed
constant's erased-subtype invariant (`True` but at an inductive), discharged
by the side tier from the constructor (`IConstantInfoWF_*`) and, at an
inductive, from its caps' source. -/
@[lockstep] theorem ifenv_push_spec {rf lf} (hfe : IFEnvRelI rf lf)
    (ci : arena.env.IConstantInfo) (hwf : IConstantInfoWF ci) :
    LSP (arena.env.ifenv_push rf ci)
      (fun r => IFEnvRelI r (lf.push (absIConstantInfo ci)) ∧
        rf.visible_below.val ≤ r.visible_below.val) :=
  fun _ h => ⟨ifenv_push_refines hfe.rel hfe.inv hwf h, by rw [ifenv_push_vis h]; omega⟩

attribute [lockstep_simp] absIConstantInfo absValueGroup absValueKind Option.map_some
  Option.map_none

end Lockstep

/-! ## The per-declaration constant check -/

open Lockstep in
@[lockstep] theorem nidx_is_proj_fn_shape_ls {pers st lst} {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.checker_base.nidx_is_proj_fn_shape pers st n)
      st lst (NIdx.isProjFnShape (absNIdx n)) :=
  LSR.ofSimRE hrel hinv fun _ h => nidx_is_proj_fn_shape_refines hrel hinv h

@[lockstep_simp] theorem absIConstantVal_levelParams (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).levelParams = cv.level_params.val.map absNIdx := rfl

open Lockstep in
@[lockstep] theorem name_nodup_spec (ns : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.checker_base.name_nodup ns)
      (fun o => TwinEq (nameNodup (ns.val.map absNIdx)) o) :=
  fun _ h => (name_nodup_refines h).symm

/-- `check_constant_val_guards_rest` is `check_constant_val_guards`'s tail past
the duplicate-declaration test (extraction rule 5).  One `lockstep` call. -/
theorem check_constant_val_guards_rest_refines {pers st lst}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.check_constant_val_guards_rest pers st cv = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkConstantValGuardsRestSpec (absIConstantVal cv)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val_guards_rest, checkConstantValGuardsRestSpec]
  simp only [am_fail_bind]
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_guards_rest_ls {pers st lst}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_constant_val_guards_rest pers st cv) lst
      (checkConstantValGuardsRestSpec (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_constant_val_guards_rest_refines hrel hinv h

/-- `check_constant_val_guards` is `installConstantVal`'s guard prefix — the
syntactic tests before the annotation. -/
theorem check_constant_val_guards_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_constant_val_guards pers vis st rf cv = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkConstantValGuardsSpec lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val_guards]
  try unfold checkConstantValGuardsSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_guards_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_constant_val_guards pers vis st rf cv) lst
      (checkConstantValGuardsSpec lf (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_constant_val_guards_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `install_constant_val_tail` is `installConstantVal`'s tail past the
annotation: the level-parameter test and the constant-resolution test. -/
theorem install_constant_val_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {ty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.install_constant_val_tail pers vis st rf cv ty = ok o) :
    Sim₀ absIConstantVal pers lst o
      (installConstantValTailSpec lf (absIConstantVal cv) (absEIdx ty)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.install_constant_val_tail]
  try unfold installConstantValTailSpec
  lockstep

open Lockstep in
@[lockstep] theorem install_constant_val_tail_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv : arena.env.IConstantVal}
    {ty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.checker_base.install_constant_val_tail pers vis st rf cv ty) lst
      (installConstantValTailSpec lf (absIConstantVal cv) (absEIdx ty)) :=
  LS.ofSim₀ fun _ h => install_constant_val_tail_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_constant_val_after_annot` is `checkConstantVal`'s tail: the
install-side tail plus the type's own inference and sort check. -/
theorem check_constant_val_after_annot_refines {pers st lst} {vis : Std.U64}
    {rf lf} {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {ty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_constant_val_after_annot pers vis st mode rf cv ty
      = ok o) :
    Sim₀ absIConstantVal pers lst o
      (checkConstantValAfterAnnotSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx ty)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val_after_annot]
  try unfold checkConstantValAfterAnnotSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_after_annot_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {ty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.checker_base.check_constant_val_after_annot pers vis st mode rf cv ty) lst
      (checkConstantValAfterAnnotSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx ty)) :=
  LS.ofSim₀ fun _ h => check_constant_val_after_annot_refines hrel hinv hfe.rel hfe.inv hvis h

/-- **`check_constant_val` ⊑ `checkConstantVal`** — the common per-declaration
constant check, whole. -/
theorem check_constant_val_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_constant_val pers vis st mode rf cv = ok o) :
    Sim₀ absIConstantVal pers lst o
      (checkConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.check_constant_val]
  rw [checkConstantVal_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem check_constant_val_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.checker_base.check_constant_val pers vis st mode rf cv) lst
      (checkConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_constant_val_refines hrel hinv hfe.rel hfe.inv hvis h

/-! ## Opening a pi telescope at fresh free variables -/

open Lockstep in
theorem open_pis_at_fvars_aux (k : Nat) :
    ∀ {pers st lst} (n : Std.U64) (h : arena.handle.EIdx) (i : Std.U64),
      n.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a)
        (arena.checker_base.open_pis_at_fvars pers st n h i) lst
        (openPisAtFvars k (absEIdx h) (absU i)) := by
  induction k with
  | zero =>
    intro pers st lst n h i hn hrel hinv
    rw [arena.checker_base.open_pis_at_fvars, openPisAtFvars]
    lockstep
  | succ m ih =>
    intro pers st lst n h i hn hrel hinv
    rw [arena.checker_base.open_pis_at_fvars, openPisAtFvars]
    lockstep

open Lockstep in
theorem open_pis_at_fvars_f_go_aux (k : Nat) :
    ∀ {pers st lst} (acc : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) (h : arena.handle.EIdx) (i : Std.U64),
      n.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a)
        (arena.checker_base.open_pis_at_fvars_f_go pers st acc n h i) lst
        (openPisAtFvarsFGo (absEIdxL acc).toArray k (absEIdx h) (absU i)) := by
  induction k with
  | zero =>
    intro pers st lst acc n h i hn hrel hinv
    rw [arena.checker_base.open_pis_at_fvars_f_go, openPisAtFvarsFGo]
    lockstep
  | succ m ih =>
    intro pers st lst acc n h i hn hrel hinv
    rw [arena.checker_base.open_pis_at_fvars_f_go, openPisAtFvarsFGo]
    lockstep


open Lockstep in
/-- `open_pis_at_fvars` ⊑ `openPisAtFvars` — structural on `n`, so no fuel of
its own. -/
@[lockstep] theorem open_pis_at_fvars_ls {pers st lst}
    {n : Std.U64}
    {h : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a)
      (arena.checker_base.open_pis_at_fvars pers st n h i) lst
      (openPisAtFvars (absU n) (absEIdx h) (absU i)) := by
  exact open_pis_at_fvars_aux _ n h i rfl hrel hinv

open Lockstep in
/-- `open_pis_at_fvars_f_go` ⊑ `openPisAtFvarsFGo` — `acc` holds the
already-created fvars, innermost binder first; one `instantiateList` pass per
domain instead of one whole-telescope `instantiate1` pass per binder. -/
@[lockstep] theorem open_pis_at_fvars_f_go_ls {pers st lst}
    {acc : alloc.vec.Vec arena.handle.EIdx}
    {n : Std.U64}
    {h : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a)
      (arena.checker_base.open_pis_at_fvars_f_go pers st acc n h i) lst
      (openPisAtFvarsFGo (absEIdxL acc).toArray (absU n) (absEIdx h) (absU i)) := by
  exact open_pis_at_fvars_f_go_aux _ acc n h i rfl hrel hinv

/-- `open_pis_at_fvars_f` ⊑ `openPisAtFvarsF` — the one-pass form, with the
fallback that covers telescopes whose binders only appear after
substitution. -/
theorem open_pis_at_fvars_f_refines {pers st lst} {n : Std.U64}
    {e : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.open_pis_at_fvars_f pers st n e i = ok o) :
    Sim₀ (Option.map (fun p => (absEIdxL p.1, absEIdx p.2)))
      pers lst o (openPisAtFvarsF (absU n) (absEIdx e) (absU i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.open_pis_at_fvars_f]
  try unfold openPisAtFvarsF
  lockstep

open Lockstep in
@[lockstep] theorem open_pis_at_fvars_f_ls {pers st lst}
    {n : Std.U64}
    {e : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a)
      (arena.checker_base.open_pis_at_fvars_f pers st n e i) lst
      (openPisAtFvarsF (absU n) (absEIdx e) (absU i)) :=
  LS.ofSim₀ fun _ h => open_pis_at_fvars_f_refines hrel hinv h

open Lockstep in
/-- `fvar_type_ds` ⊑ `fvarTypeDs` at the cursor — `xs.map Expr.fvarTypeD`,
with DESIGN §3.4's closure-free `List` recursion; the port pushes onto `out`
before it recurses, so the relation carries `out` in front of the twin's
answer. -/
theorem fvar_type_ds_aux {pers st} (hs : alloc.vec.Vec arena.handle.EIdx) (k : Nat) :
    ∀ {lst} (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx), hs.val.length - i.val = k →
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => absEIdxL a = absEIdxL out ++ b)
        (arena.checker_base.fvar_type_ds pers st hs i out) st lst
        (fvarTypeDs (absEIdxLFrom hs i)) := by
  induction k with
  | zero =>
    intro lst i out hk hrel hinv
    apply LSR.of_LS
    rw [arena.checker_base.fvar_type_ds]
    have hl := alloc.vec.Vec.len_val hs
    rw [ite_eq_left (by scalar_tac)]
    have : absEIdxLFrom hs i = [] := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [this, fvarTypeDs]
    lockstep
  | succ k ih =>
    intro lst i out hk hrel hinv
    apply LSR.of_LS
    rw [arena.checker_base.fvar_type_ds]
    have hl := alloc.vec.Vec.len_val hs
    rw [ite_eq_right (by scalar_tac)]
    have hlt : i.val < hs.val.length := by omega
    have : absEIdxLFrom hs i = absEIdx hs.val[i.val] :: (hs.val.drop (i.val + 1)).map absEIdx := by
      simp only [absEIdxLFrom]; rw [List.drop_eq_getElem_cons hlt]; rfl
    rw [this, fvarTypeDs]
    lockstep

open Lockstep in
@[lockstep] theorem fvar_type_ds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hs : alloc.vec.Vec arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdxL a)
      (arena.checker_base.fvar_type_ds pers st hs 0#usize (alloc.vec.Vec.new _)) st lst
      (fvarTypeDs (absEIdxL hs)) := by
  have H := fvar_type_ds_aux hs _ 0#usize (alloc.vec.Vec.new _) rfl hrel hinv
  have e0 : absEIdxLFrom hs 0#usize = absEIdxL hs := by simp [absEIdxLFrom, absEIdxL]
  rw [e0] at H
  intro o ho
  have := H o ho
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := this
    refine ⟨b, lst', hx, ?_, h1, h2⟩
    show b = absEIdxL a
    rw [hR]; simp [absEIdxL, alloc.vec.Vec.new]

/-! ## The block's declared parameter count -/

/-- The block's cursor at a position inside it: the element, then the rest. -/
theorem absICILFrom_cons {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    (hlt : i.val < block.val.length) :
    absICILFrom block i
      = absIConstantInfo block.val[i.val] :: (block.val.drop (i.val + 1)).map absIConstantInfo := by
  simp only [absICILFrom, List.drop_eq_getElem_cons hlt, List.map_cons]

open Lockstep in
/-- `arena::env::pi_sort_tele_len` as a store read (`Checker/Leaves.lean`'s
`env_pi_sort_tele_len_run`). -/
@[lockstep] theorem pi_sort_tele_len_ls {pers st lst} {fuel : Std.U64}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = Option.map absU a)
      (arena.env.pi_sort_tele_len pers st.store fuel h) st lst
      (piSortTeleLen? (absU fuel) (absEIdx h)) :=
  LSR.ofSimRE hrel hinv fun _ hr => Frontend.env_pi_sort_tele_len_run hrel hinv hr

/-- A `u64` handle-free comparison, read back. -/
@[lockstep_simp] theorem absU_beq_u64 (a b : Std.U64) :
    (absU a == absU b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : absU a ≠ absU b := fun e => h (Std.UScalar.eq_of_val_eq e)
    simp [h, this]

/-- `≤` on `u64`, read back. -/
@[lockstep_simp] theorem absU_le_u64 (a b : Std.U64) :
    decide (absU a ≤ absU b) = decide (a ≤ b) := by
  simp only [absU]; rfl

/-- `ind_params_ok_at` is `ind_params_ok`'s per-member test. -/
theorem ind_params_ok_at_refines {pers st lst} {n_p : Std.U64}
    {ci : arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.ind_params_ok_at pers st n_p ci = ok o) :
    Sim₀ id pers lst o
      (indParamsOkAtSpec (absU n_p) (absIConstantInfo ci)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  cases ci <;> (rw [arena.checker_base.ind_params_ok_at]; simp only [absIConstantInfo,
    indParamsOkAtSpec]) <;> lockstep

open Lockstep in
@[lockstep] theorem ind_params_ok_at_ls {pers st lst}
    {n_p : Std.U64}
    {ci : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.ind_params_ok_at pers st n_p ci) lst
      (indParamsOkAtSpec (absU n_p) (absIConstantInfo ci)) :=
  LS.ofSim₀ fun _ h => ind_params_ok_at_refines hrel hinv h

theorem ind_params_ok_aux {n_p : Std.U64} {block : alloc.vec.Vec arena.env.IConstantInfo}
    (m : Nat) : ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (i : Std.Usize), block.val.length - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = id a)
        (arena.checker_base.ind_params_ok pers st n_p block i) lst
        (indParamsOk (absU n_p) (absICILFrom block i)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro pers st lst i hm hrel hinv
    have hl := alloc.vec.Vec.len_val block
    by_cases hge : i ≥ block.len
    · have hle : block.val.length ≤ i.val := by scalar_tac
      have hnil : absICILFrom block i = [] := by
        simp [absICILFrom, List.drop_eq_nil_of_le hle]
      rw [arena.checker_base.ind_params_ok, hnil, indParamsOk]
      lockstep
    · have hlt : i.val < block.val.length := by scalar_tac
      have ih' : ∀ (i2 : Std.Usize), i2.val = i.val + 1 → ∀ {st lst},
          AStateRel₀ pers st lst → AStateInv pers st →
          Lockstep.LS pers (fun a b => b = id a)
            (arena.checker_base.ind_params_ok pers st n_p block i2) lst
            (indParamsOk (absU n_p) ((block.val.drop (i.val + 1)).map absIConstantInfo)) := by
        intro i2 hi2 st lst hrel hinv
        have e : (block.val.drop (i.val + 1)).map absIConstantInfo = absICILFrom block i2 := by
          simp [absICILFrom, hi2]
        rw [e]
        exact ih _ (by omega) i2 rfl hrel hinv
      rw [arena.checker_base.ind_params_ok, absICILFrom_cons hlt, indParamsOk_unfold]
      lockstep

/-- `ind_params_ok` ⊑ `indParamsOk` from the cursor on — **the stream's
declared parameter count, checked as official checks it** (con-leche's task
#228).  Both halves are one-sided on purpose: `false` means official
rejects. -/
theorem ind_params_ok_refines {pers st lst} {n_p : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.ind_params_ok pers st n_p block i = ok o) :
    Sim₀ id pers lst o
      (indParamsOk (absU n_p) (absICILFrom block i)) :=
  Lockstep.LS.toSim₀ (ind_params_ok_aux _ i rfl hrel hinv) hrun

open Lockstep in
@[lockstep] theorem ind_params_ok_ls {pers st lst}
    {n_p : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.ind_params_ok pers st n_p block i) lst
      (indParamsOk (absU n_p) (absICILFrom block i)) :=
  LS.ofSim₀ fun _ h => ind_params_ok_refines hrel hinv h

/-! ## `arena::checker_split` — the install/check seam of a value declaration

DESIGN §8.3's per-declaration bracket lives here: the install half writes the
annotated type and the annotated value (the terms the environment stores, so
they must be PERSISTENT and the half runs OUTSIDE the bracket), and the check
half infers and compares (everything it allocates is intermediate, and the
scratch tier is dropped at its end). -/

/-- `is_thm` is the twin's `g.kind == .thm`. -/
theorem is_thm_refines {k : arena.checker_split.ValueKind} {o : Bool}
    (hrun : arena.checker_split.is_thm k = ok o) :
    o = (absValueKind k == .thm) := by
  rw [arena.checker_split.is_thm.eq_def] at hrun
  cases k <;> (
    simp only [] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    rfl)

@[lockstep] theorem Lockstep.is_thm_spec (k : arena.checker_split.ValueKind) :
    LSP (arena.checker_split.is_thm k) (fun o => o = (absValueKind k == .thm)) :=
  fun _ h => is_thm_refines h

/-- **`install_constant_val` ⊑ `installConstantVal`** — `checkConstantVal`
minus its inference: the syntactic guards and the annotation of the type. -/
theorem install_constant_val_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_split.install_constant_val pers vis st mode rf cv = ok o) :
    Sim₀ absIConstantVal pers lst o
      (installConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtx hfe hfinv hvis
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_split.install_constant_val]
  rw [installConstantVal_unfold]
  lockstep

/-- `install_value_tail` is `install_value`'s tail past the annotation. -/
theorem install_value_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {value_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.install_value_tail pers vis st rf cv value_a = ok o) :
    Sim₀ absEIdx pers lst o
      (installValueTailSpec (lf.restrictTo (absU vis)) (absIConstantVal cv)
        (absEIdx value_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_split.install_value_tail]
  try unfold installValueTailSpec
  lockstep

open Lockstep in
@[lockstep] theorem install_value_tail_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv : arena.env.IConstantVal}
    {value_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_split.install_value_tail pers vis st rf cv value_a) lst
      (installValueTailSpec (lf.restrictTo (absU vis)) (absIConstantVal cv)
        (absEIdx value_a)) :=
  LS.ofSim₀ fun _ h => install_value_tail_refines hrel hinv hfe.rel hfe.inv h

/-- **`install_value` ⊑ `installValue`** — the value half of
`check{Defn,Thm,Opaque}Val` minus its inference.  One `lockstep` call. -/
theorem install_value_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.install_value pers vis st mode rf cv value = ok o) :
    Sim₀ absEIdx pers lst o
      (installValue (ConRon.Refine.absMode mode) (lf.restrictTo (absU vis))
        (absIConstantVal cv) (absEIdx value)) := by
  have hctx := IFEnvInv.coreCtxAt vis hfe hfinv
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_split.install_value, installValue_unfold]
  simp only [am_fail_bind]
  lockstep

@[lockstep] theorem Lockstep.install_value_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_split.install_value pers vis st mode rf cv value) lst
      (installValue (ConRon.Refine.absMode mode) lf (absIConstantVal cv)
        (absEIdx value)) := by
  have hlf : lf.restrictTo (absU vis) = lf := by rw [IFEnv.restrictTo, hvis]
  refine LS.ofSim₀ fun _ h => ?_
  have := install_value_refines hrel hinv hfe.rel hfe.inv h
  rwa [hlf] at this

/-- The same at a split scalar: the twin environment viewed at `vis`. -/
@[lockstep] theorem Lockstep.install_value_at_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    {value : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_split.install_value pers vis st mode rf cv value) lst
      (installValue (ConRon.Refine.absMode mode) (lf.restrictTo (absU vis))
        (absIConstantVal cv) (absEIdx value)) :=
  LS.ofSim₀ fun _ h => install_value_refines hrel hinv hfe.rel hfe.inv h

/-- `check_value_group_tail` is `check_value_group`'s tail: the value's type
against the declared one.

**PROVED** (task #97-T2-LOCKSTEP step 1), once the twin's type-mismatch
decline became the Rust's constant `s!"type mismatch in {g.kind.word}"`: the
old twin message read the constant's name (`readName`), a twin-only store read
that throws `.internal` at a dangling name, and that divergence was what
stopped task #97-P5-Top round 3 here.  Since task #97-T2-LOCKSTEP lane
Checker it is one `lockstep` call (`infer_type_core ; is_def_eq_core` at the
prefix view), with no precondition on the twin. -/
theorem check_value_group_tail_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    {jv : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.check_value_group_tail pers vis st mode rf g jv
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkValueGroupTailSpec (ConRon.Refine.absMode mode)
        (lf.restrictTo (absU vis)) (absValueGroup g) (absEIdx jv)) := by
  have hctx := IFEnvInv.coreCtxAt vis hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_split.check_value_group_tail, checkValueGroupTailSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_value_group_tail_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {g : arena.checker_split.ValueGroup}
    {jv : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_split.check_value_group_tail pers vis st mode rf g jv) lst
      (checkValueGroupTailSpec (ConRon.Refine.absMode mode)
        (lf.restrictTo (absU vis)) (absValueGroup g) (absEIdx jv)) :=
  LS.ofSim₀ fun _ h => check_value_group_tail_refines hrel hinv hfe.rel hfe.inv h

/-- `check_value_group_value` is `check_value_group`'s middle: the theorem's
is-a-proposition test and, for a theorem, the value's guards and annotation.

**Open, and stopped on a divergence** (task #97-P5-Top round 3).  The glue is
written in the round-3 log (`is_thm ; zero_level ; lvl_eq ; lift_fueled ;
install_value ; check_value_group_tail`, with `lvl_eq_refines` above), but it
closes only with clauses the statement does not have and, by the
coordinator's round-3 rule, must not grow.  (The NOT-A-PROPOSITION decline,
the third blocker of round 3, is gone: task #97-T2-LOCKSTEP step 1 made the
twin's message the Rust's constant `M_THM_NOT_PROP`, so the twin no longer
reads the name there.)

* (task #97-T2-LOCKSTEP) the `Good`/`EResolves` plumbing that stopped it is
  gone with the lockstep statements; it is one `lockstep` call once
  `install_value_refines` (a leaf) is `@[lockstep]`. -/
theorem check_value_group_value_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    {u : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.check_value_group_value pers vis st mode rf g u
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkValueGroupValueSpec (ConRon.Refine.absMode mode)
        (lf.restrictTo (absU vis)) (absValueGroup g) (absLIdx u)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_split.check_value_group_value]
  unfold checkValueGroupValueSpec
  lockstep

open Lockstep in
@[lockstep] theorem check_value_group_value_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    {u : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) :
    LS pers (fun _ b => b = ())
      (arena.checker_split.check_value_group_value pers vis st mode rf g u) lst
      (checkValueGroupValueSpec (ConRon.Refine.absMode mode)
        (lf.restrictTo (absU vis)) (absValueGroup g) (absLIdx u)) :=
  LS.ofSim₀ fun _ h => check_value_group_value_refines hrel hinv hfe hfinv h

/-- **`check_value_group` ⊑ `checkValueGroup`** — the check half of a value
declaration, at the environment the constant was installed at.

**PROVED** (task #97-P5-Top round 2), under ruling 2's precondition:
`infer_type_core ; ensure_sort_core ; check_value_group_value`, the first two
through `Refine2/Core`'s front doors at the prefix view `CoreCtx vis rf
(lf.restrictTo (absU vis))` (`IFEnvInv.coreCtxAt`) and the knot at
`checkFuel` (`knotRel_checkFuel'`).  **Since task #97-P5-Core round 4 the two
front doors are lockstep statements**, and since task #97-T2-LOCKSTEP lane
Checker so is this one: ruling 2's precondition is gone and the proof is one
`lockstep` call. -/
theorem check_value_group_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.check_value_group pers vis st mode rf g = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkValueGroup (ConRon.Refine.absMode mode) (lf.restrictTo (absU vis))
        (absValueGroup g)) := by
  have hctx := IFEnvInv.coreCtxAt vis hfe hfinv
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_split.check_value_group, checkValueGroup_unfold]
  lockstep

/-! ## The checker's glue callees as `@[lockstep]` specs (task #97-T2-LOCKSTEP lane Checker)

Each is its `_refines` lemma (or a Rust-only value step) in the judgement the
`lockstep` tactic zips with; the environment arguments come as `IFEnvRelI`,
which is what a fold step has in hand. -/

namespace Lockstep

@[lockstep] theorem reduce_op_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.trust_axioms.reduce_op_names st) lst
      reduceOpNames :=
  LS.ofSim₀ fun _ h => reduce_op_names_refines hrel hinv h

@[lockstep] theorem install_constant_val_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.checker_split.install_constant_val pers vis st mode rf cv) lst
      (installConstantVal (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => install_constant_val_refines hrel hinv hfe.rel hfe.inv hvis h

@[lockstep] theorem flush_caches_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.flush_caches st) lst flushCaches :=
  LSW.ofSimS₀ fun _ h => flush_caches_sim₀ hrel hinv h

end Lockstep

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.vec_dup_range_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vec_dup_range_spec

/-- info: 'ConRon.Refine2.vec_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vec_dup_eq

/-- info: 'ConRon.Refine2.pins_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pins_dup_eq

/-- info: 'ConRon.Refine2.nstore_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nstore_dup_eq

/-- info: 'ConRon.Refine2.lstore_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lstore_dup_eq

/-- info: 'ConRon.Refine2.lsstore_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lsstore_dup_eq

/-- info: 'ConRon.Refine2.estore_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms estore_dup_eq

/-- info: 'ConRon.Refine2.attempt_snapshot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms attempt_snapshot_eq

/-- info: 'ConRon.Refine2.memo_b_get_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_b_get_refines

/-- info: 'ConRon.Refine2.is_thm_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_thm_refines

/-- info: 'ConRon.Refine2.consts_resolve_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consts_resolve_aux

/-- info: 'ConRon.Refine2.nidx_is_proj_fn_shape_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nidx_is_proj_fn_shape_refines

/-- info: 'ConRon.Refine2.name_nodup_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms name_nodup_refines

end ConRon.Refine2
