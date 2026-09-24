/-
# `ConRon.Refine2.Checker.Base` — Theorem 2 for `arena::checker_base` and `arena::checker_split`

**Task #97-P5-Checker**, deliverable 2 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{checker_base,checker_split}.rs` against
`proof/ConRon/Arena/{CheckerBase,CheckerSplit}.lean`: the declaration
checker's common ground — the per-declaration constant check, the two
memoised guard walks, the projection-rule stages, the attempt bracket — and
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
copy of the state and `attempt_restore` a move of it back; D4c moves the
persistent tier aside (`freeze_tier`) before that copy and thaws it back
after the attempt, which runs against the frozen tier.  So the snapshot is
the identity in the model (`attempt_snapshot_eq`, from the `dup` lemmas
below), `attempt_restore` is `ok snap`, the freeze/thaw pair reads the same
(`TierView`, `freeze_tier_view`, `thaw_read_tier_view`), and all of it is
lockstep with no hypothesis about the attempt.  The seam itself is
`Refine2/Checker/DeclCheck.lean`'s `check_div_mod_pin_attempt_refines₀`.

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

`Refine2/Specs.lean`'s `view`/`intern_e` family (closed and open
respectively), `Refine2/ExprOps/**` (statements only so far) and
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

/-- `attempt_snapshot` ⊑ `attemptSnapshot` — in Lean the state itself, in Rust
a full copy of it, which is the identity in the model. -/
theorem attempt_snapshot_refines₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.attempt_snapshot st = ok o) :
    AStateRel₀ pers o (attemptSnapshot lst) ∧ AStateInv pers o := by
  obtain rfl := attempt_snapshot_eq hrun
  exact ⟨hrel, hinv⟩

/-- `attempt_restore` ⊑ `attemptRestore` — **lockstep**: both make the
snapshot the state, whatever state they are handed. -/
theorem attempt_restore_refines₀ {pers st lst} {snap lsnap} {o}
    (hsnap : AStateRel₀ pers snap lsnap) (hsinv : AStateInv pers snap)
    (hrun : arena.checker_base.attempt_restore st snap = ok o) :
    AStateRel₀ pers o (attemptRestore lst lsnap) ∧ AStateInv pers o := by
  unfold arena.checker_base.attempt_restore at hrun
  obtain rfl := Result.ok_injective hrun
  exact ⟨hsnap, hsinv⟩

/-- The twin's restore of its own snapshot is the identity — what makes its
error arm "resume at the pre-attempt state". -/
@[simp] theorem attemptRestore_self (s : AState) :
    attemptRestore s (attemptSnapshot s) = s := rfl

/-! ### The frozen tier (task #97-T2-LOCKSTEP D4c)

The seam moves the persistent tier aside for the attempt (`freeze_tier`) and
back after it (`thaw_tier` on `Recovered`, `thaw_read_tier` otherwise).  The
relation reads a store's persistent arm through `rPers*`, which is the store's
own table with its flag down and the tier's with it up, so the whole story is
one congruence: two stores whose four persistent READS, scratch tiers and
scratch flags agree are related to the same twin store (`TierView`). -/

/-- The four `shared_on` flags of a store, down: the shape of every store the
parse and phase A work in, and what `freeze_tier`'s guard checks. -/
def Thawed (ar : arena.store.EStore) : Prop :=
  ar.shared_on = false ∧ ar.lss.shared_on = false ∧ ar.lss.ls.shared_on = false ∧
    ar.lss.ls.ns.shared_on = false

/-- The persistent tier `freeze_tier` moves out of a store: its four own
persistent tables. -/
def tierOf (ar : arena.store.EStore) : arena.store.PersTier :=
  { n := ar.lss.ls.ns.pers, l := ar.lss.ls.pers, ls := ar.lss.pers, e := ar.pers }

/-- **`freeze_tier`'s decline is the port's own**: it claims nothing. -/
theorem freeze_tier_err {ar ar' : arena.store.EStore} {e : kernel.core_types.CheckError}
    (h : arena.checker.freeze_tier ar = ok (.Err e, ar')) :
    absAErrKind e = none := by
  rw [arena.checker.freeze_tier] at h
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp at h'

/-- **`freeze_tier` accepts only a thawed store, and hands back its own
tier**; and `thaw_tier` of what it left, with that tier, is the store it was
handed — the boundary is invisible outside phase B. -/
theorem freeze_tier_ok {ar ar' : arena.store.EStore} {tier : arena.store.PersTier}
    (h : arena.checker.freeze_tier ar = ok (.Ok tier, ar')) :
    Thawed ar ∧ tier = tierOf ar ∧ arena.checker.thaw_tier ar' tier = ok ar := by
  rw [arena.checker.freeze_tier] at h
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h0
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h1
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h2
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h3
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  simp only [Bool.not_eq_true] at h0 h1 h2 h3
  refine ⟨⟨h0, h1, h2, h3⟩, rfl, ?_⟩
  rw [arena.checker.thaw_tier]
  obtain ⟨⟨⟨⟨np, ns, nsc, nsh⟩, lp, ls, lsc, lsh⟩, lsp, lss, lssc, lssh⟩, ep, es, esc, esh⟩ :=
    ar
  simp only at h0 h1 h2 h3
  subst h0 h1 h2 h3
  rfl

/-- Two (tier, store) pairs that READ the same: the four persistent arms, the
four scratch tiers and the four scratch flags agree. -/
structure TierView (p₁ : arena.store.PersTier) (r₁ : arena.store.EStore)
    (p₂ : arena.store.PersTier) (r₂ : arena.store.EStore) : Prop where
  n : rPersN p₂ r₂.lss.ls.ns = rPersN p₁ r₁.lss.ls.ns
  l : rPersL p₂ r₂.lss.ls = rPersL p₁ r₁.lss.ls
  ls : rPersLs p₂ r₂.lss = rPersLs p₁ r₁.lss
  e : rPersE p₂ r₂ = rPersE p₁ r₁
  nScr : r₂.lss.ls.ns.scr = r₁.lss.ls.ns.scr
  lScr : r₂.lss.ls.scr = r₁.lss.ls.scr
  lsScr : r₂.lss.scr = r₁.lss.scr
  eScr : r₂.scr = r₁.scr
  nOn : r₂.lss.ls.ns.scratch_on = r₁.lss.ls.ns.scratch_on
  lOn : r₂.lss.ls.scratch_on = r₁.lss.ls.scratch_on
  lsOn : r₂.lss.scratch_on = r₁.lss.scratch_on
  eOn : r₂.scratch_on = r₁.scratch_on

/-- **The congruence**: a state's relation and invariant carry over to the
same state at a store that reads the same. -/
theorem TierView.transfer {p₁ p₂ : arena.store.PersTier} {r₂ : arena.store.EStore}
    {st : arena.monad.AState} {lst : AState} (hv : TierView p₁ st.store p₂ r₂)
    (hrel : AStateRel₀ p₁ st lst) (hinv : AStateInv p₁ st) :
    AStateRel₀ p₂ { st with store := r₂ } lst ∧ AStateInv p₂ { st with store := r₂ } := by
  obtain ⟨⟨⟨⟨⟨np, ns, non⟩, lp, ls, lon⟩, lsp, lss, lson⟩, ep, es, eon⟩, m, c, pn⟩ := hrel
  obtain ⟨⟨⟨⟨⟨npi, nsi⟩, lpi, lsi⟩, lspi, lssi⟩, epi, esi⟩, mi, ci⟩ := hinv
  refine ⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, m, c, pn⟩,
    ⟨⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, mi, ci⟩⟩ <;>
    simp only [hv.n, hv.l, hv.ls, hv.e, hv.nScr, hv.lScr, hv.lsScr, hv.eScr, hv.nOn,
      hv.lOn, hv.lsOn, hv.eOn] <;> assumption

/-- **`freeze_tier` reads the same**: the frozen store at the tier it handed
back reads what the thawed store read at any tier. -/
theorem freeze_tier_view {pers : arena.store.PersTier} {ar ar' : arena.store.EStore}
    {tier : arena.store.PersTier}
    (h : arena.checker.freeze_tier ar = ok (.Ok tier, ar')) :
    TierView pers ar tier ar' := by
  rw [arena.checker.freeze_tier] at h
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  rename_i h0
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  rename_i h1
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  rename_i h2
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  rename_i h3
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  simp only [Bool.not_eq_true] at h0 h1 h2 h3
  constructor <;> simp [rPersN, rPersL, rPersLs, rPersE, core.mem.replace, h0, h1, h2, h3]

/-- **`thaw_read_tier` reads the same**: each store gets back the table its
reads went to, so at ANY tier the thawed store reads what the frozen store
read at `tier` — whatever the four flags were. -/
theorem thaw_read_tier_view {pers : arena.store.PersTier} {ar ar' : arena.store.EStore}
    {tier : arena.store.PersTier}
    (h : arena.checker.thaw_read_tier ar tier = ok ar') :
    TierView tier ar pers ar' := by
  rw [arena.checker.thaw_read_tier] at h
  obtain ⟨⟨⟨⟨np, ns, non, nsh⟩, lp, ls, lon, lsh⟩, lsp, lss, lson, lssh⟩, ep, es, eon, esh⟩ :=
    ar
  cases nsh <;> cases lsh <;> cases lssh <;> cases esh <;>
    simp only [bind_tc_ok, if_true, if_false, Bool.false_eq_true, ok.injEq] at h <;>
    subst h <;> constructor <;> simp [rPersN, rPersL, rPersLs, rPersE]


/-- `or_else_attempt` ⊑ `orElseStepOf` — the four-way step as a PURE function
of the attempt's outcome, which is the shape the port has and which the twin
copied.  `failed` carries **only** a `native` error (DESIGN §8.3's ruling): the
arena's own machine-word limit has no `throw` behind it in con-leche, so
"con-leche would have recovered from this too" is a claim about a run the
cited checker never has. -/
theorem or_else_attempt_refines {attempt} {o}
    (hrun : arena.checker_base.or_else_attempt attempt = ok o) :
    ∀ b, attempt = .Ok b → o = (if b then .Matched else .Continued) := by
  intro b hb
  subst hb
  rw [arena.checker_base.or_else_attempt] at hrun
  cases b <;> simp_all

/-! ## The `Vec` duplications

`vec_dup` and `vec_dup_range` are `ron::hashmap::Dup` lifted to a vector;
`Refine2/Inv.lean`'s five `DupId` lemmas say `dup2` is the identity at every
handle type, so both are the identity on the abstraction. -/

/-- `vec_dup_range` copies `xs[lo..hi]` onto `out`, `dup2` at each element. -/
theorem vec_dup_range_refines {T β : Type} {A : T → β}
    {inst : ron.hashmap.Dup T} {xs out : alloc.vec.Vec T}
    {lo hi : Std.Usize} {o}
    (hdup : ConRon.Refine.HashMap.DupId inst)
    (hrun : arena.checker_base.vec_dup_range inst xs out lo hi = ok o) :
    o.val.map A = out.val.map A ++
      ((xs.val.drop lo.val).take (hi.val - lo.val)).map A := by
  sorry

/-- `vec_dup` is the identity on the abstraction. -/
theorem vec_dup_refines {T β : Type} {A : T → β} {inst : ron.hashmap.Dup T}
    {xs : alloc.vec.Vec T} {o}
    (hdup : ConRon.Refine.HashMap.DupId inst)
    (hrun : arena.checker_base.vec_dup inst xs = ok o) :
    o.val.map A = xs.val.map A := by
  obtain rfl := vec_dup_eq hdup hrun
  rfl

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
      rw [if_pos hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absNIdxLFrom, List.drop_eq_nil_of_le hle]
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [if_neg hge] at hrun
      obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hlt', rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn1
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := nidx_eq2_abs hb
      have hcons : absNIdxLFrom ns i = absNIdx ns.val[i.val] :: (ns.val.drop (i.val + 1)).map absNIdx := by
        simp only [absNIdxLFrom, List.drop_eq_getElem_cons hlt, List.map_cons]
      rw [hcons, List.contains_cons]
      by_cases hc : b = true
      · rw [if_pos hc] at hrun
        rw [← Result.ok_injective hrun]
        subst hc
        have heq : (absNIdx ns.val[i.val] == absNIdx n) = true := hbv.symm
        rw [BEq.comm] at heq
        simp [heq]
      · rw [if_neg hc] at hrun
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
      rw [if_pos hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absNIdxLFrom, List.drop_eq_nil_of_le hle, nameNodup]
    · have hlt : i.val < ns.val.length := by scalar_tac
      rw [if_neg hge] at hrun
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
      · rw [if_pos hbt] at hrun
        rw [← Result.ok_injective hrun, hbt]
        rfl
      · rw [if_neg hbt] at hrun
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

/-- `nidx_is_model_suffix` ⊑ `NIdx.isModelSuffix`. -/
theorem nidx_is_model_suffix_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.nidx_is_model_suffix pers st n = ok o) :
    SimRE id lst o (NIdx.isModelSuffix (absNIdx n)) := by
  sorry

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
  · rw [if_pos hnum] at hrun
    rw [if_pos (by rw [hnum, ntag_num_abs]; exact beq_self_eq_true _)]
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
        · rw [if_pos hstr] at hrun
          rw [if_pos (by rw [hstr, ntag_str_abs]; exact beq_self_eq_true _)]
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
              · rw [if_pos hbt] at hrun
                obtain rfl := (Result.ok_injective hrun).symm
                have : ConRon.Refine.absString sv = "proj" := by simpa [hbt] using hbv
                show Except.ok _ = Except.ok _
                simp [this]
              · rw [if_neg hbt] at hrun
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
        · rw [if_neg hstr] at hrun
          rw [if_neg (by
            rw [ntag_str_abs.symm.trans rfl] at *
            intro hx
            exact hstr (absU32_inj (by simpa using hx)))]
          obtain rfl := (Result.ok_injective hrun).symm
          rfl
  · rw [if_neg hnum] at hrun
    rw [if_neg (by
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

Both thread a `HashMap2<EIdx, bool>` exactly as `expr_ops`' three memoised
walks do; `Refine2/Checker/Shape.lean`'s `SimBM` / `SimBR` are the two shapes
(the second walk reads the store and interns nothing, so it is a reader). -/

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

/-- `consts_resolve_f_go` ⊑ `constsResolveFGo`.  Finding 10's `hvis`. -/
theorem consts_resolve_f_go_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.consts_resolve_f_go pers vis st rf rm fuel h = ok o) :
    SimBM id pers lst o
      (constsResolveFGo (lf.restrictTo (absU vis)) lm (absU fuel) (absEIdx h)) := by
  sorry

/-- `consts_resolve_f_node` is `consts_resolve_f_go`'s miss arm past the
`view` (extraction rule 5), stated against the twin's arm at that view.

`hnl`: the view is not one of the four leaves.  The Rust answers `false` at a
leaf view and the twin's transcription calls `constsResolve` (`true` at a
`bvar`), so the statement is false there; its one caller,
`consts_resolve_f_go`, reaches it only at the non-leaf views (a Rust-input
fact; coordinator's ruling). -/
theorem consts_resolve_f_node_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {v : arena.store.ENodeView} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hm : ExprOps.LMemoRel rm lm)
    (hview : lst.store.view (absEIdx h) = some (absENodeView v))
    (hnl : match v with
      | .BVar _ | .Sort _ | .Const _ _ | .Lit _ => False
      | _ => True)
    (hrun : arena.checker_base.consts_resolve_f_node pers vis st rf rm fuel v = ok o) :
    SimBM id pers lst o
      (constsResolveFNodeSpec (lf.restrictTo (absU vis)) lm (absU fuel) (absEIdx h)
        (absENodeView v)) := by
  sorry

/-- `consts_resolve_f_two` is the two-child arms' pair, in the twin's order
and WITHOUT a short-circuit (the twin's `.app` arm walks both and `&&`s). -/
theorem consts_resolve_f_two_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rm lm} {fuel : Std.U64} {a b : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.consts_resolve_f_two pers vis st rf rm fuel a b = ok o) :
    SimBM id pers lst o
      (do
        let (b₁, memo) ←
          constsResolveFGo (lf.restrictTo (absU vis)) lm (absU fuel) (absEIdx a)
        let (b₂, memo) ←
          constsResolveFGo (lf.restrictTo (absU vis)) memo (absU fuel) (absEIdx b)
        pure (b₁ && b₂, memo)) := by
  sorry

/-- `consts_resolve_f_fast` ⊑ `constsResolveFFast` — one memoised DAG walk,
which is what every front door below calls. -/
theorem consts_resolve_f_fast_refines {pers st lst} {vis : Std.U64} {rf lf}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_base.consts_resolve_f_fast pers vis st rf e = ok o) :
    Sim₀ id pers lst o
      (constsResolveFFast (lf.restrictTo (absU vis)) (absEIdx e)) := by
  sorry

open Lockstep in
@[lockstep] theorem consts_resolve_f_fast_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.consts_resolve_f_fast pers vis st rf e) lst
      (constsResolveFFast (lf.restrictTo (absU vis)) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => consts_resolve_f_fast_refines hrel hinv hfe.rel hfe.inv h

/-- `all_params_defined_list` is `ls.all (Level.allParamsDefined params)` from
the cursor on — a PURE test on con-leche values, so it carries their WF. -/
theorem all_params_defined_list_refines
    {params : alloc.vec.Vec kernel.name.Name}
    {ls : alloc.vec.Vec kernel.level.Level} {i : Std.Usize} {o : Bool}
    (hp : NamesWF params) (hl : ConRon.Refine.LevelsWF ls)
    (hrun : arena.checker_base.all_params_defined_list params ls i = ok o) :
    o = (absLevelLFrom ls i).all
      (ConLeche.Level.allParamsDefined (ConRon.Refine.absNames params)) := by
  sorry

/-- `all_level_params_defined_go` ⊑ `allLevelParamsDefinedGo` — a READER
(`SimBR`): the level-parameter test interns nothing. -/
theorem all_level_params_defined_go_refines {pers st lst}
    {params : alloc.vec.Vec kernel.name.Name} {rm lm} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hp : NamesWF params) (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.checker_base.all_level_params_defined_go pers st params rm fuel h
      = ok o) :
    SimBR id lst o
      (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm (absU fuel)
        (absEIdx h)) := by
  sorry

/-- `all_level_params_defined_node` is the walk's miss arm past the probe. -/
theorem all_level_params_defined_node_refines {pers st lst}
    {params : alloc.vec.Vec kernel.name.Name} {rm lm} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hp : NamesWF params) (hm : ExprOps.LMemoRel rm lm)
    (hmiss : lm[absEIdx h]? = none)
    (hrun : arena.checker_base.all_level_params_defined_node pers st params rm fuel h
      = ok o) :
    SimBR id lst o
      (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm (absU fuel)
        (absEIdx h)) := by
  sorry

/-- `all_level_params_defined_binder` is the walk's `.lam` / `.forallE` arm —
the one that also tests the binder metadatum's `PropWhen`. -/
theorem all_level_params_defined_binder_refines {pers st lst}
    {params : alloc.vec.Vec kernel.name.Name} {rm lm} {fuel : Std.U64}
    {t b : arena.handle.EIdx} {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hp : NamesWF params) (hm : ExprOps.LMemoRel rm lm)
    (hmwf : ConRon.Refine.BinderMetaWF m)
    (hrun : arena.checker_base.all_level_params_defined_binder pers st params rm
      fuel t b m = ok o) :
    SimBR id lst o
      (do
        let (b₁, memo) ← allLevelParamsDefinedGo (ConRon.Refine.absNames params)
          lm (absU fuel) (absEIdx t)
        if !b₁ then pure (false, memo) else do
          let (b₂, memo) ← allLevelParamsDefinedGo (ConRon.Refine.absNames params)
            memo (absU fuel) (absEIdx b)
          pure (b₂ && (ConRon.Refine.absBinderMeta m).pw.paramsDefined
            (ConRon.Refine.absNames params), memo)) := by
  sorry

/-- `all_level_params_defined` ⊑ `allLevelParamsDefined` — one memoised DAG
walk, at the parameter list read back once. -/
theorem all_level_params_defined_refines {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.all_level_params_defined pers st lps e = ok o) :
    SimRE id lst o (allLevelParamsDefined (absNIdxL lps) (absEIdx e)) := by
  sorry

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

@[lockstep] theorem Lockstep.nidx_vec_dup_spec (v : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.env.nidx_vec_dup v) (fun r => r = v) :=
  fun _ h => alloc.vec.Vec.ext _ _ (nidx_vec_dup_val h)

/-! ### Twin readers leave the state alone

The twin's pin reads (`natOpNames`, `natDivModNames`, `reduceOpNames`) read
the pin table and write nothing — a fact about the twin alone, which the
parser tier's `is_nat_op_record_refines` uses to keep its old-shape
statement across a lockstep reader. -/

/-- A twin action that never changes the state it succeeds from. -/
def AMReads {α : Type} (x : AM α) : Prop :=
  ∀ (s : AState) (v : α) (s' : AState), x.run s = .ok (v, s') → s' = s

theorem AMReads.pure' {α : Type} (a : α) : AMReads (pure a : AM α) := by
  intro s v s' h
  have h' : (Except.ok (a, s) : Except Arena.CheckError (α × AState)) = .ok (v, s') := h
  cases h'
  rfl

theorem AMReads.bind' {α β : Type} {x : AM α} {f : α → AM β} (hx : AMReads x)
    (hf : ∀ a, AMReads (f a)) : AMReads (x >>= f) := by
  intro s v s' h
  rw [am_run_bind'] at h
  cases hx' : x.run s with
  | error e => rw [hx'] at h; cases h
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [hx', except_ok_bind] at h
    rw [hf a s1 v s' h, hx s a s1 hx']

theorem pinAt_reads (i : Nat) : AMReads (pinAt i) := by
  intro s v s' h
  by_cases hi : i < s.pins.names.size
  · have h2 : (Arena.pinAt i).run s = .ok (s.pins.names[i], s) := by
      show (Arena.pinAt i) s = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, dif_pos hi]
    rw [h2] at h
    cases h
    rfl
  · have h2 : (Arena.pinAt i).run s
        = .error (Arena.CheckError.internal "arena: reserved-name pins not interned") := by
      show (Arena.pinAt i) s = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, dif_neg hi,
        Arena.fail, throwThe, MonadExceptOf.throw,
        Function.comp_apply, StateT.lift]
    rw [h2] at h
    cases h

theorem natOpNames_reads : AMReads natOpNames := by
  unfold natOpNames
  repeat (first | exact AMReads.pure' _ | refine AMReads.bind' (pinAt_reads _) fun _ => ?_)

theorem natDivModNames_reads : AMReads natDivModNames := by
  unfold natDivModNames
  repeat (first | exact AMReads.pure' _ | refine AMReads.bind' (pinAt_reads _) fun _ => ?_)

theorem reduceOpNames_reads : AMReads reduceOpNames := by
  unfold reduceOpNames
  repeat (first | exact AMReads.pure' _ | refine AMReads.bind' (pinAt_reads _) fun _ => ?_)

open Lockstep in
@[lockstep] theorem all_level_params_defined_ls {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.checker_base.all_level_params_defined pers st lps e) st lst
      (allLevelParamsDefined (absNIdxL lps) (absEIdx e)) :=
  LSR.ofSimRE hrel hinv fun _ h => all_level_params_defined_refines hrel hinv h

open Lockstep in
/-- `lift_fueled` ⊑ `liftFueled what`, for every message `what`: a fuel-out
`none` is an `internal` error on both sides (the messages are not compared;
the tactic fixes `what` from the goal's twin, task #97-T2-TACTIC round 2). -/
@[lockstep] theorem lift_fueled_ls {pers st lst} {what : String}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (o : Option Bool) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst
      (liftFueled what o) := by
  intro r h
  cases o with
  | some b =>
    simp only [arena.core.lift_fueled, Result.ok.injEq] at h
    subst h
    exact ⟨b, lst, rfl, rfl, hrel, hinv⟩
  | none =>
    simp only [arena.core.lift_fueled] at h
    obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [fail_run h]
    exact errSim_fail rfl

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

@[lockstep_simp] theorem absIConstantVal_type (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).type = absEIdx cv.ty := rfl

attribute [lockstep_simp] core.option.Option.is_some Option.isSome_map ite_true ite_false

/-- The environment viewed at its own counter is itself. -/
@[lockstep_simp] theorem IFEnv.restrictTo_visibleBelow (fe : IFEnv) :
    fe.restrictTo fe.visibleBelow = fe := rfl

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

/-- `IFEnv.restrictTo` twice is the second one. -/
@[lockstep_simp] theorem IFEnv.restrictTo_restrictTo (fe : IFEnv) (a b : Nat) :
    (fe.restrictTo a).restrictTo b = fe.restrictTo b := rfl

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

@[lockstep] theorem ifenv_push_spec {rf lf} (hfe : IFEnvRelI rf lf)
    (ci : arena.env.IConstantInfo) :
    LSP (arena.env.ifenv_push rf ci)
      (fun r => IFEnvRelI r (lf.push (absIConstantInfo ci)) ∧
        rf.visible_below.val ≤ r.visible_below.val) :=
  fun _ h => ⟨ifenv_push_refines hfe.rel hfe.inv h, by rw [ifenv_push_vis h]; omega⟩

@[lockstep_simp] theorem absNIdxLFrom_zero (ns : alloc.vec.Vec arena.handle.NIdx) :
    absNIdxLFrom ns 0#usize = absNIdxL ns := by simp [absNIdxLFrom, absNIdxL]

attribute [lockstep_simp] absIConstantInfo absValueGroup absValueKind Option.map_some
  Option.map_none

@[lockstep_simp] theorem absINatOpPinSetLFrom_zero
    (v : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) :
    absINatOpPinSetLFrom v 0#usize = absINatOpPinSetL v := by
  simp [absINatOpPinSetLFrom, absINatOpPinSetL]

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

/-- `open_pis_at_fvars` ⊑ `openPisAtFvars` — structural on `n`, so no fuel of
its own. -/
theorem open_pis_at_fvars_refines {pers st lst} {n : Std.U64}
    {h : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.open_pis_at_fvars pers st n h i = ok o) :
    Sim₀ (Option.map (fun p => (absEIdxL p.1, absEIdx p.2)))
      pers lst o (openPisAtFvars (absU n) (absEIdx h) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem open_pis_at_fvars_ls {pers st lst}
    {n : Std.U64}
    {h : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a)
      (arena.checker_base.open_pis_at_fvars pers st n h i) lst
      (openPisAtFvars (absU n) (absEIdx h) (absU i)) :=
  LS.ofSim₀ fun _ h => open_pis_at_fvars_refines hrel hinv h

/-- `open_pis_at_fvars_f_go` ⊑ `openPisAtFvarsFGo` — `acc` holds the
already-created fvars, innermost binder first; one `instantiateList` pass per
domain instead of one whole-telescope `instantiate1` pass per binder. -/
theorem open_pis_at_fvars_f_go_refines {pers st lst}
    {acc : alloc.vec.Vec arena.handle.EIdx} {n : Std.U64}
    {h : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.open_pis_at_fvars_f_go pers st acc n h i = ok o) :
    Sim₀ (Option.map (fun p => (absEIdxL p.1, absEIdx p.2)))
      pers lst o
      (openPisAtFvarsFGo (absEIdxL acc).toArray (absU n) (absEIdx h) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem open_pis_at_fvars_f_go_ls {pers st lst}
    {acc : alloc.vec.Vec arena.handle.EIdx}
    {n : Std.U64}
    {h : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a)
      (arena.checker_base.open_pis_at_fvars_f_go pers st acc n h i) lst
      (openPisAtFvarsFGo (absEIdxL acc).toArray (absU n) (absEIdx h) (absU i)) :=
  LS.ofSim₀ fun _ h => open_pis_at_fvars_f_go_refines hrel hinv h

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

/-- `fvar_type_ds` ⊑ `fvarTypeDs` at the cursor — `xs.map Expr.fvarTypeD`,
with DESIGN §3.4's closure-free `List` recursion. -/
theorem fvar_type_ds_refines {pers st lst}
    {hs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.fvar_type_ds pers st hs i out = ok o) :
    SimRE absEIdxL lst o
      (do pure (absEIdxL out ++ (← fvarTypeDs (absEIdxLFrom hs i)))) := by
  sorry

/-! ## The equality head -/

/-- `is_eq_head` ⊑ `isEqHead` — is the expression the pinned equality former at
one level? -/
theorem is_eq_head_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.is_eq_head pers st h = ok o) :
    Sim₀ id pers lst o (isEqHead (absEIdx h)) := by
  sorry

open Lockstep in
@[lockstep] theorem is_eq_head_ls {pers st lst}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.is_eq_head pers st h) lst
      (isEqHead (absEIdx h)) :=
  LS.ofSim₀ fun _ h => is_eq_head_refines hrel hinv h

/-- `eq_head_level_at` is `eq_head_level`'s tail at the universe-argument list
(extraction rule 5). -/
theorem eq_head_level_at_refines {pers st lst} {us : arena.handle.LsIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.eq_head_level_at pers st us = ok o) :
    Sim₀ absLIdx pers lst o
      (do
        match ← viewLs (absLsIdx us) with
        | [l] => pure l
        | _ => zeroLevel) := by
  sorry

open Lockstep in
@[lockstep] theorem eq_head_level_at_ls {pers st lst}
    {us : arena.handle.LsIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a)
      (arena.checker_base.eq_head_level_at pers st us) lst
      (do
        match ← viewLs (absLsIdx us) with
        | [l] => pure l
        | _ => zeroLevel) :=
  LS.ofSim₀ fun _ h => eq_head_level_at_refines hrel hinv h

/-- `eq_head_level` ⊑ `eqHeadLevel` — off shape it is `.zero`, which
`isEqHead` has already rejected wherever the result is used. -/
theorem eq_head_level_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.eq_head_level pers st h = ok o) :
    Sim₀ absLIdx pers lst o (eqHeadLevel (absEIdx h)) := by
  sorry

open Lockstep in
@[lockstep] theorem eq_head_level_ls {pers st lst}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a)
      (arena.checker_base.eq_head_level pers st h) lst
      (eqHeadLevel (absEIdx h)) :=
  LS.ofSim₀ fun _ h => eq_head_level_refines hrel hinv h

/-! ## The three list checks -/

/-- `check_typed_list` ⊑ `checkTypedList` at the cursor. -/
theorem check_typed_list_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {depth : Std.U64}
    {xs ts : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_typed_list pers vis st mode rf depth xs ts i
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkTypedList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ts i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_typed_list_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {xs ts : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_typed_list pers vis st mode rf depth xs ts i) lst
      (checkTypedList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ts i)) :=
  LS.ofSim₀ fun _ h => check_typed_list_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_annot_list` ⊑ `checkAnnotList` at the cursor. -/
theorem check_annot_list_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {depth : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_annot_list pers vis st mode rf depth xs i
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkAnnotList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_annot_list_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_annot_list pers vis st mode rf depth xs i) lst
      (checkAnnotList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i)) :=
  LS.ofSim₀ fun _ h => check_annot_list_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_def_eq_list` ⊑ `checkDefEqList` at the cursor. -/
theorem check_def_eq_list_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {depth : Std.U64}
    {xs ys : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_def_eq_list pers vis st mode rf depth xs ys i
      = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o
      (checkDefEqList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ys i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_def_eq_list_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {xs ys : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.checker_base.check_def_eq_list pers vis st mode rf depth xs ys i) lst
      (checkDefEqList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ys i)) :=
  LS.ofSim₀ fun _ h => check_def_eq_list_refines hrel hinv hfe.rel hfe.inv hvis h

/-! ## `unwrapOr`, the environment lookup and the pi result sort -/

/-- `unwrap_or` ⊑ `unwrapOr` — unwrap an optional value or fail with the given
error.  Polymorphic, so the abstraction of the element and the correspondence
of the two errors are both parameters. -/
theorem unwrap_or_refines {T β : Type} {A : T → β} {lst} {o : Option T}
    {err : kernel.core_types.CheckError} {lerr : Arena.CheckError} {r}
    (herr : absAErrKind err = lAErrKind lerr)
    (hrun : arena.checker_base.unwrap_or o err = ok r) :
    SimRE A lst r (unwrapOr (o.map A) lerr) := by
  sorry

/-- `ifenv_find_cv` ⊑ `IFEnv.findCV?`.  Finding 10's `hvis`. -/
theorem ifenv_find_cv_refines {pers st lst} {vis : Std.U64} {rf lf}
    {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.ifenv_find_cv pers vis st rf n = ok o) :
    Sim₀ (Option.map absIConstantVal) pers lst o
      (lf.findCV? (absNIdx n)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.checker_base.ifenv_find_cv]
  unfold IFEnv.findCV?
  lockstep
  -- the store-level `to_constant_val` after the Rust-only `i_constant_info_dup`:
  -- the twin reads the constant the index handed back, the Rust its copy
  all_goals
    refine Lockstep.LSS.bind (Lockstep.i_constant_info_to_constant_val_lss ‹_› ‹_› _) ?_
      (fun e s' => Lockstep.errArm_ok) (fun a b s' lst1 hR hrel hinv => ?_)
    · rw [i_constant_info_dup_abs ‹arena.env.i_constant_info_dup _ = ok _›]; rfl
    · lockstep

open Lockstep in
@[lockstep] theorem ifenv_find_cv_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (Option.map absIConstantVal) a)
      (arena.checker_base.ifenv_find_cv pers vis st rf n) lst
      (lf.findCV? (absNIdx n)) :=
  LS.ofSim₀ fun _ h => ifenv_find_cv_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `pi_result_sort` ⊑ `piResultSort`. -/
theorem pi_result_sort_refines {pers st lst} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.pi_result_sort pers st e = ok o) :
    SimRE (Option.map absLIdx) lst o (piResultSort (absEIdx e)) := by
  sorry

/-! ## The projection stages

`checkProjShape` (stage 2b) and `checkProjRule` (stage 3) are twinned in
`Arena/CheckerBase.lean` because they need nothing from
`ConLeche/Kernel/Inductives/*`.  The Rust splits stage 3 into six, which is
extraction rule 5 at a function with eleven live handles. -/

/-- `doms_match_aux_from` ⊑ `domsMatchAux` from the cursor on — over handles a
domain comparison is a handle comparison, so this is PURE. -/
theorem doms_match_aux_from_refines
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n i : Std.U64} {o : Bool}
    (hrun : arena.checker_base.doms_match_aux_from bs1 bs2 o1 o2 n i = ok o) :
    o = (List.range (absU n - absU i)).all fun j =>
      match (absBinderArr bs1)[absU o1 + absU i + j]?,
            (absBinderArr bs2)[absU o2 + absU i + j]? with
      | some b₁, some b₂ => b₁.1 == b₂.1
      | _, _ => false := by
  sorry

/-- `doms_match_aux` ⊑ `domsMatchAux` — con-leche's `List` version is
quadratic on a wide telescope and its `Array` twin is what the checker runs,
so the twin is the array one. -/
theorem doms_match_aux_refines
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 n : Std.U64} {o : Bool}
    (hrun : arena.checker_base.doms_match_aux bs1 bs2 o1 o2 n = ok o) :
    o = domsMatchAux (absBinderArr bs1) (absBinderArr bs2)
      (absU o1) (absU o2) (absU n) := by
  sorry

/-- `check_proj_shape_residual` is `check_proj_shape`'s tail: the
constructor's residual is the family applied to exactly the parameters. -/
theorem check_proj_shape_residual_refines {pers st lst}
    {cbody : arena.handle.EIdx} {n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.check_proj_shape_residual pers st cbody n_p = ok o) :
    SimRE (fun _ : Unit => ()) lst o
      (do
        unless (← getAppArgs coreWalkFuel (absEIdx cbody)).length == absU n_p do
          fail (.notImplemented "projection constructor residual arity")
        match ← view (← getAppFn coreWalkFuel (absEIdx cbody)) with
        | .const _ _ => pure ()
        | _ => fail (.notImplemented "projection constructor residual head")) := by
  sorry

/-- `check_proj_shape` ⊑ `checkProjShape` — stage 2b. -/
theorem check_proj_shape_refines {pers st lst}
    {pty ctor_ty : arena.handle.EIdx} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.checker_base.check_proj_shape pers st pty ctor_ty n_p n_f = ok o) :
    SimRE (fun _ : Unit => ()) lst o
      (checkProjShape (absEIdx pty) (absEIdx ctor_ty) (absU n_p) (absU n_f)) := by
  sorry

/-- `proj_rule_wf` is `check_proj_rule`'s four-way well-formedness conjunct. -/
theorem proj_rule_wf_refines {pers st lst} {vis : Std.U64} {rf lf}
    {rhs_a : arena.handle.EIdx} {lps : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.proj_rule_wf pers vis st rf rhs_a lps = ok o) :
    Sim₀ id pers lst o
      (do
        pure ((← allLevelParamsDefined (absNIdxL lps) (absEIdx rhs_a)) &&
          (← constsResolveFFast lf (absEIdx rhs_a)) &&
          (← looseBVarsBoundedFast coreWalkFuel 0 (absEIdx rhs_a)) &&
          !(← hasFvarFast coreWalkFuel (absEIdx rhs_a)))) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_rule_wf_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {rhs_a : arena.handle.EIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a)
      (arena.checker_base.proj_rule_wf pers vis st rf rhs_a lps) lst
      (do
        pure ((← allLevelParamsDefined (absNIdxL lps) (absEIdx rhs_a)) &&
          (← constsResolveFFast lf (absEIdx rhs_a)) &&
          (← looseBVarsBoundedFast coreWalkFuel 0 (absEIdx rhs_a)) &&
          !(← hasFvarFast coreWalkFuel (absEIdx rhs_a)))) :=
  LS.ofSim₀ fun _ h => proj_rule_wf_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_proj_rule_frame` is stage 3's parameter-frame check: the type's
telescope opened at fresh free variables, the constructor's domains
instantiated at them and compared. -/
theorem check_proj_rule_frame_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {n_p n_f : Std.U64}
    {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {crest_p rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_frame pers vis st mode rf n_p n_f
      fvs_p crest_p rhs_a = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjRuleFrameSpec (ConRon.Refine.absMode mode) lf (absU n_p) (absU n_f)
        (absEIdxL fvs_p) (absEIdx crest_p) (absEIdx rhs_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_rule_frame_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {n_p n_f : Std.U64}
    {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {crest_p rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_base.check_proj_rule_frame pers vis st mode rf n_p n_f
      fvs_p crest_p rhs_a) lst
      (checkProjRuleFrameSpec (ConRon.Refine.absMode mode) lf (absU n_p) (absU n_f)
        (absEIdxL fvs_p) (absEIdx crest_p) (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_frame_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_proj_rule_certs` is stage 3's certificate tail. -/
theorem check_proj_rule_certs_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_certs pers vis st mode rf pty cvj
      n_p n_f rhs_a = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjRuleCertsSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx rhs_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_rule_certs_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_base.check_proj_rule_certs pers vis st mode rf pty cvj
      n_p n_f rhs_a) lst
      (checkProjRuleCertsSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_certs_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_proj_rule_shape` is stage 3's λ-telescope shape check. -/
theorem check_proj_rule_shape_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {bv rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_shape pers vis st mode rf pty cvj
      n_p n_f bv rhs_a = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjRuleShapeSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_rule_shape_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {bv rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_base.check_proj_rule_shape pers vis st mode rf pty cvj
      n_p n_f bv rhs_a) lst
      (checkProjRuleShapeSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_shape_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_proj_rule_wf` is stage 3 past the annotation. -/
theorem check_proj_rule_wf_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {bv rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_wf pers vis st mode rf pty cvj lps
      n_p n_f bv rhs_a = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjRuleWfSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_rule_wf_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {bv rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_base.check_proj_rule_wf pers vis st mode rf pty cvj lps
      n_p n_f bv rhs_a) lst
      (checkProjRuleWfSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_wf_refines hrel hinv hfe.rel hfe.inv hvis h

/-- `check_proj_rule_scoped` is stage 3 past the scoping test. -/
theorem check_proj_rule_scoped_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {bv rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule_scoped pers vis st mode rf pty cvj lps
      n_p n_f bv rhs = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjRuleScopedSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_rule_scoped_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {bv rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_base.check_proj_rule_scoped pers vis st mode rf pty cvj lps
      n_p n_f bv rhs) lst
      (checkProjRuleScopedSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_scoped_refines hrel hinv hfe.rel hfe.inv hvis h

/-- **`check_proj_rule` ⊑ `checkProjRule`** — stage 3, whole: λ over the
constructor telescope returning field `i`, annotated; its λ-domains stay the
constructor's. -/
theorem check_proj_rule_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.checker_base.check_proj_rule pers vis st mode rf pty cvj lps
      n_p n_f i = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjRule (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_rule_ls {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a)
      (arena.checker_base.check_proj_rule pers vis st mode rf pty cvj lps
      n_p n_f i) lst
      (checkProjRule (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absU i)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_refines hrel hinv hfe.rel hfe.inv hvis h

/-! ## The block's partition and its declared parameter count -/

/-- `is_rec_info` ⊑ `isRecInfo`. -/
theorem is_rec_info_refines {ci : arena.env.IConstantInfo} {o : Bool}
    (hrun : arena.checker_base.is_rec_info ci = ok o) :
    o = isRecInfo (absIConstantInfo ci) := by
  rw [arena.checker_base.is_rec_info.eq_def] at hrun
  cases ci <;> (
    simp only [] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    rfl)

/-- The block's cursor at a position inside it: the element, then the rest. -/
theorem absICILFrom_cons {block : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    (hlt : i.val < block.val.length) :
    absICILFrom block i
      = absIConstantInfo block.val[i.val] :: (block.val.drop (i.val + 1)).map absIConstantInfo := by
  simp only [absICILFrom, List.drop_eq_getElem_cons hlt, List.map_cons]

private theorem all_rec_info_aux {block : alloc.vec.Vec arena.env.IConstantInfo} (m : Nat) :
    ∀ {i : Std.Usize} {o : Bool}, block.val.length - i.val = m →
      arena.checker_base.all_rec_info block i = ok o →
      o = (absICILFrom block i).all isRecInfo := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i o hm hrun
    rw [arena.checker_base.all_rec_info.eq_def] at hrun
    dsimp only at hrun
    have hl := alloc.vec.Vec.len_val block
    by_cases hge : i ≥ block.len
    · have hle : block.val.length ≤ i.val := by scalar_tac
      rw [if_pos hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absICILFrom, List.drop_eq_nil_of_le hle]
    · have hlt : i.val < block.val.length := by scalar_tac
      rw [if_neg hge] at hrun
      obtain ⟨c, hc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨_, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hc
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := is_rec_info_refines hb
      rw [absICILFrom_cons hlt, List.all_cons, ← hbv]
      by_cases hbt : b = true
      · rw [if_pos hbt] at hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (block.val.length - i2.val) (by omega) rfl hrun
        rw [hrec, hbt]
        simp [absICILFrom, hi2v]
      · rw [if_neg hbt] at hrun
        rw [← Result.ok_injective hrun]
        simp [hbt]

private theorem recs_form_suffix_aux {block : alloc.vec.Vec arena.env.IConstantInfo}
    (m : Nat) :
    ∀ {i : Std.Usize} {o : Bool}, block.val.length - i.val = m →
      arena.checker_base.recs_form_suffix block i = ok o →
      o = recsFormSuffix (absICILFrom block i) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i o hm hrun
    rw [arena.checker_base.recs_form_suffix.eq_def] at hrun
    dsimp only at hrun
    have hl := alloc.vec.Vec.len_val block
    by_cases hge : i ≥ block.len
    · have hle : block.val.length ≤ i.val := by scalar_tac
      rw [if_pos hge] at hrun
      rw [← Result.ok_injective hrun]
      simp [absICILFrom, List.drop_eq_nil_of_le hle, recsFormSuffix]
    · have hlt : i.val < block.val.length := by scalar_tac
      rw [if_neg hge] at hrun
      obtain ⟨c, hc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨_, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hc
      obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hbv := is_rec_info_refines hb
      rw [absICILFrom_cons hlt, recsFormSuffix, ← hbv]
      by_cases hbt : b = true
      · rw [if_pos hbt] at hrun ⊢
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hdrop : (block.val.drop (i.val + 1)).map absIConstantInfo
            = absICILFrom block i2 := by simp [absICILFrom, hi2v]
        rw [hdrop]
        exact all_rec_info_aux _ rfl hrun
      · rw [if_neg hbt] at hrun ⊢
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hdrop : (block.val.drop (i.val + 1)).map absIConstantInfo
            = absICILFrom block i2 := by simp [absICILFrom, hi2v]
        rw [hdrop]
        exact ih (block.val.length - i2.val) (by omega) rfl hrun

/-- `all_rec_info` is `rest.all isRecInfo` from the cursor on. -/
theorem all_rec_info_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.checker_base.all_rec_info block i = ok o) :
    o = (absICILFrom block i).all isRecInfo :=
  all_rec_info_aux _ rfl hrun

/-- `recs_form_suffix` ⊑ `recsFormSuffix` from the cursor on — do the
recursors form a suffix of the block? -/
theorem recs_form_suffix_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.checker_base.recs_form_suffix block i = ok o) :
    o = recsFormSuffix (absICILFrom block i) :=
  recs_form_suffix_aux _ rfl hrun

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

/-! ## `arena::core::lvl_eq` — the cached level comparison (task #97-P5-Top round 3)

`check_value_group_value`'s theorem arm asks `lvl_eq u zero`, and no tier had
stated `lvl_eq` against `lvlEq?`: the Core knot's own level comparisons go
through `lvls_eq`, and the Inductives tier's are inside sorried shapes.  The
proof is `Refine2/Core/Probes.lean`'s probe/write pair at the `lvlEqC` table
(key `LIdxPair`, value `Bool`, so no value abstraction), around
`read_level_m_run` twice and the old tier's `Level.is_equiv_refines`. -/

private theorem absLIdx_surj' : Function.Surjective absLIdx := by
  intro i
  obtain ⟨w⟩ := i
  obtain ⟨x, hx⟩ := absU32_surj w
  exact ⟨⟨x⟩, by simp [absLIdx, hx]⟩

theorem absLIdxPair_surj : Function.Surjective absLIdxPair := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := absLIdx_surj' a
  obtain ⟨y, hy⟩ := absLIdx_surj' b
  exact ⟨⟨x, y⟩, by simp [absLIdxPair, hx, hy]⟩

theorem absLIdxPair_inj : Function.Injective absLIdxPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [absLIdxPair, Prod.mk.injEq] at h
  simp [absLIdx_inj h.1, absLIdx_inj h.2]

/-- `arena::core::lvl_eq_probe` against `lst.caches.lvlEqC[·]?`. -/
theorem lvl_eq_probe_abs {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {k : arena.core_state.LIdxPair} {o : Option Bool}
    (hrun : arena.core.lvl_eq_probe st k = ok o) :
    o = lst.caches.lvlEqC[absLIdxPair k]? := by
  rw [arena.core.lvl_eq_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidxPair_eq2 hinv.caches.lvlEqC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.lvlEqC k trivial
  have ho : o = r := by
    cases r with
    | none => exact (Result.ok_injective hrun).symm
    | some _ => exact (Result.ok_injective hrun).symm
  rw [ho, ← hrelk, ← hto]
  simp

/-- The twin's cache hit. -/
theorem lvlEq?_hit {u v : LIdx} {lst : AState} {r : Bool}
    (h : lst.caches.lvlEqC[(u, v)]? = some r) :
    (lvlEq? u v).run lst = .ok (some r, lst) := by
  show (lvlEq? u v) lst = _
  simp only [lvlEq?, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Pure.pure, StateT.pure, Except.bind, Except.pure, h]

/-- The twin's cache miss: the two reads, the verdict, and the capped write. -/
theorem lvlEq?_miss {u v : LIdx} {lst : AState}
    (h : lst.caches.lvlEqC[(u, v)]? = none) :
    (lvlEq? u v).run lst = (do
      let lu ← readLevelM u
      let lv ← readLevelM v
      match ConLeche.Level.isEquiv lu lv with
      | some r => do
        let s ← get
        let mp := if s.caches.lvlEqC.size < cacheCap then s.caches.lvlEqC else ∅
        set { s with caches := { s.caches with lvlEqC := mp.insert (u, v) r } }
        pure (some r)
      | none => pure none : AM (Option Bool)).run lst := by
  show (lvlEq? u v) lst = _
  simp only [lvlEq?, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Pure.pure, Except.bind, Except.pure, h]
  rfl

/-- **`lvl_eq` ⊑ `lvlEq?`** — the cached universe comparison. -/
theorem lvl_eq_refines {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {u v : arena.handle.LIdx} {o}
    (hrun : arena.core.lvl_eq pers st u v = ok o) :
    Sim₀ id pers lst o (lvlEq? (absLIdx u) (absLIdx v)) := by
  rw [arena.core.lvl_eq] at hrun
  obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hkv : absLIdxPair k = (absLIdx u, absLIdx v) := by
    rw [arena.core_state.lidx_pair] at hk
    obtain ⟨a, ha, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk
    obtain ⟨b, hb, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk
    have hk' := (Result.ok_injective hk).symm
    subst hk'
    simp [absLIdxPair, dupId_lidx _ _ ha, dupId_lidx _ _ hb]
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hpe := lvl_eq_probe_abs hrel hinv hp
  rw [hkv] at hpe
  unfold Sim₀
  cases p with
  | some r =>
    have ho := (Result.ok_injective hrun).symm
    subst ho
    exact AOut₀.ok (lvlEq?_hit hpe.symm) hrel hinv
  | none =>
  rw [lvlEq?_miss hpe.symm]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hwf1 := (read_level_m_wf hinv hq1).1
  have hS1 := read_level_m_run₀ hrel hinv hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok lu =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hwf2 := (read_level_m_wf hinv1 hq2).1
  have hS2 := read_level_m_run₀ hrel1 hinv1 hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok lv =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have heq := ConRon.Refine.Level.is_equiv_refines (hwf1 lu rfl) (hwf2 lv rfl) ho1
  simp only at heq ⊢
  rw [heq]
  cases o1 with
  | none =>
    have ho := (Result.ok_injective hrun).symm
    subst ho
    exact AOut₀.ok rfl hrel2 hinv2
  | some r =>
  obtain ⟨st3, hst3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have ho := (Result.ok_injective hrun).symm
  subst ho
  rw [arena.core.lvl_eq_set] at hst3
  obtain ⟨n, hn, hst3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst3
  obtain ⟨hm, hfit, hst3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst3
  obtain ⟨pp, hpp, hst3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst3
  obtain ⟨old, hm2⟩ := pp
  have hst : st3 = { st2 with caches := { st2.caches with lvl_eq_c := hm2 } } :=
    (Result.ok_injective hst3).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step lidxPair_eq2 absLIdxPair_surj absLIdxPair_inj
    hinv2.caches.lvlEqC hrel2.caches.lvlEqC hn hfit hpp
  rw [hkv] at h1
  let mp0 := if lst2.caches.lvlEqC.size < cacheCap then lst2.caches.lvlEqC else ∅
  let mp2 := mp0.insert (absLIdx u, absLIdx v) r
  exact AOut₀.ok (lst' := { lst2 with caches := { lst2.caches with lvlEqC := mp2 } }) rfl
    { hrel2 with caches := { hrel2.caches with lvlEqC := h1 } }
    { hinv2 with caches := { hinv2.caches with lvlEqC := h2 } }

open Lockstep in
@[lockstep] theorem lvl_eq_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {u v : arena.handle.LIdx} :
    LS pers (fun a b => b = id a)
      (arena.core.lvl_eq pers st u v) lst
      (lvlEq? (absLIdx u) (absLIdx v)) :=
  LS.ofSim₀ fun _ h => lvl_eq_refines hrel hinv h

/-! ## `arena::checker_split` — the install/check seam of a value declaration

DESIGN §8.3's per-declaration bracket lives here: the install half writes the
annotated type and the annotated value (the terms the environment stores, so
they must be PERSISTENT and the half runs OUTSIDE the bracket), and the check
half infers and compares (everything it allocates is intermediate, and the
scratch tier is dropped at its end). -/

/-- `value_kind_word` ⊑ `ValueKind.word` — the kind's word in `checkDecl`'s
type-mismatch message, as code points (DESIGN §3.3). -/
theorem value_kind_word_refines {k : arena.checker_split.ValueKind} {o}
    (hrun : arena.checker_split.value_kind_word k = ok o) :
    ConRon.Refine.absString o = (absValueKind k).word := by
  sorry

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

@[lockstep] theorem nat_op_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.core.nat_op_names st) lst natOpNames :=
  LS.ofSim₀ fun _ h => nat_op_names_refines hrel hinv h

@[lockstep] theorem nat_div_mod_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.core.nat_div_mod_names st) lst
      natDivModNames :=
  LS.ofSim₀ fun _ h => nat_div_mod_names_refines hrel hinv h

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

@[lockstep] theorem pmemo_empty_spec :
    LSP arena.promote.PMemo.empty (fun o => PMemoRel o PMemo.empty) :=
  fun _ h => pmemo_empty_refines h

@[lockstep] theorem promote_new_ls {pers st lst rm lm rf lf} {fuel k : Std.U64}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hfe : IFEnvRelI rf lf)
    (hk : k.val ≤ rf.visible_below.val) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ IFEnvRelI r.2 v.2)
      (arena.promote.promote_new pers st rm fuel k rf) lst
      (promoteNew lm (absU fuel) (absU k) lf) :=
  LS.ofSimPM fun _ h => promote_new_refines hrel hinv hm hfe.rel hfe.inv
    (le_trans hk hfe.inv.visBound) h

@[lockstep] theorem promote_vg_ls {pers st lst rm lm} {fuel : Std.U64}
    {g : arena.checker_split.ValueGroup}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absValueGroup r.2)
      (arena.promote.promote_vg pers st rm fuel g) lst
      (promoteVG lm (absU fuel) (absValueGroup g)) :=
  LS.ofSimPM fun _ h => promote_vg_refines hrel hinv hm h

@[lockstep] theorem flush_caches_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.flush_caches st) lst flushCaches :=
  LSW.ofSimS₀ fun _ h => flush_caches_sim₀ hrel hinv h

@[lockstep] theorem enter_scratch_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.enter_scratch st) lst enterScratch :=
  LSW.ofSimS₀ fun _ h => enter_scratch_sim₀ hrel hinv h

@[lockstep] theorem drop_scratch_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSW pers (arena.core.drop_scratch st) lst dropScratch :=
  LSW.ofSimS₀ fun _ h => drop_scratch_sim₀ hrel hinv h

@[lockstep] theorem pin_quot_sound_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_quot_sound st) st lst
      pinQuotSound :=
  LSR.ofSimRE hrel hinv fun _ h => pin_quot_sound_refines hrel hinv h


@[lockstep] theorem check_value_group_ls {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {g : arena.checker_split.ValueGroup}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun _ b => b = ())
      (arena.checker_split.check_value_group pers vis st mode rf g) lst
      (checkValueGroup (ConRon.Refine.absMode mode) (lf.restrictTo (absU vis))
        (absValueGroup g)) :=
  LS.ofSim₀ fun _ h => check_value_group_refines hrel hinv hfe.rel hfe.inv h

@[lockstep_simp] theorem absPendingCheck_vis (p : arena.checker.PendingCheck) :
    (absPendingCheck p).vis = absU p.vis := rfl

@[lockstep_simp] theorem absPendingCheck_vg (p : arena.checker.PendingCheck) :
    (absPendingCheck p).vg = absValueGroup p.vg := rfl

end Lockstep

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.or_else_attempt_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms or_else_attempt_refines

/-- info: 'ConRon.Refine2.vec_dup_range_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vec_dup_range_spec

/-- info: 'ConRon.Refine2.vec_dup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vec_dup_eq

/-- info: 'ConRon.Refine2.vec_dup_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vec_dup_refines

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

/-- info: 'ConRon.Refine2.TierView.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TierView.transfer

/-- info: 'ConRon.Refine2.freeze_tier_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms freeze_tier_view

/-- info: 'ConRon.Refine2.thaw_read_tier_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms thaw_read_tier_view

/-- info: 'ConRon.Refine2.freeze_tier_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms freeze_tier_ok

/-- info: 'ConRon.Refine2.freeze_tier_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms freeze_tier_err

/-- info: 'ConRon.Refine2.attempt_snapshot_refines₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms attempt_snapshot_refines₀

/-- info: 'ConRon.Refine2.attempt_restore_refines₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms attempt_restore_refines₀

/-- info: 'ConRon.Refine2.is_rec_info_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_rec_info_refines

/-- info: 'ConRon.Refine2.memo_b_get_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_b_get_refines

/-- info: 'ConRon.Refine2.is_thm_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_thm_refines

/-- info: 'ConRon.Refine2.consts_resolve_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consts_resolve_aux

/-- info: 'ConRon.Refine2.nidx_is_proj_fn_shape_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nidx_is_proj_fn_shape_refines

/-- info: 'ConRon.Refine2.recs_form_suffix_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms recs_form_suffix_refines

/-- info: 'ConRon.Refine2.name_nodup_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms name_nodup_refines

/-- info: 'ConRon.Refine2.lvl_eq_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lvl_eq_refines

end ConRon.Refine2
