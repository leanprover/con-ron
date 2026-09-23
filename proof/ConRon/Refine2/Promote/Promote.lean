/-
# `ConRon.Refine2.Promote.Promote` — Theorem 2 for `arena::promote`

**Task #97-P5-Checker**, deliverable 1's second half (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/promote.rs` against
`proof/ConRon/Arena/Promote.lean`: DESIGN §8.3's scratch → persistent
memoised structural copy, at all four handle kinds, lifted to `arena::env`'s
declaration layer, plus `promote_new` — the entry the fold calls, which
promotes a step's newly installed constants in place.

## The statement shape

`Refine2/Checker/Shape.lean`'s `SimPM` / `SimPMF`: task #97-P5-0's finding 4
one tier down.  The memo is an argument-and-result pair on both sides and a
`ron::HashMap2` abstracts only relationally, so the twin's post-memo is
existentially quantified beside its post-state and `PMemoRel` relates it.

## Five Rust-only splits, and how each is stated

`promote_{n,l,e}_node`, `promote_{l,e}_two` and the `_from` cursor
companions have no twin of their own — they are task #97-P6-2's extraction
rule 5 ("a `view`'s loans must be dead at the memo's join") and DESIGN §3.4's
standing `List`-as-cursor deviation.  The `_node` three are stated against a
LOCAL TRANSCRIPTION of the twin's own arms (`promote{N,L,E}NodeSpec`) plus an
`_unfold` equation back to the twin; the `_two` pairs against `promote{L,E}Two`
(the twin's two binds, named, so the port's one call has one twin action to
zip with); the cursors against `pmapFrom` (`Promote/Prims.lean`), the cursor
recursion over the twin's `List`; `promote_proj_table_rest` against
`promoteProjTableRest`.

## Lockstep (task #97-T2-LOCKSTEP lane Promote)

Every walk is `AStateRel₀`/`AStateInv` in, `LS` out, and every case body is
one `lockstep` call over `Promote/Prims.lean`'s pairs (the views with the
Rust view's key predicate, the persistent interns, the memo primitives).  The
promote window of task #97-P5-Fresh (`AStateRelW`, `StoreWF'`) is gone: the
twin's store invariant is Theorem 1's.  The one piece that is not a zip is
`index_promoted` (finding B below), by hand.

## Findings about `promote_new`

In the section note there; finding D (`IFEnvKeys`) is task #97-T2-LOCKSTEP
lane Promote's.
-/
import ConRon.Refine2.Promote.Intern

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv RelOn)

/-! ## The memo itself -/

/-- **`arena::promote::PMemo::empty` is the twin's `PMemo.empty`** — four
fresh `HashMap2`s against four empty `Std.HashMap`s, `Refine2/Promote/Intern.lean`'s
`memo_empty_refines` four times over.  The fold's bracket starts from it, so
it is what `check_decl_step` and `annot_step` consume. -/
theorem pmemo_empty_refines {o} (hrun : arena.promote.PMemo.empty = ok o) :
    PMemoRel o PMemo.empty := by
  rw [arena.promote.PMemo.empty] at hrun
  obtain ⟨me, hme, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨mn, hmn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ml, hml, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨mls, hmls, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hie, -, hne⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) hme
  obtain ⟨hin, -, hnn⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hmn
  obtain ⟨hil, -, hnl⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.LIdx.Insts.Con_ron_coreRonHashmapHashable) hml
  obtain ⟨hils, -, hnls⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapHashable) hmls
  have ho : o = { e_m := me, n_m := mn, l_m := ml, ls_m := mls } :=
    (Result.ok_injective hrun).symm
  subst ho
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hne, ConRon.Refine.HashMap2.RelOn_empty hnn,
    ConRon.Refine.HashMap2.RelOn_empty hnl, ConRon.Refine.HashMap2.RelOn_empty hnls,
    hie, hin, hil, hils⟩

/-! ## The memo's two primitives, per handle kind

Eight one-line functions extraction rule 5 asked for; eight two-line lemmas. -/

theorem pmemo_get_n_refines {rm lm} {h : arena.handle.NIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_get_n rm h = ok o) :
    o.map absNIdx = lm.nM[absNIdx h]? := by
  rw [arena.promote.pmemo_get_n] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hm.nInv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hm.nM h trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.NIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_nidx _ _ hx]

theorem pmemo_set_n_refines {rm lm} {h r : arena.handle.NIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_set_n rm h r = ok o) :
    PMemoRel o { lm with nM := lm.nM.insert (absNIdx h) (absNIdx r) } := by
  rw [arena.promote.pmemo_set_n] at hrun
  obtain ⟨a, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hmm⟩ := p
  rw [dupId_nidx _ _ ha, dupId_nidx _ _ hb] at hp
  have hst : o = { rm with n_m := hmm } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step nidx_eq2 absNIdx_inj hm.nInv hm.nM hp
  exact { hm with nM := h1, nInv := h2 }

theorem pmemo_get_l_refines {rm lm} {h : arena.handle.LIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_get_l rm h = ok o) :
    o.map absLIdx = lm.lM[absLIdx h]? := by
  rw [arena.promote.pmemo_get_l] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidx_eq2 hm.lInv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hm.lM h trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.LIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_lidx _ _ hx]

theorem pmemo_set_l_refines {rm lm} {h r : arena.handle.LIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_set_l rm h r = ok o) :
    PMemoRel o { lm with lM := lm.lM.insert (absLIdx h) (absLIdx r) } := by
  rw [arena.promote.pmemo_set_l] at hrun
  obtain ⟨a, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hmm⟩ := p
  rw [dupId_lidx _ _ ha, dupId_lidx _ _ hb] at hp
  have hst : o = { rm with l_m := hmm } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step lidx_eq2 absLIdx_inj hm.lInv hm.lM hp
  exact { hm with lM := h1, lInv := h2 }

theorem pmemo_get_ls_refines {rm lm} {h : arena.handle.LsIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_get_ls rm h = ok o) :
    o.map absLsIdx = lm.lsM[absLsIdx h]? := by
  rw [arena.promote.pmemo_get_ls] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lsidx_eq2 hm.lsInv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hm.lsM h trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.LsIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_lsidx _ _ hx]

theorem pmemo_set_ls_refines {rm lm} {h r : arena.handle.LsIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_set_ls rm h r = ok o) :
    PMemoRel o { lm with lsM := lm.lsM.insert (absLsIdx h) (absLsIdx r) } := by
  rw [arena.promote.pmemo_set_ls] at hrun
  obtain ⟨a, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hmm⟩ := p
  rw [dupId_lsidx _ _ ha, dupId_lsidx _ _ hb] at hp
  have hst : o = { rm with ls_m := hmm } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step lsidx_eq2 absLsIdx_inj hm.lsInv hm.lsM hp
  exact { hm with lsM := h1, lsInv := h2 }

theorem pmemo_get_e_refines {rm lm} {h : arena.handle.EIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_get_e rm h = ok o) :
    o.map absEIdx = lm.eM[absEIdx h]? := by
  rw [arena.promote.pmemo_get_e] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hm.eInv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hm.eM h trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option arena.handle.EIdx) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some r =>
    rw [hrc] at hrun
    obtain ⟨x, hx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : some x = o := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hx]

theorem pmemo_set_e_refines {rm lm} {h r : arena.handle.EIdx} {o}
    (hm : PMemoRel rm lm) (hrun : arena.promote.pmemo_set_e rm h r = ok o) :
    PMemoRel o { lm with eM := lm.eM.insert (absEIdx h) (absEIdx r) } := by
  rw [arena.promote.pmemo_set_e] at hrun
  obtain ⟨a, ha, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hmm⟩ := p
  rw [dupId_eidx _ _ ha, dupId_eidx _ _ hb] at hp
  have hst : o = { rm with e_m := hmm } := (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := memo_insert_step eidx_eq2 absEIdx_inj hm.eInv hm.eM hp
  exact { hm with eM := h1, eInv := h2 }

/-! ## The three node transcriptions

`promote_{n,l,e}_node` are the twin's own arms past the probe, split off so
that the `view`'s loans are dead at the memo's join.  Each is transcribed
here at the twin's `…NodeView` and tied to the twin by an `_unfold`
equation — the shape `Refine2/ExprOps/Read.lean` wrote for `wscopedBGo`. -/

/-- `promoteN`'s three arms past the probe. -/
def promoteNNodeSpec (m : PMemo) (fuel : Nat) : NNodeView → AM (PMemo × NIdx)
  | .anonymous => do pure (m, ← internPersistentN .anonymous)
  | .str p s => do
    let (m, p) ← promoteN m fuel p
    pure (m, ← internPersistentN (.str p s))
  | .num p n => do
    let (m, p) ← promoteN m fuel p
    pure (m, ← internPersistentN (.num p n))

/-- `promote_l_two`'s twin: the two-child level arms' pair of promotions, in
the twin's order — a factoring of `promoteL`'s `max`/`imax` arms, named so
that the port's one call has one twin action to zip with. -/
def promoteLTwo (m : PMemo) (fuel : Nat) (u v : LIdx) : AM (PMemo × (LIdx × LIdx)) := do
  let (m, a) ← promoteL m fuel u
  let (m, b) ← promoteL m fuel v
  pure (m, (a, b))

/-- `promote_e_two`'s twin, as `promoteLTwo`. -/
def promoteETwo (m : PMemo) (fuel : Nat) (x y : EIdx) : AM (PMemo × (EIdx × EIdx)) := do
  let (m, a) ← promoteE m fuel x
  let (m, b) ← promoteE m fuel y
  pure (m, (a, b))

/-- `promoteL`'s five arms past the probe. -/
def promoteLNodeSpec (m : PMemo) (fuel : Nat) : LNodeView → AM (PMemo × LIdx)
  | .zero => do pure (m, ← internPersistentL .zero)
  | .succ u => do
    let (m, u) ← promoteL m fuel u
    pure (m, ← internPersistentL (.succ u))
  | .max u v => do
    let (m, (u, v)) ← promoteLTwo m fuel u v
    pure (m, ← internPersistentL (.max u v))
  | .imax u v => do
    let (m, (u, v)) ← promoteLTwo m fuel u v
    pure (m, ← internPersistentL (.imax u v))
  | .param n => do
    let (m, n) ← promoteN m fuel n
    pure (m, ← internPersistentL (.param n))

/-- `promoteE`'s ten arms past the probe. -/
def promoteENodeSpec (m : PMemo) (fuel : Nat) : ENodeView → AM (PMemo × EIdx)
  | .bvar i => do pure (m, ← internPersistentE (.bvar i))
  | .fvar idx ty => do
    let (m, ty) ← promoteE m fuel ty
    pure (m, ← internPersistentE (.fvar idx ty))
  | .sort u => do
    let (m, u) ← promoteL m fuel u
    pure (m, ← internPersistentE (.sort u))
  | .const n us => do
    let (m, n) ← promoteN m fuel n
    let (m, us) ← promoteLs m fuel us
    pure (m, ← internPersistentE (.const n us))
  | .app f a => do
    let (m, (f, a)) ← promoteETwo m fuel f a
    pure (m, ← internPersistentE (.app f a))
  | .lam ty body bm => do
    let (m, (ty, body)) ← promoteETwo m fuel ty body
    pure (m, ← internPersistentE (.lam ty body bm))
  | .forallE ty body bm => do
    let (m, (ty, body)) ← promoteETwo m fuel ty body
    pure (m, ← internPersistentE (.forallE ty body bm))
  | .letE ty val body => do
    let (m, (ty, val)) ← promoteETwo m fuel ty val
    let (m, body) ← promoteE m fuel body
    pure (m, ← internPersistentE (.letE ty val body))
  | .lit l => do pure (m, ← internPersistentE (.lit l))
  | .proj n i e => do
    let (m, n) ← promoteN m fuel n
    let (m, e) ← promoteE m fuel e
    pure (m, ← internPersistentE (.proj n i e))

/-- `promoteN` in terms of its transcription. -/
theorem promoteN_unfold (m : PMemo) (fuel : Nat) (h : NIdx) :
    promoteN m (fuel + 1) h = (do
      if h.isPersistent then pure (m, h)
      else
        match m.nM[h]? with
        | some r => pure (m, r)
        | none => do
          let (m, r) ← promoteNNodeSpec m fuel (← viewN h)
          pure ({ m with nM := m.nM.insert h r }, r)) := by
  rw [promoteN]
  split
  · rfl
  · cases hm : m.nM[h]? with
    | some r => rfl
    | none =>
      refine am_bind_congr _ ?_
      intro v
      cases v <;> twin_reduce [promoteNNodeSpec]

/-- `promoteL` in terms of its transcription. -/
theorem promoteL_unfold (m : PMemo) (fuel : Nat) (h : LIdx) :
    promoteL m (fuel + 1) h = (do
      if h.isPersistent then pure (m, h)
      else
        match m.lM[h]? with
        | some r => pure (m, r)
        | none => do
          let (m, r) ← promoteLNodeSpec m fuel (← viewL h)
          pure ({ m with lM := m.lM.insert h r }, r)) := by
  rw [promoteL]
  split
  · rfl
  · cases hm : m.lM[h]? with
    | some r => rfl
    | none =>
      refine am_bind_congr _ ?_
      intro v
      cases v <;> twin_reduce [promoteLNodeSpec, promoteLTwo]

/-- `promoteE` in terms of its transcription. -/
theorem promoteE_unfold (m : PMemo) (fuel : Nat) (h : EIdx) :
    promoteE m (fuel + 1) h = (do
      if h.isPersistent then pure (m, h)
      else
        match m.eM[h]? with
        | some r => pure (m, r)
        | none => do
          let (m, r) ← promoteENodeSpec m fuel (← view h)
          pure ({ m with eM := m.eM.insert h r }, r)) := by
  rw [promoteE]
  split
  · rfl
  · cases hm : m.eM[h]? with
    | some r => rfl
    | none =>
      refine am_bind_congr _ ?_
      intro v
      cases v <;> twin_reduce [promoteENodeSpec, promoteETwo]

/-! ## The promotion memo's primitives in the judgement shape -/

namespace Lockstep

@[lockstep] theorem pmemo_get_n_spec {rm lm} (hm : PMemoRel rm lm) (h : arena.handle.NIdx) :
    LSP (arena.promote.pmemo_get_n rm h)
      (fun o => TwinEq (lm.nM[absNIdx h]?) (o.map absNIdx)) :=
  fun _ ho => (pmemo_get_n_refines hm ho).symm

@[lockstep] theorem pmemo_set_n_spec {rm lm} (hm : PMemoRel rm lm) (h r : arena.handle.NIdx) :
    LSP (arena.promote.pmemo_set_n rm h r)
      (fun o => PMemoRel o { lm with nM := lm.nM.insert (absNIdx h) (absNIdx r) }) :=
  fun _ ho => pmemo_set_n_refines hm ho

@[lockstep] theorem pmemo_get_l_spec {rm lm} (hm : PMemoRel rm lm) (h : arena.handle.LIdx) :
    LSP (arena.promote.pmemo_get_l rm h)
      (fun o => TwinEq (lm.lM[absLIdx h]?) (o.map absLIdx)) :=
  fun _ ho => (pmemo_get_l_refines hm ho).symm

@[lockstep] theorem pmemo_set_l_spec {rm lm} (hm : PMemoRel rm lm) (h r : arena.handle.LIdx) :
    LSP (arena.promote.pmemo_set_l rm h r)
      (fun o => PMemoRel o { lm with lM := lm.lM.insert (absLIdx h) (absLIdx r) }) :=
  fun _ ho => pmemo_set_l_refines hm ho

@[lockstep] theorem pmemo_get_ls_spec {rm lm} (hm : PMemoRel rm lm) (h : arena.handle.LsIdx) :
    LSP (arena.promote.pmemo_get_ls rm h)
      (fun o => TwinEq (lm.lsM[absLsIdx h]?) (o.map absLsIdx)) :=
  fun _ ho => (pmemo_get_ls_refines hm ho).symm

@[lockstep] theorem pmemo_set_ls_spec {rm lm} (hm : PMemoRel rm lm) (h r : arena.handle.LsIdx) :
    LSP (arena.promote.pmemo_set_ls rm h r)
      (fun o => PMemoRel o { lm with lsM := lm.lsM.insert (absLsIdx h) (absLsIdx r) }) :=
  fun _ ho => pmemo_set_ls_refines hm ho

@[lockstep] theorem pmemo_get_e_spec {rm lm} (hm : PMemoRel rm lm) (h : arena.handle.EIdx) :
    LSP (arena.promote.pmemo_get_e rm h)
      (fun o => TwinEq (lm.eM[absEIdx h]?) (o.map absEIdx)) :=
  fun _ ho => (pmemo_get_e_refines hm ho).symm

@[lockstep] theorem pmemo_set_e_spec {rm lm} (hm : PMemoRel rm lm) (h r : arena.handle.EIdx) :
    LSP (arena.promote.pmemo_set_e rm h r)
      (fun o => PMemoRel o { lm with eM := lm.eM.insert (absEIdx h) (absEIdx r) }) :=
  fun _ ho => pmemo_set_e_refines hm ho

end Lockstep

/-! ## The walks, in the judgement shape

Each walk is one fuel induction, and each `_node` lemma is derived INSIDE the
successor step from that step's own induction hypothesis (the mutual block's
second half needs no induction of its own); a `_two` pair likewise.  Every
case body is one `lockstep` call. -/

namespace Lockstep

private theorem promote_n_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (h : arena.handle.NIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absNIdx r.2)
        (arena.promote.promote_n pers st rm fuel h) lst (promoteN lm n (absNIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel h hn hrel hinv hm
    rw [arena.promote.promote_n, promoteN]
    lockstep
  | succ k ih =>
    have hnode : ∀ {pers st lst rm lm} (fu : Std.U64) (v : arena.store.NNodeView),
        fu.val = k → NNodeViewWF v → AStateRel₀ pers st lst → AStateInv pers st →
        PMemoRel rm lm →
        LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absNIdx r.2)
          (arena.promote.promote_n_node pers st rm fu v) lst
          (promoteNNodeSpec lm k (absNNodeView v)) := by
      intro pers st lst rm lm fu v hfu hvwf hrel hinv hm
      cases v <;> rw [arena.promote.promote_n_node] <;>
        simp only [absNNodeView, promoteNNodeSpec] <;> lockstep
    intro pers st lst rm lm fuel h hn hrel hinv hm
    rw [arena.promote.promote_n, promoteN_unfold]
    lockstep

/-- **`promote_n` ⊑ `promoteN`**, in the judgement shape. -/
@[lockstep] theorem promote_n_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.NIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absNIdx r.2)
      (arena.promote.promote_n pers st rm fuel h) lst (promoteN lm (absU fuel) (absNIdx h)) :=
  promote_n_aux _ fuel h rfl hrel hinv hm

/-- `promote_n_node` ⊑ `promoteNNodeSpec`, from the walk at the same fuel. -/
theorem promote_n_node_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absNIdx r.2)
      (arena.promote.promote_n_node pers st rm fuel v) lst
      (promoteNNodeSpec lm (absU fuel) (absNNodeView v)) := by
  cases v <;> rw [arena.promote.promote_n_node] <;>
    simp only [absNNodeView, promoteNNodeSpec] <;> lockstep

private theorem promote_l_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (h : arena.handle.LIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLIdx r.2)
        (arena.promote.promote_l pers st rm fuel h) lst (promoteL lm n (absLIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel h hn hrel hinv hm
    rw [arena.promote.promote_l, promoteL]
    lockstep
  | succ k ih =>
    have htwo : ∀ {pers st lst rm lm} (fu : Std.U64) (u v : arena.handle.LIdx),
        fu.val = k → AStateRel₀ pers st lst → AStateInv pers st → PMemoRel rm lm →
        LS pers (fun r w => PMemoRel r.1 w.1 ∧ w.2 = (absLIdx r.2.1, absLIdx r.2.2))
          (arena.promote.promote_l_two pers st rm fu u v) lst
          (promoteLTwo lm k (absLIdx u) (absLIdx v)) := by
      intro pers st lst rm lm fu u v hfu hrel hinv hm
      rw [arena.promote.promote_l_two, promoteLTwo]
      lockstep
    have hnode : ∀ {pers st lst rm lm} (fu : Std.U64) (v : arena.store.LNodeView),
        fu.val = k → AStateRel₀ pers st lst → AStateInv pers st → PMemoRel rm lm →
        LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLIdx r.2)
          (arena.promote.promote_l_node pers st rm fu v) lst
          (promoteLNodeSpec lm k (absLNodeView v)) := by
      intro pers st lst rm lm fu v hfu hrel hinv hm
      cases v <;> rw [arena.promote.promote_l_node] <;>
        simp only [absLNodeView, promoteLNodeSpec] <;> lockstep
    intro pers st lst rm lm fuel h hn hrel hinv hm
    rw [arena.promote.promote_l, promoteL_unfold]
    lockstep

/-- **`promote_l` ⊑ `promoteL`**, in the judgement shape. -/
@[lockstep] theorem promote_l_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.LIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLIdx r.2)
      (arena.promote.promote_l pers st rm fuel h) lst (promoteL lm (absU fuel) (absLIdx h)) :=
  promote_l_aux _ fuel h rfl hrel hinv hm

/-- `promote_l_two` ⊑ `promoteLTwo`. -/
@[lockstep] theorem promote_l_two_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (u v : arena.handle.LIdx) :
    LS pers (fun r w => PMemoRel r.1 w.1 ∧ w.2 = (absLIdx r.2.1, absLIdx r.2.2))
      (arena.promote.promote_l_two pers st rm fuel u v) lst
      (promoteLTwo lm (absU fuel) (absLIdx u) (absLIdx v)) := by
  rw [arena.promote.promote_l_two, promoteLTwo]
  lockstep

/-- `promote_l_node` ⊑ `promoteLNodeSpec`. -/
theorem promote_l_node_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (v : arena.store.LNodeView) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLIdx r.2)
      (arena.promote.promote_l_node pers st rm fuel v) lst
      (promoteLNodeSpec lm (absU fuel) (absLNodeView v)) := by
  cases v <;> rw [arena.promote.promote_l_node] <;>
    simp only [absLNodeView, promoteLNodeSpec] <;> lockstep

private theorem promote_l_list_from_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.handle.LIdx)
      (i : Std.Usize) (out : alloc.vec.Vec arena.handle.LIdx),
      us.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLIdxL r.2)
        (arena.promote.promote_l_list_from pers st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteL m (absU fuel) u) lm (absLIdxL out)
          ((us.val.drop i.val).map absLIdx)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_l_list_from, vecFrom_nil us absLIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun _ => LS.pure ⟨hm, rfl⟩ hrel hinv) (fun hc => absurd hc (by scalar_tac))
  | succ k ih =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_l_list_from, vecFrom_cons us absLIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_)
    lockstep

/-- `promote_l_list_from` ⊑ `pmapFrom promoteL` — the cursor, in the judgement
shape. -/
@[lockstep] theorem promote_l_list_from_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.LIdx) (i : Std.Usize)
    (out : alloc.vec.Vec arena.handle.LIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLIdxL r.2)
      (arena.promote.promote_l_list_from pers st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteL m (absU fuel) u) lm (absLIdxL out)
        ((us.val.drop i.val).map absLIdx)) :=
  promote_l_list_from_aux _ fuel us i out rfl hrel hinv hm

theorem promoteLList_pmapFrom (m : PMemo) (fuel : Nat) (l : List LIdx) (acc : List LIdx) :
    pmapFrom (fun m u => promoteL m fuel u) m acc l =
      (do let (m, ys) ← promoteLList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteLList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_l_list` ⊑ `promoteLList`. -/
@[lockstep] theorem promote_l_list_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.LIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLIdxL r.2)
      (arena.promote.promote_l_list pers st rm fuel us) lst
      (promoteLList lm (absU fuel) (absLIdxL us)) := by
  have h := promote_l_list_from_ls hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteLList_pmapFrom] at h
  simpa [arena.promote.promote_l_list, absLIdxL, alloc.vec.Vec.new] using h

/-- **`promote_ls` ⊑ `promoteLs`** — no fuel clause on either side. -/
@[lockstep] theorem promote_ls_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.LsIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absLsIdx r.2)
      (arena.promote.promote_ls pers st rm fuel h) lst
      (promoteLs lm (absU fuel) (absLsIdx h)) := by
  rw [arena.promote.promote_ls, promoteLs]
  lockstep

private theorem promote_e_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absEIdx r.2)
        (arena.promote.promote_e pers st rm fuel h) lst (promoteE lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel h hn hrel hinv hm
    rw [arena.promote.promote_e, promoteE]
    lockstep
  | succ k ih =>
    have htwo : ∀ {pers st lst rm lm} (fu : Std.U64) (x y : arena.handle.EIdx),
        fu.val = k → AStateRel₀ pers st lst → AStateInv pers st → PMemoRel rm lm →
        LS pers (fun r w => PMemoRel r.1 w.1 ∧ w.2 = (absEIdx r.2.1, absEIdx r.2.2))
          (arena.promote.promote_e_two pers st rm fu x y) lst
          (promoteETwo lm k (absEIdx x) (absEIdx y)) := by
      intro pers st lst rm lm fu x y hfu hrel hinv hm
      rw [arena.promote.promote_e_two, promoteETwo]
      lockstep
    have hnode : ∀ {pers st lst rm lm} (fu : Std.U64) (v : arena.store.ENodeView),
        fu.val = k → ENodeViewWF v → AStateRel₀ pers st lst → AStateInv pers st →
        PMemoRel rm lm →
        LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absEIdx r.2)
          (arena.promote.promote_e_node pers st rm fu v) lst
          (promoteENodeSpec lm k (absENodeView v)) := by
      intro pers st lst rm lm fu v hfu hvwf hrel hinv hm
      cases v <;> rw [arena.promote.promote_e_node] <;>
        simp only [absENodeView, promoteENodeSpec] <;> lockstep
    intro pers st lst rm lm fuel h hn hrel hinv hm
    have hV := @view_wf_ls
    rw [arena.promote.promote_e, promoteE_unfold]
    lockstep

/-- **`promote_e` ⊑ `promoteE`**, in the judgement shape. -/
@[lockstep] theorem promote_e_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absEIdx r.2)
      (arena.promote.promote_e pers st rm fuel h) lst (promoteE lm (absU fuel) (absEIdx h)) :=
  promote_e_aux _ fuel h rfl hrel hinv hm

/-- `promote_e_two` ⊑ `promoteETwo`. -/
@[lockstep] theorem promote_e_two_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (x y : arena.handle.EIdx) :
    LS pers (fun r w => PMemoRel r.1 w.1 ∧ w.2 = (absEIdx r.2.1, absEIdx r.2.2))
      (arena.promote.promote_e_two pers st rm fuel x y) lst
      (promoteETwo lm (absU fuel) (absEIdx x) (absEIdx y)) := by
  rw [arena.promote.promote_e_two, promoteETwo]
  lockstep

/-- `promote_e_node` ⊑ `promoteENodeSpec`. -/
theorem promote_e_node_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (v : arena.store.ENodeView) (hvwf : ENodeViewWF v) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absEIdx r.2)
      (arena.promote.promote_e_node pers st rm fuel v) lst
      (promoteENodeSpec lm (absU fuel) (absENodeView v)) := by
  cases v <;> rw [arena.promote.promote_e_node] <;>
    simp only [absENodeView, promoteENodeSpec] <;> lockstep

private theorem promote_n_list_from_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.handle.NIdx)
      (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx),
      us.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absNIdxL r.2)
        (arena.promote.promote_n_list_from pers st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteN m (absU fuel) u) lm (absNIdxL out)
          ((us.val.drop i.val).map absNIdx)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_n_list_from, vecFrom_nil us absNIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun _ => LS.pure ⟨hm, rfl⟩ hrel hinv) (fun hc => absurd hc (by scalar_tac))
  | succ k ih =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_n_list_from, vecFrom_cons us absNIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_)
    lockstep

/-- `promote_n_list_from` ⊑ `pmapFrom promoteN` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_n_list_from_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absNIdxL r.2)
      (arena.promote.promote_n_list_from pers st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteN m (absU fuel) u) lm (absNIdxL out)
        ((us.val.drop i.val).map absNIdx)) :=
  promote_n_list_from_aux _ fuel us i out rfl hrel hinv hm

theorem promoteNList_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteN m fuel u) m acc l =
      (do let (m, ys) ← promoteNList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteNList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_n_list` ⊑ `promoteNList`. -/
@[lockstep] theorem promote_n_list_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absNIdxL r.2)
      (arena.promote.promote_n_list pers st rm fuel us) lst
      (promoteNList lm (absU fuel) (absNIdxL us)) := by
  have h := promote_n_list_from_ls hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteNList_pmapFrom] at h
  simpa [arena.promote.promote_n_list, absNIdxL, alloc.vec.Vec.new] using h

private theorem promote_e_list_from_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.handle.EIdx)
      (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx),
      us.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absEIdxL r.2)
        (arena.promote.promote_e_list_from pers st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteE m (absU fuel) u) lm (absEIdxL out)
          ((us.val.drop i.val).map absEIdx)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_e_list_from, vecFrom_nil us absEIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun _ => LS.pure ⟨hm, rfl⟩ hrel hinv) (fun hc => absurd hc (by scalar_tac))
  | succ k ih =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_e_list_from, vecFrom_cons us absEIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_)
    lockstep

/-- `promote_e_list_from` ⊑ `pmapFrom promoteE` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_e_list_from_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absEIdxL r.2)
      (arena.promote.promote_e_list_from pers st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteE m (absU fuel) u) lm (absEIdxL out)
        ((us.val.drop i.val).map absEIdx)) :=
  promote_e_list_from_aux _ fuel us i out rfl hrel hinv hm

theorem promoteEList_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteE m fuel u) m acc l =
      (do let (m, ys) ← promoteEList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteEList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_e_list` ⊑ `promoteEList`. -/
@[lockstep] theorem promote_e_list_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absEIdxL r.2)
      (arena.promote.promote_e_list pers st rm fuel us) lst
      (promoteEList lm (absU fuel) (absEIdxL us)) := by
  have h := promote_e_list_from_ls hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteEList_pmapFrom] at h
  simpa [arena.promote.promote_e_list, absEIdxL, alloc.vec.Vec.new] using h


/-! ### The declaration layer -/

section decl
attribute [local lockstep_simp] absIConstantVal absIRecRuleFire absIRecRule absIIndCaps
  absIProjTable absIConstantInfo absIDeclaration absIRecRuleL absICIL

/-- `promote_cv` ⊑ `promoteCV`. -/
@[lockstep] theorem promote_cv_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (cv : arena.env.IConstantVal) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIConstantVal r.2)
      (arena.promote.promote_cv pers st rm fuel cv) lst
      (promoteCV lm (absU fuel) (absIConstantVal cv)) := by
  rw [arena.promote.promote_cv, promoteCV]
  lockstep

/-- `promote_fire` ⊑ `promoteFire`. -/
@[lockstep] theorem promote_fire_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (f : arena.env.IRecRuleFire) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIRecRuleFire r.2)
      (arena.promote.promote_fire pers st rm fuel f) lst
      (promoteFire lm (absU fuel) (absIRecRuleFire f)) := by
  cases f <;> rw [arena.promote.promote_fire] <;> simp only [absIRecRuleFire, promoteFire] <;>
    lockstep

/-- `promote_rule` ⊑ `promoteRule`. -/
@[lockstep] theorem promote_rule_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (rl : arena.env.IRecRule) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIRecRule r.2)
      (arena.promote.promote_rule pers st rm fuel rl) lst
      (promoteRule lm (absU fuel) (absIRecRule rl)) := by
  rw [arena.promote.promote_rule, promoteRule]
  lockstep

/-- `promote_caps` ⊑ `promoteCaps`. -/
@[lockstep] theorem promote_caps_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (c : arena.env.IIndCaps) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIIndCaps r.2)
      (arena.promote.promote_caps pers st rm fuel c) lst
      (promoteCaps lm (absU fuel) (absIIndCaps c)) := by
  rw [arena.promote.promote_caps, promoteCaps]
  lockstep

end decl

private theorem promote_rules_from_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.env.IRecRule)
      (i : Std.Usize) (out : alloc.vec.Vec arena.env.IRecRule),
      us.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIRecRuleL r.2)
        (arena.promote.promote_rules_from pers st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteRule m (absU fuel) u) lm (absIRecRuleL out)
          ((us.val.drop i.val).map absIRecRule)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_rules_from, vecFrom_nil us absIRecRule i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun _ => LS.pure ⟨hm, rfl⟩ hrel hinv) (fun hc => absurd hc (by scalar_tac))
  | succ k ih =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_rules_from, vecFrom_cons us absIRecRule i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_)
    lockstep

/-- `promote_rules_from` ⊑ `pmapFrom promoteRule` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_rules_from_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IRecRule) (i : Std.Usize) (out : alloc.vec.Vec arena.env.IRecRule) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIRecRuleL r.2)
      (arena.promote.promote_rules_from pers st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteRule m (absU fuel) u) lm (absIRecRuleL out)
        ((us.val.drop i.val).map absIRecRule)) :=
  promote_rules_from_aux _ fuel us i out rfl hrel hinv hm

theorem promoteRules_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteRule m fuel u) m acc l =
      (do let (m, ys) ← promoteRules m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteRules m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_rules` ⊑ `promoteRules`. -/
@[lockstep] theorem promote_rules_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IRecRule) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIRecRuleL r.2)
      (arena.promote.promote_rules pers st rm fuel us) lst
      (promoteRules lm (absU fuel) (absIRecRuleL us)) := by
  have h := promote_rules_from_ls hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteRules_pmapFrom] at h
  simpa [arena.promote.promote_rules, absIRecRuleL, alloc.vec.Vec.new] using h


/-- The tail of `promoteProjTable` past its three leading promotions: the twin
of the port's `promote_proj_table_rest` split (extraction rule 5). -/
def promoteProjTableRest (m : PMemo) (fuel : Nat) (t : IProjTable) (sn tn : NIdx)
    (lps : List NIdx) : AM (PMemo × IProjTable) := do
  let (m, c) ← promoteN m fuel t.ctor
  let (m, ss) ← promoteL m fuel t.structSort
  let (m, bs) ← promoteEList m fuel t.bodies.toList
  let (m, gs) ← promoteLList m fuel t.guards
  pure (m, ⟨sn, tn, lps, t.numParams, c, t.numFields, ss, bs.toArray, gs, t.off⟩)

theorem promoteProjTable_rest (m : PMemo) (fuel : Nat) (t : IProjTable) :
    promoteProjTable m fuel t = (do
      let (m, sn) ← promoteN m fuel t.structName
      let (m, tn) ← promoteN m fuel t.tableName
      let (m, lps) ← promoteNList m fuel t.levelParams
      promoteProjTableRest m fuel t sn tn lps) := rfl

section decl2
attribute [local lockstep_simp] absIConstantVal absIRecRuleFire absIRecRule absIIndCaps
  absIProjTable absIConstantInfo absIDeclaration absIRecRuleL absICIL List.toList_toArray

/-- `promote_proj_table_rest` ⊑ `promoteProjTableRest`. -/
@[lockstep] theorem promote_proj_table_rest_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (t : arena.env.IProjTable) (sn tn : arena.handle.NIdx)
    (lps : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIProjTable r.2)
      (arena.promote.promote_proj_table_rest pers st rm fuel t sn tn lps) lst
      (promoteProjTableRest lm (absU fuel) (absIProjTable t) (absNIdx sn) (absNIdx tn)
        (absNIdxL lps)) := by
  rw [arena.promote.promote_proj_table_rest, promoteProjTableRest]
  lockstep

/-- `promote_proj_table` ⊑ `promoteProjTable`. -/
@[lockstep] theorem promote_proj_table_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (t : arena.env.IProjTable) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIProjTable r.2)
      (arena.promote.promote_proj_table pers st rm fuel t) lst
      (promoteProjTable lm (absU fuel) (absIProjTable t)) := by
  rw [arena.promote.promote_proj_table, promoteProjTable_rest]
  lockstep

/-- `promote_ci` ⊑ `promoteCI` — the seven constructors. -/
@[lockstep] theorem promote_ci_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (ci : arena.env.IConstantInfo) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIConstantInfo r.2)
      (arena.promote.promote_ci pers st rm fuel ci) lst
      (promoteCI lm (absU fuel) (absIConstantInfo ci)) := by
  cases ci <;> rw [arena.promote.promote_ci] <;> simp only [absIConstantInfo, promoteCI] <;>
    lockstep

end decl2

private theorem promote_ci_list_from_aux (n : Nat) :
    ∀ {pers st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.env.IConstantInfo)
      (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantInfo),
      us.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absICIL r.2)
        (arena.promote.promote_ci_list_from pers st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteCI m (absU fuel) u) lm (absICIL out)
          ((us.val.drop i.val).map absIConstantInfo)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_ci_list_from, vecFrom_nil us absIConstantInfo i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun _ => LS.pure ⟨hm, rfl⟩ hrel hinv) (fun hc => absurd hc (by scalar_tac))
  | succ k ih =>
    intro pers st lst rm lm fuel us i out hn hrel hinv hm
    rw [arena.promote.promote_ci_list_from, vecFrom_cons us absIConstantInfo i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_)
    lockstep

/-- `promote_ci_list_from` ⊑ `pmapFrom promoteCI` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_ci_list_from_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IConstantInfo) (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absICIL r.2)
      (arena.promote.promote_ci_list_from pers st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteCI m (absU fuel) u) lm (absICIL out)
        ((us.val.drop i.val).map absIConstantInfo)) :=
  promote_ci_list_from_aux _ fuel us i out rfl hrel hinv hm

theorem promoteCIList_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteCI m fuel u) m acc l =
      (do let (m, ys) ← promoteCIList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteCIList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_ci_list` ⊑ `promoteCIList`. -/
@[lockstep] theorem promote_ci_list_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absICIL r.2)
      (arena.promote.promote_ci_list pers st rm fuel us) lst
      (promoteCIList lm (absU fuel) (absICIL us)) := by
  have h := promote_ci_list_from_ls hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteCIList_pmapFrom] at h
  simpa [arena.promote.promote_ci_list, absICIL, alloc.vec.Vec.new] using h


section decl3
attribute [local lockstep_simp] absIConstantVal absIDeclaration absICIL

/-- `promote_decl` ⊑ `promoteDecl` — the seven constructors. -/
@[lockstep] theorem promote_decl_ls {pers st lst rm lm} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (d : arena.env.IDeclaration) :
    LS pers (fun r v => PMemoRel r.1 v.1 ∧ v.2 = absIDeclaration r.2)
      (arena.promote.promote_decl pers st rm fuel d) lst
      (promoteDecl lm (absU fuel) (absIDeclaration d)) := by
  cases d <;> rw [arena.promote.promote_decl] <;> simp only [absIDeclaration, promoteDecl] <;>
    lockstep

end decl3

end Lockstep

/-! ## The public statements

The `SimPM` forms the tier's consumers take, each one line from its judgement
above (`LS.toSimPM`).  Every one is lockstep: `AStateRel₀`, `AStateInv`, the
memo relation, and nothing about the twin's store — task #97-P5-Fresh's
promote window (`AStateRelW`, `StoreWF'`, the `ViewOK`/`NViewPers` premises of
the old `intern_persistent_n_run`) was Theorem-1 content, and under
`AStateRel₀` the window is not special (task #97-T2-AUDIT §2). -/

open Lockstep in
/-- **`promote_n` ⊑ `promoteN`** — the name walk. -/
theorem promote_n_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_n pers st rm fuel h = ok o) :
    SimPMF absNIdx pers lst o (promoteN lm (absU fuel) (absNIdx h)) :=
  LS.toSimPM (promote_n_ls hrel hinv hm fuel h) hrun

open Lockstep in
/-- `promote_n_node` ⊑ `promoteNNodeSpec` — at a view the Rust store produced
(`NNodeViewWF`: its string is a valid code-point sequence). -/
theorem promote_n_node_refines {pers st lst rm lm} {fuel : Std.U64}
    {v : arena.store.NNodeView} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hvwf : NNodeViewWF v)
    (hrun : arena.promote.promote_n_node pers st rm fuel v = ok o) :
    SimPMF absNIdx pers lst o
      (promoteNNodeSpec lm (absU fuel) (absNNodeView v)) :=
  LS.toSimPM (promote_n_node_ls hrel hinv hm fuel v hvwf) hrun

open Lockstep in
/-- `promote_l` ⊑ `promoteL`. -/
theorem promote_l_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l pers st rm fuel h = ok o) :
    SimPMF absLIdx pers lst o (promoteL lm (absU fuel) (absLIdx h)) :=
  LS.toSimPM (promote_l_ls hrel hinv hm fuel h) hrun

open Lockstep in
/-- `promote_l_node` ⊑ `promoteLNodeSpec`. -/
theorem promote_l_node_refines {pers st lst rm lm} {fuel : Std.U64}
    {v : arena.store.LNodeView} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_node pers st rm fuel v = ok o) :
    SimPMF absLIdx pers lst o
      (promoteLNodeSpec lm (absU fuel) (absLNodeView v)) :=
  LS.toSimPM (promote_l_node_ls hrel hinv hm fuel v) hrun

open Lockstep in
/-- `promote_l_two` is the two-child level arms' pair of promotions, in the
twin's order (`promoteLTwo`). -/
theorem promote_l_two_refines {pers st lst rm lm} {fuel : Std.U64}
    {u v : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_two pers st rm fuel u v = ok o) :
    SimPM (fun r p => p = (absLIdx r.1, absLIdx r.2)) pers lst o
      (promoteLTwo lm (absU fuel) (absLIdx u) (absLIdx v)) :=
  LS.toSimPM (promote_l_two_ls hrel hinv hm fuel u v) hrun

open Lockstep in
/-- `promote_l_list_from` ⊑ `promoteLList` at the cursor. -/
theorem promote_l_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {us : alloc.vec.Vec arena.handle.LIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_list_from pers st rm fuel us i out = ok o) :
    SimPMF absLIdxL pers lst o
      (do
        let (m, vs) ← promoteLList lm (absU fuel) (absLIdxLFrom us i)
        pure (m, absLIdxL out ++ vs)) := by
  have h := promote_l_list_from_ls hrel hinv hm fuel us i out
  rw [promoteLList_pmapFrom] at h
  exact LS.toSimPM h hrun

open Lockstep in
/-- `promote_l_list` ⊑ `promoteLList`. -/
theorem promote_l_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {us : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_list pers st rm fuel us = ok o) :
    SimPMF absLIdxL pers lst o (promoteLList lm (absU fuel) (absLIdxL us)) :=
  LS.toSimPM (promote_l_list_ls hrel hinv hm fuel us) hrun

open Lockstep in
/-- `promote_ls` ⊑ `promoteLs`. -/
theorem promote_ls_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.LsIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ls pers st rm fuel h = ok o) :
    SimPMF absLsIdx pers lst o (promoteLs lm (absU fuel) (absLsIdx h)) :=
  LS.toSimPM (promote_ls_ls hrel hinv hm fuel h) hrun

open Lockstep in
/-- `promote_e` ⊑ `promoteE`. -/
theorem promote_e_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e pers st rm fuel h = ok o) :
    SimPMF absEIdx pers lst o (promoteE lm (absU fuel) (absEIdx h)) :=
  LS.toSimPM (promote_e_ls hrel hinv hm fuel h) hrun

open Lockstep in
/-- `promote_e_node` ⊑ `promoteENodeSpec` — at a view the Rust store produced
(`ENodeViewWF`: the literal and the binder datum well formed). -/
theorem promote_e_node_refines {pers st lst rm lm} {fuel : Std.U64}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hvwf : ENodeViewWF v)
    (hrun : arena.promote.promote_e_node pers st rm fuel v = ok o) :
    SimPMF absEIdx pers lst o
      (promoteENodeSpec lm (absU fuel) (absENodeView v)) :=
  LS.toSimPM (promote_e_node_ls hrel hinv hm fuel v hvwf) hrun

open Lockstep in
/-- `promote_e_two` — the two-child expression arms' pair, in the twin's
order (`promoteETwo`). -/
theorem promote_e_two_refines {pers st lst rm lm} {fuel : Std.U64}
    {x y : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e_two pers st rm fuel x y = ok o) :
    SimPM (fun r p => p = (absEIdx r.1, absEIdx r.2)) pers lst o
      (promoteETwo lm (absU fuel) (absEIdx x) (absEIdx y)) :=
  LS.toSimPM (promote_e_two_ls hrel hinv hm fuel x y) hrun

/-! ## The lists -/

open Lockstep in
/-- `promote_n_list_from` ⊑ `promoteNList` at the cursor. -/
theorem promote_n_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_n_list_from pers st rm fuel ns i out = ok o) :
    SimPMF absNIdxL pers lst o
      (do
        let (m, vs) ← promoteNList lm (absU fuel) (absNIdxLFrom ns i)
        pure (m, absNIdxL out ++ vs)) := by
  have h := promote_n_list_from_ls hrel hinv hm fuel ns i out
  rw [promoteNList_pmapFrom] at h
  exact LS.toSimPM h hrun

open Lockstep in
/-- `promote_n_list` ⊑ `promoteNList`. -/
theorem promote_n_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_n_list pers st rm fuel ns = ok o) :
    SimPMF absNIdxL pers lst o (promoteNList lm (absU fuel) (absNIdxL ns)) :=
  LS.toSimPM (promote_n_list_ls hrel hinv hm fuel ns) hrun

open Lockstep in
/-- `promote_e_list_from` ⊑ `promoteEList` at the cursor. -/
theorem promote_e_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {es : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e_list_from pers st rm fuel es i out = ok o) :
    SimPMF absEIdxL pers lst o
      (do
        let (m, vs) ← promoteEList lm (absU fuel) (absEIdxLFrom es i)
        pure (m, absEIdxL out ++ vs)) := by
  have h := promote_e_list_from_ls hrel hinv hm fuel es i out
  rw [promoteEList_pmapFrom] at h
  exact LS.toSimPM h hrun

open Lockstep in
/-- `promote_e_list` ⊑ `promoteEList` — a block at ONE memo, so the sharing
survives the copy. -/
theorem promote_e_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {es : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e_list pers st rm fuel es = ok o) :
    SimPMF absEIdxL pers lst o (promoteEList lm (absU fuel) (absEIdxL es)) :=
  LS.toSimPM (promote_e_list_ls hrel hinv hm fuel es) hrun

/-! ## The declaration layer

`Arena/Env.lean`'s record, field for field: every handle is promoted and every
`Nat`, `Bool`, `ReducibilityHint`, `PropWhen` and `BinderMeta` crosses
unchanged (DESIGN §8.7's ruling that (B) imports con-leche's
representation-free types). -/

open Lockstep in
/-- `promote_cv` ⊑ `promoteCV`. -/
theorem promote_cv_refines {pers st lst rm lm} {fuel : Std.U64}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_cv pers st rm fuel cv = ok o) :
    SimPMF absIConstantVal pers lst o
      (promoteCV lm (absU fuel) (absIConstantVal cv)) :=
  LS.toSimPM (promote_cv_ls hrel hinv hm fuel cv) hrun

open Lockstep in
/-- `promote_fire` ⊑ `promoteFire`. -/
theorem promote_fire_refines {pers st lst rm lm} {fuel : Std.U64}
    {f : arena.env.IRecRuleFire} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_fire pers st rm fuel f = ok o) :
    SimPMF absIRecRuleFire pers lst o
      (promoteFire lm (absU fuel) (absIRecRuleFire f)) :=
  LS.toSimPM (promote_fire_ls hrel hinv hm fuel f) hrun

open Lockstep in
/-- `promote_rule` ⊑ `promoteRule`. -/
theorem promote_rule_refines {pers st lst rm lm} {fuel : Std.U64}
    {rl : arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_rule pers st rm fuel rl = ok o) :
    SimPMF absIRecRule pers lst o (promoteRule lm (absU fuel) (absIRecRule rl)) :=
  LS.toSimPM (promote_rule_ls hrel hinv hm fuel rl) hrun

open Lockstep in
/-- `promote_rules_from` ⊑ `promoteRules` at the cursor. -/
theorem promote_rules_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {rs : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_rules_from pers st rm fuel rs i out = ok o) :
    SimPMF absIRecRuleL pers lst o
      (do
        let (m, vs) ← promoteRules lm (absU fuel) (absIRecRuleLFrom rs i)
        pure (m, absIRecRuleL out ++ vs)) := by
  have h := promote_rules_from_ls hrel hinv hm fuel rs i out
  rw [promoteRules_pmapFrom] at h
  exact LS.toSimPM h hrun

open Lockstep in
/-- `promote_rules` ⊑ `promoteRules`. -/
theorem promote_rules_refines {pers st lst rm lm} {fuel : Std.U64}
    {rs : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_rules pers st rm fuel rs = ok o) :
    SimPMF absIRecRuleL pers lst o (promoteRules lm (absU fuel) (absIRecRuleL rs)) :=
  LS.toSimPM (promote_rules_ls hrel hinv hm fuel rs) hrun

open Lockstep in
/-- `promote_caps` ⊑ `promoteCaps` — one name; `sortZ` is a `PropWhen` over
con-leche `Name`s and carries no handle. -/
theorem promote_caps_refines {pers st lst rm lm} {fuel : Std.U64}
    {c : arena.env.IIndCaps} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_caps pers st rm fuel c = ok o) :
    SimPMF absIIndCaps pers lst o (promoteCaps lm (absU fuel) (absIIndCaps c)) :=
  LS.toSimPM (promote_caps_ls hrel hinv hm fuel c) hrun

open Lockstep in
/-- `promote_proj_table` ⊑ `promoteProjTable`, `tableName` included (it is a
stored handle, not a recomputed name — `Arena/Env.lean`'s one added field). -/
theorem promote_proj_table_refines {pers st lst rm lm} {fuel : Std.U64}
    {t : arena.env.IProjTable} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_proj_table pers st rm fuel t = ok o) :
    SimPMF absIProjTable pers lst o
      (promoteProjTable lm (absU fuel) (absIProjTable t)) :=
  LS.toSimPM (promote_proj_table_ls hrel hinv hm fuel t) hrun

open Lockstep in
/-- `promote_proj_table_rest` is the Rust-only tail of `promote_proj_table`
past its three leading promotions (extraction rule 5), stated against the
twin's tail (`promoteProjTableRest`) with those handles in hand. -/
theorem promote_proj_table_rest_refines {pers st lst rm lm} {fuel : Std.U64}
    {t : arena.env.IProjTable} {sn tn : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_proj_table_rest pers st rm fuel t sn tn lps = ok o) :
    SimPMF absIProjTable pers lst o
      (promoteProjTableRest lm (absU fuel) (absIProjTable t) (absNIdx sn) (absNIdx tn)
        (absNIdxL lps)) :=
  LS.toSimPM (promote_proj_table_rest_ls hrel hinv hm fuel t sn tn lps) hrun

open Lockstep in
/-- `promote_ci` ⊑ `promoteCI` — the seven `IConstantInfo` constructors, which
is what "the handles the environment keeps" means. -/
theorem promote_ci_refines {pers st lst rm lm} {fuel : Std.U64}
    {ci : arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ci pers st rm fuel ci = ok o) :
    SimPMF absIConstantInfo pers lst o
      (promoteCI lm (absU fuel) (absIConstantInfo ci)) :=
  LS.toSimPM (promote_ci_ls hrel hinv hm fuel ci) hrun

open Lockstep in
/-- `promote_ci_list_from` ⊑ `promoteCIList` at the cursor. -/
theorem promote_ci_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {cs : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ci_list_from pers st rm fuel cs i out = ok o) :
    SimPMF absICIL pers lst o
      (do
        let (m, vs) ← promoteCIList lm (absU fuel) (absICILFrom cs i)
        pure (m, absICIL out ++ vs)) := by
  have h := promote_ci_list_from_ls hrel hinv hm fuel cs i out
  rw [promoteCIList_pmapFrom] at h
  exact LS.toSimPM h hrun

open Lockstep in
/-- `promote_ci_list` ⊑ `promoteCIList` — a block at ONE memo. -/
theorem promote_ci_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {cs : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ci_list pers st rm fuel cs = ok o) :
    SimPMF absICIL pers lst o (promoteCIList lm (absU fuel) (absICIL cs)) :=
  LS.toSimPM (promote_ci_list_ls hrel hinv hm fuel cs) hrun

open Lockstep in
/-- `promote_decl` ⊑ `promoteDecl` — not on the fold's path (the records
arrive from the parse and are persistent) and twinned because the layer is
twinned whole. -/
theorem promote_decl_refines {pers st lst rm lm} {fuel : Std.U64}
    {d : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_decl pers st rm fuel d = ok o) :
    SimPMF absIDeclaration pers lst o
      (promoteDecl lm (absU fuel) (absIDeclaration d)) :=
  LS.toSimPM (promote_decl_ls hrel hinv hm fuel d) hrun

/-- `promote_vg` ⊑ `promoteVG` — the datum that crosses the install/check
seam, promoted beside the environment and at the SAME memo (an `opaque`'s
value is not in the environment; only the pending record holds it). -/
theorem promote_vg_refines {pers st lst rm lm} {fuel : Std.U64}
    {g : arena.checker_split.ValueGroup} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_vg pers st rm fuel g = ok o) :
    SimPMF absValueGroup pers lst o
      (promoteVG lm (absU fuel) (absValueGroup g)) := by
  rw [arena.promote.promote_vg] at hrun
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have h1 := promote_cv_refines hrel hinv hm hq1
  simp only [SimPM, POut] at h1
  unfold SimPMF SimPM
  rw [promoteVG, am_run_bind']
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st1) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AErrSim.bind h1 _
  | Ok p1 =>
    obtain ⟨m2, cv2⟩ := p1
    obtain ⟨m', v1, lst1, hx1, hv1, hm1, hrel1, hinv1⟩ := h1
    obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r2, st2⟩ := q2
    have h2 := promote_e_refines hrel1 hinv1 hm1 hq2
    simp only [SimPM, POut] at h2
    erw [hx1, except_ok_bind]
    dsimp only
    rw [am_run_bind']
    cases r2 with
    | Err e =>
      have hrun' : (ok (core.result.Result.Err e, st2) : Result _) = ok o := hrun
      obtain rfl := (Result.ok_injective hrun').symm
      exact AErrSim.bind h2 _
    | Ok p2 =>
      obtain ⟨m3, jv2⟩ := p2
      obtain ⟨m'', v2, lst2, hx2, hv2, hm2, hrel2, hinv2⟩ := h2
      obtain rfl := (Result.ok_injective hrun).symm
      erw [hx2, except_ok_bind]
      refine ⟨m'', _, lst2, rfl, ?_, hm2, hrel2, hinv2⟩
      simp only [absValueGroup, hv1, hv2]

/-! ## The fold's entry

**Three findings, and all three are about the same function.**

*Finding A — `erase_installed` and `index_promoted` walk the environment the
other way.*  The twin's `IEnv.consts` is con-leche's newest-first `List` and
the Rust's is an oldest-first `Vec` whose index stores a POSITION into it
(`Refine2/AbsState.lean`'s note), so "the `k` newest" is `consts.take k` on
one side and slots `n - k .. n` on the other, and the re-indexing loop that
runs DOWN from `n` over the Rust is the twin's head-to-tail recursion.  The
two statements below spell that correspondence out; it is arithmetic and not
a divergence.

*Finding B — the port's `index_promoted` FUSES what the twin does in two
passes*, and the fusion is sound only because promotion reads no index.  The
twin is `promoteCIList` and then `indexPromoted`; the port promotes slot
`j-1`, writes it back into its own slot (the Aeneas subset cannot move an
element out of an owned `Vec`) and inserts its row, then recurses.  Since
`promote_ci` touches only the store and the memo, the interleaving is
invisible — but it is why `index_promoted_refines` is stated against the
twin's two passes composed, and not against a loop.

*Finding C — `promote_new` DECLINES where the twin promotes, and the
statement needs `k ≤ n`.*  The port answers `Ok (m, fe)` unchanged when
`k as usize > fe.env.consts.len()`; the twin's `promoteNew` has no such arm —
`consts.take k` at `k > length` is the whole list, so it promotes everything.
The port's arm is a guard on a `usize` cast, so "the twin does the same" is
false there and the success arm of §8.2 fails.  The hypothesis is
`absU k ≤ rf.env.consts.val.length`, which every call site has: `k` is
`fe.visibleBelow - n₀` for the counter read before the step, and every install
route grows the environment by `IFEnv.push` alone.  Like task #97-P5-0's
finding 3 and task #97-P5-1's findings 7–8, **it is Theorem 1's clause to
carry**, not this tier's to re-derive. -/

/-- `eraseInstalled` reads back as a membership test.  Copied from
`Bridge/Promote/Coh.lean`'s `eraseInstalled_getElem?_eq` (`Refine2` may not
import `Bridge`). -/
theorem eraseInstalled_getElem?_eq' (n : NIdx) : ∀ (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)),
    (eraseInstalled idx cs)[n]? = if (∃ c ∈ cs, c.name = n) then none else idx[n]? := by
  intro cs
  induction cs with
  | nil => intro idx; simp [eraseInstalled]
  | cons c cs ih =>
    intro idx
    simp only [eraseInstalled, ih, Std.HashMap.getElem?_erase]
    by_cases h1 : ∃ c' ∈ cs, c'.name = n
    · rw [if_pos h1, if_pos ⟨_, List.mem_cons_of_mem _ h1.choose_spec.1, h1.choose_spec.2⟩]
    · rw [if_neg h1]
      by_cases h2 : c.name = n
      · rw [if_pos (beq_iff_eq.mpr h2), if_pos ⟨c, by simp, h2⟩]
      · rw [if_neg (by simpa using h2), if_neg]
        rintro ⟨c', hc', hn⟩
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact h2 hn
        · exact h1 ⟨c', hc', hn⟩

/-- `erase_installed`'s loop, read back at the port's own index: the rows
keyed by a name of slots `i..n` are gone, the rest untouched, the environment
and the counter do not move. -/
private theorem erase_installed_aux (m : Nat) :
    ∀ {rf : arena.env.IFEnv} {i : Std.Usize} {o},
      rf.env.consts.val.length - i.val = m → IFEnvInv rf →
      arena.promote.erase_installed rf i = ok o →
      o.env = rf.env ∧ o.visible_below = rf.visible_below ∧ IFEnvInv o ∧
      ∀ k, ConRon.Refine.HashMap2.toFun o.idx k =
        if (∃ c ∈ rf.env.consts.val.drop i.val, (absIConstantInfo c).name = absNIdx k)
        then none else ConRon.Refine.HashMap2.toFun rf.idx k := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro rf i o hm hfinv hrun
    rw [arena.promote.erase_installed.eq_def] at hrun
    dsimp only at hrun
    have hl := alloc.vec.Vec.len_val rf.env.consts
    by_cases hge : i ≥ alloc.vec.Vec.len rf.env.consts
    · have hle : rf.env.consts.val.length ≤ i.val := by scalar_tac
      rw [if_pos hge] at hrun
      obtain rfl := (Result.ok_injective hrun).symm
      refine ⟨rfl, rfl, hfinv, fun k => ?_⟩
      rw [List.drop_eq_nil_of_le hle]
      simp
    · have hlt : i.val < rf.env.consts.val.length := by scalar_tac
      rw [if_neg hge] at hrun
      obtain ⟨ci, hci, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hci' := vec_index_some hci
      rw [List.getElem?_eq_getElem hlt] at hci'
      obtain rfl := (Option.some_inj.mp hci').symm
      obtain ⟨nn, hnn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm'⟩ := q
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have hname : absNIdx nn = (absIConstantInfo rf.env.consts.val[i.val]).name :=
        i_constant_info_name_abs hnn
      obtain ⟨hinv', -, hupd, -⟩ :=
        ConRon.Refine.HashMap2.remove_refines_wf (P := fun _ => True) nidx_eq2
          hfinv.idxInv ConRon.Refine.HashMap2.KeysOk_true trivial hq
      have hfinv1 : IFEnvInv { rf with idx := hm' } := by
        refine ⟨hinv', hfinv.2.1, fun k p hp => ?_⟩
        simp only at hp
        rw [hupd, Function.update_apply] at hp
        split at hp
        · cases hp
        · exact hfinv.2.2 k p hp
      obtain ⟨he, hv, hI, hidx⟩ :=
        ih (rf.env.consts.val.length - i2.val) (by omega) (rf := { rf with idx := hm' })
          rfl hfinv1 hrun
      refine ⟨he, hv, hI, fun k => ?_⟩
      rw [hidx k]
      simp only
      rw [hupd, Function.update_apply, hi2v, List.drop_eq_getElem_cons hlt]
      by_cases hr : ∃ c ∈ rf.env.consts.val.drop (i.val + 1),
          (absIConstantInfo c).name = absNIdx k
      · rw [if_pos hr, if_pos (by
          obtain ⟨c, hc, h⟩ := hr; exact ⟨c, List.mem_cons_of_mem _ hc, h⟩)]
      · rw [if_neg hr]
        by_cases hk : k = nn
        · rw [if_pos hk, if_pos ⟨_, List.mem_cons_self, by rw [hk]; exact hname.symm⟩]
        · rw [if_neg hk, if_neg]
          rintro ⟨c, hc, h⟩
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hk (absNIdx_inj (h.symm.trans hname.symm))
          · exact hr ⟨c, hc, h⟩

private theorem take_rev_mem {α β : Type} (f : α → β) (v : List α) (i : Nat) (c : β) :
    c ∈ ((v.map f).reverse.take (v.length - i)) ↔ c ∈ (v.drop i).map f := by
  rw [List.take_reverse, List.mem_reverse, List.length_map, ← List.map_drop]
  by_cases h : i ≤ v.length
  · rw [Nat.sub_sub_self h]
  · rw [show v.length - (v.length - i) = v.length by omega, List.drop_length,
      List.drop_eq_nil_of_le (by omega)]

/-- `erase_installed` forgets the index rows of the constants at slots `i..n`,
which over the twin's newest-first list is `eraseInstalled` at its first
`n - i`.  A stale row under a scratch key is not merely useless:
`dropScratch` hands that word back to the next declaration, and `IFEnv.find?`
would answer a different constant under it. -/
theorem erase_installed_refines {rf lf} {i : Std.Usize} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.promote.erase_installed rf i = ok o) :
    (IFEnvRel o
        { lf with
          idx := eraseInstalled lf.idx
                   ((absIEnv rf.env).consts.take
                     (rf.env.consts.val.length - i.val)) })
      ∧ IFEnvInv o := by
  obtain ⟨he, hv, hI, hidx⟩ := erase_installed_aux _ rfl hfinv hrun
  refine ⟨⟨?_, ?_, ?_⟩, hI⟩
  · show lf.env = absIEnv o.env
    rw [he]; exact hfe.env
  · intro k
    show _ = (eraseInstalled lf.idx _)[absNIdx k]?
    rw [eraseInstalled_getElem?_eq', hidx k, he]
    have hmem : (∃ c ∈ (absIEnv rf.env).consts.take (rf.env.consts.val.length - i.val),
          c.name = absNIdx k) ↔
        (∃ c ∈ rf.env.consts.val.drop i.val, (absIConstantInfo c).name = absNIdx k) := by
      simp only [absIEnv, take_rev_mem, List.mem_map]
      constructor
      · rintro ⟨c, ⟨a, ha, rfl⟩, h⟩; exact ⟨a, ha, h⟩
      · rintro ⟨a, ha, h⟩; exact ⟨_, ⟨a, ha, rfl⟩, h⟩
    by_cases hr : ∃ c ∈ rf.env.consts.val.drop i.val, (absIConstantInfo c).name = absNIdx k
    · rw [if_pos hr, if_pos (hmem.mpr hr)]; rfl
    · rw [if_neg hr, if_neg (fun h => hr (hmem.mp h))]
      exact hfe.idx k
  · show lf.visibleBelow = absU o.visible_below
    rw [hv]; exact hfe.visibleBelow

/-- The twin of `index_promoted` on the slice `start..j` of a newest-first
constant list `cs` of length `n`: `promoteCIList` on the slice, then
`indexPromoted` (finding B), the rest of the list untouched. -/
def indexPromotedTwin (m : PMemo) (fuel : Nat) (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (vb n start j c : Nat) :
    AM (PMemo × IFEnv) := do
  let (m, mid) ← promoteCIList m fuel ((cs.drop (n - j)).take (j - start))
  pure (m, ⟨⟨cs.take (n - j) ++ mid ++ cs.drop (n - start)⟩, indexPromoted idx c mid, vb⟩)

theorem indexPromotedTwin_zero (m : PMemo) (fuel : Nat) (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (vb n j c : Nat) :
    indexPromotedTwin m fuel cs idx vb n j j c = pure (m, ⟨⟨cs⟩, idx, vb⟩) := by
  simp [indexPromotedTwin, promoteCIList, indexPromoted]

private theorem take_set_succ {α : Type} : ∀ (l : List α) (i : Nat) (x : α),
    i < l.length → (l.set i x).take (i + 1) = l.take i ++ [x]
  | [], _, _, h => by simp at h
  | y :: ys, 0, x, _ => by simp
  | y :: ys, i + 1, x, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
    rw [take_set_succ ys i x (by simpa using h)]

/-- One step of the slice: the newest constant of the slice promoted, written
back into its own position and indexed, then the rest of the slice. -/
theorem indexPromotedTwin_succ (m : PMemo) (fuel : Nat) (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (vb n start j c : Nat)
    (hn : cs.length = n) (hsj : start < j) (hj : j ≤ n) :
    indexPromotedTwin m fuel cs idx vb n start j c =
      (do
        let (m, c') ← promoteCI m fuel (cs[n - j]'(by omega))
        indexPromotedTwin m fuel (cs.set (n - j) c') (idx.insert c'.name (c - 1, c')) vb
          n start (j - 1) (c - 1)) := by
  have hlt : n - j < cs.length := by omega
  have hd : (cs.drop (n - j)).take (j - start)
      = cs[n - j] :: (cs.drop (n - j + 1)).take (j - 1 - start) := by
    rw [List.drop_eq_getElem_cons hlt, show j - start = (j - 1 - start) + 1 by omega,
      List.take_succ_cons]
  simp only [indexPromotedTwin, hd, promoteCIList, bind_assoc]
  congr 1
  funext p
  obtain ⟨m', c'⟩ := p
  simp only [bind_assoc, pure_bind]
  have h1 : n - (j - 1) = n - j + 1 := by omega
  rw [h1, List.drop_set_of_lt (by omega), take_set_succ cs (n - j) c' hlt,
    List.drop_set_of_lt (show n - j < n - start by omega),
    show j - 1 - start = j - 1 - start from rfl]
  congr 1
  funext q
  obtain ⟨m'', mid⟩ := q
  simp [indexPromoted, List.append_assoc]

/-- **The index clause `index_promoted` needs** (a statement gap, found by this
task): every row of the port's index points at a slot whose constant carries
the row's key.  `IFEnvRel` reads a row THROUGH its position, so overwriting a
slot moves every row that points at it; the twin re-indexes by NAME.  The two
agree exactly when the rows at a slot are keyed by that slot's name.  It is a
fact about the Rust `IFEnv` alone (every writer — `mk_ifenv_go`,
`ifenv_push`, `index_promoted` — stores its own constant's name at its own
slot), the kind of representation invariant `IFEnvInv` carries. -/
def IFEnvKeys (rf : arena.env.IFEnv) : Prop :=
  ∀ k p, ConRon.Refine.HashMap2.toFun rf.idx k = some p →
    ∃ ci, rf.env.consts.val[p.2.val]? = some ci ∧ (absIConstantInfo ci).name = absNIdx k

theorem reverse_set' {α : Type} (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    (l.set i x).reverse = l.reverse.set (l.length - 1 - i) x := by
  apply List.ext_getElem (by simp)
  intro q h1 h2
  simp only [List.length_reverse, List.length_set] at h1 h2
  simp only [List.getElem_reverse, List.getElem_set, List.length_set, List.length_reverse]
  split_ifs <;> first | rfl | omega

private theorem index_promoted_step {rf lf : _} {start j i : Std.Usize}
    {c i1 i2 : Std.U64} {ci : arena.env.IConstantInfo} {nn : arena.handle.NIdx}
    {hm : ron.hashmap2.HashMap2 arena.handle.NIdx (Std.U64 × Std.U64)}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hfree : ∀ k p, ConRon.Refine.HashMap2.toFun rf.idx k = some p →
      p.2.val < start.val ∨ j.val ≤ p.2.val)
    (hsj : start.val < j.val) (hj : j.val ≤ rf.env.consts.val.length)
    (hiv : i.val = j.val - 1) (hi1 : i1.val = c.val - 1) (hc1 : 1 ≤ c.val)
    (hi2 : i2.val = i.val)
    (hnn : absNIdx nn = (absIConstantInfo ci).name)
    (hinvm : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable hm)
    (hupd : ConRon.Refine.HashMap2.toFun hm =
      Function.update (ConRon.Refine.HashMap2.toFun rf.idx) nn (some (i1, i2))) :
    let rf' : arena.env.IFEnv :=
      { rf with env := { consts := alloc.vec.Vec.set rf.env.consts i ci }, idx := hm }
    let lf' : IFEnv :=
      ⟨⟨lf.env.consts.set (rf.env.consts.val.length - j.val) (absIConstantInfo ci)⟩,
        lf.idx.insert (absIConstantInfo ci).name (absU c - 1, absIConstantInfo ci),
        lf.visibleBelow⟩
    IFEnvRel rf' lf' ∧ IFEnvInv rf' ∧
      rf'.env.consts.val.length = rf.env.consts.val.length ∧
      ∀ k p, ConRon.Refine.HashMap2.toFun rf'.idx k = some p →
        p.2.val < start.val ∨ i.val ≤ p.2.val := by
  intro rf' lf'
  have hlen : rf'.env.consts.val.length = rf.env.consts.val.length := by
    simp [rf', alloc.vec.Vec.set_val_eq]
  have hil : i.val < rf.env.consts.val.length := by omega
  -- the Rust list at `i` and elsewhere
  have hget : ∀ q : Nat, rf'.env.consts.val[q]? =
      if q = i.val then (if q < rf.env.consts.val.length then some ci else none)
      else rf.env.consts.val[q]? := by
    intro q
    simp only [rf', alloc.vec.Vec.set_val_eq]
    rw [List.getElem?_set]
    by_cases hq : i.val = q
    · subst hq; simp [hil]
    · simp [hq, Ne.symm hq]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hinvm, ?_, ?_⟩, hlen, ?_⟩
  · -- the environment: the reversed list, set at the mirrored position
    show lf'.env = absIEnv rf'.env
    simp only [lf', absIEnv, hfe.env]
    congr 1
    simp only [rf', alloc.vec.Vec.set_val_eq, List.map_set]
    rw [reverse_set' _ _ _ (by simpa using hil)]
    simp only [List.length_map]
    congr 1
    omega
  · intro k
    show ((ConRon.Refine.HashMap2.toFun hm k).bind fun p =>
        (rf'.env.consts.val[p.2.val]?).map fun ci => (absU p.1, absIConstantInfo ci))
      = (lf.idx.insert (absIConstantInfo ci).name (absU c - 1, absIConstantInfo ci))[absNIdx k]?
    rw [hupd, Function.update_apply]
    by_cases hk : k = nn
    · subst hk
      rw [if_pos rfl, ← hnn, Std.HashMap.getElem?_insert_self]
      simp only [Option.bind_some, hget, hi2, if_pos hil, if_true, Option.map_some]
      congr 2
    · rw [if_neg hk, Std.HashMap.getElem?_insert, ← hnn,
        if_neg (by intro h; exact hk (absNIdx_inj (by simpa using h)).symm), ← hfe.idx k]
      cases hp : ConRon.Refine.HashMap2.toFun rf.idx k with
      | none => rfl
      | some p =>
        simp only [Option.bind_some]
        rw [hget, if_neg]
        rcases hfree k p hp with h | h <;> omega
  · exact hfe.visibleBelow
  · show rf.visible_below.val ≤ rf'.env.consts.val.length
    rw [hlen]; exact hfinv.visBound
  · intro k p hp
    rw [hlen]
    simp only [rf'] at hp
    rw [hupd, Function.update_apply] at hp
    split at hp
    · cases hp; simp only; omega
    · exact hfinv.idxRange k p hp
  · intro k p hp
    simp only [rf'] at hp
    rw [hupd, Function.update_apply] at hp
    split at hp
    · cases hp; simp only; omega
    · rcases hfree k p hp with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)

open Lockstep in
private theorem index_promoted_aux (d : Nat) :
    ∀ {pers st lst rm lm rf lf} (fuel : Std.U64) (start j : Std.Usize) (c : Std.U64),
      j.val - start.val = d → start.val ≤ j.val → j.val ≤ rf.env.consts.val.length →
      AStateRel₀ pers st lst → AStateInv pers st → PMemoRel rm lm →
      IFEnvRel rf lf → IFEnvInv rf →
      (∀ k p, ConRon.Refine.HashMap2.toFun rf.idx k = some p →
        p.2.val < start.val ∨ j.val ≤ p.2.val) →
      LS pers (fun r v => PMemoRel r.1 v.1 ∧ IFEnvRelI r.2 v.2)
        (arena.promote.index_promoted pers st rm fuel rf start j c) lst
        (indexPromotedTwin lm (absU fuel) lf.env.consts lf.idx lf.visibleBelow
          rf.env.consts.val.length start.val j.val (absU c)) := by
  induction d with
  | zero =>
    intro pers st lst rm lm rf lf fuel start j c hd hle hj hrel hinv hm hfe hfinv hfree
    have hje : j.val = start.val := by omega
    rw [arena.promote.index_promoted, if_pos (by scalar_tac), hje, indexPromotedTwin_zero]
    exact LS.pure ⟨hm, hfe, hfinv⟩ hrel hinv
  | succ d ih =>
    intro pers st lst rm lm rf lf fuel start j c hd hle hj hrel hinv hm hfe hfinv hfree
    have hsj : start.val < j.val := by omega
    have hlen : lf.env.consts.length = rf.env.consts.val.length := by
      rw [hfe.env]; simp [absIEnv]
    rw [arena.promote.index_promoted, if_neg (by scalar_tac),
      indexPromotedTwin_succ _ _ _ _ _ _ _ _ _ hlen hsj hj]
    refine LS.bind_eq fun i hi => ?_
    obtain ⟨-, hi1⟩ := ConRon.Refine.Nat.usub_val hi
    have hiv : i.val = j.val - 1 := by rw [hi1]; rfl
    refine LS.bind_eq fun ii hii => ?_
    obtain ⟨hb, hii⟩ := ExprOps.vecIndexAt hii
    have htw : absIConstantInfo ii =
        lf.env.consts[rf.env.consts.val.length - j.val]'(by omega) := by
      simp only [hfe.env, absIEnv, List.getElem_reverse, List.getElem_map, List.length_map]
      rw [← hii]
      have e : rf.env.consts.val.length - 1 - (rf.env.consts.val.length - j.val) = i.val := by
        omega
      simp only [e]
    refine LS.bind (promote_ci_ls hrel hinv hm fuel ii) (by rw [htw]) ?_ ?_
    · intro e st1
      exact errArm_ok
    · rintro ⟨m2, ci⟩ ⟨m2', ci'⟩ st1 lst1 ⟨hM, hci⟩ hrel1 hinv1
      simp only at hM hci
      subst hci
      try simp only
      refine LS.bind_eq fun nn hnn => ?_
      have hnn' := i_constant_info_name_abs hnn
      refine LS.bind_eq fun i1 hi1' => ?_
      obtain ⟨hc1, hi1v⟩ := ConRon.Refine.Nat.usub_val hi1'
      refine LS.bind_eq fun i2 hi2 => ?_
      have hi2v : i2.val = i.val := by
        simp only [lift, Result.ok.injEq] at hi2
        rw [← hi2, usize_cast_u64_val]
      refine LS.bind_eq fun q hq => ?_
      obtain ⟨old, hmm⟩ := q
      obtain ⟨hinvm, -, hupd, -⟩ :=
        ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True) nidx_eq2
          hfinv.idxInv ConRon.Refine.HashMap2.KeysOk_true trivial hq
      try simp only
      refine LS.bind_eq fun q2 hq2 => ?_
      obtain ⟨x, back⟩ := q2
      haveI : Inhabited arena.env.IConstantInfo := ⟨ci⟩
      obtain ⟨-, -, hback⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq2
      subst hback
      try simp only
      obtain ⟨hrel', hinv', hlen', hfree'⟩ := index_promoted_step (i := i) (ci := ci) (nn := nn)
        (c := c) (i1 := i1) (i2 := i2) hfe hfinv hfree hsj hj hiv hi1v (by
          rw [u64_one_val] at hc1; exact hc1) hi2v hnn' hinvm hupd
      have hrec := ih fuel start i i1 (by omega) (by omega) (by rw [hlen']; omega)
          hrel1 hinv1 hM hrel' hinv' hfree'
      rw [hlen'] at hrec
      refine LS.tail hrec ?_ (fun _ _ h => h)
      simp only [hiv, show absU i1 = absU c - 1 from hi1v]

/-- `index_promoted` ⊑ `promoteCIList` followed by `indexPromoted`, on the
slice `start..j` (finding B: the port fuses the two passes, which promotion
reading no index makes invisible).  The promoted records are written back
into their own slots, so the environment's shape is unchanged and only the
middle segment moves.

`hfree` — *no index row points into the slice* — is the Rust-side fact the
statement needs (`IFEnvKeys`' note): a row pointing at a slot of the slice
would move with the overwrite, and the twin's row (keyed by name) would not.
`promote_new` establishes it from `IFEnvKeys` and `erase_installed`. -/
theorem index_promoted_refines {pers st lst rm lm rf lf} {fuel : Std.U64}
    {start j : Std.Usize} {c : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hle : start.val ≤ j.val) (hj : j.val ≤ rf.env.consts.val.length)
    (hfree : ∀ k p, ConRon.Refine.HashMap2.toFun rf.idx k = some p →
      p.2.val < start.val ∨ j.val ≤ p.2.val)
    (hrun : arena.promote.index_promoted pers st rm fuel rf start j c = ok o) :
    SimPM IFEnvRelI pers lst o
      (indexPromotedTwin lm (absU fuel) (absIEnv rf.env).consts lf.idx lf.visibleBelow
        rf.env.consts.val.length start.val j.val (absU c)) := by
  have h := index_promoted_aux _ fuel start j c rfl hle hj hrel hinv hm hfe hfinv hfree
  rw [hfe.env] at h
  exact Lockstep.LS.toSimPM h hrun

/-- **`promote_new` ⊑ `promoteNew`** — the phase-A bracket's promotion half:
the `k` constants the step just installed, copied into the persistent tier and
re-indexed, everything below them untouched.  `hk` is finding C.

**The result relation is `IFEnvRelI`, not `IFEnvRel`** (task #97-P5-Checker
round 4): both bracketed steps of `Refine2/Checker/Top.lean` hand
`promote_new`'s environment to the NEXT step of their fold, which takes
`IFEnvInv` beside `IFEnvRel` (task #97-P5-Checker-2 §3's `IFEnvRelI`).  It is
true — `index_promoted` stores `j - 1` for a cursor `j ≤ n`, `erase_installed`
only removes rows, the environment's length and counter do not move, and the
decline arm returns `fe` itself — and without it neither leaf closes. -/
theorem promote_new_refines_keyed {pers st lst rm lm rf lf} {fuel k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hkeys : IFEnvKeys rf)
    (hk : absU k ≤ rf.env.consts.val.length)
    (hrun : arena.promote.promote_new pers st rm fuel k rf = ok o) :
    SimPM IFEnvRelI pers lst o
      (promoteNew lm (absU fuel) (absU k) lf) := by
  rw [arena.promote.promote_new] at hrun
  by_cases hk0 : k = 0#u64
  · rw [if_pos hk0] at hrun
    obtain rfl := (Result.ok_injective hrun).symm
    have h0 : absU k = 0 := by rw [hk0]; rfl
    unfold SimPM
    rw [promoteNew, h0]
    exact ⟨lm, lf, lst, rfl, ⟨hfe, hfinv⟩, hm, hrel, hinv⟩
  · rw [if_neg hk0] at hrun
    have hn := alloc.vec.Vec.len_val rf.env.consts
    obtain ⟨kk, hkk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hkkv : kk.val = k.val := by
      simp only [lift, Result.ok.injEq] at hkk
      rw [← hkk]
      have hkb : k.val ≤ Std.Usize.max := le_trans hk rf.env.consts.property
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    have hkle : ¬ kk > alloc.vec.Vec.len rf.env.consts := by
      have : absU k = k.val := rfl
      scalar_tac
    rw [if_neg hkle] at hrun
    obtain ⟨start, hstart, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hsv : start.val = rf.env.consts.val.length - k.val := by
      have := ConRon.Refine.HashMap.uscalar_sub_eq hstart
      scalar_tac
    obtain ⟨fe2, hfe2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨hR2, hI2⟩ := erase_installed_refines hfe hfinv hfe2
    have henv : absIEnv fe2.env = absIEnv rf.env := by
      rw [← hR2.env, ← hfe.env]
    have hlen : fe2.env.consts.val.length = rf.env.consts.val.length := by
      have h := congrArg (fun e : IEnv => e.consts.length) henv
      simpa [absIEnv] using h
    -- no row of the erased index points into the installed slots
    have hfree : ∀ kk p, ConRon.Refine.HashMap2.toFun fe2.idx kk = some p →
        p.2.val < start.val ∨ (alloc.vec.Vec.len rf.env.consts).val ≤ p.2.val := by
      intro kk p hp
      obtain ⟨-, -, -, hidx⟩ := erase_installed_aux _ rfl hfinv hfe2
      rw [hidx kk] at hp
      split at hp
      · cases hp
      · rename_i hnot
        left
        obtain ⟨ci, hci, hname⟩ := hkeys kk p hp
        by_contra hge
        apply hnot
        have hlt : p.2.val < rf.env.consts.val.length := hfinv.idxRange kk p hp
        refine ⟨ci, ?_, hname⟩
        rw [List.getElem?_eq_getElem hlt] at hci
        cases (Option.some_inj.mp hci)
        exact List.mem_iff_getElem.mpr ⟨p.2.val - start.val, by simp; omega,
          by simp [List.getElem_drop]; congr 1; omega⟩
    have hI := index_promoted_refines hrel hinv hm hR2 hI2
      (by scalar_tac) (by rw [hlen]; scalar_tac) hfree hrun
    have hkabs : absU k = k.val := rfl
    have hk0' : (absU k == 0) = false := by
      have : k.val ≠ 0 := by
        intro h; apply hk0; exact Aeneas.Std.UScalar.eq_imp _ _ (by simpa using h)
      simpa [hkabs] using this
    have hvb : absU rf.visible_below = lf.visibleBelow := hfe.visibleBelow.symm
    -- the twin's two sides are one action
    have htw : indexPromotedTwin lm (absU fuel) (absIEnv fe2.env).consts
          (eraseInstalled lf.idx
            ((absIEnv rf.env).consts.take (rf.env.consts.val.length - start.val)))
          lf.visibleBelow fe2.env.consts.val.length start.val
          (alloc.vec.Vec.len rf.env.consts).val (absU rf.visible_below)
        = promoteNew lm (absU fuel) (absU k) lf := by
      rw [indexPromotedTwin]
      have hlenA : ((absIEnv rf.env).consts).length = rf.env.consts.val.length := by
        simp [absIEnv]
      rw [promoteNew, hk0']
      obtain ⟨⟨consts⟩, idx, vb⟩ := lf
      have hcs : (absIEnv rf.env).consts = consts := by
        have := hfe.env; simp only at this; rw [← this]
      simp only [henv, hlen, hn, hcs, hvb, Nat.sub_self, List.drop_zero, List.take_zero,
        List.nil_append, hsv, Bool.false_eq_true, ↓reduceIte]
      have hkn : k.val ≤ rf.env.consts.val.length := hk
      rw [Nat.sub_sub_self hkn, hkabs]
    rw [← htw]
    exact hI

/-- **`promote_new` ⊑ `promoteNew`, as the checker tier consumes it** — the
statement without `IFEnvKeys`.

**`sorry`, and false as stated** (task #97-T2-LOCKSTEP lane Promote): with a
row `b ↦ (0, 0)` keyed by a name that is NOT slot 0's, `IFEnvRel` holds (the
twin row reads `(0, abs consts[0])`), `erase_installed` leaves the row, and
`index_promoted` overwrites slot 0 with its promotion — the port's row now
reads the PROMOTED constant, the twin's still the old one.
`promote_new_refines_keyed` is the true statement; the key clause is a
Rust-side representation invariant of `IFEnv` (every writer keeps it) and
belongs in `IFEnvInv`, which is the checker lane's shape — the ruling asked
for in DESIGN `#97-T2-LANE-Promote`. -/
theorem promote_new_refines {pers st lst rm lm rf lf} {fuel k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hk : absU k ≤ rf.env.consts.val.length)
    (hrun : arena.promote.promote_new pers st rm fuel k rf = ok o) :
    SimPM IFEnvRelI pers lst o
      (promoteNew lm (absU fuel) (absU k) lf) :=
  promote_new_refines_keyed hrel hinv hm hfe hfinv sorry hk hrun

/-! ## The axiom census

The eight memo primitives are this file's closed group; `pmemo_get_e` and
`pmemo_set_e` stand for the other six, which are the same proof at another
handle type. -/

/-- info: 'ConRon.Refine2.pmemo_get_e_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pmemo_get_e_refines

/-- info: 'ConRon.Refine2.pmemo_set_e_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pmemo_set_e_refines

/-- info: 'ConRon.Refine2.pmemo_get_n_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pmemo_get_n_refines

/-- info: 'ConRon.Refine2.pmemo_set_ls_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pmemo_set_ls_refines

/-- info: 'ConRon.Refine2.pmemo_empty_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pmemo_empty_refines

/-- info: 'ConRon.Refine2.promoteE_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteE_unfold

/-- info: 'ConRon.Refine2.promoteN_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteN_unfold

/-- info: 'ConRon.Refine2.promote_n_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_n_refines

/-- info: 'ConRon.Refine2.promote_e_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_e_refines

/-- info: 'ConRon.Refine2.promote_ci_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_ci_list_refines

/-- info: 'ConRon.Refine2.promote_decl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_decl_refines

/-- info: 'ConRon.Refine2.promote_vg_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_vg_refines

/-- info: 'ConRon.Refine2.erase_installed_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erase_installed_refines

/-- info: 'ConRon.Refine2.index_promoted_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms index_promoted_refines

/-- info: 'ConRon.Refine2.promote_new_refines_keyed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_new_refines_keyed

/-- info: 'ConRon.Refine2.promote_new_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_new_refines

end ConRon.Refine2
