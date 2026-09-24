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
    ∀ {P t st lst rm lm} (fuel : Std.U64) (h : arena.handle.NIdx),
      fuel.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) → PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absNIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_n t st rm fuel h) lst (promoteN lm n (absNIdx h)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel h hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_n, promoteN]
    lockstep
  | succ k ih =>
    have hnode : ∀ {P t st lst rm lm} (fu : Std.U64) (v : arena.store.NNodeView),
        fu.val = k → NNodeViewWF v → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) →
        PMemoRel rm lm →
        LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absNIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
          (arena.promote.promote_n_node t st rm fu v) lst
          (promoteNNodeSpec lm k (absNNodeView v)) := by
      intro P t st lst rm lm fu v hfu hvwf hP ht hsc hrel hinv hm
      cases v <;> rw [arena.promote.promote_n_node] <;>
        simp only [absNNodeView, promoteNNodeSpec] <;> lockstep
    intro P t st lst rm lm fuel h hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_n, promoteN_unfold]
    lockstep

/-- **`promote_n` ⊑ `promoteN`**, in the judgement shape. -/
@[lockstep] theorem promote_n_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.NIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absNIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_n t st rm fuel h) lst (promoteN lm (absU fuel) (absNIdx h)) :=
  promote_n_aux _ fuel h rfl hP ht hsc hrel hinv hm

/-- `promote_n_node` ⊑ `promoteNNodeSpec`, from the walk at the same fuel. -/
theorem promote_n_node_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absNIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_n_node t st rm fuel v) lst
      (promoteNNodeSpec lm (absU fuel) (absNNodeView v)) := by
  cases v <;> rw [arena.promote.promote_n_node] <;>
    simp only [absNNodeView, promoteNNodeSpec] <;> lockstep

private theorem promote_l_aux (n : Nat) :
    ∀ {P t st lst rm lm} (fuel : Std.U64) (h : arena.handle.LIdx),
      fuel.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) → PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_l t st rm fuel h) lst (promoteL lm n (absLIdx h)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel h hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_l, promoteL]
    lockstep
  | succ k ih =>
    have htwo : ∀ {P t st lst rm lm} (fu : Std.U64) (u v : arena.handle.LIdx),
        fu.val = k → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) → PMemoRel rm lm →
        LST P (fun p w => (PMemoRel p.1.1 w.1 ∧ w.2 = (absLIdx p.1.2.1, absLIdx p.1.2.2)) ∧ p.2.frozen = true) (fun t' => glue t' st)
          (arena.promote.promote_l_two t st rm fu u v) lst
          (promoteLTwo lm k (absLIdx u) (absLIdx v)) := by
      intro P t st lst rm lm fu u v hfu hP ht hsc hrel hinv hm
      rw [arena.promote.promote_l_two, promoteLTwo]
      lockstep
    have hnode : ∀ {P t st lst rm lm} (fu : Std.U64) (v : arena.store.LNodeView),
        fu.val = k → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) → PMemoRel rm lm →
        LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
          (arena.promote.promote_l_node t st rm fu v) lst
          (promoteLNodeSpec lm k (absLNodeView v)) := by
      intro P t st lst rm lm fu v hfu hP ht hsc hrel hinv hm
      cases v <;> rw [arena.promote.promote_l_node] <;>
        simp only [absLNodeView, promoteLNodeSpec] <;> lockstep
    intro P t st lst rm lm fuel h hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_l, promoteL_unfold]
    lockstep

/-- **`promote_l` ⊑ `promoteL`**, in the judgement shape. -/
@[lockstep] theorem promote_l_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.LIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_l t st rm fuel h) lst (promoteL lm (absU fuel) (absLIdx h)) :=
  promote_l_aux _ fuel h rfl hP ht hsc hrel hinv hm

/-- `promote_l_two` ⊑ `promoteLTwo`. -/
@[lockstep] theorem promote_l_two_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (u v : arena.handle.LIdx) :
    LST P (fun p w => (PMemoRel p.1.1 w.1 ∧ w.2 = (absLIdx p.1.2.1, absLIdx p.1.2.2)) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_l_two t st rm fuel u v) lst
      (promoteLTwo lm (absU fuel) (absLIdx u) (absLIdx v)) := by
  rw [arena.promote.promote_l_two, promoteLTwo]
  lockstep

/-- `promote_l_node` ⊑ `promoteLNodeSpec`. -/
theorem promote_l_node_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (v : arena.store.LNodeView) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_l_node t st rm fuel v) lst
      (promoteLNodeSpec lm (absU fuel) (absLNodeView v)) := by
  cases v <;> rw [arena.promote.promote_l_node] <;>
    simp only [absLNodeView, promoteLNodeSpec] <;> lockstep

private theorem promote_l_list_from_aux (n : Nat) :
    ∀ {P t st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.handle.LIdx)
      (i : Std.Usize) (out : alloc.vec.Vec arena.handle.LIdx),
      us.val.length - i.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) →
      PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_l_list_from t st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteL m (absU fuel) u) lm (absLIdxL out)
          ((us.val.drop i.val).map absLIdx)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_l_list_from, vecFrom_nil us absLIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun _ => LS.packT_ok_ok (LS.pure ⟨⟨hm, rfl⟩, ht⟩ hrel hinv))
      (fun hc => absurd hc (by scalar_tac)))
  | succ k ih =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_l_list_from, vecFrom_cons us absLIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_))
    lockstep

/-- `promote_l_list_from` ⊑ `pmapFrom promoteL` — the cursor, in the judgement
shape. -/
@[lockstep] theorem promote_l_list_from_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.LIdx) (i : Std.Usize)
    (out : alloc.vec.Vec arena.handle.LIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_l_list_from t st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteL m (absU fuel) u) lm (absLIdxL out)
        ((us.val.drop i.val).map absLIdx)) :=
  promote_l_list_from_aux _ fuel us i out rfl hP ht hsc hrel hinv hm

theorem promoteLList_pmapFrom (m : PMemo) (fuel : Nat) (l : List LIdx) (acc : List LIdx) :
    pmapFrom (fun m u => promoteL m fuel u) m acc l =
      (do let (m, ys) ← promoteLList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteLList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_l_list` ⊑ `promoteLList`. -/
@[lockstep] theorem promote_l_list_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.LIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_l_list t st rm fuel us) lst
      (promoteLList lm (absU fuel) (absLIdxL us)) := by
  have h := promote_l_list_from_ls hP ht hsc hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteLList_pmapFrom] at h
  simpa [arena.promote.promote_l_list, absLIdxL, alloc.vec.Vec.new] using h

/-- **`promote_ls` ⊑ `promoteLs`** — no fuel clause on either side. -/
@[lockstep] theorem promote_ls_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.LsIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absLsIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_ls t st rm fuel h) lst
      (promoteLs lm (absU fuel) (absLsIdx h)) := by
  rw [arena.promote.promote_ls, promoteLs]
  lockstep

private theorem promote_e_aux (n : Nat) :
    ∀ {P t st lst rm lm} (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) → PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absEIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_e t st rm fuel h) lst (promoteE lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel h hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_e, promoteE]
    lockstep
  | succ k ih =>
    have htwo : ∀ {P t st lst rm lm} (fu : Std.U64) (x y : arena.handle.EIdx),
        fu.val = k → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) → PMemoRel rm lm →
        LST P (fun p w => (PMemoRel p.1.1 w.1 ∧ w.2 = (absEIdx p.1.2.1, absEIdx p.1.2.2)) ∧ p.2.frozen = true) (fun t' => glue t' st)
          (arena.promote.promote_e_two t st rm fu x y) lst
          (promoteETwo lm k (absEIdx x) (absEIdx y)) := by
      intro P t st lst rm lm fu x y hfu hP ht hsc hrel hinv hm
      rw [arena.promote.promote_e_two, promoteETwo]
      lockstep
    have hnode : ∀ {P t st lst rm lm} (fu : Std.U64) (v : arena.store.ENodeView),
        fu.val = k → ENodeViewWF v → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) →
        PMemoRel rm lm →
        LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absEIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
          (arena.promote.promote_e_node t st rm fu v) lst
          (promoteENodeSpec lm k (absENodeView v)) := by
      intro P t st lst rm lm fu v hfu hvwf hP ht hsc hrel hinv hm
      cases v <;> rw [arena.promote.promote_e_node] <;>
        simp only [absENodeView, promoteENodeSpec] <;> lockstep
    intro P t st lst rm lm fuel h hn hP ht hsc hrel hinv hm
    have hV := @view_wf_ls
    rw [arena.promote.promote_e, promoteE_unfold]
    lockstep

/-- **`promote_e` ⊑ `promoteE`**, in the judgement shape. -/
@[lockstep] theorem promote_e_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absEIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_e t st rm fuel h) lst (promoteE lm (absU fuel) (absEIdx h)) :=
  promote_e_aux _ fuel h rfl hP ht hsc hrel hinv hm

/-- `promote_e_two` ⊑ `promoteETwo`. -/
@[lockstep] theorem promote_e_two_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (x y : arena.handle.EIdx) :
    LST P (fun p w => (PMemoRel p.1.1 w.1 ∧ w.2 = (absEIdx p.1.2.1, absEIdx p.1.2.2)) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_e_two t st rm fuel x y) lst
      (promoteETwo lm (absU fuel) (absEIdx x) (absEIdx y)) := by
  rw [arena.promote.promote_e_two, promoteETwo]
  lockstep

/-- `promote_e_node` ⊑ `promoteENodeSpec`. -/
theorem promote_e_node_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (v : arena.store.ENodeView) (hvwf : ENodeViewWF v) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absEIdx p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_e_node t st rm fuel v) lst
      (promoteENodeSpec lm (absU fuel) (absENodeView v)) := by
  cases v <;> rw [arena.promote.promote_e_node] <;>
    simp only [absENodeView, promoteENodeSpec] <;> lockstep

private theorem promote_n_list_from_aux (n : Nat) :
    ∀ {P t st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.handle.NIdx)
      (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx),
      us.val.length - i.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) →
      PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absNIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_n_list_from t st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteN m (absU fuel) u) lm (absNIdxL out)
          ((us.val.drop i.val).map absNIdx)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_n_list_from, vecFrom_nil us absNIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun _ => LS.packT_ok_ok (LS.pure ⟨⟨hm, rfl⟩, ht⟩ hrel hinv))
      (fun hc => absurd hc (by scalar_tac)))
  | succ k ih =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_n_list_from, vecFrom_cons us absNIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_))
    lockstep

/-- `promote_n_list_from` ⊑ `pmapFrom promoteN` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_n_list_from_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absNIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_n_list_from t st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteN m (absU fuel) u) lm (absNIdxL out)
        ((us.val.drop i.val).map absNIdx)) :=
  promote_n_list_from_aux _ fuel us i out rfl hP ht hsc hrel hinv hm

theorem promoteNList_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteN m fuel u) m acc l =
      (do let (m, ys) ← promoteNList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteNList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_n_list` ⊑ `promoteNList`. -/
@[lockstep] theorem promote_n_list_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.NIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absNIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_n_list t st rm fuel us) lst
      (promoteNList lm (absU fuel) (absNIdxL us)) := by
  have h := promote_n_list_from_ls hP ht hsc hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteNList_pmapFrom] at h
  simpa [arena.promote.promote_n_list, absNIdxL, alloc.vec.Vec.new] using h

private theorem promote_e_list_from_aux (n : Nat) :
    ∀ {P t st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.handle.EIdx)
      (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx),
      us.val.length - i.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) →
      PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absEIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_e_list_from t st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteE m (absU fuel) u) lm (absEIdxL out)
          ((us.val.drop i.val).map absEIdx)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_e_list_from, vecFrom_nil us absEIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun _ => LS.packT_ok_ok (LS.pure ⟨⟨hm, rfl⟩, ht⟩ hrel hinv))
      (fun hc => absurd hc (by scalar_tac)))
  | succ k ih =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_e_list_from, vecFrom_cons us absEIdx i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_))
    lockstep

/-- `promote_e_list_from` ⊑ `pmapFrom promoteE` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_e_list_from_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absEIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_e_list_from t st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteE m (absU fuel) u) lm (absEIdxL out)
        ((us.val.drop i.val).map absEIdx)) :=
  promote_e_list_from_aux _ fuel us i out rfl hP ht hsc hrel hinv hm

theorem promoteEList_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteE m fuel u) m acc l =
      (do let (m, ys) ← promoteEList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteEList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_e_list` ⊑ `promoteEList`. -/
@[lockstep] theorem promote_e_list_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.handle.EIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absEIdxL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_e_list t st rm fuel us) lst
      (promoteEList lm (absU fuel) (absEIdxL us)) := by
  have h := promote_e_list_from_ls hP ht hsc hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteEList_pmapFrom] at h
  simpa [arena.promote.promote_e_list, absEIdxL, alloc.vec.Vec.new] using h


/-! ### The declaration layer -/

section decl
attribute [local lockstep_simp] absIConstantVal absIRecRuleFire absIRecRule absIIndCaps
  absIProjTable absIConstantInfo absIDeclaration absIRecRuleL absICIL

/-- `promote_cv` ⊑ `promoteCV`. -/
@[lockstep] theorem promote_cv_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (cv : arena.env.IConstantVal) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIConstantVal p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_cv t st rm fuel cv) lst
      (promoteCV lm (absU fuel) (absIConstantVal cv)) := by
  rw [arena.promote.promote_cv, promoteCV]
  lockstep

/-- `promote_fire` ⊑ `promoteFire`. -/
@[lockstep] theorem promote_fire_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (f : arena.env.IRecRuleFire) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIRecRuleFire p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_fire t st rm fuel f) lst
      (promoteFire lm (absU fuel) (absIRecRuleFire f)) := by
  cases f <;> rw [arena.promote.promote_fire] <;> simp only [absIRecRuleFire, promoteFire] <;>
    lockstep

/-- `promote_rule` ⊑ `promoteRule`. -/
@[lockstep] theorem promote_rule_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (rl : arena.env.IRecRule) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIRecRule p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_rule t st rm fuel rl) lst
      (promoteRule lm (absU fuel) (absIRecRule rl)) := by
  rw [arena.promote.promote_rule, promoteRule]
  lockstep

/-- `promote_caps` ⊑ `promoteCaps`. -/
@[lockstep] theorem promote_caps_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (c : arena.env.IIndCaps) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIIndCaps p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_caps t st rm fuel c) lst
      (promoteCaps lm (absU fuel) (absIIndCaps c)) := by
  rw [arena.promote.promote_caps, promoteCaps]
  lockstep

end decl

private theorem promote_rules_from_aux (n : Nat) :
    ∀ {P t st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.env.IRecRule)
      (i : Std.Usize) (out : alloc.vec.Vec arena.env.IRecRule),
      us.val.length - i.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) →
      PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIRecRuleL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_rules_from t st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteRule m (absU fuel) u) lm (absIRecRuleL out)
          ((us.val.drop i.val).map absIRecRule)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_rules_from, vecFrom_nil us absIRecRule i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun _ => LS.packT_ok_ok (LS.pure ⟨⟨hm, rfl⟩, ht⟩ hrel hinv))
      (fun hc => absurd hc (by scalar_tac)))
  | succ k ih =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_rules_from, vecFrom_cons us absIRecRule i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_))
    lockstep

/-- `promote_rules_from` ⊑ `pmapFrom promoteRule` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_rules_from_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IRecRule) (i : Std.Usize) (out : alloc.vec.Vec arena.env.IRecRule) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIRecRuleL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_rules_from t st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteRule m (absU fuel) u) lm (absIRecRuleL out)
        ((us.val.drop i.val).map absIRecRule)) :=
  promote_rules_from_aux _ fuel us i out rfl hP ht hsc hrel hinv hm

theorem promoteRules_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteRule m fuel u) m acc l =
      (do let (m, ys) ← promoteRules m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteRules m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_rules` ⊑ `promoteRules`. -/
@[lockstep] theorem promote_rules_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IRecRule) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIRecRuleL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_rules t st rm fuel us) lst
      (promoteRules lm (absU fuel) (absIRecRuleL us)) := by
  have h := promote_rules_from_ls hP ht hsc hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
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
@[lockstep] theorem promote_proj_table_rest_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (pt : arena.env.IProjTable) (sn tn : arena.handle.NIdx)
    (lps : alloc.vec.Vec arena.handle.NIdx) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIProjTable p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_proj_table_rest t st rm fuel pt sn tn lps) lst
      (promoteProjTableRest lm (absU fuel) (absIProjTable pt) (absNIdx sn) (absNIdx tn)
        (absNIdxL lps)) := by
  rw [arena.promote.promote_proj_table_rest, promoteProjTableRest]
  lockstep

/-- `promote_proj_table` ⊑ `promoteProjTable`. -/
@[lockstep] theorem promote_proj_table_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (pt : arena.env.IProjTable) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIProjTable p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_proj_table t st rm fuel pt) lst
      (promoteProjTable lm (absU fuel) (absIProjTable pt)) := by
  rw [arena.promote.promote_proj_table, promoteProjTable_rest]
  lockstep
  all_goals (try simp only [Aeneas.Std.uncurry]); all_goals (try dsimp only)
  all_goals lockstep

/-- `promote_ci` ⊑ `promoteCI` — the seven constructors. -/
@[lockstep] theorem promote_ci_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (ci : arena.env.IConstantInfo) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIConstantInfo p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_ci t st rm fuel ci) lst
      (promoteCI lm (absU fuel) (absIConstantInfo ci)) := by
  cases ci <;> rw [arena.promote.promote_ci] <;> simp only [absIConstantInfo, promoteCI] <;>
    lockstep

end decl2

private theorem promote_ci_list_from_aux (n : Nat) :
    ∀ {P t st lst rm lm} (fuel : Std.U64) (us : alloc.vec.Vec arena.env.IConstantInfo)
      (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantInfo),
      us.val.length - i.val = n → P.frozen = false → t.frozen = true → ScratchOn st.store →
        AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) →
      PMemoRel rm lm →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absICIL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
        (arena.promote.promote_ci_list_from t st rm fuel us i out) lst
        (pmapFrom (fun m u => promoteCI m (absU fuel) u) lm (absICIL out)
          ((us.val.drop i.val).map absIConstantInfo)) := by
  induction n with
  | zero =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_ci_list_from, vecFrom_nil us absIConstantInfo i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun _ => LS.packT_ok_ok (LS.pure ⟨⟨hm, rfl⟩, ht⟩ hrel hinv))
      (fun hc => absurd hc (by scalar_tac)))
  | succ k ih =>
    intro P t st lst rm lm fuel us i out hn hP ht hsc hrel hinv hm
    rw [arena.promote.promote_ci_list_from, vecFrom_cons us absIConstantInfo i (by omega), pmapFrom]
    have hl := alloc.vec.Vec.len_val us
    refine LS.packT_ite (LS.ite (fun hc => absurd hc (by scalar_tac)) (fun hc => ?_))
    lockstep

/-- `promote_ci_list_from` ⊑ `pmapFrom promoteCI` — the cursor, in the judgement shape. -/
@[lockstep] theorem promote_ci_list_from_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IConstantInfo) (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantInfo) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absICIL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_ci_list_from t st rm fuel us i out) lst
      (pmapFrom (fun m u => promoteCI m (absU fuel) u) lm (absICIL out)
        ((us.val.drop i.val).map absIConstantInfo)) :=
  promote_ci_list_from_aux _ fuel us i out rfl hP ht hsc hrel hinv hm

theorem promoteCIList_pmapFrom (m : PMemo) (fuel : Nat) l acc :
    pmapFrom (fun m u => promoteCI m fuel u) m acc l =
      (do let (m, ys) ← promoteCIList m fuel l; pure (m, acc ++ ys)) :=
  pmapFrom_cons_eq _ (fun m l => promoteCIList m fuel l) (fun _ => rfl) (fun _ _ _ => rfl) l m acc

/-- `promote_ci_list` ⊑ `promoteCIList`. -/
@[lockstep] theorem promote_ci_list_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (us : alloc.vec.Vec arena.env.IConstantInfo) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absICIL p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_ci_list t st rm fuel us) lst
      (promoteCIList lm (absU fuel) (absICIL us)) := by
  have h := promote_ci_list_from_ls hP ht hsc hrel hinv hm fuel us 0#usize (alloc.vec.Vec.new _)
  rw [promoteCIList_pmapFrom] at h
  simpa [arena.promote.promote_ci_list, absICIL, alloc.vec.Vec.new] using h


section decl3
attribute [local lockstep_simp] absIConstantVal absIDeclaration absICIL

/-- `promote_decl` ⊑ `promoteDecl` — the seven constructors. -/
@[lockstep] theorem promote_decl_ls {P t st lst rm lm} (hP : P.frozen = false) (ht : t.frozen = true)
    (hsc : ScratchOn st.store) (hrel : AStateRel₀ P (glue t st) lst)
    (hinv : AStateInv P (glue t st)) (hm : PMemoRel rm lm) (fuel : Std.U64)
    (d : arena.env.IDeclaration) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absIDeclaration p.1.2) ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.promote.promote_decl t st rm fuel d) lst
      (promoteDecl lm (absU fuel) (absIDeclaration d)) := by
  cases d <;> rw [arena.promote.promote_decl] <;> simp only [absIDeclaration, promoteDecl] <;>
    lockstep

end decl3

end Lockstep

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
  refine ⟨⟨?_, ?_, ?_, by rw [he]; exact hfe.envWF, fun k p hp => ?_⟩, hI⟩
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
  · -- the keys: `erase_installed` only removes rows
    rw [hidx k] at hp
    split at hp
    · cases hp
    · obtain ⟨c, hc, hcn⟩ := hfe.keys k p hp
      exact ⟨c, by rw [he]; exact hc, hcn⟩

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

theorem reverse_set' {α : Type} (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    (l.set i x).reverse = l.reverse.set (l.length - 1 - i) x := by
  apply List.ext_getElem (by simp)
  intro q h1 h2
  simp only [List.length_reverse, List.length_set] at h1 h2
  simp only [List.getElem_reverse, List.getElem_set, List.length_set, List.length_reverse]
  split_ifs <;> first | rfl | omega

/-- **`promote_ci` keeps a constant canonical** (`IConstantInfoWF`): the one
datum the predicate reads, an inductive's `caps.sort_z`, is copied by
`i_ind_caps_dup` (the identity) and never promoted.  A fact about the Rust
program alone; `index_promoted` writes back the promotion of a constant it
read out of the related environment, so `IFEnvRel.envWF` of the source gives
the premise (task #97-T2-LANE-Promote round 2, replacing the seam
`ifenvRel_envWF_promote`). -/
theorem promote_ci_wf {t st m fuel} {ci : arena.env.IConstantInfo} {m2 ci' t'}
    (hwf : IConstantInfoWF ci)
    (h : arena.promote.promote_ci t st m fuel ci = ok (.Ok (m2, ci'), t')) :
    IConstantInfoWF ci' := by
  cases ci with
  | IndInfo v c =>
    rw [arena.promote.promote_ci] at h
    obtain ⟨⟨r, st1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok p =>
      obtain ⟨⟨r2, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases r2 with
      | Err e => cases Result.ok_injective h
      | Ok p2 =>
        cases Result.ok_injective h
        rw [arena.promote.promote_caps] at h2
        obtain ⟨⟨r3, st3⟩, -, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
        cases r3 with
        | Err e => cases Result.ok_injective h2
        | Ok p3 =>
          obtain ⟨caps, hcaps, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
          cases Result.ok_injective h2
          cases Lockstep.i_ind_caps_dup_spec c caps hcaps
          exact hwf
  | _ =>
    rw [arena.promote.promote_ci] at h
    repeat (first
      | (obtain ⟨⟨_r, _st⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; cases _r <;>
          try (cases Result.ok_injective h; done))
      | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h))
    all_goals (cases Result.ok_injective h; trivial)

/-- A Rust-output fact joined to a tier walk's lockstep post (the fact is read
off the Rust run alone). -/
private theorem LST.and_rust {α β : Type} {P0 : arena.store.PersTier}
    {R : α × arena.store.PersTier → β → Prop} {Q : α → Prop}
    {G : arena.store.PersTier → arena.monad.AState}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.PersTier)}
    {lst : AState} {x : AM β}
    (h : Lockstep.LST P0 R G m lst x) (hQ : ∀ a t', m = ok (.Ok a, t') → Q a) :
    Lockstep.LST P0 (fun p b => R p b ∧ Q p.1) G m lst x := by
  intro o st' hm
  obtain ⟨⟨r, t'⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hh := Lockstep.LST.apply h h1
  have h2' := Result.ok_injective h2
  cases r with
  | Err e =>
    simp only [Lockstep.packTOut, Prod.mk.injEq] at h2'
    obtain ⟨rfl, rfl⟩ := h2'
    exact hh
  | Ok a =>
    simp only [Lockstep.packTOut, Prod.mk.injEq] at h2'
    obtain ⟨rfl, rfl⟩ := h2'
    obtain ⟨b, lst', h3, h4, h5, h6⟩ := hh
    exact ⟨b, lst', h3, ⟨h4, hQ a t' h1⟩, h5, h6⟩

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
    (hciwf : IConstantInfoWF ci)
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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨hinvm, ?_, ?_⟩, hlen, ?_⟩
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
  · -- the stored constants stay canonical: the old ones by `hfe`, the
    -- promoted one by `hciwf` (the promotion of a stored constant, `promote_ci_wf`)
    intro c' hc'
    simp only [rf', alloc.vec.Vec.set_val_eq] at hc'
    rcases List.mem_or_eq_of_mem_set hc' with h | h
    · exact hfe.envWF c' h
    · rw [h]; exact hciwf
  · -- the keys: the new row by the promoted constant's name, the old rows
    -- point outside `start..j` and so at unmoved slots
    intro k p hp
    simp only [rf'] at hp
    rw [hupd, Function.update_apply] at hp
    split at hp
    · rename_i hk
      subst hk
      cases hp
      refine ⟨ci, ?_, hnn.symm⟩
      rw [hget, hi2, if_pos rfl, if_pos hil]
    · obtain ⟨c'', hc'', hcn⟩ := hfe.keys k p hp
      refine ⟨c'', ?_, hcn⟩
      rw [hget, if_neg (by rcases hfree k p hp with h | h <;> omega)]
      exact hc''
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
    ∀ {P t st lst rm lm rf lf} (fuel : Std.U64) (start j : Std.Usize) (c : Std.U64),
      j.val - start.val = d → start.val ≤ j.val → j.val ≤ rf.env.consts.val.length →
      P.frozen = false → t.frozen = true → ScratchOn st.store →
      AStateRel₀ P (glue t st) lst → AStateInv P (glue t st) → PMemoRel rm lm →
      IFEnvRel rf lf → IFEnvInv rf →
      (∀ k p, ConRon.Refine.HashMap2.toFun rf.idx k = some p →
        p.2.val < start.val ∨ j.val ≤ p.2.val) →
      LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ IFEnvRelI p.1.2 v.2) ∧ p.2.frozen = true)
        (fun t' => glue t' st)
        (arena.promote.index_promoted t st rm fuel rf start j c) lst
        (indexPromotedTwin lm (absU fuel) lf.env.consts lf.idx lf.visibleBelow
          rf.env.consts.val.length start.val j.val (absU c)) := by
  induction d with
  | zero =>
    intro P t st lst rm lm rf lf fuel start j c hd hle hj hP ht hsc hrel hinv hm hfe hfinv
      hfree
    have hje : j.val = start.val := by omega
    show LS _ _ (packT _ _) _ _
    rw [arena.promote.index_promoted, if_pos (by scalar_tac), hje, indexPromotedTwin_zero]
    exact LS.packT_ok_ok (LS.pure ⟨⟨hm, hfe, hfinv⟩, ht⟩ hrel hinv)
  | succ d ih =>
    intro P t st lst rm lm rf lf fuel start j c hd hle hj hP ht hsc hrel hinv hm hfe hfinv
      hfree
    have hsj : start.val < j.val := by omega
    have hlen : lf.env.consts.length = rf.env.consts.val.length := by
      rw [hfe.env]; simp [absIEnv]
    show LS _ _ (packT _ _) _ _
    rw [arena.promote.index_promoted, if_neg (by scalar_tac),
      indexPromotedTwin_succ _ _ _ _ _ _ _ _ _ hlen hsj hj]
    refine LS.packT_bind (LS.bind_eq fun i hi => ?_)
    obtain ⟨-, hi1⟩ := ConRon.Refine.Nat.usub_val hi
    have hiv : i.val = j.val - 1 := by rw [hi1]; rfl
    refine LS.packT_bind (LS.bind_eq fun ii hii => ?_)
    obtain ⟨hb, hii⟩ := ExprOps.vecIndexAt hii
    have htw : absIConstantInfo ii =
        lf.env.consts[rf.env.consts.val.length - j.val]'(by omega) := by
      simp only [hfe.env, absIEnv, List.getElem_reverse, List.getElem_map, List.length_map]
      rw [← hii]
      have e : rf.env.consts.val.length - 1 - (rf.env.consts.val.length - j.val) = i.val := by
        omega
      simp only [e]
    -- the promoted constant is canonical: `ii` is stored in the related source
    have hiiwf : IConstantInfoWF ii :=
      hfe.envWF ii (by rw [← hii]; exact List.getElem_mem _)
    refine LS.packT_bind (LS.bindT (LST.and_rust (promote_ci_ls hP ht hsc hrel hinv hm fuel ii)
        (Q := fun r => IConstantInfoWF r.2)
        (fun a t' h => promote_ci_wf hiiwf h)) (by rw [htw]) ?_ ?_)
    · intro e t1
      exact ErrArm.packT_ok_err
    · rintro ⟨m2, ci⟩ t1 ⟨m2', ci'⟩ lst1 ⟨⟨⟨hM, hci⟩, hf1⟩, hciwf⟩ hrel1 hinv1
      simp only at hM hci hciwf hf1
      subst hci
      try dsimp only
      refine LS.packT_bind (LS.bind_eq fun nn hnn => ?_)
      have hnn' := i_constant_info_name_abs hnn
      refine LS.packT_bind (LS.bind_eq fun i1 hi1' => ?_)
      obtain ⟨hc1, hi1v⟩ := ConRon.Refine.Nat.usub_val hi1'
      refine LS.packT_bind (LS.bind_eq fun i2 hi2 => ?_)
      have hi2v : i2.val = i.val := by
        simp only [lift, Result.ok.injEq] at hi2
        rw [← hi2, usize_cast_u64_val]
      refine LS.packT_bind (LS.bind_eq fun q hq => ?_)
      obtain ⟨old, hmm⟩ := q
      obtain ⟨hinvm, -, hupd, -⟩ :=
        ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True) nidx_eq2
          hfinv.idxInv ConRon.Refine.HashMap2.KeysOk_true trivial hq
      try dsimp only
      refine LS.packT_bind (LS.bind_eq fun q2 hq2 => ?_)
      obtain ⟨x, back⟩ := q2
      haveI : Inhabited arena.env.IConstantInfo := ⟨ci⟩
      obtain ⟨-, -, hback⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq2
      subst hback
      try dsimp only
      obtain ⟨hrel', hinv', hlen', hfree'⟩ := index_promoted_step (i := i) (ci := ci) (nn := nn)
        (c := c) (i1 := i1) (i2 := i2) hfe hfinv hfree hsj hj hiv hi1v (by
          rw [u64_one_val] at hc1; exact hc1) hi2v hnn' hciwf hinvm hupd
      have hrec := ih fuel start i i1 (by omega) (by omega) (by rw [hlen']; omega)
          hP hf1 hsc hrel1 hinv1 hM hrel' hinv' hfree'
      rw [hlen'] at hrec
      refine LS.tailT hrec ?_ (fun _ _ h => h)
      simp only [hiv, show absU i1 = absU c - 1 from hi1v]

open Lockstep in
/-- `index_promoted` ⊑ `promoteCIList` followed by `indexPromoted`, on the
slice `start..j` (finding B: the port fuses the two passes, which promotion
reading no index makes invisible).  The promoted records are written back
into their own slots, so the environment's shape is unchanged and only the
middle segment moves.

`hfree` — *no index row points into the slice* — is the Rust-side fact the
statement needs (`IFEnvKeys`' note): a row pointing at a slot of the slice
would move with the overwrite, and the twin's row (keyed by name) would not.
`promote_new` establishes it from `IFEnvKeys` and `erase_installed`. -/
theorem index_promoted_ls {P t st lst rm lm rf lf} {fuel : Std.U64}
    {start j : Std.Usize} {c : Std.U64}
    (hP : P.frozen = false) (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hle : start.val ≤ j.val) (hj : j.val ≤ rf.env.consts.val.length)
    (hfree : ∀ k p, ConRon.Refine.HashMap2.toFun rf.idx k = some p →
      p.2.val < start.val ∨ j.val ≤ p.2.val) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ IFEnvRelI p.1.2 v.2) ∧ p.2.frozen = true)
      (fun t' => glue t' st)
      (arena.promote.index_promoted t st rm fuel rf start j c) lst
      (indexPromotedTwin lm (absU fuel) (absIEnv rf.env).consts lf.idx lf.visibleBelow
        rf.env.consts.val.length start.val j.val (absU c)) := by
  have h := index_promoted_aux _ fuel start j c rfl hle hj hP ht hsc hrel hinv hm hfe hfinv
    hfree
  rw [hfe.env] at h
  exact h

open Lockstep in
/-- **`promote_new` ⊑ `promoteNew`** — the phase-A bracket's promotion half:
the `k` constants the step just installed, copied into the persistent tier and
re-indexed, everything below them untouched.  `hk` is finding C.  A TIER walk
(task #98-FREEZE): the frozen state is read, the bracket's tier is written,
and the relation after it is the glued state's at the grown tier, which is
still `frozen`.

**The result relation is `IFEnvRelI`, not `IFEnvRel`** (task #97-P5-Checker
round 4): both bracketed steps of `Refine2/Checker/Top.lean` hand
`promote_new`'s environment to the NEXT step of their fold, which takes
`IFEnvInv` beside `IFEnvRel` (task #97-P5-Checker-2 §3's `IFEnvRelI`). -/
theorem promote_new_ls_keyed {P t st lst rm lm rf lf} {fuel k : Std.U64}
    (hP : P.frozen = false) (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hkeys : IFEnvKeys rf)
    (hk : absU k ≤ rf.env.consts.val.length) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ IFEnvRelI p.1.2 v.2) ∧ p.2.frozen = true)
      (fun t' => glue t' st)
      (arena.promote.promote_new t st rm fuel k rf) lst
      (promoteNew lm (absU fuel) (absU k) lf) := by
  show LS _ _ (packT _ _) _ _
  rw [arena.promote.promote_new]
  by_cases hk0 : k = 0#u64
  · rw [if_pos hk0]
    have h0 : absU k = 0 := by rw [hk0]; rfl
    rw [promoteNew, h0]
    exact LS.packT_ok_ok (LS.pure ⟨⟨hm, hfe, hfinv⟩, ht⟩ hrel hinv)
  · rw [if_neg hk0]
    have hn := alloc.vec.Vec.len_val rf.env.consts
    refine LS.packT_bind (LS.bind_eq fun kk hkk => ?_)
    have hkkv : kk.val = k.val := by
      simp only [lift, Result.ok.injEq] at hkk
      rw [← hkk]
      have hkb : k.val ≤ Std.Usize.max := le_trans hk rf.env.consts.property
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      scalar_tac
    have hkle : ¬ kk > alloc.vec.Vec.len rf.env.consts := by
      have : absU k = k.val := rfl
      scalar_tac
    refine LS.packT_ite (LS.ite (fun h => absurd h hkle) (fun _ => ?_))
    refine LS.packT_bind (LS.bind_eq fun start hstart => ?_)
    have hsv : start.val = rf.env.consts.val.length - k.val := by
      have := ConRon.Refine.HashMap.uscalar_sub_eq hstart
      scalar_tac
    refine LS.packT_bind (LS.bind_eq fun fe2 hfe2 => ?_)
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
    have hI := index_promoted_ls (fuel := fuel) (c := rf.visible_below) hP ht hsc hrel hinv hm hR2 hI2
      (by scalar_tac) (by rw [hlen]; scalar_tac) hfree
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
    exact LS.tailT hI htw (fun _ _ h => h)

open Lockstep in
/-- **`promote_new` ⊑ `promoteNew`, as the checker tier consumes it** — the
key clause is `IFEnvRel.keys` since task #97-P5-Core round 5. -/
theorem promote_new_ls {P t st lst rm lm rf lf} {fuel k : Std.U64}
    (hP : P.frozen = false) (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hk : absU k ≤ rf.env.consts.val.length) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ IFEnvRelI p.1.2 v.2) ∧ p.2.frozen = true)
      (fun t' => glue t' st)
      (arena.promote.promote_new t st rm fuel k rf) lst
      (promoteNew lm (absU fuel) (absU k) lf) :=
  promote_new_ls_keyed hP ht hsc hrel hinv hm hfe hfinv hfe.keys hk

open Lockstep in
/-- `promote_vg` ⊑ `promoteVG` — the datum that crosses the install/check
seam, promoted beside the environment and at the SAME memo (an `opaque`'s
value is not in the environment; only the pending record holds it). -/
theorem promote_vg_ls {P t st lst rm lm} {fuel : Std.U64}
    (hP : P.frozen = false) (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (hm : PMemoRel rm lm) (g : arena.checker_split.ValueGroup) :
    LST P (fun p v => (PMemoRel p.1.1 v.1 ∧ v.2 = absValueGroup p.1.2) ∧ p.2.frozen = true)
      (fun t' => glue t' st)
      (arena.promote.promote_vg t st rm fuel g) lst
      (promoteVG lm (absU fuel) (absValueGroup g)) := by
  rw [arena.promote.promote_vg, promoteVG]
  lockstep

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

/-- info: 'ConRon.Refine2.Lockstep.promote_n_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lockstep.promote_n_ls

/-- info: 'ConRon.Refine2.Lockstep.promote_e_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lockstep.promote_e_ls

/-- info: 'ConRon.Refine2.Lockstep.promote_ci_list_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lockstep.promote_ci_list_ls

/-- info: 'ConRon.Refine2.Lockstep.promote_decl_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lockstep.promote_decl_ls

/-- info: 'ConRon.Refine2.promote_vg_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_vg_ls

/-- info: 'ConRon.Refine2.erase_installed_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erase_installed_refines

/-- info: 'ConRon.Refine2.index_promoted_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms index_promoted_ls

/-- info: 'ConRon.Refine2.promote_new_ls_keyed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_new_ls_keyed

/-- info: 'ConRon.Refine2.promote_new_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_new_ls

end ConRon.Refine2
