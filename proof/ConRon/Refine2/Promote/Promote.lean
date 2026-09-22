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

`promote_{n,l,e}_node`, `promote_{l,e}_two` and the four `_from` cursor
companions have no twin of their own — they are task #97-P6-2's extraction
rule 5 ("a `view`'s loans must be dead at the memo's join") and DESIGN §3.4's
standing `List`-as-cursor deviation.  The `_node` three are stated against a
LOCAL TRANSCRIPTION of the twin's own arms (`promote{N,L,E}NodeSpec` below)
plus an `_unfold` equation back to the twin, which is the shape
`Refine2/ExprOps/Read.lean` wrote for `wscopedBGo`; the `_two` two and the
`_from` four are stated against the twin's arm inline.

## Three findings, all of them about `promote_new`

They are in the section note there.

## What these lemmas wait on

`Refine2/Specs.lean`'s `intern_persistent_{e,n,l,ls}` — the four persistent
interns, among task #97-P5-1 §8's thirty-two still open — and `view`,
`view_n`, `view_l`, `view_ls`, which are closed.  The shape step is the fuel
peel of task #97-P5-0's rule 3 at `promote{N,L,E}` and a `Vec`-cursor measure
induction at the four `_from` companions.
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

/-- `Refine2/Specs.lean`'s `view_run_state` at the NAME store: `viewN` is a
READER, so the existential post-state of its `AOut` collapses.  It belongs
beside its expression sibling and is here only because this tier may not edit
that file. -/
private theorem viewN_run_state {lst lst' : AState} {hh : NIdx} {v : NNodeView}
    (h : (Arena.viewN hh).run lst = .ok (v, lst')) : lst' = lst := by
  rw [show (Arena.viewN hh).run lst
      = (match lst.store.ns.view hh with
         | some w => Except.ok (w, lst)
         | none => Except.error (Arena.CheckError.internal
             "arena: dangling name handle")) by
    show ((match lst.store.ns.view hh with
            | some w => (pure w : AM NNodeView)
            | none => Arena.fail
                (.internal "arena: dangling name handle")).run lst) = _
    cases lst.store.ns.view hh <;> rfl] at h
  split at h
  · exact (congrArg Prod.snd (Except.ok.inj h)).symm
  · exact absurd h (by simp)

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

/-- `promoteL`'s five arms past the probe. -/
def promoteLNodeSpec (m : PMemo) (fuel : Nat) : LNodeView → AM (PMemo × LIdx)
  | .zero => do pure (m, ← internPersistentL .zero)
  | .succ u => do
    let (m, u) ← promoteL m fuel u
    pure (m, ← internPersistentL (.succ u))
  | .max u v => do
    let (m, u) ← promoteL m fuel u
    let (m, v) ← promoteL m fuel v
    pure (m, ← internPersistentL (.max u v))
  | .imax u v => do
    let (m, u) ← promoteL m fuel u
    let (m, v) ← promoteL m fuel v
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
    let (m, f) ← promoteE m fuel f
    let (m, a) ← promoteE m fuel a
    pure (m, ← internPersistentE (.app f a))
  | .lam ty body bm => do
    let (m, ty) ← promoteE m fuel ty
    let (m, body) ← promoteE m fuel body
    pure (m, ← internPersistentE (.lam ty body bm))
  | .forallE ty body bm => do
    let (m, ty) ← promoteE m fuel ty
    let (m, body) ← promoteE m fuel body
    pure (m, ← internPersistentE (.forallE ty body bm))
  | .letE ty val body => do
    let (m, ty) ← promoteE m fuel ty
    let (m, val) ← promoteE m fuel val
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
      cases v <;> twin_reduce [promoteLNodeSpec]

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
      cases v <;> twin_reduce [promoteENodeSpec]

/-! ## The four handle kinds

**Task #97-P5-Checker-2 closes the NAME walk, and it is the template for the
other three.**  `promote_n` and `promote_n_node` are ONE `partial_fixpoint`
block and one induction: `promote_n` at `f + 1` calls `promote_n_node` at `f`,
and `promote_n_node` at `f` calls `promote_n` at `f` — so the node lemma is
derived INSIDE the successor step from that step's own induction hypothesis
and needs no second induction.  Everything else is task #97-P5-2 §6's idiom
with `absU fuel = n` generalised.

What it rests on: `Refine2/Specs.lean`'s `intern_persistent_n_run` (still
open, and named rather than re-proved), `view_n_run`, `nidx_is_persistent_abs`
and this file's own `pmemo_{get,set}_n_refines`.  **`Ext` comes out of the
composition** — every step's `AOut`/`POut` carries one and `Ext.trans` chains
them — so `Arena/PromoteExt.lean`'s `promoteN_ext` is not needed here; it is
needed where a walk's `Ext` has to be produced WITHOUT decomposing it, which
is `Bridge/Promote/Exact.lean`'s business. -/

/-- The name walk, by the fuel's measure; `promote_n_node` derived inside the
successor step. -/
/-- `promote_n_node` at the fuel `promote_n` calls it with, from that call's
own induction hypothesis — the mutual block's second half, which needs no
induction of its own. -/
private theorem promote_n_node_aux (n : Nat)
    (ih : ∀ {pers st lst rm lm} {fuel : Std.U64} {h : arena.handle.NIdx} {o},
      absU fuel = n → AStateRel pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      arena.promote.promote_n pers st rm fuel h = ok o →
      SimPMF absNIdx pers lst o (promoteN lm n (absNIdx h))) :
    ∀ {pers st lst rm lm} {fu : Std.U64} {v : arena.store.NNodeView} {o},
      absU fu = n → AStateRel pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      arena.promote.promote_n_node pers st rm fu v = ok o →
      SimPMF absNIdx pers lst o (promoteNNodeSpec lm n (absNNodeView v)) := by
    intro pers st lst rm lm fu v o hk hrel hinv hm hrun
    cases v with
    | Anonymous =>
      rw [arena.promote.promote_n_node] at hrun
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨qr, qst⟩ := q
      have hI := intern_persistent_n_run hrel hinv .Anonymous hq
      simp only [Sim, AOut, absNNodeView] at hI
      simp only [SimPMF, SimPM, POut, promoteNNodeSpec, absNNodeView,
        StateT.run_bind]
      cases hqr : qr with
      | Err e =>
        rw [hqr] at hI hrun
        have ho := Result.ok_injective hrun
        rw [← congrArg Prod.fst ho]
        exact AErrSim.bind hI _
      | Ok r1 =>
        rw [hqr] at hI hrun
        obtain ⟨lst1, hx, hrel1, hinv1, hext1, -⟩ := hI
        have ho := Result.ok_injective hrun
        rw [← congrArg Prod.fst ho, ← congrArg Prod.snd ho]
        exact ⟨lm, absNIdx r1, lst1, by rw [hx]; rfl, rfl, hm, hrel1, hinv1,
          hext1⟩
    | Str p str =>
      rw [arena.promote.promote_n_node] at hrun
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hP := ih (h := p) hk hrel hinv hm hq
      obtain ⟨qr, qst⟩ := q
      simp only [SimPMF, SimPM, POut] at hP
      simp only [SimPMF, SimPM, POut, promoteNNodeSpec, absNNodeView,
        StateT.run_bind]
      cases hqr : qr with
      | Err e =>
        rw [hqr] at hP hrun
        have ho := Result.ok_injective hrun
        rw [← congrArg Prod.fst ho]
        exact AErrSim.bind hP _
      | Ok p1 =>
        rw [hqr] at hP hrun
        obtain ⟨m', v', lst1, hx, hv, hm', hrel1, hinv1, hext1⟩ := hP
        subst hv
        obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨q2r, q2st⟩ := q2
        have hI := intern_persistent_n_run hrel1 hinv1 (.Str p1.2 str) hq2
        simp only [Sim, AOut, absNNodeView] at hI
        rw [hx]
        cases hq2r : q2r with
        | Err e =>
          rw [hq2r] at hI hrun
          have ho := Result.ok_injective hrun
          rw [← congrArg Prod.fst ho]
          exact AErrSim.bind hI _
        | Ok r2 =>
          rw [hq2r] at hI hrun
          obtain ⟨lst2, hy, hrel2, hinv2, hext2, -⟩ := hI
          have ho := Result.ok_injective hrun
          rw [← congrArg Prod.fst ho, ← congrArg Prod.snd ho]
          exact ⟨m', absNIdx r2, lst2,
            by simp only [except_ok_bind]; rw [hy]; rfl, rfl, hm', hrel2,
            hinv2, Ext.trans hext1 hext2⟩
    | Num p num =>
      rw [arena.promote.promote_n_node] at hrun
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hP := ih (h := p) hk hrel hinv hm hq
      obtain ⟨qr, qst⟩ := q
      simp only [SimPMF, SimPM, POut] at hP
      simp only [SimPMF, SimPM, POut, promoteNNodeSpec, absNNodeView,
        StateT.run_bind]
      cases hqr : qr with
      | Err e =>
        rw [hqr] at hP hrun
        have ho := Result.ok_injective hrun
        rw [← congrArg Prod.fst ho]
        exact AErrSim.bind hP _
      | Ok p1 =>
        rw [hqr] at hP hrun
        obtain ⟨m', v', lst1, hx, hv, hm', hrel1, hinv1, hext1⟩ := hP
        subst hv
        obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨q2r, q2st⟩ := q2
        have hI := intern_persistent_n_run hrel1 hinv1 (.Num p1.2 num) hq2
        simp only [Sim, AOut, absNNodeView] at hI
        rw [hx]
        cases hq2r : q2r with
        | Err e =>
          rw [hq2r] at hI hrun
          have ho := Result.ok_injective hrun
          rw [← congrArg Prod.fst ho]
          exact AErrSim.bind hI _
        | Ok r2 =>
          rw [hq2r] at hI hrun
          obtain ⟨lst2, hy, hrel2, hinv2, hext2, -⟩ := hI
          have ho := Result.ok_injective hrun
          rw [← congrArg Prod.fst ho, ← congrArg Prod.snd ho]
          exact ⟨m', absNIdx r2, lst2,
            by simp only [except_ok_bind]; rw [hy]; rfl, rfl, hm', hrel2,
            hinv2, Ext.trans hext1 hext2⟩

private theorem promote_n_aux (n : Nat) :
    ∀ {pers st lst rm lm} {fuel : Std.U64} {h : arena.handle.NIdx} {o},
      absU fuel = n → AStateRel pers st lst → AStateInv pers st →
      PMemoRel rm lm →
      arena.promote.promote_n pers st rm fuel h = ok o →
      SimPMF absNIdx pers lst o (promoteN lm n (absNIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel h o hn hrel hinv hm hrun
    rw [arena.promote.promote_n] at hrun
    have hz : fuel = 0#u64 := by
      have h0 : fuel.val = 0 := hn
      scalar_tac
    rw [if_pos hz] at hrun
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    exact POut.err (AErrSim.internal (by rw [promoteN]; rfl))
  | succ n ih =>
    have hnode := promote_n_node_aux n ih
    intro pers st lst rm lm fuel h o hn hrel hinv hm hrun
    rw [arena.promote.promote_n] at hrun
    have hnz : ¬ (fuel = 0#u64) := by
      intro hc; rw [hc] at hn; simp at hn
    rw [if_neg hnz] at hrun
    obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hb2 := nidx_is_persistent_abs hb
    rw [promoteN_unfold, hb2]
    by_cases hp : b = true
    · rw [if_pos hp] at hrun ⊢
      obtain ⟨d, hd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have ho := Result.ok_injective hrun
      subst ho
      exact ⟨lm, absNIdx h, lst, rfl, by rw [dupId_nidx _ _ hd], hm, hrel,
        hinv, Ext.refl _⟩
    · rw [if_neg hp] at hrun ⊢
      obtain ⟨g, hg, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hgm := pmemo_get_n_refines hm hg
      cases hgc : g with
      | some r =>
        rw [hgc] at hrun hgm
        have ho := Result.ok_injective hrun
        subst ho
        rw [← hgm]
        exact ⟨lm, absNIdx r, lst, rfl, rfl, hm, hrel, hinv, Ext.refl _⟩
      | none =>
        rw [hgc] at hrun hgm
        rw [← hgm]
        obtain ⟨w, hw, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hV := view_n_run hrel hinv hw
        simp only [AOut] at hV
        simp only [SimPMF, SimPM, POut, Option.map, StateT.run_bind]
        cases hwc : w with
        | Err e =>
          rw [hwc] at hrun hV
          have ho := Result.ok_injective hrun
          subst ho
          exact AErrSim.bind hV _
        | Ok vw =>
          rw [hwc] at hrun hV
          obtain ⟨lstv, hxv, hrelv, hinvv, -, -⟩ := hV
          have hlv : lstv = lst := viewN_run_state hxv
          rw [hlv] at hxv
          rw [hxv, except_ok_bind]
          obtain ⟨fu, hfu, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hfuv : absU fu = n := by
            have h1 : fu.val = fuel.val - (1#u64 : Std.U64).val :=
              (ConRon.Refine.Nat.usub_val hfu).2
            have h2 : fuel.val = n + 1 := hn
            have h3 : (1#u64 : Std.U64).val = 1 := rfl
            show fu.val = n
            omega
          obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hN := hnode (v := vw) hfuv hrel hinv hm hq
          obtain ⟨qr, qst⟩ := q
          simp only [SimPMF, SimPM, POut] at hN
          cases hqr : qr with
          | Err e =>
            rw [hqr] at hN hrun
            have ho := Result.ok_injective hrun
            subst ho
            exact AErrSim.bind hN _
          | Ok p1 =>
            rw [hqr] at hN hrun
            obtain ⟨m', v', lst1, hx, hv, hm', hrel1, hinv1, hext1⟩ := hN
            subst hv
            obtain ⟨m3, hm3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hm3r := pmemo_set_n_refines hm' hm3
            have ho := Result.ok_injective hrun
            subst ho
            exact ⟨{ m' with nM := m'.nM.insert (absNIdx h) (absNIdx p1.2) },
              absNIdx p1.2, lst1, by rw [hx]; rfl, rfl, hm3r, hrel1, hinv1,
              hext1⟩

/-- **`promote_n` ⊑ `promoteN`** — the name walk, closed modulo
`Refine2/Specs.lean`'s `intern_persistent_n_run`. -/
theorem promote_n_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_n pers st rm fuel h = ok o) :
    SimPMF absNIdx pers lst o (promoteN lm (absU fuel) (absNIdx h)) :=
  promote_n_aux _ rfl hrel hinv hm hrun

/-- `promote_n_node` ⊑ `promoteNNodeSpec`. -/
theorem promote_n_node_refines {pers st lst rm lm} {fuel : Std.U64}
    {v : arena.store.NNodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_n_node pers st rm fuel v = ok o) :
    SimPMF absNIdx pers lst o
      (promoteNNodeSpec lm (absU fuel) (absNNodeView v)) :=
  promote_n_node_aux (absU fuel)
    (fun hk hrel' hinv' hm' hq => hk ▸ promote_n_refines hrel' hinv' hm' hq)
    rfl hrel hinv hm hrun

/-- `promote_l` ⊑ `promoteL`. -/
theorem promote_l_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l pers st rm fuel h = ok o) :
    SimPMF absLIdx pers lst o (promoteL lm (absU fuel) (absLIdx h)) := by
  sorry

/-- `promote_l_node` ⊑ `promoteLNodeSpec`. -/
theorem promote_l_node_refines {pers st lst rm lm} {fuel : Std.U64}
    {v : arena.store.LNodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_node pers st rm fuel v = ok o) :
    SimPMF absLIdx pers lst o
      (promoteLNodeSpec lm (absU fuel) (absLNodeView v)) := by
  sorry

/-- `promote_l_two` is the two-child level arms' pair of promotions, in the
twin's order; it has no twin of its own and is stated against the arm. -/
theorem promote_l_two_refines {pers st lst rm lm} {fuel : Std.U64}
    {u v : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_two pers st rm fuel u v = ok o) :
    SimPM (fun r p => p = (absLIdx r.1, absLIdx r.2)) pers lst o
      (do
        let (m, a) ← promoteL lm (absU fuel) (absLIdx u)
        let (m, b) ← promoteL m (absU fuel) (absLIdx v)
        pure (m, (a, b))) := by
  sorry

/-- `promote_l_list_from` ⊑ `promoteLList` at the cursor. -/
theorem promote_l_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {us : alloc.vec.Vec arena.handle.LIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_list_from pers st rm fuel us i out = ok o) :
    SimPMF (fun v => absLIdxL out ++ absLIdxL v) pers lst o
      (do
        let (m, vs) ← promoteLList lm (absU fuel) (absLIdxLFrom us i)
        pure (m, absLIdxL out ++ vs)) := by
  sorry

/-- `promote_l_list` ⊑ `promoteLList`. -/
theorem promote_l_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {us : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_list pers st rm fuel us = ok o) :
    SimPMF absLIdxL pers lst o (promoteLList lm (absU fuel) (absLIdxL us)) := by
  sorry

/-- `promote_ls` ⊑ `promoteLs`. -/
theorem promote_ls_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ls pers st rm fuel h = ok o) :
    SimPMF absLsIdx pers lst o (promoteLs lm (absU fuel) (absLsIdx h)) := by
  sorry

/-- `promote_e` ⊑ `promoteE`. -/
theorem promote_e_refines {pers st lst rm lm} {fuel : Std.U64}
    {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e pers st rm fuel h = ok o) :
    SimPMF absEIdx pers lst o (promoteE lm (absU fuel) (absEIdx h)) := by
  sorry

/-- `promote_e_node` ⊑ `promoteENodeSpec`. -/
theorem promote_e_node_refines {pers st lst rm lm} {fuel : Std.U64}
    {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e_node pers st rm fuel v = ok o) :
    SimPMF absEIdx pers lst o
      (promoteENodeSpec lm (absU fuel) (absENodeView v)) := by
  sorry

/-- `promote_e_two` — the two-child expression arms' pair, in the twin's
order. -/
theorem promote_e_two_refines {pers st lst rm lm} {fuel : Std.U64}
    {x y : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e_two pers st rm fuel x y = ok o) :
    SimPM (fun r p => p = (absEIdx r.1, absEIdx r.2)) pers lst o
      (do
        let (m, a) ← promoteE lm (absU fuel) (absEIdx x)
        let (m, b) ← promoteE m (absU fuel) (absEIdx y)
        pure (m, (a, b))) := by
  sorry

/-! ## The lists -/

/-- `promote_n_list_from` ⊑ `promoteNList` at the cursor. -/
theorem promote_n_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {ns : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_n_list_from pers st rm fuel ns i out = ok o) :
    SimPMF (fun v => absNIdxL out ++ absNIdxL v) pers lst o
      (do
        let (m, vs) ← promoteNList lm (absU fuel) (absNIdxLFrom ns i)
        pure (m, absNIdxL out ++ vs)) := by
  sorry

/-- `promote_n_list` ⊑ `promoteNList`. -/
theorem promote_n_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {ns : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_n_list pers st rm fuel ns = ok o) :
    SimPMF absNIdxL pers lst o (promoteNList lm (absU fuel) (absNIdxL ns)) := by
  sorry

/-- `promote_e_list_from` ⊑ `promoteEList` at the cursor. -/
theorem promote_e_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {es : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e_list_from pers st rm fuel es i out = ok o) :
    SimPMF (fun v => absEIdxL out ++ absEIdxL v) pers lst o
      (do
        let (m, vs) ← promoteEList lm (absU fuel) (absEIdxLFrom es i)
        pure (m, absEIdxL out ++ vs)) := by
  sorry

/-- `promote_e_list` ⊑ `promoteEList` — a block at ONE memo, so the sharing
survives the copy. -/
theorem promote_e_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {es : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_e_list pers st rm fuel es = ok o) :
    SimPMF absEIdxL pers lst o (promoteEList lm (absU fuel) (absEIdxL es)) := by
  sorry

/-! ## The declaration layer

`Arena/Env.lean`'s record, field for field: every handle is promoted and every
`Nat`, `Bool`, `ReducibilityHint`, `PropWhen` and `BinderMeta` crosses
unchanged (DESIGN §8.7's ruling that (B) imports con-leche's
representation-free types). -/

/-- `promote_cv` ⊑ `promoteCV`. -/
theorem promote_cv_refines {pers st lst rm lm} {fuel : Std.U64}
    {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_cv pers st rm fuel cv = ok o) :
    SimPMF absIConstantVal pers lst o
      (promoteCV lm (absU fuel) (absIConstantVal cv)) := by
  sorry

/-- `promote_fire` ⊑ `promoteFire`. -/
theorem promote_fire_refines {pers st lst rm lm} {fuel : Std.U64}
    {f : arena.env.IRecRuleFire} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_fire pers st rm fuel f = ok o) :
    SimPMF absIRecRuleFire pers lst o
      (promoteFire lm (absU fuel) (absIRecRuleFire f)) := by
  sorry

/-- `promote_rule` ⊑ `promoteRule`. -/
theorem promote_rule_refines {pers st lst rm lm} {fuel : Std.U64}
    {rl : arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_rule pers st rm fuel rl = ok o) :
    SimPMF absIRecRule pers lst o (promoteRule lm (absU fuel) (absIRecRule rl)) := by
  sorry

/-- `promote_rules_from` ⊑ `promoteRules` at the cursor. -/
theorem promote_rules_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {rs : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_rules_from pers st rm fuel rs i out = ok o) :
    SimPMF (fun v => absIRecRuleL out ++ absIRecRuleL v) pers lst o
      (do
        let (m, vs) ← promoteRules lm (absU fuel) (absIRecRuleLFrom rs i)
        pure (m, absIRecRuleL out ++ vs)) := by
  sorry

/-- `promote_rules` ⊑ `promoteRules`. -/
theorem promote_rules_refines {pers st lst rm lm} {fuel : Std.U64}
    {rs : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_rules pers st rm fuel rs = ok o) :
    SimPMF absIRecRuleL pers lst o (promoteRules lm (absU fuel) (absIRecRuleL rs)) := by
  sorry

/-- `promote_caps` ⊑ `promoteCaps` — one name; `sortZ` is a `PropWhen` over
con-leche `Name`s and carries no handle. -/
theorem promote_caps_refines {pers st lst rm lm} {fuel : Std.U64}
    {c : arena.env.IIndCaps} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_caps pers st rm fuel c = ok o) :
    SimPMF absIIndCaps pers lst o (promoteCaps lm (absU fuel) (absIIndCaps c)) := by
  sorry

/-- `promote_proj_table` ⊑ `promoteProjTable`, `tableName` included (it is a
stored handle, not a recomputed name — `Arena/Env.lean`'s one added field). -/
theorem promote_proj_table_refines {pers st lst rm lm} {fuel : Std.U64}
    {t : arena.env.IProjTable} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_proj_table pers st rm fuel t = ok o) :
    SimPMF absIProjTable pers lst o
      (promoteProjTable lm (absU fuel) (absIProjTable t)) := by
  sorry

/-- `promote_proj_table_rest` is the Rust-only tail of `promote_proj_table`
past its three leading promotions (extraction rule 5), stated against the same
twin with those handles in hand. -/
theorem promote_proj_table_rest_refines {pers st lst rm lm} {fuel : Std.U64}
    {t : arena.env.IProjTable} {sn tn : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_proj_table_rest pers st rm fuel t sn tn lps = ok o) :
    SimPMF absIProjTable pers lst o
      (do
        let (m, c) ← promoteN lm (absU fuel) (absNIdx t.ctor)
        let (m, ss) ← promoteL m (absU fuel) (absLIdx t.struct_sort)
        let (m, bs) ← promoteEList m (absU fuel) (absEIdxL t.bodies)
        let (m, gs) ← promoteLList m (absU fuel) (absLIdxL t.guards)
        pure (m, ⟨absNIdx sn, absNIdx tn, absNIdxL lps, absU t.num_params, c,
          absU t.num_fields, ss, bs.toArray, gs, absU t.off⟩)) := by
  sorry

/-- `promote_ci` ⊑ `promoteCI` — the seven `IConstantInfo` constructors, which
is what "the handles the environment keeps" means. -/
theorem promote_ci_refines {pers st lst rm lm} {fuel : Std.U64}
    {ci : arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ci pers st rm fuel ci = ok o) :
    SimPMF absIConstantInfo pers lst o
      (promoteCI lm (absU fuel) (absIConstantInfo ci)) := by
  sorry

/-- `promote_ci_list_from` ⊑ `promoteCIList` at the cursor. -/
theorem promote_ci_list_from_refines {pers st lst rm lm} {fuel : Std.U64}
    {cs : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ci_list_from pers st rm fuel cs i out = ok o) :
    SimPMF (fun v => absICIL out ++ absICIL v) pers lst o
      (do
        let (m, vs) ← promoteCIList lm (absU fuel) (absICILFrom cs i)
        pure (m, absICIL out ++ vs)) := by
  sorry

/-- `promote_ci_list` ⊑ `promoteCIList` — a block at ONE memo. -/
theorem promote_ci_list_refines {pers st lst rm lm} {fuel : Std.U64}
    {cs : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_ci_list pers st rm fuel cs = ok o) :
    SimPMF absICIL pers lst o (promoteCIList lm (absU fuel) (absICIL cs)) := by
  sorry

/-- `promote_decl` ⊑ `promoteDecl` — not on the fold's path (the records
arrive from the parse and are persistent) and twinned because the layer is
twinned whole. -/
theorem promote_decl_refines {pers st lst rm lm} {fuel : Std.U64}
    {d : arena.env.IDeclaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_decl pers st rm fuel d = ok o) :
    SimPMF absIDeclaration pers lst o
      (promoteDecl lm (absU fuel) (absIDeclaration d)) := by
  sorry

/-- `promote_vg` ⊑ `promoteVG` — the datum that crosses the install/check
seam, promoted beside the environment and at the SAME memo (an `opaque`'s
value is not in the environment; only the pending record holds it). -/
theorem promote_vg_refines {pers st lst rm lm} {fuel : Std.U64}
    {g : arena.checker_split.ValueGroup} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_vg pers st rm fuel g = ok o) :
    SimPMF absValueGroup pers lst o
      (promoteVG lm (absU fuel) (absValueGroup g)) := by
  sorry

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
  sorry

/-- `index_promoted` ⊑ `promoteCIList` followed by `indexPromoted`, on the
slice `start..j` (finding B).  The promoted records are written back into
their own slots, so the environment's shape is unchanged and only the middle
segment moves. -/
theorem index_promoted_refines {pers st lst rm lm rf lf} {fuel : Std.U64}
    {start j : Std.Usize} {c : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hle : start.val ≤ j.val) (hj : j.val ≤ rf.env.consts.val.length)
    (hrun : arena.promote.index_promoted pers st rm fuel rf start j c = ok o) :
    SimPM (fun r v => IFEnvRel r v) pers lst o
      (do
        let n := rf.env.consts.val.length
        let cs := (absIEnv rf.env).consts
        let (m, mid) ← promoteCIList lm (absU fuel)
          ((cs.drop (n - j.val)).take (j.val - start.val))
        pure (m, ⟨⟨cs.take (n - j.val) ++ mid ++ cs.drop (n - start.val)⟩,
          indexPromoted lf.idx (absU c) mid, lf.visibleBelow⟩)) := by
  sorry

/-- **`promote_new` ⊑ `promoteNew`** — the phase-A bracket's promotion half:
the `k` constants the step just installed, copied into the persistent tier and
re-indexed, everything below them untouched.  `hk` is finding C. -/
theorem promote_new_refines {pers st lst rm lm rf lf} {fuel k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : PMemoRel rm lm) (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hk : absU k ≤ rf.env.consts.val.length)
    (hrun : arena.promote.promote_new pers st rm fuel k rf = ok o) :
    SimPM (fun r v => IFEnvRel r v) pers lst o
      (promoteNew lm (absU fuel) (absU k) lf) := by
  sorry


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

/-- info: 'ConRon.Refine2.promote_n_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promote_n_refines

end ConRon.Refine2
