/-
# `ConRon.Refine2.Modular.WorkerRead` — `modular/worker.rs`: phases 1–4 of the worker

**Task #166, Theorem 2.**  `worker_reach` (phase 4 and the hoist) and `worker_read` (phases 1–4)
against their twins `workerReach`, `workerRead` (`Arena/Modular/Worker.lean`).  Both claim their
accept only: the Rust's `Ok` is a run of the twin in related states (`LA`; `worker_read`'s
failure carries a position, so its claim is stated out, `WorkerReadAccept`).

**Lane L2's reach.**  `worker_reach_la` takes `reach::record_reads`, `reach::owner_map` and
`reach::reach` as the shapes `RecordReadsRel` (in `Modular/Worker.lean`), `OwnerMapRel` and
`ReachHyp` (here); `recordReadsRel_holds`, `ownerMapRel_holds` and `reachHyp_holds` prove them,
and `worker_read_refines` takes none.
The home is `home_of_refines'` (`load_view`, `check_views` with their Theorem 2).  `copies_ok`'s
claim is over a tier whose frozen base is empty (`hb`, `hok`), passed through too.
-/
import ConRon.Refine2.Modular.Worker
import ConRon.Refine2.Modular.WorkerCopies
import ConRon.Refine2.Modular.ReachRel
import ConRon.Refine2.Modular.ReachGo

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.worker

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Lockstep (LS)
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine2.Frontend (absNIdxArr absIDeclArr)

/-! ## Lane L2's reach -/

/-- **`reach::owner_map` is `ownerMap`** — lane L2's `owner_map_ls`, in the shape
`worker_reach_la` takes. -/
def OwnerMapRel (pers : arena.store.PersTier) : Prop :=
  ∀ {st lst} (ds : alloc.vec.Vec arena.env.IDeclaration), AStateRel₀ pers st lst → AStateInv pers st →
    LS pers IdxRel (frontend.modular.reach.owner_map pers st ds) lst
      (Modular.ownerMap (absIDeclArr ds).toList)

/-- **`OwnerMapRel` holds**: lane L2's `owner_map_ls`. -/
theorem ownerMapRel_holds (pers : arena.store.PersTier) : OwnerMapRel pers :=
  fun ds hrel hinv => owner_map_ls hrel hinv ds

/-- **`reach::reach`'s accept is `reach`'s** — lane L2's `reach_refines` (its rejects name
records, so an accept), in the shape `worker_reach_la` takes. -/
def ReachHyp {F : Type} (inst : frontend.checker_io.CheckerFs F) (fsv : F)
    (fs : Arena.Frontend.Olean.OleanFs) (pers : arena.store.PersTier) : Prop :=
  ∀ {st lst} (pk : frontend.olean.spec.OleanPins) (sp : frontend.olean.files.Roots)
    (m : arena.handle.NIdx) {wr : frontend.olean.index.WorkerReads} {wr' : Arena.Frontend.Olean.WorkerReads}
    {own : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {own' : _root_.Std.HashSet NIdx}
    (roots : alloc.vec.Vec arena.handle.NIdx),
    WorkerReadsRel wr wr' → NSet own own' → AStateRel₀ pers st lst → AStateInv pers st →
    LA pers ReachRel (frontend.modular.reach.reach inst fsv pk pers st sp m wr own roots) lst
      (Modular.reach fs (absPins pk) (absRoots sp) (absNIdx m) wr' own' (absNIdxArr roots))

/-- **`ReachHyp` holds**: lane L2's `reach_refines`. -/
theorem reachHyp_holds {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F}
    {fs : Arena.Frontend.Olean.OleanFs} {pers : arena.store.PersTier} (hfs : FsRel inst fsv fs) :
    ReachHyp inst fsv fs pers := by
  intro _ _ _ _ _ _ _ _ _ _ hw ho hrel hinv
  exact reach_refines hfs hw ho hrel hinv

/-! ## `worker_reach` -/

/-- `worker_reach`'s answer against the twin's. -/
def WorkerReachRel (a : frontend.modular.reach.Reach × alloc.vec.Vec arena.env.IDeclaration ×
    alloc.vec.Vec arena.handle.NIdx) (b : Modular.Reach × _root_.Array IDeclaration × _root_.Array NIdx) :
    Prop :=
  ReachRel a.1 b.1 ∧ b.2.1 = absIDeclArr a.2.1 ∧ b.2.2 = absNIdxArr a.2.2

section reads

variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F}
  {fs : Arena.Frontend.Olean.OleanFs}

/-- **`worker_reach`'s accept is `workerReach`'s**: the own holes, the roots, the reach, its
names distinct, the copies, the own records hoisted. -/
theorem worker_reach_la {pers : arena.store.PersTier} (hRR : RecordReadsRel pers)
    (hOM : OwnerMapRel pers) (hRe : ReachHyp inst fsv fs pers)
    (hb : BaseRel pers.env {}) (hok : BaseOK pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (pk : frontend.olean.spec.OleanPins) (sp : frontend.olean.files.Roots)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) (m : arena.handle.NIdx)
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {x' : _root_.Array Arena.Frontend.Olean.ImportRec} (hx : x.val.length = x'.size)
    {wr : frontend.olean.index.WorkerReads} {wr' : Arena.Frontend.Olean.WorkerReads}
    (hwr : WorkerReadsRel wr wr')
    {cs : alloc.vec.Vec frontend.olean.lazy.CEntry}
    {cs' : _root_.Array Arena.Frontend.Olean.CEntry} (hcs : List.Forall₂ CEntryRel cs.val cs'.toList)
    (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LA pers WorkerReachRel (worker_reach inst fsv pk pers st sp pins m x wr cs ds) lst
      (Modular.workerReach fs (absPins pk) (absRoots sp) (absINatOpPinSetL pins) (absNIdx m) x' wr' cs'
        (absIDeclArr ds)) := by
  rw [worker_reach, Modular.workerReach]
  refine LA.rust fun u hu0 => ?_
  have hu : ConRon.Refine2.Frontend.UsedRel _ u _ pers := own_uses_used_rel (own_uses_of_rel hcs hu0) pers
  refine LA.bind (own_holes_ok_la hu hrel hinv pk m x hx.symm wr.index ds
      (fun st lst h1 h2 => LS.la (recs_loaded_ls h1 h2 hwr.index ds false)))
    (fun _ _ _ _ h => by simp at h) ?_
  rintro _ _ st1 lst1 _ hrel1 hinv1
  refine LA.bind (LS.la (roots_at_ls hRR hrel1 hinv1 pins hx hwr.index hcs ds))
    (fun _ _ _ _ h => by simp at h) ?_
  rintro rs _ st2 lst2 rfl hrel2 hinv2
  refine LA.rust fun hm hhm => ?_
  have hN := own_names_of_rel hwr.index hx hcs hhm
  refine LA.bind (hRe pk sp m rs hwr hN hrel2 hinv2) (fun _ _ _ _ h => by simp at h) ?_
  rintro r3 r' st3 lst3 hR hrel3 hinv3
  rw [hR.ctx]
  refine LA.bind (LS.la (ctx_names_nodup_ls hrel3 hinv3 r3.ctx)) (fun _ _ _ _ h => by simp at h) ?_
  rintro b b' st4 lst4 hbb hrel4 hinv4
  rw [hbb]
  cases b
  · la_err
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine LA.bind (copies_ok_la hrel4 hinv4 hb hok pk m x x' wr wr' r3 hR.ctx ds
        (fun st lst h1 h2 => by rw [hR.ctx]; exact LS.la (hOM _ h1 h2))
        (fun st lst h1 h2 => LS.la (copy_recs_ls h1 h2 hx hwr.index ds)))
      (fun _ _ _ _ h => by simp at h) ?_
    rintro _ _ st5 lst5 _ hrel5 hinv5
    refine LA.rust fun v hv => ?_
    have ev := decls_dup_eq hv
    rw [← ev]
    refine LA.bind (LS.la (own_recs_ls hrel5 hinv5 hx hwr.index v)) (fun _ _ _ _ h => by simp at h) ?_
    rintro o _ st6 lst6 rfl hrel6 hinv6
    intro a st' h
    obtain ⟨⟨r7, st7⟩, h7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r7 with
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok p =>
      obtain ⟨own, hoisted⟩ := p
      obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      cases h1
      obtain ⟨lst7, hx7, hrel7, hinv7⟩ := Sim₀.apply (ConRon.Refine2.Frontend.hoist_nat_op_ground_refines hu hrel6 hinv6 h7)
      exact ⟨_, lst7, by rw [am_bind_ok hx7]; rfl, ⟨hR, rfl, rfl⟩, hrel7, hinv7⟩

/-! ## `worker_read` -/

/-- **`WorkerRead` against the twin's**, field by field; `ER` the exports' relation
(`check_views`'). -/
structure WorkerReadRel
    (ER : alloc.vec.Vec frontend.olean.module.Expo → _root_.Array ConLeche.Frontend.Olean.Expo → Prop)
    (w : frontend.modular.worker.WorkerRead) (w' : Modular.WorkerRead) : Prop where
  home : LoadedRel w.home w'.home
  expo : ER w.expo w'.expo
  reads : WorkerReadsRel w.reads w'.reads
  emitted : w'.emitted = absIDeclArr w.emitted
  own : w'.own = absIDeclArr w.own
  reach : ReachRel w.reach w'.reach
  hoisted : w'.hoisted = absNIdxArr w.hoisted
  pins : w'.pins = absPins w.pins
  values : List.Forall₂ ModRefRel w.values.val w'.values.toList
  start : w'.start = w.start.val

/-- **The accept of `worker_read`**: the Rust's `Ok` is the twin's `.ok`, in related states. -/
def WorkerReadAccept (pers : arena.store.PersTier)
    (ER : alloc.vec.Vec frontend.olean.module.Expo → _root_.Array ConLeche.Frontend.Olean.Expo → Prop)
    (m : Result (core.result.Result frontend.modular.worker.WorkerRead
      (kernel.core_types.CheckError × Std.U64) × arena.monad.AState))
    (lst : AState) (x : AM (Except (CheckError × Nat) Modular.WorkerRead)) : Prop :=
  ∀ w st', m = ok (.Ok w, st') →
    ∃ w' lst', x.run lst = .ok (.ok w', lst') ∧ WorkerReadRel ER w w' ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st'

/-- **`worker_read`'s accept is `workerRead`'s**: the pins, the private files, the home, the
worker's reads, the own records, then `worker_reach`. -/
theorem worker_read_refines (hfs : FsRel inst fsv fs) {pers : arena.store.PersTier}
    (hb : BaseRel pers.env {}) (hok : BaseOK pers)
    {st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (sp : frontend.olean.files.Roots) (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (m : arena.handle.NIdx) (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) :
    WorkerReadAccept pers ExpoRel (worker_read inst fsv pers st sp pins m x) lst
      (Modular.workerRead fs (absRoots sp) (absINatOpPinSetL pins) (absNIdx m) (absImports x)) := by
  intro w st' h
  rw [worker_read] at h
  unfold Modular.workerRead
  -- the pins
  obtain ⟨⟨r, e⟩, h0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e1 => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok p =>
  obtain ⟨pk', lst1, hx1, rfl, hrel1, hinv1⟩ := olean_pins_refines hrel hinv _ _ h0
  rw [am_bind_ok hx1]
  -- the private files
  obtain ⟨r1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e1 => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok f =>
  obtain ⟨n, hn⟩ := read_files_name h1
  obtain ⟨f', ef, hf⟩ := read_files_refines hfs hn h1
  rw [am_bind_ok (read_name_run (st := withStore st e) hrel1 hn)]
  have ef' : Arena.Frontend.Olean.readFiles fs (absRoots sp) (ConRon.Refine.absName n) .private = .ok f' := ef
  simp only [ef', Arena.Frontend.Olean.liftE]
  rw [pure_bind]
  -- the home
  obtain ⟨⟨r2, e1⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e2 => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok hh =>
  obtain ⟨l, expo⟩ := hh
  obtain ⟨⟨l', expo'⟩, lst2, hx2, ⟨hL, hE⟩, hrel2, hinv2⟩ :=
    home_of_refines' hf (st := withStore st e) hrel1 hinv1 _ e1 h2
  rw [am_bind_ok hx2]
  -- the worker's reads
  obtain ⟨⟨r3, e2⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err e3 => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok wr =>
  obtain ⟨wr', lst3, hx3, hW, hrel3, hinv3⟩ :=
    worker_reads_refines hfs (st := withStore (withStore st e) e1) hrel2 hinv2 _ e2 h3
  rw [am_bind_ok hx3]
  -- the header test
  have hcont : ∀ {b}, ron.hashmap2.HashMap2.contains_key
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 wr.loads.index m = ok b →
      b = wr'.loads.index.contains (absNIdx m) := fun hb => hW.loads.index.contains_eq hb
  simp only at h ⊢
  by_cases hi : (alloc.vec.Vec.len x != 0#usize) = true
  on_goal 1 =>
    simp only [hi, ↓reduceIte] at h
    obtain ⟨b, hcb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ec := hcont hcb
    cases b
    on_goal 2 =>
      simp only [↓reduceIte] at h
      iterate 8 (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
      cases (Prod.mk.inj (Result.ok_injective h)).1
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [ite_eq_right (by simp [← ec])]
  on_goal 2 =>
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    rw [ite_eq_right (by simp at hi; simp [absImports, hi])]
  all_goals
    obtain ⟨⟨r4, e3⟩, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r4 with
    | Err e4 => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok d =>
    obtain ⟨lst4, hx4, he3, hrel4, hinv4⟩ := own_records_refines hrel3 hinv3 hL h4
    rw [pure_bind, am_bind_ok (show (Modular.ownRecords (absPins p) l').run lst3 = _ from hx4)]
    obtain ⟨⟨r5, st1⟩, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r5 with
    | Err e4 => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok t =>
    obtain ⟨r6, own, hoisted⟩ := t
    obtain ⟨⟨r', own', hoisted'⟩, lst5, hx5, ⟨hR, rfl, rfl⟩, hrel5, hinv5⟩ :=
      worker_reach_la (recordReadsRel_holds pers) (ownerMapRel_holds pers) (reachHyp_holds hfs) hb hok (st := { st with store := e3 })
        (by rw [he3]; exact hrel4) (by rw [he3]; exact hinv4) p sp pins m (x' := absImports x) (by simp) hW hL.constants d _ _ h5
    simp only
    rw [am_bind_ok hx5]
    obtain ⟨⟨values, l1⟩, h6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hV, hL1⟩ := home_values_rel hL h6
    obtain ⟨h7, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h7
    refine ⟨_, lst5, rfl, ⟨hL1, hE, hW, rfl, rfl, hR, rfl, rfl, hV, ?_⟩, hrel5, hinv5⟩
    rw [hR.ctx]; simp [absIDeclArr]
end reads

end ConRon.Refine2.Modular
