import ConRon.MainTheorem.Driver
import ConRon.MainTheorem.Args
import ConRon.MainTheorem.Conclusions

/-!
# `ConRon.MainTheorem.Oleans` — the walk of the extracted driver at `--olean -- <root>`

**Task #171, slice 2** (DESIGN.md §3.9).  An exit 0 of `run_args` at
`["--olean", "--search-path=" ++ dirs, "--", root]` is every step premise of the `--olean`
staged lemma (`OleanStages`), the root the module `parseModName root` names and the lookup
`searchPathOf dirs`; lane C's conclusion then gives con-leche's `main_oleans`.

| lemma | what it walks |
|---|---|
| `rust_stages_oleans_dec`, `oleans_model_of_stages_dec` | `Stages.rust_stages_oleans`, lane C's `oleans_model_of_stages` with the preparation's `UsedConsts` the read with its records moved out, and the reads and the pool at two instances' states |
| `olean_job_sol`, `olean_stepAt` | `check_main::olean_job`, `OleanJobStep`'s step: `oleanJobStepSol` |
| `parallelAll_mono`, `check_phase_olean_ok` | `check_main::check_phase_olean`: the pool's contract at `oleanJobStep` |
| `intern_names_roots`, `intern_consts_nil` | `check_main::intern_names`, `intern_consts` |
| `check_oleans_zero` | `check_main::check_oleans` |
| `parse_mod_names_loop_val`, `parse_args_oleans`, `olean_args_oleans`, `run_args_oleans` | the argument list, `cli::olean_args`, `cli::run_args` |
| `oleans_of_canGive` | `main_oleans`'s proof |
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.MainTheorem.Stages
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean
open ConLeche (IsModel FS)
open ConLeche.Frontend.Olean (closureConstants)

namespace ConRon.MainTheorem

set_option autoImplicit false

universe w

/-- **The read with its records moved out answers the same `UsedConsts`**: what a theorem
mentions is read off the merged constants alone. -/
theorem olean_read_used_rel_dec {pers : arena.store.PersTier} {rd : frontend.olean.records.OleanRead}
    {rd' : ConRon.Arena.Frontend.Olean.OleanRead} (hrd : OleanReadRel rd rd')
    (v : alloc.vec.Vec arena.env.IDeclaration) :
    UsedRel frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts
      { rd with decls := v } rd'.usedOf pers := by
  intro rst lst d o hrel hinv h
  exact olean_read_used_rel hrd hrel hinv h

/-- `Stages.rust_stages_oleans` with the preparation's `UsedConsts` the read with its records
moved out (`core::mem::replace(&mut rd.decls, Vec::new())`, `check_main::check_oleans`): what a
theorem mentions is the merged constants', which the move leaves. -/
theorem rust_stages_oleans_dec (hT2 : ReadOleansRefines)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    (hfz : pers.frozen = false)
    {st0 st1 st2 st4 st5 st6 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {rd : frontend.olean.records.OleanRead}
    {prepared : frontend.prepare.Prepared}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ix : arena.stream_index.IStreamIndex}
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e pers st1 = ok (.Ok pre, st2))
    {names : List kernel.name.Name} {roots : alloc.vec.Vec arena.handle.NIdx}
    {stR : arena.monad.AState} (hroots : InternRoots pers st2 names roots.val stR)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs} {F : ConLeche.FS}
    (hsnap : SnapshotOf finst fsv F)
    {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
    (hsnap' : SnapshotOf finst' fsv' F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv pers stR.store ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false
      = ok (.Ok rd, store3))
    {v : alloc.vec.Vec arena.env.IDeclaration}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers { stR with store := store3 } pre rd.decls { rd with decls := v }
      = ok (.Ok prepared, st4))
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins pers st4 pins maxNatSize = ok (.Ok ipins, st5))
    (h6 : OleanPoolAccepts finst' fsv' pers st5 .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩ ix st6) :
    ∃ (sA sB sB' sC sD sE sF : ConRon.Arena.AState) (rd' : ConRon.Arena.Frontend.Olean.OleanRead)
      (I : ConRon.Arena.IStreamIndex),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      (names.map ConRon.Refine.absName).mapM ConRon.Arena.internName sB
          = .ok (roots.val.map absNIdx, sB') ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absSearchPath dirs) (roots.val.map absNIdx).toArray none false false sB' = .ok (.ok rd', sC) ∧
      ConRon.Arena.Frontend.prepareD (absPreludeIx pre) rd'.decls rd'.usedOf sC
          = .ok (absPrepared prepared, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins)
          (ConRon.Refine.Nat.toNat maxNatSize) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledOleanAccepts (ConRon.Bridge.Frontend.Olean.modelFs F) rd'.pins
          (absSearchPath dirs) rd'.values .verified (absINatOpPinSetL ipins)
          (absIDeclL prepared.decls).toArray sE I sF ∧
      AStateRel₀ pers st6 sF := by
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hfz hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hrelA hinvA h2
  subst hpreL
  obtain ⟨sB', hR, hrelR, hinvR⟩ := internRoots_refines names roots.val hroots hrelB hinvB
  have hfs := fsRel_of_snapshot hsnap
  obtain ⟨rd', sC, hC, hrd, hrelC, hinvC⟩ := hT2 hfs hrelR hinvR h3
  obtain ⟨sD, hD, hrelD, hinvD⟩ :=
    (prepare_d_refines (olean_read_used_rel_dec hrd v) hrelC hinvC h4).apply
  have hdecls : absIDeclArr rd.decls = rd'.decls := by
    simp [absIDeclArr, hrd.decls]
  rw [hdecls] at hD
  obtain ⟨sE, hE, hrelE, hinvE⟩ :=
    (intern_all_pins_refines hrelD hinvD
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  obtain ⟨I, sF, hF, hrelF, -⟩ :=
    olean_pool_accepts_refines (values' := rd'.values) (fsRel_of_snapshot hsnap') hrd.values hrelE hinvE hfz h6
  rw [hrd.pins] at hF
  exact ⟨sA, sB, sB', sC, sD, sE, sF, rd', I, hA, hB, hR, hC, hD, hE, hF, hrelF⟩


/-- `oleans_model_of_stages` at the driver's preparation (`rust_stages_oleans_dec`): its
`UsedConsts` the read with its records moved out. -/
theorem oleans_model_of_stages_dec (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {names : List kernel.name.Name} {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {st1 st2 stR st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {roots : alloc.vec.Vec arena.handle.NIdx}
    (hroots : InternRoots emptyTier st2 names roots.val stR)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
    (hsnap' : SnapshotOf finst' fsv' F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false
      = ok (.Ok rd, store3))
    {prepared : frontend.prepare.Prepared}
    {v : alloc.vec.Vec arena.env.IDeclaration}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } pre rd.decls { rd with decls := v }
      = ok (.Ok prepared, st4))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
      (oleanJobStep finst' fsv' tier .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩)) :
    ∃ model, IsModel V model
      (closureConstants (absSearchPath dirs) F (names.map ConRon.Refine.absName).toArray) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  obtain ⟨sA, sB, sB', sC, sD, sE, sF, rd', I, hA, hB, hR, hC, hD, hE, hF, -⟩ :=
    rust_stages_oleans_dec read_oleans_refines hdec rfl hest hst0 h1 h2 hroots hsnap hsnap' h3 h4 h5
      (oleanPoolAccepts_intro h6 h7 h8)
  exact ConRon.Bridge.stagesO_isModel V hk hind (pins := ConRon.Refine.absPins pins)
    hA hB hR hC hD hE hF



/-! ## The `.olean` job -/

/-- A fold whose every step answers as another's is that one's fold. -/
theorem foldAllOk_mono {S E I : Type} {step step' : S → I → Result (core.result.Result Unit E × S)}
    (h : ∀ x k r, step x k = ok r → step' x k = ok r) :
    ∀ (s : S) (ks : List I), FoldAllOk step s ks → FoldAllOk step' s ks
  | _, [], _ => trivial
  | s, k :: ks, ⟨s', h1, h2⟩ => ⟨s', h s k _ h1, foldAllOk_mono h s' ks h2⟩

/-- **The pool's contract carries over** to a step that answers as the pool's wherever that
one answers. -/
theorem parallelAll_mono {S E : Type} {n : Nat} {init init' : Result S}
    {step step' : S → Nat → Result (core.result.Result Unit E × S)} (hi : init = init')
    (h : ∀ x k r, step x k = ok r → step' x k = ok r) :
    ParallelAll n init step → ParallelAll n init' step' := by
  rintro ⟨parts, hcov, hparts⟩
  refine ⟨parts, hcov, fun w hw => ?_⟩
  obtain ⟨hs, s₀, h0, hf⟩ := hparts w hw
  exact ⟨hs, s₀, hi ▸ h0, foldAllOk_mono h s₀ w hf⟩


/-- Two binds of one computation agree where their continuations do. -/
theorem bind_ext {α β : Type} {m : Result α} {f g : α → Result β} (h : ∀ x, f x = g x) :
    m >>= f = m >>= g := by
  rw [funext h]

/-- **`check_main::olean_job` is `oleanJobStepSol`** at its solution, the job's position a
`usize`. -/
theorem olean_job_sol {F : Type} (inst : frontend.checker_io.CheckerFs F) (fsv : F)
    (tier : arena.store.PersTier) (w : arena.monad.AState) (c : frontend.olean.records.ValueCache)
    (mode : kernel.env.CheckMode) (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (pk : frontend.olean.spec.OleanPins)
    (values : alloc.vec.Vec frontend.olean.records.ModRef) (sp : frontend.olean.files.Roots)
    (sol : Option arena.justify.Solution) (k : Std.Usize) :
    driver.check_main.olean_job inst fsv tier w c mode pins ds pk values sp sol k =
      (do
        let (r, x) ← oleanJobStepSol inst fsv tier mode pins ds pk values sp sol (w, c) k.val
        ok (r, x.1, x.2)) := by
  rw [driver.check_main.olean_job, oleanJobStepSol, dite_eq_left k.hBounds]
  simp only [lift, bind_ok]
  have hk' : (UScalar.ofNatCore (ty := .Usize) k.val k.hBounds) = k := by
    apply UScalar.eq_of_val_eq; rw [UScalar.ofNatCore_val_eq]
  rw [hk']
  by_cases hk : k >= alloc.vec.Vec.len ds
  · have hn : ds.val[k.val]? = none := by
      apply List.getElem?_eq_none
      have := alloc.vec.Vec.len_val ds
      scalar_tac
    rw [ite_eq_left hk, hn]
    simp only [Std.bind_assoc]
    refine bind_ext (fun p => ?_); rcases p with ⟨_, _⟩; simp
  · have hlt : k.val < ds.val.length := by
      have := alloc.vec.Vec.len_val ds
      scalar_tac
    rw [ite_eq_right hk, ConRon.Args.vec_index_ok' hlt, bind_ok,
      List.getElem?_eq_getElem hlt]
    generalize ds.val[k.val] = d
    cases d with
    | ThmDecl cv v =>
      simp only [Std.bind_assoc]
      refine bind_ext (fun t => ?_)
      by_cases ht : t = arena.handle.ETAG_BVAR
      · simp only [ht, ite_true, Std.bind_assoc]
        refine bind_ext (fun code => ?_)
        rcases code with _ | code
        · simp only [Std.bind_assoc, Aeneas.Std.bind_ok, uncurry]
          refine bind_ext (fun p => ?_); rcases p with ⟨_, _⟩; simp
        · simp only [Std.bind_assoc, Aeneas.Std.bind_ok, uncurry]
          refine bind_ext (fun st1 => ?_)
          refine bind_ext (fun q => ?_); rcases q with ⟨r, ar, c1⟩
          rcases r with v1 | e1
          · simp only [Std.bind_assoc, Aeneas.Std.bind_ok, uncurry]
            refine bind_ext (fun cv' => ?_)
            refine bind_ext (fun q => ?_); rcases q with ⟨r2, st3⟩
            rcases r2 with _ | e2 <;> simp
          · simp
      · simp only [ht, ite_false, Std.bind_assoc, Aeneas.Std.bind_ok, uncurry]
        refine bind_ext (fun p => ?_); rcases p with ⟨_, _⟩; simp
    | _ =>
      simp only [Std.bind_assoc]
      refine bind_ext (fun p => ?_); rcases p with ⟨_, _⟩; simp
/-- **A job of the `.olean` pool, at a `Nat` position, is `oleanJobStepSol`** from the step's
first position: wherever the extracted step answers, the twin-facing step answers the same. -/
theorem olean_stepAt {I : Type} (inst : frontend.checker_io.CheckerFs I)
    (st : driver.check_main.OleanJobStep) (s : I) :
    ∀ x k r, stepAt
        (driver.check_main.OleanJobStep.Insts.Con_ron_coreFrontendChecker_ioStepFPairAStateValueCache
          inst) st s x k = ok r →
      oleanJobStepSol inst s st.tier st.mode st.pins st.ds st.pk st.values st.sp st.sol x
        (st.start.val + k) = ok r := by
  intro x k r h
  unfold stepAt at h
  split at h
  · rename_i hk
    simp only [driver.check_main.OleanJobStep.Insts.Con_ron_coreFrontendChecker_ioStepFPairAStateValueCache.step] at h
    obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r1, a1, vc1⟩, hj, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [olean_job_sol] at hj
    obtain ⟨⟨r2, x2⟩, hs, hj⟩ := ConRon.Refine.bind_eq_ok_iff.mp hj
    have hiv : i.val = st.start.val + k := by
      have := ConRon.Refine.Nat.uadd_val hi
      rw [this, UScalar.ofNatCore_val_eq]
    rw [hiv] at hs
    cases Result.ok_injective hj
    cases Result.ok_injective h
    exact hs
  · exact absurd h (by simp)


/-! ## The walk of `check_main::check_oleans` -/

section Walk

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **The names interned** (`check_main::intern_names`): the staged lemmas' `InternRoots`, at
well-formed names. -/
theorem intern_names_loop_roots {pers : arena.store.PersTier} {ns : alloc.vec.Vec kernel.name.Name}
    (hwf : ∀ n ∈ ns.val, ConRon.Refine.NameWF n) :
    ∀ (k : Nat) (i : Std.Usize) (st : arena.monad.AState) (out : alloc.vec.Vec arena.handle.NIdx),
      ns.val.length - i.val = k → i.val ≤ ns.val.length →
      ∀ {rs st'}, driver.check_main.intern_names_loop pers st ns out i = ok (.Ok rs, st') →
      ∃ hs, rs.val = out.val ++ hs ∧ InternRoots pers st (ns.val.drop i.val) hs st' := by
  intro k
  induction k with
  | zero =>
    intro i st out hk hi rs st' h
    rw [driver.check_main.intern_names_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], by simp, ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ k ih =>
    intro i st out hk hi rs st' h
    have hlt : i.val < ns.val.length := by omega
    rw [driver.check_main.intern_names_loop] at h
    rw [ite_eq_left (by scalar_tac), ConRon.Args.vec_index_ok' hlt, bind_ok] at h
    obtain ⟨⟨r, st1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e => simp at h
    | Ok hd =>
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hv : i2.val = i.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
      obtain ⟨hs, hrs, hir⟩ := ih i2 st1 out1 (by omega) (by omega) h
      refine ⟨hd :: hs, ?_, ?_⟩
      · rw [hrs, ConRon.Refine.vec_push_val hout1]; simp
      · rw [List.drop_eq_getElem_cons hlt]
        refine ⟨hwf _ (List.getElem_mem hlt), st1, hr, ?_⟩
        rw [← hv]; exact hir

theorem intern_names_roots {pers : arena.store.PersTier} {ns : alloc.vec.Vec kernel.name.Name}
    (hwf : ∀ n ∈ ns.val, ConRon.Refine.NameWF n) {st : arena.monad.AState} {rs st'}
    (h : driver.check_main.intern_names pers st ns = ok (.Ok rs, st')) :
    InternRoots pers st ns.val rs.val st' := by
  obtain ⟨hs, hrs, hir⟩ := intern_names_loop_roots hwf _ 0#usize st _ rfl (by simp) h
  simp only [alloc.vec.Vec.new] at hrs
  rw [hrs]
  simpa using hir

/-- **The check phase of an `.olean` run, accepted** (`check_main::check_phase_olean`): the
staged lemmas' `h6`, `h7` and `h8` — the index from the empty one, the tier frozen, and the worker
map's contract at the `.olean` job at the solution `sol` (`oleanJobStepSol`), its reads at the
state the map ran at; the thaw hands back the index and the index build's state. -/
theorem check_phase_olean_ok (hpool : PoolSound io) {s s' : S}
    {pers st mode ipins ds pk values sp sol jobs fr syn ix st'}
    (h : driver.check_main.check_phase_olean io s pers st mode ipins ds pk values sp sol jobs fr
      syn = ok (.Ok ix, s', st')) :
    ∃ st1 tier frozen,
      (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index pers st e ds 0#usize) = ok (.Ok ix, st1) ∧
      arena.checker.freeze_tier st1.store ix = ok (tier, frozen) ∧
      ParallelAll ds.length (oleanWorkerInit st1.pins)
        (oleanJobStepSol io.CheckerFsInst s tier mode ipins ds pk values sp sol) ∧
      st' = st1 := by
  rw [driver.check_main.check_phase_olean] at h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r, st1⟩, hbi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    have := Result.ok_injective h
    simp at this
  | Ok ix0 =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨workers, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨tier, frozen⟩, hfz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r1, io1⟩, hpar, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨ix1, e1⟩, hth, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [(freeze_tier_ok hfz).2] at hth
    have hth' := Result.ok_injective hth
    simp only [Prod.mk.injEq] at hth'
    obtain ⟨rfl, rfl⟩ := hth'
    cases r1 with
    | Err p =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have := Result.ok_injective h
      simp at this
    | Ok u =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hres := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hres
      obtain ⟨rfl, -, rfl⟩ := hres
      refine ⟨st1, tier, frozen, by rw [hii, bind_ok]; exact hbi, hfz, ?_, rfl⟩
      have hpa := hpool _ _ s _ _ io1 hpar
      rw [alloc.vec.Vec.len_val] at hpa
      refine parallelAll_mono rfl ?_ hpa
      intro x k r hk
      have := olean_stepAt io.CheckerFsInst _ s x k r hk
      simpa using this

/-- **What an exit 0 of `--olean` on a closure ran**: the step premises of
`oleans_model_of_stages_dec`, at the binary's start values, `--verified` and the embedded pins,
the reader at one state of the instance and the pool at another, both snapshots of `fs`. -/
inductive OleanStages (fs : ConLeche.FS) (names : List kernel.name.Name)
    (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)) : Prop where
  | intro {st1 st2 stR st4 st5 st6 : arena.monad.AState} {pre : frontend.prepare.PreludeIx}
      {roots : alloc.vec.Vec arena.handle.NIdx}
      {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
      {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
      {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
      {prepared : frontend.prepare.Prepared} {v : alloc.vec.Vec arena.env.IDeclaration}
      {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
      {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
      {ix : arena.stream_index.IStreamIndex} {tier : arena.store.PersTier}
      {frozen : arena.store.EStore}
      (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
      (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
      (hroots : InternRoots emptyTier st2 names roots.val stR)
      (hsnap : SnapshotOf finst fsv fs) (hsnap' : SnapshotOf finst' fsv' fs)
      (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store
        ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false = ok (.Ok rd, store3))
      (h4 : frontend.prepare.prepare_d
        frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts
        emptyTier { stR with store := store3 } pre rd.decls { rd with decls := v }
        = ok (.Ok prepared, st4))
      (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
      (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
      (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
      (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
      (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
        (oleanJobStep finst' fsv' tier .Verified ipins prepared.decls rd.pins rd.values
          ⟨dirs, alloc.vec.Vec.new _⟩)) :
      OleanStages fs names dirs

/-- `intern_consts` of no constant: none, the state as it was. -/
theorem intern_consts_nil {pers : arena.store.PersTier} {st : arena.monad.AState}
    {cs : alloc.vec.Vec kernel.name.Name} (hcs : cs.val = []) :
    driver.check_main.intern_consts pers st cs = ok (.Ok none, st) := by
  rw [driver.check_main.intern_consts]
  have : alloc.vec.Vec.len cs = 0#usize := by
    have := alloc.vec.Vec.len_val cs
    simp [alloc.vec.Vec.length, hcs] at this; scalar_tac
  rw [ite_eq_left this]

/-- An `.olean` read's failure is never exit 0. -/
theorem oleans_failed_ne {s s' : S} {e line roots v} {c : Std.U8}
    (h : driver.check_main.oleans_failed io s e line roots v = ok (c, s')) : c.val ≠ 0 := by
  rw [driver.check_main.oleans_failed] at h
  obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have := Result.ok_injective h
  simp only [Prod.mk.injEq] at this
  rw [← this.1]
  exact exit_code_ne hc0

/-- **The check of a closure, 0** (`check_main::check_oleans` at `--verified`, the embedded
pins, no `--constant`): its calls are the step premises (`OleanStages`). -/
theorem check_oleans_zero (hfs : AnswersAs io fs) (hpool : PoolSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {roots cs : alloc.vec.Vec kernel.name.Name} (hcs : cs.val = [])
    (hwf : ∀ n ∈ roots.val, ConRon.Refine.NameWF n)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {c : Std.U8}
    (h : driver.check_main.check_oleans io s a roots cs ⟨dirs, alloc.vec.Vec.new _⟩ = ok (c, s'))
    (hc : c.val = 0) : OleanStages fs roots.val dirs := by
  rw [driver.check_main.check_oleans] at h
  simp only [hver, ite_true, bind_ok] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r0, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok u =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r1, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok pre =>
  obtain ⟨⟨r2, st3⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => exact (oleans_failed_ne h hc).elim
  | Ok rs =>
  simp only [intern_consts_nil hcs, bind_ok] at h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨read, e3⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases read with
  | Err p =>
    obtain ⟨e, line⟩ := p
    exact (oleans_failed_ne h hc).elim
  | Ok rd =>
  simp only [core.mem.replace] at h
  obtain ⟨⟨r4, st4⟩, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r4 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok prepared =>
  have h := hoisted_bind h
  obtain ⟨o, hpr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | none => exact (code_ne h (by decide) hc).elim
  | some ps =>
  have hpins := embedded_pins_ok hpr
  obtain ⟨⟨r5, st5⟩, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r5 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok ipins =>
  obtain ⟨⟨jobs, io2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨verdict, io3, st8⟩, hph, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ix, rfl⟩ := verdict_of_zero h hc
  obtain ⟨st6, tier, frozen, h6, h7, h8, -⟩ := check_phase_olean_ok hpool hph
  exact OleanStages.intro h1 h2 (intern_names_roots hwf hr2) (hfs s) (hfs io2) h3 h4 hpins h5
    h6 h7 h8

end Walk

/-! ## The argument list `["--olean", "--search-path=" ++ dirs, "--", root]` -/

/-- `--search-path=` ++ `dirs` as code points: the prefix, then the directories'. -/
theorem search_word {w : alloc.vec.Vec Std.U32} {dirs : String}
    (hw : w.val.map UScalar.val = ("--search-path=" ++ dirs).toList.map Char.toNat) :
    ∃ T : List Std.U32, w.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32,
      104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T := by
  rw [String.toList_append, List.map_append] at hw
  obtain ⟨l1, l2, hl, h1, -⟩ := List.map_eq_append_iff.mp hw
  refine ⟨l2, ?_⟩
  have hp : "--search-path=".toList.map Char.toNat = ([45#u32, 45#u32, 115#u32, 101#u32, 97#u32,
      114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] : List Std.U32).map
      UScalar.val := by decide
  rw [hl, vals_eq (h1.trans hp)]

/-- `push_files` copies the arguments from `i` on, after `out`. -/
theorem push_files_loop_val (argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)) :
    ∀ (k : Nat) (out : alloc.vec.Vec (alloc.vec.Vec Std.U32)) (i : Std.Usize),
      argv.val.length - i.val = k → ∀ {v}, driver.cli.push_files_loop argv out i = ok v →
      v.val.map (·.val) = out.val.map (·.val) ++ (argv.val.drop i.val).map (·.val) := by
  intro k
  induction k with
  | zero =>
    intro out i hk v h
    rw [driver.cli.push_files_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by omega)]
    simp
  | succ k ih =>
    intro out i hk v h
    have hlt : i.val < argv.val.length := by omega
    rw [driver.cli.push_files_loop] at h
    rw [ite_eq_left (by scalar_tac), ConRon.Args.vec_index_ok' hlt, bind_ok] at h
    obtain ⟨w, hw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi3v := add_ok_val hi3
    rw [ih out1 i3 (by simp at hi3v; omega) h, push_val hout1, hi3v,
      List.drop_eq_getElem_cons (i := i.val) hlt]
    simp only [List.map_append, List.map_cons, List.map_nil, str_copy_val hw, List.append_assoc,
      List.singleton_append]
    rfl

/-- **The module names parsed** (`cli::parse_mod_names`): each file's `parse_mod_name`. -/
theorem parse_mod_names_loop_val (fs : alloc.vec.Vec (alloc.vec.Vec Std.U32)) :
    ∀ (k : Nat) (out : alloc.vec.Vec kernel.name.Name) (i : Std.Usize),
      fs.val.length - i.val = k → i.val ≤ fs.val.length → ∀ {rs},
      driver.cli.parse_mod_names_loop fs out i = ok (.Ok rs) →
      ∃ ns, rs.val = out.val ++ ns ∧
        List.Forall₂ (fun f n => frontend.olean.files.parse_mod_name f = ok (some n))
          (fs.val.drop i.val) ns := by
  intro k
  induction k with
  | zero =>
    intro out i hk hi rs h
    rw [driver.cli.parse_mod_names_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    refine ⟨[], by simp, ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    exact List.Forall₂.nil
  | succ k ih =>
    intro out i hk hi rs h
    have hlt : i.val < fs.val.length := by omega
    rw [driver.cli.parse_mod_names_loop] at h
    rw [ite_eq_left (by scalar_tac), ConRon.Args.vec_index_ok' hlt, bind_ok] at h
    obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases o with
    | none =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp at h
    | some n =>
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hv : i2.val = i.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
      obtain ⟨ns, hrs, hfa⟩ := ih out1 i2 (by omega) (by omega) h
      refine ⟨n :: ns, ?_, ?_⟩
      · rw [hrs, ConRon.Refine.vec_push_val hout1]; simp
      · rw [List.drop_eq_getElem_cons hlt]
        rw [hv] at hfa
        exact List.Forall₂.cons ho hfa

/-- `parse_const_names` of no constant: none. -/
theorem parse_const_names_nil {cs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} (hcs : cs.val = []) :
    ∃ r : alloc.vec.Vec kernel.name.Name, driver.cli.parse_const_names cs = ok (.Ok r) ∧
      r.val = [] := by
  refine ⟨alloc.vec.Vec.new _, ?_, rfl⟩
  rw [driver.cli.parse_const_names, driver.cli.parse_const_names_loop]
  have : ¬ (0#usize : Std.Usize) < alloc.vec.Vec.len cs := by
    have := alloc.vec.Vec.len_val cs
    simp [alloc.vec.Vec.length, hcs] at this; scalar_tac
  rw [ite_eq_right this]

/-- A `usize` sum of literals. -/
theorem usize_add_lit {a b : Std.Usize} (h : a.val + 1 = b.val) : a + 1#usize = ok b := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Std.Usize.add_spec (x := a) (y := 1#usize)
    (by have := b.hBounds; scalar_tac))
  rw [hy]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hyv, ← h]
  rfl

/-- **The parse of `["--olean", "--search-path=" ++ dirs, "--", root]`**: `--olean`, the
search path the directories, the one file `root`, every other default. -/
theorem parse_args_oleans {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 w1 w2 w3 : alloc.vec.Vec Std.U32} {T : List Std.U32}
    (hv : argv.val = [w0, w1, w2, w3])
    (h0 : w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32])
    (h1 : w1.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32,
      112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T)
    (h2 : w2.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = true ∧ a.compare = false ∧
      a.scheduled = false ∧ a.modular = false ∧ a.module = false ∧
      a.verified = true ∧ a.trusted_path.val = [] ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) w1 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [w3.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some w2 := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_olean g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_search g1 h1 (usize_add_lit (b := 2#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g2 h2 (usize_add_lit (b := 3#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 3#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsp, ?_⟩
  simpa using hf

section Run

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- A usage error is never exit 0. -/
theorem usage_ne {s s' : S} {b : driver.cli.Bad} {c : Std.U8}
    (h : (do io.usage s b; ok (3#u8, s)) = ok (c, s')) (hc : c.val = 0) : False := by
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact code_ne h (by decide) hc

/-- **`--olean` on one root, at exit 0** (`cli::olean_args`, no `--module`, `--modular`,
`--trusted-search-path` or `--constant`): the root parsed, the closure checked along a copy of
the search path. -/
theorem olean_args_oleans {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = false)
    (hsch : a.scheduled = false) (hmod : a.modular = false)
    (hmo : a.module = false) (htp : a.trusted_path.val = []) (hcon : a.constants.val = [])
    {f : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f]) {c : Std.U8}
    (h : driver.cli.olean_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (roots cs : alloc.vec.Vec kernel.name.Name) (nm : kernel.name.Name)
      (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      roots.val = [nm] ∧ frontend.olean.files.parse_mod_name f = ok (some nm) ∧ cs.val = [] ∧
      dirs.val.map (·.val) = a.search_path.val.map (·.val) ∧
      driver.check_main.check_oleans io s a roots cs ⟨dirs, alloc.vec.Vec.new _⟩ = ok (c, s') := by
  rw [driver.cli.olean_args] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases b with
  | true => exact (usage_ne h hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => exact (usage_ne h hc).elim
  | Ok rs =>
  obtain ⟨ns, hrs, hfa⟩ := parse_mod_names_loop_val a.files _ _ 0#usize rfl (by simp) hr
  rw [hfiles] at hfa
  obtain ⟨nm, hnm, hns⟩ : ∃ nm, frontend.olean.files.parse_mod_name f = ok (some nm) ∧ ns = [nm] := by
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hfa
    rcases hfa with _ | ⟨hx, hrest⟩
    cases hrest
    exact ⟨_, hx, rfl⟩
  obtain ⟨cs, hcs, hcsv⟩ := parse_const_names_nil hcon
  simp only [hcs, Aeneas.Std.bind_ok, hcmp, Bool.false_eq_true, ite_false] at h
  have htm : driver.cli.trusted_misplaced a = ok false := by
    rw [driver.cli.trusted_misplaced]
    have : alloc.vec.Vec.len a.trusted_path = 0#usize := by
      have := alloc.vec.Vec.len_val a.trusted_path
      simp [alloc.vec.Vec.length, htp] at this; scalar_tac
    rw [ite_eq_left this]
  simp only [htm, bind_ok, Bool.false_eq_true, ite_false, hsch, hmod, hmo] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [frontend.olean.files.roots_of_path] at hsp
  cases Result.ok_injective hsp
  refine ⟨rs, cs, nm, v, by rw [hrs, hns]; rfl, hnm, hcsv, ?_, h⟩
  have := push_files_loop_val a.search_path _ _ 0#usize rfl hv
  simpa using this

/-- Two lists of paths with the same code points name the same directories. -/
theorem absSearchPath_of_vals {d d' : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (h : d.val.map (·.val) = d'.val.map (·.val)) : absSearchPath d = absSearchPath d' := by
  have : absSearchPath d = (d.val.map (·.val)).map
      (fun l => (⟨String.ofList (l.map fun c => Char.ofNat c.val)⟩ : System.FilePath)) := by
    simp [absSearchPath, ConRon.Refine.absString]
  rw [this, h]
  simp [absSearchPath, ConRon.Refine.absString]

/-- `["--olean", "--search-path=" ++ dirs, "--", root]`'s `argv`. -/
theorem argv_oleans {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (h : ArgvOf argv ["--olean", "--search-path=" ++ dirs, "--", root]) :
    ∃ w0 w1 w2 w3, argv.val = [w0, w1, w2, w3] ∧
      w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] ∧
      w1.val.map UScalar.val = ("--search-path=" ++ dirs).toList.map Char.toNat ∧
      w2.val = [45#u32, 45#u32] ∧ w3.val.map UScalar.val = root.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, l⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨w0, w1, w2, w3, rfl, vals_eq (h0.trans (by decide)), h1, vals_eq (h2.trans (by decide)),
    h3⟩

/-- **An exit 0 of `["--olean", "--search-path=" ++ dirs, "--", root]`** (`cli::run_args`): the
root is a module name the Rust parsed, the search path `dirs`'s directories, and the run's
calls the step premises (`OleanStages`). -/
theorem run_args_oleans (hfs : AnswersAs io fs) (hpool : PoolSound io)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (hargv : ArgvOf argv ["--olean", "--search-path=" ++ dirs, "--", root]) {s s' : S}
    {c : Std.U8} (h : driver.cli.run_args io s argv = ok (c, s')) (hc : c.val = 0) :
    ∃ (nm : kernel.name.Name) (dv : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      ConLeche.Frontend.Olean.parseModName root = some (ConRon.Refine.absName nm) ∧
      absSearchPath dv = ConLeche.Driver.searchPathOf dirs ∧ OleanStages fs [nm] dv := by
  obtain ⟨w0, w1, w2, w3, hv, h0, h1, h2, h3⟩ := argv_oleans hargv
  obtain ⟨T, hT⟩ := search_word h1
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some w2 := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word g1 (by rw [hT]; simp) (by rw [hT]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_end g2 h2]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, htp, hcon, hsp, hfl⟩ :=
    parse_args_oleans hv h0 hT h2 ha
  simp only [hbad, hcg, hol, hcmp, hsch, hmod, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f', hf', hf'v⟩ : ∃ f', a.files.val = [f'] ∧ f'.val = w3.val := by
    rcases hfv : a.files.val with _ | ⟨f', _ | ⟨g, l⟩⟩ <;> rw [hfv] at hfl <;> simp at hfl
    exact ⟨f', rfl, hfl⟩
  obtain ⟨roots, cs, nm, dv, hroots, hnm, hcs, hdv, hck⟩ :=
    olean_args_oleans hcmp hsch hmod hmo htp hcon hf' h hc
  have hf3 : f'.val.map UScalar.val = root.toList.map Char.toNat := by rw [hf'v]; exact h3
  obtain ⟨hwf, hpm⟩ := ConRon.Args.parse_mod_name_some hf3 hnm
  have hst := check_oleans_zero hfs hpool hver hcs
    (by rw [hroots]; intro n hn; simp at hn; subst hn; exact hwf) hck hc
  rw [hroots] at hst
  refine ⟨nm, dv, hpm, ?_, hst⟩
  rw [absSearchPath_of_vals hdv]
  exact ConRon.Args.push_dirs_search h1 hsp

end Run

/-- **`main_oleans`'s conclusion from an exit 0**: the closure of the root, along the search
path `dirs`, has a model. -/
theorem oleans_of_canGive (V : Type w) [ConLeche.SetTheory V] {dirs root : String}
    {r : ConLeche.Name} {fs : ConLeche.FS}
    (hr : ConLeche.Frontend.Olean.parseModName root = some r)
    (h : CanGiveConforming ["--olean", "--search-path=" ++ dirs, "--", root] fs 0) :
    ∃ model, IsModel V model (closureConstants (ConLeche.Driver.searchPathOf dirs) fs #[r]) := by
  obtain ⟨S, io, s, s', argv, c, hfs, hpool, -, hargv, hrun, hc⟩ := h
  obtain ⟨nm, dv, hp, hsp, hst⟩ := run_args_oleans hfs hpool hargv hrun (by simpa using hc)
  have hnm : ConRon.Refine.absName nm = r := Option.some.inj (hp.symm.trans hr)
  cases hst with
  | intro h1 h2 hroots hsnap hsnap' h3 h4 hpins h5 h6 h7 h8 =>
    have := oleans_model_of_stages_dec V h1 h2 hroots hsnap hsnap' h3 h4 hpins h5 h6 h7 h8
    rw [hsp] at this
    simpa [hnm] using this

end ConRon.MainTheorem
