import ConRon.MainTheorem.ModArgs

/-!
# `ConRon.MainTheorem.Modular` — the walks of `--check-graph`, `--olean --module` and
`--olean --modular`

**Task #171, slice 2** (DESIGN.md §3.9).  An exit 0 of the graph check is
`Stages.rust_graph`'s premises (`GraphStages`), an exit 0 of a module's worker is
`rust_worker_gen2`'s (`WorkerStages`: `Stages.rust_worker_gen` with the worker's reads and its
jobs each at a state of its own instance, a snapshot of `fs`), and an exit 0 of
`--olean --modular` is the graph's premises, its modules read back (`rust_graph_names`) and at
every one a worker's premises, reads and jobs at the code map's state (`ModularStages`).
`modular_of_stages` and `modular_one_of_stages` compose them as `Stages.model_modular_of`
does, with upstream's `closure_sees_isModel`: con-leche's `main_modular` and
`main_modular_one`.

| lemma | what it walks |
|---|---|
| `graph_start_ok`, `check_graph_zero`, `check_graph_args_zero`, `run_args_graph` | `graph::graph_start`, `graph::check_graph`, `cli::check_graph_args`, `cli::run_args` |
| `module_read_ok`, `module_phase_ok`, `module_verdict_zero`, `check_module_zero` | `worker::module_read`, `module_phase`, `module_verdict`, `check_module` |
| `olean_args_module`, `run_args_module` | `cli::olean_args` → `module_args`, `cli::run_args` |
| `jobs_in_order_loop_fold`, `parallelAll_of_fold`, `module_phase_in_ok`, `check_module_in_zero` | a module of `--modular`: its jobs in order are the pool's contract at one worker |
| `graph_names_loop_val`, `rust_graph_names` | `modular::graph_names`: the modules read back are the closure's |
| `first_failure_none`, `modular_verdict_zero`, `check_modular_zero` | `modular::modular_verdict`, `check_modular`, through `CodesSound` |
| `olean_args_modular`, `run_args_modular` | `cli::olean_args` → `modular_args`, `cli::run_args` |
| `modular_of_canGive`, `modular_one_of_canGive` | `main_modular`'s and `main_modular_one`'s proofs |
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.MainTheorem.Stages
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

namespace ConRon.MainTheorem

set_option autoImplicit false

universe w

/-! ## A worker at two instances -/

section Worker2

/-- `Stages.rust_worker_gen` with the worker's reads and its pool's at two instances, each a
snapshot of `F`: the run's one module reads at one state of the instance and puts its jobs on the
worker map at a later one. -/
theorem rust_worker_gen2 (hR : ConRon.Bridge.Modular.ReachRunHyp)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
    (hsnap' : SnapshotOf finst' fsv' F)
    {sp : frontend.olean.files.Roots} (hsp : (absRoots sp).bare = absRoots sp)
    {mName : kernel.name.Name} {rest : List kernel.name.Name}
    {st1 st2 st3 st4 st5 : arena.monad.AState} {m : arena.handle.NIdx} {hs : List arena.handle.NIdx}
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {xC : Array ConLeche.Frontend.Olean.ImportRec}
    (hx : ∀ st : ConRon.Arena.EStore, ConRon.Bridge.Frontend.ListRel
        (ConRon.Bridge.Frontend.Olean.NR st) (absNIdx m :: hs.map absNIdx)
        (ConRon.Refine.absName mName :: rest.map ConRon.Refine.absName) →
      ConRon.Bridge.Frontend.Olean.ImpsD st (absImports x) xC)
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (hroot : InternRoots emptyTier st1 (mName :: rest) (m :: hs) st2)
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3))
    {w : frontend.modular.worker.WorkerRead}
    (hwork : frontend.modular.worker.worker_read finst fsv emptyTier st3 sp ipins m x
      = ok (.Ok w, st4))
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    (hds : frontend.modular.worker.worker_decls w = ok ds)
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st5.store ix = ok (tier, frozen))
    {ws ws' : arena.monad.AState}
    (hws : arena.checker.worker_state st5.pins = ok ws)
    (hinfer : frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws'))
    (h8 : ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
      (fun c k => oleanJobStepSol finst' fsv' tier .Verified ipins ds w.pins w.values
        sp none c (w.start.val + k))) :
    ConLeche.Driver.WorkerAccepted (ConRon.Refine.absPins pins) (absRoots sp) F
      (ConRon.Refine.absName mName) 1 xC := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := emptyTier) rfl hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ := (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨sB, hB, hrelB, hinvB⟩ := internRoots_refines (mName :: rest) (m :: hs) hroot hrelA hinvA
  obtain ⟨sC, hC, hrelC, hinvC⟩ :=
    (intern_all_pins_refines hrelB hinvB (ConRon.Refine.PinsWF.decode_wf_refine2 hpins) h5).dest
  have hfs := fsRel_of_snapshot hsnap
  obtain ⟨w', sD, hD, hwr, hrelD, hinvD⟩ :=
    ConRon.Refine2.Modular.worker_read_refines hfs emptyTier_base.1 emptyTier_base.2 hrelC hinvC
      _ ipins m x w st4 hwork
  have hdecls := ConRon.Refine2.Modular.worker_decls_eq hwr.reach.ctx.symm hwr.own.symm hds
  -- the index, the freeze, the fresh worker, the inferred flags
  rw [stream_index_empty_eq, bind_ok] at h6
  obtain ⟨I, sE, hE, hrelE, hinvE, hIrel, hIfr⟩ := build_index_empty_refines hrelD hinvD h6
  obtain ⟨htier, -⟩ := freeze_tier_ok h7
  subst htier
  obtain ⟨hidle, hinvW⟩ := worker_state_rel ix hrelE hinvE rfl hws
  obtain ⟨w₁, hF, -, -⟩ := ConRon.Refine2.Modular.infer_flags_la hidle hinvW rfl ⟨hIrel, hIfr⟩
    (hwr.reach.pending.imp fun _ _ h => h) hinfer
  -- the pool
  obtain ⟨I', sE', hP, -, -, -⟩ := olean_pool_accepts_from_sol_refines (values' := w'.values)
    (sol := none) (J := none) trivial (fsRel_of_snapshot hsnap') hwr.values hrelD hinvD rfl
    (oleanPoolAcceptsFromSol_intro (by rw [stream_index_empty_eq, bind_ok]; exact h6) h7 h8)
  -- one index: the build is a function
  obtain ⟨parts, hbuild, hrest⟩ := hP
  have hEq := hbuild.symm.trans hE
  simp only [Except.ok.injEq, Prod.mk.injEq] at hEq
  obtain ⟨hI1, hI2⟩ := hEq
  rw [hI1, hI2] at hbuild hrest
  have hdecls' : (absIDeclL ds).toArray = ConRon.Arena.Modular.workerDecls w' := hdecls
  rw [hdecls'] at hbuild hrest
  rw [← hwr.pins, ← hwr.start] at hrest
  have hP' : ConRon.Arena.PooledOleanAcceptsFromJ (ConRon.Bridge.Frontend.Olean.modelFs F) w'.pins
      (absRoots sp) w'.values .verified (absINatOpPinSetL ipins) none
      w'.start (ConRon.Arena.Modular.workerDecls w') sD I sE :=
    ⟨parts, hbuild, hrest⟩
  have hctxE : (absIDeclL w.reach.ctx).toArray = w'.reach.ctx := hwr.reach.ctx.symm
  rw [hctxE] at hF
  exact ConRon.Bridge.Modular.workerStage_run ConRon.Bridge.CoreSpec.of_core
    ConRon.Bridge.Inductives.indSpec_of_bridge ConRon.Bridge.Modular.Home.homeHyp_holds hR hsp
    (names := rest.map ConRon.Refine.absName) (hs := hs.map absNIdx) hA
    (by simpa only [List.map_cons] using hB) (fun h => hx _ h) hC hD hP' hF


end Worker2

/-! ## The jobs of a module of `--modular`, in order -/

/-- **The jobs in order** (`worker::jobs_in_order`), all accepted: a fold of the `.olean` job
over the positions from `k` below `n`, every step `Ok`. -/
theorem jobs_in_order_loop_fold {F : Type} (inst : frontend.checker_io.CheckerFs F) (fsv : F)
    (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (pk : frontend.olean.spec.OleanPins)
    (values : alloc.vec.Vec frontend.olean.records.ModRef) (sp : frontend.olean.files.Roots)
    (start n : Std.Usize) :
    ∀ (m : Nat) (k : Std.Usize) (w : arena.monad.AState) (c : frontend.olean.records.ValueCache),
      n.val - k.val = m → ∀ {w' c'},
      driver.worker.jobs_in_order_loop inst fsv tier w c mode pins ds pk values sp start n k
        = ok (.Ok (), w', c') →
      FoldAllOk (fun x j => oleanJobStepSol inst fsv tier mode pins ds pk values sp none x
        (start.val + j)) (w, c) (List.range' k.val (n.val - k.val)) := by
  intro m
  induction m with
  | zero =>
    intro k w c hm w' c' h
    rw [show n.val - k.val = 0 from hm]
    trivial
  | succ m ih =>
    intro k w c hm w' c' h
    rw [driver.worker.jobs_in_order_loop] at h
    rw [ite_eq_left (by scalar_tac)] at h
    obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, w1, c1⟩, hj, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e => simp at h
    | Ok u =>
      obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hiv : i.val = start.val + k.val := ConRon.Refine.Nat.uadd_val hi
      have hk1v : k1.val = k.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hk1; simpa using this
      rw [olean_job_sol] at hj
      obtain ⟨⟨r2, x2⟩, hs, hj⟩ := ConRon.Refine.bind_eq_ok_iff.mp hj
      have hj' : (r2, x2.1, x2.2) = (core.result.Result.Ok u, w1, c1) := Result.ok_injective hj
      simp only [Prod.mk.injEq] at hj'
      obtain ⟨rfl, hw1, hc1⟩ := hj'
      subst hw1 hc1
      rw [show n.val - k.val = (n.val - k1.val) + 1 by omega, List.range'_succ]
      refine ⟨x2, ?_, ?_⟩
      · cases u; show oleanJobStepSol inst fsv tier mode pins ds pk values sp none (w, c) (start.val + k.val) = _
        rw [← hiv]; exact hs
      · have := ih k1 x2.1 x2.2 (by omega) h
        rw [hk1v] at this
        rw [show n.val - (k.val + 1) = n.val - k1.val by omega] at this
        simpa using this

/-- One worker's fold over `0..n` is the pool's contract at `n`. -/
theorem parallelAll_of_fold {S E : Type} {n : Nat} {init : Result S} {s₀ : S}
    {step : S → Nat → Result (core.result.Result Unit E × S)} (hi : init = ok s₀)
    (h : FoldAllOk step s₀ (List.range' 0 n)) : ParallelAll n init step :=
  ⟨[List.range' 0 n], fun k hk => ⟨_, List.mem_singleton_self _, by simp; omega⟩,
    fun w hw => by
      rw [List.mem_singleton] at hw
      subst hw
      exact ⟨List.pairwise_lt_range', s₀, hi, h⟩⟩

/-! ## The graph check -/

section Graph

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **The graph check's start, accepted** (`graph::graph_start`): the reserved pins, the
reader's pins; the instance's state as it was. -/
theorem graph_start_ok {s s' : S} {pk : frontend.olean.spec.OleanPins} {st' : arena.monad.AState}
    (h : driver.graph.graph_start io s emptyTier startState = ok (.Ok pk, s', st')) :
    ∃ g1 gstore2, arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1) ∧
      frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2) ∧
      st' = { g1 with store := gstore2 } ∧ s' = s := by
  rw [driver.graph.graph_start] at h
  obtain ⟨⟨r, g1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  | Ok u =>
    obtain ⟨⟨r1, e⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r1 with
    | Err e1 =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact absurd (Result.ok_injective h) (by simp)
    | Ok pk' =>
      have h := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨g1, e, h1, h2, rfl, rfl⟩

/-- A graph walk's failure is never exit 0. -/
theorem graph_failed_ne {s s' : S} {e} {c : Std.U8}
    (h : driver.graph.graph_failed io s e = ok (c, s')) : c.val ≠ 0 := by
  rw [driver.graph.graph_failed] at h
  obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have := Result.ok_injective h
  simp only [Prod.mk.injEq] at this
  rw [← this.1]
  exact exit_code_ne hc0

/-- The graph check's start, failed: an exit code that is not 0. -/
theorem graph_start_err {s s' : S} {pers : arena.store.PersTier} {st st' : arena.monad.AState}
    {c0 : Std.U8} (h : driver.graph.graph_start io s pers st = ok (.Err c0, s', st')) :
    c0.val ≠ 0 := by
  rw [driver.graph.graph_start] at h
  obtain ⟨⟨r, g1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at h
    rw [← h.1]; decide
  | Ok u =>
    obtain ⟨⟨r1, e⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r1 with
    | Err e1 =>
      obtain ⟨⟨i, io1⟩, hgf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h
      rw [← h.1]; exact graph_failed_ne hgf
    | Ok pk => simp at h

/-- **The graph's modules read back** (`modular::graph_names`): each node's name, as the twin
denotes the node, well formed. -/
theorem graph_names_loop_val {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : ConRon.Arena.AState} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (c : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))) :
    ∀ (k : Nat) (out : alloc.vec.Vec kernel.name.Name) (i : Std.Usize)
      (CC : List ConLeche.Driver.Graph.Node), c.val.length - i.val = k → i.val ≤ c.val.length →
      ConRon.Bridge.Frontend.ListRel (ConRon.Bridge.Modular.NodeD lst.store)
        ((c.val.drop i.val).map ConRon.Refine2.Modular.absNode) CC →
      (∀ n ∈ out.val, ConRon.Refine.NameWF n) →
      ∀ {ns}, driver.modular.graph_names_loop pers st c out i = ok (.Ok ns) →
      ns.val.map ConRon.Refine.absName = out.val.map ConRon.Refine.absName ++ CC.map (·.1) ∧
        ∀ n ∈ ns.val, ConRon.Refine.NameWF n := by
  intro k
  induction k with
  | zero =>
    intro out i CC hk hi hlr hwf ns h
    rw [driver.modular.graph_names_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by omega)] at hlr
    cases hlr
    exact ⟨by simp, hwf⟩
  | succ k ih =>
    intro out i CC hk hi hlr hwf ns h
    have hlt : i.val < c.val.length := by omega
    rw [driver.modular.graph_names_loop] at h
    rw [ite_eq_left (by scalar_tac), ConRon.Args.vec_index_ok' hlt, bind_ok] at h
    obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [List.drop_eq_getElem_cons hlt, List.map_cons] at hlr
    cases hlr with
    | cons hd htl =>
    rename_i eC CC'
    have hrn := read_name_abs₀ hrel hr
    have hd1 : ConRon.Arena.denoteN lst.store.ns (absNIdx (c.val.get ⟨i.val, hlt⟩).1) = some eC.1 :=
      hd.1
    rw [hd1] at hrn
    obtain ⟨y, rfl, hy⟩ := hrn
    have hwy := ConRon.Refine2.Lockstep.read_name_wf hinv hr
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hv : i2.val = i.val + 1 := by
      have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
    rw [← hv] at htl
    have hwf1 : ∀ n ∈ out1.val, ConRon.Refine.NameWF n := by
      rw [ConRon.Refine.vec_push_val hout1]
      intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hwf n hn
      · simp at hn; subst hn; exact hwy
    obtain ⟨hns, hnw⟩ := ih out1 i2 CC' (by omega) (by omega) htl hwf1 h
    refine ⟨?_, hnw⟩
    rw [hns, ConRon.Refine.vec_push_val hout1]
    simp [hy]

/-- **The graph check at the Rust, its modules read back** (`modular::check_modular`'s first
step): `Stages.rust_graph`'s facts, the closure's modules the names `graph_names` read. -/
theorem rust_graph_names {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {names : List kernel.name.Name}
    {st1 stR : arena.monad.AState} {store2 store3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {roots : alloc.vec.Vec arena.handle.NIdx}
    {c : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (hpk : frontend.olean.spec.olean_pins emptyTier st1.store = ok (.Ok pk, store2))
    (hroots : InternRoots emptyTier { st1 with store := store2 } names roots.val stR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier stR.store
      ⟨dirs, alloc.vec.Vec.new _⟩ roots none = ok (.Ok c, store3))
    {ns : alloc.vec.Vec kernel.name.Name}
    (hns : driver.modular.graph_names emptyTier { stR with store := store3 } c = ok (.Ok ns)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ CC, ConLeche.ModelIO.CanGive
        (ConLeche.Frontend.Olean.moduleImports (absSearchPath dirs) e.1) F (.ok e.2)) ∧
      (∀ r ∈ names.map ConRon.Refine.absName, r ∈ CC.map (·.1)) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure (absSearchPath dirs) F
        (names.map ConRon.Refine.absName) e.1) ∧
      CC.map (·.1) = ns.val.map ConRon.Refine.absName ∧ ∀ n ∈ ns.val, ConRon.Refine.NameWF n := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := emptyTier) rfl hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ := (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨pk', sB, hB, rfl, hrelB, hinvB⟩ := olean_pins_refines hrelA hinvA _ _ hpk
  obtain ⟨sC, hC, hrelC, hinvC⟩ := internRoots_refines names roots.val hroots hrelB hinvB
  obtain ⟨C, sD, hD, rfl, hrelD, hinvD⟩ :=
    ConRon.Refine2.Modular.graph_of_refines (fsRel_of_snapshot hsnap) hrelC hinvC _ _ hgraph
  obtain ⟨CC, rk, hlr, good, hr, edges, inj, hhdr⟩ :=
    ConRon.Bridge.Modular.graphStage_run_nodes rfl hA hB hC hD
  refine ⟨CC, rk, good, hr, edges, inj, hhdr, ?_⟩
  obtain ⟨hn, hw⟩ := graph_names_loop_val (st := { stR with store := store3 }) hrelD hinvD c _ _
    0#usize CC rfl (by simp) (by simpa using hlr) (by simp [alloc.vec.Vec.new]) hns
  exact ⟨by rw [hn]; simp, hw⟩

/-- **What an exit 0 of the graph check ran**: the premises of `Stages.rust_graph`. -/
inductive GraphStages (fs : ConLeche.FS) (names : List kernel.name.Name)
    (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)) : Prop where
  | intro {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
      {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
      {pk : frontend.olean.spec.OleanPins} {groots : alloc.vec.Vec arena.handle.NIdx}
      {c : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
      (hsnap : SnapshotOf finst fsv fs)
      (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
      (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
      (hroots : InternRoots emptyTier { g1 with store := gstore2 } names groots.val gR)
      (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store
        ⟨dirs, alloc.vec.Vec.new _⟩ groots none = ok (.Ok c, gstore3)) :
      GraphStages fs names dirs

/-- **The graph check, 0** (`graph::check_graph`): its calls are `rust_graph`'s premises. -/
theorem check_graph_zero (hfs : AnswersAs io fs) {s s' : S}
    {roots : alloc.vec.Vec kernel.name.Name} (hwf : ∀ n ∈ roots.val, ConRon.Refine.NameWF n)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {c : Std.U8}
    (h : driver.graph.check_graph io s ⟨dirs, alloc.vec.Vec.new _⟩ roots = ok (c, s'))
    (hc : c.val = 0) : GraphStages fs roots.val dirs := by
  rw [driver.graph.check_graph] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r, io1, st1⟩, hgs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err c0 =>
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    rw [← this.1] at hc
    exact (graph_start_err hgs hc).elim
  | Ok pk =>
  obtain ⟨g1, gstore2, h1g, hpk, hst1, -⟩ := graph_start_ok hgs
  obtain ⟨⟨r1, st2⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok rs =>
  obtain ⟨⟨r2, gstore3⟩, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok cc =>
  rw [hst1] at hr1
  exact GraphStages.intro (hfs io1) h1g hpk (intern_names_roots hwf hr1) hg

end Graph

/-! ## A module's worker -/

section Worker

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **What a worker checks, read** (`worker::module_read`): the pins interned, phases 1-4, the
jobs' records. -/
theorem module_read_ok {F : Type} {finst : frontend.checker_io.CheckerFs F}
    {wn : frontend.checker_io.WorkerNotes F} {fsv : F} {pers : arena.store.PersTier}
    {st st' : arena.monad.AState} {sp : frontend.olean.files.Roots} {m : arena.handle.NIdx}
    {mName : kernel.name.Name} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {maxNatSize : ron.nat.Nat} {verified : Bool} {who : Option kernel.name.Name}
    {pace : frontend.pace.Pace} {w : frontend.modular.worker.WorkerRead}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    (h : driver.worker.module_read finst wn fsv pers st sp m mName x pins maxNatSize verified who
      pace = ok (.Ok (w, ipins, ds), st')) :
    ∃ st1, arena.checker.intern_all_pins pers st pins maxNatSize = ok (.Ok ipins, st1) ∧
      frontend.modular.worker.worker_read finst fsv pers st1 sp ipins m x
        = ok (.Ok w, st') ∧
      frontend.modular.worker.worker_decls w = ok ds := by
  rw [driver.worker.module_read] at h
  obtain ⟨⟨r, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  | Ok p =>
  obtain ⟨⟨r1, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  | Ok w' =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨st3, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hst3 : st3 = st2 := by
    split at h3
    · obtain ⟨_, -, h3⟩ := ConRon.Refine.bind_eq_ok_iff.mp h3
      exact (Result.ok_injective h3).symm
    · exact (Result.ok_injective h3).symm
  obtain ⟨ds', hds, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  rw [← hst3] at h2
  exact ⟨st1, h1, h2, hds⟩

/-- A worker step's failure is never exit 0. -/
theorem worker_failed_ne {F : Type} {wn : frontend.checker_io.WorkerNotes F} {fsv : F} {m e v}
    {c : Std.U8} (h : driver.worker.worker_failed wn fsv m e v = ok c) : c.val ≠ 0 := by
  rw [driver.worker.worker_failed] at h
  obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  exact exit_code_ne hc0

/-- `module_read`'s failure is never exit 0. -/
theorem module_read_err {F : Type} {finst : frontend.checker_io.CheckerFs F}
    {wn : frontend.checker_io.WorkerNotes F} {fsv : F} {pers st sp m mName x pins maxNatSize
      verified who pace} {c : Std.U8} {st' : arena.monad.AState}
    (h : driver.worker.module_read finst wn fsv pers st sp m mName x pins maxNatSize verified who
      pace = ok (.Err c, st')) : c.val ≠ 0 := by
  rw [driver.worker.module_read] at h
  obtain ⟨⟨r, st1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at h
    rw [← h.1]; exact worker_failed_ne hi
  | Ok p =>
  obtain ⟨⟨r1, st2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err p1 =>
    obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at h
    rw [← h.1]; exact worker_failed_ne hi
  | Ok w' =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨st3, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ds', -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp at h

/-- The verdict of a worker, 0: its check phase accepted. -/
theorem module_verdict_zero {F : Type} {wn : frontend.checker_io.WorkerNotes F} {fsv : F}
    {who pers st ds own v verified} {c : Std.U8}
    (h : driver.worker.module_verdict wn fsv who pers st ds own v verified = ok c)
    (hc : c.val = 0) : ∃ ix, v = .Ok ix := by
  cases v with
  | Ok ix => exact ⟨ix, rfl⟩
  | Err p =>
    exfalso
    obtain ⟨e, i⟩ := p
    rw [driver.worker.module_verdict] at h
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h] at hc
    exact exit_code_ne hc0 hc

/-- The jobs of a module's check phase: those from `start`. -/
theorem module_jobs_val {ds : alloc.vec.Vec arena.env.IDeclaration} {start n : Std.Usize}
    (h : driver.worker.module_jobs ds start = ok n) : n.val = ds.length - start.val := by
  rw [driver.worker.module_jobs] at h
  have hl := alloc.vec.Vec.len_val ds
  split at h
  · have := (ConRon.Refine.Nat.usub_val h).2
    rw [this, hl]
  · cases Result.ok_injective h
    simp [alloc.vec.Vec.length] at hl ⊢
    scalar_tac

/-- **A module's check phase, accepted** (`worker::module_phase`, the run's one module): the
index over every record, the tier frozen, the reach's inferred flags on a worker's state over
it, and the worker map's contract at the jobs from `start`, reading at the state the map ran
at. -/
theorem module_phase_ok (hpool : PoolSound io) {s s' : S} {pers st mode ipins}
    {w : frontend.modular.worker.WorkerRead} {ds sp jobs ix st'}
    (h : driver.worker.module_phase io s pers st mode ipins w ds sp jobs = ok (.Ok ix, s', st')) :
    ∃ ix0 st1 tier frozen ws ws',
      (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index pers st e ds 0#usize) = ok (.Ok ix0, st1) ∧
      arena.checker.freeze_tier st1.store ix0 = ok (tier, frozen) ∧
      arena.checker.worker_state st1.pins = ok ws ∧
      frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
      ParallelAll (ds.length - w.start.val) (oleanWorkerInit st1.pins)
        (fun c k => oleanJobStepSol io.CheckerFsInst s tier mode ipins ds w.pins w.values sp none
          c (w.start.val + k)) := by
  rw [driver.worker.module_phase] at h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r, st1⟩, hbi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok ix0 =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨workers, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨tier, frozen⟩, hfz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨fws, hfws, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r1, fws'⟩, hinf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  | Ok u =>
  obtain ⟨⟨r2, io1⟩, hpar, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨ix1, e1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err p =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  | Ok u2 =>
  cases u
  refine ⟨ix0, st1, tier, frozen, fws, fws', by rw [hii, bind_ok]; exact hbi, hfz, hfws, hinf, ?_⟩
  have hpa := hpool _ _ s _ _ io1 hpar
  rw [module_jobs_val hn] at hpa
  refine parallelAll_mono rfl ?_ hpa
  intro x k r hk
  exact olean_stepAt io.CheckerFsInst _ s x k r hk

/-- **A module's check phase in `--modular`, accepted** (`worker::module_phase_in`): as
`module_phase_ok`, the jobs in order on one worker. -/
theorem module_phase_in_ok {F : Type} {finst : frontend.checker_io.CheckerFs F} {fsv : F}
    {pers st mode ipins} {w : frontend.modular.worker.WorkerRead} {ds sp ix st'}
    (h : driver.worker.module_phase_in finst fsv pers st mode ipins w ds sp = ok (.Ok ix, st')) :
    ∃ ix0 st1 tier frozen ws ws',
      (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index pers st e ds 0#usize) = ok (.Ok ix0, st1) ∧
      arena.checker.freeze_tier st1.store ix0 = ok (tier, frozen) ∧
      arena.checker.worker_state st1.pins = ok ws ∧
      frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
      ParallelAll (ds.length - w.start.val) (oleanWorkerInit st1.pins)
        (fun c k => oleanJobStepSol finst fsv tier mode ipins ds w.pins w.values sp none
          c (w.start.val + k)) := by
  rw [driver.worker.module_phase_in] at h
  obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r, st1⟩, hbi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => simp at h
  | Ok ix0 =>
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨tier, frozen⟩, hfz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨fws, hfws, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r1, fws'⟩, hinf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp at h
  | Ok u =>
  obtain ⟨cache, hcache, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r2, w2, c2⟩, hjobs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨ix1, e1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err p => simp at h
  | Ok u2 =>
  cases u
  cases u2
  refine ⟨ix0, st1, tier, frozen, fws, fws', by rw [hii, bind_ok]; exact hbi, hfz, hfws, hinf, ?_⟩
  have hfold := jobs_in_order_loop_fold finst fsv tier mode ipins ds w.pins w.values sp w.start n
    _ 0#usize fws cache rfl hjobs
  rw [module_jobs_val hn] at hfold
  refine parallelAll_of_fold (s₀ := (fws, cache)) ?_ (by simpa using hfold)
  simp only [oleanWorkerInit, hfws, hcache, bind_ok]

/-- **The imports a run adds to a module's header**, con-leche's: none, or at a compared
challenge `import all` of its solution (`Graph.solutionImport`). -/
def solX : Option kernel.name.Name → Array ConLeche.Frontend.Olean.ImportRec
  | none => #[]
  | some s => #[ConLeche.Driver.Graph.solutionImport (ConRon.Refine.absName s)]

/-- **What an exit 0 of a module's worker ran**: the premises of `rust_worker_gen2` (the pins
the embedded ones) at the lookup `sp`, the module named `mName` and with `sol` a compared
challenge's solution, interned after it and added to its header (`solX`); its reads at one
instance's state and its jobs at another's, both snapshots of `fs`. -/
inductive WorkerStages (fs : ConLeche.FS) (sp : frontend.olean.files.Roots)
    (mName : kernel.name.Name) (sol : Option kernel.name.Name)
    (pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet) : Prop where
  | intro {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
      {Fs' : Type} {finst' : frontend.checker_io.CheckerFs Fs'} {fsv' : Fs'}
      {st1 st2 st3 st4 st5 : arena.monad.AState} {m : arena.handle.NIdx}
      {hs : List arena.handle.NIdx}
      {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
      {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
      {w : frontend.modular.worker.WorkerRead} {ds : alloc.vec.Vec arena.env.IDeclaration}
      {ix : arena.stream_index.IStreamIndex} {tier : arena.store.PersTier}
      {frozen : arena.store.EStore} {ws ws' : arena.monad.AState}
      (hsnap : SnapshotOf finst fsv fs) (hsnap' : SnapshotOf finst' fsv' fs)
      (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
      (hbare : (absRoots sp).bare = absRoots sp)
      (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
      (hroot : InternRoots emptyTier st1 (mName :: sol.toList) (m :: hs) st2)
      (hx : ∀ st : ConRon.Arena.EStore, ConRon.Bridge.Frontend.ListRel
          (ConRon.Bridge.Frontend.Olean.NR st) (absNIdx m :: hs.map absNIdx)
          (ConRon.Refine.absName mName :: sol.toList.map ConRon.Refine.absName) →
        ConRon.Bridge.Frontend.Olean.ImpsD st (absImports x) (solX sol))
      (h5 : arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3))
      (hwork : frontend.modular.worker.worker_read finst fsv emptyTier st3 sp ipins m x
        = ok (.Ok w, st4))
      (hds : frontend.modular.worker.worker_decls w = ok ds)
      (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5))
      (h7 : arena.checker.freeze_tier st5.store ix = ok (tier, frozen))
      (hws : arena.checker.worker_state st5.pins = ok ws)
      (hinfer : frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws'))
      (h8 : ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
        (fun c k => oleanJobStepSol finst' fsv' tier .Verified ipins ds w.pins w.values
          sp none c (w.start.val + k))) :
      WorkerStages fs sp mName sol pins

/-- A worker run is an accepted worker, at the imports it added. -/
theorem WorkerStages.accepted {fs : ConLeche.FS} {sp : frontend.olean.files.Roots}
    {mName : kernel.name.Name} {sol : Option kernel.name.Name}
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} (h : WorkerStages fs sp mName sol pins) :
    ConLeche.Driver.WorkerAccepted (ConRon.Refine.absPins pins) (absRoots sp) fs
      (ConRon.Refine.absName mName) 1 (solX sol) := by
  cases h with
  | intro hsnap hsnap' hpins hbare h1 hroot hx h5 hwork hds h6 h7 hws hinfer h8 =>
    obtain ⟨_, hdec⟩ := decode_of_decode_embedded hpins
    exact rust_worker_gen2 ConRon.Bridge.Modular.reachRunHyp_holds hsnap hsnap' hbare hx h1 hroot
      hdec h5 hwork hds h6 h7 hws hinfer h8

/-- A worker run's pins are the embedded ones. -/
theorem WorkerStages.hpins {fs : ConLeche.FS} {sp : frontend.olean.files.Roots}
    {mName : kernel.name.Name} {sol : Option kernel.name.Name}
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} (h : WorkerStages fs sp mName sol pins) :
    kernel.pins_decode.decode_embedded = ok (.Ok pins) := by
  cases h with
  | intro hsnap hsnap' hpins => exact hpins

/-- **The imports a worker adds, made** (`worker::added_imports`): the solution's name, if any,
interned (`InternRoots` of `sol.toList`), and the imports what `solX` denotes wherever the
module and the solution are read back. -/
theorem added_imports_ok {F : Type} {wn : frontend.checker_io.WorkerNotes F} {fsv : F}
    {pers : arena.store.PersTier} {st st' : arena.monad.AState} {mName : kernel.name.Name}
    {sol : Option kernel.name.Name} (hwf : ∀ n ∈ sol.toList, ConRon.Refine.NameWF n) {v : Bool}
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    (h : driver.worker.added_imports wn fsv pers st mName sol v = ok (.Ok x, st')) :
    ∃ hs, InternRoots pers st sol.toList hs st' ∧
      ∀ (m : arena.handle.NIdx) (est : ConRon.Arena.EStore), ConRon.Bridge.Frontend.ListRel
          (ConRon.Bridge.Frontend.Olean.NR est) (absNIdx m :: hs.map absNIdx)
          (ConRon.Refine.absName mName :: sol.toList.map ConRon.Refine.absName) →
        ConRon.Bridge.Frontend.Olean.ImpsD est (absImports x) (solX sol) := by
  cases sol with
  | none =>
    simp only [driver.worker.added_imports, Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun _ _ _ => rfl⟩
  | some sName =>
    simp only [driver.worker.added_imports] at h
    obtain ⟨⟨r, st1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp at h
    | Ok sh =>
      obtain ⟨xi, hxi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x', hx', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[sh], ⟨hwf _ (by simp), st1, hr, rfl⟩, fun m est hl => ?_⟩
      have hxv : x'.val = [xi] := by rw [ConRon.Refine.vec_push_val hx']; rfl
      cases hl with
      | cons _ hl' =>
        cases hl' with
        | cons hs _ => exact solImport_impsD hs hxi hxv

/-- `added_imports`' failure is never exit 0. -/
theorem added_imports_err {F : Type} {wn : frontend.checker_io.WorkerNotes F} {fsv : F}
    {pers st mName sol v} {c : Std.U8} {st' : arena.monad.AState}
    (h : driver.worker.added_imports wn fsv pers st mName sol v = ok (.Err c, st')) :
    c.val ≠ 0 := by
  cases sol with
  | none => simp [driver.worker.added_imports] at h
  | some sName =>
    simp only [driver.worker.added_imports] at h
    obtain ⟨⟨r, st1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e =>
      obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at h
      rw [← h.1]; exact worker_failed_ne hi
    | Ok sh =>
      obtain ⟨xi, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨x', -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp at h

/-- **The copies' step, 0**: the verdict before it was 0. -/
theorem module_copies_zero {F : Type} {wn : frontend.checker_io.WorkerNotes F} {fsv : F}
    {who mName pers st x w c v} {c1 : Std.U8} {st' : arena.monad.AState}
    (h : driver.worker.module_copies wn fsv who mName pers st x w c v = ok (c1, st'))
    (hc : c1.val = 0) : c.val = 0 := by
  rw [driver.worker.module_copies] at h
  by_cases h0 : c != 0#u8
  · rw [ite_eq_left h0] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [h.1]; exact hc
  · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h0
    rw [h0]; rfl

/-- **The run's one module, 0** (`worker::check_module` at `--verified`, the embedded pins):
its calls are a worker's (`WorkerStages`) at the lookup `sp`, `sol` added to its header. -/
theorem check_module_zero (hfs : AnswersAs io fs) (hpool : PoolSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {sp : frontend.olean.files.Roots}
    (hbare : (absRoots sp).bare = absRoots sp)
    {mName : kernel.name.Name} (hwf : ConRon.Refine.NameWF mName)
    {sol : Option kernel.name.Name} (hwfS : ∀ n ∈ sol.toList, ConRon.Refine.NameWF n)
    {c : Std.U8}
    (h : driver.worker.check_module io s a sp mName sol = ok (c, s'))
    (hc : c.val = 0) : ∃ pins, WorkerStages fs sp mName sol pins := by
  rw [driver.worker.check_module] at h
  simp only [hver, ite_true, bind_ok] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r0, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (worker_failed_ne hc0) hc).elim
  | Ok u =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r1, st2⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (worker_failed_ne hc0) hc).elim
  | Ok m =>
  obtain ⟨⟨rx, st3⟩, hrx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases rx with
  | Err c0 => exact (code_ne h (added_imports_err hrx) hc).elim
  | Ok x =>
  obtain ⟨hs, hirs, hx⟩ := added_imports_ok hwfS hrx
  obtain ⟨o, hpr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | none => exact (code_ne h (by decide) hc).elim
  | some ps =>
  have hpins := embedded_pins_ok hpr
  obtain ⟨⟨r2, st4⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err c0 =>
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    rw [← this.1] at hc
    exact (module_read_err hr2 hc).elim
  | Ok r3 =>
  obtain ⟨w, ipins, ds⟩ := r3
  obtain ⟨st3', h5, hwork, hds⟩ := module_read_ok hr2
  obtain ⟨⟨jobs, io2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨verdict, io3, st5⟩, hph, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨c2, st6⟩, hcp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hc2 : c2.val = 0 := by
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    rw [this.1]; exact hc
  obtain ⟨ix, rfl⟩ := module_verdict_zero hc1 (module_copies_zero hcp hc2)
  obtain ⟨ix0, st5', tier, frozen, ws, ws', h6, h7, hws, hinfer, h8⟩ := module_phase_ok hpool hph
  exact ⟨ps, WorkerStages.intro (hfs s) (hfs io2) hpins hbare h1 ⟨hwf, st2, hr1, hirs⟩
    (fun est hl => hx m est hl) h5 hwork hds h6 h7 hws hinfer h8⟩

end Worker

/-! ## The composition: a family of models -/

/-- **A graph check and a worker at every module of its headers' closure, each an exit 0 of
its own run on the snapshot `fs`, have a family of models** (`Stages.model_modular_of`, the
worker runs each at its own instance). -/
theorem modular_of_stages (V : Type w) [ConLeche.SetTheory V] {fs : ConLeche.FS}
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {rName : kernel.name.Name}
    (hg : GraphStages fs [rName] dirs)
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absSearchPath dirs) fs
        [ConRon.Refine.absName rName] m' →
      ∃ mName : kernel.name.Name, ConRon.Refine.absName mName = m' ∧
        ∃ (dv : alloc.vec.Vec (alloc.vec.Vec Std.U32)) (pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet),
          absSearchPath dv = absSearchPath dirs ∧
            WorkerStages fs ⟨dv, alloc.vec.Vec.new _⟩ mName none pins) :
    ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
      (∀ m, ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) fs #[ConRon.Refine.absName rName] m →
        ConLeche.IsModel V (model m) (ConLeche.Frontend.Olean.moduleConstants (absSearchPath dirs) fs m)) ∧
      (∀ m n m', ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) fs #[ConRon.Refine.absName rName] m →
        ConLeche.Frontend.Olean.Sees (absSearchPath dirs) fs m n m' → model m n = model m' n) := by
  cases hg with
  | intro hsnap h1g hpk hroots hgraph =>
  obtain ⟨CC, rk, good, hr, edges, inj, hhdr⟩ := rust_graph hsnap h1g hpk hroots hgraph
  obtain ⟨_, -, _, pins0, -, hw0⟩ := hwork (ConRon.Refine.absName rName) (.root (by simp))
  refine ConLeche.Driver.Compose.closure_sees_isModel (pins := ConRon.Refine.absPins pins0) V CC rk
    good edges inj (fun M hM => ?_) (hr _ (by simp))
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  obtain ⟨mName, hmn, dv, pins, hdv, hw⟩ := hwork e.1 (hhdr e he)
  have hpe : pins = pins0 := by
    have := hw.hpins.symm.trans hw0.hpins
    simpa using this
  subst hpe
  rw [← hmn]
  have := hw.accepted
  simp only [absRoots] at this
  rw [hdv] at this
  exact ⟨1, this⟩

/-! ## The runs of `--check-graph` and `--olean --module` -/

section Runs

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- The one root of a parse, and its search path's copy. -/
theorem one_root {a : driver.cli.Args} {f : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f])
    {rs : alloc.vec.Vec kernel.name.Name}
    (hr : driver.cli.parse_mod_names a.files = ok (.Ok rs)) :
    ∃ nm, rs.val = [nm] ∧ frontend.olean.files.parse_mod_name f = ok (some nm) := by
  obtain ⟨ns, hrs, hfa⟩ := parse_mod_names_loop_val a.files _ _ 0#usize rfl (by simp) hr
  rw [hfiles] at hfa
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hfa
  rcases hfa with _ | ⟨hx, hrest⟩
  cases hrest
  exact ⟨_, by rw [hrs]; rfl, hx⟩

/-- **`--check-graph` on one root, at exit 0** (`cli::check_graph_args`). -/
theorem check_graph_args_zero {s s' : S} {a : driver.cli.Args} (hol : a.olean = false)
    (hcmp : a.compare = false) (hmo : a.module = false) (htp : a.trusted_path.val = []) (hcon : a.constants.val = [])
    {f : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f]) {c : Std.U8}
    (h : driver.cli.check_graph_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (roots : alloc.vec.Vec kernel.name.Name) (nm : kernel.name.Name)
      (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      roots.val = [nm] ∧ frontend.olean.files.parse_mod_name f = ok (some nm) ∧
      dirs.val.map (·.val) = a.search_path.val.map (·.val) ∧
      driver.graph.check_graph io s ⟨dirs, alloc.vec.Vec.new _⟩ roots = ok (c, s') := by
  rw [driver.cli.check_graph_args] at h
  have hfb : driver.cli.check_graph_flags_bad a = ok false := by
    rw [driver.cli.check_graph_flags_bad]
    have h0 : ¬ alloc.vec.Vec.len a.constants > 0#usize := by
      have := alloc.vec.Vec.len_val a.constants
      simp [alloc.vec.Vec.length, hcon] at this; scalar_tac
    have h1 : ¬ alloc.vec.Vec.len a.trusted_path > 0#usize := by
      have := alloc.vec.Vec.len_val a.trusted_path
      simp [alloc.vec.Vec.length, htp] at this; scalar_tac
    simp only [hol, hmo, Bool.false_eq_true, ite_false, ite_eq_right h0, ite_eq_right h1]
  rw [hfb, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases b with
  | true => exact (usage_ne h hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => exact (usage_ne h hc).elim
  | Ok rs =>
  obtain ⟨nm, hrs, hnm⟩ := one_root hfiles hr
  simp only [hcmp, Bool.false_eq_true, ite_false] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [frontend.olean.files.roots_of_path] at hsp
  cases Result.ok_injective hsp
  refine ⟨rs, nm, v, hrs, hnm, ?_, h⟩
  have := push_files_loop_val a.search_path _ _ 0#usize rfl hv
  simpa using this

/-- `sol_roots` with no trusted path: the search path's copy, no fallback. -/
theorem sol_roots_plain {a : driver.cli.Args} (htp : a.trusted_path.val = [])
    {sp : frontend.olean.files.Roots} (h : driver.cli.sol_roots a = ok sp) :
    ∃ dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32), sp = ⟨dirs, alloc.vec.Vec.new _⟩ ∧
      dirs.val.map (·.val) = a.search_path.val.map (·.val) := by
  rw [driver.cli.sol_roots] at h
  have h0 : alloc.vec.Vec.len a.trusted_path = 0#usize := by
    have := alloc.vec.Vec.len_val a.trusted_path
    simp [alloc.vec.Vec.length, htp] at this; scalar_tac
  rw [ite_eq_left h0] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [frontend.olean.files.roots_of_path] at h
  cases Result.ok_injective h
  refine ⟨v, rfl, ?_⟩
  have := push_files_loop_val a.search_path _ _ 0#usize rfl hv
  simpa using this

/-- **`--olean --module` on one root, at exit 0** (`cli::olean_args`, `module_args`). -/
theorem olean_args_module {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = false)
    (hsch : a.scheduled = false) (hmod : a.modular = false)
    (hmo : a.module = true) (htp : a.trusted_path.val = []) (hcon : a.constants.val = [])
    {f : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f]) {c : Std.U8}
    (h : driver.cli.olean_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (nm : kernel.name.Name) (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      frontend.olean.files.parse_mod_name f = ok (some nm) ∧
      dirs.val.map (·.val) = a.search_path.val.map (·.val) ∧
      driver.worker.check_module io s a ⟨dirs, alloc.vec.Vec.new _⟩ nm none = ok (c, s') := by
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
  obtain ⟨nm, hrs, hnm⟩ := one_root hfiles hr
  obtain ⟨cs, hcs, hcsv⟩ := parse_const_names_nil hcon
  simp only [hcs, Aeneas.Std.bind_ok, hcmp, Bool.false_eq_true, ite_false] at h
  have htm : driver.cli.trusted_misplaced a = ok false := by
    rw [driver.cli.trusted_misplaced]
    have : alloc.vec.Vec.len a.trusted_path = 0#usize := by
      have := alloc.vec.Vec.len_val a.trusted_path
      simp [alloc.vec.Vec.length, htp] at this; scalar_tac
    rw [ite_eq_left this]
  simp only [htm, bind_ok, Bool.false_eq_true, ite_false, hsch, hmod, hmo, ite_true] at h
  rw [driver.cli.module_args] at h
  have h1 : ¬ (alloc.vec.Vec.len rs != 1#usize) = true := by
    have := alloc.vec.Vec.len_val rs
    simp [alloc.vec.Vec.length, hrs] at this
    simp; scalar_tac
  have h2 : ¬ alloc.vec.Vec.len cs > 0#usize := by
    have := alloc.vec.Vec.len_val cs
    simp [alloc.vec.Vec.length, hcsv] at this; scalar_tac
  rw [ite_eq_right h1, ite_eq_right h2] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨dirs, rfl, hd⟩ := sol_roots_plain htp hsp
  rw [ConRon.Args.vec_index_ok' (by simp [hrs]), bind_ok] at h
  simp only [hrs] at h
  exact ⟨nm, dirs, hnm, hd, h⟩

/-- **An exit 0 of `["--check-graph", "--search-path=" ++ dirs, "--", root]`**
(`cli::run_args`): the root a module name the Rust parsed, the search path `dirs`'s
directories, the graph check's calls `rust_graph`'s premises. -/
theorem run_args_graph (hfs : AnswersAs io fs)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (hargv : ArgvOf argv ["--check-graph", "--search-path=" ++ dirs, "--", root]) {s s' : S}
    {c : Std.U8} (h : driver.cli.run_args io s argv = ok (c, s')) (hc : c.val = 0) :
    ∃ (nm : kernel.name.Name) (dv : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      ConLeche.Frontend.Olean.parseModName root = some (ConRon.Refine.absName nm) ∧
      absSearchPath dv = ConLeche.Driver.searchPathOf dirs ∧ GraphStages fs [nm] dv := by
  obtain ⟨w0, w1, w2, w3, hv, h0, h1, h2, h3⟩ := argv_graph hargv
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
    parse_args_graph hv h0 hT h2 ha
  simp only [hbad, hcg, hcmp, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f', hf', hf'v⟩ : ∃ f', a.files.val = [f'] ∧ f'.val = w3.val := by
    rcases hfv : a.files.val with _ | ⟨f', _ | ⟨g, l⟩⟩ <;> rw [hfv] at hfl <;> simp at hfl
    exact ⟨f', rfl, hfl⟩
  obtain ⟨roots, nm, dv, hroots, hnm, hdv, hck⟩ := check_graph_args_zero hol hcmp hmo htp hcon hf' h hc
  have hf3 : f'.val.map UScalar.val = root.toList.map Char.toNat := by rw [hf'v]; exact h3
  obtain ⟨hwf, hpm⟩ := ConRon.Args.parse_mod_name_some hf3 hnm
  have hst := check_graph_zero hfs (by rw [hroots]; intro n hn; simp at hn; subst hn; exact hwf)
    hck hc
  rw [hroots] at hst
  refine ⟨nm, dv, hpm, ?_, hst⟩
  rw [absSearchPath_of_vals hdv]
  exact ConRon.Args.push_dirs_search h1 hsp

/-- **An exit 0 of `["--olean", "--module", "--search-path=" ++ dirs, "--", root]`**
(`cli::run_args`): the root a module name the Rust parsed, the search path `dirs`'s
directories, its worker's calls `rust_worker_gen2`'s premises. -/
theorem run_args_module (hfs : AnswersAs io fs) (hpool : PoolSound io)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (hargv : ArgvOf argv ["--olean", "--module", "--search-path=" ++ dirs, "--", root]) {s s' : S}
    {c : Std.U8} (h : driver.cli.run_args io s argv = ok (c, s')) (hc : c.val = 0) :
    ∃ (nm : kernel.name.Name) (dv : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      ConLeche.Frontend.Olean.parseModName root = some (ConRon.Refine.absName nm) ∧
      absSearchPath dv = ConLeche.Driver.searchPathOf dirs ∧
      ∃ pins, WorkerStages fs ⟨dv, alloc.vec.Vec.new _⟩ nm none pins := by
  obtain ⟨w0, wm, w1, w2, w3, hv, h0, hm, h1, h2, h3⟩ := argv_module hargv
  obtain ⟨T, hT⟩ := search_word h1
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have gm : argv.val[(1#usize : Std.Usize).val]? = some wm := by simp [hv]
  have g1 : argv.val[(2#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(3#usize : Std.Usize).val]? = some w2 := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word gm (by rw [hm]; simp) (by rw [hm]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_word g1 (by rw [hT]; simp) (by rw [hT]; simp) (usize_add_lit (b := 3#usize) rfl),
      ConRon.Args.help_end g2 h2]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, htp, hcon, hsp, hfl⟩ :=
    parse_args_module hv h0 hm hT h2 ha
  simp only [hbad, hcg, hol, hcmp, hsch, hmod, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f', hf', hf'v⟩ : ∃ f', a.files.val = [f'] ∧ f'.val = w3.val := by
    rcases hfv : a.files.val with _ | ⟨f', _ | ⟨g, l⟩⟩ <;> rw [hfv] at hfl <;> simp at hfl
    exact ⟨f', rfl, hfl⟩
  obtain ⟨nm, dv, hnm, hdv, hck⟩ := olean_args_module hcmp hsch hmod hmo htp hcon hf' h hc
  have hf3 : f'.val.map UScalar.val = root.toList.map Char.toNat := by rw [hf'v]; exact h3
  obtain ⟨hwf, hpm⟩ := ConRon.Args.parse_mod_name_some hf3 hnm
  obtain ⟨pins, hst⟩ := check_module_zero hfs hpool hver rfl hwf (by simp) hck hc
  refine ⟨nm, dv, hpm, ?_, pins, hst⟩
  rw [absSearchPath_of_vals hdv]
  exact ConRon.Args.push_dirs_search h1 hsp

end Runs

/-- **`main_modular`'s conclusion**: on a snapshot where the graph check of `root` exits 0 and
every module of its headers' closure has an exit 0 of `--olean --module`, a family of models. -/
theorem modular_of_canGive (V : Type w) [ConLeche.SetTheory V] {dirs root : String}
    {r : ConLeche.Name} {fs : ConLeche.FS}
    (hr : ConLeche.Frontend.Olean.parseModName root = some r)
    (h : CanGiveConforming ["--check-graph", "--search-path=" ++ dirs, "--", root] fs 0)
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (ConLeche.Driver.searchPathOf dirs) fs [r] m' →
      ∃ root', ConLeche.Frontend.Olean.parseModName root' = some m' ∧
        CanGiveConforming ["--olean", "--module", "--search-path=" ++ dirs, "--", root'] fs 0) :
    ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
      (∀ m, ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.searchPathOf dirs) fs #[r] m →
        ConLeche.IsModel V (model m)
          (ConLeche.Frontend.Olean.moduleConstants (ConLeche.Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.searchPathOf dirs) fs #[r] m →
        ConLeche.Frontend.Olean.Sees (ConLeche.Driver.searchPathOf dirs) fs m n m' →
          model m n = model m' n) := by
  obtain ⟨S, io, s, s', argv, c, hfs, -, -, hargv, hrun, hc⟩ := h
  obtain ⟨nm, dv, hp, hsp, hg⟩ := run_args_graph hfs hargv hrun (by simpa using hc)
  have hnm : ConRon.Refine.absName nm = r := Option.some.inj (hp.symm.trans hr)
  have := modular_of_stages V hg (fun m' hm' => by
    rw [hsp, hnm] at hm'
    obtain ⟨root', hroot', hcg⟩ := hwork m' hm'
    obtain ⟨S', io', t, t', argv', c', hfs', hpool', -, hargv', hrun', hc'⟩ := hcg
    obtain ⟨nm', dv', hp', hsp', pins, hst⟩ :=
      run_args_module hfs' hpool' hargv' hrun' (by simpa using hc')
    exact ⟨nm', Option.some.inj (hp'.symm.trans hroot'), dv', pins, by rw [hsp', hsp], hst⟩)
  rw [hsp, hnm] at this
  exact this

/-! ## `--olean --modular`: every module in one process -/

section One

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **No module failed** (`modular::first_failure` answered none): every code from `k` is 0. -/
theorem first_failure_none (codes : alloc.vec.Vec Std.U8) :
    ∀ (m : Nat) (k : Std.Usize), codes.val.length - k.val = m →
      driver.modular.first_failure_loop codes k = ok none →
      ∀ j, k.val ≤ j → (hj : j < codes.val.length) → codes.val[j] = 0#u8 := by
  intro m
  induction m with
  | zero =>
    intro k hm _ j hk hj
    omega
  | succ m ih =>
    intro k hm h j hk hj
    have hlt : k.val < codes.val.length := by omega
    rw [driver.modular.first_failure_loop] at h
    rw [ite_eq_left (by scalar_tac), ConRon.Args.vec_index_ok' hlt, bind_ok] at h
    by_cases h0 : codes.val[k.val] != 0#u8
    · rw [ite_eq_left h0] at h; simp at h
    · rw [ite_eq_right h0] at h
      obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hv : k1.val = k.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hk1; simpa using this
      by_cases hjk : j = k.val
      · subst hjk
        exact UScalar.eq_of_val_eq (by simpa using h0)
      · exact ih k1 (by omega) h j (by omega) hj

/-- **A failing module's code is not 0** (`modular::first_failure` answered `some k`). -/
theorem first_failure_some (codes : alloc.vec.Vec Std.U8) :
    ∀ (m : Nat) (k : Std.Usize), codes.val.length - k.val = m → ∀ {k'},
      driver.modular.first_failure_loop codes k = ok (some k') →
      ∃ hk : k'.val < codes.val.length, codes.val[k'.val] ≠ 0#u8 := by
  intro m
  induction m with
  | zero =>
    intro k hm k' h
    rw [driver.modular.first_failure_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    simp at h
  | succ m ih =>
    intro k hm k' h
    have hlt : k.val < codes.val.length := by omega
    rw [driver.modular.first_failure_loop] at h
    rw [ite_eq_left (by scalar_tac), ConRon.Args.vec_index_ok' hlt, bind_ok] at h
    by_cases h0 : codes.val[k.val] != 0#u8
    · rw [ite_eq_left h0] at h
      simp only [Result.ok.injEq, Option.some.injEq] at h
      subst h
      exact ⟨hlt, by simpa using h0⟩
    · rw [ite_eq_right h0] at h
      obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hv : k1.val = k.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hk1; simpa using this
      exact ih k1 (by omega) h

/-- **The run's verdict, 0**: every module's code is 0. -/
theorem modular_verdict_zero {s s' : S} {codes : alloc.vec.Vec Std.U8}
    {names : alloc.vec.Vec kernel.name.Name} {v : Bool} {c : Std.U8}
    (h : driver.modular.modular_verdict io s codes names v = ok (c, s')) (hc : c.val = 0) :
    ∀ j, (hj : j < codes.val.length) → codes.val[j] = 0#u8 := by
  rw [driver.modular.modular_verdict] at h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | none =>
    intro j hj
    exact first_failure_none codes _ 0#usize rfl ho j (by simp) hj
  | some k =>
    exfalso
    obtain ⟨hk, hne⟩ := first_failure_some codes _ 0#usize rfl ho
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [ConRon.Args.vec_index_ok' hk, bind_ok] at h
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    apply hne
    apply UScalar.eq_of_val_eq
    rw [this.1, hc]; rfl

/-- **A module of `--modular`, 0** (`worker::check_module_in` at `--verified`, the embedded
pins): its calls are a worker's (`WorkerStages`), reads and jobs at the one state. -/
theorem check_module_in_zero {F : Type} {finst : frontend.checker_io.CheckerFs F}
    {wn : frontend.checker_io.WorkerNotes F} {fsv : F} (hsnap : SnapshotOf finst fsv fs)
    {sp : frontend.olean.files.Roots} (hbare : (absRoots sp).bare = absRoots sp)
    {mName : kernel.name.Name} (hwf : ConRon.Refine.NameWF mName)
    {sol : Option kernel.name.Name} (hwfS : ∀ n ∈ sol.toList, ConRon.Refine.NameWF n)
    {maxNatSize : ron.nat.Nat} {c : Std.U8}
    (h : driver.worker.check_module_in finst wn fsv sp mName sol true maxNatSize = ok c)
    (hc : c.val = 0) : ∃ pins, WorkerStages fs sp mName sol pins := by
  rw [driver.worker.check_module_in] at h
  simp only [ite_true, bind_ok] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r0, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e => exact (worker_failed_ne h hc).elim
  | Ok u =>
  obtain ⟨⟨r1, st2⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e => exact (worker_failed_ne h hc).elim
  | Ok m =>
  obtain ⟨⟨rx, st3⟩, hrx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases rx with
  | Err c0 =>
    rw [← Result.ok_injective h] at hc
    exact (added_imports_err hrx hc).elim
  | Ok x =>
  obtain ⟨hs, hirs, hx⟩ := added_imports_ok hwfS hrx
  obtain ⟨o, hpr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | none =>
    rw [← Result.ok_injective h] at hc
    exact absurd hc (by decide)
  | some ps =>
  have hr2 := embedded_pins_ok hpr
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r3, st4⟩, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err c0 =>
    rw [← Result.ok_injective h] at hc
    exact (module_read_err hr3 hc).elim
  | Ok r4 =>
  obtain ⟨w, ipins, ds⟩ := r4
  obtain ⟨st3', h5, hwork, hds⟩ := module_read_ok hr3
  obtain ⟨⟨verdict, st5⟩, hph, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨c2, st6⟩, hcp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hc2 : c2.val = 0 := by rw [Result.ok_injective h]; exact hc
  obtain ⟨ix, rfl⟩ := module_verdict_zero hc1 (module_copies_zero hcp hc2)
  obtain ⟨ix0, st5', tier, frozen, ws, ws', h6, h7, hws, hinfer, h8⟩ := module_phase_in_ok hph
  exact ⟨ps, WorkerStages.intro hsnap hsnap hr2 hbare h1 ⟨hwf, st2, hr1, hirs⟩
    (fun est hl => hx m est hl) h5 hwork hds h6 h7 hws hinfer h8⟩

/-- **What an exit 0 of `--olean --modular` ran**: the graph check's calls, its modules read
back, and at every one of them, well formed, a worker's calls. -/
inductive ModularStages (fs : ConLeche.FS) (names : List kernel.name.Name)
    (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)) : Prop where
  | intro {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
      {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
      {pk : frontend.olean.spec.OleanPins} {groots : alloc.vec.Vec arena.handle.NIdx}
      {c : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
      {ns : alloc.vec.Vec kernel.name.Name}
      (hsnap : SnapshotOf finst fsv fs)
      (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
      (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
      (hroots : InternRoots emptyTier { g1 with store := gstore2 } names groots.val gR)
      (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store
        ⟨dirs, alloc.vec.Vec.new _⟩ groots none = ok (.Ok c, gstore3))
      (hns : driver.modular.graph_names emptyTier { gR with store := gstore3 } c = ok (.Ok ns))
      (hwork : ∀ k (hk : k < ns.val.length), ConRon.Refine.NameWF ns.val[k] →
        ∃ pins, WorkerStages fs ⟨dirs, alloc.vec.Vec.new _⟩ ns.val[k] none pins) :
      ModularStages fs names dirs

/-- **The one-process mode, 0** (`modular::check_modular` at `--verified`, the embedded pins):
the graph check's calls, and at every module of it, its worker's. -/
theorem check_modular_zero (hfs : AnswersAs io fs) (hcodes : CodesSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {roots : alloc.vec.Vec kernel.name.Name} (hwf : ∀ n ∈ roots.val, ConRon.Refine.NameWF n)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {c : Std.U8}
    (h : driver.modular.check_modular io s a roots ⟨dirs, alloc.vec.Vec.new _⟩ none = ok (c, s'))
    (hc : c.val = 0) : ModularStages fs roots.val dirs := by
  rw [driver.modular.check_modular] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r, io1, st1⟩, hgs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err c0 =>
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    rw [← this.1] at hc
    exact (graph_start_err hgs hc).elim
  | Ok pk =>
  obtain ⟨g1, gstore2, h1g, hpk, hst1, -⟩ := graph_start_ok hgs
  obtain ⟨⟨r1, st2⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [hst1] at hr1
  cases r1 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok rs =>
  obtain ⟨⟨r2, gstore3⟩, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok cc =>
  obtain ⟨r3, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok ns =>
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨jobs, io2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨threads, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨nr, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r4, io3⟩, hpar, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r4 with
  | Err m =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok cs =>
  obtain ⟨io4, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hall := modular_verdict_zero h hc
  obtain ⟨hlen, hcode⟩ := hcodes _ _ io2 _ _ cs io3 hpar
  refine ModularStages.intro (hfs io1) h1g hpk (intern_names_roots hwf hr1) hg hr3 ?_
  intro k hk hwk
  have hkn : k < (alloc.vec.Vec.len ns).val := by rw [alloc.vec.Vec.len_val]; exact hk
  have hc0 := hcode (UScalar.ofNatCore (ty := .Usize) k (by scalar_tac)) (by rw [UScalar.ofNatCore_val_eq]; exact hkn)
  rw [UScalar.ofNatCore_val_eq] at hc0
  have hcs0 : cs.val[k]! = 0#u8 := by
    have hk' : k < cs.val.length := by rw [hlen]; exact hkn
    rw [getElem!_pos cs.val k hk']
    exact hall k hk'
  rw [hcs0] at hc0
  simp only [driver.modular.ModularStep.Insts.Con_ron_coreFrontendChecker_ioCodeStep.code] at hc0
  have hkl : UScalar.ofNatCore (ty := .Usize) k (by scalar_tac) < alloc.vec.Vec.len ns := by
    have := UScalar.ofNatCore_val_eq (ty := .Usize) (x := k) (by scalar_tac)
    scalar_tac
  rw [ite_eq_left hkl, ConRon.Args.vec_index_ok' (by rw [UScalar.ofNatCore_val_eq]; exact hk),
    bind_ok] at hc0
  simp only [UScalar.ofNatCore_val_eq, hver, driver.modular.step_sol, bind_ok] at hc0
  exact check_module_in_zero (hfs io2) rfl hwk (by simp) hc0 rfl

/-- **`--olean --modular` on one root, at exit 0** (`cli::olean_args`, `modular_args`). -/
theorem olean_args_modular {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = false)
    (hsch : a.scheduled = false) (hmod : a.modular = true)
    (hmo : a.module = false) (htp : a.trusted_path.val = []) (hcon : a.constants.val = [])
    {f : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f]) {c : Std.U8}
    (h : driver.cli.olean_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (roots : alloc.vec.Vec kernel.name.Name) (nm : kernel.name.Name)
      (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      roots.val = [nm] ∧ frontend.olean.files.parse_mod_name f = ok (some nm) ∧
      dirs.val.map (·.val) = a.search_path.val.map (·.val) ∧
      driver.modular.check_modular io s a roots ⟨dirs, alloc.vec.Vec.new _⟩ none = ok (c, s') := by
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
  obtain ⟨nm, hrs, hnm⟩ := one_root hfiles hr
  obtain ⟨cs, hcs, hcsv⟩ := parse_const_names_nil hcon
  simp only [hcs, Aeneas.Std.bind_ok, hcmp, Bool.false_eq_true, ite_false] at h
  have htm : driver.cli.trusted_misplaced a = ok false := by
    rw [driver.cli.trusted_misplaced]
    have : alloc.vec.Vec.len a.trusted_path = 0#usize := by
      have := alloc.vec.Vec.len_val a.trusted_path
      simp [alloc.vec.Vec.length, htp] at this; scalar_tac
    rw [ite_eq_left this]
  simp only [htm, bind_ok, Bool.false_eq_true, ite_false, hsch, hmod, ite_true] at h
  rw [driver.cli.modular_args] at h
  have h1 : ¬ (alloc.vec.Vec.len rs != 1#usize) = true := by
    have := alloc.vec.Vec.len_val rs
    simp [alloc.vec.Vec.length, hrs] at this
    simp; scalar_tac
  have h2 : ¬ alloc.vec.Vec.len cs > 0#usize := by
    have := alloc.vec.Vec.len_val cs
    simp [alloc.vec.Vec.length, hcsv] at this; scalar_tac
  rw [ite_eq_right h1, ite_eq_right h2] at h
  simp only [hmo, Bool.false_eq_true, ite_false] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨dirs, rfl, hd⟩ := sol_roots_plain htp hsp
  exact ⟨rs, nm, dirs, hrs, hnm, hd, h⟩

/-- **An exit 0 of `["--olean", "--modular", "--search-path=" ++ dirs, "--", root]`**
(`cli::run_args`): the root a module name the Rust parsed, the search path `dirs`'s
directories, the run's calls `ModularStages`. -/
theorem run_args_modular (hfs : AnswersAs io fs) (hcodes : CodesSound io)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (hargv : ArgvOf argv ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) {s s' : S}
    {c : Std.U8} (h : driver.cli.run_args io s argv = ok (c, s')) (hc : c.val = 0) :
    ∃ (nm : kernel.name.Name) (dv : alloc.vec.Vec (alloc.vec.Vec Std.U32)),
      ConLeche.Frontend.Olean.parseModName root = some (ConRon.Refine.absName nm) ∧
      absSearchPath dv = ConLeche.Driver.searchPathOf dirs ∧ ModularStages fs [nm] dv := by
  obtain ⟨w0, wm, w1, w2, w3, hv, h0, hm, h1, h2, h3⟩ := argv_modular hargv
  obtain ⟨T, hT⟩ := search_word h1
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have gm : argv.val[(1#usize : Std.Usize).val]? = some wm := by simp [hv]
  have g1 : argv.val[(2#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(3#usize : Std.Usize).val]? = some w2 := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word gm (by rw [hm]; simp) (by rw [hm]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_word g1 (by rw [hT]; simp) (by rw [hT]; simp) (usize_add_lit (b := 3#usize) rfl),
      ConRon.Args.help_end g2 h2]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, htp, hcon, hsp, hfl⟩ :=
    parse_args_modular hv h0 hm hT h2 ha
  simp only [hbad, hcg, hol, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f', hf', hf'v⟩ : ∃ f', a.files.val = [f'] ∧ f'.val = w3.val := by
    rcases hfv : a.files.val with _ | ⟨f', _ | ⟨g, l⟩⟩ <;> rw [hfv] at hfl <;> simp at hfl
    exact ⟨f', rfl, hfl⟩
  obtain ⟨roots, nm, dv, hroots, hnm, hdv, hck⟩ := olean_args_modular hcmp hsch hmod hmo htp hcon hf' h hc
  have hf3 : f'.val.map UScalar.val = root.toList.map Char.toNat := by rw [hf'v]; exact h3
  obtain ⟨hwf, hpm⟩ := ConRon.Args.parse_mod_name_some hf3 hnm
  have hst := check_modular_zero hfs hcodes hver
    (by rw [hroots]; intro n hn; simp at hn; subst hn; exact hwf) hck hc
  rw [hroots] at hst
  refine ⟨nm, dv, hpm, ?_, hst⟩
  rw [absSearchPath_of_vals hdv]
  exact ConRon.Args.push_dirs_search h1 hsp

end One

/-- **`--olean --modular`'s family of models**: `modular_of_stages`, its workers the code map's
at the graph's modules, read back. -/
theorem modular_one_of_stages (V : Type w) [ConLeche.SetTheory V] {fs : ConLeche.FS}
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {rName : kernel.name.Name}
    (hm : ModularStages fs [rName] dirs) :
    ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
      (∀ m, ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) fs #[ConRon.Refine.absName rName] m →
        ConLeche.IsModel V (model m) (ConLeche.Frontend.Olean.moduleConstants (absSearchPath dirs) fs m)) ∧
      (∀ m n m', ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) fs #[ConRon.Refine.absName rName] m →
        ConLeche.Frontend.Olean.Sees (absSearchPath dirs) fs m n m' → model m n = model m' n) := by
  cases hm with
  | intro hsnap h1g hpk hroots hgraph hns hwork =>
  obtain ⟨CC, rk, good, hr, edges, inj, hhdr, hnames, hwf⟩ :=
    rust_graph_names hsnap h1g hpk hroots hgraph hns
  have hacc : ∀ M ∈ CC.map (·.1), ∃ pins, ∃ mName : kernel.name.Name,
      ConRon.Refine.absName mName = M ∧
        WorkerStages fs ⟨dirs, alloc.vec.Vec.new _⟩ mName none pins := by
    intro M hM
    rw [hnames] at hM
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hM
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    obtain ⟨pins, hw⟩ := hwork k hk (hwf _ (List.getElem_mem hk))
    exact ⟨pins, _, rfl, hw⟩
  obtain ⟨pins0, _, -, hw0⟩ := hacc (ConRon.Refine.absName rName) (hr _ (by simp))
  refine ConLeche.Driver.Compose.closure_sees_isModel (pins := ConRon.Refine.absPins pins0) V CC rk
    good edges inj (fun M hM => ?_) (hr _ (by simp))
  obtain ⟨pins, mName, hmn, hw⟩ := hacc M hM
  have hpe : pins = pins0 := by
    have := hw.hpins.symm.trans hw0.hpins
    simpa using this
  subst hpe
  rw [← hmn]
  exact ⟨1, hw.accepted⟩

/-- **`main_modular_one`'s conclusion from an exit 0**. -/
theorem modular_one_of_canGive (V : Type w) [ConLeche.SetTheory V] {dirs root : String}
    {r : ConLeche.Name} {fs : ConLeche.FS}
    (hr : ConLeche.Frontend.Olean.parseModName root = some r)
    (h : CanGiveConforming ["--olean", "--modular", "--search-path=" ++ dirs, "--", root] fs 0) :
    ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
      (∀ m, ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.searchPathOf dirs) fs #[r] m →
        ConLeche.IsModel V (model m)
          (ConLeche.Frontend.Olean.moduleConstants (ConLeche.Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.searchPathOf dirs) fs #[r] m →
        ConLeche.Frontend.Olean.Sees (ConLeche.Driver.searchPathOf dirs) fs m n m' →
          model m n = model m' n) := by
  obtain ⟨S, io, s, s', argv, c, hfs, -, hcodes, hargv, hrun, hc⟩ := h
  obtain ⟨nm, dv, hp, hsp, hm⟩ := run_args_modular hfs hcodes hargv hrun (by simpa using hc)
  have hnm : ConRon.Refine.absName nm = r := Option.some.inj (hp.symm.trans hr)
  have := modular_one_of_stages V hm
  rw [hsp, hnm] at this
  exact this

end ConRon.MainTheorem
