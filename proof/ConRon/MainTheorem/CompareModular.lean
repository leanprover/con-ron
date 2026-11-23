import ConRon.MainTheorem.CompareOleans

/-!
# `ConRon.MainTheorem.CompareModular` — the walks of `--check-graph --compare`, the compare
worker and `--olean --modular --compare`

**Task #171, slice 3b** (DESIGN.md §3.9).  An exit 0 of the compared graph check is
`Stages.rust_graph_cmp`'s premises (`GraphCmpStages`), at the solution's lookup; an exit 0 of
a module's worker at `--trusted-search-path` is `WorkerStages` at that lookup, and of the compare
worker `WorkerStages` with the solution added (`solX`); an exit 0 of `--olean --modular --compare`
is the compared graph's premises, its modules read back (`rust_graph_cmp_names`) and at every
one a worker's, the challenge's the compare worker's (`ModularCmpStages`).  The challenge's
walk through the trusted path alone (`compare_module::chal_walk`) runs on a store of its own and
is its verdict only: no theorem needs it.  `cmp_family` and `cmp_no_False` compose them as
`Stages.model_modular_compare_of` does, with upstream's `compare_sees_isModel` and
`compare_no_False`, each worker its own run: con-leche's `main_modular_compare`,
`main_modular_compare_one` and `main_modular_compare_no_False`.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.MainTheorem.Stages
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

namespace ConRon.MainTheorem

set_option autoImplicit false

universe w

/-! ## The graph check of a compared run -/

/-- **What an exit 0 of `--check-graph --compare` ran**: the premises of
`Stages.rust_graph_cmp` at the lookup `spR` (the solution's). -/
inductive GraphCmpStages (fs : ConLeche.FS) (cName sName : kernel.name.Name)
    (spR : frontend.olean.files.Roots) : Prop where
  | intro {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
      {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
      {pk : frontend.olean.spec.OleanPins} {gc gs : arena.handle.NIdx}
      {groots : alloc.vec.Vec arena.handle.NIdx}
      {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
      (hsnap : SnapshotOf finst fsv fs) (hgr : groots.val = [gc])
      (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
      (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
      (hroots : InternRoots emptyTier { g1 with store := gstore2 } [cName, sName] [gc, gs] gR)
      (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store spR groots
        (some (gc, gs)) = ok (.Ok cg, gstore3)) :
      GraphCmpStages fs cName sName spR

/-- The compared graph check's facts (`Stages.rust_graph_cmp`). -/
theorem GraphCmpStages.facts {fs : ConLeche.FS} {cName sName : kernel.name.Name}
    {spR : frontend.olean.files.Roots} (h : GraphCmpStages fs cName sName spR)
    (hsp : (absRoots spR).bare = absRoots spR) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ CC, ConLeche.Driver.Graph.NodeOk (absRoots spR) fs
        (ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName) (ConRon.Refine.absName sName)) e) ∧
      ConRon.Refine.absName cName ∈ CC.map (·.1) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure (absRoots spR) fs
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] e.1) := by
  cases h with
  | intro hsnap hgr h1g hpk hroots hgraph =>
    exact rust_graph_cmp hsnap hsp hgr h1g hpk hroots hgraph

/-- The solution's lookup has no root resolved. -/
theorem sol_roots_bare {a : driver.cli.Args} {sp : frontend.olean.files.Roots}
    (h : driver.cli.sol_roots a = ok sp) : (absRoots sp).bare = absRoots sp := by
  rw [sol_roots_abs h .anonymous .anonymous]
  exact solRoots_bare _

section Runs

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **The compared graph check, 0** (`compare_module::check_graph_cmp`): the challenge walk
answered none, and the graph's calls are `rust_graph_cmp`'s premises at the solution's lookup. -/
theorem check_graph_cmp_zero (hfs : AnswersAs io fs) {s s' : S} {a : driver.cli.Args}
    {cn sn : kernel.name.Name} (hwfC : ConRon.Refine.NameWF cn) (hwfS : ConRon.Refine.NameWF sn)
    {c : Std.U8} (h : driver.compare_module.check_graph_cmp io s a cn sn = ok (c, s'))
    (hc : c.val = 0) :
    ∃ spR, driver.cli.sol_roots a = ok spR ∧ GraphCmpStages fs cn sn spR := by
  rw [driver.compare_module.check_graph_cmp] at h
  obtain ⟨o, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | some e => exact (graph_failed_ne h hc).elim
  | none =>
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r, io1, st1⟩, hgs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err c0 =>
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    rw [← this.1] at hc
    exact (graph_start_err hgs hc).elim
  | Ok pk =>
  obtain ⟨g1, gstore2, h1g, hpk, rfl, -⟩ := graph_start_ok hgs
  obtain ⟨⟨r1, stR1⟩, hnc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok gc =>
  obtain ⟨⟨r2, gR⟩, hns, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok gs =>
  obtain ⟨groots, hgr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r3, gstore3⟩, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok cg =>
  exact ⟨sp, hsp, GraphCmpStages.intro (hfs io1) (one_root_val hgr) h1g hpk
    ⟨hwfC, stR1, hnc, hwfS, gR, hns, rfl⟩ hg⟩

/-- Two different module names, at exit 0: the pair the check runs on. -/
theorem two_names_ok {s s' : S} {roots : alloc.vec.Vec kernel.name.Name}
    {n0 n1 : kernel.name.Name} (hr : roots.val = [n0, n1]) {b : driver.cli.Bad} {c : Std.U8}
    {k : kernel.name.Name → kernel.name.Name → Result (Std.U8 × S)}
    (h : (do
      if alloc.vec.Vec.len roots != 2#usize then
        do io.usage s b; ok (3#u8, s)
      else
        let n ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice kernel.name.Name)
          roots 0#usize
        let n1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice kernel.name.Name)
          roots 1#usize
        let bb ← kernel.name.beq n n1
        if bb then
          do io.usage s driver.cli.Bad.CompareSameModule; ok (3#u8, s)
        else k n n1) = ok (c, s')) (hc : c.val = 0) : k n0 n1 = ok (c, s') := by
  have hl : ¬ (alloc.vec.Vec.len roots != 2#usize) = true := by
    have := alloc.vec.Vec.len_val roots
    simp [alloc.vec.Vec.length, hr] at this
    simp; scalar_tac
  rw [ite_eq_right hl, ConRon.Args.vec_index_ok' (by simp [hr]), bind_ok,
    ConRon.Args.vec_index_ok' (by simp [hr]), bind_ok] at h
  obtain ⟨bb, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases bb with
  | true =>
    simp only [ite_true] at h
    exact (usage_ne h hc).elim
  | false =>
    simp only [Bool.false_eq_true, ite_false, hr] at h
    exact h

/-- **`--check-graph --compare` at two roots, at exit 0** (`cli::check_graph_args`,
`check_graph_cmp_args`). -/
theorem check_graph_args_cmp {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = true)
    {f0 f1 : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f0, f1]) {c : Std.U8}
    (h : driver.cli.check_graph_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (n0 n1 : kernel.name.Name),
      frontend.olean.files.parse_mod_name f0 = ok (some n0) ∧
      frontend.olean.files.parse_mod_name f1 = ok (some n1) ∧
      driver.compare_module.check_graph_cmp io s a n0 n1 = ok (c, s') := by
  rw [driver.cli.check_graph_args] at h
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases b with
  | true => exact (usage_ne h hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases b1 with
  | true => exact (usage_ne h hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e => exact (usage_ne h hc).elim
  | Ok rs =>
  obtain ⟨n0, n1, hrs, h0, h1⟩ := two_roots hfiles hr
  simp only [hcmp, ite_true] at h
  rw [driver.cli.check_graph_cmp_args] at h
  exact ⟨n0, n1, h0, h1, two_names_ok (io := io) (s := s)
    (b := driver.cli.Bad.CheckGraphCompareTwo)
    (k := driver.compare_module.check_graph_cmp io s a) hrs h hc⟩

/-- **An exit 0 of `--check-graph --compare --trusted-search-path=T --search-path=D -- c s`**
(`cli::run_args`): the two roots module names the Rust parsed, the solution's lookup con-leche's
`CmpReq.solRoots` at `searchPathOf T` and `searchPathOf D`, the graph's calls `GraphCmpStages`. -/
theorem run_args_graph_cmp (hfs : AnswersAs io fs)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (hargv : ArgvOf argv ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) {x x' : S}
    {code : Std.U8} (h : driver.cli.run_args io x argv = ok (code, x')) (hc : code.val = 0) :
    ∃ (cn sn : kernel.name.Name) (spR : frontend.olean.files.Roots),
      ConLeche.Frontend.Olean.parseModName c = some (ConRon.Refine.absName cn) ∧
      ConLeche.Frontend.Olean.parseModName s = some (ConRon.Refine.absName sn) ∧
      (∀ X Y, absRoots spR = (⟨X, Y, ConLeche.Driver.searchPathOf T,
        ConLeche.Driver.searchPathOf D, none⟩ : ConLeche.Driver.CmpReq).solRoots) ∧
      GraphCmpStages fs cn sn spR := by
  obtain ⟨w0, w1, wT, wD, wE, f0, f1, hv, h0, h1, hT, hD, hE, hf0, hf1⟩ := argv_graph_cmp hargv
  obtain ⟨TT, hTT⟩ := trusted_word hT
  obtain ⟨DD, hDD⟩ := search_word hD
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wE := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word g1 (by rw [h1]; simp) (by rw [h1]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_word g2 (by rw [hTT]; simp) (by rw [hTT]; simp) (usize_add_lit (b := 3#usize) rfl),
      ConRon.Args.help_word g3 (by rw [hDD]; simp) (by rw [hDD]; simp) (usize_add_lit (b := 4#usize) rfl),
      ConRon.Args.help_end g4 hE]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, hcon, htp, hsp, hfl⟩ :=
    parse_args_graph_cmp hv h0 h1 hTT hDD hE ha
  simp only [hbad, hcg, ite_true] at h
  obtain ⟨f0', f1', hf', hf0', hf1'⟩ : ∃ f0' f1', a.files.val = [f0', f1'] ∧
      f0'.val = f0.val ∧ f1'.val = f1.val := by
    rcases hfv : a.files.val with _ | ⟨f0', _ | ⟨f1', _ | ⟨g, l⟩⟩⟩ <;> rw [hfv] at hfl <;>
      simp at hfl
    exact ⟨f0', f1', rfl, hfl.1, hfl.2⟩
  obtain ⟨n0, n1, hn0, hn1, hck⟩ := check_graph_args_cmp hcmp hf' h hc
  have hc0 : f0'.val.map UScalar.val = c.toList.map Char.toNat := by rw [hf0']; exact hf0
  have hc1 : f1'.val.map UScalar.val = s.toList.map Char.toNat := by rw [hf1']; exact hf1
  obtain ⟨hwf0, hpm0⟩ := ConRon.Args.parse_mod_name_some hc0 hn0
  obtain ⟨hwf1, hpm1⟩ := ConRon.Args.parse_mod_name_some hc1 hn1
  obtain ⟨spR, hspR, hst⟩ := check_graph_cmp_zero hfs hwf0 hwf1 hck hc
  refine ⟨n0, n1, spR, hpm0, hpm1, fun X Y => ?_, hst⟩
  rw [sol_roots_abs hspR X Y, show absSearchPath a.trusted_path = _ from
    ConRon.Args.push_dirs_trusted hT htp,
    show absSearchPath a.search_path = _ from ConRon.Args.push_dirs_search hD hsp]

/-! ## The workers: a module's, at the trusted path; the compare worker -/

/-- **`--olean --module` on one root, any trusted path, at exit 0** (`cli::olean_args`,
`module_args`): the worker at the solution's lookup. -/
theorem olean_args_module_t {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = false)
    (hsch : a.scheduled = false) (hmod : a.modular = false) (hmo : a.module = true) (hcon : a.constants.val = [])
    {f : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f]) {c : Std.U8}
    (h : driver.cli.olean_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (nm : kernel.name.Name) (sp : frontend.olean.files.Roots),
      frontend.olean.files.parse_mod_name f = ok (some nm) ∧ driver.cli.sol_roots a = ok sp ∧
      driver.worker.check_module io s a sp nm none = ok (c, s') := by
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
  obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases b1 with
  | true => exact (usage_ne h hc).elim
  | false =>
  simp only [Bool.false_eq_true, ite_false, hsch, hmod, hmo, ite_true] at h
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
  rw [ConRon.Args.vec_index_ok' (by simp [hrs]), bind_ok] at h
  simp only [hrs] at h
  exact ⟨nm, sp, hnm, hsp, h⟩

/-- **An exit 0 of `--olean --module --trusted-search-path=T --search-path=D -- root`**: the root
a module name the Rust parsed, the worker's lookup con-leche's `CmpReq.solRoots`, its calls a
worker's (`WorkerStages`). -/
theorem run_args_module_t (hfs : AnswersAs io fs) (hpool : PoolSound io)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D root : String}
    (hargv : ArgvOf argv ["--olean", "--module", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", root]) {x x' : S}
    {code : Std.U8} (h : driver.cli.run_args io x argv = ok (code, x')) (hc : code.val = 0) :
    ∃ (nm : kernel.name.Name) (sp : frontend.olean.files.Roots),
      ConLeche.Frontend.Olean.parseModName root = some (ConRon.Refine.absName nm) ∧
      (∀ X Y, absRoots sp = (⟨X, Y, ConLeche.Driver.searchPathOf T,
        ConLeche.Driver.searchPathOf D, none⟩ : ConLeche.Driver.CmpReq).solRoots) ∧
      ∃ pins, WorkerStages fs sp nm none pins := by
  obtain ⟨w0, w1, wT, wD, wE, f0, hv, h0, h1, hT, hD, hE, hf0⟩ := argv_module_t hargv
  obtain ⟨TT, hTT⟩ := trusted_word hT
  obtain ⟨DD, hDD⟩ := search_word hD
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wE := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word g1 (by rw [h1]; simp) (by rw [h1]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_word g2 (by rw [hTT]; simp) (by rw [hTT]; simp) (usize_add_lit (b := 3#usize) rfl),
      ConRon.Args.help_word g3 (by rw [hDD]; simp) (by rw [hDD]; simp) (usize_add_lit (b := 4#usize) rfl),
      ConRon.Args.help_end g4 hE]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, hcon, htp, hsp, hfl⟩ :=
    parse_args_module_t hv h0 h1 hTT hDD hE ha
  simp only [hbad, hcg, hol, hsch, hmod, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f', hf', hf'v⟩ : ∃ f', a.files.val = [f'] ∧ f'.val = f0.val := by
    rcases hfv : a.files.val with _ | ⟨f', _ | ⟨g, l⟩⟩ <;> rw [hfv] at hfl <;> simp at hfl
    exact ⟨f', rfl, hfl⟩
  obtain ⟨nm, sp, hnm, hspR, hck⟩ := olean_args_module_t hcmp hsch hmod hmo hcon hf' h hc
  have hf3 : f'.val.map UScalar.val = root.toList.map Char.toNat := by rw [hf'v]; exact hf0
  obtain ⟨hwf, hpm⟩ := ConRon.Args.parse_mod_name_some hf3 hnm
  obtain ⟨pins, hst⟩ := check_module_zero hfs hpool hver (sol_roots_bare hspR) hwf
    (by simp) hck hc
  refine ⟨nm, sp, hpm, fun X Y => ?_, pins, hst⟩
  rw [sol_roots_abs hspR X Y, show absSearchPath a.trusted_path = _ from
    ConRon.Args.push_dirs_trusted hT htp,
    show absSearchPath a.search_path = _ from ConRon.Args.push_dirs_search hD hsp]

/-- **The compare worker, 0** (`compare_module::check_cmp_module`): the challenge walk answered
none, and the worker of the challenge, the solution added, at the solution's lookup. -/
theorem check_cmp_module_zero (hfs : AnswersAs io fs) (hpool : PoolSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {cn sn : kernel.name.Name} (hwfC : ConRon.Refine.NameWF cn)
    (hwfS : ConRon.Refine.NameWF sn) {c : Std.U8}
    (h : driver.compare_module.check_cmp_module io s a cn sn = ok (c, s')) (hc : c.val = 0) :
    ∃ sp, driver.cli.sol_roots a = ok sp ∧ ∃ pins, WorkerStages fs sp cn (some sn) pins := by
  rw [driver.compare_module.check_cmp_module] at h
  obtain ⟨o, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | some e => exact (graph_failed_ne h hc).elim
  | none =>
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨sp, hsp, check_module_zero hfs hpool hver (sol_roots_bare hsp) hwfC
    (by simpa using hwfS) h hc⟩

/-- **`--olean --module --compare` at two roots, at exit 0** (`cli::olean_args`,
`compare_olean_args`). -/
theorem olean_args_module_cmp {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = true)
    (hsch : a.scheduled = false) (hmod : a.modular = false) (hmo : a.module = true) (hcon : a.constants.val = [])
    {f0 f1 : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f0, f1]) {c : Std.U8}
    (h : driver.cli.olean_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (n0 n1 : kernel.name.Name),
      frontend.olean.files.parse_mod_name f0 = ok (some n0) ∧
      frontend.olean.files.parse_mod_name f1 = ok (some n1) ∧
      driver.compare_module.check_cmp_module io s a n0 n1 = ok (c, s') := by
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
  obtain ⟨n0, n1, hrs, h0, h1⟩ := two_roots hfiles hr
  obtain ⟨cs, hcs, hcsv⟩ := parse_const_names_nil hcon
  simp only [hcs, Aeneas.Std.bind_ok, hcmp, ite_true] at h
  rw [driver.cli.compare_olean_args] at h
  have h2 : ¬ alloc.vec.Vec.len cs > 0#usize := by
    have := alloc.vec.Vec.len_val cs
    simp [alloc.vec.Vec.length, hcsv] at this; scalar_tac
  simp only [driver.cli.cmp_mode, driver.cli.cmp_mode_bad, hmo, hmod, hsch, bind_ok, ite_true,
    Bool.false_eq_true, ite_false, ite_eq_right h2] at h
  exact ⟨n0, n1, h0, h1, two_names_ok (io := io) (s := s) (b := driver.cli.Bad.CompareTwoModules)
    (k := driver.compare_module.check_cmp_module io s a) hrs h hc⟩

/-- **An exit 0 of `--olean --module --compare --trusted-search-path=T --search-path=D -- c s`**:
the two roots module names the Rust parsed, the lookup con-leche's `CmpReq.solRoots`, the compare
worker's calls (`WorkerStages` at the solution). -/
theorem run_args_module_cmp (hfs : AnswersAs io fs) (hpool : PoolSound io)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (hargv : ArgvOf argv ["--olean", "--module", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) {x x' : S}
    {code : Std.U8} (h : driver.cli.run_args io x argv = ok (code, x')) (hc : code.val = 0) :
    ∃ (cn sn : kernel.name.Name) (sp : frontend.olean.files.Roots),
      ConLeche.Frontend.Olean.parseModName c = some (ConRon.Refine.absName cn) ∧
      ConLeche.Frontend.Olean.parseModName s = some (ConRon.Refine.absName sn) ∧
      (∀ X Y, absRoots sp = (⟨X, Y, ConLeche.Driver.searchPathOf T,
        ConLeche.Driver.searchPathOf D, none⟩ : ConLeche.Driver.CmpReq).solRoots) ∧
      ∃ pins, WorkerStages fs sp cn (some sn) pins := by
  obtain ⟨w0, w1, w2, wT, wD, wE, f0, f1, hv, h0, h1, h2, hT, hD, hE, hf0, hf1⟩ :=
    argv_module_cmp hargv
  obtain ⟨TT, hTT⟩ := trusted_word hT
  obtain ⟨DD, hDD⟩ := search_word hD
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some w2 := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g5 : argv.val[(5#usize : Std.Usize).val]? = some wE := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word g1 (by rw [h1]; simp) (by rw [h1]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_word g2 (by rw [h2]; simp) (by rw [h2]; simp) (usize_add_lit (b := 3#usize) rfl),
      ConRon.Args.help_word g3 (by rw [hTT]; simp) (by rw [hTT]; simp) (usize_add_lit (b := 4#usize) rfl),
      ConRon.Args.help_word g4 (by rw [hDD]; simp) (by rw [hDD]; simp) (usize_add_lit (b := 5#usize) rfl),
      ConRon.Args.help_end g5 hE]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, hcon, htp, hsp, hfl⟩ :=
    parse_args_module_cmp hv h0 h1 h2 hTT hDD hE ha
  simp only [hbad, hcg, hol, hsch, hmod, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f0', f1', hf', hf0', hf1'⟩ : ∃ f0' f1', a.files.val = [f0', f1'] ∧
      f0'.val = f0.val ∧ f1'.val = f1.val := by
    rcases hfv : a.files.val with _ | ⟨f0', _ | ⟨f1', _ | ⟨g, l⟩⟩⟩ <;> rw [hfv] at hfl <;>
      simp at hfl
    exact ⟨f0', f1', rfl, hfl.1, hfl.2⟩
  obtain ⟨n0, n1, hn0, hn1, hck⟩ := olean_args_module_cmp hcmp hsch hmod hmo hcon hf' h hc
  have hc0 : f0'.val.map UScalar.val = c.toList.map Char.toNat := by rw [hf0']; exact hf0
  have hc1 : f1'.val.map UScalar.val = s.toList.map Char.toNat := by rw [hf1']; exact hf1
  obtain ⟨hwf0, hpm0⟩ := ConRon.Args.parse_mod_name_some hc0 hn0
  obtain ⟨hwf1, hpm1⟩ := ConRon.Args.parse_mod_name_some hc1 hn1
  obtain ⟨sp, hspR, pins, hst⟩ := check_cmp_module_zero hfs hpool hver hwf0 hwf1 hck hc
  refine ⟨n0, n1, sp, hpm0, hpm1, fun X Y => ?_, pins, hst⟩
  rw [sol_roots_abs hspR X Y, show absSearchPath a.trusted_path = _ from
    ConRon.Args.push_dirs_trusted hT htp,
    show absSearchPath a.search_path = _ from ConRon.Args.push_dirs_search hD hsp]

end Runs

/-! ## `--olean --modular --compare`: every module in one process -/

/-- A one-name `InternRoots` and one more name interned after it. -/
theorem internRoots_snoc1 {pers : arena.store.PersTier} {st st1 st2 : arena.monad.AState}
    {n s : kernel.name.Name} {hs : List arena.handle.NIdx} {sh : arena.handle.NIdx}
    (hA : InternRoots pers st [n] hs st1) (hwf : ConRon.Refine.NameWF s)
    (hi : arena.monad.intern_name pers st1 s = ok (.Ok sh, st2)) :
    ∃ h, hs = [h] ∧ InternRoots pers st [n, s] [h, sh] st2 := by
  rcases hs with _ | ⟨h, _ | ⟨h', hs'⟩⟩
  · simp [InternRoots] at hA
  · obtain ⟨hwfn, st₁, hn, hrest⟩ := hA
    have hrest : st1 = st₁ := hrest
    subst hrest
    exact ⟨h, rfl, hwfn, st1, hn, hwf, st2, hi, rfl⟩
  · obtain ⟨_, _, _, hrest⟩ := hA
    simp [InternRoots] at hrest

/-- **The graph check of a compared `--modular`, its modules read back**: `rust_graph_cmp`'s
facts, the closure's modules the names `graph_names` read. -/
theorem rust_graph_cmp_names {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {spR : frontend.olean.files.Roots} (hsp : (absRoots spR).bare = absRoots spR)
    {cName sName : kernel.name.Name}
    {st1 stR : arena.monad.AState} {store2 store3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {c s : arena.handle.NIdx}
    {roots : alloc.vec.Vec arena.handle.NIdx} (hrv : roots.val = [c])
    {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (hpk : frontend.olean.spec.olean_pins emptyTier st1.store = ok (.Ok pk, store2))
    (hroots : InternRoots emptyTier { st1 with store := store2 } [cName, sName] [c, s] stR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier stR.store spR roots (some (c, s))
      = ok (.Ok cg, store3))
    {ns : alloc.vec.Vec kernel.name.Name}
    (hns : driver.modular.graph_names emptyTier { stR with store := store3 } cg = ok (.Ok ns)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ CC, ConLeche.Driver.Graph.NodeOk (absRoots spR) F
        (ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName) (ConRon.Refine.absName sName)) e) ∧
      ConRon.Refine.absName cName ∈ CC.map (·.1) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] e.1) ∧
      CC.map (·.1) = ns.val.map ConRon.Refine.absName ∧ ∀ n ∈ ns.val, ConRon.Refine.NameWF n := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := emptyTier) rfl hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ := (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨pk', sB, hB, rfl, hrelB, hinvB⟩ := olean_pins_refines hrelA hinvA _ _ hpk
  obtain ⟨sC, hC, hrelC, hinvC⟩ := internRoots_refines [cName, sName] [c, s] hroots hrelB hinvB
  obtain ⟨C, sD, hD, rfl, hrelD, hinvD⟩ :=
    ConRon.Refine2.Modular.graph_of_refines (fsRel_of_snapshot hsnap) hrelC hinvC _ _ hgraph
  rw [hrv] at hD
  obtain ⟨CC, rk, hlr, good, hr, edges, inj, hhdr⟩ :=
    ConRon.Bridge.Modular.graphStageCmp_run_nodes hsp hA hB hC hD
  refine ⟨CC, rk, good, hr, edges, inj, hhdr, ?_⟩
  obtain ⟨hn, hw⟩ := graph_names_loop_val (st := { stR with store := store3 }) hrelD hinvD cg _ _
    0#usize CC rfl (by simp) (by simpa using hlr) (by simp [alloc.vec.Vec.new]) hns
  exact ⟨by rw [hn]; simp, hw⟩

/-- **What an exit 0 of `--olean --modular --compare` ran**: the compared graph check's calls at
the lookup `spR`, its modules read back, and at every one of them, well formed, a worker's calls,
the challenge's the compare worker's. -/
inductive ModularCmpStages (fs : ConLeche.FS) (cName sName : kernel.name.Name)
    (spR : frontend.olean.files.Roots) : Prop where
  | intro {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
      {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
      {pk : frontend.olean.spec.OleanPins} {gc gs : arena.handle.NIdx}
      {groots : alloc.vec.Vec arena.handle.NIdx}
      {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
      {ns : alloc.vec.Vec kernel.name.Name}
      (hsnap : SnapshotOf finst fsv fs) (hgr : groots.val = [gc])
      (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
      (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
      (hroots : InternRoots emptyTier { g1 with store := gstore2 } [cName, sName] [gc, gs] gR)
      (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store spR groots
        (some (gc, gs)) = ok (.Ok cg, gstore3))
      (hns : driver.modular.graph_names emptyTier { gR with store := gstore3 } cg = ok (.Ok ns))
      (hwork : ∀ k (hk : k < ns.val.length), ConRon.Refine.NameWF ns.val[k] →
        ∃ pins, WorkerStages fs spR ns.val[k]
          (if ConRon.Refine.absName ns.val[k] = ConRon.Refine.absName cName then some sName
            else none) pins) :
      ModularCmpStages fs cName sName spR

section OneCmp

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **A module's step at a compared run** (`modular::step_sol`): the solution at the challenge,
none elsewhere. -/
theorem step_sol_some {m root s : kernel.name.Name} (hm : ConRon.Refine.NameWF m)
    (hr : ConRon.Refine.NameWF root) {o : Option kernel.name.Name}
    (h : driver.modular.step_sol m root (some s) = ok o) :
    o = if ConRon.Refine.absName m = ConRon.Refine.absName root then some s else none := by
  simp only [driver.modular.step_sol] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Refine.Name.name_beq_exact' hm hr hb] at h
  by_cases he : ConRon.Refine.absName m = ConRon.Refine.absName root
  · simp only [he, decide_true, ite_true, Result.ok.injEq] at h
    simp only [he, ↓reduceIte]; exact h.symm
  · simp only [he, decide_false, Bool.false_eq_true, ite_false, Result.ok.injEq] at h
    simp only [he, ↓reduceIte]; exact h.symm

/-- **The one-process comparison, 0** (`modular::check_modular` at the solution, `--verified`,
the embedded pins): the compared graph check's calls, and at every module of it, its worker's,
the challenge's the compare worker. -/
theorem check_modular_cmp_zero (hfs : AnswersAs io fs) (hcodes : CodesSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {roots : alloc.vec.Vec kernel.name.Name} {cName sName : kernel.name.Name}
    (hroots1 : roots.val = [cName]) (hwfC : ConRon.Refine.NameWF cName)
    (hwfS : ConRon.Refine.NameWF sName)
    {sp : frontend.olean.files.Roots} (hbare : (absRoots sp).bare = absRoots sp) {c : Std.U8}
    (h : driver.modular.check_modular io s a roots sp (some sName) = ok (c, s'))
    (hc : c.val = 0) : ModularCmpStages fs cName sName sp := by
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
  have hir := intern_names_roots (by rw [hroots1]; intro n hn; simp at hn; subst hn; exact hwfC) hr1
  rw [hroots1] at hir
  obtain ⟨⟨r2, st3⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok sh =>
  obtain ⟨gc, hrs, hir2⟩ := internRoots_snoc1 hir hwfS hr2
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.vec_index_ok' (by simp [hrs])] at hn
  simp only [hrs, Result.ok.injEq] at hn
  subst hn
  simp only [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2, Result.ok.injEq] at hn1
  subst hn1
  obtain ⟨⟨r3, gstore3⟩, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok cg =>
  obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.vec_index_ok' (by simp [hroots1])] at hn2
  simp [hroots1] at hn2
  subst hn2
  obtain ⟨o, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | some e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | none =>
  obtain ⟨r4, hr4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r4 with
  | Err e => exact (graph_failed_ne h hc).elim
  | Ok ns =>
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨jobs, io2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨threads, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r5, io3⟩, hpar, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r5 with
  | Err m =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok cs =>
  obtain ⟨io4, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hall := modular_verdict_zero h hc
  obtain ⟨hlen, hcode⟩ := hcodes _ _ io2 _ _ cs io3 hpar
  obtain ⟨-, -, -, -, -, -, -, hwfns⟩ :=
    rust_graph_cmp_names (hfs io1) hbare hrs h1g hpk hir2 hg hr4
  refine ModularCmpStages.intro (hfs io1) hrs h1g hpk hir2 hg hr4 ?_
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
  simp only [UScalar.ofNatCore_val_eq, hver] at hc0
  obtain ⟨o, ho, hc0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hc0
  have ho' := step_sol_some hwk hwfC ho
  subst ho'
  refine check_module_in_zero (hfs io2) hbare hwk ?_ hc0 rfl
  split <;> simp [hwfS]

end OneCmp

/-! ## The compositions -/

/-- **The family of models of a compared modular check**, from the compared graph check's
facts at the lookup `R` and an accepted worker at every module of the graph, each at a lookup
`R` too and adding con-leche's `cmpExtra` (upstream's `compare_sees_isModel`). -/
theorem cmp_family (V : Type w) [ConLeche.SetTheory V] {fs : ConLeche.FS}
    {C S : ConLeche.Name} {T D : ConLeche.Frontend.Olean.SearchPath}
    {Cg : List ConLeche.Driver.Graph.Node} {rk : ConLeche.Name → Nat}
    (good : ∀ e ∈ Cg, ConLeche.Driver.Graph.NodeOk (⟨C, S, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs
      (ConLeche.Driver.Graph.cmpExtra C S) e)
    (hC : C ∈ Cg.map (·.1))
    (edges : ∀ e ∈ Cg, ∀ i ∈ e.2, i.module ∈ Cg.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (Cg.map fun e => rk e.1).Nodup)
    (hhdr : ∀ e ∈ Cg, ConLeche.Frontend.Olean.HdrClosure (⟨C, S, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs [C, S] e.1)
    (hacc : ∀ M ∈ Cg.map (·.1), ∃ (pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet)
        (mName : kernel.name.Name) (sol : Option kernel.name.Name) (sp : frontend.olean.files.Roots),
      ConRon.Refine.absName mName = M ∧
      absRoots sp = (⟨C, S, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots ∧
      solX sol = ConLeche.Driver.Graph.cmpExtra C S M ∧ WorkerStages fs sp mName sol pins) :
    ∀ fs', ConLeche.FS.AgreeUnder (ConLeche.Driver.trustedOr T D) fs fs' →
      ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
        (∀ m, ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs' #[C] m →
          ConLeche.IsModel V (model m)
            (ConLeche.Frontend.Olean.moduleConstants (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs' m)) ∧
        (∀ m n m', ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs' #[C] m →
          ConLeche.Frontend.Olean.Sees (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs' m n m' →
          model m n = model m' n) := by
  obtain ⟨pins0, m0, sol0, sp0, hm0, hsp0, hx0, hw0⟩ := hacc C hC
  refine ConLeche.Driver.Compose.compare_sees_isModel (pins := ConRon.Refine.absPins pins0) V Cg rk
    good hC edges inj hhdr (fun M hM => ?_)
  obtain ⟨pins, mName, sol, sp, hmn, hsp, hx, hw⟩ := hacc M hM
  have hpe : pins = pins0 := by
    have := hw.hpins.symm.trans hw0.hpins
    simpa using this
  subst hpe
  have := hw.accepted
  rw [hsp, hx, hmn] at this
  exact ⟨1, this⟩

/-- `cmp_family`'s conclusion at the challenge's private part: no constant of type `False`
(upstream's `compare_no_False`). -/
theorem cmp_no_False {fs : ConLeche.FS} {C S : ConLeche.Name}
    {T D : ConLeche.Frontend.Olean.SearchPath}
    {Cg : List ConLeche.Driver.Graph.Node} {rk : ConLeche.Name → Nat}
    (good : ∀ e ∈ Cg, ConLeche.Driver.Graph.NodeOk (⟨C, S, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs
      (ConLeche.Driver.Graph.cmpExtra C S) e)
    (hC : C ∈ Cg.map (·.1))
    (edges : ∀ e ∈ Cg, ∀ i ∈ e.2, i.module ∈ Cg.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (Cg.map fun e => rk e.1).Nodup)
    (hhdr : ∀ e ∈ Cg, ConLeche.Frontend.Olean.HdrClosure (⟨C, S, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs [C, S] e.1)
    (hacc : ∀ M ∈ Cg.map (·.1), ∃ (pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet)
        (mName : kernel.name.Name) (sol : Option kernel.name.Name) (sp : frontend.olean.files.Roots),
      ConRon.Refine.absName mName = M ∧
      absRoots sp = (⟨C, S, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots ∧
      solX sol = ConLeche.Driver.Graph.cmpExtra C S M ∧ WorkerStages fs sp mName sol pins)
    (V : Type w) [ConLeche.SetTheory V] {m : ConLeche.Name} {ci : ConLeche.ConstantInfo}
    (hcl : ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs #[C] m)
    (hci : ConLeche.Frontend.Olean.InModulePart (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs m .private ci)
    (hty : ci.type = .const ConLeche.falseName []) : False := by
  obtain ⟨pins0, m0, sol0, sp0, hm0, hsp0, hx0, hw0⟩ := hacc C hC
  refine ConLeche.Driver.Compose.compare_no_False (pins := ConRon.Refine.absPins pins0) V Cg rk
    good hC edges inj hhdr (fun M hM => ?_) hcl hci hty
  obtain ⟨pins, mName, sol, sp, hmn, hsp, hx, hw⟩ := hacc M hM
  have hpe : pins = pins0 := by
    have := hw.hpins.symm.trans hw0.hpins
    simpa using this
  subst hpe
  have := hw.accepted
  rw [hsp, hx, hmn] at this
  exact ⟨1, this⟩

/-- `solX` at a module's step: the solution at the challenge, none elsewhere, is `cmpExtra`. -/
theorem solX_step (C S : kernel.name.Name) (m : kernel.name.Name) :
    solX (if ConRon.Refine.absName m = ConRon.Refine.absName C then some S else none) =
      ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName C) (ConRon.Refine.absName S)
        (ConRon.Refine.absName m) := by
  by_cases he : ConRon.Refine.absName m = ConRon.Refine.absName C
  · simp [solX, ConLeche.Driver.Graph.cmpExtra, he]
  · simp [solX, ConLeche.Driver.Graph.cmpExtra, he]

/-- **`--olean --modular --compare`'s family**: the graph's facts, its modules read back, the
workers the code map's. -/
theorem modular_cmp_one_of_stages (V : Type w) [ConLeche.SetTheory V] {fs : ConLeche.FS}
    {cName sName : kernel.name.Name} {spR : frontend.olean.files.Roots}
    {T D : ConLeche.Frontend.Olean.SearchPath}
    (hsr : absRoots spR = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName, T, D, none⟩ :
      ConLeche.Driver.CmpReq).solRoots)
    (hm : ModularCmpStages fs cName sName spR) :
    ∀ fs', ConLeche.FS.AgreeUnder (ConLeche.Driver.trustedOr T D) fs fs' →
      ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
        (∀ m, ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs'
            #[ConRon.Refine.absName cName] m →
          ConLeche.IsModel V (model m)
            (ConLeche.Frontend.Olean.moduleConstants (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs' m)) ∧
        (∀ m n m', ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs'
            #[ConRon.Refine.absName cName] m →
          ConLeche.Frontend.Olean.Sees (ConLeche.Driver.trustedOr T D : ConLeche.Frontend.Olean.Roots) fs' m n m' →
          model m n = model m' n) := by
  have hbare : (absRoots spR).bare = absRoots spR := by rw [hsr]; exact solRoots_bare _
  cases hm with
  | intro hsnap hgr h1g hpk hroots hgraph hns hwork =>
  obtain ⟨CC, rk, good, hC, edges, inj, hhdr, hnames, hwf⟩ :=
    rust_graph_cmp_names hsnap hbare hgr h1g hpk hroots hgraph hns
  rw [hsr] at good hhdr
  refine cmp_family V good hC edges inj hhdr (fun M hM => ?_)
  rw [hnames] at hM
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hM
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨pins, hw⟩ := hwork k hk (hwf _ (List.getElem_mem hk))
  exact ⟨pins, _, _, spR, rfl, hsr, solX_step cName sName _, hw⟩

/-- **The graph check's and the workers' runs, composed** (`main_modular_compare`'s proof): the
compared graph check of `cName` and `sName` at the lookup `spR`, a worker at every module of the
headers' closure but the challenge, and the compare worker at it, each its own run on the one
snapshot, each at a lookup with the same directories. -/
theorem modular_cmp_of_stages {fs : ConLeche.FS} {cName sName : kernel.name.Name}
    {spR : frontend.olean.files.Roots} {T D : ConLeche.Frontend.Olean.SearchPath}
    (hsr : absRoots spR = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName, T, D, none⟩ :
      ConLeche.Driver.CmpReq).solRoots)
    (hg : GraphCmpStages fs cName sName spR)
    (hwork : ∀ m, ConLeche.Frontend.Olean.HdrClosure (⟨ConRon.Refine.absName cName,
        ConRon.Refine.absName sName, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] m →
      m ≠ ConRon.Refine.absName cName →
      ∃ (mName : kernel.name.Name) (sp : frontend.olean.files.Roots) (pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet),
        ConRon.Refine.absName mName = m ∧
        absRoots sp = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName, T, D, none⟩ :
          ConLeche.Driver.CmpReq).solRoots ∧ WorkerStages fs sp mName none pins)
    {spC : frontend.olean.files.Roots} {pinsC : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hspC : absRoots spC = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName, T, D, none⟩ :
      ConLeche.Driver.CmpReq).solRoots)
    {cName' sName' : kernel.name.Name}
    (hc' : ConRon.Refine.absName cName' = ConRon.Refine.absName cName)
    (hs' : ConRon.Refine.absName sName' = ConRon.Refine.absName sName)
    (hcmp : WorkerStages fs spC cName' (some sName') pinsC) :
    ∃ (Cg : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ Cg, ConLeche.Driver.Graph.NodeOk (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName, T, D, none⟩ :
        ConLeche.Driver.CmpReq).solRoots fs
        (ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName) (ConRon.Refine.absName sName)) e) ∧
      ConRon.Refine.absName cName ∈ Cg.map (·.1) ∧
      (∀ e ∈ Cg, ∀ i ∈ e.2, i.module ∈ Cg.map (·.1) ∧ rk i.module < rk e.1) ∧
      (Cg.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ Cg, ConLeche.Frontend.Olean.HdrClosure (⟨ConRon.Refine.absName cName,
        ConRon.Refine.absName sName, T, D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] e.1) ∧
      (∀ M ∈ Cg.map (·.1), ∃ (pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet)
          (mName : kernel.name.Name) (sol : Option kernel.name.Name) (sp : frontend.olean.files.Roots),
        ConRon.Refine.absName mName = M ∧
        absRoots sp = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName, T, D, none⟩ :
          ConLeche.Driver.CmpReq).solRoots ∧
        solX sol = ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName)
          (ConRon.Refine.absName sName) M ∧ WorkerStages fs sp mName sol pins) := by
  have hbare : (absRoots spR).bare = absRoots spR := by rw [hsr]; exact solRoots_bare _
  obtain ⟨Cg, rk, good, hC, edges, inj, hhdr⟩ := hg.facts hbare
  rw [hsr] at good hhdr
  refine ⟨Cg, rk, good, hC, edges, inj, hhdr, fun M hM => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  by_cases hce : e.1 = ConRon.Refine.absName cName
  · refine ⟨pinsC, cName', some sName', spC, hc'.trans hce.symm, hspC, ?_, hcmp⟩
    rw [hce]; simp [solX, ConLeche.Driver.Graph.cmpExtra, hs']
  · obtain ⟨mName, sp, pins, hmn, hsp, hw⟩ := hwork e.1 (hhdr e he) hce
    refine ⟨pins, mName, none, sp, hmn, hsp, ?_, hw⟩
    simp [solX, ConLeche.Driver.Graph.cmpExtra, hce]

/-! ## The run of `--olean --modular --compare` -/

section RunOneCmp

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **`--olean --modular --compare` at two roots, at exit 0** (`cli::olean_args`,
`compare_olean_args`): the one-process mode at the challenge alone, the solution added, at the
solution's lookup. -/
theorem olean_args_modular_cmp {s s' : S} {a : driver.cli.Args} (hcmp : a.compare = true)
    (hsch : a.scheduled = false) (hmod : a.modular = true) (hmo : a.module = false) (hcon : a.constants.val = [])
    {f0 f1 : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [f0, f1]) {c : Std.U8}
    (h : driver.cli.olean_args io s a = ok (c, s')) (hc : c.val = 0) :
    ∃ (n0 n1 : kernel.name.Name) (rs : alloc.vec.Vec kernel.name.Name)
      (sp : frontend.olean.files.Roots),
      frontend.olean.files.parse_mod_name f0 = ok (some n0) ∧
      frontend.olean.files.parse_mod_name f1 = ok (some n1) ∧ rs.val = [n0] ∧
      driver.cli.sol_roots a = ok sp ∧
      driver.modular.check_modular io s a rs sp (some n1) = ok (c, s') := by
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
  obtain ⟨n0, n1, hrs, h0, h1⟩ := two_roots hfiles hr
  obtain ⟨cs, hcs, hcsv⟩ := parse_const_names_nil hcon
  simp only [hcs, Aeneas.Std.bind_ok, hcmp, ite_true] at h
  rw [driver.cli.compare_olean_args] at h
  have h2 : ¬ alloc.vec.Vec.len cs > 0#usize := by
    have := alloc.vec.Vec.len_val cs
    simp [alloc.vec.Vec.length, hcsv] at this; scalar_tac
  simp only [driver.cli.cmp_mode, driver.cli.cmp_mode_bad, hmo, hmod, hsch, bind_ok, ite_true,
    Bool.false_eq_true, ite_false, ite_eq_right h2] at h
  have h' := two_names_ok (io := io) (s := s) (b := driver.cli.Bad.CompareTwoModules)
    (k := fun n n1 => (do
      let sp ← driver.cli.sol_roots a
      let n2 ← kernel.name.dup n
      let rs ← alloc.vec.Vec.push (alloc.vec.Vec.new kernel.name.Name) n2
      driver.modular.check_modular io s a rs sp (some n1))) hrs h hc
  simp only [ConRon.Refine.name_dup_eq, bind_ok] at h'
  obtain ⟨sp, hsp, h'⟩ := ConRon.Refine.bind_eq_ok_iff.mp h'
  obtain ⟨rs1, hrs1, h'⟩ := ConRon.Refine.bind_eq_ok_iff.mp h'
  exact ⟨n0, n1, rs1, sp, h0, h1, by rw [ConRon.Refine.vec_push_val hrs1]; rfl, hsp, h'⟩

/-- **An exit 0 of `--olean --modular --compare --trusted-search-path=T --search-path=D -- c s`**:
the two roots module names the Rust parsed, the lookup con-leche's `CmpReq.solRoots`, the run's
calls `ModularCmpStages`. -/
theorem run_args_modular_cmp (hfs : AnswersAs io fs) (hcodes : CodesSound io)
    {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (hargv : ArgvOf argv ["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) {x x' : S}
    {code : Std.U8} (h : driver.cli.run_args io x argv = ok (code, x')) (hc : code.val = 0) :
    ∃ (cn sn : kernel.name.Name) (sp : frontend.olean.files.Roots),
      ConLeche.Frontend.Olean.parseModName c = some (ConRon.Refine.absName cn) ∧
      ConLeche.Frontend.Olean.parseModName s = some (ConRon.Refine.absName sn) ∧
      (∀ X Y, absRoots sp = (⟨X, Y, ConLeche.Driver.searchPathOf T,
        ConLeche.Driver.searchPathOf D, none⟩ : ConLeche.Driver.CmpReq).solRoots) ∧
      ModularCmpStages fs cn sn sp := by
  obtain ⟨w0, w1, w2, wT, wD, wE, f0, f1, hv, h0, h1, h2, hT, hD, hE, hf0, hf1⟩ :=
    argv_modular_cmp hargv
  obtain ⟨TT, hTT⟩ := trusted_word hT
  obtain ⟨DD, hDD⟩ := search_word hD
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some w2 := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g5 : argv.val[(5#usize : Std.Usize).val]? = some wE := by simp [hv]
  have hhelp : driver.cli.help_wanted argv = ok false := by
    rw [driver.cli.help_wanted,
      ConRon.Args.help_word g0 (by rw [h0]; simp) (by rw [h0]; simp) (usize_add_lit (b := 1#usize) rfl),
      ConRon.Args.help_word g1 (by rw [h1]; simp) (by rw [h1]; simp) (usize_add_lit (b := 2#usize) rfl),
      ConRon.Args.help_word g2 (by rw [h2]; simp) (by rw [h2]; simp) (usize_add_lit (b := 3#usize) rfl),
      ConRon.Args.help_word g3 (by rw [hTT]; simp) (by rw [hTT]; simp) (usize_add_lit (b := 4#usize) rfl),
      ConRon.Args.help_word g4 (by rw [hDD]; simp) (by rw [hDD]; simp) (usize_add_lit (b := 5#usize) rfl),
      ConRon.Args.help_end g5 hE]
  rw [driver.cli.run_args, hhelp, bind_ok] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsch, hmod, hmo, hver, hcon, htp, hsp, hfl⟩ :=
    parse_args_modular_cmp hv h0 h1 h2 hTT hDD hE ha
  simp only [hbad, hcg, hol, Bool.false_eq_true, ite_false, ite_true] at h
  obtain ⟨f0', f1', hf', hf0', hf1'⟩ : ∃ f0' f1', a.files.val = [f0', f1'] ∧
      f0'.val = f0.val ∧ f1'.val = f1.val := by
    rcases hfv : a.files.val with _ | ⟨f0', _ | ⟨f1', _ | ⟨g, l⟩⟩⟩ <;> rw [hfv] at hfl <;>
      simp at hfl
    exact ⟨f0', f1', rfl, hfl.1, hfl.2⟩
  obtain ⟨n0, n1, rs, spR, hn0, hn1, hrs, hspR, hck⟩ :=
    olean_args_modular_cmp hcmp hsch hmod hmo hcon hf' h hc
  have hc0 : f0'.val.map UScalar.val = c.toList.map Char.toNat := by rw [hf0']; exact hf0
  have hc1 : f1'.val.map UScalar.val = s.toList.map Char.toNat := by rw [hf1']; exact hf1
  obtain ⟨hwf0, hpm0⟩ := ConRon.Args.parse_mod_name_some hc0 hn0
  obtain ⟨hwf1, hpm1⟩ := ConRon.Args.parse_mod_name_some hc1 hn1
  have hst := check_modular_cmp_zero hfs hcodes hver hrs hwf0 hwf1 (sol_roots_bare hspR) hck hc
  refine ⟨n0, n1, spR, hpm0, hpm1, fun X Y => ?_, hst⟩
  rw [sol_roots_abs hspR X Y, show absSearchPath a.trusted_path = _ from
    ConRon.Args.push_dirs_trusted hT htp,
    show absSearchPath a.search_path = _ from ConRon.Args.push_dirs_search hD hsp]

end RunOneCmp

/-! ## From the run premises -/

/-- **The three runs of `main_modular_compare`, unpacked**: the graph check's and the workers'
stages, composed (`modular_cmp_of_stages`), in con-leche's names. -/
theorem modular_cmp_facts_of_canGive {T D c s : String} {C S : ConLeche.Name} {fs : ConLeche.FS}
    (hc : ConLeche.Frontend.Olean.parseModName c = some C)
    (hs : ConLeche.Frontend.Olean.parseModName s = some S)
    (hgraph : CanGiveConforming ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] fs 0)
    (hwork : ∀ m, ConLeche.Frontend.Olean.HdrClosure
        (⟨C, S, ConLeche.Driver.searchPathOf T, ConLeche.Driver.searchPathOf D, none⟩ :
          ConLeche.Driver.CmpReq).solRoots fs [C, S] m → m ≠ C →
      ∃ root', ConLeche.Frontend.Olean.parseModName root' = some m ∧ CanGiveConforming
        ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
          root'] fs 0)
    (hcmp : CanGiveConforming ["--olean", "--module", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] fs 0) :
    ∃ (Cg : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ Cg, ConLeche.Driver.Graph.NodeOk (⟨C, S, ConLeche.Driver.searchPathOf T,
        ConLeche.Driver.searchPathOf D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs
        (ConLeche.Driver.Graph.cmpExtra C S) e) ∧
      C ∈ Cg.map (·.1) ∧
      (∀ e ∈ Cg, ∀ i ∈ e.2, i.module ∈ Cg.map (·.1) ∧ rk i.module < rk e.1) ∧
      (Cg.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ Cg, ConLeche.Frontend.Olean.HdrClosure (⟨C, S, ConLeche.Driver.searchPathOf T,
        ConLeche.Driver.searchPathOf D, none⟩ : ConLeche.Driver.CmpReq).solRoots fs [C, S] e.1) ∧
      (∀ M ∈ Cg.map (·.1), ∃ (pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet)
          (mName : kernel.name.Name) (sol : Option kernel.name.Name) (sp : frontend.olean.files.Roots),
        ConRon.Refine.absName mName = M ∧
        absRoots sp = (⟨C, S, ConLeche.Driver.searchPathOf T, ConLeche.Driver.searchPathOf D, none⟩ :
          ConLeche.Driver.CmpReq).solRoots ∧
        solX sol = ConLeche.Driver.Graph.cmpExtra C S M ∧ WorkerStages fs sp mName sol pins) := by
  obtain ⟨S1, io, x, x', argv, code, hfs, -, -, hargv, hrun, hcode⟩ := hgraph
  obtain ⟨cn, sn, spR, hpc, hps, hsr, hg⟩ := run_args_graph_cmp hfs hargv hrun (by simpa using hcode)
  have hcn : ConRon.Refine.absName cn = C := Option.some.inj (hpc.symm.trans hc)
  have hsn : ConRon.Refine.absName sn = S := Option.some.inj (hps.symm.trans hs)
  obtain ⟨S2, io2, x2, x2', argv2, code2, hfs2, hpool2, -, hargv2, hrun2, hcode2⟩ := hcmp
  obtain ⟨cn', sn', spC, hpc', hps', hspC, pinsC, hwC⟩ :=
    run_args_module_cmp hfs2 hpool2 hargv2 hrun2 (by simpa using hcode2)
  have hcn' : ConRon.Refine.absName cn' = ConRon.Refine.absName cn :=
    Option.some.inj (hpc'.symm.trans hpc)
  have hsn' : ConRon.Refine.absName sn' = ConRon.Refine.absName sn :=
    Option.some.inj (hps'.symm.trans hps)
  have := modular_cmp_of_stages (T := ConLeche.Driver.searchPathOf T)
    (D := ConLeche.Driver.searchPathOf D) (hsr _ _) hg
    (fun m hm hne => by
      rw [hcn, hsn] at hm
      rw [hcn] at hne
      obtain ⟨root', hroot', hcg⟩ := hwork m hm hne
      obtain ⟨S3, io3, x3, x3', argv3, code3, hfs3, hpool3, -, hargv3, hrun3, hcode3⟩ := hcg
      obtain ⟨nm, sp, hpm, hsp, pins, hw⟩ :=
        run_args_module_t hfs3 hpool3 hargv3 hrun3 (by simpa using hcode3)
      exact ⟨nm, sp, pins, Option.some.inj (hpm.symm.trans hroot'), hsp _ _, hw⟩)
    (hspC _ _) hcn' hsn' hwC
  rw [hcn, hsn] at this
  exact this

/-- **`main_modular_compare_one`'s conclusion from an exit 0**. -/
theorem modular_cmp_one_of_canGive (V : Type w) [ConLeche.SetTheory V] {T D c s : String}
    {C S : ConLeche.Name} {fs : ConLeche.FS}
    (hc : ConLeche.Frontend.Olean.parseModName c = some C)
    (hs : ConLeche.Frontend.Olean.parseModName s = some S)
    (h : CanGiveConforming ["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] fs 0) :
    ∀ fs', ConLeche.FS.AgreeUnder (ConLeche.Driver.trustedOr (ConLeche.Driver.searchPathOf T)
        (ConLeche.Driver.searchPathOf D)) fs fs' →
      ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
        (∀ m, ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.trustedOr (ConLeche.Driver.searchPathOf T)
            (ConLeche.Driver.searchPathOf D) : ConLeche.Frontend.Olean.Roots) fs' #[C] m →
          ConLeche.IsModel V (model m) (ConLeche.Frontend.Olean.moduleConstants
            (ConLeche.Driver.trustedOr (ConLeche.Driver.searchPathOf T)
              (ConLeche.Driver.searchPathOf D) : ConLeche.Frontend.Olean.Roots) fs' m)) ∧
        (∀ m n m', ConLeche.Frontend.Olean.InClosure (ConLeche.Driver.trustedOr
            (ConLeche.Driver.searchPathOf T) (ConLeche.Driver.searchPathOf D) :
              ConLeche.Frontend.Olean.Roots) fs' #[C] m →
          ConLeche.Frontend.Olean.Sees (ConLeche.Driver.trustedOr (ConLeche.Driver.searchPathOf T)
            (ConLeche.Driver.searchPathOf D) : ConLeche.Frontend.Olean.Roots) fs' m n m' →
          model m n = model m' n) := by
  obtain ⟨S1, io, x, x', argv, code, hfs, -, hcodes, hargv, hrun, hcode⟩ := h
  obtain ⟨cn, sn, sp, hpc, hps, hsr, hm⟩ :=
    run_args_modular_cmp hfs hcodes hargv hrun (by simpa using hcode)
  have hcn : ConRon.Refine.absName cn = C := Option.some.inj (hpc.symm.trans hc)
  have hsn : ConRon.Refine.absName sn = S := Option.some.inj (hps.symm.trans hs)
  have := modular_cmp_one_of_stages V (hsr _ _) hm
  rw [hcn] at this
  exact this

end ConRon.MainTheorem
