import ConRon.MainTheorem.Oleans

/-!
# `ConRon.MainTheorem.ModArgs` — the parses of `--check-graph`, `--olean --module` and
`--olean --modular` at one root

**Task #171, slice 2**: `Oleans.lean`'s `parse_args_oleans` and `argv_oleans` at the three other
argument lists of con-leche's modular theorems.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.MainTheorem.Stages
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

namespace ConRon.MainTheorem

set_option autoImplicit false

/-- **The parse of `["--check-graph", "--search-path=" ++ dirs, "--", root]`**: `--check-graph`, the
search path the directories, the one file `root`, every other default. -/
theorem parse_args_graph {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 w1 w2 w3 : alloc.vec.Vec Std.U32} {T : List Std.U32}
    (hv : argv.val = [w0, w1, w2, w3])
    (h0 : w0.val = [45#u32, 45#u32, 99#u32, 104#u32, 101#u32, 99#u32, 107#u32, 45#u32, 103#u32,
      114#u32, 97#u32, 112#u32, 104#u32])
    (h1 : w1.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32,
      112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T)
    (h2 : w2.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = true ∧ a.olean = false ∧ a.compare = false ∧
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
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_check_graph g0 h0)
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

/-- `["--check-graph", "--search-path=" ++ dirs, "--", root]`'s `argv`. -/
theorem argv_graph {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (h : ArgvOf argv ["--check-graph", "--search-path=" ++ dirs, "--", root]) :
    ∃ w0 w1 w2 w3, argv.val = [w0, w1, w2, w3] ∧
      w0.val = [45#u32, 45#u32, 99#u32, 104#u32, 101#u32, 99#u32, 107#u32, 45#u32, 103#u32,
        114#u32, 97#u32, 112#u32, 104#u32] ∧
      w1.val.map UScalar.val = ("--search-path=" ++ dirs).toList.map Char.toNat ∧
      w2.val = [45#u32, 45#u32] ∧ w3.val.map UScalar.val = root.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, l⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨w0, w1, w2, w3, rfl, vals_eq (h0.trans (by decide)), h1, vals_eq (h2.trans (by decide)),
    h3⟩

/-- **The parse of `["--olean", "--module", "--search-path=" ++ dirs, "--", root]`**: `--olean`, `--module`, the
search path the directories, the one file `root`, every other default. -/
theorem parse_args_module {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 wm w1 w2 w3 : alloc.vec.Vec Std.U32} {T : List Std.U32}
    (hv : argv.val = [w0, wm, w1, w2, w3])
    (h0 : w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32])
    (hm : wm.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32])
    (h1 : w1.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32,
      112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T)
    (h2 : w2.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = true ∧ a.compare = false ∧
      a.scheduled = false ∧ a.modular = false ∧ a.module = true ∧
      a.verified = true ∧ a.trusted_path.val = [] ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) w1 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [w3.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have gm : argv.val[(1#usize : Std.Usize).val]? = some wm := by simp [hv]
  have g1 : argv.val[(2#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(3#usize : Std.Usize).val]? = some w2 := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_olean g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_word gm (by rw [hm]; simp) (ConRon.Args.parse_one_module gm hm)
    (usize_add_lit (b := 2#usize) rfl)] at h
  rw [ConRon.Args.loop_search g1 h1 (usize_add_lit (b := 3#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g2 h2 (usize_add_lit (b := 4#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 4#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsp, ?_⟩
  simpa using hf

/-- `["--olean", "--module", "--search-path=" ++ dirs, "--", root]`'s `argv`. -/
theorem argv_module {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (h : ArgvOf argv ["--olean", "--module", "--search-path=" ++ dirs, "--", root]) :
    ∃ w0 wm w1 w2 w3, argv.val = [w0, wm, w1, w2, w3] ∧
      w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] ∧
      wm.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32] ∧
      w1.val.map UScalar.val = ("--search-path=" ++ dirs).toList.map Char.toNat ∧
      w2.val = [45#u32, 45#u32] ∧ w3.val.map UScalar.val = root.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨wm, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, l⟩⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, hm, h1, h2, h3⟩ := h
  refine ⟨w0, wm, w1, w2, w3, rfl, vals_eq (h0.trans (by decide)), vals_eq (hm.trans (by decide)), h1, vals_eq (h2.trans (by decide)),
    h3⟩

/-- **The parse of `["--olean", "--modular", "--search-path=" ++ dirs, "--", root]`**: `--olean`, `--modular`, the
search path the directories, the one file `root`, every other default. -/
theorem parse_args_modular {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 wm w1 w2 w3 : alloc.vec.Vec Std.U32} {T : List Std.U32}
    (hv : argv.val = [w0, wm, w1, w2, w3])
    (h0 : w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32])
    (hm : wm.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 97#u32, 114#u32])
    (h1 : w1.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32,
      112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T)
    (h2 : w2.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = true ∧ a.compare = false ∧
      a.scheduled = false ∧ a.modular = true ∧ a.module = false ∧
      a.verified = true ∧ a.trusted_path.val = [] ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) w1 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [w3.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have gm : argv.val[(1#usize : Std.Usize).val]? = some wm := by simp [hv]
  have g1 : argv.val[(2#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(3#usize : Std.Usize).val]? = some w2 := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_olean g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_word gm (by rw [hm]; simp) (ConRon.Args.parse_one_modular gm hm)
    (usize_add_lit (b := 2#usize) rfl)] at h
  rw [ConRon.Args.loop_search g1 h1 (usize_add_lit (b := 3#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g2 h2 (usize_add_lit (b := 4#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 4#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsp, ?_⟩
  simpa using hf

/-- `["--olean", "--modular", "--search-path=" ++ dirs, "--", root]`'s `argv`. -/
theorem argv_modular {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {dirs root : String}
    (h : ArgvOf argv ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) :
    ∃ w0 wm w1 w2 w3, argv.val = [w0, wm, w1, w2, w3] ∧
      w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] ∧
      wm.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 97#u32, 114#u32] ∧
      w1.val.map UScalar.val = ("--search-path=" ++ dirs).toList.map Char.toNat ∧
      w2.val = [45#u32, 45#u32] ∧ w3.val.map UScalar.val = root.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨wm, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, l⟩⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, hm, h1, h2, h3⟩ := h
  refine ⟨w0, wm, w1, w2, w3, rfl, vals_eq (h0.trans (by decide)), vals_eq (hm.trans (by decide)), h1, vals_eq (h2.trans (by decide)),
    h3⟩

end ConRon.MainTheorem
