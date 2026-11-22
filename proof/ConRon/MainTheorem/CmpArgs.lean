import ConRon.MainTheorem.Modular

/-!
# `ConRon.MainTheorem.CmpArgs` — the parses of the compared `.olean` runs' argument lists

**Task #171, slice 3b**: `ModArgs.lean`'s parses at the argument lists of con-leche's compared
`.olean` theorems, each with `--trusted-search-path=T --search-path=D`: the trusted directories
are `searchPathOf T` (`push_dirs_trusted`) as the search path's are `searchPathOf D`.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.MainTheorem.Stages
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean
open ConRon.Refine (absString)

namespace ConRon.Args

variable {a : driver.cli.Args} {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {i : Std.Usize}
  {s : alloc.vec.Vec Std.U32}

theorem parse_one_compare' (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32]) :
    driver.cli.parse_one a argv i = ok { a with compare := true } := by
  parse_one_word hs, hv

/-- **`--trusted-search-path=DIRS`**: the directories, after the ones before. -/
theorem parse_one_trusted {T : List Std.U32} (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T) :
    driver.cli.parse_one a argv i = (do
      let v ← driver.cli.push_dirs a.trusted_path s 22#usize
      ok { a with trusted_path := v }) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.parse_one, ConRon.Args.vec_index_ok'' hi, hx]
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, hv, w_verified_val, w_trusted_val, w_progress_val, w_olean_val, w_check_graph_val, w_module_val, w_modular_val, w_compare_val, w_jobs_val, w_progress_eq_val, w_jobs_eq_val, w_max_nat_size_eq_val, w_constant_eq_val, w_search_path_eq_val, w_trusted_search_path_eq_val, w_schedule_val, w_worker_stack_size_eq_val, driver.cli.parse_valued,
    ConRon.Args.cps_starts_with_eq, List.cons_append, List.cons_beq_cons, List.take_succ_cons,
    List.length_cons, List.length_nil]
  simp

/-- **`--trusted-search-path=DIRS` in the loop**: the directories pushed, then the loop goes on. -/
theorem loop_trusted {T : List Std.U32} (hs : argv.val[i.val]? = some s)
    (hv : s.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T) {i2 : Std.Usize}
    (hi2 : i + 1#usize = ok i2) :
    driver.cli.parse_args_loop argv a i = (do
      let v ← driver.cli.push_dirs a.trusted_path s 22#usize
      driver.cli.parse_args_loop argv { a with trusted_path := v } i2) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hs
  rw [driver.cli.parse_args_loop]
  have hlt : ¬ i >= alloc.vec.Vec.len argv := by scalar_tac
  rw [ite_eq_right hlt, ConRon.Args.vec_index_ok'' hi, hx]
  have hne : (s.val == [45#u32, 45#u32]) = false := by rw [hv]; simp
  simp only [bind_ok, lift, ConRon.Args.cps_beq_eq, w_end_val, hne, Bool.false_eq_true, ite_false,
    parse_one_trusted hs hv]
  cases driver.cli.push_dirs a.trusted_path s 22#usize <;> simp [hi2]

/-- **`--trusted-search-path=` + `dirs`, as the Rust reads it, is `searchPathOf dirs`**. -/
theorem push_dirs_trusted {dirs : String} {v : alloc.vec.Vec Std.U32}
    (hs : v.val.map UScalar.val = ("--trusted-search-path=" ++ dirs).toList.map Char.toNat)
    {r : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (h : driver.cli.push_dirs (alloc.vec.Vec.new _) v 22#usize = ok r) :
    r.val.map (fun d => (⟨absString d⟩ : System.FilePath)) = ConLeche.Driver.searchPathOf dirs := by
  rw [driver.cli.push_dirs] at h
  obtain ⟨⟨out1, cur⟩, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hlen : 22 ≤ v.val.length := by
    have := congrArg List.length hs
    simp only [List.length_map, String.toList_append, List.length_append] at this
    rw [this]
    exact Nat.le_add_right _ _
  have key := push_dirs_loop_val hs _ 22#usize _ _ rfl (by simpa using hlen) hl
  replace h : (if alloc.vec.Vec.len cur > 0#usize then alloc.vec.Vec.push out1 cur else ok out1) = ok r := h
  have hr : r.val = out1.val ++ (if cur.val = [] then [] else [cur]) := by
    by_cases h0 : cur.val = []
    · rw [ite_eq_right (fun h' => (len_pos cur).mp h' h0)] at h
      cases Result.ok_injective h; simp [h0]
    · rw [ite_eq_left ((len_pos cur).mpr h0)] at h
      rw [ConRon.Refine.vec_push_val h]; simp [h0]
  have hdrop : (("--trusted-search-path=" ++ dirs).toList).drop 22 = dirs.toList := by
    simp [String.toList_append]
  simp only [show (22#usize : Std.Usize).val = 22 from rfl, hdrop, absString_new,
    String.toList_empty, List.reverse_nil] at key
  simp only [ConLeche.Driver.searchPathOf]
  rw [hr, show (":" : String) = String.singleton ':' from rfl, splitOn_one]
  have : List.map (fun d => (⟨absString d⟩ : System.FilePath)) (out1.val ++ (if cur.val = [] then [] else [cur]))
      = ((out1.val ++ (if cur.val = [] then [] else [cur])).map absString).map System.FilePath.mk := by
    rw [List.map_map]; rfl
  rw [this, key, List.splitOn, List.splitOnPPrepend_nil_right]
  rfl

end ConRon.Args

namespace ConRon.MainTheorem

set_option autoImplicit false

/-- `--trusted-search-path=` ++ `dirs` as code points: the prefix, then the directories'. -/
theorem trusted_word {w : alloc.vec.Vec Std.U32} {dirs : String}
    (hw : w.val.map UScalar.val = ("--trusted-search-path=" ++ dirs).toList.map Char.toNat) :
    ∃ T : List Std.U32, w.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ T := by
  rw [String.toList_append, List.map_append] at hw
  obtain ⟨l1, l2, hl, h1, -⟩ := List.map_eq_append_iff.mp hw
  refine ⟨l2, ?_⟩
  have hp : "--trusted-search-path=".toList.map Char.toNat = ([45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] : List Std.U32).map
      UScalar.val := by decide
  rw [hl, vals_eq (h1.trans hp)]

/-- `["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`'s `argv`. -/
theorem argv_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (h : ArgvOf argv ["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) :
    ∃ w0 w1 wT wD wE f0 f1, argv.val = [w0, w1, wT, wD, wE, f0, f1] ∧
      w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] ∧
      w1.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32] ∧
      wT.val.map UScalar.val = ("--trusted-search-path=" ++ T).toList.map Char.toNat ∧
      wD.val.map UScalar.val = ("--search-path=" ++ D).toList.map Char.toNat ∧
      wE.val = [45#u32, 45#u32] ∧
      f0.val.map UScalar.val = c.toList.map Char.toNat ∧
      f1.val.map UScalar.val = s.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨w1, _ | ⟨wT, _ | ⟨wD, _ | ⟨wE, _ | ⟨f0, _ | ⟨f1, _ | ⟨wX, l⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨w0, w1, wT, wD, wE, f0, f1, rfl, vals_eq (h0.trans (by decide)), vals_eq (h1.trans (by decide)), h2, h3, vals_eq (h4.trans (by decide)), h5, h6⟩

/-- **The parse of `["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`**: `--olean`, `--compare`, the trusted directories and the search path the
directories, the files, every other default. -/
theorem parse_args_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 w1 wT wD wE f0 f1 : alloc.vec.Vec Std.U32} {TT DD : List Std.U32}
    (hv : argv.val = [w0, w1, wT, wD, wE, f0, f1])
    (h0 : w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32])
    (h1 : w1.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32])
    (hT : wT.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ TT)
    (hD : wD.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ DD)
    (hE : wE.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = true ∧ a.compare = true ∧
      a.scheduled = false ∧ a.modular = false ∧ a.module = false ∧
      a.verified = true ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wT 22#usize = ok a.trusted_path ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wD 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [f0.val, f1.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wE := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_olean g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_word g1 (by rw [h1]; simp) (ConRon.Args.parse_one_compare' g1 h1)
    (usize_add_lit (b := 2#usize) rfl)] at h
  rw [ConRon.Args.loop_trusted g2 hT (usize_add_lit (b := 3#usize) rfl)] at h
  obtain ⟨tp, htp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_search g3 hD (usize_add_lit (b := 4#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g4 hE (usize_add_lit (b := 5#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 5#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, htp, hsp, ?_⟩
  simpa using hf

/-- `["--check-graph", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`'s `argv`. -/
theorem argv_graph_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (h : ArgvOf argv ["--check-graph", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) :
    ∃ w0 w1 wT wD wE f0 f1, argv.val = [w0, w1, wT, wD, wE, f0, f1] ∧
      w0.val = [45#u32, 45#u32, 99#u32, 104#u32, 101#u32, 99#u32, 107#u32, 45#u32, 103#u32, 114#u32, 97#u32, 112#u32, 104#u32] ∧
      w1.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32] ∧
      wT.val.map UScalar.val = ("--trusted-search-path=" ++ T).toList.map Char.toNat ∧
      wD.val.map UScalar.val = ("--search-path=" ++ D).toList.map Char.toNat ∧
      wE.val = [45#u32, 45#u32] ∧
      f0.val.map UScalar.val = c.toList.map Char.toNat ∧
      f1.val.map UScalar.val = s.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨w1, _ | ⟨wT, _ | ⟨wD, _ | ⟨wE, _ | ⟨f0, _ | ⟨f1, _ | ⟨wX, l⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨w0, w1, wT, wD, wE, f0, f1, rfl, vals_eq (h0.trans (by decide)), vals_eq (h1.trans (by decide)), h2, h3, vals_eq (h4.trans (by decide)), h5, h6⟩

/-- **The parse of `["--check-graph", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`**: `--check-graph`, `--compare`, the trusted directories and the search path the
directories, the files, every other default. -/
theorem parse_args_graph_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 w1 wT wD wE f0 f1 : alloc.vec.Vec Std.U32} {TT DD : List Std.U32}
    (hv : argv.val = [w0, w1, wT, wD, wE, f0, f1])
    (h0 : w0.val = [45#u32, 45#u32, 99#u32, 104#u32, 101#u32, 99#u32, 107#u32, 45#u32, 103#u32, 114#u32, 97#u32, 112#u32, 104#u32])
    (h1 : w1.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32])
    (hT : wT.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ TT)
    (hD : wD.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ DD)
    (hE : wE.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = true ∧ a.olean = false ∧ a.compare = true ∧
      a.scheduled = false ∧ a.modular = false ∧ a.module = false ∧
      a.verified = true ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wT 22#usize = ok a.trusted_path ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wD 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [f0.val, f1.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wE := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_check_graph g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_word g1 (by rw [h1]; simp) (ConRon.Args.parse_one_compare' g1 h1)
    (usize_add_lit (b := 2#usize) rfl)] at h
  rw [ConRon.Args.loop_trusted g2 hT (usize_add_lit (b := 3#usize) rfl)] at h
  obtain ⟨tp, htp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_search g3 hD (usize_add_lit (b := 4#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g4 hE (usize_add_lit (b := 5#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 5#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, htp, hsp, ?_⟩
  simpa using hf

/-- `["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", root]`'s `argv`. -/
theorem argv_module_t {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D root : String}
    (h : ArgvOf argv ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", root]) :
    ∃ w0 w1 wT wD wE f0, argv.val = [w0, w1, wT, wD, wE, f0] ∧
      w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] ∧
      w1.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32] ∧
      wT.val.map UScalar.val = ("--trusted-search-path=" ++ T).toList.map Char.toNat ∧
      wD.val.map UScalar.val = ("--search-path=" ++ D).toList.map Char.toNat ∧
      wE.val = [45#u32, 45#u32] ∧
      f0.val.map UScalar.val = root.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨w1, _ | ⟨wT, _ | ⟨wD, _ | ⟨wE, _ | ⟨f0, _ | ⟨wX, l⟩⟩⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨w0, w1, wT, wD, wE, f0, rfl, vals_eq (h0.trans (by decide)), vals_eq (h1.trans (by decide)), h2, h3, vals_eq (h4.trans (by decide)), h5⟩

/-- **The parse of `["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", root]`**: `--olean`, `--module`, the trusted directories and the search path the
directories, the files, every other default. -/
theorem parse_args_module_t {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 w1 wT wD wE f0 : alloc.vec.Vec Std.U32} {TT DD : List Std.U32}
    (hv : argv.val = [w0, w1, wT, wD, wE, f0])
    (h0 : w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32])
    (h1 : w1.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32])
    (hT : wT.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ TT)
    (hD : wD.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ DD)
    (hE : wE.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = true ∧ a.compare = false ∧
      a.scheduled = false ∧ a.modular = false ∧ a.module = true ∧
      a.verified = true ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wT 22#usize = ok a.trusted_path ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wD 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [f0.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wE := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_olean g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_word g1 (by rw [h1]; simp) (ConRon.Args.parse_one_module g1 h1)
    (usize_add_lit (b := 2#usize) rfl)] at h
  rw [ConRon.Args.loop_trusted g2 hT (usize_add_lit (b := 3#usize) rfl)] at h
  obtain ⟨tp, htp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_search g3 hD (usize_add_lit (b := 4#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g4 hE (usize_add_lit (b := 5#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 5#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, htp, hsp, ?_⟩
  simpa using hf

/-- `["--olean", "--module", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`'s `argv`. -/
theorem argv_module_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (h : ArgvOf argv ["--olean", "--module", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) :
    ∃ w0 w1 w2 wT wD wE f0 f1, argv.val = [w0, w1, w2, wT, wD, wE, f0, f1] ∧
      w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] ∧
      w1.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32] ∧
      w2.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32] ∧
      wT.val.map UScalar.val = ("--trusted-search-path=" ++ T).toList.map Char.toNat ∧
      wD.val.map UScalar.val = ("--search-path=" ++ D).toList.map Char.toNat ∧
      wE.val = [45#u32, 45#u32] ∧
      f0.val.map UScalar.val = c.toList.map Char.toNat ∧
      f1.val.map UScalar.val = s.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨wT, _ | ⟨wD, _ | ⟨wE, _ | ⟨f0, _ | ⟨f1, _ | ⟨wX, l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨w0, w1, w2, wT, wD, wE, f0, f1, rfl, vals_eq (h0.trans (by decide)), vals_eq (h1.trans (by decide)), vals_eq (h2.trans (by decide)), h3, h4, vals_eq (h5.trans (by decide)), h6, h7⟩

/-- **The parse of `["--olean", "--module", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`**: `--olean`, `--module`, `--compare`, the trusted directories and the search path the
directories, the files, every other default. -/
theorem parse_args_module_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 w1 w2 wT wD wE f0 f1 : alloc.vec.Vec Std.U32} {TT DD : List Std.U32}
    (hv : argv.val = [w0, w1, w2, wT, wD, wE, f0, f1])
    (h0 : w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32])
    (h1 : w1.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 101#u32])
    (h2 : w2.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32])
    (hT : wT.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ TT)
    (hD : wD.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ DD)
    (hE : wE.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = true ∧ a.compare = true ∧
      a.scheduled = false ∧ a.modular = false ∧ a.module = true ∧
      a.verified = true ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wT 22#usize = ok a.trusted_path ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wD 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [f0.val, f1.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some w2 := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g5 : argv.val[(5#usize : Std.Usize).val]? = some wE := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_olean g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_word g1 (by rw [h1]; simp) (ConRon.Args.parse_one_module g1 h1)
    (usize_add_lit (b := 2#usize) rfl)] at h
  rw [ConRon.Args.loop_word g2 (by rw [h2]; simp) (ConRon.Args.parse_one_compare' g2 h2)
    (usize_add_lit (b := 3#usize) rfl)] at h
  rw [ConRon.Args.loop_trusted g3 hT (usize_add_lit (b := 4#usize) rfl)] at h
  obtain ⟨tp, htp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_search g4 hD (usize_add_lit (b := 5#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g5 hE (usize_add_lit (b := 6#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 6#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, htp, hsp, ?_⟩
  simpa using hf

/-- `["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`'s `argv`. -/
theorem argv_modular_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {T D c s : String}
    (h : ArgvOf argv ["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) :
    ∃ w0 w1 w2 wT wD wE f0 f1, argv.val = [w0, w1, w2, wT, wD, wE, f0, f1] ∧
      w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32] ∧
      w1.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 97#u32, 114#u32] ∧
      w2.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32] ∧
      wT.val.map UScalar.val = ("--trusted-search-path=" ++ T).toList.map Char.toNat ∧
      wD.val.map UScalar.val = ("--search-path=" ++ D).toList.map Char.toNat ∧
      wE.val = [45#u32, 45#u32] ∧
      f0.val.map UScalar.val = c.toList.map Char.toNat ∧
      f1.val.map UScalar.val = s.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨wT, _ | ⟨wD, _ | ⟨wE, _ | ⟨f0, _ | ⟨f1, _ | ⟨wX, l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    rw [hv] at h <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, List.nil_eq,
      reduceCtorEq, and_false, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨w0, w1, w2, wT, wD, wE, f0, f1, rfl, vals_eq (h0.trans (by decide)), vals_eq (h1.trans (by decide)), vals_eq (h2.trans (by decide)), h3, h4, vals_eq (h5.trans (by decide)), h6, h7⟩

/-- **The parse of `["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]`**: `--olean`, `--modular`, `--compare`, the trusted directories and the search path the
directories, the files, every other default. -/
theorem parse_args_modular_cmp {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {w0 w1 w2 wT wD wE f0 f1 : alloc.vec.Vec Std.U32} {TT DD : List Std.U32}
    (hv : argv.val = [w0, w1, w2, wT, wD, wE, f0, f1])
    (h0 : w0.val = [45#u32, 45#u32, 111#u32, 108#u32, 101#u32, 97#u32, 110#u32])
    (h1 : w1.val = [45#u32, 45#u32, 109#u32, 111#u32, 100#u32, 117#u32, 108#u32, 97#u32, 114#u32])
    (h2 : w2.val = [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32])
    (hT : wT.val = [45#u32, 45#u32, 116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 101#u32, 100#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ TT)
    (hD : wD.val = [45#u32, 45#u32, 115#u32, 101#u32, 97#u32, 114#u32, 99#u32, 104#u32, 45#u32, 112#u32, 97#u32, 116#u32, 104#u32, 61#u32] ++ DD)
    (hE : wE.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = true ∧ a.compare = true ∧
      a.scheduled = false ∧ a.modular = true ∧ a.module = false ∧
      a.verified = true ∧ a.constants.val = [] ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wT 22#usize = ok a.trusted_path ∧
      driver.cli.push_dirs (alloc.vec.Vec.new _) wD 14#usize = ok a.search_path ∧
      a.files.val.map (·.val) = [f0.val, f1.val] := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  cases Result.ok_injective ha0
  have g0 : argv.val[(0#usize : Std.Usize).val]? = some w0 := by simp [hv]
  have g1 : argv.val[(1#usize : Std.Usize).val]? = some w1 := by simp [hv]
  have g2 : argv.val[(2#usize : Std.Usize).val]? = some w2 := by simp [hv]
  have g3 : argv.val[(3#usize : Std.Usize).val]? = some wT := by simp [hv]
  have g4 : argv.val[(4#usize : Std.Usize).val]? = some wD := by simp [hv]
  have g5 : argv.val[(5#usize : Std.Usize).val]? = some wE := by simp [hv]
  rw [ConRon.Args.loop_word g0 (by rw [h0]; simp) (ConRon.Args.parse_one_olean g0 h0)
    (usize_add_lit (b := 1#usize) rfl)] at h
  rw [ConRon.Args.loop_word g1 (by rw [h1]; simp) (ConRon.Args.parse_one_modular g1 h1)
    (usize_add_lit (b := 2#usize) rfl)] at h
  rw [ConRon.Args.loop_word g2 (by rw [h2]; simp) (ConRon.Args.parse_one_compare' g2 h2)
    (usize_add_lit (b := 3#usize) rfl)] at h
  rw [ConRon.Args.loop_trusted g3 hT (usize_add_lit (b := 4#usize) rfl)] at h
  obtain ⟨tp, htp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_search g4 hD (usize_add_lit (b := 5#usize) rfl)] at h
  obtain ⟨sp, hsp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [ConRon.Args.loop_end g5 hE (usize_add_lit (b := 6#usize) rfl)] at h
  obtain ⟨fl, hfl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases Result.ok_injective h
  have hf := push_files_loop_val argv _ _ 6#usize rfl hfl
  simp only [hv] at hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, htp, hsp, ?_⟩
  simpa using hf

end ConRon.MainTheorem
