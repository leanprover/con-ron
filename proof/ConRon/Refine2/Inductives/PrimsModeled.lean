/-
# `ConRon.Refine2.Inductives.PrimsModeled` — the modeled route's `@[lockstep]` primitives

Task #97-T2-LOCKSTEP lane Inductives Modeled.  The `@[lockstep]` pairs the
modeled route (`Refine2/Inductives/Modeled.lean`) needs and no other tier
provides, kept apart from `Inductives/Prims.lean` (the other Inductives lane's)
so the two lanes never edit one file.

* **The generated name parts.**  `iota_thm_name` and `core::proj_model_name`
  build `"iota_" ++ toString j` / `"proj_" ++ toString i` as a constant's code
  points followed by the port's own decimal recursion
  (`kernel::core_k::nat_to_dec`, `Refine/CoreKNames.lean`'s
  `nat_to_dec_refines`) and `code_points_from` from `0`.  The two Rust-only
  steps get `LSP` specs; the intern is `intern_n_node_cat_ls`, applied by hand
  after `lockstep` (the concatenation is not a side goal the tiers solve).
* **`arena::env::proj_fn_name`** ⊑ `projFnName`: two name interns at the
  STORE level, the shape of `Promote/Intern.lean`'s `proj_table_name_lss`.
* **`arena::core::proj_model_name`** ⊑ `projModelName`.
-/
import ConRon.Refine2.Inductives.SpecModeled
import ConRon.Refine.Env
import ConRon.Refine2.Frontend.ExportC
import ConRon.Refine2.Checker.Canon

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

namespace IndModeledPrims

open Lockstep

/-- `kernel::core_k::nat_to_dec` is `toString` on the index, in valid code
points. -/
@[lockstep] theorem nat_to_dec_spec (i : Std.U64) :
    LSP (kernel.core_k.nat_to_dec i)
      (fun r => ConRon.Refine.absString r = toString i.val ∧ ConRon.Refine.StrWF r) :=
  fun _ h => ConRon.Refine.CoreK.nat_to_dec_refines h

/-- `code_points_from s 0 out` appends the whole slice. -/
@[lockstep] theorem code_points_from_spec (s : Slice Std.U32) (out : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.code_points_from s 0#usize out)
      (fun v => v.val = out.val ++ s.val) := by
  intro v h
  have := ConRon.Refine.Env.code_points_from_val s _ 0#usize out v le_rfl h
  simpa using this

/-- A name part `lit ++ toString n`, built as the constant `X`'s code points
followed by the decimal digits `d`, interned: the twin's
`.str m (lit ++ toString n)`. -/
theorem intern_n_node_cat_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m : arena.handle.NIdx) {k : Std.Usize}
    (X : Array Std.U32 k) (p : String)
    (hp : String.ofList (X.val.map fun c => Char.ofNat c.val) = p)
    (hpwf : ∀ c ∈ X.val, Nat.isValidChar c.val)
    {x d a : alloc.vec.Vec Std.U32} {n : Nat}
    (ha : a.val = x.val ++ (alloc.vec.Vec.deref d).val)
    (hd : ConRon.Refine.absString d = toString n ∧ ConRon.Refine.StrWF d)
    (hx : x.val = X.val) :
    LS pers (fun a b => b = absNIdx a)
      (arena.monad.intern_n_node pers st (arena.store.NNodeView.Str m a)) lst
      (internNNode (.str (absNIdx m) (p ++ toString n))) := by
  have hdv : (alloc.vec.Vec.deref d).val = d.val := Slice.from_val _ _
  rw [hdv, hx] at ha
  have hs : ConRon.Refine.absString a = p ++ toString n := by
    rw [← hp, ← hd.1, ConRon.Refine.absString, ConRon.Refine.absString, ha,
      List.map_append, String.ofList_append]
  have hwf : ConRon.Refine.StrWF a := by
    intro c hc
    rw [ha] at hc
    rcases List.mem_append.mp hc with h | h
    · exact hpwf c h
    · exact hd.2 c h
  have h := intern_n_node_ls hrel hinv (.Str m a) hwf
  simpa [absNNodeView, hs] using h

/-- `arena::core::proj_model_name` ⊑ `projModelName` —
`(T.str "_model").str ("proj_" ++ toString i)`, interned. -/
@[lockstep] theorem proj_model_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t : arena.handle.NIdx) (i : Std.U64) :
    LS pers (fun a b => b = absNIdx a) (arena.core.proj_model_name pers st t i) lst
      (projModelName (absNIdx t) (absU i)) := by
  rw [arena.core.proj_model_name, projModelName]
  lockstep
  refine intern_n_node_cat_ls ‹_› ‹_› _ arena.core.proj_model_name.PROJ_ _
    ?_ ?_ (by assumption) ?_ ?_ <;>
    first | assumption | (simp only [global_simps]; decide) | simp_all

/-- The `"proj"` component of a projection function's name. -/
theorem proj_fn_s_abs {v : alloc.vec.Vec Std.U32}
    (h : kernel.core_types.code_points (Array.to_slice arena.env.proj_fn_name.S) = ok v) :
    ConRon.Refine.absString v = "proj" ∧ ConRon.Refine.StrWF v := by
  have hv : v.val = [112#u32, 114#u32, 111#u32, 106#u32] := by
    rw [ConRon.Refine.Env.code_points_val h, Array.val_to_slice, arena.env.proj_fn_name.S,
      Array.make_val]
  refine ⟨?_, ?_⟩
  · rw [ConRon.Refine.absString, hv]; rfl
  · intro c hc; rw [hv] at hc; fin_cases hc <;> decide

/-- `arena::env::proj_fn_name` ⊑ `projFnName` — two name interns at the store
level (`proj_table_name_lss`'s shape, with the field index for `0`). -/
@[lockstep] theorem proj_fn_name_lss {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (sn : arena.handle.NIdx) (i : Std.U64) :
    LSS pers (fun a b => b = absNIdx a) (arena.env.proj_fn_name pers st.store sn i) st lst
      (projFnName (absNIdx sn) (absU i)) := by
  intro o s' hrun
  rw [arena.env.proj_fn_name] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [dupId_nidx _ _ hn] at hrun
  obtain ⟨sl, hsl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [lift, Result.ok.injEq] at hsl
  subst hsl
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨habs, hswf⟩ := proj_fn_s_abs hv
  obtain ⟨⟨r1, ar1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hok1, herr1, -⟩ :=
    estore_intern_name_abs (ls := lst.store) hrel.store hinv.store
      (v := arena.store.NNodeView.Str sn v) hswf h1
  have hrun1 : (projFnName (absNIdx sn) (absU i)).run lst
      = ((internNNode (.str (absNIdx sn) "proj")) >>= fun s =>
          internNNode (.num s (absU i))).run lst := rfl
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    simp only [Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    exact AErrSim.of_none (herr1 e rfl)
  | Ok s1 =>
    obtain ⟨hs1, hrelS, hinvS, hcap1⟩ := hok1 s1 rfl
    simp only [absNNodeView, habs] at hs1 hrelS hcap1
    obtain ⟨hok2, herr2, -⟩ :=
      estore_intern_name_abs (ls := (lst.store.internName (.str (absNIdx sn) "proj")).1)
        hrelS hinvS (v := arena.store.NNodeView.Num s1 i) trivial hrun
    rw [hrun1, run_bind_ok (internNNode_run_of_cap hcap1)]
    cases o with
    | Err e => exact AErrSim.of_none (herr2 e rfl)
    | Ok a =>
      obtain ⟨hs2, hrelS2, hinvS2, hcap2⟩ := hok2 a rfl
      simp only [absNNodeView, hs1] at hs2 hrelS2 hcap2
      exact ⟨_, _, internNNode_run_of_cap hcap2, hs2.symm,
        ⟨hrelS2, hrel.memos, hrel.caches, hrel.pins⟩, ⟨hinvS2, hinv.memos, hinv.caches⟩⟩

/-- A twin test on a found constant's presence (`(fe.find? n).isSome`, the
Rust's `ifenv_find(..).is_some()`): after `ifenv_find_twin` rewrites the twin's
lookup to the abstraction of the Rust answer, the twin tests
`(o.map absIConstantInfo).isSome`, which is the Rust's own test. -/
@[lockstep_simp] theorem isSome_map_is_some {α β : Type} (f : α → β) (a : Option α) :
    (a.map f).isSome = core.option.Option.is_some a := by
  cases a <;> rfl

/-- The same for the twin's `(fe.find? n).isNone`. -/
@[lockstep_simp] theorem isNone_map_is_none {α β : Type} (f : α → β) (a : Option α) :
    (a.map f).isNone = core.option.Option.is_none a := by
  cases a <;> rfl

/-- The twin's `recs.isEmpty` is the port's `recs.len() == 0`. -/
@[lockstep_simp] theorem absICIL_isEmpty (v : alloc.vec.Vec arena.env.IConstantInfo) :
    ((absICIL v).isEmpty = true) = (alloc.vec.Vec.len v = 0#usize) := by
  apply propext
  simp only [absICIL, List.isEmpty_iff, List.map_eq_nil_iff]
  constructor
  · intro h; have : v.val.length = 0 := by simp [h]
    scalar_tac
  · intro h; have : v.val.length = 0 := by scalar_tac
    exact List.eq_nil_of_length_eq_zero this

/-- `arena::env::ifenv_dup` is the identity under `IFEnvRelI`: the constants
are copied record by record (`i_constant_infos_dup_abs`), the index table is
the table (`HashMap2.dup_spec`), the counter is the counter. -/
theorem ifenv_dup_rel {rf a : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (h : arena.env.ifenv_dup rf = ok a) : IFEnvRelI a lf := by
  rw [arena.env.ifenv_dup, arena.env.i_env_dup] at h
  obtain ⟨ie, hie, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, hie⟩ := ConRon.Refine.bind_eq_ok_iff.mp hie
  obtain rfl := (Result.ok_injective hie).symm
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := (Result.ok_injective h).symm
  have hvv := i_constant_infos_dup_abs hv
  have hpair : ConRon.Refine.HashMap.DupId (Pair.Insts.Con_ron_coreRonHashmapDup
      U64.Insts.Con_ron_coreRonHashmapDup U64.Insts.Con_ron_coreRonHashmapDup) := by
    intro a b h
    obtain ⟨x, y⟩ := a
    have h' : (do let t ← U64.Insts.Con_ron_coreRonHashmapDup.dup2 x
                  let t1 ← U64.Insts.Con_ron_coreRonHashmapDup.dup2 y
                  ok (t, t1)) = ok b := h
    simp only [ConRon.Refine.bind_eq_ok_iff, Result.ok.injEq] at h'
    obtain ⟨u, hu, w, hw, hb⟩ := h'
    rw [(Result.ok_injective (α := Std.U64) hu).symm,
      (Result.ok_injective (α := Std.U64) hw).symm] at hb
    exact hb.symm
  have hm' : hm = rf.idx :=
    ConRon.Refine.HashMap2.dup_spec dupId_nidx hpair hhm
  subst hm'
  have hlen : v.val.length = rf.env.consts.val.length := by
    simpa using congrArg List.length hvv
  obtain ⟨⟨henv, hidx, hvis⟩, ⟨hinv1, hinv2, hinv3⟩⟩ := hfe
  refine ⟨⟨?_, ?_, hvis⟩, ⟨hinv1, ?_, ?_⟩⟩
  · rw [henv]; simp only [absIEnv, hvv]
  · intro n
    rw [← hidx n]
    congr 1
    funext p
    have hk : v.val[p.2.val]?.map absIConstantInfo
        = rf.env.consts.val[p.2.val]?.map absIConstantInfo := by
      rw [← List.getElem?_map, hvv, List.getElem?_map]
    have := congrArg (Option.map fun c => (absU p.1, c)) hk
    simpa [Option.map_map, Function.comp_def] using this
  · simp only [hlen]; exact hinv2
  · intro n p hp; rw [hlen]; exact hinv3 n p hp

/-- `arena::env::i_constant_info_to_constant_val` ⊑ `IConstantInfo.toConstantVal`
at the store level — `Frontend/ExportC.lean`'s `Sim₀` statement, in `LSS` form. -/
@[lockstep] theorem i_constant_info_to_constant_val_lss {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (c : arena.env.IConstantInfo) :
    LSS pers (fun a b => b = absIConstantVal a)
      (arena.env.i_constant_info_to_constant_val pers st.store c) st lst
      (absIConstantInfo c).toConstantVal := by
  intro o s' h
  have hs := Frontend.i_constant_info_to_constant_val_refines hrel hinv h
  cases o with
  | Err e => exact hs
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := hs
    exact ⟨_, lst', hx, rfl, h1, h2⟩

/-- `arena::canon::i_constant_info_beq` is the twin's `==` on the abstraction
(`Checker/Canon.lean`'s `i_constant_info_beq_refines`). -/
@[lockstep] theorem i_constant_info_beq_spec (a b : arena.env.IConstantInfo) :
    LSP (arena.canon.i_constant_info_beq a b)
      (fun o => o = (absIConstantInfo a == absIConstantInfo b)) :=
  fun _ h => i_constant_info_beq_refines h

/-- `arena::core::nidx_vec_beq` is `==` on the abstracted name lists
(`Inductives/Shape.lean`'s `nidx_vec_beq_abs`). -/
@[lockstep] theorem nidx_vec_beq_spec (a b : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.core.nidx_vec_beq a b) (fun o => o = (absNIdxL a == absNIdxL b)) :=
  fun _ h => nidx_vec_beq_abs h

/-- `arena::env::i_rec_rules_dup` is the identity on the abstraction. -/
@[lockstep] theorem i_rec_rules_dup_spec (rs : alloc.vec.Vec arena.env.IRecRule) :
    LSP (arena.env.i_rec_rules_dup rs)
      (fun r => r.val.map absIRecRule = rs.val.map absIRecRule) :=
  fun _ h => i_rec_rules_dup_abs h

/-- A lockstep goal whose twin is propositionally another program. -/
theorem LS_of_twin_eq {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x y : AM β} (h : LS pers R m lst x) (hx : x = y) :
    LS pers R m lst y := hx ▸ h

/-! ### The member-name guard (`check_member_val`)

`level::name_is_model_suffix` on the name `read_name_m` answered.  The three
lemmas are `RefineOld/IndModeled.lean`'s (task #97-P5-Ind round 1), restated
here so the tier does not import the old refinement. -/

/-- `"_model"`'s code points as a `Vec<u32>`. -/
theorem modelStr_witness :
    ∃ v : alloc.vec.Vec Std.U32,
      v.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32]
        ∧ ConRon.Refine.StrWF v ∧ ConRon.Refine.absString v = "_model" := by
  refine ⟨alloc.vec.Vec.from [95#u32, 109#u32, 111#u32, 100#u32, 101#u32,
    108#u32] (by simp only [List.length_cons, List.length_nil]; scalar_tac),
    ?_, ?_, ?_⟩
  · exact alloc.vec.Vec.from_val _ _
  · intro c hc
    rw [alloc.vec.Vec.from_val] at hc
    fin_cases hc <;> decide
  · rw [ConRon.Refine.absString, alloc.vec.Vec.from_val]; rfl

/-- `level::is_model_str` decides `absString s = "_model"`. -/
theorem is_model_str_refines {s : alloc.vec.Vec Std.U32} (hs : ConRon.Refine.StrWF s)
    {b : Bool} (h : kernel.level.is_model_str s = ok b) :
    b = decide (ConRon.Refine.absString s = "_model") := by
  obtain ⟨w, hwv, hwwf, hwabs⟩ := modelStr_witness
  have hiff : ConRon.Refine.absString s = "_model" ↔ s.val = w.val := by
    constructor
    · intro hstr
      rw [ConRon.Refine.Name.absString_inj hs hwwf (by rw [hstr, hwabs])]
    · intro hval
      rw [ConRon.Refine.absString, hval, ← ConRon.Refine.absString, hwabs]
  have hgoal : decide (ConRon.Refine.absString s = "_model") = decide (s.val = w.val) := by
    rw [Bool.eq_iff_iff]
    simpa using hiff
  rw [hgoal, hwv]
  have hgi : ∀ (i : Std.Usize) (x : Std.U32), i.val < s.val.length →
      s.val[i.val]? = some x →
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) s i
        = ok x := by
    intro i x hi hx
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec s i hi)
    subst hyv
    rw [alloc.vec.Vec.index_slice_index, hy]
    rw [List.getElem?_eq_getElem hi] at hx
    congr 1
    exact Option.some_inj.mp hx
  rw [kernel.level.is_model_str] at h
  by_cases hlen : s.val.length = 6
  · rw [if_pos (show alloc.vec.Vec.len s = 6#usize by
      have := alloc.vec.Vec.len_val s; scalar_tac)] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, hval⟩ :
        ∃ a0 a1 a2 a3 a4 a5 : Std.U32, s.val = [a0, a1, a2, a3, a4, a5] := by
      rcases hl : s.val with _ | ⟨a0, l1⟩
      · rw [hl] at hlen; simp at hlen
      rcases l1 with _ | ⟨a1, l2⟩
      · rw [hl] at hlen; simp at hlen
      rcases l2 with _ | ⟨a2, l3⟩
      · rw [hl] at hlen; simp at hlen
      rcases l3 with _ | ⟨a3, l4⟩
      · rw [hl] at hlen; simp at hlen
      rcases l4 with _ | ⟨a4, l5⟩
      · rw [hl] at hlen; simp at hlen
      rcases l5 with _ | ⟨a5, l6⟩
      · rw [hl] at hlen; simp at hlen
      rcases l6 with _ | ⟨a6, l7⟩
      · exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
      · rw [hl] at hlen; simp at hlen
    rw [hval]
    rw [hgi 0#usize a0 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc0 : a0 = 95#u32
    case neg => rw [if_neg hc0, Result.ok.injEq] at h; simp [← h, hc0]
    rw [if_pos hc0] at h
    rw [hgi 1#usize a1 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc1 : a1 = 109#u32
    case neg => rw [if_neg hc1, Result.ok.injEq] at h; simp [← h, hc1]
    rw [if_pos hc1] at h
    rw [hgi 2#usize a2 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc2 : a2 = 111#u32
    case neg => rw [if_neg hc2, Result.ok.injEq] at h; simp [← h, hc2]
    rw [if_pos hc2] at h
    rw [hgi 3#usize a3 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc3 : a3 = 100#u32
    case neg => rw [if_neg hc3, Result.ok.injEq] at h; simp [← h, hc3]
    rw [if_pos hc3] at h
    rw [hgi 4#usize a4 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok] at h
    by_cases hc4 : a4 = 101#u32
    case neg => rw [if_neg hc4, Result.ok.injEq] at h; simp [← h, hc4]
    rw [if_pos hc4] at h
    rw [hgi 5#usize a5 (by rw [hlen]; scalar_tac) (by rw [hval]; rfl),
      bind_tc_ok, Result.ok.injEq] at h
    rw [← h, hc0, hc1, hc2, hc3, hc4]
    simp
  · rw [if_neg (show ¬ alloc.vec.Vec.len s = 6#usize by
      have := alloc.vec.Vec.len_val s
      intro hc; apply hlen; scalar_tac), Result.ok.injEq] at h
    rw [← h]
    have hne : s.val ≠ [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
      intro hc; apply hlen; rw [hc]; rfl
    simp [hne]

/-- `Name.isModelSuffix` at a `.str` node. -/
theorem isModelSuffix_str (p : ConLeche.Name) (x : String) :
    ConLeche.Name.isModelSuffix (.str p x) = decide (x = "_model") := by
  by_cases hx : x = "_model"
  · subst hx; rfl
  · simp only [ConLeche.Name.isModelSuffix, hx, decide_false]
    split <;> simp_all

/-- `level::name_is_model_suffix` refines `Name.isModelSuffix`. -/
theorem name_is_model_suffix_refines {n : kernel.name.Name} (hn : ConRon.Refine.NameWF n)
    {b : Bool} (h : kernel.level.name_is_model_suffix n = ok b) :
    b = (ConRon.Refine.absName n).isModelSuffix := by
  cases hn with
  | @anonymous n' hmk =>
    rw [ConRon.Refine.name_anonymous_inv hmk] at h ⊢
    rw [kernel.level.name_is_model_suffix] at h
    simp at h
    subst h
    rfl
  | @str pre str n' hpre hstr hmk =>
    obtain ⟨hh, rfl⟩ := ConRon.Refine.mk_str_inv hmk
    rw [kernel.level.name_is_model_suffix] at h
    simp only [ConRon.Refine.arc_deref_eq, bind_tc_ok] at h
    rw [is_model_str_refines hstr h, ConRon.Refine.absName_mk, ConRon.Refine.absNameKind,
      isModelSuffix_str]
  | @num pre m n' hpre hmk =>
    obtain ⟨hh, rfl⟩ := ConRon.Refine.mk_num_inv hmk
    rw [kernel.level.name_is_model_suffix] at h
    simp at h
    subst h
    rfl

/-- `level::name_is_model_suffix` in `LSP` form, at a well-formed name. -/
@[lockstep] theorem name_is_model_suffix_spec {n : kernel.name.Name}
    (hn : ConRon.Refine.NameWF n) :
    LSP (kernel.level.name_is_model_suffix n)
      (fun b => TwinEq ((ConRon.Refine.absName n).isModelSuffix) b) :=
  fun _ h => (name_is_model_suffix_refines hn h).symm

/-- `arena::monad::read_name_m` ⊑ `readNameM` (`Refine2/Specs.lean`'s
`read_name_m_run₀`), with the answer's well-formedness (`read_name_m_wf`) —
the name guard reads it. -/
@[lockstep] theorem read_name_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.NIdx) :
    LS pers (fun a b => ConRon.Refine.NameWF a ∧ b = ConRon.Refine.absName a)
      (arena.monad.read_name_m pers st h) lst (Arena.readNameM (absNIdx h)) := by
  intro o st' hm
  have hs := read_name_m_run₀ hrel hinv hm
  have hwf := (read_name_m_wf hinv hm).1
  cases o with
  | Err e => exact hs
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := hs
    exact ⟨_, lst', hx, ⟨hwf a rfl, rfl⟩, h1, h2⟩

/-! ### The fields of an abstracted recursor rule

The twin reads `r.ctor`, `r.nfields`, … of `absIRecRule r`; these are the
port's fields, abstracted.  Not `lockstep_simp` here (a global registration
would reach the other lanes' files through `Inductives/Top.lean`): the modeled
route registers them locally. -/

theorem absIRecRule_ctor (r : arena.env.IRecRule) : (absIRecRule r).ctor = absNIdx r.ctor := rfl
theorem absIRecRule_nfields (r : arena.env.IRecRule) :
    (absIRecRule r).nfields = absU r.nfields := rfl
theorem absIRecRule_ctorParams (r : arena.env.IRecRule) :
    (absIRecRule r).ctorParams = absU r.ctor_params := rfl
theorem absIRecRule_fire (r : arena.env.IRecRule) :
    (absIRecRule r).fire = absIRecRuleFire r.fire := rfl
theorem absIRecRule_rhs (r : arena.env.IRecRule) : (absIRecRule r).rhs = absEIdx r.rhs := rfl
theorem absIRecRule_k (r : arena.env.IRecRule) : (absIRecRule r).k = r.k := rfl
theorem absIRecRule_eta (r : arena.env.IRecRule) : (absIRecRule r).eta = r.eta := rfl
theorem absIRecRule_paramsBlind (r : arena.env.IRecRule) :
    (absIRecRule r).paramsBlind = r.params_blind := rfl

/-- The handle comparison at an `EIdx`, the twin's `==` (the `NIdx` one is
`Checker/Base.lean`'s `nidx_eq2_spec`). -/
@[lockstep] theorem eidx_eq2_spec (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun o => o = (absEIdx a == absEIdx b)) :=
  fun _ h => eidx_eq2_abs h

/-- `ifenv_dup` in `LSP` form: the copy stands for the same twin environment. -/
@[lockstep] theorem ifenv_dup_spec {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) :
    LSP (arena.env.ifenv_dup rf) (fun a => IFEnvRelI a lf) :=
  fun _ h => ifenv_dup_rel hfe h

end IndModeledPrims

open Lean Elab Tactic in
/-- Fails unless the goal mentions the port's `Option` tests. -/
elab "ind_opt_guard" : tactic => do
  let t ← getMainTarget
  unless t.containsConst (fun n => n == ``core.option.Option.is_some ||
      n == ``core.option.Option.is_none) do
    throwError "ind_opt_guard: no Option test"

/-- A twin test `is_none o` decided by the port's `is_some o` (or the reverse). -/
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (ind_opt_guard
               simp only [core.option.Option.is_some, core.option.Option.is_none] at *
               simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]; done))

/-- `lockstep`, then a twin `if` left under a `>>= pure` is decided by the last
Rust test (`hc`) and `lockstep` runs again.  The core tactic's
`LS.twin_bind_pure` fallback fires when the Rust's next bind finds no partner
while the twin is an undecided `if`, and it wraps the `if` in `>>= pure`, where
the twin-`if` rule no longer sees it. -/
syntax "lockstep_ite" : tactic
macro_rules | `(tactic| lockstep_ite) => `(tactic| (lockstep; all_goals (try (
  rw [bind_pure]
  (first
    | refine Lockstep.LS.twin_ite_pos ‹_› ?_
    | refine Lockstep.LS.twin_ite_neg ‹_› ?_
    | refine Lockstep.LS.twin_ite_pos (by lockstep_side_ite) ?_
    | refine Lockstep.LS.twin_ite_neg (by lockstep_side_ite) ?_)
  lockstep_ite))))

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.IndModeledPrims.proj_model_name_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IndModeledPrims.proj_model_name_ls

/-- info: 'ConRon.Refine2.IndModeledPrims.proj_fn_name_lss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IndModeledPrims.proj_fn_name_lss

/-- `lockstep_ite`, then a leaf the zip stopped at because the twin still
matches on a value the port's own match lumped into a wildcard arm (`_ =>
false` against the twin's `| some (.thmInfo …), … | _, _ => pure false`): the
twin's `match` is split, contradicted arms dropped, and the zip resumes. -/
syntax "lockstep_mod" : tactic
macro_rules | `(tactic| lockstep_mod) => `(tactic| (lockstep_ite; all_goals (try (
  split <;> (try simp_all) <;> lockstep_mod))))

end ConRon.Refine2
