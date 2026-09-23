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

/-- `ifenv_dup` in `LSP` form: the copy stands for the same twin environment. -/
@[lockstep] theorem ifenv_dup_spec {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) :
    LSP (arena.env.ifenv_dup rf) (fun a => IFEnvRelI a lf) :=
  fun _ h => ifenv_dup_rel hfe h

end IndModeledPrims

/-- `lockstep`, then a twin `if` left under a `>>= pure` is decided by the last
Rust test (`hc`) and `lockstep` runs again.  The core tactic's
`LS.twin_bind_pure` fallback fires when the Rust's next bind finds no partner
while the twin is an undecided `if`, and it wraps the `if` in `>>= pure`, where
the twin-`if` rule no longer sees it. -/
macro "lockstep_ite" : tactic => `(tactic| (lockstep; all_goals (try (
  rw [bind_pure]; (first | rw [if_pos ‹_›] | rw [if_neg ‹_›]); lockstep))))

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.IndModeledPrims.proj_model_name_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IndModeledPrims.proj_model_name_ls

/-- info: 'ConRon.Refine2.IndModeledPrims.proj_fn_name_lss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IndModeledPrims.proj_fn_name_lss

end ConRon.Refine2
