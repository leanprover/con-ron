/-
`FEnv.findProj?`, derived (task #49, `CORE_PLAN.md` step 4).

`CoreKBase.lean`'s `FEnvRel` is *find*-agreement only, so the projection-table
read the `core_k.rs` shape guards and the projection inference clauses do —
`fenv::find_proj` — has to be derived from it rather than assumed.  That needs
two `env.rs` refinements, `proj_table_name` (in `CoreKBase.lean`) and
`proj_table_entry` (here), and then the three `fenv.rs` index walks that sit on
top of `find_proj`/`find`.

**TO BE UNIFIED WITH TASK #46**: `env::proj_table_entry` belongs in
`Refine/Env.lean` and `fenv::find_proj`/`tower_slots_all_f`/`rec_slots_all_f`
in `Refine/FEnv.lean`.  They are here because step 4 cannot be stated without
them and steps 1 and 2 are being landed in parallel.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.FEnv

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

open ConRon.Refine.T22

/-- `Array.getD` on a `List.toArray` is `List.getD`: the one bridge between
con-leche's `ProjTable.bodies : Array Expr` and the port's `Vec<Expr>` (task
#10, surprise 8 — the Lean's `bodies` is an `Array` while its `guards` is a
`List`). -/
theorem toArray_getD {α : Type} (l : List α) (i : Nat) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  simp [Array.getD, List.getD]
  split
  · rename_i h; rw [List.getElem?_eq_getElem (by simpa using h)]; rfl
  · rename_i h; rw [List.getElem?_eq_none (by simpa using h)]; rfl

/-- `ConLeche/Kernel/Env.lean:466-468` — `env::proj_table_entry` refines
`ProjTable.entry`.  The two `getD`s are the out-of-range guards: Lean's
`default : Expr` is `.bvar 0` (`env::default_expr`) and `guards.getD i .zero`
falls back to `Level.zero`. -/
theorem proj_table_entry_refines {tbl : env.ProjTable} {i : Std.U64} {pe : env.ProjEntry}
    (htbl : ProjTableWF tbl) (h : env.proj_table_entry tbl i = ok pe) :
    absProjEntry pe = (absProjTable tbl).entry i.val ∧ ProjEntryWF pe := by
  obtain ⟨hsn, hlp, hct, hss, hbd, hgd⟩ := htbl
  rw [env.proj_table_entry] at h
  simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, name_dup_eq, level_dup_eq,
    expr_dup_eq, exists_eq_left'] at h
  obtain ⟨body, hbody, fs, hfs, lps, hlps, rfl⟩ := h
  -- the `bodies.getD i default` guard
  have hblen : (Std.UScalar.cast .U64 (alloc.vec.Vec.len tbl.bodies) : Std.U64).val
      = tbl.bodies.val.length := by
    rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  have hb : absExpr body = (absExprs tbl.bodies).toArray.getD i.val default ∧ ExprWF body := by
    split at hbody
    · rename_i hlt
      have hlt' : i.val < tbl.bodies.val.length := by rw [← hblen]; scalar_tac
      simp only [bind_eq_ok_iff, Result.ok.injEq] at hbody
      obtain ⟨_, rfl, e, hidx, rfl⟩ := hbody
      have hg := ExprOps.vec_index_getElem? hidx
      have hiv : (Std.UScalar.cast .Usize i : Std.Usize).val = i.val :=
        ExprOps.u64_cast_usize_val_of_lt (by have := tbl.bodies.property; omega) hlt'
      rw [hiv, List.getElem?_eq_getElem hlt'] at hg
      have hbv : tbl.bodies.val[i.val] = e := Option.some_injective _ hg
      refine ⟨?_, hbd e (by rw [← hbv]; exact List.getElem_mem hlt')⟩
      rw [toArray_getD, absExprs, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hlt', hbv]
      rfl
    · rename_i hge
      have hge' : tbl.bodies.val.length ≤ i.val := by rw [← hblen]; scalar_tac
      obtain ⟨h1, h2⟩ := default_expr_refines hbody
      refine ⟨?_, h2⟩
      rw [h1, toArray_getD, absExprs, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simpa using hge')]
      rfl
  -- the `guards.getD i .zero` guard
  have hglen : (Std.UScalar.cast .U64 (alloc.vec.Vec.len tbl.guards) : Std.U64).val
      = tbl.guards.val.length := by
    rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
  have hf : absLevel fs = (absLevels tbl.guards).getD i.val .zero ∧ LevelWF fs := by
    split at hfs
    · rename_i hlt
      have hlt' : i.val < tbl.guards.val.length := by rw [← hglen]; scalar_tac
      simp only [bind_eq_ok_iff, Result.ok.injEq] at hfs
      obtain ⟨_, rfl, l, hidx, rfl⟩ := hfs
      have hg := ExprOps.vec_index_getElem? hidx
      have hiv : (Std.UScalar.cast .Usize i : Std.Usize).val = i.val :=
        ExprOps.u64_cast_usize_val_of_lt (by have := tbl.guards.property; omega) hlt'
      rw [hiv, List.getElem?_eq_getElem hlt'] at hg
      have hbv : tbl.guards.val[i.val] = l := Option.some_injective _ hg
      refine ⟨?_, hgd l (by rw [← hbv]; exact List.getElem_mem hlt')⟩
      rw [absLevels, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hlt', hbv]
      rfl
    · rename_i hge
      have hge' : tbl.guards.val.length ≤ i.val := by rw [← hglen]; scalar_tac
      refine ⟨?_, LevelWF.zero hfs⟩
      rw [Level.zero_refines hfs, absLevels, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_none (by simpa using hge')]
      rfl
  have hlpsv : absNames lps = absNames tbl.level_params := by
    rw [absNames, absNames, PropWhen.names_copy_val hlps]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [absProjEntry, absProjTable, ConLeche.ProjTable.entry]
    simp only [hb.1, hf.1, hlpsv]
  · exact hsn
  · intro n hn
    exact hlp n (by rw [← PropWhen.names_copy_val hlps]; exact hn)
  · exact hct
  · exact hb.2
  · exact hf.2
  · exact hss

/-- `ConLeche/Kernel/Env.lean:596` — `env::proj_fn_name` refines `projFnName`. -/
theorem proj_fn_name_refines {t n : name.Name} {i : Std.U64} (ht : NameWF t)
    (h : env.proj_fn_name t i = ok n) :
    absName n = ConLeche.projFnName (absName t) i.val ∧ NameWF n := by
  rw [env.proj_fn_name] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨sl, hsl, v, hv, n1, hmk, hnum⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step ht hsl hv hmk
    (L := [112#u32, 114#u32, 111#u32, 106#u32]) (by simp [env.PROJ_STR]) (by decide)
  obtain ⟨h2, h2wf⟩ := num_lit_step h1wf hnum
  exact ⟨by rw [h2, h1]; rfl, h2wf⟩

/-- `ConLeche/Kernel/Env.lean:1201` — `env::is_rec_info` is the cited
`| some (.recInfo _ _ _ _) => true | _ => false`, on the `ConstantInfo` itself. -/
theorem is_rec_info_refines {ci : env.ConstantInfo} {c : Bool}
    (h : env.is_rec_info ci = ok c) :
    c = (match absConstantInfo ci with | .recInfo _ _ _ _ => true | _ => false) := by
  cases ci <;> (rw [env.is_rec_info] at h; simp_all [absConstantInfo])

/-- `ConLeche/Kernel/FEnv.lean:92-96` — **`fenv::find_proj` refines
`FEnv.findProj?`**, derived from `FEnvRel`'s find clause through
`proj_table_name_refines` and `proj_table_entry_refines`. -/
theorem find_proj_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) {t : name.Name} {i : Std.U64}
    {o : Option env.ProjEntry} (ht : NameWF t)
    (h : fenv.find_proj fe t i = ok o) :
    o.map absProjEntry = lfe.findProj? (absName t) i.val ∧
      ∀ pe, o = some pe → ProjEntryWF pe := by
  rw [fenv.find_proj] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, oc, hoc, h⟩ := h
  obtain ⟨habs, hnwf⟩ := proj_table_name_refines ht hn
  rw [ConLeche.FEnv.findProj?, ← habs]
  cases oc with
  | none =>
    rw [hrel.find_none hnwf hoc]
    simp only [Result.ok.injEq] at h
    subst h; exact ⟨rfl, by simp⟩
  | some ci =>
    rw [hrel.find_some hnwf hoc]
    have hciwf := hwf n ci hoc
    cases ci with
    | AxiomInfo _ | DefnInfo _ _ _ | ThmInfo _ _ | IndInfo _ _ | CtorInfo _ _ _
    | RecInfo _ _ _ _ =>
      simp only [Result.ok.injEq] at h
      subst h; exact ⟨rfl, by simp⟩
    | ProjInfo tbl =>
      dsimp only at h
      split at h
      · rename_i hlt
        have hlt' : i.val < tbl.num_fields.val := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨pe, hpe, rfl⟩ := h
        obtain ⟨h1, h2⟩ := proj_table_entry_refines hciwf hpe
        refine ⟨?_, ?_⟩
        · simp only [absConstantInfo, Option.map_some]
          rw [if_pos (show i.val < (absProjTable tbl).numFields from hlt'), h1]
        · intro pe' hpe'; rw [← Option.some_injective _ hpe']; exact h2
      · rename_i hge
        have hge' : ¬ i.val < tbl.num_fields.val := by scalar_tac
        simp only [Result.ok.injEq] at h
        subst h
        refine ⟨?_, by simp⟩
        simp only [absConstantInfo, Option.map_none]
        rw [if_neg (show ¬ i.val < (absProjTable tbl).numFields from hge')]

/-! ## The two index walks over `find_proj`/`find`

`fenv::tower_slots_all_f` and `fenv::rec_slots_all_f` are the `(List.range nF).all`
of the cited `FEnv.lean:98-110`, as the index recursion §3.4 asks for; the
`*_from` lemmas are stated on `List.range' j (nF - j)` in the task-#5 shape. -/

/-- `ConLeche/Kernel/FEnv.lean:98-99` — the index recursion behind
`tower_slots_all_f`. -/
theorem tower_slots_all_f_from_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) {t : name.Name} (ht : NameWF t) (N : Nat) :
    ∀ (n_f j : Std.U64) (c : Bool), n_f.val - j.val = N →
      fenv.tower_slots_all_f_from fe t n_f j = ok c →
      c = ((List.range' j.val (n_f.val - j.val)).all
            fun k => (lfe.findProj? (absName t) k).isSome) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n_f j c hN h
    rw [fenv.tower_slots_all_f_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have : n_f.val - j.val = 0 := by scalar_tac
      rw [this]; simp only [List.range'_zero, List.all_nil]
      exact (Result.ok_injective h).symm
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o, ho, h⟩ := h
      obtain ⟨habs, _⟩ := find_proj_refines hrel hwf ht ho
      have hsome : core.option.Option.is_some o
          = (lfe.findProj? (absName t) j.val).isSome := by
        rw [← habs, core.option.Option.is_some]; cases o <;> simp
      have hcons : n_f.val - j.val = (n_f.val - (j.val + 1)) + 1 := by omega
      rw [hcons, List.range'_succ, List.all_cons, ← hsome]
      split at h
      · rename_i hb
        simp only [bind_eq_ok_iff] at h
        obtain ⟨j2, hj2, hrec⟩ := h
        have hj2v : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
        rw [ih (n_f.val - j2.val) (by omega) n_f j2 c (by omega) hrec, hj2v]
        simp only [hb, Bool.true_and]
      · rename_i hb
        simp only [Bool.not_eq_true] at hb
        rw [hb]
        simp only [Bool.false_and]
        exact (Result.ok_injective h).symm

/-- `ConLeche/Kernel/FEnv.lean:98-99` — `fenv::tower_slots_all_f` refines
`FEnv.towerSlotsAllF` (and, since the port reads every environment through the
index, `Core.lean:1000-1005 towerSlotsAll` as well). -/
theorem tower_slots_all_f_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) {t : name.Name} {n_f : Std.U64} {c : Bool}
    (ht : NameWF t) (h : fenv.tower_slots_all_f fe t n_f = ok c) :
    c = lfe.towerSlotsAllF (absName t) n_f.val := by
  rw [fenv.tower_slots_all_f] at h
  rw [tower_slots_all_f_from_refines hrel hwf ht _ n_f 0#u64 c rfl h]
  simp [ConLeche.FEnv.towerSlotsAllF, List.range_eq_range']

/-- `ConLeche/Kernel/FEnv.lean:106-110` — `fenv::rec_slot_ok` is the cited
body's one-slot test. -/
theorem rec_slot_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) {n : name.Name} {c : Bool} (hn : NameWF n)
    (h : fenv.rec_slot_ok fe n = ok c) :
    c = (match lfe.find? (absName n) with | some (.recInfo _ _ _ _) => true | _ => false) := by
  rw [fenv.rec_slot_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  cases o with
  | none => rw [hrel.find_none hn ho]; exact (Result.ok_injective h).symm
  | some ci =>
    rw [hrel.find_some hn ho, is_rec_info_refines h]
    cases ci <;> simp [absConstantInfo]

/-- `ConLeche/Kernel/FEnv.lean:106-110` — the index recursion behind
`rec_slots_all_f`. -/
theorem rec_slots_all_f_from_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) {t : name.Name} (ht : NameWF t) (N : Nat) :
    ∀ (n_f j : Std.U64) (c : Bool), n_f.val - j.val = N →
      fenv.rec_slots_all_f_from fe t n_f j = ok c →
      c = ((List.range' j.val (n_f.val - j.val)).all
            fun k => match lfe.find? (ConLeche.projFnName (absName t) k) with
                     | some (.recInfo _ _ _ _) => true | _ => false) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n_f j c hN h
    rw [fenv.rec_slots_all_f_from.eq_def] at h
    split at h
    · rename_i hge
      have : n_f.val - j.val = 0 := by scalar_tac
      rw [this]; simp only [List.range'_zero, List.all_nil]
      exact (Result.ok_injective h).symm
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨pn, hpn, b, hb, h⟩ := h
      obtain ⟨hpnabs, hpnwf⟩ := proj_fn_name_refines ht hpn
      have hbv := rec_slot_ok_refines hrel hpnwf hb
      rw [hpnabs] at hbv
      have hcons : n_f.val - j.val = (n_f.val - (j.val + 1)) + 1 := by omega
      rw [hcons, List.range'_succ, List.all_cons, ← hbv]
      split at h
      · rename_i hbt
        simp only [bind_eq_ok_iff] at h
        obtain ⟨j2, hj2, hrec⟩ := h
        have hj2v : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
        rw [ih (n_f.val - j2.val) (by omega) n_f j2 c (by omega) hrec, hj2v]
        simp only [hbt, Bool.true_and]
      · rename_i hbt
        simp only [Bool.not_eq_true] at hbt
        rw [hbt]
        simp only [Bool.false_and]
        exact (Result.ok_injective h).symm

/-- `ConLeche/Kernel/FEnv.lean:106-110` — `fenv::rec_slots_all_f` refines
`FEnv.recSlotsAllF` (and `Core.lean:1007-1015 recSlotsAll`). -/
theorem rec_slots_all_f_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) {t : name.Name} {n_f : Std.U64} {c : Bool}
    (ht : NameWF t) (h : fenv.rec_slots_all_f fe t n_f = ok c) :
    c = lfe.recSlotsAllF (absName t) n_f.val := by
  rw [fenv.rec_slots_all_f] at h
  rw [rec_slots_all_f_from_refines hrel ht _ n_f 0#u64 c rfl h]
  simp only [ConLeche.FEnv.recSlotsAllF, List.range_eq_range',
    show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero]
  rfl

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.find_proj_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms find_proj_refines

end ConRon.Refine
