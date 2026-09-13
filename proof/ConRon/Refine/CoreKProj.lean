/-
`FEnv.findProj?`, derived (task #49, `CORE_PLAN.md` step 4).

`CoreKBase.lean`'s `FindAgree` is *find*-agreement only, so the projection-table
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

/-- `ConLeche/Kernel/Env.lean:466-468` — `env::proj_table_entry` refines
`ProjTable.entry` and its view is well formed when the table is: task #46's two
`Refine/Env.lean` lemmas, paired the way `find_proj_refines` consumes them. -/
theorem proj_table_entry_refines {tbl : env.ProjTable} {i : Std.U64} {pe : env.ProjEntry}
    (htbl : ProjTableWF tbl) (h : env.proj_table_entry tbl i = ok pe) :
    absProjEntry pe = (absProjTable tbl).entry i.val ∧ ProjEntryWF pe :=
  ⟨Env.proj_table_entry_refines h, Env.proj_table_entry_wf htbl h⟩

/-- `ConLeche/Kernel/FEnv.lean:92-96` — **`fenv::find_proj` refines
`FEnv.findProj?`**, and what it hands back is well formed.

Task #46's `FEnv.find_proj_refines` proves the same equation from the full
three-clause `FEnv.FEnvRel`; this one is derived from `FindAgree`/`FindWF`
alone (`CoreKBase.lean`'s section note says why step 4 wants the weaker
hypothesis) and adds the `ProjEntryWF` conjunct, which the projection
inference clauses need because the entry's `body` is used as a term. -/
theorem find_proj_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) {t : name.Name} {i : Std.U64}
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
    have hciwf := hwf n ci hnwf hoc
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
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) {t : name.Name} (ht : NameWF t) (N : Nat) :
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
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) {t : name.Name} {n_f : Std.U64} {c : Bool}
    (ht : NameWF t) (h : fenv.tower_slots_all_f fe t n_f = ok c) :
    c = lfe.towerSlotsAllF (absName t) n_f.val := by
  rw [fenv.tower_slots_all_f] at h
  rw [tower_slots_all_f_from_refines hrel hwf ht _ n_f 0#u64 c rfl h]
  simp [ConLeche.FEnv.towerSlotsAllF, List.range_eq_range']

/-- `ConLeche/Kernel/FEnv.lean:106-110` — `fenv::rec_slot_ok` is the cited
body's one-slot test. -/
theorem rec_slot_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) {n : name.Name} {c : Bool} (hn : NameWF n)
    (h : fenv.rec_slot_ok fe n = ok c) :
    c = (match lfe.find? (absName n) with | some (.recInfo _ _ _ _) => true | _ => false) := by
  rw [fenv.rec_slot_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  cases o with
  | none => rw [hrel.find_none hn ho]; exact (Result.ok_injective h).symm
  | some ci =>
    rw [hrel.find_some hn ho, Env.is_rec_info_refines h]
    cases ci <;> simp [absConstantInfo, ConLeche.ConstantInfo.isRecInfo]

/-- `ConLeche/Kernel/FEnv.lean:106-110` — the index recursion behind
`rec_slots_all_f`. -/
theorem rec_slots_all_f_from_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) {t : name.Name} (ht : NameWF t) (N : Nat) :
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
    (hrel : FindAgree fe lfe) {t : name.Name} {n_f : Std.U64} {c : Bool}
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
