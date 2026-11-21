/-
# `ConRon.Refine2.Checker.Justify` — Theorem 2 for the justification by a solution

`arena::justify` against `Arena/Justify.lean` (con-leche's `Cached/Justify.lean`).  The solution
is related by `SolRel`: its index by the stream index's own relation (`StreamIndexRel`), the
record mates entry for entry.  A solution lookup is the stream index's base lookup at the index's
own bound (`solution_find_eq`), so `ifenv_find_base_abs` reads it.
-/
import ConRon.Refine2.Checker.Needs
import ConRon.Refine2.Checker.StreamIndex
import ConRon.Refine2.Inductives.BlockShape
import ConRon.Arena.Justify

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The solution, related -/

/-- **`arena::justify::Solution` against the twin's `ISolution`**: the index by
`StreamIndexRel`, the mates entry for entry, the mates map well formed. -/
structure SolRel (sol : arena.justify.Solution) (J : ISolution) : Prop where
  ix : StreamIndexRel sol.ix J.idx
  mates : ConRon.Refine.HashMap2.RelOn (fun _ => True) sol.mates J.mates absNIdx absNIdxList
  matesInv : ConRon.Refine.HashMap2.Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
    sol.mates

/-- The tier `pers` with the solution's index in place of its own: what a solution lookup
reads. -/
def solTier (pers : arena.store.PersTier) (sol : arena.justify.Solution) : arena.store.PersTier :=
  { pers with env := sol.ix }

/-- **A solution lookup is a base lookup** of the solution's index, at its own bound. -/
theorem solution_find_eq (pers : arena.store.PersTier) (sol : arena.justify.Solution)
    (n : arena.handle.NIdx) :
    arena.justify.solution_find sol n =
      arena.env.ifenv_find_base (solTier pers sol) sol.ix.next n := rfl

/-- `solution_find` ⊑ `ISolution.find?`. -/
theorem solution_find_abs {pers : arena.store.PersTier} {sol : arena.justify.Solution}
    {J : ISolution} (hJ : SolRel sol J) {n : arena.handle.NIdx}
    {o : Option arena.env.IConstantInfo}
    (hrun : arena.justify.solution_find sol n = ok o) :
    o.map absIConstantInfo = J.find? (absNIdx n) := by
  rw [solution_find_eq pers] at hrun
  have hb : BaseOK (solTier pers sol) := StreamIndexRel.baseOK (pers := solTier pers sol) hJ.ix
  rw [ifenv_find_base_abs hb hrun]
  simp only [solTier]
  rw [hJ.ix.consts.rows n, ISolution.find?, ← hJ.ix.next]
  cases J.idx.base.idx[absNIdx n]? with
  | none => rfl
  | some r => obtain ⟨c, ci⟩ := r; rfl

open Lockstep in
@[lockstep] theorem solution_find_spec {pers st lst} (_hrel : AStateRel₀ pers st lst)
    {sol : arena.justify.Solution} {J : ISolution}
    (hJ : SolRel sol J) (n : arena.handle.NIdx) :
    LSP (arena.justify.solution_find sol n)
      (fun o => TwinEq (J.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (solution_find_abs (pers := pers) hJ h).symm

/-- A stored slot in range is read (`Core/LS/Prims.lean`'s private lemma, again). -/
private theorem read_tbl_slot' {ts : alloc.vec.Vec arena.env.IProjTable} {s : Std.U64} {o}
    (hslt : s.val < ts.val.length)
    (hrun : (do
        let i2 ← lift (Std.UScalar.cast .Usize s)
        if i2 < alloc.vec.Vec.len ts then
          (do
            let i4 ← lift (Std.UScalar.cast .Usize s)
            let it ← alloc.vec.Vec.index
              (core.slice.index.SliceIndexUsizeSlice arena.env.IProjTable) ts i4
            ok (some it))
        else ok none : Result (Option arena.env.IProjTable)) = ok o) :
    o.map absIProjTable = (ts.val[s.val]?).map absIProjTable := by
  have hsfit : s.val ≤ Std.Usize.max := le_of_lt (lt_of_lt_of_le hslt ts.property)
  obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hi2v : i2.val = s.val := by
    rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hsfit]
    exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi2).symm
  have hb : i2 < alloc.vec.Vec.len ts := by
    apply (Std.UScalar.lt_equiv _ _).mpr
    rw [hi2v, alloc.vec.Vec.len_val]
    exact hslt
  rw [ite_eq_left hb] at hrun
  obtain ⟨i4, hi4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨it, hit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases Result.ok_injective hrun
  have hi4v : i4.val = s.val := by
    rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hsfit]
    exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi4).symm
  have hit' := vec_index_some hit
  rw [hi4v] at hit'
  simp [hit']

/-- `solution_find_table` ⊑ `ISolution.findTable?`. -/
theorem solution_find_table_abs {pers : arena.store.PersTier} {sol : arena.justify.Solution}
    {J : ISolution} (hJ : SolRel sol J) {n : arena.handle.NIdx}
    {o : Option arena.env.IProjTable}
    (hrun : arena.justify.solution_find_table sol n = ok o) :
    o.map absIProjTable = J.findTable? (absNIdx n) := by
  rw [arena.justify.solution_find_table] at hrun
  obtain ⟨of, hof, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hf := solution_find_abs (pers := pers) hJ hof
  rw [ISolution.findTable?, ← hf]
  cases of with
  | none =>
    simp only [core.option.Option.is_some] at hrun
    cases Result.ok_injective hrun
    rfl
  | some ci =>
    simp only [core.option.Option.is_some] at hrun
    simp only [Option.map_some, Option.isSome_some, ↓reduceIte]
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hJ.ix.tables.inv
      ConRon.Refine.HashMap2.KeysOk_true trivial hr
    have hrow := hJ.ix.tables.rows n
    unfold ixTbl at hrow
    rw [← hto] at hrow
    rw [← hrow]
    cases r with
    | none => cases Result.ok_injective hrun; rfl
    | some e =>
      obtain ⟨rp, sl⟩ := e
      simp only [Option.bind_some]
      obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi3v : i3.val = sol.ix.firsts.val.length := by
        simp only [lift, Result.ok.injEq] at hi3
        subst hi3
        rw [usize_cast_u64_val']
        simp [alloc.vec.Vec.len]
      have hsz : J.idx.firsts.size = sol.ix.firsts.val.length := by
        rw [← Array.length_toList, hJ.ix.firsts]; simp
      by_cases hd : rp < i3
      · rw [ite_eq_left hd] at hrun
        have hd' : absU rp < J.idx.firsts.size := by
          have := (Std.UScalar.lt_equiv rp i3).mp hd
          simp only [absU]; omega
        have hrd := read_tbl_slot' (hJ.ix.tables.range n (rp, sl) hto.symm) hrun
        rw [hrd]
        cases sol.ix.tables.val[sl.val]? <;> simp [hd']
      · rw [ite_eq_right hd] at hrun
        cases Result.ok_injective hrun
        have hd' : ¬ absU rp < J.idx.firsts.size := by
          intro h; apply hd; apply (Std.UScalar.lt_equiv rp i3).mpr
          simp only [absU] at h; omega
        cases sol.ix.tables.val[sl.val]? <;> simp [hd']

open Lockstep in
@[lockstep] theorem solution_find_table_spec {pers st lst} (_hrel : AStateRel₀ pers st lst)
    {sol : arena.justify.Solution} {J : ISolution}
    (hJ : SolRel sol J) (n : arena.handle.NIdx) :
    LSP (arena.justify.solution_find_table sol n)
      (fun o => TwinEq (J.findTable? (absNIdx n)) (o.map absIProjTable)) :=
  fun _ h => (solution_find_table_abs (pers := pers) hJ h).symm

/-! ## The pure comparisons -/

open Lockstep in
@[lockstep] theorem is_stmt_kind_spec (ci : arena.env.IConstantInfo) :
    LSP (arena.justify.is_stmt_kind ci)
      (fun o => TwinEq (absIConstantInfo ci).isStmtKind o) := by
  intro o h
  cases ci <;> simp only [arena.justify.is_stmt_kind, Result.ok.injEq] at h <;> subst h <;> rfl

open Lockstep in
@[lockstep] theorem levels_renaming_spec (ps ps2 : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.justify.levels_renaming ps ps2)
      (fun o => TwinEq (levelsRenaming (absNIdxList ps) (absNIdxList ps2)) o) := by
  intro o h
  rw [arena.justify.levels_renaming] at h
  simp only [TwinEq, levelsRenaming, absNIdxList, List.length_map]
  by_cases hl : alloc.vec.Vec.len ps = alloc.vec.Vec.len ps2
  · simp only [hl, ↓reduceIte] at h
    have hl' : ps.val.length = ps2.val.length := by
      have := congrArg Aeneas.Std.UScalar.val hl; simpa using this
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := (name_nodup_refines hb)
    simp only [absNIdxL] at hbv
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      have := name_nodup_refines h
      simp only [absNIdxL] at this
      rw [← hbv, ← this]
      simp [hl']
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases Result.ok_injective h
      rw [← hbv]
      simp
  · simp only [hl, ↓reduceIte] at h
    cases Result.ok_injective h
    have hl' : ps.val.length ≠ ps2.val.length := by
      intro he; apply hl; apply Aeneas.Std.UScalar.eq_equiv _ _ |>.mpr; simpa using he
    simp [hl']

open Lockstep in
@[lockstep] theorem i_constant_val_beq_spec (a b : arena.env.IConstantVal) :
    LSP (arena.canon.i_constant_val_beq a b)
      (fun o => TwinEq (absIConstantVal a == absIConstantVal b) o) := by
  intro o h
  rw [i_constant_val_beq_refines h]
  simp [TwinEq, beq_eq_decide]

open Lockstep in
@[lockstep] theorem i_constant_info_beq_spec (a b : arena.env.IConstantInfo) :
    LSP (arena.canon.i_constant_info_beq a b)
      (fun o => TwinEq (absIConstantInfo a == absIConstantInfo b) o) := by
  intro o h
  rw [i_constant_info_beq_refines h]
  simp [TwinEq, beq_eq_decide]

open Lockstep in
@[lockstep] theorem i_proj_table_beq_spec (a b : arena.env.IProjTable) :
    LSP (arena.justify.i_proj_table_beq a b)
      (fun o => TwinEq (absIProjTable a == absIProjTable b) o) := by
  intro o h
  have key : (absIProjTable a == absIProjTable b) =
      ((absNIdx a.struct_name == absNIdx b.struct_name) &&
        (a.level_params.val.map absNIdx == b.level_params.val.map absNIdx) &&
        decide (a.num_params = b.num_params) &&
        (absNIdx a.ctor == absNIdx b.ctor) && decide (a.num_fields = b.num_fields) &&
        (absEIdxL a.bodies == absEIdxL b.bodies)) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, absIProjTable, IProjTable.mk.injEq, Bool.and_eq_true, decide_eq_true_eq,
      absEIdxL, absU]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨⟨⟨⟨⟨h1, h2⟩, Aeneas.Std.UScalar.eq_equiv _ _ |>.mpr h3⟩, h4⟩,
        Aeneas.Std.UScalar.eq_equiv _ _ |>.mpr h5⟩, by simpa using h6⟩
    · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
      exact ⟨h1, h2, congrArg Aeneas.Std.UScalar.val h3, h4, congrArg Aeneas.Std.UScalar.val h5, by simpa using h6⟩
  rw [TwinEq, key]
  rw [arena.justify.i_proj_table_beq] at h
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e1 := Lockstep.PA1.eq2_nidx _ _ _ hb1
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases Result.ok_injective h; simp [← e1]
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have e2 := nidx_vec_beq_spec _ _ _ hb2
    cases b2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h; cases Result.ok_injective h; simp [← e2]
    | true =>
      simp only [↓reduceIte] at h
      by_cases h3 : a.num_params = b.num_params
      · simp only [h3, ↓reduceIte] at h
        obtain ⟨b4, hb4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have e4 := Lockstep.PA1.eq2_nidx _ _ _ hb4
        cases b4 with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h; cases Result.ok_injective h
          simp [← e4]
        | true =>
          simp only [↓reduceIte] at h
          by_cases h5 : a.num_fields = b.num_fields
          · simp only [h5, ↓reduceIte] at h
            have := canon_eidx_vec_beq_twin _ _ _ h
            simp [← e1, ← e2, ← e4, h3, h5, this]
          · simp only [h5, ↓reduceIte] at h
            cases Result.ok_injective h
            simp [h5]
      · simp only [h3, ↓reduceIte] at h
        cases Result.ok_injective h
        simp [h3]

open Lockstep in
@[lockstep] theorem table_beq_p_spec (a b : Option arena.env.IProjTable) :
    LSP (arena.justify.table_beq_p a b)
      (fun o => TwinEq (tableBeqP (a.map absIProjTable) (b.map absIProjTable)) o) := by
  intro o h
  cases a <;> cases b <;> simp only [arena.justify.table_beq_p, Result.ok.injEq] at h <;>
    (try subst h) <;> (try rfl)
  exact (i_proj_table_beq_spec _ _ _ h)

/-! ## Which records offer a statement -/

open Lockstep in
@[lockstep] theorem i_declaration_dup_spec (d : arena.env.IDeclaration) :
    LSP (arena.env.i_declaration_dup d) (fun o => absIDeclaration o = absIDeclaration d) :=
  fun _ h => i_declaration_dup_abs h

open Lockstep in
@[lockstep] theorem builtin_axiom_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) :
    LS pers (fun a b => b = a) (arena.justify.builtin_axiom_name st n) lst
      (builtinAxiomName (absNIdx n)) := by
  rw [arena.justify.builtin_axiom_name, builtinAxiomName]
  lockstep

open Lockstep in
@[lockstep] theorem justifiable_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pd : arena.env.IDeclaration) :
    LS pers (fun a b => b = a.map absIConstantVal) (arena.justify.justifiable st pd) lst
      (justifiable (absIDeclaration pd)) := by
  cases pd <;> rw [arena.justify.justifiable.eq_def] <;> simp only [absIDeclaration, justifiable] <;>
    lockstep

open Lockstep in
@[lockstep] theorem side_record_val_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) (cv : arena.env.IConstantVal)
    (v : arena.handle.EIdx) :
    LS pers (fun a b => b = absIDeclaration a) (arena.justify.side_record_val pers st d cv v) lst
      (sideRecordVal (absIDeclaration d) (absIConstantVal cv) (absEIdx v)) := by
  rw [arena.justify.side_record_val, sideRecordVal]
  lockstep

open Lockstep in
@[lockstep] theorem side_record_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = absIDeclaration a) (arena.justify.side_record pers st d) lst
      (sideRecord (absIDeclaration d)) := by
  cases d <;> rw [arena.justify.side_record.eq_def] <;> simp only [absIDeclaration, sideRecord] <;>
    lockstep

/-! ## The comparison -/

open Lockstep in
@[lockstep] theorem same_cv_up_to_levels_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cv cv2 : arena.env.IConstantVal) :
    LS pers (fun a b => b = a) (arena.justify.same_cv_up_to_levels pers st cv cv2) lst
      (sameCvUpToLevels (absIConstantVal cv) (absIConstantVal cv2)) := by
  rw [arena.justify.same_cv_up_to_levels, sameCvUpToLevels]
  lockstep

open Lockstep in
@[lockstep] theorem copy_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ci2 ci : arena.env.IConstantInfo) :
    LS pers (fun a b => b = a) (arena.justify.copy_b pers st ci2 ci) lst
      (copyB (absIConstantInfo ci2) (absIConstantInfo ci)) := by
  rw [arena.justify.copy_b, copyB]
  lockstep

open Lockstep in
@[lockstep] theorem refines_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ci ci2 : arena.env.IConstantInfo) :
    LS pers (fun a b => b = a) (arena.justify.refines_b pers st ci ci2) lst
      (refinesB (absIConstantInfo ci) (absIConstantInfo ci2)) := by
  cases ci <;> rw [arena.justify.refines_b, refinesB.eq_def] <;> simp only [absIConstantInfo] <;> lockstep

/-! ## The cone -/

/-- `rec_names_of` ⊑ `recNames`, from the cursor on, onto `out`. -/
theorem rec_names_of_ls {pers} (all : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.NIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = absNIdxL a)
        (arena.justify.rec_names_of pers st all i out) lst
        (recNames (absNIdxL out) ((all.val.drop i.val).map absNIdx)) := by
  refine ls_cursor_acc all absNIdx
    (fun (w : alloc.vec.Vec arena.handle.NIdx) L => recNames (absNIdxL w) L)
    (fun st i w => arena.justify.rec_names_of pers st all i w) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [arena.justify.rec_names_of.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len all by scalar_tac), recNames]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.justify.rec_names_of.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len all by scalar_tac), recNames]
    lockstep

open Lockstep in
@[lockstep] theorem rec_names_of_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (all : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = absNIdxL a)
      (arena.justify.rec_names_of pers st all 0#usize (alloc.vec.Vec.new _)) lst
      (recNames [] (absNIdxList all)) := by
  have h := rec_names_of_ls (pers := pers) all 0#usize st lst (alloc.vec.Vec.new _) hrel hinv
  simp only [Lockstep.usize_zero_val', List.drop_zero, absNIdxL, Lockstep.vec_new_val',
    List.map_nil] at h
  exact h

/-- The mates map's lookup. -/
theorem mates_get_abs {m : ron.hashmap2.HashMap2 arena.handle.NIdx (alloc.vec.Vec arena.handle.NIdx)}
    {lm : Std.HashMap NIdx (List NIdx)}
    (hrel : ConRon.Refine.HashMap2.RelOn (fun _ => True) m lm absNIdx absNIdxList)
    (hinv : ConRon.Refine.HashMap2.Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable m)
    {k : arena.handle.NIdx} {o}
    (h : ron.hashmap2.HashMap2.get arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 m k = ok o) :
    o.map absNIdxList = lm[absNIdx k]? := by
  rw [ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hinv ConRon.Refine.HashMap2.KeysOk_true
    trivial h]
  exact hrel k trivial

open Lockstep in
/-- `needs_mates` ⊑ the cited `x.names (mates.getD n #[])`, as the twin's `match`. -/
@[lockstep] theorem needs_mates_spec {sol : arena.justify.Solution} {J : ISolution}
    (hJ : SolRel sol J) (n : arena.handle.NIdx) (x : arena.needs.NeedsSt) {y : NeedsSt}
    (hy : NSRel x y) :
    LSP (arena.justify.needs_mates sol.mates n x)
      (fun a => NSRel a (match J.mates[absNIdx n]? with
        | some ms => y.names ms
        | none => y)) := by
  intro a h
  rw [arena.justify.needs_mates] at h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hg := mates_get_abs hJ.mates hJ.matesInv ho
  cases o with
  | none =>
    rw [← hg]; cases Result.ok_injective h; exact hy
  | some ms =>
    rw [← hg]
    exact needs_names_spec x ms hy a h

open Lockstep in
@[lockstep] theorem entry_needs_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {sol : arena.justify.Solution} {J : ISolution}
    (hJ : SolRel sol J) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (ci : arena.env.IConstantInfo) :
    LS pers (fun a b => b = absNIdxList a) (arena.justify.entry_needs pers st sol.mates fe ci) lst
      (entryNeeds J.mates lfe (absIConstantInfo ci)) := by
  rw [arena.justify.entry_needs, entryNeeds]
  cases ci <;> simp only [absIConstantInfo] <;> lockstep
  -- the answer: the walk's names, its state related by `NSRel`
  all_goals exact LS.pure (NSRel.acc (by assumption)) ‹_› ‹_›

open Lockstep in
@[lockstep] theorem cone_entry_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {sol : arena.justify.Solution} {J : ISolution}
    (hJ : SolRel sol J) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (n : arena.handle.NIdx) :
    LS pers (fun a b => b = a.map absNIdxList) (arena.justify.cone_entry pers st sol fe n) lst
      (coneEntry J lfe (absNIdx n)) := by
  rw [arena.justify.cone_entry, coneEntry]
  lockstep

/-- The cone walk's answer, related: the failing name, the fuel, `seen` by `NMemoRel`. -/
abbrev ConeOut (a : Option arena.handle.NIdx × Std.U64 × ron.hashmap2.HashMap2 arena.handle.NIdx Bool)
    (b : Option NIdx × Nat × Std.HashMap NIdx Bool) : Prop :=
  ∃ m', Lockstep.NMemoRel a.2.2 m' ∧ b = (a.1.map absNIdx, absU a.2.1, m')

/-! ## The cone walk's stack -/

/-- **The cone walk's stack**: the vector up to its height, top last, against the twin's work
list, head on top. -/
def ConeStackRel (stk : alloc.vec.Vec arena.handle.NIdx) (h : Std.Usize) (l : List NIdx) : Prop :=
  h.val ≤ stk.val.length ∧ (stk.val.take h.val).reverse.map absNIdx = l

theorem cone_take_set_succ {α : Type} : ∀ (l : List α) (i : Nat) (x : α), i < l.length →
    (l.set i x).take (i + 1) = l.take i ++ [x]
  | [], _, _, h => absurd h (by simp)
  | _ :: _, 0, _, _ => by simp
  | a :: t, i + 1, x, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
    rw [cone_take_set_succ t i x (by simpa using h)]

/-- One name onto the stack: a slot overwritten below the vector's length, the vector grown at
it. -/
theorem cone_stack_put {stk stk1 : alloc.vec.Vec arena.handle.NIdx} {h h1 : Std.Usize}
    {l : List NIdx} (hs : ConeStackRel stk h l) (x : arena.handle.NIdx)
    (hstk : stk1.val = if h.val < stk.val.length then stk.val.set h.val x else stk.val ++ [x])
    (hh : h1.val = h.val + 1) : ConeStackRel stk1 h1 (absNIdx x :: l) := by
  obtain ⟨hle, hl⟩ := hs
  split at hstk
  · rename_i hlt
    refine ⟨by rw [hstk, hh]; simp; omega, ?_⟩
    rw [hstk, hh, cone_take_set_succ _ _ _ hlt]
    simp [hl]
  · have heq : h.val = stk.val.length := by omega
    refine ⟨by rw [hstk, hh]; simp; omega, ?_⟩
    rw [hstk, hh, heq]
    rw [heq, List.take_length] at hl
    simp [← hl]

/-- `cone_push`'s loop: the first `K` names of `ns` onto the stack, the last first, so the
twin's list grows by them in front. -/
theorem cone_push_loop_rel (ns : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (K : Nat) (stk : alloc.vec.Vec arena.handle.NIdx) (h k : Std.Usize) (l : List NIdx)
      {o : alloc.vec.Vec arena.handle.NIdx × Std.Usize},
      k.val = K → K ≤ ns.val.length → ConeStackRel stk h l →
      arena.justify.cone_push_loop ns stk h k = ok o →
      ConeStackRel o.1 o.2 ((ns.val.take K).map absNIdx ++ l) := by
  intro K
  induction K with
  | zero =>
    intro stk h k l o hk _ hs hrun
    rw [arena.justify.cone_push_loop.eq_def, ite_eq_left (show k = 0#usize by scalar_tac)] at hrun
    cases Result.ok_injective hrun
    simpa using hs
  | succ K ih =>
    intro stk h k l o hk hK hs hrun
    rw [arena.justify.cone_push_loop.eq_def, ite_eq_right (show ¬ k = 0#usize by scalar_tac)] at hrun
    obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hk1v := ConRon.Refine.HashMap.uscalar_sub_eq hk1
    have hone : (1#usize : Std.Usize).val = 1 := rfl
    rw [hone] at hk1v
    have hK1 : k1.val = K := by omega
    have hlt : K < ns.val.length := by omega
    obtain ⟨stk1, hstk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨h1, hh1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hh1v := ConRon.Refine.Nat.uadd_val hh1
    rw [hone] at hh1v
    have hv : (alloc.vec.Vec.len stk).val = stk.val.length := by simp [alloc.vec.Vec.len]
    have hput : stk1.val = if h.val < stk.val.length then stk.val.set h.val ns.val[K]
        else stk.val ++ [ns.val[K]] := by
      split at hstk1
      · rename_i hlt'
        rw [ite_eq_left (show h.val < stk.val.length by rw [← hv]; exact hlt')]
        obtain ⟨x, hx, hstk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hstk1
        obtain ⟨x1, hx1, hstk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hstk1
        obtain ⟨q, hq, hstk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hstk1
        obtain ⟨y, back⟩ := q
        let _ : Inhabited arena.handle.NIdx := ⟨x⟩
        obtain ⟨-, -, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hq
        cases Result.ok_injective hstk1
        have e1 := dupId_nidx _ _ hx1
        have e2 := ConRon.Refine.ExprOps.vec_index_getElem? hx
        rw [hK1, List.getElem?_eq_getElem hlt] at e2
        rw [alloc.vec.Vec.set_val_eq, e1, ← Option.some.inj e2]
      · rename_i hge
        rw [ite_eq_right (show ¬ h.val < stk.val.length from fun hc => hge (by rw [← hv] at hc; exact hc))]
        obtain ⟨x, hx, hstk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hstk1
        obtain ⟨x1, hx1, hstk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hstk1
        have e1 := dupId_nidx _ _ hx1
        have e2 := ConRon.Refine.ExprOps.vec_index_getElem? hx
        rw [hK1, List.getElem?_eq_getElem hlt] at e2
        rw [ConRon.Refine.vec_push_val hstk1, e1, ← Option.some.inj e2]
    have hs1 := cone_stack_put hs ns.val[K] hput hh1v
    have := ih stk1 h1 k1 _ hK1 (by omega) hs1 hrun
    rwa [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append,
      List.append_assoc]

/-- **`cone_push`**: the cited `ns ++ work`, on the stack. -/
theorem cone_push_rel {stk : alloc.vec.Vec arena.handle.NIdx} {h : Std.Usize} {l : List NIdx}
    (hs : ConeStackRel stk h l) (ns : alloc.vec.Vec arena.handle.NIdx)
    {o : alloc.vec.Vec arena.handle.NIdx × Std.Usize}
    (hrun : arena.justify.cone_push stk h ns = ok o) :
    ConeStackRel o.1 o.2 (absNIdxList ns ++ l) := by
  have := cone_push_loop_rel ns ns.val.length stk h (alloc.vec.Vec.len ns) l
    (by simp [alloc.vec.Vec.len]) le_rfl hs hrun
  rwa [List.take_length] at this

open Lockstep in
/-- `cone_go`'s loop ⊑ `coneGo`: induction on the fuel, and at each fuel on the stack's
height.  A name taken off the stack is the twin's head; a name accepted spends one fuel and
pushes what it reads (`cone_push_rel`). -/
theorem cone_go_loop_ls {pers} {sol : arena.justify.Solution} {J : ISolution} (hJ : SolRel sol J)
    {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe) :
    ∀ (F : Nat) (fuel : Std.U64), fuel.val = F →
    ∀ (H : Nat) (stk : alloc.vec.Vec arena.handle.NIdx) (h : Std.Usize) (W : List NIdx),
      h.val = H → ConeStackRel stk h W →
    ∀ {st lst} {rm : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {lm : Std.HashMap NIdx Bool},
      AStateRel₀ pers st lst → AStateInv pers st → Lockstep.NMemoRel rm lm →
      LS pers ConeOut (arena.justify.cone_go_loop pers st sol fe stk h fuel rm) lst
        (coneGo J lfe F lm W) := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ihF =>
  intro fuel hF H
  induction H with
  | zero =>
    intro stk h W hh hs st lst rm lm hrel hinv hm
    obtain ⟨-, hl⟩ := hs
    rw [hh, List.take_zero, List.reverse_nil, List.map_nil] at hl
    subst hl
    rw [arena.justify.cone_go_loop.eq_def, ite_eq_left (show h = 0#usize by scalar_tac), coneGo]
    exact LS.pure ⟨lm, hm, by simp [absU, hF]⟩ hrel hinv
  | succ k ihH =>
    intro stk h W hh hs st lst rm lm hrel hinv hm
    obtain ⟨hle, hl⟩ := hs
    have hlt : k < stk.val.length := by omega
    obtain ⟨h1, hh1e, hh1v⟩ := ConRon.Refine.usize_sub_ok (i := h) (by omega)
    have hb : h1.val < stk.length := by scalar_tac
    obtain ⟨x, hx, hxv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec stk h1 hb)
    have hrest : ConeStackRel stk h1 ((stk.val.take k).reverse.map absNIdx) :=
      ⟨by omega, by rw [hh1v, hh]; rfl⟩
    have hW : W = absNIdx x :: (stk.val.take k).reverse.map absNIdx := by
      rw [← hl, hh, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
        List.reverse_append]
      have : stk.val[k] = x := by rw [hxv]; simp only [show h1.val = k by omega]
      simp [this]
    subst hW
    have ihH' := fun {st lst} {rm} {lm} => ihH stk h1 _ (by omega) hrest (st := st) (lst := lst)
      (rm := rm) (lm := lm)
    clear ihH
    rw [arena.justify.cone_go_loop.eq_def, ite_eq_right (show ¬ h = 0#usize by scalar_tac), hh1e]
    simp only [bind_ok, alloc.vec.Vec.index_slice_index, hx]
    rcases F with _ | f
    · rw [coneGo]
      lockstep
    · have ihF' : ∀ (fuel' : Std.U64), fuel'.val = f →
          ∀ (stk' : alloc.vec.Vec arena.handle.NIdx) (h' : Std.Usize) (W' : List NIdx),
            ConeStackRel stk' h' W' →
          ∀ {st lst} {rm : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
            {lm : Std.HashMap NIdx Bool},
            AStateRel₀ pers st lst → AStateInv pers st → Lockstep.NMemoRel rm lm →
            LS pers ConeOut (arena.justify.cone_go_loop pers st sol fe stk' h' fuel' rm) lst
              (coneGo J lfe f lm W') :=
        fun fuel' hf stk' h' W' hs' => ihF f (by omega) fuel' hf h'.val stk' h' W' rfl hs'
      clear ihF
      rw [coneGo]
      lockstep
      -- the name refused: the fuel unspent; the name accepted: the stack pushed (`cone_push_rel`)
      all_goals first
        | exact LS.pure ⟨_, hm, by simp [absU, hF]⟩ ‹_› ‹_›
        | (refine ihF' _ ?_ _ _ _ (cone_push_rel hrest _ ‹_›) ‹_› ‹_› ‹_›; scalar_tac)

open Lockstep in
@[lockstep] theorem cone_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {sol : arena.justify.Solution} {J : ISolution}
    (hJ : SolRel sol J) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (fuel : Std.U64) {rm : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    {lm : Std.HashMap NIdx Bool} (hm : Lockstep.NMemoRel rm lm) (work : alloc.vec.Vec arena.handle.NIdx) :
    LS pers ConeOut (arena.justify.cone_go pers st sol fe fuel rm work) lst
      (coneGo J lfe (absU fuel) lm (absNIdxList work)) := by
  intro o st' hrun
  rw [arena.justify.cone_go] at hrun
  obtain ⟨⟨stk0, h0⟩, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have h00 : ConeStackRel (alloc.vec.Vec.new arena.handle.NIdx) 0#usize [] := ⟨by simp, by simp⟩
  have hs := cone_push_rel h00 work hp
  rw [List.append_nil] at hs
  exact cone_go_loop_ls hJ hctx _ fuel rfl _ stk0 h0 _ rfl hs hrel hinv hm o st' hrun

/-! ## The justification -/

open Lockstep in
/-- `name_msg` reads the name back as the twin's interpolation does; the text itself is a
message, which no relation compares. -/
@[lockstep] theorem name_msg_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pre post : alloc.vec.Vec Std.U32) (n : arena.handle.NIdx) :
    LS pers (fun _ _ => True) (arena.justify.name_msg pers st pre n post) lst
      (readNameM (absNIdx n)) := by
  rw [arena.justify.name_msg]
  lockstep

open Lockstep in
/-- `name_msg` in tail position: the twin's interpolation of the name read back. -/
theorem name_msg_tail_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pre post : alloc.vec.Vec Std.U32) (n : arena.handle.NIdx)
    (f : ConLeche.Name → String) :
    LS pers (fun _ _ => True) (arena.justify.name_msg pers st pre n post) lst
      (do let x ← readNameM (absNIdx n); pure (f x)) := by
  rw [arena.justify.name_msg]
  lockstep

open Lockstep in
@[lockstep] theorem justify_why_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {sol : arena.justify.Solution} {J : ISolution}
    (hJ : SolRel sol J) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cv : arena.env.IConstantVal) :
    LS pers (fun a b => a.isSome = b.isSome) (arena.justify.justify_why pers st sol fe cv) lst
      (justifyWhy J lfe (absIConstantVal cv)) := by
  have hnext := hJ.ix.next
  have hcw := core_walk_fuel_abs
  rw [arena.justify.justify_why, justifyWhy]
  lockstep

open Lockstep in
@[lockstep] theorem decl_label_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun _ _ => True) (arena.justify.decl_label pers st d) lst
      (declLabel (absIDeclaration d)) := by
  cases d <;> rw [arena.justify.decl_label.eq_def] <;> simp only [absIDeclaration, declLabel] <;>
    lockstep
  all_goals first
    | exact name_msg_tail_ls ‹_› ‹_› _ _ _ _
    | (convert name_msg_tail_ls ‹_› ‹_› _ _ _ (fun x => toString "inductive " ++ toString x)
        using 4; simpa [List.getElem_map, Lockstep.TwinEq] using ‹Lockstep.TwinEq (absIConstantInfo _).name _›)

open Lockstep in
@[lockstep] theorem check_justified_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {mode : kernel.env.CheckMode} {sol : arena.justify.Solution}
    {J : ISolution} (hJ : SolRel sol J) {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hfe : IFEnvRelI pers fe lfe) (pd : arena.env.IDeclaration) (cv : arena.env.IConstantVal) :
    LS pers (IFEnvRelI pers) (arena.justify.check_justified pers st mode sol fe pd cv) lst
      (checkJustified (ConRon.Refine.absMode mode) J lfe (absIDeclaration pd)
        (absIConstantVal cv)) := by
  have hctx := hfe.coreCtx
  rw [arena.justify.check_justified, checkJustified]
  lockstep
  -- the verdict of `justify_why`, an `Option` the relation pins by its constructor
  all_goals (cases ‹Option String› <;> simp at ‹Option.isSome _ = Option.isSome _›; lockstep)
  -- the reserved names' rejection: the Rust's error value thrown, the twin's thrown
  exact LS_fail_absACheckError _

/-- The solution, if any, related. -/
def OptSolRel : Option arena.justify.Solution → Option ISolution → Prop
  | none, none => True
  | some s, some J => SolRel s J
  | _, _ => False

open Lockstep in
@[lockstep] theorem check_decl_ls {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {d : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers) (arena.check_decl.check_decl pers st mode pins rf d) lst
      (checkDecl (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) lf (absIDeclaration d)) :=
  LS.ofSimRel₀ fun _ h => check_decl_refines hrel hinv hfe.rel hfe.inv h

open Lockstep in
/-- **`check_record` ⊑ `checkRecord`**: without a solution the record's own check; with one,
the justification route for a record that offers a statement. -/
@[lockstep] theorem check_record_ls {pers st lst} {rf lf}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {d : arena.env.IDeclaration}
    {sol : Option arena.justify.Solution} {J : Option ISolution} (hJ : OptSolRel sol J)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers) (arena.justify.check_record pers st mode pins sol rf d) lst
      (checkRecord (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) J lf
        (absIDeclaration d)) := by
  cases sol <;> cases J <;> simp only [OptSolRel] at hJ
  · rw [arena.justify.check_record, checkRecord]
    exact check_decl_ls hrel hinv hfe
  · rename_i s j
    rw [arena.justify.check_record, checkRecord]
    lockstep

/-! ## The records a fold with a solution checks -/

/-- `side_records` ⊑ `sideRecordsGo`, from the cursor on, onto `out`: its loop
(`side_records_loop`), one step per record. -/
theorem side_records_ls {pers} (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.env.IDeclaration),
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => b = a.val.map absIDeclaration)
        (arena.justify.side_records pers st ds i out) lst
        (sideRecordsGo (out.val.map absIDeclaration) ((ds.val.drop i.val).map absIDeclaration)) := by
  refine ls_cursor_acc ds absIDeclaration
    (fun (w : alloc.vec.Vec arena.env.IDeclaration) L =>
      sideRecordsGo (w.val.map absIDeclaration) L)
    (fun st i w => arena.justify.side_records_loop pers st ds w i) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [arena.justify.side_records_loop.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ds by scalar_tac), sideRecordsGo]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.justify.side_records_loop.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ds by scalar_tac), sideRecordsGo]
    lockstep

end ConRon.Refine2
