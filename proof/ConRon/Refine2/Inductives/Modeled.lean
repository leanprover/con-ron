/-
# `ConRon.Refine2.Inductives.Modeled` — Theorem 2 for `arena::inductives::modeled`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/modeled.rs` against
`proof/ConRon/Arena/Inductives/Modeled.lean`: the member checks against the
`_model` artifacts under the group-local renaming, the iota-rule checks
against the `_model.iota_j` theorems, the capability checks and the projection
installs.

**Ninety-one `pub fn`s against twenty-one twin `def`s — the tier's densest
split, and the crate's after `decl_check`.**  `checkIotaThm` and
`checkIotaThmN` are two hundred-line `do` blocks that DESIGN §3.4 cuts into
eight and eleven; `checkEtaThm`, `checkUnitThm`, `checkProjIota` and
`checkModeled` are cut four to eight ways each.
`Refine2/Inductives/SpecModeled.lean` carries a transcription of every
fragment and the eleven `_unfold` equations that tie them back.

## Findings

**Finding 15 (`Refine2/Inductives/Shape.lean`) is discharged here.**
`arena::expr_ops::rename_consts_fast` takes the `NIdxToNIdx` dictionary and
`Refine2/ExprOps/Mut.lean`'s statements carry `RenameRel inst f g`; the
modeled route's only instantiation is `RenameBy`, whose twin is the TABLE
`renameBy tbl` closes over.  `rename_by_refines` is the equation that says the
dictionary and the table answer the same name, and it is what discharges
`RenameRel` at every call site of this module.

**Findings 20–22 are fixed in the twin** (task #97-T2-LOCKSTEP lane
Inductives).  Round 1 recorded three places where the twin did something the
port does not: `checkIotaThm`/`checkIotaThmN` computed `eqHeadLevel` at the very
end where the port's `iota_stmt_open_at` reads it in the prologue (finding 20);
`checkIotaThm`, `checkIotaThmN` and `checkIotaRule` read the recursor's NAME
(`readName cvName`) to interpolate it into their declines, which the port
never does (finding 21, carried as an `hname : "cvName resolves"` hypothesis —
a fact about the twin's store, which a lockstep statement may not carry); and
`checkIotaSidesTy` took the name for its messages (finding 22).  The twin now
reads `eqHeadLevel` where the port does and declines with the port's constant
messages, so the `hname` hypotheses and the quantified-over names are gone.

## What these lemmas wait on

`Refine2/Specs.lean`'s `intern_*` family, `Refine2/ExprOps/**`'s
`strip_pis` / `strip_lams` / `inst_pis_at_f` / `inst_lams_at_f` /
`inst_spine` / `inst_lp_fast` / `rename_consts_fast` / `mk_app_n`,
`Refine2/Checker/Base.lean`'s `check_constant_val` / `check_def_eq_list` /
`check_annot_list` / `check_typed_list` / `unwrap_or` / `is_eq_head` /
`eq_head_level` / `doms_match_aux` / `check_proj_shape` / `check_proj_rule`,
and `Refine2/Inductives/SpecModeled.lean`'s own eleven `_unfold` equations.
**`KnotRel checkFuel` at thirty-one statements** and **finding 10's `hvis` at
thirty-four**.
-/
import ConRon.Refine2.Inductives.SpecModeled
import ConRon.Refine2.ExprOps.Mut

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The two helpers of the modeled route -/

/-- `doms_match_renamed` ⊑ `domsMatchRenamed` — `domsMatchAux` with the right
side renamed.  The dictionary and the twin's function are related by
`RenameRel` (task #97-P5-0's finding 6), which is the only difference. -/
theorem doms_match_renamed_refines {F : Type}
    {inst : arena.expr_ops.NIdxToNIdx F} {pers st lst} {f : F} {g : NIdx → NIdx}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hf : RenameRel inst f g)
    (hrun : arena.inductives.modeled.doms_match_renamed inst pers st f bs1 bs2 o1 o2
      k = ok o) :
    Sim₀ id pers lst o
      (domsMatchRenamed g (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU k)) := by
  sorry

open Lockstep in
@[lockstep] theorem doms_match_renamed_ls
    {F : Type}
    {inst : arena.expr_ops.NIdxToNIdx F}
    {pers st lst}
    {f : F}
    {g : NIdx → NIdx}
    {bs1 bs2 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {o1 o2 k : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hf : RenameRel inst f g) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.doms_match_renamed inst pers st f bs1 bs2 o1 o2 k) lst
      (domsMatchRenamed g (absBinderL bs1) (absBinderL bs2) (absU o1) (absU o2)
        (absU k)) :=
  LS.ofSim₀ fun _ h => doms_match_renamed_refines hrel hinv hf h

/-- `eq_basis_stored` ⊑ `eqBasisStored` — *the pinned `Eq` basis is the stored
`Eq`*, the guard three clauses of this module share. -/
theorem eq_basis_stored_refines {pers st lst} {vis : Std.U64} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.inductives.modeled.eq_basis_stored pers vis st rf = ok o) :
    Sim₀ id pers lst o (eqBasisStored lf) := by
  sorry

open Lockstep in
@[lockstep] theorem eq_basis_stored_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.eq_basis_stored pers vis st rf) lst
                       (eqBasisStored lf) :=
  LS.ofSim₀ fun _ h => eq_basis_stored_refines hrel hinv hfe hvis h

/-- `model_name` ⊑ `internNNode (.str n "_model")` — the one name suffix every
modeled-route lookup builds.  Over handles building a name means INTERNING
one, which is why the renaming maps are tables (the twin's module note). -/
theorem model_name_refines {pers st lst} {n : arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.model_name pers st n = ok o) :
    Sim₀ absNIdx pers lst o
      (internNNode (.str (absNIdx n) "_model")) := by
  sorry

open Lockstep in
@[lockstep] theorem model_name_ls
    {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.inductives.modeled.model_name pers st n) lst
      (internNNode (.str (absNIdx n) "_model")) :=
  LS.ofSim₀ fun _ h => model_name_refines hrel hinv h

/-- `intern_ls` ⊑ `internLsNode` at the level list `nestedRuleShape`
returned. -/
theorem intern_ls_refines {pers st lst} {us : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.intern_ls pers st us = ok o) :
    Sim₀ absLsIdx pers lst o (internLsNode (absLIdxL us)) := by
  sorry

open Lockstep in
@[lockstep] theorem intern_ls_ls
    {pers st lst}
    {us : alloc.vec.Vec arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLsIdx a) (arena.inductives.modeled.intern_ls pers st us) lst
                             (internLsNode (absLIdxL us)) :=
  LS.ofSim₀ fun _ h => intern_ls_refines hrel hinv h

/-! ## The renaming tables -/

/-- `rename_by_from` ⊑ `renameBy` from the cursor on — `tbl.find? (·.1 == n)`,
a name the table does not mention being its own image. -/
theorem rename_by_from_refines
    {tbl : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)} {i : Std.Usize}
    {n : arena.handle.NIdx} {o}
    (hrun : arena.inductives.modeled.rename_by_from tbl i n = ok o) :
    absNIdx o = renameBy (absRenameTblFrom tbl i) (absNIdx n) := by
  simp only [absRenameTblFrom, renameBy]
  refine cursor_induction (fun i : Std.Usize => i.val) tbl.val.length
    (fun i (_ : Unit) => ∀ o, arena.inductives.modeled.rename_by_from tbl i n = ok o →
      absNIdx o = (match ((tbl.val.drop i.val).map
          fun p => (absNIdx p.1, absNIdx p.2)).find? (·.1 == absNIdx n) with
        | some p => p.2
        | none => absNIdx n))
    ?_ ?_ i () o hrun
  · intro i _ hn o h
    rw [arena.inductives.modeled.rename_by_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len tbl by scalar_tac)] at h
    rw [dupId_nidx _ _ h, List.drop_eq_nil_of_le hn]
    rfl
  · intro i _ hi ih o h
    rw [arena.inductives.modeled.rename_by_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len tbl by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hqb, hqv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hq)
    obtain ⟨n1, n2⟩ := q
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b = (absNIdx n1 == absNIdx n) := nidx_eq2_abs hb
    rw [List.drop_eq_getElem_cons hqb, hqv, List.map_cons, List.find?_cons]
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      simp only [← hbv]
      rw [ih i2 () hi2v o h, hi2v]
    · rw [hbb] at h hbv
      rw [if_pos (by simp)] at h
      simp only [← hbv]
      rw [dupId_nidx _ _ h]

open Lockstep in
@[lockstep] theorem rename_by_from_twin
    {tbl : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)}
    {i : Std.Usize}
    {n : arena.handle.NIdx} :
    LSP (arena.inductives.modeled.rename_by_from tbl i n) (fun o => TwinEq (renameBy (absRenameTblFrom tbl i) (absNIdx n)) (absNIdx o)) :=
  fun o h => (rename_by_from_refines h).symm

/-- `rename_by` ⊑ `renameBy`. -/
theorem rename_by_refines
    {tbl : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)}
    {n : arena.handle.NIdx} {o}
    (hrun : arena.inductives.modeled.rename_by tbl n = ok o) :
    absNIdx o = renameBy (absRenameTbl tbl) (absNIdx n) := by
  rw [arena.inductives.modeled.rename_by] at hrun
  rw [rename_by_from_refines hrun]
  simp [absRenameTbl, absRenameTblFrom,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

open Lockstep in
@[lockstep] theorem rename_by_twin
    {tbl : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)}
    {n : arena.handle.NIdx} :
    LSP (arena.inductives.modeled.rename_by tbl n) (fun o => TwinEq (renameBy (absRenameTbl tbl) (absNIdx n)) (absNIdx o)) :=
  fun o h => (rename_by_refines h).symm

/-- **Finding 15, cashed.**  `RenameBy` IS the twin's partial application
`renameBy tbl`, so the `RenameRel` hypothesis every `rename_consts` statement
of `Refine2/ExprOps/Mut.lean` carries is discharged at this tier's every call
site by this one lemma. -/
theorem rename_by_rel {r : arena.inductives.modeled.RenameBy} :
    RenameRel arena.inductives.modeled.RenameBy.Insts.Con_ron_coreArenaExpr_opsNIdxToNIdx
      r (renameBy (absRenameBy r)) := by
  intro n o hrun
  exact (rename_by_refines hrun).symm

/-- `block_rename_table_from` ⊑ `blockRenameTable` from the cursor on, with
the accumulated pairs in front. -/
theorem block_rename_table_from_refines {pers st lst}
    {block_names : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.block_rename_table_from pers st block_names i
      out = ok o) :
    Sim₀ absRenameTbl pers lst o
      (do pure (absRenameTbl out ++
        (← blockRenameTable (absNIdxLFrom block_names i)))) := by
  sorry

open Lockstep in
@[lockstep] theorem block_rename_table_from_ls
    {pers st lst}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRenameTbl a) (arena.inductives.modeled.block_rename_table_from pers st block_names i out) lst
      (do pure (absRenameTbl out ++
        (← blockRenameTable (absNIdxLFrom block_names i)))) :=
  LS.ofSim₀ fun _ h => block_rename_table_from_refines hrel hinv h

/-- `block_rename_table` ⊑ `blockRenameTable` — every member name maps to its
`_model` companion, every other name to itself. -/
theorem block_rename_table_refines {pers st lst}
    {block_names : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.block_rename_table pers st block_names = ok o) :
    Sim₀ absRenameBy pers lst o
      (blockRenameTable (absNIdxL block_names)) := by
  sorry

open Lockstep in
@[lockstep] theorem block_rename_table_ls
    {pers st lst}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRenameBy a) (arena.inductives.modeled.block_rename_table pers st block_names) lst
      (blockRenameTable (absNIdxL block_names)) :=
  LS.ofSim₀ fun _ h => block_rename_table_refines hrel hinv h

/-- `proj_pairs_from` ⊑ `projBack.go` at `back := true` and `projFwd.go` at
`back := false`, with the accumulated pairs in front. -/
theorem proj_pairs_from_refines {pers st lst} {t : arena.handle.NIdx}
    {n_f j : Std.U64} {back : Bool}
    {out : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.proj_pairs_from pers st t n_f j back out
      = ok o) :
    Sim₀ absRenameTbl pers lst o
      (do pure (absRenameTbl out ++
        (← projPairsFromSpec (absNIdx t) back (absU n_f - absU j) (absU j)))) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_pairs_from_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {n_f j : Std.U64}
    {back : Bool}
    {out : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRenameTbl a) (arena.inductives.modeled.proj_pairs_from pers st t n_f j back out) lst
      (do pure (absRenameTbl out ++
        (← projPairsFromSpec (absNIdx t) back (absU n_f - absU j) (absU j)))) :=
  LS.ofSim₀ fun _ h => proj_pairs_from_refines hrel hinv h

/-- `proj_back` ⊑ `projBack` — rename a model-side projection type back to
public names, as a table. -/
theorem proj_back_refines {pers st lst} {t ctor : arena.handle.NIdx}
    {n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.proj_back pers st t ctor n_f = ok o) :
    Sim₀ absRenameBy pers lst o
      (projBack (absNIdx t) (absNIdx ctor) (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_back_ls
    {pers st lst}
    {t ctor : arena.handle.NIdx}
    {n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRenameBy a) (arena.inductives.modeled.proj_back pers st t ctor n_f) lst
      (projBack (absNIdx t) (absNIdx ctor) (absU n_f)) :=
  LS.ofSim₀ fun _ h => proj_back_refines hrel hinv h

/-- `proj_fwd` ⊑ `projFwd` — the forward (public → model) map on the
projection family. -/
theorem proj_fwd_refines {pers st lst} {t ctor : arena.handle.NIdx}
    {n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.proj_fwd pers st t ctor n_f = ok o) :
    Sim₀ absRenameBy pers lst o
      (projFwd (absNIdx t) (absNIdx ctor) (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_fwd_ls
    {pers st lst}
    {t ctor : arena.handle.NIdx}
    {n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absRenameBy a) (arena.inductives.modeled.proj_fwd pers st t ctor n_f) lst
      (projFwd (absNIdx t) (absNIdx ctor) (absU n_f)) :=
  LS.ofSim₀ fun _ h => proj_fwd_refines hrel hinv h

/-! ## The equation pattern -/

/-- `eq_app3` ⊑ `eqApp3?` — the shape of every pinned iota/eta/unit statement
body, read in one function.  A READER with no state in the return at all
(`SimRE`), and the module's only one. -/
theorem eq_app3_refines {pers st lst} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.eq_app3 pers st h = ok o) :
    SimRE (Option.map fun q =>
        (absNIdx q.1, absLIdx q.2.1, absEIdx q.2.2.1, absEIdx q.2.2.2.1,
          absEIdx q.2.2.2.2))
      lst o (eqApp3? (absEIdx h)) := by
  sorry

open Lockstep in
@[lockstep] theorem eq_app3_ls
    {pers st lst}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (Option.map fun q => (absNIdx q.1, absLIdx q.2.1, absEIdx q.2.2.1, absEIdx q.2.2.2.1, absEIdx q.2.2.2.2)) a) (arena.inductives.modeled.eq_app3 pers st h) st lst
            (eqApp3? (absEIdx h)) :=
  LSR.ofSimRE hrel hinv fun _ h => eq_app3_refines hrel hinv h

/-! ## The iota certificates -/

/-- `check_iota_slot_ty` ⊑ `checkIotaSidesTy`'s TT-lane tail. -/
theorem check_iota_slot_ty_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {depth : Std.U64} {alpha_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_slot_ty pers vis st mode rfS depth
      alpha_s l_a = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaSlotTySpec (ConRon.Refine.absMode mode) lfS (absU depth)
        (absEIdx alpha_s) (absLIdx l_a)) := by
  -- lockstep trial
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.modeled.check_iota_slot_ty, checkIotaSlotTySpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_iota_slot_ty_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {alpha_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_slot_ty pers vis st mode rfS depth alpha_s l_a) lst
      (checkIotaSlotTySpec (ConRon.Refine.absMode mode) lfS (absU depth)
        (absEIdx alpha_s) (absLIdx l_a)) :=
  LS.ofSim₀ fun _ h => check_iota_slot_ty_refines hrel hinv hfe hvis h

/-- `check_iota_sides_ty` ⊑ `checkIotaSidesTy` — both sides of a modeled iota
equation inhabit the equation's type, and the type slot inhabits the sort the
statement's own `Eq.{ℓA}` names. -/
theorem check_iota_sides_ty_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {depth : Std.U64}
    {alpha_s lhs_s rhs_s : arena.handle.EIdx} {l_a : arena.handle.LIdx}
    {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_sides_ty pers vis st mode rfS depth
      alpha_s lhs_s rhs_s l_a = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaSidesTy (ConRon.Refine.absMode mode) lfS (absU depth)
        (absEIdx alpha_s) (absEIdx lhs_s) (absEIdx rhs_s) (absLIdx l_a)) := by
  -- lockstep trial
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.modeled.check_iota_sides_ty, checkIotaSidesTy_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem check_iota_sides_ty_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {alpha_s lhs_s rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_sides_ty pers vis st mode rfS depth alpha_s lhs_s rhs_s l_a) lst
      (checkIotaSidesTy (ConRon.Refine.absMode mode) lfS (absU depth)
        (absEIdx alpha_s) (absEIdx lhs_s) (absEIdx rhs_s) (absLIdx l_a)) :=
  LS.ofSim₀ fun _ h => check_iota_sides_ty_refines hrel hinv hfe hvis h

/-- `iota_thm_name` ⊑ `iotaThmName` — `(cvName.str "_model").str "iota_j"`,
interned.  `toString j` is the port's own decimal recursion
(`kernel::core_k::nat_to_dec`). -/
theorem iota_thm_name_refines {pers st lst} {cv_name : arena.handle.NIdx}
    {j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.iota_thm_name pers st cv_name j = ok o) :
    Sim₀ absNIdx pers lst o
      (iotaThmName (absNIdx cv_name) (absU j)) := by
  sorry

open Lockstep in
@[lockstep] theorem iota_thm_name_ls
    {pers st lst}
    {cv_name : arena.handle.NIdx}
    {j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.inductives.modeled.iota_thm_name pers st cv_name j) lst
      (iotaThmName (absNIdx cv_name) (absU j)) :=
  LS.ofSim₀ fun _ h => iota_thm_name_refines hrel hinv h

/-- `last_d_eidx` ⊑ `xs.getLastD dflt` — the major premise is the argument
spine's last entry. -/
theorem last_d_eidx_refines {xs : alloc.vec.Vec arena.handle.EIdx}
    {dflt : arena.handle.EIdx} {o}
    (hrun : arena.inductives.modeled.last_d_eidx xs dflt = ok o) :
    absEIdx o = (absEIdxL xs).getLastD (absEIdx dflt) := by
  rw [arena.inductives.modeled.last_d_eidx] at hrun
  by_cases hz : alloc.vec.Vec.len xs = 0#usize
  · rw [if_pos hz] at hrun
    have hnil : xs.val = [] := by
      have : xs.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero this
    rw [dupId_eidx _ _ hrun, absEIdxL, hnil]
    rfl
  · rw [if_neg hz] at hrun
    have hpos : 0 < xs.val.length := by
      rcases Nat.eq_zero_or_pos xs.val.length with hc | hc
      · exact absurd (show alloc.vec.Vec.len xs = 0#usize by scalar_tac) hz
      · exact hc
    obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hi2v : i2.val = xs.val.length - 1 := by
      obtain ⟨-, hv⟩ := ConRon.Refine.Nat.usub_val hi2
      simpa using hv
    have hget : xs.val[xs.val.length - 1]? = some e := by
      rw [← hi2v]; exact vec_index_some he
    rw [dupId_eidx _ _ hrun, absEIdxL, List.getLastD_eq_getLast?,
      List.getLast?_eq_getElem?]
    simp only [List.length_map, List.getElem?_map, hget]
    rfl

open Lockstep in
@[lockstep] theorem last_d_eidx_twin
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {dflt : arena.handle.EIdx} :
    LSP (arena.inductives.modeled.last_d_eidx xs dflt) (fun o => TwinEq ((absEIdxL xs).getLastD (absEIdx dflt)) (absEIdx o)) :=
  fun o h => (last_d_eidx_refines h).symm

/-- `iota_stmt_open_at` ⊑ the prologue's tail: the telescope, the equation
head and its arity (finding 20's hoisted `eqHeadLevel` among them). -/
theorem iota_stmt_open_at_refines {pers st lst} {depth : Std.U64}
    {tty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.iota_stmt_open_at pers st depth tty = ok o) :
    Sim₀ (fun r => (absEIdxL r.1, absEIdxL r.2.1, absLIdx r.2.2))
      pers lst o (iotaStmtOpenAtSpec (absU depth) (absEIdx tty)) := by
  sorry

open Lockstep in
@[lockstep] theorem iota_stmt_open_at_ls
    {pers st lst}
    {depth : Std.U64}
    {tty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun r => (absEIdxL r.1, absEIdxL r.2.1, absLIdx r.2.2)) a) (arena.inductives.modeled.iota_stmt_open_at pers st depth tty) lst
                 (iotaStmtOpenAtSpec (absU depth) (absEIdx tty)) :=
  LS.ofSim₀ fun _ h => iota_stmt_open_at_refines hrel hinv h

/-- `iota_stmt_open` ⊑ the prologue both statement checks share. -/
theorem iota_stmt_open_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {depth j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.iota_stmt_open pers vis st rf2 cv_name lps depth
      j = ok o) :
    Sim₀ (fun r => (absEIdxL r.1, absEIdxL r.2.1, absLIdx r.2.2))
      pers lst o
      (iotaStmtOpenSpec lf2 (absNIdx cv_name) (absNIdxL lps) (absU depth) (absU j)
       ) := by
  sorry

open Lockstep in
@[lockstep] theorem iota_stmt_open_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {depth j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = (fun r => (absEIdxL r.1, absEIdxL r.2.1, absLIdx r.2.2)) a) (arena.inductives.modeled.iota_stmt_open pers vis st rf2 cv_name lps depth j) lst
      (iotaStmtOpenSpec lf2 (absNIdx cv_name) (absNIdxL lps) (absU depth) (absU j)
       ) :=
  LS.ofSim₀ fun _ h => iota_stmt_open_refines hrel hinv hfe hvis h

/-- `iota_lhs_prefix_ok` ⊑ the left side's head, arity and prefix pins. -/
theorem iota_lhs_prefix_ok_refines {pers st lst}
    {f : arena.inductives.modeled.RenameBy} {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {m_i r_p : Std.U64}
    {fvs : alloc.vec.Vec arena.handle.EIdx} {lfn : arena.handle.EIdx}
    {largs : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.iota_lhs_prefix_ok pers st f cv_name lps m_i r_p
      fvs lfn largs = ok o) :
    Sim₀ id pers lst o
      (iotaLhsPrefixOkSpec (absRenameBy f) (absNIdx cv_name) (absNIdxL lps)
        (absU m_i) (absU r_p) (absEIdxL fvs) (absEIdx lfn) (absEIdxL largs)) := by
  sorry

open Lockstep in
@[lockstep] theorem iota_lhs_prefix_ok_ls
    {pers st lst}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {m_i r_p : Std.U64}
    {fvs : alloc.vec.Vec arena.handle.EIdx}
    {lfn : arena.handle.EIdx}
    {largs : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.iota_lhs_prefix_ok pers st f cv_name lps m_i r_p fvs lfn largs) lst
      (iotaLhsPrefixOkSpec (absRenameBy f) (absNIdx cv_name) (absNIdxL lps)
        (absU m_i) (absU r_p) (absEIdxL fvs) (absEIdx lfn) (absEIdxL largs)) :=
  LS.ofSim₀ fun _ h => iota_lhs_prefix_ok_refines hrel hinv h

/-- `check_iota_major` ⊑ `checkIotaThm`'s major-premise pin. -/
theorem check_iota_major_refines {pers st lst}
    {f : arena.inductives.modeled.RenameBy} {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal} {cn_p : Std.U64}
    {fvs x_fvs largs : alloc.vec.Vec arena.handle.EIdx}
    {b0 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.check_iota_major pers st f r cvj cn_p fvs x_fvs
      largs b0 = ok o) :
    Sim₀ id pers lst o
      (checkIotaMajorSpec (absRenameBy f) (absIRecRule r) (absIConstantVal cvj)
        (absU cn_p) (absEIdxL fvs) (absEIdxL x_fvs) (absEIdxL largs)
        (absEIdx b0)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_major_ls
    {pers st lst}
    {f : arena.inductives.modeled.RenameBy}
    {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal}
    {cn_p : Std.U64}
    {fvs x_fvs largs : alloc.vec.Vec arena.handle.EIdx}
    {b0 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_iota_major pers st f r cvj cn_p fvs x_fvs largs b0) lst
      (checkIotaMajorSpec (absRenameBy f) (absIRecRule r) (absIConstantVal cvj)
        (absU cn_p) (absEIdxL fvs) (absEIdxL x_fvs) (absEIdxL largs)
        (absEIdx b0)) :=
  LS.ofSim₀ fun _ h => check_iota_major_refines hrel hinv h

/-- `check_iota_thm_rhs` ⊑ `checkIotaThm`'s right-side stage. -/
theorem check_iota_thm_rhs_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {depth : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx} {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {b0 : arena.handle.EIdx} {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_rhs pers vis st mode rfS f depth
      rhs_a fvs targs rhs_s l_a b0 = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmRhsSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absU depth) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_rhs_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {depth : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_rhs pers vis st mode rfS f depth rhs_a fvs targs rhs_s l_a b0) lst
      (checkIotaThmRhsSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absU depth) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_rhs_refines hrel hinv hfe hvis h

/-- `check_iota_thm_lams` ⊑ `checkIotaThm`'s λ-domain stage. -/
theorem check_iota_thm_lams_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {depth : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx} {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {b0 : arena.handle.EIdx}
    {all : alloc.vec.Vec arena.handle.EIdx} {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_lams pers vis st mode rfS f depth
      rhs_a fvs targs rhs_s l_a b0 all = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmLamsSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absU depth) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) (absEIdxL all) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_lams_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {depth : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {all : alloc.vec.Vec arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_lams pers vis st mode rfS f depth rhs_a fvs targs rhs_s l_a b0 all) lst
      (checkIotaThmLamsSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absU depth) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) (absEIdxL all) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_lams_refines hrel hinv hfe hvis h

/-- `check_iota_thm_frames` ⊑ `checkIotaThm`'s public-frame stage. -/
theorem check_iota_thm_frames_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p depth : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx} {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {b0 : arena.handle.EIdx} {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_frames pers vis st mode rfS f
      ty_a r_p cvj cn_p depth rhs_a fvs targs rhs_s l_a b0 = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmFramesSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU r_p) (absIConstantVal cvj) (absU cn_p) (absU depth)
        (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs) (absEIdx rhs_s)
        (absLIdx l_a) (absEIdx b0) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_frames_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p depth : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_frames pers vis st mode rfS f ty_a r_p cvj cn_p depth rhs_a fvs targs rhs_s l_a b0) lst
      (checkIotaThmFramesSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU r_p) (absIConstantVal cvj) (absU cn_p) (absU depth)
        (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs) (absEIdx rhs_s)
        (absLIdx l_a) (absEIdx b0) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_frames_refines hrel hinv hfe hvis h

/-- `check_iota_thm_prefix` ⊑ `checkIotaThm`'s prefix-domain stage. -/
theorem check_iota_thm_prefix_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p depth : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx} {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {b0 : arena.handle.EIdx} {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_prefix pers vis st mode rfS f
      ty_a r_p cvj cn_p depth rhs_a fvs targs rhs_s l_a b0 = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmPrefixSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU r_p) (absIConstantVal cvj) (absU cn_p) (absU depth)
        (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs) (absEIdx rhs_s)
        (absLIdx l_a) (absEIdx b0) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_prefix_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p depth : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_prefix pers vis st mode rfS f ty_a r_p cvj cn_p depth rhs_a fvs targs rhs_s l_a b0) lst
      (checkIotaThmPrefixSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU r_p) (absIConstantVal cvj) (absU cn_p) (absU depth)
        (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs) (absEIdx rhs_s)
        (absLIdx l_a) (absEIdx b0) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_prefix_refines hrel hinv hfe hvis h

/-- `check_iota_thm_idx` ⊑ `checkIotaThm`'s index-tuple stage. -/
theorem check_iota_thm_idx_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {m_i r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p depth : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx} {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx} {cdoms : alloc.vec.Vec arena.handle.EIdx}
    {cres : arena.handle.EIdx} {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_idx pers vis st mode rfS f ty_a
      m_i r_p cvj cn_p depth rhs_a fvs x_fvs largs targs rhs_s l_a b0 cdoms cres
      = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmIdxSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU depth) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absEIdxL cdoms) (absEIdx cres) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_idx_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {m_i r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p depth : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {cdoms : alloc.vec.Vec arena.handle.EIdx}
    {cres : arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_idx pers vis st mode rfS f ty_a m_i r_p cvj cn_p depth rhs_a fvs x_fvs largs targs rhs_s l_a b0 cdoms cres) lst
      (checkIotaThmIdxSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU depth) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absEIdxL cdoms) (absEIdx cres) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_idx_refines hrel hinv hfe hvis h

/-- `check_iota_thm_ctor` ⊑ `checkIotaThm`'s constructor-telescope stage. -/
theorem check_iota_thm_ctor_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {m_i r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx} {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx} {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_ctor pers vis st mode rfS f ty_a
      m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0 = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmCtorSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_ctor_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {m_i r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_ctor pers vis st mode rfS f ty_a m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0) lst
      (checkIotaThmCtorSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_ctor_refines hrel hinv hfe hvis h

/-- `check_iota_thm` ⊑ `checkIotaThm` — **check a canonical recursor rule's
`iota_j` theorem, semantically**. -/
theorem check_iota_thm_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p j : Std.U64} {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal} {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_iota_thm pers st mode rf2 rfS f cv_name
      lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThm (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p j : Std.U64}
    {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm pers st mode rf2 rfS f cv_name lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a) lst
      (checkIotaThm (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_iota_thm_refines hrel hinv hfe2 hfeS h

/-! ## The nested-shape recogniser -/

/-- `lower_bvars_list` ⊑ `nestedRuleShape`'s `(args.take cnP).mapM
(lowerBVarsFast …)`, from the cursor on. -/
theorem lower_bvars_list_refines {pers st lst} {k : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.lower_bvars_list pers st k xs i out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← lowerBVarsListSpec (absU k) (absEIdxLFrom xs i)))) := by
  sorry

open Lockstep in
@[lockstep] theorem lower_bvars_list_ls
    {pers st lst}
    {k : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.modeled.lower_bvars_list pers st k xs i out) lst
      (do pure (absEIdxL out ++
        (← lowerBVarsListSpec (absU k) (absEIdxLFrom xs i)))) :=
  LS.ofSim₀ fun _ h => lower_bvars_list_refines hrel hinv h

/-- `lift_bvars_list` ⊑ `nestedRuleShape`'s `pins.mapM (liftLooseBVarsFast …)`,
from the cursor on. -/
theorem lift_bvars_list_refines {pers st lst} {k : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.lift_bvars_list pers st k xs i out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← liftBVarsListSpec (absU k) (absEIdxLFrom xs i)))) := by
  sorry

open Lockstep in
@[lockstep] theorem lift_bvars_list_ls
    {pers st lst}
    {k : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.modeled.lift_bvars_list pers st k xs i out) lst
      (do pure (absEIdxL out ++
        (← liftBVarsListSpec (absU k) (absEIdxLFrom xs i)))) :=
  LS.ofSim₀ fun _ h => lift_bvars_list_refines hrel hinv h

/-- `nested_pins_ok` ⊑ `nestedRuleShape`'s `pins.allM`, from the cursor on. -/
theorem nested_pins_ok_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {lps : alloc.vec.Vec arena.handle.NIdx} {r_p : Std.U64}
    {pins : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.nested_pins_ok pers vis st rfS lps r_p pins i
      = ok o) :
    Sim₀ id pers lst o
      (nestedPinsOkSpec lfS (absNIdxL lps) (absU r_p) (absEIdxLFrom pins i)) := by
  sorry

open Lockstep in
@[lockstep] theorem nested_pins_ok_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {r_p : Std.U64}
    {pins : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.nested_pins_ok pers vis st rfS lps r_p pins i) lst
      (nestedPinsOkSpec lfS (absNIdxL lps) (absU r_p) (absEIdxLFrom pins i)) :=
  LS.ofSim₀ fun _ h => nested_pins_ok_refines hrel hinv hfe hvis h

/-- `nested_rule_shape_args` ⊑ `nestedRuleShape`'s argument-spine stage. -/
theorem nested_rule_shape_args_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {lps : alloc.vec.Vec arena.handle.NIdx} {m_i r_p cn_p : Std.U64}
    {dom : arena.handle.EIdx} {lvls_idx : arena.handle.LsIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.nested_rule_shape_args pers vis st rfS lps m_i
      r_p cn_p dom lvls_idx = ok o) :
    Sim₀ (Option.map fun q => (absLIdxL q.1, absEIdxL q.2)) pers lst o
      (nestedRuleShapeArgsSpec lfS (absNIdxL lps) (absU m_i) (absU r_p) (absU cn_p)
        (absEIdx dom) (absLsIdx lvls_idx)) := by
  sorry

open Lockstep in
@[lockstep] theorem nested_rule_shape_args_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {m_i r_p cn_p : Std.U64}
    {dom : arena.handle.EIdx}
    {lvls_idx : arena.handle.LsIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (Option.map fun q => (absLIdxL q.1, absEIdxL q.2)) a) (arena.inductives.modeled.nested_rule_shape_args pers vis st rfS lps m_i r_p cn_p dom lvls_idx) lst
      (nestedRuleShapeArgsSpec lfS (absNIdxL lps) (absU m_i) (absU r_p) (absU cn_p)
        (absEIdx dom) (absLsIdx lvls_idx)) :=
  LS.ofSim₀ fun _ h => nested_rule_shape_args_refines hrel hinv hfe hvis h

/-- `nested_rule_shape_at` ⊑ `nestedRuleShape`'s body past the `iota_j`
guard. -/
theorem nested_rule_shape_at_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {lps : alloc.vec.Vec arena.handle.NIdx} {ty_a : arena.handle.EIdx}
    {m_i r_p cn_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.nested_rule_shape_at pers vis st rfS lps ty_a
      m_i r_p cn_p = ok o) :
    Sim₀ (Option.map fun q => (absLIdxL q.1, absEIdxL q.2)) pers lst o
      (nestedRuleShapeAtSpec lfS (absNIdxL lps) (absEIdx ty_a) (absU m_i)
        (absU r_p) (absU cn_p)) := by
  sorry

open Lockstep in
@[lockstep] theorem nested_rule_shape_at_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p cn_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (Option.map fun q => (absLIdxL q.1, absEIdxL q.2)) a) (arena.inductives.modeled.nested_rule_shape_at pers vis st rfS lps ty_a m_i r_p cn_p) lst
      (nestedRuleShapeAtSpec lfS (absNIdxL lps) (absEIdx ty_a) (absU m_i)
        (absU r_p) (absU cn_p)) :=
  LS.ofSim₀ fun _ h => nested_rule_shape_at_refines hrel hinv hfe hvis h

/-- `nested_rule_shape` ⊑ `nestedRuleShape` — the constructor's level and
parameter instantiations, read off the recursor type's major-premise
domain. -/
theorem nested_rule_shape_refines {pers st lst} {rf2 lf2} {rfS lfS}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p cn_p j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.nested_rule_shape pers st rf2 rfS cv_name lps
      ty_a m_i r_p cn_p j = ok o) :
    Sim₀ (Option.map fun q => (absLIdxL q.1, absEIdxL q.2)) pers lst o
      (nestedRuleShape lf2 lfS (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a)
        (absU m_i) (absU r_p) (absU cn_p) (absU j)) := by
  -- lockstep trial
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.modeled.nested_rule_shape, nestedRuleShape_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem nested_rule_shape_ls
    {pers st lst}
    {rf2 lf2}
    {rfS lfS}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p cn_p j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = (Option.map fun q => (absLIdxL q.1, absEIdxL q.2)) a) (arena.inductives.modeled.nested_rule_shape pers st rf2 rfS cv_name lps ty_a m_i r_p cn_p j) lst
      (nestedRuleShape lf2 lfS (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a)
        (absU m_i) (absU r_p) (absU cn_p) (absU j)) :=
  LS.ofSim₀ fun _ h => nested_rule_shape_refines hrel hinv hfe2 hfeS h

/-! ## `checkIotaThmN` -/

/-- `inst_spine_list_renamed` ⊑ `checkIotaThmN`'s `pins.mapM fun p =>
instSpine … (← renameConsts f p)`, from the cursor on. -/
theorem inst_spine_list_renamed_refines {pers st lst}
    {f : arena.inductives.modeled.RenameBy}
    {args : alloc.vec.Vec arena.handle.EIdx} {t : Std.U64}
    {pins : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.inst_spine_list_renamed pers st f args t pins i
      out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← instSpineListRenamedSpec (absRenameBy f) (absEIdxL args) (absU t)
          (absEIdxLFrom pins i)))) := by
  sorry

open Lockstep in
@[lockstep] theorem inst_spine_list_renamed_ls
    {pers st lst}
    {f : arena.inductives.modeled.RenameBy}
    {args : alloc.vec.Vec arena.handle.EIdx}
    {t : Std.U64}
    {pins : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.modeled.inst_spine_list_renamed pers st f args t pins i out) lst
      (do pure (absEIdxL out ++
        (← instSpineListRenamedSpec (absRenameBy f) (absEIdxL args) (absU t)
          (absEIdxLFrom pins i)))) :=
  LS.ofSim₀ fun _ h => inst_spine_list_renamed_refines hrel hinv h

/-- `inst_spine_list` ⊑ the same without the renaming — the public frame's. -/
theorem inst_spine_list_refines {pers st lst}
    {args : alloc.vec.Vec arena.handle.EIdx} {t : Std.U64}
    {pins : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.inst_spine_list pers st args t pins i out
      = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← instSpineListSpec (absEIdxL args) (absU t)
          (absEIdxLFrom pins i)))) := by
  sorry

open Lockstep in
@[lockstep] theorem inst_spine_list_ls
    {pers st lst}
    {args : alloc.vec.Vec arena.handle.EIdx}
    {t : Std.U64}
    {pins : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.modeled.inst_spine_list pers st args t pins i out) lst
      (do pure (absEIdxL out ++
        (← instSpineListSpec (absEIdxL args) (absU t)
          (absEIdxLFrom pins i)))) :=
  LS.ofSim₀ fun _ h => inst_spine_list_refines hrel hinv h

/-- `check_iota_thm_n_fields` ⊑ `checkIotaThmN`'s field stage. -/
theorem check_iota_thm_n_fields_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {m_i r_p cn_p cn_f : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx} {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {b0 : arena.handle.EIdx}
    {fvs_p : alloc.vec.Vec arena.handle.EIdx} {crest_p : arena.handle.EIdx}
    {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_n_fields pers vis st mode rfS f
      m_i r_p cn_p cn_f rhs_a fvs targs rhs_s l_a b0 fvs_p crest_p = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmNFieldsSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absU m_i) (absU r_p) (absU cn_p) (absU cn_f) (absEIdx rhs_a)
        (absEIdxL fvs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0)
        (absEIdxL fvs_p) (absEIdx crest_p) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_n_fields_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {m_i r_p cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {crest_p : arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_n_fields pers vis st mode rfS f m_i r_p cn_p cn_f rhs_a fvs targs rhs_s l_a b0 fvs_p crest_p) lst
      (checkIotaThmNFieldsSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absU m_i) (absU r_p) (absU cn_p) (absU cn_f) (absEIdx rhs_a)
        (absEIdxL fvs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0)
        (absEIdxL fvs_p) (absEIdx crest_p) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_fields_refines hrel hinv hfe hvis h

/-- `check_iota_thm_n_frames` ⊑ `checkIotaThmN`'s public-frame stage. -/
theorem check_iota_thm_n_frames_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {m_i r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx} {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {b0 : arena.handle.EIdx}
    {lvls_idx : arena.handle.LsIdx} {pins : alloc.vec.Vec arena.handle.EIdx}
    {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_n_frames pers vis st mode rfS f
      ty_a m_i r_p cvj cn_p cn_f rhs_a fvs targs rhs_s l_a b0 lvls_idx pins
      = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmNFramesSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) (absLsIdx lvls_idx)
        (absEIdxL pins) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_n_frames_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {m_i r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lvls_idx : arena.handle.LsIdx}
    {pins : alloc.vec.Vec arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_n_frames pers vis st mode rfS f ty_a m_i r_p cvj cn_p cn_f rhs_a fvs targs rhs_s l_a b0 lvls_idx pins) lst
      (checkIotaThmNFramesSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) (absLsIdx lvls_idx)
        (absEIdxL pins) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_frames_refines hrel hinv hfe hvis h

/-- `check_iota_thm_n_prefix` ⊑ `checkIotaThmN`'s prefix-domain stage. -/
theorem check_iota_thm_n_prefix_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {m_i r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx} {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx} {b0 : arena.handle.EIdx}
    {lvls_idx : arena.handle.LsIdx} {pins : alloc.vec.Vec arena.handle.EIdx}
    {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_n_prefix pers vis st mode rfS f
      ty_a m_i r_p cvj cn_p cn_f rhs_a fvs targs rhs_s l_a b0 lvls_idx pins
      = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmNPrefixSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) (absLsIdx lvls_idx)
        (absEIdxL pins) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_n_prefix_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {m_i r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lvls_idx : arena.handle.LsIdx}
    {pins : alloc.vec.Vec arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_n_prefix pers vis st mode rfS f ty_a m_i r_p cvj cn_p cn_f rhs_a fvs targs rhs_s l_a b0 lvls_idx pins) lst
      (checkIotaThmNPrefixSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL targs)
        (absEIdx rhs_s) (absLIdx l_a) (absEIdx b0) (absLsIdx lvls_idx)
        (absEIdxL pins) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_prefix_refines hrel hinv hfe hvis h

/-- `check_iota_thm_n_idx` ⊑ `checkIotaThmN`'s index-tuple stage. -/
theorem check_iota_thm_n_idx_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {m_i r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx} {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx} {lvls_idx : arena.handle.LsIdx}
    {pins cdoms : alloc.vec.Vec arena.handle.EIdx} {cres : arena.handle.EIdx}
    {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_n_idx pers vis st mode rfS f ty_a
      m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0 lvls_idx pins
      cdoms cres = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmNIdxSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absLsIdx lvls_idx) (absEIdxL pins) (absEIdxL cdoms)
        (absEIdx cres) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_n_idx_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {m_i r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lvls_idx : arena.handle.LsIdx}
    {pins cdoms : alloc.vec.Vec arena.handle.EIdx}
    {cres : arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_n_idx pers vis st mode rfS f ty_a m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0 lvls_idx pins cdoms cres) lst
      (checkIotaThmNIdxSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absLsIdx lvls_idx) (absEIdxL pins) (absEIdxL cdoms)
        (absEIdx cres) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_idx_refines hrel hinv hfe hvis h

/-- `check_iota_thm_n_ctor` ⊑ `checkIotaThmN`'s constructor-telescope stage. -/
theorem check_iota_thm_n_ctor_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {m_i r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx} {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx} {lvls_idx : arena.handle.LsIdx}
    {pins pins_f : alloc.vec.Vec arena.handle.EIdx} {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_n_ctor pers vis st mode rfS f
      ty_a m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0 lvls_idx
      pins pins_f = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmNCtorSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absLsIdx lvls_idx) (absEIdxL pins) (absEIdxL pins_f)
        lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_n_ctor_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {m_i r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lvls_idx : arena.handle.LsIdx}
    {pins pins_f : alloc.vec.Vec arena.handle.EIdx}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_n_ctor pers vis st mode rfS f ty_a m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0 lvls_idx pins pins_f) lst
      (checkIotaThmNCtorSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absLsIdx lvls_idx) (absEIdxL pins) (absEIdxL pins_f)
        lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_ctor_refines hrel hinv hfe hvis h

/-- `check_iota_thm_n_major` ⊑ `checkIotaThmN`'s major-premise stage. -/
theorem check_iota_thm_n_major_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx} {m_i r_p : Std.U64} {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64} {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx} {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx} {lvls : alloc.vec.Vec arena.handle.LIdx}
    {pins pins_f : alloc.vec.Vec arena.handle.EIdx} {r : arena.env.IRecRule}
    {lcv : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_thm_n_major pers vis st mode rfS f
      ty_a m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0 lvls pins
      pins_f r = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmNMajorSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absLIdxL lvls) (absEIdxL pins) (absEIdxL pins_f)
        (absIRecRule r) lcv) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_n_major_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {f : arena.inductives.modeled.RenameBy}
    {ty_a : arena.handle.EIdx}
    {m_i r_p : Std.U64}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fvs x_fvs largs targs : alloc.vec.Vec arena.handle.EIdx}
    {rhs_s : arena.handle.EIdx}
    {l_a : arena.handle.LIdx}
    {b0 : arena.handle.EIdx}
    {lvls : alloc.vec.Vec arena.handle.LIdx}
    {pins pins_f : alloc.vec.Vec arena.handle.EIdx}
    {r : arena.env.IRecRule}
    {lcv : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_n_major pers vis st mode rfS f ty_a m_i r_p cvj cn_p cn_f rhs_a fvs x_fvs largs targs rhs_s l_a b0 lvls pins pins_f r) lst
      (checkIotaThmNMajorSpec (ConRon.Refine.absMode mode) lfS (absRenameBy f)
        (absEIdx ty_a) (absU m_i) (absU r_p) (absIConstantVal cvj) (absU cn_p)
        (absU cn_f) (absEIdx rhs_a) (absEIdxL fvs) (absEIdxL x_fvs)
        (absEIdxL largs) (absEIdxL targs) (absEIdx rhs_s) (absLIdx l_a)
        (absEIdx b0) (absLIdxL lvls) (absEIdxL pins) (absEIdxL pins_f)
        (absIRecRule r) lcv) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_major_refines hrel hinv hfe hvis h

/-- `check_iota_thm_n_at` ⊑ `checkIotaThmN`'s prologue at a recognised shape. -/
theorem check_iota_thm_n_at_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p j : Std.U64} {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal} {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx} {lvls : alloc.vec.Vec arena.handle.LIdx}
    {pins : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_iota_thm_n_at pers st mode rf2 rfS f
      cv_name lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a lvls pins = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkIotaThmNAtSpec (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a) (absLIdxL lvls) (absEIdxL pins)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_thm_n_at_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p j : Std.U64}
    {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {lvls : alloc.vec.Vec arena.handle.LIdx}
    {pins : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_iota_thm_n_at pers st mode rf2 rfS f cv_name lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a lvls pins) lst
      (checkIotaThmNAtSpec (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a) (absLIdxL lvls) (absEIdxL pins)) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_at_refines hrel hinv hfe2 hfeS h

/-- `check_iota_thm_n` ⊑ `checkIotaThmN` — **the nested-auxiliary statement
check**: a rule the nested shape does not recognise is `.inert`, and the
twin's closing `pure (.nested lvls pins)` is this function's `Ok`. -/
theorem check_iota_thm_n_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p j : Std.U64} {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal} {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_iota_thm_n pers st mode rf2 rfS f cv_name
      lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok o) :
    Sim₀ absIRecRuleFire pers lst o
      (checkIotaThmN (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a)) := by
  -- lockstep trial
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.modeled.check_iota_thm_n, checkIotaThmN_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem check_iota_thm_n_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p j : Std.U64}
    {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = absIRecRuleFire a) (arena.inductives.modeled.check_iota_thm_n pers st mode rf2 rfS f cv_name lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a) lst
      (checkIotaThmN (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_iota_thm_n_refines hrel hinv hfe2 hfeS h

/-! ## One rule, and the fold over a recursor's rules -/

/-- `check_iota_rule_bits` ⊑ `checkIotaRule`'s stored rule. -/
theorem check_iota_rule_bits_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {cv_name : arena.handle.NIdx} {r : arena.env.IRecRule} {cn_p : Std.U64}
    {rhs_a : arena.handle.EIdx} {fire : arena.env.IRecRuleFire} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_iota_rule_bits pers vis st rf2 cv_name r
      cn_p rhs_a fire = ok o) :
    Sim₀ absIRecRule pers lst o
      (checkIotaRuleBitsSpec lf2 (absNIdx cv_name) (absIRecRule r) (absU cn_p)
        (absEIdx rhs_a) (absIRecRuleFire fire)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_rule_bits_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {cv_name : arena.handle.NIdx}
    {r : arena.env.IRecRule}
    {cn_p : Std.U64}
    {rhs_a : arena.handle.EIdx}
    {fire : arena.env.IRecRuleFire}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = absIRecRule a) (arena.inductives.modeled.check_iota_rule_bits pers vis st rf2 cv_name r cn_p rhs_a fire) lst
      (checkIotaRuleBitsSpec lf2 (absNIdx cv_name) (absIRecRule r) (absU cn_p)
        (absEIdx rhs_a) (absIRecRuleFire fire)) :=
  LS.ofSim₀ fun _ h => check_iota_rule_bits_refines hrel hinv hfe hvis h

/-- `check_iota_rule_fire` ⊑ `checkIotaRule`'s guard-and-firing stage. -/
theorem check_iota_rule_fire_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p j : Std.U64} {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal} {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_iota_rule_fire pers st mode rf2 rfS f
      cv_name lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a = ok o) :
    Sim₀ absIRecRule pers lst o
      (checkIotaRuleFireSpec (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_rule_fire_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p j : Std.U64}
    {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = absIRecRule a) (arena.inductives.modeled.check_iota_rule_fire pers st mode rf2 rfS f cv_name lps ty_a m_i r_p j r cvj cn_p cn_f rhs_a) lst
      (checkIotaRuleFireSpec (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
        (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_iota_rule_fire_refines hrel hinv hfe2 hfeS h

/-- `check_iota_rule_wf` ⊑ `checkIotaRule`'s well-formedness stage. -/
theorem check_iota_rule_wf_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p j : Std.U64} {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal} {cn_p cn_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_iota_rule_wf pers st mode rf2 rfS f
      cv_name lps ty_a m_i r_p j r cvj cn_p cn_f = ok o) :
    Sim₀ absIRecRule pers lst o
      (checkIotaRuleWfSpec (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
       ) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_rule_wf_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p j : Std.U64}
    {r : arena.env.IRecRule}
    {cvj : arena.env.IConstantVal}
    {cn_p cn_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = absIRecRule a) (arena.inductives.modeled.check_iota_rule_wf pers st mode rf2 rfS f cv_name lps ty_a m_i r_p j r cvj cn_p cn_f) lst
      (checkIotaRuleWfSpec (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r) (absIConstantVal cvj) (absU cn_p) (absU cn_f)
       ) :=
  LS.ofSim₀ fun _ h => check_iota_rule_wf_refines hrel hinv hfe2 hfeS h

/-- `check_iota_rule` ⊑ `checkIotaRule` — one modeled recursor rule: generic
well-formedness of the right-hand side, then the model's `iota_j` theorem. -/
theorem check_iota_rule_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p j : Std.U64} {r : arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_iota_rule pers st mode rf2 rfS f cv_name
      lps ty_a m_i r_p j r = ok o) :
    Sim₀ absIRecRule pers lst o
      (checkIotaRule (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_rule_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p j : Std.U64}
    {r : arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = absIRecRule a) (arena.inductives.modeled.check_iota_rule pers st mode rf2 rfS f cv_name lps ty_a m_i r_p j r) lst
      (checkIotaRule (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
        (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
        (absU j) (absIRecRule r)) :=
  LS.ofSim₀ fun _ h => check_iota_rule_refines hrel hinv hfe2 hfeS h

/-- `check_iota_rules` ⊑ `checkIotaRules` from the cursor on, with the
accumulated rules in front. -/
theorem check_iota_rules_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx} {m_i r_p j : Std.U64}
    {rules : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_iota_rules pers st mode rf2 rfS f cv_name
      lps ty_a m_i r_p j rules i out = ok o) :
    Sim₀ absIRecRuleL pers lst o
      (do pure (absIRecRuleL out ++
        (← checkIotaRules (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
          (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
          (absU j) (absIRecRuleLFrom rules i)))) := by
  sorry

open Lockstep in
@[lockstep] theorem check_iota_rules_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {cv_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ty_a : arena.handle.EIdx}
    {m_i r_p j : Std.U64}
    {rules : alloc.vec.Vec arena.env.IRecRule}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = absIRecRuleL a) (arena.inductives.modeled.check_iota_rules pers st mode rf2 rfS f cv_name lps ty_a m_i r_p j rules i out) lst
      (do pure (absIRecRuleL out ++
        (← checkIotaRules (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f)
          (absNIdx cv_name) (absNIdxL lps) (absEIdx ty_a) (absU m_i) (absU r_p)
          (absU j) (absIRecRuleLFrom rules i)))) :=
  LS.ofSim₀ fun _ h => check_iota_rules_refines hrel hinv hfe2 hfeS h

/-! ## The block's members -/

/-- `check_member_model` ⊑ `checkMemberVal`'s model-counterpart stage. -/
theorem check_member_model_refines {pers st lst} {vis : Std.U64}
    {f : arena.inductives.modeled.RenameBy} {rf2 lf2}
    {cv_a : arena.env.IConstantVal} {lblock : List NIdx} {lan : ConLeche.Name} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_member_model pers vis st f rf2 cv_a
      = ok o) :
    Sim₀ absIConstantVal pers lst o
      (checkMemberModelSpec (absRenameBy f) lf2 (absIConstantVal cv_a) lblock
        lan) := by
  sorry

open Lockstep in
@[lockstep] theorem check_member_model_ls
    {pers st lst}
    {vis : Std.U64}
    {f : arena.inductives.modeled.RenameBy}
    {rf2 lf2}
    {cv_a : arena.env.IConstantVal}
    {lblock : List NIdx}
    {lan : ConLeche.Name}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a) (arena.inductives.modeled.check_member_model pers vis st f rf2 cv_a) lst
      (checkMemberModelSpec (absRenameBy f) lf2 (absIConstantVal cv_a) lblock
        lan) :=
  LS.ofSim₀ fun _ h => check_member_model_refines hrel hinv hfe hvis h

/-- `check_member_val` ⊑ `checkMemberVal` — a block member's constant against
its `_model` counterpart. -/
theorem check_member_val_refines {pers st lst} {vis : Std.U64}
    {mode : kernel.env.CheckMode} {block_names : alloc.vec.Vec arena.handle.NIdx}
    {rf2 lf2} {cv : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_member_val pers vis st mode block_names
      rf2 cv = ok o) :
    Sim₀ absIConstantVal pers lst o
      (checkMemberVal (ConRon.Refine.absMode mode) (absNIdxL block_names) lf2
        (absIConstantVal cv)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_member_val_ls
    {pers st lst}
    {vis : Std.U64}
    {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    {rf2 lf2}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a) (arena.inductives.modeled.check_member_val pers vis st mode block_names rf2 cv) lst
      (checkMemberVal (ConRon.Refine.absMode mode) (absNIdxL block_names) lf2
        (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_member_val_refines hrel hinv hfe hvis h

/-- `check_ind_member` ⊑ `checkIndMember` — check and install one non-recursor
member against its `_model` counterpart, with the executed tier's flush at the
environment transition. -/
theorem check_ind_member_refines {pers st lst} {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx} {caps : arena.env.IIndCaps}
    {rf2 lf2} {ci : arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hrun : arena.inductives.modeled.check_ind_member pers st mode block_names caps
      rf2 ci = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkIndMember (ConRon.Refine.absMode mode) (absNIdxL block_names)
        (absIIndCaps caps) lf2 (absIConstantInfo ci)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_ind_member_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    {caps : arena.env.IIndCaps}
    {rf2 lf2}
    {ci : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) :
    LS pers IFEnvRelI (arena.inductives.modeled.check_ind_member pers st mode block_names caps rf2 ci) lst
      (checkIndMember (ConRon.Refine.absMode mode) (absNIdxL block_names)
        (absIIndCaps caps) lf2 (absIConstantInfo ci)) :=
  LS.ofSimRel₀ fun _ h => check_ind_member_refines hrel hinv hfe h

/-- `check_ind_members` ⊑ `checkIndMembers` from the cursor on. -/
theorem check_ind_members_refines {pers st lst} {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx} {caps : arena.env.IIndCaps}
    {rf lf} {nonrecs : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.modeled.check_ind_members pers st mode block_names caps
      rf nonrecs i = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkIndMembers (ConRon.Refine.absMode mode) (absNIdxL block_names)
        (absIIndCaps caps) lf (absICILFrom nonrecs i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_ind_members_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    {caps : arena.env.IIndCaps}
    {rf lf}
    {nonrecs : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.inductives.modeled.check_ind_members pers st mode block_names caps rf nonrecs i) lst
      (checkIndMembers (ConRon.Refine.absMode mode) (absNIdxL block_names)
        (absIIndCaps caps) lf (absICILFrom nonrecs i)) :=
  LS.ofSimRel₀ fun _ h => check_ind_members_refines hrel hinv hfe h

/-- `provision_recs` ⊑ `provisionRecs` from the cursor on, with the
accumulated checked records in front — phase 0 of the recursor group. -/
theorem provision_recs_refines {pers st lst} {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx} {rfA lfA}
    {recs : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfA lfA)
    (hrun : arena.inductives.modeled.provision_recs pers st mode block_names rfA recs
      i out = ok o) :
    SimRel₀ (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = absRecsL out ++ absRecsL r.2)
      pers lst o
      (provisionRecs (ConRon.Refine.absMode mode) (absNIdxL block_names) lfA
        (absICILFrom recs i)) := by
  sorry

open Lockstep in
@[lockstep] theorem provision_recs_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    {rfA lfA}
    {recs : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfA lfA) :
    LS pers (fun r v => IFEnvRelI r.1 v.1 ∧ v.2 = absRecsL out ++ absRecsL r.2) (arena.inductives.modeled.provision_recs pers st mode block_names rfA recs i out) lst
      (provisionRecs (ConRon.Refine.absMode mode) (absNIdxL block_names) lfA
        (absICILFrom recs i)) :=
  LS.ofSimRel₀ fun _ h => provision_recs_refines hrel hinv hfe h

/-- `install_ind_recs` ⊑ `installIndRecs` from the cursor on. -/
theorem install_ind_recs_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {f : arena.inductives.modeled.RenameBy} {rfA lfA}
    {checked : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hfeA : IFEnvRelI rfA lfA)
    (hrun : arena.inductives.modeled.install_ind_recs pers st mode rf2 rfS f rfA
      checked i = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (installIndRecs (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f) lfA
        (absRecsLFrom checked i)) := by
  sorry

open Lockstep in
@[lockstep] theorem install_ind_recs_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {f : arena.inductives.modeled.RenameBy}
    {rfA lfA}
    {checked : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hfeA : IFEnvRelI rfA lfA) :
    LS pers IFEnvRelI (arena.inductives.modeled.install_ind_recs pers st mode rf2 rfS f rfA checked i) lst
      (installIndRecs (ConRon.Refine.absMode mode) lf2 lfS (absRenameBy f) lfA
        (absRecsLFrom checked i)) :=
  LS.ofSimRel₀ fun _ h => install_ind_recs_refines hrel hinv hfe2 hfeS hfeA h

/-- `check_ind_recs` ⊑ `checkIndRecs` — check and install a block's recursors
*as a group*.  The twin uses `fe₂` four times where Lean's value semantics
copies it for free; the port pays two `ifenv_dup`s, which the refinement
absorbs as `IFEnvRel` of the same record. -/
theorem check_ind_recs_refines {pers st lst} {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx} {rf2 lf2}
    {recs : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hrun : arena.inductives.modeled.check_ind_recs pers st mode block_names rf2 recs
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkIndRecs (ConRon.Refine.absMode mode) (absNIdxL block_names) lf2
        (absICIL recs)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_ind_recs_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    {rf2 lf2}
    {recs : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) :
    LS pers IFEnvRelI (arena.inductives.modeled.check_ind_recs pers st mode block_names rf2 recs) lst
      (checkIndRecs (ConRon.Refine.absMode mode) (absNIdxL block_names) lf2
        (absICIL recs)) :=
  LS.ofSimRel₀ fun _ h => check_ind_recs_refines hrel hinv hfe h

/-! ## The projection functions -/

/-- `check_proj_lookups_model` ⊑ `checkProjLookups`' model stage. -/
theorem check_proj_lookups_model_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx} {i : Std.U64}
    {cvj : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_lookups_model pers vis st rf2 t lps i
      cvj = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absIConstantVal r.2))
      pers lst o
      (checkProjLookupsModelSpec lf2 (absNIdx t) (absNIdxL lps) (absU i)
        (absIConstantVal cvj)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_lookups_model_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.U64}
    {cvj : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absIConstantVal r.2)) a) (arena.inductives.modeled.check_proj_lookups_model pers vis st rf2 t lps i cvj) lst
      (checkProjLookupsModelSpec lf2 (absNIdx t) (absNIdxL lps) (absU i)
        (absIConstantVal cvj)) :=
  LS.ofSim₀ fun _ h => check_proj_lookups_model_refines hrel hinv hfe hvis h

/-- `check_proj_lookups` ⊑ `checkProjLookups` — stage 1 of `checkProjFn`: the
stored constants the projection depends on. -/
theorem check_proj_lookups_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {t ctor_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_lookups pers vis st rf2 t ctor_name
      lps n_p n_f i = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absIConstantVal r.2))
      pers lst o
      (checkProjLookups lf2 (absNIdx t) (absNIdx ctor_name) (absNIdxL lps)
        (absU n_p) (absU n_f) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_lookups_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = (fun r => (absIConstantVal r.1, absIConstantVal r.2)) a) (arena.inductives.modeled.check_proj_lookups pers vis st rf2 t ctor_name lps n_p n_f i) lst
      (checkProjLookups lf2 (absNIdx t) (absNIdx ctor_name) (absNIdxL lps)
        (absU n_p) (absU n_f) (absU i)) :=
  LS.ofSim₀ fun _ h => check_proj_lookups_refines hrel hinv hfe hvis h

/-- `check_proj_ty_wf` ⊑ `checkProjTy`'s well-formedness stage. -/
theorem check_proj_ty_wf_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {pty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_ty_wf pers vis st rf2 lps n_p pty
      = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjTyWfSpec lf2 (absNIdxL lps) (absU n_p) (absEIdx pty)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_ty_wf_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {pty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.modeled.check_proj_ty_wf pers vis st rf2 lps n_p pty) lst
      (checkProjTyWfSpec lf2 (absNIdxL lps) (absU n_p) (absEIdx pty)) :=
  LS.ofSim₀ fun _ h => check_proj_ty_wf_refines hrel hinv hfe hvis h

/-- `check_proj_ty` ⊑ `checkProjTy` — stage 2: the public projection type,
pinned by the renaming roundtrip. -/
theorem check_proj_ty_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {t ctor_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {mty : arena.handle.EIdx} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_ty pers vis st rf2 t ctor_name lps
      mty n_p n_f = ok o) :
    Sim₀ absEIdx pers lst o
      (checkProjTy lf2 (absNIdx t) (absNIdx ctor_name) (absNIdxL lps)
        (absEIdx mty) (absU n_p) (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_ty_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {mty : arena.handle.EIdx}
    {n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.modeled.check_proj_ty pers vis st rf2 t ctor_name lps mty n_p n_f) lst
      (checkProjTy lf2 (absNIdx t) (absNIdx ctor_name) (absNIdxL lps)
        (absEIdx mty) (absU n_p) (absU n_f)) :=
  LS.ofSim₀ fun _ h => check_proj_ty_refines hrel hinv hfe hvis h

/-- `check_proj_iota_field` ⊑ `checkProjIota`'s field stage. -/
theorem check_proj_iota_field_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {n_p n_f i : Std.U64}
    {tty sbody rhs_c : arena.handle.EIdx} {lpmn : NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_iota_field pers vis st mode rfS n_p
      n_f i tty sbody rhs_c = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkProjIotaFieldSpec (ConRon.Refine.absMode mode) lfS (absU n_p)
        (absU n_f) (absU i) (absEIdx tty) (absEIdx sbody) (absEIdx rhs_c)
        lpmn) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_iota_field_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {n_p n_f i : Std.U64}
    {tty sbody rhs_c : arena.handle.EIdx}
    {lpmn : NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_proj_iota_field pers vis st mode rfS n_p n_f i tty sbody rhs_c) lst
      (checkProjIotaFieldSpec (ConRon.Refine.absMode mode) lfS (absU n_p)
        (absU n_f) (absU i) (absEIdx tty) (absEIdx sbody) (absEIdx rhs_c)
        lpmn) :=
  LS.ofSim₀ fun _ h => check_proj_iota_field_refines hrel hinv hfe hvis h

/-- `check_proj_iota_lhs` ⊑ `checkProjIota`'s redex stage. -/
theorem check_proj_iota_lhs_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64} {pmn : arena.handle.NIdx}
    {tty sbody : arena.handle.EIdx} {p_args : alloc.vec.Vec arena.handle.EIdx}
    {mk_spine : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_iota_lhs pers vis st mode rfS lps n_p
      n_f i pmn tty sbody p_args mk_spine = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkProjIotaLhsSpec (ConRon.Refine.absMode mode) lfS (absNIdxL lps)
        (absU n_p) (absU n_f) (absU i) (absNIdx pmn) (absEIdx tty)
        (absEIdx sbody) (absEIdxL p_args) (absEIdx mk_spine)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_iota_lhs_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64}
    {pmn : arena.handle.NIdx}
    {tty sbody : arena.handle.EIdx}
    {p_args : alloc.vec.Vec arena.handle.EIdx}
    {mk_spine : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_proj_iota_lhs pers vis st mode rfS lps n_p n_f i pmn tty sbody p_args mk_spine) lst
      (checkProjIotaLhsSpec (ConRon.Refine.absMode mode) lfS (absNIdxL lps)
        (absU n_p) (absU n_f) (absU i) (absNIdx pmn) (absEIdx tty)
        (absEIdx sbody) (absEIdxL p_args) (absEIdx mk_spine)) :=
  LS.ofSim₀ fun _ h => check_proj_iota_lhs_refines hrel hinv hfe hvis h

/-- `check_proj_iota_body` ⊑ `checkProjIota`'s body stage. -/
theorem check_proj_iota_body_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64} {pmn : arena.handle.NIdx}
    {tty sbody : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_iota_body pers vis st mode rfS
      ctor_name lps cvj n_p n_f i pmn tty sbody = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkProjIotaBodySpec (ConRon.Refine.absMode mode) lfS (absNIdx ctor_name)
        (absNIdxL lps) (absIConstantVal cvj) (absU n_p) (absU n_f) (absU i)
        (absNIdx pmn) (absEIdx tty) (absEIdx sbody)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_iota_body_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64}
    {pmn : arena.handle.NIdx}
    {tty sbody : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_proj_iota_body pers vis st mode rfS ctor_name lps cvj n_p n_f i pmn tty sbody) lst
      (checkProjIotaBodySpec (ConRon.Refine.absMode mode) lfS (absNIdx ctor_name)
        (absNIdxL lps) (absIConstantVal cvj) (absU n_p) (absU n_f) (absU i)
        (absNIdx pmn) (absEIdx tty) (absEIdx sbody)) :=
  LS.ofSim₀ fun _ h => check_proj_iota_body_refines hrel hinv hfe hvis h

/-- `check_proj_iota_doms` ⊑ `checkProjIota`'s domain stage. -/
theorem check_proj_iota_doms_refines {pers st lst} {vis : Std.U64} {rfS lfS}
    {mode : kernel.env.CheckMode} {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64} {pmn : arena.handle.NIdx} {tty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow)
    (hrun : arena.inductives.modeled.check_proj_iota_doms pers vis st mode rfS t
      ctor_name lps cvj n_p n_f i pmn tty = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkProjIotaDomsSpec (ConRon.Refine.absMode mode) lfS (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absIConstantVal cvj) (absU n_p)
        (absU n_f) (absU i) (absNIdx pmn) (absEIdx tty)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_iota_doms_ls
    {pers st lst}
    {vis : Std.U64}
    {rfS lfS}
    {mode : kernel.env.CheckMode}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64}
    {pmn : arena.handle.NIdx}
    {tty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfS lfS)
    (hvis : absU vis = lfS.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_proj_iota_doms pers vis st mode rfS t ctor_name lps cvj n_p n_f i pmn tty) lst
      (checkProjIotaDomsSpec (ConRon.Refine.absMode mode) lfS (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absIConstantVal cvj) (absU n_p)
        (absU n_f) (absU i) (absNIdx pmn) (absEIdx tty)) :=
  LS.ofSim₀ fun _ h => check_proj_iota_doms_refines hrel hinv hfe hvis h

/-- `check_proj_iota` ⊑ `checkProjIota` — stage 4: the model's
`proj_i.iota` theorem pins the rule. -/
theorem check_proj_iota_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {rfS lfS} {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS)
    (hrun : arena.inductives.modeled.check_proj_iota pers st mode rf2 rfS t ctor_name
      lps cvj n_p n_f i = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkProjIota (ConRon.Refine.absMode mode) lf2 lfS (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absIConstantVal cvj) (absU n_p)
        (absU n_f) (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_iota_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {rfS lfS}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe2 : IFEnvRelI rf2 lf2)
    (hfeS : IFEnvRelI rfS lfS) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.modeled.check_proj_iota pers st mode rf2 rfS t ctor_name lps cvj n_p n_f i) lst
      (checkProjIota (ConRon.Refine.absMode mode) lf2 lfS (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absIConstantVal cvj) (absU n_p)
        (absU n_f) (absU i)) :=
  LS.ofSim₀ fun _ h => check_proj_iota_refines hrel hinv hfe2 hfeS h

/-- `check_proj_fn_rule` ⊑ `checkProjFn`'s rule-and-install stage. -/
theorem check_proj_fn_rule_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64} {pty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hrun : arena.inductives.modeled.check_proj_fn_rule pers st mode rf2 t ctor_name
      lps cvj n_p n_f i pty = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkProjFnRuleSpec (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absIConstantVal cvj) (absU n_p)
        (absU n_f) (absU i) (absEIdx pty)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_proj_fn_rule_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f i : Std.U64}
    {pty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) :
    LS pers IFEnvRelI (arena.inductives.modeled.check_proj_fn_rule pers st mode rf2 t ctor_name lps cvj n_p n_f i pty) lst
      (checkProjFnRuleSpec (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absIConstantVal cvj) (absU n_p)
        (absU n_f) (absU i) (absEIdx pty)) :=
  LS.ofSimRel₀ fun _ h => check_proj_fn_rule_refines hrel hinv hfe h

/-- `check_proj_fn` ⊑ `checkProjFn` — the public projection function for field
`i`, stored as a degenerate recursor carrying one rule. -/
theorem check_proj_fn_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf2 lf2} {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hrun : arena.inductives.modeled.check_proj_fn pers st mode rf2 t ctor_name lps
      n_p n_f i = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkProjFn (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) (absU i)) := by
  -- lockstep trial
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.inductives.modeled.check_proj_fn, checkProjFn]
  lockstep

open Lockstep in
@[lockstep] theorem check_proj_fn_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2) :
    LS pers IFEnvRelI (arena.inductives.modeled.check_proj_fn pers st mode rf2 t ctor_name lps n_p n_f i) lst
      (checkProjFn (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) (absU i)) :=
  LS.ofSimRel₀ fun _ h => check_proj_fn_refines hrel hinv hfe h

/-! ## The capabilities -/

/-- `proj_models_ok` ⊑ `checkEtaThm`'s projection-model pin, from field `j`
on. -/
theorem proj_models_ok_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_f j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.proj_models_ok pers vis st rf2 t lps n_f j
      = ok o) :
    Sim₀ id pers lst o
      (projModelsOkSpec lf2 (absNIdx t) (absNIdxL lps) (absU n_f - absU j)
        (absU j)) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_models_ok_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_f j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.proj_models_ok pers vis st rf2 t lps n_f j) lst
      (projModelsOkSpec lf2 (absNIdx t) (absNIdxL lps) (absU n_f - absU j)
        (absU j)) :=
  LS.ofSim₀ fun _ h => proj_models_ok_refines hrel hinv hfe hvis h

/-- `eta_proj_args` ⊑ `checkEtaThm`'s `(List.range nF).mapM`, from field `j`
on, with the accumulated arguments in front. -/
theorem eta_proj_args_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ps_hi : alloc.vec.Vec arena.handle.EIdx} {b0 : arena.handle.EIdx}
    {n_f j : Std.U64} {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.eta_proj_args pers st t lps ps_hi b0 n_f j out
      = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← etaProjArgsSpec (absNIdx t) (absNIdxL lps) (absEIdxL ps_hi)
          (absEIdx b0) (absU n_f - absU j) (absU j)))) := by
  sorry

open Lockstep in
@[lockstep] theorem eta_proj_args_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {ps_hi : alloc.vec.Vec arena.handle.EIdx}
    {b0 : arena.handle.EIdx}
    {n_f j : Std.U64}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.modeled.eta_proj_args pers st t lps ps_hi b0 n_f j out) lst
      (do pure (absEIdxL out ++
        (← etaProjArgsSpec (absNIdx t) (absNIdxL lps) (absEIdxL ps_hi)
          (absEIdx b0) (absU n_f - absU j) (absU j)))) :=
  LS.ofSim₀ fun _ h => eta_proj_args_refines hrel hinv h

/-- `check_eta_thm_eq` ⊑ `checkEtaThm`'s equation stage. -/
theorem check_eta_thm_eq_refines {pers st lst} {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_f : Std.U64} {cm : arena.handle.NIdx}
    {sbody tbody_m : arena.handle.EIdx}
    {ps_hi : alloc.vec.Vec arena.handle.EIdx} {fam_hi : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.check_eta_thm_eq pers st mode t lps n_f cm sbody
      tbody_m ps_hi fam_hi = ok o) :
    Sim₀ id pers lst o
      (checkEtaThmEqSpec (ConRon.Refine.absMode mode) (absNIdx t) (absNIdxL lps)
        (absU n_f) (absNIdx cm) (absEIdx sbody) (absEIdx tbody_m)
        (absEIdxL ps_hi) (absEIdx fam_hi)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_eta_thm_eq_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_f : Std.U64}
    {cm : arena.handle.NIdx}
    {sbody tbody_m : arena.handle.EIdx}
    {ps_hi : alloc.vec.Vec arena.handle.EIdx}
    {fam_hi : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_eta_thm_eq pers st mode t lps n_f cm sbody tbody_m ps_hi fam_hi) lst
      (checkEtaThmEqSpec (ConRon.Refine.absMode mode) (absNIdx t) (absNIdxL lps)
        (absU n_f) (absNIdx cm) (absEIdx sbody) (absEIdx tbody_m)
        (absEIdxL ps_hi) (absEIdx fam_hi)) :=
  LS.ofSim₀ fun _ h => check_eta_thm_eq_refines hrel hinv h

/-- `check_eta_thm_body` ⊑ `checkEtaThm`'s subject-binder stage. -/
theorem check_eta_thm_body_refines {pers st lst} {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {t_hd : arena.handle.EIdx} {cm : arena.handle.NIdx}
    {sbinders : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {sbody tbody_m : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.check_eta_thm_body pers st mode t lps n_p n_f
      t_hd cm sbinders sbody tbody_m = ok o) :
    Sim₀ id pers lst o
      (checkEtaThmBodySpec (ConRon.Refine.absMode mode) (absNIdx t) (absNIdxL lps)
        (absU n_p) (absU n_f) (absEIdx t_hd) (absNIdx cm) (absBinderL sbinders)
        (absEIdx sbody) (absEIdx tbody_m)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_eta_thm_body_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {t_hd : arena.handle.EIdx}
    {cm : arena.handle.NIdx}
    {sbinders : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {sbody tbody_m : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_eta_thm_body pers st mode t lps n_p n_f t_hd cm sbinders sbody tbody_m) lst
      (checkEtaThmBodySpec (ConRon.Refine.absMode mode) (absNIdx t) (absNIdxL lps)
        (absU n_p) (absU n_f) (absEIdx t_hd) (absNIdx cm) (absBinderL sbinders)
        (absEIdx sbody) (absEIdx tbody_m)) :=
  LS.ofSim₀ fun _ h => check_eta_thm_body_refines hrel hinv h

/-- `check_eta_thm_shape` ⊑ `checkEtaThm`'s shape stage. -/
theorem check_eta_thm_shape_refines {pers st lst} {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {tm cm : arena.handle.NIdx}
    {tty mtty : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.check_eta_thm_shape pers st mode t lps n_p n_f
      tm cm tty mtty = ok o) :
    Sim₀ id pers lst o
      (checkEtaThmShapeSpec (ConRon.Refine.absMode mode) (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_f) (absNIdx tm) (absNIdx cm)
        (absEIdx tty) (absEIdx mtty)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_eta_thm_shape_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {tm cm : arena.handle.NIdx}
    {tty mtty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_eta_thm_shape pers st mode t lps n_p n_f tm cm tty mtty) lst
      (checkEtaThmShapeSpec (ConRon.Refine.absMode mode) (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_f) (absNIdx tm) (absNIdx cm)
        (absEIdx tty) (absEIdx mtty)) :=
  LS.ofSim₀ fun _ h => check_eta_thm_shape_refines hrel hinv h

/-- `check_eta_thm_at` ⊑ `checkEtaThm`'s pin stage. -/
theorem check_eta_thm_at_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {mode : kernel.env.CheckMode} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f : Std.U64}
    {tm cm : arena.handle.NIdx} {tcv cvm_t cvm_c : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_eta_thm_at pers vis st mode rf2 t lps n_p
      n_f tm cm tcv cvm_t cvm_c = ok o) :
    Sim₀ id pers lst o
      (checkEtaThmAtSpec (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_f) (absNIdx tm) (absNIdx cm)
        (absIConstantVal tcv) (absIConstantVal cvm_t)
        (absIConstantVal cvm_c)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_eta_thm_at_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {tm cm : arena.handle.NIdx}
    {tcv cvm_t cvm_c : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_eta_thm_at pers vis st mode rf2 t lps n_p n_f tm cm tcv cvm_t cvm_c) lst
      (checkEtaThmAtSpec (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdxL lps) (absU n_p) (absU n_f) (absNIdx tm) (absNIdx cm)
        (absIConstantVal tcv) (absIConstantVal cvm_t)
        (absIConstantVal cvm_c)) :=
  LS.ofSim₀ fun _ h => check_eta_thm_at_refines hrel hinv hfe hvis h

/-- `check_eta_thm` ⊑ `checkEtaThm` — does the model document structural eta
for this single-constructor block? -/
theorem check_eta_thm_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {mode : kernel.env.CheckMode} {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_eta_thm pers vis st mode rf2 t ctor_name
      lps n_p n_f = ok o) :
    Sim₀ id pers lst o
      (checkEtaThm (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_eta_thm_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_eta_thm pers vis st mode rf2 t ctor_name lps n_p n_f) lst
      (checkEtaThm (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f)) :=
  LS.ofSim₀ fun _ h => check_eta_thm_refines hrel hinv hfe hvis h

/-- `fam_at` ⊑ `mkAppN tHd (← structPsAt o nP)` — the model family at an
offset, which the twin writes out at three. -/
theorem fam_at_refines {pers st lst} {t_hd : arena.handle.EIdx}
    {ofs n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.fam_at pers st t_hd ofs n_p = ok o) :
    Sim₀ absEIdx pers lst o
      (famAtSpec (absEIdx t_hd) (absU ofs) (absU n_p)) := by
  sorry

open Lockstep in
@[lockstep] theorem fam_at_ls
    {pers st lst}
    {t_hd : arena.handle.EIdx}
    {ofs n_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.inductives.modeled.fam_at pers st t_hd ofs n_p) lst
      (famAtSpec (absEIdx t_hd) (absU ofs) (absU n_p)) :=
  LS.ofSim₀ fun _ h => fam_at_refines hrel hinv h

/-- `check_unit_thm_eq` ⊑ `checkUnitThm`'s equation stage. -/
theorem check_unit_thm_eq_refines {pers st lst} {mode : kernel.env.CheckMode}
    {sbody tbody_m fam2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.check_unit_thm_eq pers st mode sbody tbody_m
      fam2 = ok o) :
    Sim₀ id pers lst o
      (checkUnitThmEqSpec (ConRon.Refine.absMode mode) (absEIdx sbody)
        (absEIdx tbody_m) (absEIdx fam2)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_unit_thm_eq_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {sbody tbody_m fam2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_unit_thm_eq pers st mode sbody tbody_m fam2) lst
      (checkUnitThmEqSpec (ConRon.Refine.absMode mode) (absEIdx sbody)
        (absEIdx tbody_m) (absEIdx fam2)) :=
  LS.ofSim₀ fun _ h => check_unit_thm_eq_refines hrel hinv h

/-- `check_unit_thm_shape` ⊑ `checkUnitThm`'s shape stage. -/
theorem check_unit_thm_shape_refines {pers st lst} {mode : kernel.env.CheckMode}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {tm : arena.handle.NIdx}
    {sbinders : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {sbody tbody_m : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.check_unit_thm_shape pers st mode lps n_p tm
      sbinders sbody tbody_m = ok o) :
    Sim₀ id pers lst o
      (checkUnitThmShapeSpec (ConRon.Refine.absMode mode) (absNIdxL lps)
        (absU n_p) (absNIdx tm) (absBinderL sbinders) (absEIdx sbody)
        (absEIdx tbody_m)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_unit_thm_shape_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {tm : arena.handle.NIdx}
    {sbinders : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {sbody tbody_m : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_unit_thm_shape pers st mode lps n_p tm sbinders sbody tbody_m) lst
      (checkUnitThmShapeSpec (ConRon.Refine.absMode mode) (absNIdxL lps)
        (absU n_p) (absNIdx tm) (absBinderL sbinders) (absEIdx sbody)
        (absEIdx tbody_m)) :=
  LS.ofSim₀ fun _ h => check_unit_thm_shape_refines hrel hinv h

/-- `check_unit_thm_at` ⊑ `checkUnitThm`'s pin stage. -/
theorem check_unit_thm_at_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {mode : kernel.env.CheckMode} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64} {tm : arena.handle.NIdx} {tty : arena.handle.EIdx}
    {tlps : alloc.vec.Vec arena.handle.NIdx} {mtty : arena.handle.EIdx}
    {mlps : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_unit_thm_at pers vis st mode rf2 lps n_p
      tm tty tlps mtty mlps = ok o) :
    Sim₀ id pers lst o
      (checkUnitThmAtSpec (ConRon.Refine.absMode mode) lf2 (absNIdxL lps)
        (absU n_p) (absNIdx tm) (absEIdx tty) (absNIdxL tlps) (absEIdx mtty)
        (absNIdxL mlps)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_unit_thm_at_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {tm : arena.handle.NIdx}
    {tty : arena.handle.EIdx}
    {tlps : alloc.vec.Vec arena.handle.NIdx}
    {mtty : arena.handle.EIdx}
    {mlps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_unit_thm_at pers vis st mode rf2 lps n_p tm tty tlps mtty mlps) lst
      (checkUnitThmAtSpec (ConRon.Refine.absMode mode) lf2 (absNIdxL lps)
        (absU n_p) (absNIdx tm) (absEIdx tty) (absNIdxL tlps) (absEIdx mtty)
        (absNIdxL mlps)) :=
  LS.ofSim₀ fun _ h => check_unit_thm_at_refines hrel hinv hfe hvis h

/-- `check_unit_thm` ⊑ `checkUnitThm` — does the model document unit-likeness
for this block? -/
theorem check_unit_thm_refines {pers st lst} {vis : Std.U64} {rf2 lf2}
    {mode : kernel.env.CheckMode} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.check_unit_thm pers vis st mode rf2 t lps n_p
      = ok o) :
    Sim₀ id pers lst o
      (checkUnitThm (ConRon.Refine.absMode mode) lf2 (absNIdx t) (absNIdxL lps)
        (absU n_p)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_unit_thm_ls
    {pers st lst}
    {vis : Std.U64}
    {rf2 lf2}
    {mode : kernel.env.CheckMode}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.check_unit_thm pers vis st mode rf2 t lps n_p) lst
      (checkUnitThm (ConRon.Refine.absMode mode) lf2 (absNIdx t) (absNIdxL lps)
        (absU n_p)) :=
  LS.ofSim₀ fun _ h => check_unit_thm_refines hrel hinv hfe hvis h

/-- `ctor_targets_fam` ⊑ `ctorTargetsFam` — official's structure-likeness,
read off the block's own constructor. -/
theorem ctor_targets_fam_refines {pers st lst} {ctor_ty : arena.handle.EIdx}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.modeled.ctor_targets_fam pers st ctor_ty t lps n_p n_f
      = ok o) :
    Sim₀ id pers lst o
      (ctorTargetsFam (absEIdx ctor_ty) (absNIdx t) (absNIdxL lps) (absU n_p)
        (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem ctor_targets_fam_ls
    {pers st lst}
    {ctor_ty : arena.handle.EIdx}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.ctor_targets_fam pers st ctor_ty t lps n_p n_f) lst
      (ctorTargetsFam (absEIdx ctor_ty) (absNIdx t) (absNIdxL lps) (absU n_p)
        (absU n_f)) :=
  LS.ofSim₀ fun _ h => ctor_targets_fam_refines hrel hinv h

/-- `install_proj_fn_step` ⊑ `installProjFnStep` — one projection-function
install step, skipped where the model's artifact is absent. -/
theorem install_proj_fn_step_refines {pers st lst} {mode : kernel.env.CheckMode}
    {t ctor_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {re le} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI re le)
    (hrun : arena.inductives.modeled.install_proj_fn_step pers st mode t ctor_name
      lps n_p n_f re i = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (installProjFnStep (ConRon.Refine.absMode mode) (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) le
        (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem install_proj_fn_step_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {re le}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI re le) :
    LS pers IFEnvRelI (arena.inductives.modeled.install_proj_fn_step pers st mode t ctor_name lps n_p n_f re i) lst
      (installProjFnStep (ConRon.Refine.absMode mode) (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) le
        (absU i)) :=
  LS.ofSimRel₀ fun _ h => install_proj_fn_step_refines hrel hinv hfe h

/-- `install_proj_fns` ⊑ `installProjFns` — the projection fold. -/
theorem install_proj_fns_refines {pers st lst} {mode : kernel.env.CheckMode}
    {t ctor_name : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {rf lf} {k i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.modeled.install_proj_fns pers st mode t ctor_name lps
      n_p n_f rf k i = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (installProjFns (ConRon.Refine.absMode mode) (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) lf (absU k)
        (absU i)) := by
  sorry

open Lockstep in
@[lockstep] theorem install_proj_fns_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {rf lf}
    {k i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.inductives.modeled.install_proj_fns pers st mode t ctor_name lps n_p n_f rf k i) lst
      (installProjFns (ConRon.Refine.absMode mode) (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) lf (absU k)
        (absU i)) :=
  LS.ofSimRel₀ fun _ h => install_proj_fns_refines hrel hinv hfe h

/-- `ind_block_caps` ⊑ `indBlockCaps` — the capabilities recorded for a
single-constructor modeled block.  **`checkEtaThm` runs whatever the
level-parameter test says**: Lean lifts the `(← …)` out of the `&&`, so a
short-circuiting port would leave the store several names behind the twin's,
and the port does not short-circuit either. -/
theorem ind_block_caps_refines {pers st lst} {vis : Std.U64}
    {mode : kernel.env.CheckMode} {rf lf}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.inductives.modeled.ind_block_caps pers vis st mode rf cv_t cv_c n_p
      n_f = ok o) :
    Sim₀ absIIndCaps pers lst o
      (indBlockCaps (ConRon.Refine.absMode mode) lf (absIConstantVal cv_t)
        (absIConstantVal cv_c) (absU n_p) (absU n_f)) := by
  sorry

open Lockstep in
@[lockstep] theorem ind_block_caps_ls
    {pers st lst}
    {vis : Std.U64}
    {mode : kernel.env.CheckMode}
    {rf lf}
    {cv_t cv_c : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absIIndCaps a) (arena.inductives.modeled.ind_block_caps pers vis st mode rf cv_t cv_c n_p n_f) lst
      (indBlockCaps (ConRon.Refine.absMode mode) lf (absIConstantVal cv_t)
        (absIConstantVal cv_c) (absU n_p) (absU n_f)) :=
  LS.ofSim₀ fun _ h => ind_block_caps_refines hrel hinv hfe hvis h

/-- `ctor_residual_ok` ⊑ `ctorResidualOk` — con-leche's task #136: an
eta-capable family's constructor returns the family applied to its
parameters. -/
theorem ctor_residual_ok_refines {pers st lst} {vis : Std.U64}
    {mode : kernel.env.CheckMode} {rf2 lf2} {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_f : Std.U64} {eta : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow)
    (hrun : arena.inductives.modeled.ctor_residual_ok pers vis st mode rf2 t
      ctor_name lps n_p n_f eta = ok o) :
    Sim₀ id pers lst o
      (ctorResidualOk (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) eta) := by
  sorry

open Lockstep in
@[lockstep] theorem ctor_residual_ok_ls
    {pers st lst}
    {vis : Std.U64}
    {mode : kernel.env.CheckMode}
    {rf2 lf2}
    {t ctor_name : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {eta : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf2 lf2)
    (hvis : absU vis = lf2.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.ctor_residual_ok pers vis st mode rf2 t ctor_name lps n_p n_f eta) lst
      (ctorResidualOk (ConRon.Refine.absMode mode) lf2 (absNIdx t)
        (absNIdx ctor_name) (absNIdxL lps) (absU n_p) (absU n_f) eta) :=
  LS.ofSim₀ fun _ h => ctor_residual_ok_refines hrel hinv hfe hvis h

/-! ## The install -/

/-- `filter_recs` ⊑ `block.filter isRecInfo` (and its complement) from the
cursor on, with the accumulated members in front. -/
theorem filter_recs_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {want : Bool} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrun : arena.inductives.modeled.filter_recs block want i out = ok o) :
    absICIL o = absICIL out ++ filterRecsSpec (absICILFrom block i) want := by
  simp only [absICIL, absICILFrom, filterRecsSpec]
  refine cursor_induction (fun i : Std.Usize => i.val) block.val.length
    (fun i out => ∀ o, arena.inductives.modeled.filter_recs block want i out = ok o →
      o.val.map absIConstantInfo = out.val.map absIConstantInfo ++
        ((block.val.drop i.val).map absIConstantInfo).filter
          (fun ci => isRecInfo ci == want))
    ?_ ?_ i out o hrun
  · intro i out hn o h
    rw [arena.inductives.modeled.filter_recs.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le hn]
    simp
  · intro i out hi ih o h
    rw [arena.inductives.modeled.filter_recs.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hqb, hqv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hii)
    have hbv : b = isRecInfo (absIConstantInfo ii) := is_rec_info_abs hb
    rw [List.drop_eq_getElem_cons hqb, hqv, List.map_cons, List.filter_cons]
    by_cases hw : b = want
    · rw [if_pos hw] at h
      obtain ⟨ii1, hii1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out1 hi2v o h, hi2v, if_pos (by rw [← hbv, hw]; simp),
        ConRon.Refine.vec_push_val hout1]
      simp [i_constant_info_dup_abs hii1]
    · rw [if_neg hw] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out hi2v o h, hi2v, if_neg (by rw [← hbv]; simpa using hw)]

open Lockstep in
@[lockstep] theorem filter_recs_twin
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {want : Bool}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} :
    LSP (arena.inductives.modeled.filter_recs block want i out) (fun o => TwinEq (absICIL out ++ filterRecsSpec (absICILFrom block i) want) (absICIL o)) :=
  fun o h => (filter_recs_refines h).symm

/-- `block_names_of` ⊑ `block.map (·.name)` from the cursor on. -/
theorem block_names_of_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.inductives.modeled.block_names_of block i out = ok o) :
    absNIdxL o = absNIdxL out ++ blockNamesOfSpec (absICILFrom block i) := by
  simp only [absNIdxL, absICILFrom, blockNamesOfSpec, List.map_map,
    Function.comp_def]
  refine vec_cursor_copy block absNIdx _
    (arena.inductives.modeled.block_names_of block) ?_ ?_ i out o hrun
  · intro i out o hn h
    rw [arena.inductives.modeled.block_names_of.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < block.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.modeled.block_names_of.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hix : ii = x := by
      have h1 := vec_index_some hii; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hix
    exact ⟨i2, n, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      i_constant_info_name_abs hn, h⟩

open Lockstep in
@[lockstep] theorem block_names_of_twin
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.NIdx} :
    LSP (arena.inductives.modeled.block_names_of block i out) (fun o => TwinEq (absNIdxL out ++ blockNamesOfSpec (absICILFrom block i)) (absNIdxL o)) :=
  fun o h => (block_names_of_refines h).symm

/-- `filter_kind` ⊑ the twin's two constructor filters, at a tag. -/
theorem filter_kind_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {kind : Std.U64} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrun : arena.inductives.modeled.filter_kind block kind i out = ok o) :
    absICIL o = absICIL out ++ filterKindSpec (absICILFrom block i) (absU kind) := by
  simp only [absICIL, absICILFrom, filterKindSpec]
  refine cursor_induction (fun i : Std.Usize => i.val) block.val.length
    (fun i out => ∀ o,
      arena.inductives.modeled.filter_kind block kind i out = ok o →
      o.val.map absIConstantInfo = out.val.map absIConstantInfo ++
        ((block.val.drop i.val).map absIConstantInfo).filter
          (fun ci => match ci with
            | .indInfo _ _ => absU kind == 0
            | .ctorInfo _ _ _ => absU kind == 1
            | _ => false))
    ?_ ?_ i out o hrun
  · intro i out hn o h
    rw [arena.inductives.modeled.filter_kind.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le hn]
    simp
  · intro i out hi ih o h
    rw [arena.inductives.modeled.filter_kind.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hit, hhit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hqb, hqv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hii)
    have hk0 : (decide (kind = 0#u64)) = (absU kind == 0) := by
      by_cases hk : kind = 0#u64
      · subst hk; rfl
      · have h2 : ¬ (absU kind = 0) := by
          simp only [absU]; intro hc; exact hk (by scalar_tac)
        simp [hk, h2]
    have hk1 : (decide (kind = 1#u64)) = (absU kind == 1) := by
      by_cases hk : kind = 1#u64
      · subst hk; rfl
      · have h2 : ¬ (absU kind = 1) := by
          simp only [absU]; intro hc; exact hk (by scalar_tac)
        simp [hk, h2]
    have hhitv : hit = (match absIConstantInfo ii with
        | .indInfo _ _ => absU kind == 0
        | .ctorInfo _ _ _ => absU kind == 1
        | _ => false) := by
      cases ii <;> simp only [] at hhit <;> rw [← Result.ok_injective hhit] <;>
        simp only [absIConstantInfo, hk0, hk1]
    rw [List.drop_eq_getElem_cons hqb, hqv, List.map_cons, List.filter_cons, ← hhitv]
    cases hb : hit
    · rw [hb] at h hhitv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out hi2v o h, hi2v]
      simp
    · rw [hb] at h hhitv
      rw [if_pos (by simp)] at h
      obtain ⟨ii1, hii1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 out1 hi2v o h, hi2v, ConRon.Refine.vec_push_val hout1]
      simp [i_constant_info_dup_abs hii1]

open Lockstep in
@[lockstep] theorem filter_kind_twin
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {kind : Std.U64}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} :
    LSP (arena.inductives.modeled.filter_kind block kind i out) (fun o => TwinEq (absICIL out ++ filterKindSpec (absICILFrom block i) (absU kind)) (absICIL o)) :=
  fun o h => (filter_kind_refines h).symm

/-- `single_ind_ctor` ⊑ the twin's two-list match
`[.indInfo cvT _], [.ctorInfo cvC nP nF]`. -/
theorem single_ind_ctor_refines {block : alloc.vec.Vec arena.env.IConstantInfo}
    {o} (hrun : arena.inductives.modeled.single_ind_ctor block = ok o) :
    (o.map fun q => (absIConstantVal q.1, absIConstantVal q.2.1, absU q.2.2.1,
        absU q.2.2.2))
      = singleIndCtorSpec (absICIL block) := by
  rw [arena.inductives.modeled.single_ind_ctor] at hrun
  obtain ⟨inds, hinds, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨ctors, hctors, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hz : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
  have hi : absICIL inds = filterKindSpec (absICIL block) 0 := by
    have h2 := filter_kind_refines hinds
    simpa [absICIL, absICILFrom, alloc.vec.Vec.new, absU, hz] using h2
  have hc : absICIL ctors = filterKindSpec (absICIL block) 1 := by
    have h2 := filter_kind_refines hctors
    simpa [absICIL, absICILFrom, alloc.vec.Vec.new, absU, hz] using h2
  rw [singleIndCtorSpec, ← hi, ← hc, absICIL, absICIL]
  by_cases hl1 : inds.val.length = 1
  · rw [if_neg (by simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac)] at hrun
    by_cases hl2 : ctors.val.length = 1
    · rw [if_neg (by simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac)] at hrun
      obtain ⟨ii, hii, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨ii1, hii1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl1
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hl2
      have hav : a = ii := by
        have h0 := vec_index_some hii; rw [ha, hz] at h0; simpa using h0
      have hbv : b = ii1 := by
        have h0 := vec_index_some hii1; rw [hb, hz] at h0; simpa using h0
      rw [hav] at ha
      rw [hbv] at hb
      rw [ha, hb, List.map_cons, List.map_nil, List.map_cons, List.map_nil]
      cases ii
      case IndInfo cv_t caps =>
        cases ii1
        case CtorInfo cv_c n_p n_f =>
          obtain ⟨iv, hiv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨iv1, hiv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          rw [← Result.ok_injective hrun]
          simp [absIConstantInfo, i_constant_val_dup_abs hiv,
            i_constant_val_dup_abs hiv1]
        all_goals (rw [← Result.ok_injective hrun]; rfl)
      all_goals (rw [← Result.ok_injective hrun]; rfl)
    · rw [if_pos (by simp only [bne_iff_ne, ne_eq]; intro hcc; exact hl2 (by scalar_tac))]
        at hrun
      rw [← Result.ok_injective hrun]
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl1
      rw [ha]
      rcases hm : ctors.val with _ | ⟨y, ys⟩
      · cases a <;> simp only [List.map_cons, List.map_nil] <;> rfl
      · rcases ys with _ | ⟨y2, ys2⟩
        · exact absurd (by simp [hm]) hl2
        · cases a <;> simp
  · rw [if_pos (by simp only [bne_iff_ne, ne_eq]; intro hcc; exact hl1 (by scalar_tac))]
      at hrun
    rw [← Result.ok_injective hrun]
    rcases hm : inds.val with _ | ⟨x, xs⟩
    · simp only [List.map_cons, List.map_nil]; rfl
    · rcases xs with _ | ⟨x2, xs2⟩
      · exact absurd (by simp [hm]) hl1
      · simp

open Lockstep in
@[lockstep] theorem single_ind_ctor_twin
    {block : alloc.vec.Vec arena.env.IConstantInfo} :
    LSP (arena.inductives.modeled.single_ind_ctor block) (fun o => TwinEq (singleIndCtorSpec (absICIL block)) ((o.map fun q => (absIConstantVal q.1, absIConstantVal q.2.1, absU q.2.2.1, absU q.2.2.2)))) :=
  fun o h => (single_ind_ctor_refines h).symm

/-- `proj_fn_family_free` ⊑ the projection-function name family's freeness
from field `j` on — the same test the direct route's table install makes. -/
theorem proj_fn_family_free_modeled_refines {pers st lst} {vis : Std.U64} {rf lf}
    {t : arena.handle.NIdx} {n_f j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.inductives.modeled.proj_fn_family_free pers vis st rf t n_f j
      = ok o) :
    Sim₀ id pers lst o
      (projFnFamilyFreeSpec lf (absNIdx t) (absU n_f - absU j) (absU j)) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_fn_family_free_modeled_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {t : arena.handle.NIdx}
    {n_f j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.modeled.proj_fn_family_free pers vis st rf t n_f j) lst
      (projFnFamilyFreeSpec lf (absNIdx t) (absU n_f - absU j) (absU j)) :=
  LS.ofSim₀ fun _ h => proj_fn_family_free_modeled_refines hrel hinv hfe hvis h

/-- `check_modeled_projs` ⊑ `checkModeled`'s projection stage. -/
theorem check_modeled_projs_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf3 lf3} {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64}
    {eta : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf3 lf3)
    (hrun : arena.inductives.modeled.check_modeled_projs pers st mode rf3 cv_t cv_c
      n_p n_f eta = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkModeledProjsSpec (ConRon.Refine.absMode mode) lf3
        (absIConstantVal cv_t) (absIConstantVal cv_c) (absU n_p) (absU n_f)
        eta) := by
  -- lockstep trial
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.inductives.modeled.check_modeled_projs, checkModeledProjsSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_modeled_projs_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf3 lf3}
    {cv_t cv_c : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {eta : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf3 lf3) :
    LS pers IFEnvRelI (arena.inductives.modeled.check_modeled_projs pers st mode rf3 cv_t cv_c n_p n_f eta) lst
      (checkModeledProjsSpec (ConRon.Refine.absMode mode) lf3
        (absIConstantVal cv_t) (absIConstantVal cv_c) (absU n_p) (absU n_f)
        eta) :=
  LS.ofSimRel₀ fun _ h => check_modeled_projs_refines hrel hinv hfe h

/-- `check_modeled_struct` ⊑ `checkModeled`'s single-type-former,
single-constructor arm. -/
theorem check_modeled_struct_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {block_names : alloc.vec.Vec arena.handle.NIdx}
    {nonrecs recs : alloc.vec.Vec arena.env.IConstantInfo}
    {cv_t cv_c : arena.env.IConstantVal} {n_p n_f : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.modeled.check_modeled_struct pers st mode rf block_names
      nonrecs recs cv_t cv_c n_p n_f = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkModeledStructSpec (ConRon.Refine.absMode mode) lf
        (absNIdxL block_names) (absICIL nonrecs) (absICIL recs)
        (absIConstantVal cv_t) (absIConstantVal cv_c) (absU n_p)
        (absU n_f)) := by
  -- lockstep trial
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.inductives.modeled.check_modeled_struct, checkModeledStructSpec]
  lockstep

open Lockstep in
@[lockstep] theorem check_modeled_struct_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf lf}
    {block_names : alloc.vec.Vec arena.handle.NIdx}
    {nonrecs recs : alloc.vec.Vec arena.env.IConstantInfo}
    {cv_t cv_c : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.inductives.modeled.check_modeled_struct pers st mode rf block_names nonrecs recs cv_t cv_c n_p n_f) lst
      (checkModeledStructSpec (ConRon.Refine.absMode mode) lf
        (absNIdxL block_names) (absICIL nonrecs) (absICIL recs)
        (absIConstantVal cv_t) (absIConstantVal cv_c) (absU n_p)
        (absU n_f)) :=
  LS.ofSimRel₀ fun _ h => check_modeled_struct_refines hrel hinv hfe h

/-- `check_modeled` ⊑ `checkModeled` — **the modeled route's front door**:
every member is checked against its `_model` counterpart, then stored as a
real inductive-kind constant. -/
theorem check_modeled_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.modeled.check_modeled pers st mode rf block = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkModeled (ConRon.Refine.absMode mode) lf (absICIL block)) := by
  -- lockstep trial
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.inductives.modeled.check_modeled, checkModeled_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem check_modeled_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.inductives.modeled.check_modeled pers st mode rf block) lst
      (checkModeled (ConRon.Refine.absMode mode) lf (absICIL block)) :=
  LS.ofSimRel₀ fun _ h => check_modeled_refines hrel hinv hfe h

/-! ## The axiom census

The eight closed readers of this module read `[propext, Classical.choice,
Quot.sound]` and nothing else — `rename_by_rel` is finding 15's discharge and
is the one every `rename_consts` call site of the tier will cite. -/

/-- info: 'ConRon.Refine2.single_ind_ctor_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms single_ind_ctor_refines

/-- info: 'ConRon.Refine2.rename_by_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rename_by_rel


end ConRon.Refine2
