/-
# `ConRon.Refine2.Inductives.BlockTail` — Theorem 2 for `arena::inductives::block_tail`

**Task #105** (DESIGN.md §8.2).  `crates/con-ron-core/src/arena/inductives/block_tail.rs`
against `proof/ConRon/Arena/Inductives/BlockTail.lean`: the uniform route's
entry `check_block` — the distinct names, the pass (`check_block_pass`, with
`check_block_pass_classes` its inline tail), and the install after it
(`check_block_tail`: index sorts, constructors consed, the generated recursor
stage, the recursors consed at their majors, the projection tables).

`BlockPass` carries the pass's environment, so it RELATES
(`BlockPassRel`: `IFEnvRelI` on `env1`, the abstraction on every other
field) rather than abstracts.

`check_block_ls` is the tier's export to the checker (`Refine2/Checker/Top.lean`'s
`check_ind_decl_refines`), stated in `Inductives/Top.lean`'s shape.
-/
import ConRon.Refine2.Inductives.BlockInstall
import ConRon.Refine2.Inductives.GenRecCheck

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

open Lockstep

/-- The pass's record: the environment related, every other field abstracted. -/
structure BlockPassRel (r : arena.inductives.block_tail.BlockPass) (q : BlockPass) : Prop where
  env1 : IFEnvRelI r.env1 q.env1
  cvTas : q.cvTas = absICVL r.cv_tas
  p : q.p = absBlockParts r.p
  ctorsAs : q.ctorsAs = absCtorsLL r.ctors_as
  sortsss : q.sortsss = absLIdxLLL r.sortsss
  kinds : q.kinds = absKindsLLL r.kinds
  nfs : q.nfs = absEIdxLL r.nfs
  params : q.params = absEIdxL r.params
  rd : q.rd = absClassRead r.rd
  cls : q.cls = absTargetMajorL r.cls
  tbl : q.tbl = r.tbl.val.map absNestCtorNf

/-- An `LS` at a weaker answer relation. -/
theorem LS.mono_rel {α β : Type} {pers : arena.store.PersTier} {R R' : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R m lst x) (hR : ∀ a b, R a b → R' a b) :
    LS pers R' m lst x := by
  intro o st' hm
  have h1 := h o st' hm
  cases o with
  | Err e => exact h1
  | Ok a =>
    obtain ⟨b, lst', hx, hR1, h2, h3⟩ := h1
    exact ⟨b, lst', hx, hR _ _ hR1, h2, h3⟩

/-- `check_block_inds` with the pair of abstractions as ONE equation, so the
twin's `let (fe₁, cvTas, p₁) ← …` destructures a known term. -/
@[lockstep high] theorem check_block_inds_pair_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockParts) (is_rec : Bool) :
    LS pers (fun a b => IFEnvRelI a.1 b.1 ∧ b.2 = (absICVL a.2.1, absBlockShape a.2.2))
      (arena.inductives.block_install.check_block_inds pers st mode rf p is_rec) lst
      (checkBlockInds (ConRon.Refine.absMode mode) lf (absBlockParts p) is_rec) :=
  LS.mono_rel (check_block_inds_ls hrel hinv mode hfe p is_rec)
    (fun _ _ h => ⟨h.1, Prod.ext h.2.1 h.2.2⟩)

attribute [local lockstep_inline] arena.inductives.block_tail.check_block_pass_classes

/-- `check_block_pass` ⊑ `checkBlockPass` (`check_block_pass_classes` inline). -/
@[lockstep] theorem check_block_pass_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p0 : arena.inductives.block_parts.BlockParts} {is_rec : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers BlockPassRel
      (arena.inductives.block_tail.check_block_pass pers st mode rf p0 is_rec) lst
      (checkBlockPass (ConRon.Refine.absMode mode) lf (absBlockParts p0) is_rec) := by
  rw [arena.inductives.block_tail.check_block_pass, checkBlockPass]
  lockstep
  exact LS.pure ⟨by assumption, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by simp [absNestState]⟩ ‹_› ‹_›

/-- `check_block_rec` ⊑ `checkBlockRec`: the generated recursor stage. -/
@[lockstep] theorem check_block_rec_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p : arena.inductives.block_parts.BlockParts} {nested : Bool}
    {params : alloc.vec.Vec arena.handle.EIdx}
    {tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf}
    {rd : arena.inductives.class_read.ClassRead}
    {ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {cv_tas : alloc.vec.Vec arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => IFEnvRelI a.1 b.1 ∧ b.2 = absRuleOutL a.2)
      (arena.inductives.block_tail.check_block_rec pers st mode rf p nested params tbl rd ms
        block cv_tas) lst
      (checkBlockRec (ConRon.Refine.absMode mode) lf (absBlockParts p) nested (absEIdxL params)
        (tbl.val.map absNestCtorNf) (absClassRead rd) (absTargetMajorL ms)
        (block.val.map absIConstantInfo) (absICVL cv_tas)) := by
  rw [arena.inductives.block_tail.check_block_rec, checkBlockRec]
  exact gen_rec_check_ls hrel hinv hfe _ _ _ _ _ _ _ _

/-- `check_block_tables` ⊑ `checkBlockTables`, from the cursor on: the three
lists walked side by side. -/
@[lockstep] theorem check_block_tables_ls {pers st lst} {rf lf}
    {p : arena.inductives.block_parts.BlockShape}
    {ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {sortsss : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx))}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block_tables pers st p ctors_as sortsss i rf) lst
      (checkBlockTables (absBlockShape p) ((p.members.val.drop i.val).map absMemberShape)
        ((ctors_as.val.drop i.val).map absCtorsL) ((sortsss.val.drop i.val).map absLIdxLL)
        lf) := by
  sorry

/-- `check_block_tail` ⊑ `checkBlockTail`, at a related pass. -/
@[lockstep] theorem check_block_tail_ls {pers st lst} {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {r : arena.inductives.block_tail.BlockPass} {q : BlockPass}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : BlockPassRel r q) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block_tail pers st mode block r) lst
      (checkBlockTail (ConRon.Refine.absMode mode) (absICIL block) q) := by
  sorry

/-- **`block_tail::check_block` ⊑ `checkBlock`** — the uniform install. -/
@[lockstep] theorem check_block_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {p0 : arena.inductives.block_parts.BlockParts}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block pers st mode rf block p0) lst
      (checkBlock (ConRon.Refine.absMode mode) lf (absICIL block) (absBlockParts p0)) := by
  rw [arena.inductives.block_tail.check_block, checkBlock]
  lockstep
  all_goals
    simp only [TwinEq, absBlockParts_shape, absNIdxL] at *
    try simp only [← ‹(absBlockShape p0.shape).allCtors = _›] at *
    try simp only [‹List.map _ (absCtorsL _) = _›] at *
    try simp only [← ‹(absBlockShape p0.shape).memberNames = _›] at *
    lockstep

end ConRon.Refine2
