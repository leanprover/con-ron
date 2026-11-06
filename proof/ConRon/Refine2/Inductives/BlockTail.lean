/-
# `ConRon.Refine2.Inductives.BlockTail` — Theorem 2 for `arena::inductives::block_tail`

**Task #105** (DESIGN.md §8.2, Theorem 2); restated by task #143.
`crates/con-ron-core/src/arena/inductives/block_tail.rs` against
`proof/ConRon/Arena/Inductives/BlockTail.lean`: the uniform route's entry
`check_block` — the distinct names, each member's former reduced to its telescope
(`reduce_member(s)`), the pass (`check_block_pass`, with
`check_block_pass_classes` its inline tail), the checks after it
(`check_block_tail`: index sorts, constructors consed, the generated recursor
stage, the stream's K flags and recursors against the generated ones at the
generated family pushed and popped, `check_block_tail_stream`, the tables'
checks), and the block's install pushed onto the constructors' environment
(`Checker/Install.lean`'s `block_recs`, `block_tables`).

`BlockPass` carries the pass's environment, so it RELATES (`BlockPassRel`:
`IFEnvRelI` on `env1`, the abstraction on every other field) rather than
abstracts.  `check_block_ls` is the tier's export to the checker
(`Refine2/Checker/Top.lean`), stated in `Inductives/Top.lean`'s shape.
-/
import ConRon.Refine2.Inductives.BlockInstall
import ConRon.Refine2.Inductives.GenRecCheck
import ConRon.Refine2.Inductives.StreamRecs
import ConRon.Refine2.Checker.Install

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

open Lockstep

/-- The field kinds of the root frame's outputs, as the twin's lists. -/
def absKindsLLL (v : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
    arena.inductives.positivity.NestFieldKind))) : List (List (List NestFieldKind)) :=
  v.val.map fun ks => ks.val.map fun k => k.val.map absNestFieldKind

/-- The pass's record: the environment related, every other field abstracted. -/
structure BlockPassRel (pers : arena.store.PersTier) (r : arena.inductives.block_tail.BlockPass)
    (q : BlockPass) : Prop where
  env1 : IFEnvRelI pers r.env1 q.env1
  p : q.p = absBlockShape r.p
  kinds : q.kinds = absKindsLLL r.kinds
  params : q.params = absEIdxL r.params
  rd : q.rd = absClassRead r.rd
  cls : q.cls = absTargetMajorL r.cls
  tbl : q.tbl = r.tbl.val.map absNestCtorNf

attribute [local lockstep_inline] arena.inductives.block_tail.check_block_pass_classes

/-- `check_block_pass` ⊑ `checkBlockPass` (`check_block_pass_classes` inline). -/
@[lockstep] theorem check_block_pass_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p0 : arena.inductives.block_shape.BlockShape} {is_rec : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (BlockPassRel pers)
      (arena.inductives.block_tail.check_block_pass pers st mode rf p0 is_rec) lst
      (checkBlockPass (ConRon.Refine.absMode mode) lf (absBlockShape p0) is_rec) := by
  sorry -- T143-STUB

/-- `check_block_rec` ⊑ `checkBlockRec`: the generated recursor stage. -/
@[lockstep] theorem check_block_rec_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p : arena.inductives.block_shape.BlockShape} {nested : Bool}
    {params : alloc.vec.Vec arena.handle.EIdx}
    {tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf}
    {rd : arena.inductives.class_read.ClassRead}
    {ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => IFEnvRelI pers a.1 b.1 ∧ b.2 = absRuleOutL a.2)
      (arena.inductives.block_tail.check_block_rec pers st mode rf p nested params tbl rd ms
        block) lst
      (checkBlockRec (ConRon.Refine.absMode mode) lf (absBlockShape p) nested (absEIdxL params)
        (tbl.val.map absNestCtorNf) (absClassRead rd) (absTargetMajorL ms)
        (block.val.map absIConstantInfo)) := by
  rw [arena.inductives.block_tail.check_block_rec, checkBlockRec]
  exact gen_rec_check_ls hrel hinv hfe _ _ _ _ _ _ _

/-- `check_block_tables` ⊑ `checkBlockTables` from the member cursor on: the
table's checks at every structure-like member. -/
@[lockstep] theorem check_block_tables_ls {pers st lst} {rf lf}
    {p : arena.inductives.block_shape.BlockShape}
    {ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape} {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_tail.check_block_tables pers st p rf ms i) lst
      (checkBlockTables (absBlockShape p) lf ((ms.val.drop i.val).map absMemberShape)) := by
  sorry -- T143-STUB

/-- `check_block_tail_stream` ⊑ the stream's records against the generated
family: the K flags, the generated records pushed TEMPORARILY, the comparison,
the pops.  Its answer is the twin's popped environment. -/
@[lockstep] theorem check_block_tail_stream_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (IFEnvRelI pers)
      (arena.inductives.block_tail.check_block_tail_stream pers st mode p out rf) lst
      (do
        streamKCheck (absBlockShape p) (absBlockShape p).recs (out.val.map absRecOut)
        let infos ← blockRecInfosTF (absBlockShape p) 0 (out.val.map absRecOut)
        let (feG, prevs) := consBlockRecsTemp infos lf []
        flushCaches
        streamRecsCheck (ConRon.Refine.absMode mode) feG (absBlockShape p).recs
          (out.val.map absRecOut)
        let fe₃ := prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feG
        flushCaches
        pure fe₃) := by
  sorry -- T143-STUB

/-- `check_block_tail` ⊑ `checkBlockTail`, at a related pass. -/
@[lockstep] theorem check_block_tail_ls {pers st lst} {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {r : arena.inductives.block_tail.BlockPass} {q : BlockPass}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : BlockPassRel pers r q) :
    LS pers (IFEnvRelI pers)
      (arena.inductives.block_tail.check_block_tail pers st mode block r) lst
      (checkBlockTail (ConRon.Refine.absMode mode) (absICIL block) q) := by
  sorry -- T143-STUB

/-! ## The block's check -/

/-- `declined_at_definition` ⊑ `declinedAtDefinition`. -/
@[lockstep] theorem declined_at_definition_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxL a)
      (arena.inductives.block_tail.declined_at_definition st) st lst declinedAtDefinition := by
  sorry -- T143-STUB

/-- `reduce_member` ⊑ `reduceMember`: a member's former at its telescope. -/
@[lockstep] theorem reduce_member_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (ms : arena.inductives.block_shape.MemberShape) (n_p : Std.U64) :
    LS pers (fun a b => b = absMemberShape a)
      (arena.inductives.block_tail.reduce_member pers st mode rf ms n_p) lst
      (reduceMember (ConRon.Refine.absMode mode) lf (absMemberShape ms) (absU n_p)) := by
  sorry -- T143-STUB

/-- `reduce_members` ⊑ `reduceMembers` from the cursor on, behind the
accumulator. -/
@[lockstep] theorem reduce_members_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (n_p : Std.U64) (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) (i : Std.Usize)
    (out : alloc.vec.Vec arena.inductives.block_shape.MemberShape) :
    LS pers (fun a b => a.val.map absMemberShape = out.val.map absMemberShape ++ b)
      (arena.inductives.block_tail.reduce_members pers st mode rf n_p ms i out) lst
      (reduceMembers (ConRon.Refine.absMode mode) lf (absU n_p)
        ((ms.val.drop i.val).map absMemberShape)) := by
  sorry -- T143-STUB

/-- **`block_tail::check_block` ⊑ `checkBlock`** — a block checked, and its
install pushed onto the constructors' environment. -/
@[lockstep] theorem check_block_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {p0 : arena.inductives.block_shape.BlockShape}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers)
      (arena.inductives.block_tail.check_block pers st mode rf block p0) lst
      (checkBlock (ConRon.Refine.absMode mode) lf (absICIL block) (absBlockShape p0)) := by
  sorry -- T143-STUB

end ConRon.Refine2
