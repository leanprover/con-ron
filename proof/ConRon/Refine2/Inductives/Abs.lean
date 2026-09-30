/-
# `ConRon.Refine2.Inductives.Abs` — the uniform route's records, abstracted

**Task #105** (DESIGN.md §8.2, Theorem 2).  The records of
`arena::inductives::{positivity, block_parts, class_read, rec_check, gen_rec}`
against their twins (`Arena/Inductives/*.lean`), field for field.  Every Rust
`Vec` is the twin's `List` (`v.val.map abs`), every `u64` a `Nat` (`absU`).

**Two records RELATE rather than abstract**, and neither needs a semantic
fact:

* `NestCtx` carries `vis : u64`, which the twin's record does not: over the
  twin's `IFEnv` the bound is `fe.visibleBelow` (the twin module note's
  "`vis` dropped" ruling), so `absNestCtx` forgets it and a statement that
  reads it pairs the context with the environment by `absU ctx.vis =
  lf.visibleBelow` — the relation `Refine2/Core/KnotRel.lean` uses for the
  knot's `vis`.
* `NestState.keys`/`ctorNfs` are `Array`s in the twin: `absNestState` builds
  them with `List.toArray`.
-/
import ConRon.Refine2.Inductives.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

open ConRon.Arena

/-! ## `positivity` -/

def absNestKey (k : arena.inductives.positivity.NestKey) : NestKey :=
  ⟨absNIdx k.cname, absLsIdx k.lvls, absEIdxL k.ds⟩

def absNestHole (h : arena.inductives.positivity.NestHole) : NestHole :=
  ⟨absNestKey h.key, absU h.base⟩

def absNestFieldKind : arena.inductives.positivity.NestFieldKind → NestFieldKind
  | .Ordinary => .ordinary
  | .Recursive t => .recursive (absU t)
  | .Reflexive t => .reflexive (absU t)
  | .InProgress => .inProgress
  | .Nested b => .nested b

def absNestCtorNf (e : arena.inductives.positivity.NestCtorNf) : NestCtorNf :=
  ⟨absNIdx e.ctor, absLsIdx e.lvls, absEIdxL e.ds, absEIdx e.ty⟩

/-- `vis` is dropped (module note). -/
def absNestCtx (c : arena.inductives.positivity.NestCtx) : NestCtx :=
  ⟨absNIdxL c.names, absNIdxL c.lps, absU c.n_p, c.n_idxs.val.map absU,
    absEIdxL c.params, absLIdx c.sort, absLsIdx c.lvls⟩

def absNestState (s : arena.inductives.positivity.NestState) : NestState :=
  ⟨(s.keys.val.map absNestKey).toArray, s.active.val.map absNestKey,
    (s.ctor_nfs.val.map absNestCtorNf).toArray⟩

def absFvMap : arena.inductives.positivity.FvMap → FvMap
  | .HoleImg m => .holeImg (absNestCtx m.ctx) (m.prog.val.map absNestHole) (absU m.n)
  | .KeyMap ds holes => .keyMap (absEIdxL ds) (absEIdxL holes)
  | .Erase => .erase
  | .Canon pfvs => .canon (absEIdxL pfvs)

/-! ## `block_parts` -/

def absMemberShape (m : arena.inductives.block_parts.MemberShape) : MemberShape :=
  ⟨absIConstantVal m.cv_t, absU m.n_idx, absCtorsL m.ctors⟩

def absRecShape (r : arena.inductives.block_parts.RecShape) : RecShape :=
  ⟨absIConstantVal r.cv_r, absU r.r_p, absU r.m_i, absU r.tgt, absEIdxL r.rhss⟩

def absBlockShape (p : arena.inductives.block_parts.BlockShape) : BlockShape :=
  ⟨p.members.val.map absMemberShape, p.recs.val.map absRecShape, absU p.n_p,
    absNIdx p.elim, absLIdx p.res_sort, p.large, p.is_prop⟩

def absBlockParts (p : arena.inductives.block_parts.BlockParts) : BlockParts :=
  ⟨absBlockShape p.shape⟩

theorem absBlockShape_members (p : arena.inductives.block_parts.BlockShape) :
    (absBlockShape p).members = p.members.val.map absMemberShape := rfl
theorem absBlockShape_recs (p : arena.inductives.block_parts.BlockShape) :
    (absBlockShape p).recs = p.recs.val.map absRecShape := rfl

/-! ## `class_read` -/

def absClassKey (k : arena.inductives.class_read.ClassKey) : ClassKey :=
  ⟨absNIdx k.ind, absLsIdx k.lvls, absEIdxL k.ds⟩

def absNatPair (p : Std.U64 × Std.U64) : Nat × Nat := (absU p.1, absU p.2)

def absClassSlot : arena.inductives.class_read.ClassSlot → ClassSlot
  | .Motive k => .motive (absClassKey k)
  | .Minor c n ihs => .minor (absU c) (absNIdx n) (ihs.val.map absNatPair)

def absClassRead (r : arena.inductives.class_read.ClassRead) : ClassRead :=
  ⟨r.slots.val.map absClassSlot, r.rec_cls.val.map absU⟩

/-! ## `rec_check` -/

def absTargetMajor (m : arena.inductives.rec_check.TargetMajor) : TargetMajor :=
  { ind := absNIdx m.ind, lvls := absLsIdx m.lvls, ds := absEIdxL m.ds,
    nPc := absU m.n_pc, nIdx := absU m.n_idx, ctors := absCtorsL m.ctors,
    member := m.member.map absU, nfs := m.nfs.val.map absNestCtorNf,
    pfvs := absEIdxL m.pfvs }

/-! ## `gen_rec` -/

def absClassField : arena.inductives.gen_rec.ClassField → ClassField
  | .Ordinary => .ordinary
  | .Recursive c t => .recursive (absU c) (absU t)

def absClassCtor (x : arena.inductives.gen_rec.ClassCtor) : ClassCtor :=
  ⟨absIConstantVal x.cv, absU x.n_f, x.kinds.val.map absClassField, absEIdx x.ty_d,
    absEIdx x.ty_n⟩

def absClassGen (g : arena.inductives.gen_rec.ClassGen) : ClassGen :=
  ⟨absU g.n_p, absEIdxL g.params, g.cls.val.map absTargetMajor, absEIdxL g.former_tys,
    g.slots.val.map absClassSlot, g.ctors.val.map (fun cs => cs.val.map absClassCtor),
    absLIdx g.elim, ConRon.Refine.absBinderMeta g.bm, absBinderL g.pre⟩

end ConRon.Refine2
