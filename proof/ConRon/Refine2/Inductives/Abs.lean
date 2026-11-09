/-
# `ConRon.Refine2.Inductives.Abs` — the uniform route's records, abstracted

**Task #105** (DESIGN.md §8.2, Theorem 2).  The records of
`arena::inductives::{positivity, block_shape, class_read, rec_check, gen_rec}`
against their twins (`Arena/Inductives/*.lean`), field for field.  Every Rust
`Vec` is the twin's `List` (`v.val.map abs`), every `u64` a `Nat` (`absU`).

`NestState.keys`/`ctorNfs` are `Array`s in the twin: `absNestState` builds
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
  ⟨absNestKey h.key, absU h.base, absU h.n_idx⟩

def absNestFieldKind : arena.inductives.positivity.NestFieldKind → NestFieldKind
  | .Ordinary => .ordinary
  | .Recursive t => .recursive (absU t)
  | .Reflexive t => .reflexive (absU t)
  | .InProgress => .inProgress
  | .Nested b => .nested b

def absNestCtorNf (e : arena.inductives.positivity.NestCtorNf) : NestCtorNf :=
  ⟨absNIdx e.ctor, absLsIdx e.lvls, absEIdxL e.ds, absEIdx e.ty⟩

def absNestCtx (c : arena.inductives.positivity.NestCtx) : NestCtx :=
  ⟨absNIdxL c.names, absNIdxL c.lps, absU c.n_p, c.n_idxs.val.map absU,
    absEIdxL c.params, absLIdx c.sort, c.formers.val.map absIConstantVal, absLsIdx c.lvls⟩

def absNestState (s : arena.inductives.positivity.NestState) : NestState :=
  ⟨(s.keys.val.map absNestKey).toArray, s.active.val.map absNestKey,
    (s.ctor_nfs.val.map absNestCtorNf).toArray⟩

def absFvMap : arena.inductives.positivity.FvMap → FvMap
  | .HoleImg m => .holeImg (absNestCtx m.ctx) (m.prog.val.map absNestHole) (absU m.n)
  | .KeyMap ds holes => .keyMap (absEIdxL ds) (absEIdxL holes)
  | .Erase => .erase
  | .Canon pfvs => .canon (absEIdxL pfvs)

/-! ## `block_shape` -/

def absMemberShape (m : arena.inductives.block_shape.MemberShape) : MemberShape :=
  ⟨absIConstantVal m.cv_t, absIConstantVal m.declared, absU m.n_idx, absCtorsL m.ctors⟩

def absRecShape (r : arena.inductives.block_shape.RecShape) : RecShape :=
  ⟨absIConstantVal r.cv_r, absU r.r_p, absU r.m_i, absU r.tgt, r.rules.val.map absIRecRule,
    r.is_k⟩

def absBlockShape (p : arena.inductives.block_shape.BlockShape) : BlockShape :=
  ⟨p.members.val.map absMemberShape, p.recs.val.map absRecShape, absU p.n_p,
    absNIdx p.elim, absLIdx p.res_sort, p.large, p.is_prop⟩

theorem absBlockShape_members (p : arena.inductives.block_shape.BlockShape) :
    (absBlockShape p).members = p.members.val.map absMemberShape := rfl
theorem absBlockShape_recs (p : arena.inductives.block_shape.BlockShape) :
    (absBlockShape p).recs = p.recs.val.map absRecShape := rfl

/-! ## An error as a value

`readBlock` and its readers return the cited `Except` as a VALUE (the Rust's
inner `Result`), beside the arena's own failure.  The value's error is the
port's message abstracted as a string, so the relation is a function of the
Rust value and `lockstep` substitutes it. -/

/-- The port's `CheckError` as the twin's: the kind, the message's code points as
a string. -/
def absACheckError : kernel.core_types.CheckError → Arena.CheckError
  | .NotImplemented m => .notImplemented (ConRon.Refine.absString m)
  | .Invalid m => .invalid (ConRon.Refine.absString m)
  | .Internal m => .internal (ConRon.Refine.absString m)
  | .Native m => .native (ConRon.Refine.absString m)

@[simp, lockstep_simp] theorem lAErrKind_absACheckError (e : kernel.core_types.CheckError) :
    lAErrKind (absACheckError e) = absAErrKind e := by
  cases e <;> rfl

/-- A Rust `Result<T, CheckError>` value as the twin's `Except CheckError`. -/
def absExc {α β : Type} (f : α → β) :
    core.result.Result α kernel.core_types.CheckError → Except Arena.CheckError β
  | .Ok a => .ok (f a)
  | .Err e => .error (absACheckError e)

@[simp, lockstep_simp] theorem absExc_ok {α β : Type} (f : α → β) (a : α) : absExc f (.Ok a) = .ok (f a) := rfl
@[simp, lockstep_simp] theorem absExc_err {α β : Type} (f : α → β) (e : kernel.core_types.CheckError) :
    absExc f (.Err e) = .error (absACheckError e) := rfl

/-- con-leche: none — a message constant's code points, as a string. -/
def msgOf {n : Std.Usize} (M : Array Std.U32 n) : String :=
  String.ofList (M.val.map fun c => Char.ofNat c.val)

/-- A message read off a constant through `code_points` is the constant's string. -/
theorem absString_of_msg {n : Std.Usize} {M : Array Std.U32 n} {v : alloc.vec.Vec Std.U32}
    {s : Slice Std.U32} (hv : v.val = s.val) (hs : s.val = M.val) :
    ConRon.Refine.absString v = msgOf M := by
  simp only [ConRon.Refine.absString, msgOf, hv, hs]

/-! ### The reader's and the reserved names' messages, once -/
theorem msg_M_PARAMS_EXCEED : msgOf arena.inductives.block_shape.M_PARAMS_EXCEED = "inductive type declares more parameters than its type has binders" := by decide +kernel
theorem msg_M_NO_REC_ELIM : msgOf arena.inductives.block_shape.M_NO_REC_ELIM = "no recursor of the block eliminates the inductive type" := by decide +kernel
theorem msg_M_REC_COUNTS : msgOf arena.inductives.block_shape.M_REC_COUNTS = "the argument counts of a recursor do not fit the block" := by decide +kernel
theorem msg_M_ORDER : msgOf arena.inductives.block_shape.M_ORDER = "inductive block: its records are not the inductive types, then the constructors, then the recursors" := by decide +kernel
theorem msg_M_NO_TYPE : msgOf arena.inductives.block_shape.M_NO_TYPE = "inductive block declares no inductive type" := by decide +kernel
theorem msg_M_NO_RECS : msgOf arena.inductives.block_shape.M_NO_RECS = "inductive block carries no recursor records; the input must carry the recursors of every inductive block" := by decide +kernel
theorem msg_M_TYPE_LEVELS : msgOf arena.inductives.block_shape.M_TYPE_LEVELS = "inductive type declares other universe parameters than the block's first type" := by decide +kernel
theorem msg_M_CTOR_PARAMS : msgOf arena.inductives.block_shape.M_CTOR_PARAMS = "constructor declares another parameter count than the block" := by decide +kernel
theorem msg_M_CTOR_LEVELS_ONE : msgOf arena.inductives.block_shape.M_CTOR_LEVELS_ONE = "constructor declares other universe parameters than its type" := by decide +kernel
theorem msg_M_CTOR_LEVELS : msgOf arena.inductives.block_shape.M_CTOR_LEVELS = "constructor declares other universe parameters than the block's inductive types" := by decide +kernel
theorem msg_M_BASIS_NOT_PIN : msgOf arena.basis.M_BASIS_NOT_PIN = "reserved basis name: the block is not the pinned one" := by decide +kernel
theorem msg_M_BASIS_IN_BLOCK : msgOf arena.basis.M_BASIS_IN_BLOCK = "reserved basis name in the block of" := by decide +kernel
theorem msg_M_BASIS_NAME : msgOf arena.basis.M_BASIS_NAME = "reserved basis name" := by decide +kernel

/-- The message equation in the shape an error leaf asks for. -/
theorem msg_eq_absString {n : Std.Usize} {M : Array Std.U32 n} {v : alloc.vec.Vec Std.U32}
    {s : Slice Std.U32} {str : String} (hv : v.val = s.val) (hs : s.val = M.val)
    (h : msgOf M = str) : str = ConRon.Refine.absString v := by
  rw [absString_of_msg hv hs, h]

/-- An error leaf of the reader or the reserved names' check: the Rust's
`Invalid(code_points(&M))`, abstracted, is the twin's `.invalid "…"`. -/
macro "msg_leaf" : tactic => `(tactic| (
  try simp only [ConRon.Refine2.absExc_err, Except.error.injEq]
  exact congrArg ConRon.Arena.CheckError.invalid
    (ConRon.Refine2.msg_eq_absString ‹_› ‹_› (by simp only [ConRon.Refine2.msg_M_PARAMS_EXCEED, ConRon.Refine2.msg_M_NO_REC_ELIM, ConRon.Refine2.msg_M_REC_COUNTS, ConRon.Refine2.msg_M_ORDER, ConRon.Refine2.msg_M_NO_TYPE, ConRon.Refine2.msg_M_NO_RECS, ConRon.Refine2.msg_M_TYPE_LEVELS, ConRon.Refine2.msg_M_CTOR_PARAMS, ConRon.Refine2.msg_M_CTOR_LEVELS_ONE, ConRon.Refine2.msg_M_CTOR_LEVELS, ConRon.Refine2.msg_M_BASIS_NOT_PIN, ConRon.Refine2.msg_M_BASIS_IN_BLOCK, ConRon.Refine2.msg_M_BASIS_NAME]))))

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
    absLIdx g.elim, absBinderL g.pre⟩

end ConRon.Refine2
