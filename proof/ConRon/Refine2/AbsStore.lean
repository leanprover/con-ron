/-
# `ConRon.Refine2.AbsStore` — the Rust arena store as the twin's `EStore`

**Deliverable 1 of task #97 P5, part 1** (DESIGN.md §8.2, Theorem 2).  The
abstraction of `arena::store`'s four nested stores to
`ConRon.Arena.{NStore,LStore,LsStore,EStore}`, and of `arena::store::PersTier`
— the reader parameter — to *nothing*, because the twin's monad does not have
one (task #97-LC §1) and the tier arrives instead as the persistent arm of the
abstract store:

    absStore (pers, st) = { st.store with
      pers := if st.store.shared_on then pers.e else st.store.pers }

which is task #97-LC's own equation, one tier deep in each of the four stores.

## What is a function here and what is a relation

| Rust | twin | abstraction |
|---|---|---|
| `EIdx`/`NIdx`/`LIdx`/`LsIdx`/`BMIdx` = `{word : u32}` | `Idx k` = `{word : UInt32}` | a FUNCTION (`absEIdx`, …) — the same word |
| a node record (`AppNode` = two handles) | the same record over `Idx` | a FUNCTION (`absAppNode`, …) |
| `Tbl.rows : Vec (A × D)` | `Tbl.nodes : Array α` **and** `Tbl.der : Array δ` | a FUNCTION each way (task #97-P6-10 interleaved the two columns; `rows.map (·.1)` and `rows.map (·.2)`) |
| `Tbl.cons : ron::HashMap2<A, I>` | `Tbl.cons : Std.HashMap α ι` | a **RELATION** — `Refine/HashMap2.lean`'s `Rel`, because a `Std.HashMap` is not recoverable from a probe agreement |

So `TblRel` is a relation and everything above it is, exactly as
`RefineOld/State.lean`'s `StateRel` was: this is the shape the 1 894-lemma
tier of the `Expr`-tree checker ran on, and `Refine2/Shape.lean`'s `AOut`
carries the resulting `∃ lst'` the same way `Out` did.

## The capacity invariant round 2 predicted is NOT needed

Task #97s round 2's second unpredicted finding was "both halves need a
capacity invariant: Rust's `n as u32` truncates rather than failing, so the
cons tables' index cast is faithful only below `IDX_CAP`".  **On the real
store it is not needed, and the reason is the two-layer route's own dividend.**
`Tbl::push`'s handle is `Idx::pack(tag, tier, self.rows.len() as u32)`, whose
`as u32` Aeneas models as `UScalar.cast .U32` at value `len % 2 ^ 32`; the
twin writes `Idx.mk tag tier (UInt32.ofNat tb.size)`, and `UInt32.ofNat`
truncates by the SAME modulus.  The two therefore agree unconditionally, and
`arena::handle::word_mk`'s `+`/`*` on `u32` make the hypothesis `= ok`
vacuous where the arithmetic would wrap out of the word.  A handle past
`IDX_CAP` is wrong — it reads as the other tier — but it is *equally* wrong on
both sides, which is all Theorem 2 claims; excluding it is `StoreWF`'s
`capOK` clause and therefore Theorem 1's business (and `Arena/Monad.lean`'s
`internE` tests it, which is how the twin discharges it).  Only the
`HashMap2` invariant survives into `Refine2/Inv.lean`.
-/
import ConRon.Refine2.Idiom
import ConRon.Refine.HashMap2WF
import ConRon.Refine.Expr
import ConRon.Refine.PropWhen
import ConRon.Arena.Store

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## Decidable equality of the generated key types

`Refine/HashMap2.lean`'s `toFun` — and with it `Rel`, which this file is
written in — needs `DecidableEq` on the port's key type.  `Refine/Abs.lean`
supplies the four classical instances the `Expr`-tree checker's key types
needed and its note says why nothing is lost (every occurrence is inside a
`Prop`; the port's own decision procedure is `Eq2::eq2` and is what the
refinement lemmas are about).  The arena's eighteen cons keys are the same
situation, plus the memo keys of `Refine2/AbsState.lean`. -/

noncomputable instance : DecidableEq arena.store.AnonNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.StrNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.NumNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.ZeroNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.SuccNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.BinLNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.ParamNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.ListNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.BVarNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.FVarNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.SortNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.ConstNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.AppNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.BindNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.BMNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.LetNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.LitNode := Classical.decEq _
noncomputable instance : DecidableEq arena.store.ProjNode := Classical.decEq _

/-! ## The handles

DESIGN §8.3: "handles are the same `u32` words".  One function per kind
because the Rust has five distinct one-field structures where the twin has one
generic `Idx k`; each is `absU32` on the word and nothing else. -/

/-- con-leche: none — an expression handle. -/
def absEIdx (i : arena.handle.EIdx) : EIdx := ⟨absU32 i.word⟩
/-- con-leche: none — a name handle. -/
def absNIdx (i : arena.handle.NIdx) : NIdx := ⟨absU32 i.word⟩
/-- con-leche: none — a level handle. -/
def absLIdx (i : arena.handle.LIdx) : LIdx := ⟨absU32 i.word⟩
/-- con-leche: none — a universe-argument-list handle. -/
def absLsIdx (i : arena.handle.LsIdx) : LsIdx := ⟨absU32 i.word⟩
/-- con-leche: none — a binder-datum handle (task #97-P6-16). -/
def absBMIdx (i : arena.handle.BMIdx) : BMIdx := ⟨absU32 i.word⟩

@[simp] theorem absEIdx_word (i) : (absEIdx i).word = absU32 i.word := rfl
@[simp] theorem absNIdx_word (i) : (absNIdx i).word = absU32 i.word := rfl
@[simp] theorem absLIdx_word (i) : (absLIdx i).word = absU32 i.word := rfl
@[simp] theorem absLsIdx_word (i) : (absLsIdx i).word = absU32 i.word := rfl
@[simp] theorem absBMIdx_word (i) : (absBMIdx i).word = absU32 i.word := rfl

theorem absEIdx_inj : Function.Injective absEIdx := by
  intro a b h
  have hw : absU32 a.word = absU32 b.word := by
    simpa using congrArg Idx.word h
  cases a; cases b; simpa using absU32_inj hw

theorem absNIdx_inj : Function.Injective absNIdx := by
  intro a b h
  have hw : absU32 a.word = absU32 b.word := by
    simpa using congrArg Idx.word h
  cases a; cases b; simpa using absU32_inj hw

theorem absLIdx_inj : Function.Injective absLIdx := by
  intro a b h
  have hw : absU32 a.word = absU32 b.word := by
    simpa using congrArg Idx.word h
  cases a; cases b; simpa using absU32_inj hw

theorem absLsIdx_inj : Function.Injective absLsIdx := by
  intro a b h
  have hw : absU32 a.word = absU32 b.word := by
    simpa using congrArg Idx.word h
  cases a; cases b; simpa using absU32_inj hw

theorem absBMIdx_inj : Function.Injective absBMIdx := by
  intro a b h
  have hw : absU32 a.word = absU32 b.word := by
    simpa using congrArg Idx.word h
  cases a; cases b; simpa using absU32_inj hw

/-! ### The word's three fields

`Arena/Handle.lean` and `arena::handle` both write the packing with `*`, `/`
and `%`, so each field reading transfers through `absU32`'s three operation
lemmas.  Stated forward from `= ok`, as everything here is. -/

theorem word_tag_abs {w t : Std.U32} (h : arena.handle.word_tag w = ok t) :
    absU32 w / 268435456 = absU32 t := by
  rw [arena.handle.word_tag, arena.handle.TAG_SPAN] at h
  have hd := absU32_div h
  simpa [absU32] using hd

theorem word_tier_abs {w t : Std.U32} (h : arena.handle.word_tier w = ok t) :
    absU32 w / 134217728 % 2 = absU32 t := by
  rw [arena.handle.word_tier, arena.handle.IDX_CAP] at h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := absU32_div hy
  have h2 := absU32_mod h
  rw [← h2, ← h1]
  simp [absU32]

theorem word_index_abs {w r : Std.U32} (h : arena.handle.word_index w = ok r) :
    absU32 w % 134217728 = absU32 r := by
  rw [arena.handle.word_index, arena.handle.IDX_CAP] at h
  have hm := absU32_mod h
  simpa [absU32] using hm

theorem eidx_tag_abs {i : arena.handle.EIdx} {t : Std.U32}
    (h : arena.handle.EIdx.tag i = ok t) : (absEIdx i).tag = absU32 t := by
  rw [arena.handle.EIdx.tag] at h
  exact word_tag_abs h

theorem nidx_tag_abs {i : arena.handle.NIdx} {t : Std.U32}
    (h : arena.handle.NIdx.tag i = ok t) : (absNIdx i).tag = absU32 t := by
  rw [arena.handle.NIdx.tag] at h
  exact word_tag_abs h

theorem lidx_tag_abs {i : arena.handle.LIdx} {t : Std.U32}
    (h : arena.handle.LIdx.tag i = ok t) : (absLIdx i).tag = absU32 t := by
  rw [arena.handle.LIdx.tag] at h
  exact word_tag_abs h

theorem word_is_persistent_abs {w : Std.U32} {b : Bool}
    (h : arena.handle.word_is_persistent w = ok b) :
    (absU32 w / 134217728 % 2 == 0) = b := by
  rw [arena.handle.word_is_persistent] at h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq] at h
  rw [word_tier_abs hy, ← h]
  by_cases hc : y = 0#u32
  · subst hc; simp [absU32]
  · have hne : absU32 y ≠ 0 := by
      intro hz
      exact hc (absU32_inj (by simpa [absU32] using hz))
    simp [hc, hne]

theorem eidx_is_persistent_abs {i : arena.handle.EIdx} {b : Bool}
    (h : arena.handle.EIdx.is_persistent i = ok b) :
    (absEIdx i).isPersistent = b := by
  rw [arena.handle.EIdx.is_persistent] at h
  have hp := word_is_persistent_abs h
  simpa [Idx.isPersistent, Idx.tier, absEIdx] using hp

/-! ## The node records

One function per constructor array, on both the expression store's ten (plus
the binder-datum store's one) and the name, level and level-list stores'
nine. -/

def absAnonNode (_ : arena.store.AnonNode) : AnonNode := .mk
def absStrNode (r : arena.store.StrNode) : StrNode :=
  ⟨absNIdx r.pre, ConRon.Refine.absString r.s⟩
def absNumNode (r : arena.store.NumNode) : NumNode := ⟨absNIdx r.pre, absU r.n⟩

def absZeroNode (_ : arena.store.ZeroNode) : ZeroNode := .mk
def absSuccNode (r : arena.store.SuccNode) : SuccNode := ⟨absLIdx r.u⟩
def absBinLNode (r : arena.store.BinLNode) : BinLNode := ⟨absLIdx r.u, absLIdx r.v⟩
def absParamNode (r : arena.store.ParamNode) : ParamNode := ⟨absNIdx r.n⟩
def absListNode (r : arena.store.ListNode) : ListNode := ⟨r.us.val.map absLIdx⟩

def absLDer (d : arena.store.LDer) : LDer := ⟨absU64 d.hash, d.has_param⟩

def absBVarNode (r : arena.store.BVarNode) : BVarNode := ⟨absU r.i⟩
def absFVarNode (r : arena.store.FVarNode) : FVarNode := ⟨absU r.idx, absEIdx r.ty⟩
def absSortNode (r : arena.store.SortNode) : SortNode := ⟨absLIdx r.u⟩
def absConstNode (r : arena.store.ConstNode) : ConstNode :=
  ⟨absNIdx r.n, absLsIdx r.us⟩
def absAppNode (r : arena.store.AppNode) : AppNode := ⟨absEIdx r.f, absEIdx r.a⟩
def absBindNode (r : arena.store.BindNode) : BindNode :=
  ⟨absEIdx r.ty, absEIdx r.body, absBMIdx r.m⟩
def absBMNode (r : arena.store.BMNode) : BMNode := ⟨ConRon.Refine.absPropWhen r.pw⟩
def absLetNode (r : arena.store.LetNode) : LetNode :=
  ⟨absEIdx r.ty, absEIdx r.val, absEIdx r.body⟩
def absLitNode (r : arena.store.LitNode) : LitNode := ⟨ConRon.Refine.absLiteral r.l⟩
def absProjNode (r : arena.store.ProjNode) : ProjNode :=
  ⟨absNIdx r.n, absU r.i, absEIdx r.e⟩

/-! ## The four node VIEWS

`view`'s result, and `intern`'s argument.  `LsNodeView` is a `Vec<LIdx>`
against the twin's `List LIdx` (`Arena/Store.lean`'s own note: con-leche's
`Expr.const` carries a `List Level`), so its abstraction is the `Vec`'s list
mapped. -/

def absNNodeView : arena.store.NNodeView → NNodeView
  | .Anonymous => .anonymous
  | .Str p s => .str (absNIdx p) (ConRon.Refine.absString s)
  | .Num p n => .num (absNIdx p) (absU n)

def absLNodeView : arena.store.LNodeView → LNodeView
  | .Zero => .zero
  | .Succ u => .succ (absLIdx u)
  | .Max u v => .max (absLIdx u) (absLIdx v)
  | .Imax u v => .imax (absLIdx u) (absLIdx v)
  | .Param n => .param (absNIdx n)

def absLsNodeView (v : alloc.vec.Vec arena.handle.LIdx) : LsNodeView :=
  v.val.map absLIdx

def absENodeView : arena.store.ENodeView → ENodeView
  | .BVar i => .bvar (absU i)
  | .FVar idx ty => .fvar (absU idx) (absEIdx ty)
  | .Sort u => .sort (absLIdx u)
  | .Const n us => .const (absNIdx n) (absLsIdx us)
  | .App f a => .app (absEIdx f) (absEIdx a)
  | .Lam ty b m => .lam (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)
  | .ForallE ty b m =>
    .forallE (absEIdx ty) (absEIdx b) (ConRon.Refine.absBinderMeta m)
  | .LetE ty v b => .letE (absEIdx ty) (absEIdx v) (absEIdx b)
  | .Lit l => .lit (ConRon.Refine.absLiteral l)
  | .Proj n i e => .proj (absNIdx n) (absU i) (absEIdx e)

attribute [simp] absNNodeView absLNodeView absENodeView absLsNodeView
attribute [simp] absAnonNode absStrNode absNumNode absZeroNode absSuccNode
  absBinLNode absParamNode absListNode absLDer absBVarNode absFVarNode
  absSortNode absConstNode absAppNode absBindNode absBMNode absLetNode
  absLitNode absProjNode

/-! ## One table

The node column, the derived column and the cons table.  The first two are
equations between the twin's `Array` and the Rust's interleaved `Vec` of
pairs (task #97-P6-10's change, whose ledger row says exactly this: "the
refinement reads `rows.map (·.1)` for `nodes` and `rows.map (·.2)` for
`der`"); the third is `Refine/HashMap2.lean`'s `Rel`. -/

/-! ### The derived word's HASH field is OUTSIDE the relation, and has to be

**The one place Theorem 1 and Theorem 2 want incompatible things of the same
field.**  DESIGN §8.3 asks the derived column to hold *"con-leche's own packed
word — `Expr.data`'s formula verbatim"*, so that `derived st i = (denote st
i).data` is Theorem 1's exactness lemma; con-leche computes that word with
Lean core's `mixHash`, which is

    @[extern "lean_uint64_mix_hash"] opaque mixHash : UInt64 → UInt64 → UInt64

— **`opaque`**.  The port implements the same algorithm concretely
(`kernel::name::mix_hash`, a `wrapping_mul`/`>>>`/`^^^` chain), and *no proof
can relate a concrete function to an opaque constant*.  So a `TblRel` whose
`der` clause is a VALUE equation is unprovable the moment anything is
interned, and the whole tower above it would be vacuous.

The resolution is that the hash field is **not observable**, and that is a
fact about the port checked in the port: `expr::hash_of_data` and every read
of `LDer.hash` occur in `arena/store.rs` and nowhere else in `arena/`, all of
them inside the `der_of_*` family — the hash of a node is computed only to be
mixed into the hash of its parent.  The cons tables key on the node RECORD and
not on the derived word, and `Refine/HashMap2.lean`'s specification of a table
(`Inv`, `toFun`, `get`, `insert`) never mentions a hash value.  What the
checker's control flow *does* read is `bvarOfData`, `fvarOfData`, `lpOfData`
(the three cutoffs of DESIGN §8.3's lesson 20) and `LDer.hasParam`.

`TblRel` therefore carries an OBSERVATION `obsD` and relates the two columns
up to it.  The three instances below are the whole of the design decision. -/

/-- The expression tier's derived word, as what the checker can see of it:
`Expr.data`'s three non-hash fields.  The hash (bits 63…32) is dropped. -/
def derObsE (w : UInt64) : UInt64 × UInt64 × Bool :=
  (ConLeche.bvarOfData w, ConLeche.fvarOfData w, ConLeche.lpOfData w)

/-- The NAME tier's derived word is `Name.hashData` and nothing else, so
nothing of it is observable. -/
def derObsN (_ : UInt64) : Unit := ()

/-- A level's (and a level list's) derived record: the has-a-parameter bit is
observable — `instantiateLevelParams`' cutoff reads it — and the hash is
not. -/
def derObsL (d : LDer) : Bool := d.hasParam

structure TblRel {A I D α ι δ ω : Type} [DecidableEq A] [BEq α] [Hashable α]
    (P : A → Prop) (absA : A → α) (absI : I → ι) (absD : D → δ) (obsD : δ → ω)
    (rt : arena.store.Tbl A I D) (lt : Tbl α ι δ) : Prop where
  nodes : lt.nodes.toList = rt.rows.val.map (fun p => absA p.1)
  der : lt.der.toList.map obsD = rt.rows.val.map (fun p => obsD (absD p.2))
  cons : ConRon.Refine.HashMap2.RelOn P rt.cons lt.cons absA absI

/-! ### The key predicates

`RelOn P` rather than `Rel`, for the reason `HashMap2WF.lean`'s own note
gives: the `Eq2` dictionary of a key type that carries a CACHED WORD
(`StrNode`'s code points, `LitNode`'s `Literal`, `BMNode`'s `PropWhen`) is
exact only on well-formed keys, so the probe agreement can only be claimed
there.  Fourteen of the eighteen key types are handles and scalars through
and through and take `True`. -/

def AnonNodeWF (_ : arena.store.AnonNode) : Prop := True
def StrNodeWF (r : arena.store.StrNode) : Prop := ConRon.Refine.StrWF r.s
def NumNodeWF (_ : arena.store.NumNode) : Prop := True
def ZeroNodeWF (_ : arena.store.ZeroNode) : Prop := True
def SuccNodeWF (_ : arena.store.SuccNode) : Prop := True
def BinLNodeWF (_ : arena.store.BinLNode) : Prop := True
def ParamNodeWF (_ : arena.store.ParamNode) : Prop := True
def ListNodeWF (_ : arena.store.ListNode) : Prop := True
def BVarNodeWF (_ : arena.store.BVarNode) : Prop := True
def FVarNodeWF (_ : arena.store.FVarNode) : Prop := True
def SortNodeWF (_ : arena.store.SortNode) : Prop := True
def ConstNodeWF (_ : arena.store.ConstNode) : Prop := True
def AppNodeWF (_ : arena.store.AppNode) : Prop := True
def BindNodeWF (_ : arena.store.BindNode) : Prop := True
def LetNodeWF (_ : arena.store.LetNode) : Prop := True
def LitNodeWF (r : arena.store.LitNode) : Prop := ConRon.Refine.LiteralWF r.l
def ProjNodeWF (_ : arena.store.ProjNode) : Prop := True
def BMNodeWF (r : arena.store.BMNode) : Prop := ConRon.Refine.PropWhenWF r.pw

/-! ## The four tiers -/

structure NTablesRel (rt : arena.store.NTables) (lt : NTables) : Prop where
  anons : TblRel AnonNodeWF absAnonNode absNIdx absU64 derObsN rt.anons lt.anons
  strs : TblRel StrNodeWF absStrNode absNIdx absU64 derObsN rt.strs lt.strs
  nums : TblRel NumNodeWF absNumNode absNIdx absU64 derObsN rt.nums lt.nums

structure LTablesRel (rt : arena.store.LTables) (lt : LTables) : Prop where
  zeros : TblRel ZeroNodeWF absZeroNode absLIdx absLDer derObsL rt.zeros lt.zeros
  succs : TblRel SuccNodeWF absSuccNode absLIdx absLDer derObsL rt.succs lt.succs
  maxs : TblRel BinLNodeWF absBinLNode absLIdx absLDer derObsL rt.maxs lt.maxs
  imaxs : TblRel BinLNodeWF absBinLNode absLIdx absLDer derObsL rt.imaxs lt.imaxs
  params : TblRel ParamNodeWF absParamNode absLIdx absLDer derObsL rt.params lt.params

structure LsTablesRel (rt : arena.store.LsTables) (lt : LsTables) : Prop where
  lists : TblRel ListNodeWF absListNode absLsIdx absLDer derObsL rt.lists lt.lists

structure ETablesRel (rt : arena.store.ETables) (lt : ETables) : Prop where
  bvars : TblRel BVarNodeWF absBVarNode absEIdx absU64 derObsE rt.bvars lt.bvars
  fvars : TblRel FVarNodeWF absFVarNode absEIdx absU64 derObsE rt.fvars lt.fvars
  sorts : TblRel SortNodeWF absSortNode absEIdx absU64 derObsE rt.sorts lt.sorts
  consts : TblRel ConstNodeWF absConstNode absEIdx absU64 derObsE rt.consts lt.consts
  apps : TblRel AppNodeWF absAppNode absEIdx absU64 derObsE rt.apps lt.apps
  lams : TblRel BindNodeWF absBindNode absEIdx absU64 derObsE rt.lams lt.lams
  foralls : TblRel BindNodeWF absBindNode absEIdx absU64 derObsE rt.foralls lt.foralls
  lets : TblRel LetNodeWF absLetNode absEIdx absU64 derObsE rt.lets lt.lets
  lits : TblRel LitNodeWF absLitNode absEIdx absU64 derObsE rt.lits lt.lits
  projs : TblRel ProjNodeWF absProjNode absEIdx absU64 derObsE rt.projs lt.projs
  bms : TblRel BMNodeWF absBMNode absBMIdx absU64 derObsE rt.bms lt.bms

/-! ## The persistent arm: which of the two tiers holds it

Task #97-LC §1's equation.  `shared_on` selects, and `shared_on → self.pers =
∅` is the conjunct task #97-P6-6b's ledger names — but the refinement does
not need that conjunct at all: it reads the tier `pers_get_*` reads, whichever
that is, and the twin's ONE persistent field is related to it.  This is the
whole of "the twin keeps `AM := StateT AState (Except CheckError)` and the
ledger carries the relation instead". -/

/-- The expression tier every persistent read of the Rust store goes to. -/
@[inline] def rPersE (pers : arena.store.PersTier) (s : arena.store.EStore) :
    arena.store.ETables := if s.shared_on then pers.e else s.pers
/-- The level-list tier every persistent read goes to. -/
@[inline] def rPersLs (pers : arena.store.PersTier) (s : arena.store.LsStore) :
    arena.store.LsTables := if s.shared_on then pers.ls else s.pers
/-- The level tier every persistent read goes to. -/
@[inline] def rPersL (pers : arena.store.PersTier) (s : arena.store.LStore) :
    arena.store.LTables := if s.shared_on then pers.l else s.pers
/-- The name tier every persistent read goes to. -/
@[inline] def rPersN (pers : arena.store.PersTier) (s : arena.store.NStore) :
    arena.store.NTables := if s.shared_on then pers.n else s.pers

/-! ## The four stores -/

structure NStoreRel (pers : arena.store.PersTier) (rs : arena.store.NStore)
    (ls : NStore) : Prop where
  perst : NTablesRel (rPersN pers rs) ls.pers
  scrt : NTablesRel rs.scr ls.scr
  scratchOn : ls.scratchOn = rs.scratch_on

structure LStoreRel (pers : arena.store.PersTier) (rs : arena.store.LStore)
    (ls : LStore) : Prop where
  ns : NStoreRel pers rs.ns ls.ns
  perst : LTablesRel (rPersL pers rs) ls.pers
  scrt : LTablesRel rs.scr ls.scr
  scratchOn : ls.scratchOn = rs.scratch_on

structure LsStoreRel (pers : arena.store.PersTier) (rs : arena.store.LsStore)
    (ls : LsStore) : Prop where
  lvl : LStoreRel pers rs.ls ls.ls
  perst : LsTablesRel (rPersLs pers rs) ls.pers
  scrt : LsTablesRel rs.scr ls.scr
  scratchOn : ls.scratchOn = rs.scratch_on

/-- **`absStore (pers, st)`**, as a relation (the module note says why the
cons tables make it one): the Rust's `(pers : &PersTier, st.store)` against
the twin's single `EStore`. -/
structure StoreRel (pers : arena.store.PersTier) (rs : arena.store.EStore)
    (ls : EStore) : Prop where
  lss : LsStoreRel pers rs.lss ls.lss
  perst : ETablesRel (rPersE pers rs) ls.pers
  scrt : ETablesRel rs.scr ls.scr
  scratchOn : ls.scratchOn = rs.scratch_on

end ConRon.Refine2
