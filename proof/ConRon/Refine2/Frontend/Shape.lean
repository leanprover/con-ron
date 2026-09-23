/-
# `ConRon.Refine2.Frontend.Shape` — the parse state, and the shapes above it

**Task #97-P5-Frontend** (DESIGN.md §8.2, Theorem 2), the frontend tier's
vocabulary: `StateDRel` — `export_c::StateD`'s nineteen fields against
`Arena/Frontend/ExportC.lean`'s — the two error channels the parse has that
the checker tier has not, and the two hypotheses about the unverified
modeller seam.

## The three things this tier decides

**1. The parse has TWO error channels and the checker tier has neither.**

| the port returns | the twin returns | the shape |
|---|---|---|
| `Result<T, LineErr>` | `AM β` | `SimL` |
| `Result<(), LineErr>` + `&mut StateD` | `AM (StateD ⊕ RecordVerdict)` | `SimDV` |
| `Result<T, (CheckError, u64)>` | `AM (Except (CheckError × Nat) β)` | `SimStream` |

`LineErr` (`export_c.rs`, deviation 1) merges the twin's `throw` with the
RIGHT SUMMAND of `StateD ⊕ RecordVerdict`: a `LineErr::Err e` is the twin's
`fail` at `e`'s kind, and a `LineErr::Verdict v` is the twin's *success*
returning `.inr v`, at the same verdict kind.  At a function whose twin is a
plain `AM β` there is nowhere for the right summand to go, so `ALineErrSim`'s
`Verdict` arm is **`False`** — a strengthening the proofs discharge, and what
lets a reader's failure be carried into a verdict-valued caller with no side
lemma (`SimDV.of_bind`), exactly as `RefineOld/Frontend/StateDR.lean`'s
`LineOutV.of_bind` did.

`SimStream` is `Refine2/Checker/Top.lean`'s **`SimFold` at another error
pair** — the kind mirrored, the position equal, the state not compared on the
error arm.  The two are the same definition at `(CheckError, u64)` in both
cases and they belong together in `Refine2/Shape.lean`; keeping them apart is
what stops this tier importing the whole declaration checker, and DESIGN.md's
section lists the merge.

**2. Half of `arena::frontend` threads a bare `&mut EStore`, not an
`&mut AState`.**  The parse touches no memo (task #97-P4e part 1), so
**twenty-four** of the 221 — `state_d_init`, `prelude_key`, `front_of`,
`note_decl`, `parse_expr_rec_d` and nineteen more — take the store alone,
where the seventy-six above `proj_rewrite_d` take the whole state (part 2's
narrowing; the remaining 121 take no state at all).  Rather than a second family of shapes,
`withStore` lifts the port's post-store into the ambient `AState` —
`{ rst with store := e }` — and the one family covers both.  That the twin's
corresponding action really leaves the memos alone is not assumed: it is what
the proof shows, since `AStateRel₀` at the lifted state demands exactly it.

**3. The frontend tier of Theorem 2 needs NO well-formedness hypothesis on a
term**, and that is the arena's dividend.  `RefineOld/Frontend/Base.lean`'s
`StateDWF` had six clauses — `IdTableWF NameWF`, `ExprWF` on the declarations,
`MapValsWF` on the two projection tables — because the `Expr`-tree port's
`absExpr` is exact on well-formed values only.  Over handles `absIDeclaration`
is **total**, and `RelOn P` at every table of this state takes `P := True`,
because every key and every value is a handle.  What is left is the two
places a `Vec<u32>` is compared against a con-leche `String` LITERAL — a
definition's `safety` and a quotient record's `kind` — and that is
`DeclRecStrWF`, task #87 §8's finding, carried here as the scanner's
obligation it always was.

**4. Lockstep (task #97-T2-LOCKSTEP, lane Frontend).**  Every success arm
below relates the post-states by `AStateRel₀` — the same data in two
representations — and carries no `Ext` and no `StoreWF`: those are the twin's
own invariants, and Theorem 1's (DESIGN §8.2, task #97-T2-AUDIT §6).  The
modeller seam `ModellerRefines`/`SimGen` is lockstep too: the Rust generator
does what the twin's does, from related states to related states.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Frontend.Text

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun)

/-! ## The ambient state, lifted from a bare store

The port's parse threads `&mut EStore` where the twin threads `AState`;
`withStore` is the lift, and `AStateRel₀ pers (withStore rst e) lst'` is what a
store-only function's success arm claims — which says, among other things,
that the twin's action left every memo alone. -/

/-- The ambient Rust state with its store replaced: what a `&mut EStore`
function hands back, read as an `AState`. -/
@[reducible] def withStore (rst : arena.monad.AState) (e : arena.store.EStore) :
    arena.monad.AState := { rst with store := e }

@[simp] theorem withStore_store (rst : arena.monad.AState) (e : arena.store.EStore) :
    (withStore rst e).store = e := rfl

@[simp] theorem withStore_self (rst : arena.monad.AState) :
    withStore rst rst.store = rst := rfl

/-! ## The record verdict -/

/-- The twin's `RecordVerdict` without its message: the two kinds a refinement
lemma can claim.  Unlike `CheckError` it has no port-only arm, so both
constructors are mirrored. -/
inductive VerdictKind where
  | declined
  | invalid
  deriving DecidableEq, Repr

/-- The twin's verdict, as its kind. -/
def lVerdictKind : Arena.Frontend.RecordVerdict → VerdictKind
  | .declined _ => .declined
  | .invalid _ => .invalid

/-- The port's verdict, as its kind. -/
def absVerdictKind : frontend.types.RecordVerdict → VerdictKind
  | .Declined _ => .declined
  | .Invalid _ => .invalid

/-! ## The line error channel -/

/-- **What a port `LineErr` claims about the twin's `AM`.**  Two arms, and the
second is a CLAIM and not a silence: at a function whose twin is a plain
`AM β` a `Verdict` is impossible, because the port's readers and value
builders reach their error channel only through `export_c::merr`. -/
def ALineErrSim {γ : Type} (e : frontend.export_c.LineErr)
    (x : Except Arena.CheckError γ) : Prop :=
  match e with
  | .Err ce => AErrSim ce x
  | .Verdict _ => False

theorem ALineErrSim.err {γ : Type} {ce : kernel.core_types.CheckError}
    {x : Except Arena.CheckError γ} (h : AErrSim ce x) :
    ALineErrSim (.Err ce) x := h

theorem ALineErrSim.native {γ : Type} {x : Except Arena.CheckError γ} (m) :
    ALineErrSim (.Err (.Native m)) x := AErrSim.native m

/-- Error propagation through a bind, the move every arm makes. -/
theorem ALineErrSim.bind {γ δ : Type} {e : frontend.export_c.LineErr}
    {x : Except Arena.CheckError γ} (h : ALineErrSim e x)
    (f : γ → Except Arena.CheckError δ) : ALineErrSim e (x >>= f) := by
  cases e with
  | Err ce => exact AErrSim.bind h f
  | Verdict v => exact h.elim

theorem ALineErrSim.of_eq {γ : Type} {e : frontend.export_c.LineErr}
    {x y : Except Arena.CheckError γ} (h : ALineErrSim e x) (hxy : y = x) :
    ALineErrSim e y := by rw [hxy]; exact h

/-! ## `SimL` — a port function with a `LineErr` channel and a store

The value builders and readers of the parse: `st_name`, `parse_cv_d`,
`note_decl_entries`, …  The twin is `AM β`; the port's post-state is either a
bare `EStore` (lifted by `withStore`) or an `AState`. -/

/-- The outcome of a `LineErr`-channelled port function — lockstep (task
#97-T2-LOCKSTEP): the twin's post-state is related by `AStateRel₀`, and nothing
about the twin's own store (`StoreWF`, `Ext`) is claimed. -/
def LOut {α β : Type} (A : α → β) (pers : arena.store.PersTier)
    (o : core.result.Result α frontend.export_c.LineErr)
    (rst' : arena.monad.AState)
    (x : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok r => ∃ lst', x = .ok (A r, lst') ∧ AStateRel₀ pers rst' lst' ∧
      AStateInv pers rst'
  | .Err e => ALineErrSim e x

/-- `LOut` at the Rust's outcome pair. -/
def SimL {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α frontend.export_c.LineErr × arena.monad.AState)
    (x : AM β) : Prop :=
  LOut A pers o.1 o.2 (x.run lst)

theorem LOut.ok {α β : Type} {A : α → β} {r : α} {pers : arena.store.PersTier}
    {lst' : AState} {rst' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)} (hx : x = .ok (A r, lst'))
    (hrel : AStateRel₀ pers rst' lst') (hinv : AStateInv pers rst') :
    LOut A pers (.Ok r) rst' x :=
  ⟨lst', hx, hrel, hinv⟩

theorem LOut.err {α β : Type} {A : α → β} {e : frontend.export_c.LineErr}
    {pers : arena.store.PersTier} {rst' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)} (h : ALineErrSim e x) :
    LOut A pers (.Err e) rst' x := h

theorem LOut.dest {α β : Type} {A : α → β} {r : α} {pers : arena.store.PersTier}
    {rst' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)}
    (h : LOut A pers (.Ok r) rst' x) :
    ∃ lst', x = .ok (A r, lst') ∧ AStateRel₀ pers rst' lst' ∧
      AStateInv pers rst' := h

/-- **A `LineErr`-channelled READER**: no state in the return at all
(`st_name`, `st_level`, `st_expr`, `get_decl_d`, `note_one`, `declares`…).
The twin answers the abstraction and leaves the state alone. -/
def SimLR {α β : Type} (A : α → β) (lst : AState)
    (o : core.result.Result α frontend.export_c.LineErr) (x : AM β) : Prop :=
  match o with
  | .Ok r => x.run lst = .ok (A r, lst)
  | .Err e => ALineErrSim e (x.run lst)

theorem SimLR.ok {α β : Type} {A : α → β} {lst : AState} {r : α} {x : AM β}
    (h : x.run lst = .ok (A r, lst)) : SimLR A lst (.Ok r) x := h

theorem SimLR.err {α β : Type} {A : α → β} {lst : AState}
    {e : frontend.export_c.LineErr} {x : AM β}
    (h : ALineErrSim e (x.run lst)) : SimLR A lst (.Err e) x := h

theorem SimLR.apply {α β : Type} {A : α → β} {lst : AState} {r : α} {x : AM β}
    (h : SimLR A lst (.Ok r) x) : x.run lst = .ok (A r, lst) := h

/-! ## The parse's index tables

`scan_types::IdTable<T>` against `ConLeche/Frontend/Scan/Types.lean:341-344`,
at the three HANDLE kinds — which is the whole of the change from
`RefineOld/Frontend/StateDR.lean`'s `IdTableRel`: the element abstraction is
`absNIdx`/`absLIdx`/`absEIdx` where it was `absName`/`absLevel`/`absExpr`, and
those are TOTAL where the three value abstractions were exact on well-formed
values only.  So the table relation needs no `P`. -/

/-- The overflow map's `Hashable` dictionary. -/
abbrev hU64 := U64.Insts.Con_ron_coreRonHashmapHashable
/-- The overflow map's `Eq2` dictionary: `u64`'s `==`. -/
abbrev eU64 := U64.Insts.Con_ron_coreRonHashmapEq2

/-- `u64`'s `eq2` is exact and total. -/
theorem u64Eq2Spec : ConRon.Refine.HashMap.Eq2Spec eU64 := by intro a b; rfl

theorem u64Eq2Fwd {P : Std.U64 → Prop} : ConRon.Refine.HashMap.Eq2Fwd eU64 P :=
  ConRon.Refine.HashMap.Eq2Fwd_of_Eq2Spec u64Eq2Spec

/-- Every key of a `u64`-keyed table satisfies the empty restriction. -/
theorem u64KeysOk {T : Type} (m : ron.hashmap.HashMap Std.U64 T) :
    ConRon.Refine.HashMap.KeysOk (fun _ : Std.U64 => True) m := fun _ _ => trivial

/-- `scan_types::IdTable T` denotes `ConLeche.Frontend.IdTable α` under `A`:
the dense prefix element for element, the overflow map key for key, plus the
port's own hash-table invariant, which a probe of the overflow map needs and
no abstraction can supply. -/
structure IdTableRel {T α : Type} (A : T → α)
    (t : frontend.scan_types.IdTable T)
    (lt : ConLeche.Frontend.IdTable α) : Prop where
  dense : t.dense.val.map A = lt.dense.toList
  sparse : ConRon.Refine.HashMap.RelOn (fun _ : Std.U64 => True) t.sparse lt.sparse
    absU64 A
  inv : ConRon.Refine.HashMap.Inv hU64 t.sparse

/-! ## Probing a handle-keyed table of the parse

Every `HashMap2` of `StateD` and of `ModelCtx` is keyed on an `NIdx`, and the
restriction is `anyN` — no restriction at all, because `absNIdx` is injective
on every handle.  So one lemma serves every probe of this tier: the port's
`get` answers `toFun`, with no side condition but the table's own `Inv`. -/

/-- The key restriction every table of the parse state takes: none. -/
@[reducible] def anyN (_ : arena.handle.NIdx) : Prop := True

theorem anyNKeysOk {V : Type} (m : ron.hashmap2.HashMap2 arena.handle.NIdx V) :
    KeysOk anyN m := fun _ _ => trivial

/-- **The one probe lemma of the tier.** -/
theorem nidx_get {V : Type} {m : ron.hashmap2.HashMap2 arena.handle.NIdx V}
    (hinv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable m)
    {k : arena.handle.NIdx} {r : Option V}
    (h : ron.hashmap2.HashMap2.get arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2 m k = ok r) :
    r = toFun m k :=
  ConRon.Refine.HashMap2.get_refines_gen nidx_eq2 hinv (anyNKeysOk m) trivial h

/-! ## The frontend's own records -/

def absProjRecOwner (o : frontend.types.ProjRecOwner) : ProjRecOwner :=
  ⟨absNIdx o.t, o.lps.val.map absNIdx, absU o.n_p, absNIdx o.ctor, absU o.n_f,
    absNIdx o.rec_name, o.rec_lps.val.map absNIdx, absEIdx o.rec_type,
    absU o.num_motives, absU o.num_minors⟩

def absMIndTypeRec (t : frontend.types.MIndTypeRec) : MIndTypeRec :=
  ⟨absIConstantVal t.cv, absU t.n_p, absU t.n_idx, t.ctors.val.map absNIdx,
    t.is_rec, t.is_reflexive, absU t.num_nested⟩

def absMIndCtorRec (c : frontend.types.MIndCtorRec) : MIndCtorRec :=
  ⟨absIConstantVal c.cv, absU c.n_p, absU c.n_f⟩

def absMIndRecRec (r : frontend.types.MIndRecRec) : MIndRecRec :=
  ⟨absIConstantVal r.cv, absU r.n_p, absU r.n_m, absU r.nm, absU r.n_i,
    r.rules.val.map absIRecRule⟩

def absBlockRec (b : frontend.types.BlockRec) : BlockRec :=
  ⟨b.types.val.map absMIndTypeRec, b.ctors.val.map absMIndCtorRec,
    b.recs.val.map absMIndRecRec⟩

/-- `arena::env::IDeclaration` lists, at the containers the twin has.  The
`…Arr` family is the parse's, whose `decls` is an `Array`; the `…L` family is
`Refine2/Checker/Shape.lean`'s and is reused where the twin takes a `List`. -/
def absIDeclArr (v : alloc.vec.Vec arena.env.IDeclaration) : Array IDeclaration :=
  (v.val.map absIDeclaration).toArray
def absIDeclArrFrom (v : alloc.vec.Vec arena.env.IDeclaration) (i : Std.Usize) :
    Array IDeclaration := ((v.val.drop i.val).map absIDeclaration).toArray
def absNIdxArr (v : alloc.vec.Vec arena.handle.NIdx) : Array NIdx :=
  (v.val.map absNIdx).toArray
def absProjRecOwnerL (v : alloc.vec.Vec frontend.types.ProjRecOwner) :
    List ProjRecOwner := v.val.map absProjRecOwner
def absBinderPairs (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    List (EIdx × ConLeche.BinderMeta) :=
  v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)
def absBinderPairsFrom
    (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Std.Usize) : List (EIdx × ConLeche.BinderMeta) :=
  (v.val.drop i.val).map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)

/-- `proj_rec`'s three tuple aliases, which the twin spells as tuples too
(task #97-P4e part 2: *"the twin's tuples, spelled as tuples"*). -/
def absProjTypeRec
    (t : arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) × arena.handle.EIdx ×
      Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool) :
    NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool :=
  (absNIdx t.1, t.2.1.val.map absNIdx, absEIdx t.2.2.1, absU t.2.2.2.1,
    absU t.2.2.2.2.1, t.2.2.2.2.2.1.val.map absNIdx, t.2.2.2.2.2.2)

def absProjCtorRec (c : arena.handle.NIdx × Std.U64 × arena.handle.EIdx) :
    NIdx × Nat × EIdx := (absNIdx c.1, absU c.2.1, absEIdx c.2.2)

def absProjRecRec
    (r : arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) × arena.handle.EIdx ×
      Std.U64 × Std.U64) : NIdx × List NIdx × EIdx × Nat × Nat :=
  (absNIdx r.1, r.2.1.val.map absNIdx, absEIdx r.2.2.1, absU r.2.2.2.1,
    absU r.2.2.2.2)

def absProjTypeRecL
    (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool)) :
    List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool) :=
  v.val.map absProjTypeRec
def absProjTypeRecLFrom
    (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool))
    (i : Std.Usize) :
    List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool) :=
  (v.val.drop i.val).map absProjTypeRec
def absProjCtorRecL (v : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)) :
    List (NIdx × Nat × EIdx) := v.val.map absProjCtorRec
def absProjCtorRecLFrom
    (v : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)) (i : Std.Usize) :
    List (NIdx × Nat × EIdx) := (v.val.drop i.val).map absProjCtorRec
def absProjRecRecL
    (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64)) : List (NIdx × List NIdx × EIdx × Nat × Nat) :=
  v.val.map absProjRecRec
def absProjRecRecLFrom
    (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64)) (i : Std.Usize) :
    List (NIdx × List NIdx × EIdx × Nat × Nat) :=
  (v.val.drop i.val).map absProjRecRec

/-- `note_decl`'s intermediate: one entry per constant a pushed record
declares.  The twin builds the same four-tuple list inline in `noteDecl`. -/
def absNoteEntry
    (e : arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) × arena.handle.EIdx ×
      (Option Std.U64)) : NIdx × List NIdx × EIdx × Option Nat :=
  (absNIdx e.1, e.2.1.val.map absNIdx, absEIdx e.2.2.1, e.2.2.2.map absU)

def absNoteEntryL
    (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × (Option Std.U64))) : List (NIdx × List NIdx × EIdx × Option Nat) :=
  v.val.map absNoteEntry
def absNoteEntryLFrom
    (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × (Option Std.U64))) (i : Std.Usize) :
    List (NIdx × List NIdx × EIdx × Option Nat) :=
  (v.val.drop i.val).map absNoteEntry

attribute [simp] absProjRecOwner absMIndTypeRec absMIndCtorRec absMIndRecRec
  absBlockRec absIDeclArr absIDeclArrFrom absNIdxArr
  absProjRecOwnerL absBinderPairs absBinderPairsFrom absProjTypeRec absProjCtorRec
  absProjRecRec absProjTypeRecL absProjTypeRecLFrom absProjCtorRecL
  absProjCtorRecLFrom absProjRecRecL absProjRecRecLFrom absNoteEntry
  absNoteEntryL absNoteEntryLFrom withStore

/-! ## `StateDRel` — the parse state

Nineteen fields against nineteen.  Three `IdTable`s, five handle-keyed
`HashMap2`s, six `Vec`s, three scalars and two flags.  **Every `RelOn` is at
`P := True`**, because every key and every value is a handle — see the module
note's point 3.  The one payload that is not is `in_model_declined`'s reason,
a `Vec<u32>` against a `String`, and it is not compared: a decline REASON is a
message like any other (DESIGN §3.1, and task #87 §13's ruling, where
weakening this very clause was the fix). -/

/-- `export_c::StateD` against `Arena/Frontend/ExportC.lean`'s. -/
structure StateDRel (rs : frontend.export_c.StateD) (ls : Arena.Frontend.StateD) :
    Prop where
  names : IdTableRel absNIdx rs.names ls.names
  levels : IdTableRel absLIdx rs.levels ls.levels
  exprs : IdTableRel absEIdx rs.exprs ls.exprs
  decls : ls.decls = absIDeclArr rs.decls
  projOwners : RelOn anyN rs.proj_owners ls.projOwners absNIdx absProjRecOwner
  projLevels : RelOn anyN rs.proj_levels ls.projLevels absNIdx absLIdx
  projRewrites : ls.projRewrites = absNIdxArr rs.proj_rewrites
  constTypes : RelOn anyN rs.const_types ls.constTypes absNIdx
    (fun p => (p.1.val.map absNIdx, absEIdx p.2))
  heights : RelOn anyN rs.heights ls.heights absNIdx absU
  inModel : ls.inModel = rs.in_model
  inModelled : ls.inModelled = absNIdxArr rs.in_modelled
  genRecords : ls.genRecords = absU rs.gen_records
  genOwner : RelOn anyN rs.gen_owner ls.genOwner absNIdx absNIdx
  /-- `inModelGen` is the `CON_LECHE_INMODEL_DUMP` writer's receipt, which no
  reader below the dump looks at; the twin carries it because DESIGN §8.6's
  lockstep rule is clause-for-clause, and so does the port.  The relation
  compares the ORDINALS and the declarations. -/
  inModelGen : ls.inModelGen =
    (rs.in_model_gen.val.map fun p => (absU p.1, absIDeclArr p.2)).toArray
  indCount : ls.indCount = absU rs.ind_count
  indBlocks : RelOn anyN rs.ind_blocks ls.indBlocks absNIdx absBlockRec
  inModelCensus : ls.inModelCensus = rs.in_model_census
  /-- The census's declines: the BLOCK NAMES only.  Task #87 §13 — *"the
  ruling was to weaken the relation, not to strengthen the hypothesis"*: a
  decline reason is a message, and the theorem does not read messages. -/
  inModelDeclined : ls.inModelDeclined.map (·.1) =
    (rs.in_model_declined.val.map fun p => absNIdx p.1).toArray

/-- The Rust-side invariant of the parse state: the five hash tables'.  The
three `IdTable`s carry their overflow map's `Inv` inside `IdTableRel`, because
`Tbl`'s does not travel any other way. -/
structure StateDInv (rs : frontend.export_c.StateD) : Prop where
  projOwners : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rs.proj_owners
  projLevels : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rs.proj_levels
  constTypes : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rs.const_types
  heights : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rs.heights
  genOwner : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rs.gen_owner
  indBlocks : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rs.ind_blocks

/-- **`export_c::ParseResultD` against `Arena/Frontend/ExportC.lean`'s.**  A
relation and not a function, for `StateDRel`'s reason: two of its seven fields
are `HashMap2`s.  The census's declines compare BLOCK NAMES only. -/
structure ParseResultDRel (rp : frontend.export_c.ParseResultD)
    (lp : Arena.Frontend.ParseResultD) : Prop where
  decls : lp.decls = absIDeclArr rp.decls
  projRewrites : lp.projRewrites = absNIdxArr rp.proj_rewrites
  inModelled : lp.inModelled = absNIdxArr rp.in_modelled
  genRecords : lp.genRecords = absU rp.gen_records
  genOwner : RelOn anyN rp.gen_owner lp.genOwner absNIdx absNIdx
  inModelGen : lp.inModelGen =
    (rp.in_model_gen.val.map fun p => (absU p.1, absIDeclArr p.2)).toArray
  inModelDeclined : lp.inModelDeclined.map (·.1) =
    (rp.in_model_declined.val.map fun p => absNIdx p.1).toArray

/-! ## `SimD` / `SimDV` — a line function, which threads the parse state too

The port's line functions take `&mut AState` (or `&mut EStore`) AND
`&mut StateD`; the twin takes the `StateD` by value and returns it.  The
success arm carries the post-state's `StateDInv` beside its `StateDRel`
(task #97-P5-Front, finding F2): without it no loop over lines can hand the
next line the invariant its probes need.  `SimD` is
the `AM StateD`-valued family and `SimDV` the `AM (StateD ⊕ RecordVerdict)`
one; `SimDV.of_bind` is where `ALineErrSim`'s `False` arm pays. -/

/-- A line step whose twin returns the state. -/
def SimD (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result Unit frontend.export_c.LineErr ×
      arena.monad.AState × frontend.export_c.StateD)
    (x : AM Arena.Frontend.StateD) : Prop :=
  match o.1 with
  | .Ok _ => ∃ lsd' lst', x.run lst = .ok (lsd', lst') ∧ StateDRel o.2.2 lsd' ∧ StateDInv o.2.2 ∧
      AStateRel₀ pers o.2.1 lst' ∧ AStateInv pers o.2.1
  | .Err e => ALineErrSim e (x.run lst)

theorem SimD.mk {pers : arena.store.PersTier} {lst lst' : AState}
    {lsd' : Arena.Frontend.StateD} {rst' : arena.monad.AState}
    {rsd' : frontend.export_c.StateD} {x : AM Arena.Frontend.StateD}
    (hx : x.run lst = .ok (lsd', lst')) (hd : StateDRel rsd' lsd')
    (hi : StateDInv rsd')
    (hrel : AStateRel₀ pers rst' lst') (hinv : AStateInv pers rst') :
    SimD pers lst (.Ok (), rst', rsd') x :=
  ⟨lsd', lst', hx, hd, hi, hrel, hinv⟩

theorem SimD.err {pers : arena.store.PersTier} {lst : AState}
    {e : frontend.export_c.LineErr}
    {rst' : arena.monad.AState} {rsd' : frontend.export_c.StateD}
    {x : AM Arena.Frontend.StateD} (h : ALineErrSim e (x.run lst)) :
    SimD pers lst (.Err e, rst', rsd') x := h

/-- A line step whose twin returns the state OR a verdict — the line layer
proper (`apply_line`, `process_line_core_d`, `install_ind_d`).  This is where
the port's second `LineErr` arm lands: a `Verdict` is a twin SUCCESS at the
right summand, at the same verdict kind. -/
def SimDV (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result Unit frontend.export_c.LineErr ×
      arena.monad.AState × frontend.export_c.StateD)
    (x : AM (Arena.Frontend.StateD ⊕ Arena.Frontend.RecordVerdict)) : Prop :=
  match o.1 with
  | .Ok _ => ∃ lsd' lst', x.run lst = .ok (.inl lsd', lst') ∧ StateDRel o.2.2 lsd' ∧ StateDInv o.2.2 ∧
      AStateRel₀ pers o.2.1 lst' ∧ AStateInv pers o.2.1
  | .Err (.Err ce) => AErrSim ce (x.run lst)
  | .Err (.Verdict v) => ∃ lv lst', x.run lst = .ok (.inr lv, lst') ∧
      lVerdictKind lv = absVerdictKind v

theorem SimDV.mk {pers : arena.store.PersTier} {lst lst' : AState}
    {lsd' : Arena.Frontend.StateD} {rst' : arena.monad.AState}
    {rsd' : frontend.export_c.StateD}
    {x : AM (Arena.Frontend.StateD ⊕ Arena.Frontend.RecordVerdict)}
    (hx : x.run lst = .ok (.inl lsd', lst')) (hd : StateDRel rsd' lsd')
    (hi : StateDInv rsd')
    (hrel : AStateRel₀ pers rst' lst') (hinv : AStateInv pers rst') :
    SimDV pers lst (.Ok (), rst', rsd') x :=
  ⟨lsd', lst', hx, hd, hi, hrel, hinv⟩

theorem SimDV.verdict {pers : arena.store.PersTier} {lst lst' : AState}
    {v : frontend.types.RecordVerdict}
    {lv : Arena.Frontend.RecordVerdict} {rst' : arena.monad.AState}
    {rsd' : frontend.export_c.StateD}
    {x : AM (Arena.Frontend.StateD ⊕ Arena.Frontend.RecordVerdict)}
    (hx : x.run lst = .ok (.inr lv, lst'))
    (hk : lVerdictKind lv = absVerdictKind v) :
    SimDV pers lst (.Err (.Verdict v), rst', rsd') x := ⟨lv, lst', hx, hk⟩

/-- **A reader's failure, inside a line function.**  The one move that carries
a `SimL`-shaped failure into the sum's outcome, and where `ALineErrSim`'s
`False` arm pays: the reader cannot have returned a verdict. -/
theorem SimDV.of_bind {γ : Type} {pers : arena.store.PersTier} {lst : AState}
    {e : frontend.export_c.LineErr}
    {rst' : arena.monad.AState} {rsd' : frontend.export_c.StateD}
    {x : Except Arena.CheckError (γ × AState)}
    {f : γ × AState → Except Arena.CheckError
      ((Arena.Frontend.StateD ⊕ Arena.Frontend.RecordVerdict) × AState)}
    {y : AM (Arena.Frontend.StateD ⊕ Arena.Frontend.RecordVerdict)}
    (h : ALineErrSim e x) (hy : y.run lst = x >>= f) :
    SimDV pers lst (.Err e, rst', rsd') y := by
  cases e with
  | Err ce => exact (hy ▸ AErrSim.bind h f : AErrSim ce (y.run lst))
  | Verdict v => exact h.elim

/-! ## `SimStream` — the chunk drivers' error PAIR

`Refine2/Checker/Top.lean`'s `SimFold` at the parse's own error pair.  The
kind is mirrored and the position is real content and is compared; the state
is NOT compared on the error arm, and must not be — the twin's `chunkStep`
hands back whatever state the failing line left.

**The error arm has TWO twin shapes** (task #97-P5-Front, finding F1).  The
port folds every failure of a line into the pair: `line_err_to_check` sends a
`LineErr::Err e` to `(e, line)` exactly as it sends a verdict, and
`parse_bytes`/`parse_chunks` send a `state_d_init` failure to `(e, 0)`.  The
twin does not: a `fail` inside `applyLine` (an unknown index, a dangling
handle, a quotient kind it does not know) or inside `StateD.init` is an `AM`
THROW, which no `match ← …` of `feedChunk`/`parseBytes` catches, so the
twin's run is `.error le` with no position at all.  Only the verdict arm and
the scanner's own errors come back as the twin's `.ok (.error (le, n))`.  The
arm therefore claims *the twin fails too, at the same kind — as a value at the
same position, or as a throw*.  The success arm, which is the one the
composition reads, is unchanged. -/
/-- **What a port error PAIR claims about the twin's run**: the twin fails
too, at the same kind — either as an error VALUE at the same position, or as
an `AM` throw (the module note's finding F1).  A `Native` claims nothing. -/
def StreamErrSim {γ : Type} (p : kernel.core_types.CheckError × Std.U64)
    (x : Except Arena.CheckError (Except (Arena.CheckError × Nat) γ × AState)) :
    Prop :=
  ∀ k, absAErrKind p.1 = some k →
    (∃ le lst', x = .ok (.error (le, absU p.2), lst') ∧ lAErrKind le = some k) ∨
    (∃ le, x = .error le ∧ lAErrKind le = some k)

theorem StreamErrSim.native {γ : Type} {n : Std.U64} (m)
    {x : Except Arena.CheckError (Except (Arena.CheckError × Nat) γ × AState)} :
    StreamErrSim (.Native m, n) x := by
  intro k hk; simp at hk

/-- A throw, carried: the port's `(e, n)` for an `AErrSim e` twin failure. -/
theorem StreamErrSim.of_throw {γ δ : Type} {e : kernel.core_types.CheckError}
    {n : Std.U64} {x : Except Arena.CheckError δ}
    {f : δ → Except Arena.CheckError (Except (Arena.CheckError × Nat) γ × AState)}
    (h : AErrSim e x) : StreamErrSim (e, n) (x >>= f) := by
  intro k hk
  obtain ⟨le, hx, hle⟩ := h k hk
  exact Or.inr ⟨le, by rw [hx]; rfl, hle⟩

def SimStreamRel {α β : Type} (R : α → β → Prop) (pers : arena.store.PersTier)
    (lst : AState)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64) ×
      arena.monad.AState)
    (x : AM (Except (Arena.CheckError × Nat) β)) : Prop :=
  match o.1 with
  | .Ok r => ∃ v lst', x.run lst = .ok (.ok v, lst') ∧ R r v ∧
      AStateRel₀ pers o.2 lst' ∧ AStateInv pers o.2
  | .Err p => StreamErrSim p (x.run lst)

/-- The common case: the result abstracts by a FUNCTION. -/
abbrev SimStream {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64) ×
      arena.monad.AState)
    (x : AM (Except (Arena.CheckError × Nat) β)) : Prop :=
  SimStreamRel (fun r v => v = A r) pers lst o x

theorem SimStreamRel.ok {α β : Type} {R : α → β → Prop} {pers : arena.store.PersTier}
    {lst lst' : AState} {r : α} {v : β} {rst' : arena.monad.AState}
    {x : AM (Except (Arena.CheckError × Nat) β)}
    (hx : x.run lst = .ok (.ok v, lst')) (hr : R r v) (hrel : AStateRel₀ pers rst' lst')
    (hinv : AStateInv pers rst') :
    SimStreamRel R pers lst (.Ok r, rst') x := ⟨v, lst', hx, hr, hrel, hinv⟩

/-- A port `Native` in the pair claims nothing, exactly as it does in a throw. -/
theorem SimStreamRel.native {α β : Type} {R : α → β → Prop}
    {pers : arena.store.PersTier}
    {lst : AState} {rst' : arena.monad.AState} {n : Std.U64} (m)
    {x : AM (Except (Arena.CheckError × Nat) β)} :
    SimStreamRel R pers lst (.Err (.Native m, n), rst') x :=
  StreamErrSim.native m

/-! ## The `StateD`-carrying variant of the stream shape

`feed_chunk` and `chunk_step` thread the parse state by `&mut` beside the
`AState`, so their success arm carries `StateDRel` as well. -/
def SimStreamD {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64) ×
      arena.monad.AState × frontend.export_c.StateD)
    (x : AM (Except (Arena.CheckError × Nat) (Arena.Frontend.StateD × β))) : Prop :=
  match o.1 with
  | .Ok r => ∃ lsd' lst', x.run lst = .ok (.ok (lsd', A r), lst') ∧
      StateDRel o.2.2 lsd' ∧ StateDInv o.2.2 ∧ AStateRel₀ pers o.2.1 lst' ∧ AStateInv pers o.2.1
  | .Err p => StreamErrSim p (x.run lst)

/-! ## The modeller seam (DESIGN §8.2's `Modeller`)

Task #84 made the parse quantify over the modeller, and Charon renders a trait
method on a type parameter as a TYPECLASS FIELD, so the extracted parse is
quantified over an opaque `generate`.  This tier therefore carries the same
two promises the original campaign carried (`RefineOld/Frontend/Base.lean`'s
`ModellerWF` and task #87 §16's `ModellerRefines`) — minus the first, which
the arena does not need: `ModellerWF` said *"every declaration `generate`
returns is well formed"*, and over handles `absIDeclaration` is total.  **One
promise, not two.**

The seam is unverified by design (§8.2: a wrong generated record is rejected
or declined by the fold, never accepted; its correctness decides coverage
only), so the promise disappears the day the modeller leaves the parse, and
not before. -/

/-- `types::ModelCtx`'s three borrowed tables against the twin's three
functions.  `ctx_height` answers `0` on a miss where the twin's `heights` is
total, which is the one clause that is not a plain probe agreement. -/
structure CtxRel (rc : frontend.types.ModelCtx) (lc : Arena.Frontend.Ctx) : Prop where
  tbl : ∀ n, lc.tbl (absNIdx n) =
    (toFun rc.tbl n).map fun p => (p.1.val.map absNIdx, absEIdx p.2)
  heights : ∀ n, lc.heights (absNIdx n) = ((toFun rc.heights n).map absU).getD 0
  blocks : ∀ n, lc.blocks (absNIdx n) = (toFun rc.blocks n).map absBlockRec
  tblInv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rc.tbl
  heightsInv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rc.heights
  blocksInv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rc.blocks

/-- **The outcome of one `generate` call.**  The port's generator takes a bare
`&mut EStore` — it interns and touches no memo — and its decline carries a
`Vec<u32>` message where the twin's carries a `String`; messages are never
compared, so the error arm claims only that the twin declines too. -/
def SimGen (pers : arena.store.PersTier) (rst : arena.monad.AState) (lst : AState)
    (o : core.result.Result (alloc.vec.Vec arena.env.IDeclaration)
      (alloc.vec.Vec Std.U32) × arena.store.EStore)
    (x : AM (Except String (List IDeclaration))) : Prop :=
  ∃ lst', AStateRel₀ pers (withStore rst o.2) lst' ∧
    AStateInv pers (withStore rst o.2) ∧
    (match o.1 with
     | .Ok ds => x.run lst = .ok (.ok (ds.val.map absIDeclaration), lst')
     | .Err _ => ∃ s, x.run lst = .ok (.error s, lst'))

/-- **The modeller hypothesis**, task #87 §16's `ModellerRefines` over
handles: *the port's generator refines the twin's, at a related state and a
related context*.  One clause. -/
structure ModellerRefines {G : Type} (inst : frontend.types.Modeller G) (m : G)
    (lmd : Arena.Frontend.Modeller) : Prop where
  generate : ∀ {pers rst lst rc lc b o},
    AStateRel₀ pers rst lst → AStateInv pers rst → CtxRel rc lc →
    inst.generate m pers rst.store rc b = ok o →
    SimGen pers rst lst o (lmd.generate lc (absBlockRec b))

/-! ## The scanner seam

`crates/con-ron-core/src/frontend/{scan_fast,scan_types}.rs` is the byte
recogniser the arena swap did not touch, and the twin does not twin it either
— `Arena/Frontend/ExportC.lean` calls `ConLeche.Frontend.scanLineFwd` by name
(task #97e part 1 checked `Scan/{Types,Fast}.lean` is term-free).  So the two
sides of this seam are **the same two sides tasks #85-#87 proved equal**, and
what this tier owes is a record of the statements that tier proved, not a new
argument.

`ScanSpec`'s three clauses are, verbatim, `Scan/Line.lean`'s
`scan_line_fwd_refines`, `scan_line_fwd_str_wf` (+ `scan_line_fwd_digits`) and
`Scan/Kit.lean`'s `newline_from_refines` — the scanner tier task #97-P5-Front
moved back from `RefineOld/Frontend/` — and **`Scan/Spec.lean`'s `scanSpec :
ScanSpec` discharges it**.  The record stays a parameter of the tier's
statements so that they do not import the scanner tier; a caller passes
`scanSpec`. -/

/-- The declaration record's two SPELLING payloads hold valid code points —
task #87 §8's `DeclRecStrWF`, the one place this tier needs a well-formedness
clause, because `"safe"` and `"type"` are compared against con-leche `String`
LITERALS and `absString` sends an invalid code point to `'\0'`. -/
def DeclRecStrWF : frontend.scan_types.DeclRec → Prop
  | .Defn _ _ _ s => ConRon.Refine.StrWF s
  | .Quot _ k => ConRon.Refine.StrWF k
  | _ => True

/-- A `NameRec`'s string payload holds valid code points. -/
def NameRecStrWF : frontend.scan_types.NameRec → Prop
  | .Str _ s => ConRon.Refine.StrWF s
  | .Num _ _ => True

/-- An `ExprRec`'s string literal holds valid code points: the store's
`ENodeViewWF` at a `Lit (StrVal s)` node, which the intern needs for the same
reason `NameRecStrWF` is — `absString` is exact on valid code points only. -/
def ExprRecStrWF : frontend.scan_types.ExprRec → Prop
  | .StrVal s => ConRon.Refine.StrWF s
  | _ => True

/-- Every string payload of a line holds valid code points: the declaration
record's two spellings (`DeclRecStrWF`), a name's component and a string
literal.  **Task #97-P5-Front round 2 (finding F5)**: until then only the
first was here, which left `apply_line`'s name and expression arms without
the `NameRecStrWF` / `ExprRecStrWF` their writers need; the scanner owes all
three (`Scan/Spec.lean`, from `scan_line_fwd_str_wf` and `scan_line_fwd_wf`). -/
def LineRecStrWF : frontend.scan_types.LineRec → Prop
  | .Decl d => DeclRecStrWF d
  | .Name _ n => NameRecStrWF n
  | .Expr _ r => ExprRecStrWF r
  | _ => True

/-- What `parse_expr_rec_d` needs of a `natVal` literal's digits (deviation 2):
`nat_decimal::from_decimal` never declines them and its value is theirs. -/
def NatValSpec (r : frontend.scan_types.ExprRec) : Prop :=
  ∀ ds, r = .NatVal ds →
    ∀ o, frontend.nat_decimal.from_decimal (alloc.vec.Vec.deref ds) = ok o →
      ∃ n, o = some n ∧ ConRon.Refine.Nat.toNat n = natOfDigits ds

/-- `NatValSpec` at a line. -/
def LineNatValSpec : frontend.scan_types.LineRec → Prop
  | .Expr _ r => NatValSpec r
  | _ => True

/-- **The scanner's obligation, as a record.**  Three clauses, every one of
them a theorem of `ConRon/RefineOld/Frontend/` against the SAME Rust
functions; see the section note. -/
structure ScanSpec : Prop where
  /-- `scan_line_fwd` returns what `scanLineFwd` returns, at the same position,
  and fails at the same tag and offset (`RefineOld/Frontend/ScanLine.lean`'s
  `scan_line_fwd_refines`). -/
  scanLineFwd : ∀ {b : Slice Std.U8} {i : Std.Usize} {o},
    frontend.scan_fast.scan_line_fwd b i = ok o →
    ScanSim absLineRec o (ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i))
  /-- Every string payload of a scanned line holds valid code points
  (`ScanLine.lean`'s `scan_line_fwd_str_wf`), and a `natVal`'s digits are a
  decimal run (`ScanStr.lean`'s `scan_quoted_nat_digits`). -/
  scanLineStr : ∀ {b : Slice Std.U8} {i : Std.Usize} {r : frontend.scan_types.LineRec}
    {j : Std.Usize},
    frontend.scan_fast.scan_line_fwd b i = ok (.Ok (r, j)) →
    LineRecStrWF r ∧ LineNatValSpec r
  /-- `newline_from` is `newlineFrom` (`ScanKit.lean`). -/
  newlineFrom : ∀ {b : Slice Std.U8} {i : Std.Usize} {v : Bool},
    frontend.scan_fast.newline_from b i = ok v →
    v = ConLeche.Frontend.newlineFrom (absBytes b) (absPos i)

end ConRon.Refine2.Frontend
