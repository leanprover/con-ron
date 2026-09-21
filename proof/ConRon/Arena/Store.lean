/-
# The four interned stores (DESIGN.md §8.3, task #97 P2a)

Names, levels, level lists and expressions, each as **one array per
constructor per tier** of a uniform fixed-size record, a **parallel derived
array** holding con-leche's own cached word for that node, and a **cons table**
per constructor per tier keyed by the constructor's fields.

    NStore ⊂ LStore ⊂ LsStore ⊂ EStore

is the layering: a level mentions a name (`param`), a level list mentions
levels, an expression mentions all three.  The stores nest so that the
denotation signatures DESIGN §8.3 asks for (`denoteN : NStore → NIdx → …`,
`denoteE : EStore → EIdx → …`) are literally true.  Nesting costs nothing at
runtime: interning an expression node never touches the name arrays, because
an `ENodeView`'s children are handles.

## The derived word

`Tbl`'s `der` array holds, per node, exactly what con-leche caches on the
corresponding value:

* names — `ConLeche.Name.hashData`, a `UInt64`;
* levels and level lists — the `UInt64` hash *and* the has-a-parameter flag,
  because `Expr.data` reads both (`levelHash`/`levelHasParam` on a `.sort`,
  `levelsHash`/`levelsHaveParam` on a `.const`).  `ConLeche.Level` itself
  caches only the hash, so `LDer.hasParam` is an arena addition: con-leche
  recomputes `levelHasParam` by an `O(|u|)` walk at every node construction
  (`Kernel/Expr.lean:114-127`), which an interned store can do in `O(1)`;
* expressions — `ConLeche.Expr.data`, the packed
  `hash(32) | bvarB(15) | fvarB(15) | hasLP(1)` word, by the exact formulas of
  `Kernel/Expr.lean:356-402`.

Every formula below is a transliteration of con-leche's with `e.data` replaced
by `st.derived h`; that is what makes `derived_exact` (`WFProofs.lean`) a
ten-case `simp`.

## Memory discipline (DESIGN §8.4)

Every mutation detaches first — `let tb := t.f; let t := { t with f := .empty };
… tb.push …` — so the array and the table being grown are uniquely referenced
(lesson 14).  `Tbl.push` consumes its argument by `match`, for the same
reason.  Functions that hand out a whole table are `@[noinline]` (lesson 15).
No `for`, no `mut`, no `Nat` multiply (lessons 16, 7).
-/
import ConRon.Arena.Handle
import ConLeche.Kernel.Expr

namespace ConRon.Arena

open ConLeche

/-! ## The generic interned table

One constructor's array of one tier: the node records, the parallel derived
words, and the cons table from record to handle.  This is nanoda's
`UniqueIndexSet` (`util.rs:28`, `_tmp/t97/nanoda-design.md` §2) — "`Array A` +
`HashMap A Nat`, and that is how to build it in Lean" — plus the derived
column con-leche's lesson 1 keeps *outside* the cons key. -/

/-- con-leche: none — nanoda's `UniqueIndexSet<A>` (`util.rs:28-33`) with
con-leche's parallel derived array beside it (lesson 1: derived data never
lives inside the cons key). -/
structure Tbl (α : Type) [BEq α] [Hashable α] (ι : Type) (δ : Type) where
  nodes : Array α
  der : Array δ
  cons : Std.HashMap α ι

namespace Tbl

variable {α ι δ : Type} [BEq α] [Hashable α]

/-- con-leche: none — the empty table. -/
def empty : Tbl α ι δ := ⟨#[], #[], ∅⟩

instance : Inhabited (Tbl α ι δ) := ⟨empty⟩

/-- con-leche: none — how many nodes this constructor has in this tier. -/
@[inline] def size (t : Tbl α ι δ) : Nat := t.nodes.size

/-- con-leche: none — read one node record. -/
@[inline] def node? (t : Tbl α ι δ) (n : Nat) : Option α := t.nodes[n]?

/-- con-leche: none — read one derived word (`default` out of range; the
range is a `StoreWF` clause, so the fallback is never taken on a well-formed
store). -/
@[inline] def derAt [Inhabited δ] (t : Tbl α ι δ) (n : Nat) : δ :=
  t.der.getD n default

/-- con-leche: none — the cons-table probe. -/
@[inline] def find? (t : Tbl α ι δ) (a : α) : Option ι := t.cons[a]?

/-- con-leche: none — append a node with its derived word and register it in
the cons table.  `match` on the argument, not projections, so the three
components are uniquely referenced at the update (DESIGN §8.4 lesson 14). -/
def push (t : Tbl α ι δ) (a : α) (d : δ) (i : ι) : Tbl α ι δ :=
  match t with
  | ⟨ns, ds, cs⟩ => ⟨ns.push a, ds.push d, cs.insert a i⟩

end Tbl

/-! ## Names -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the `anonymous`
constructor, line 35. -/
structure AnonNode where
  mk ::
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the `str`
constructor, line 36. -/
structure StrNode where
  pre : NIdx
  s : String
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the `num`
constructor, line 37. -/
structure NumNode where
  pre : NIdx
  n : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : BEq AnonNode := instBEqOfDecidableEq
instance : BEq StrNode := instBEqOfDecidableEq
instance : BEq NumNode := instBEqOfDecidableEq

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the store-side view of a
name node: con-leche's three constructors with the prefix as a handle. -/
inductive NNodeView where
  | anonymous
  | str (pre : NIdx) (s : String)
  | num (pre : NIdx) (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: none — one tier of the name store. -/
structure NTables where
  anons : Tbl AnonNode NIdx UInt64
  strs : Tbl StrNode NIdx UInt64
  nums : Tbl NumNode NIdx UInt64

/-- con-leche: none — the name store: two tiers and the scratch flag
(DESIGN §8.3). -/
structure NStore where
  pers : NTables
  scr : NTables
  scratchOn : Bool

/-! ## Levels -/

/-- con-leche: ConLeche/Kernel/Expr.lean:41-46 Level — the `zero`
constructor, line 41. -/
structure ZeroNode where
  mk ::
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:41-46 Level — the `succ`
constructor, line 42. -/
structure SuccNode where
  u : LIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:41-46 Level — the `max` constructor,
line 43, and `imax`, line 44, which has the same two fields and therefore the
same record in its own array. -/
structure BinLNode where
  u : LIdx
  v : LIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:41-46 Level — the `param`
constructor, line 45. -/
structure ParamNode where
  n : NIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : BEq ZeroNode := instBEqOfDecidableEq
instance : BEq SuccNode := instBEqOfDecidableEq
instance : BEq BinLNode := instBEqOfDecidableEq
instance : BEq ParamNode := instBEqOfDecidableEq

/-- con-leche: ConLeche/Kernel/Expr.lean:41-46 Level — the store-side view of
a level node. -/
inductive LNodeView where
  | zero
  | succ (u : LIdx)
  | max (u v : LIdx)
  | imax (u v : LIdx)
  | param (n : NIdx)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the `hashData`
computed field, lines 47-53, plus the has-a-parameter flag, which con-leche
recomputes by a walk (`Kernel/Expr.lean:114-122 levelHasParam`) because a
`Level` tree has nowhere to cache it. -/
structure LDer where
  hash : UInt64
  hasParam : Bool
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: none — one tier of the level store. -/
structure LTables where
  zeros : Tbl ZeroNode LIdx LDer
  succs : Tbl SuccNode LIdx LDer
  maxs : Tbl BinLNode LIdx LDer
  imaxs : Tbl BinLNode LIdx LDer
  params : Tbl ParamNode LIdx LDer

/-- con-leche: none — the level store, over the name store. -/
structure LStore where
  ns : NStore
  pers : LTables
  scr : LTables
  scratchOn : Bool

/-! ## Level lists

One interned object per universe-argument list, so comparing two `const`
nodes' level arguments is one word comparison (nanoda's `LevelsPtr`,
`_tmp/t97/nanoda-design.md` §1).  A `List LIdx`, not an `Array LIdx` as
DESIGN §8.3 writes it: con-leche's `Expr.const` carries a `List Level`, so a
list node denotes pointwise with no `toList` in the statement, and `List` is
what `Std.HashMap`'s `BEq`/`Hashable` already handle. -/

/-- con-leche: none — the interned universe-argument list (nanoda's
`LevelsPtr`, `util.rs:84`). -/
structure ListNode where
  us : List LIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : BEq ListNode := instBEqOfDecidableEq

/-- con-leche: none — the store-side view of a level-list node. -/
abbrev LsNodeView := List LIdx

/-- con-leche: none — one tier of the level-list store (a single
constructor). -/
structure LsTables where
  lists : Tbl ListNode LsIdx LDer

/-- con-leche: none — the level-list store, over the level store. -/
structure LsStore where
  ls : LStore
  pers : LsTables
  scr : LsTables
  scratchOn : Bool

/-! ## Expressions -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `bvar`
constructor, line 344. -/
structure BVarNode where
  i : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `fvar`
constructor, line 345. -/
structure FVarNode where
  idx : Nat
  ty : EIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `sort`
constructor, line 346. -/
structure SortNode where
  u : LIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `const`
constructor, line 347. -/
structure ConstNode where
  n : NIdx
  us : LsIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `app`
constructor, line 348. -/
structure AppNode where
  f : EIdx
  a : EIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `lam`
constructor, line 349, and `forallE`, line 350: same three fields, its own
array. -/
structure BindNode where
  ty : EIdx
  body : EIdx
  m : ConLeche.BinderMeta
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `letE`
constructor, line 351. -/
structure LetNode where
  ty : EIdx
  val : EIdx
  body : EIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `lit`
constructor, line 352. -/
structure LitNode where
  l : ConLeche.Literal
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `proj`
constructor, line 353. -/
structure ProjNode where
  n : NIdx
  i : Nat
  e : EIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : BEq BVarNode := instBEqOfDecidableEq
instance : BEq FVarNode := instBEqOfDecidableEq
instance : BEq SortNode := instBEqOfDecidableEq
instance : BEq ConstNode := instBEqOfDecidableEq
instance : BEq AppNode := instBEqOfDecidableEq
instance : BEq BindNode := instBEqOfDecidableEq
instance : BEq LetNode := instBEqOfDecidableEq
instance : BEq LitNode := instBEqOfDecidableEq
instance : BEq ProjNode := instBEqOfDecidableEq

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the store-side view of
an expression node: con-leche's ten constructors with every subterm replaced
by a handle.  `BinderMeta` and `Literal` stay *values* (they are not
expressions), exactly as DESIGN §8.3 specifies. -/
inductive ENodeView where
  | bvar (i : Nat)
  | fvar (idx : Nat) (ty : EIdx)
  | sort (u : LIdx)
  | const (n : NIdx) (us : LsIdx)
  | app (f a : EIdx)
  | lam (ty body : EIdx) (m : ConLeche.BinderMeta)
  | forallE (ty body : EIdx) (m : ConLeche.BinderMeta)
  | letE (ty val body : EIdx)
  | lit (l : ConLeche.Literal)
  | proj (n : NIdx) (i : Nat) (e : EIdx)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: none — one tier of the expression store: ten arrays, ten
derived columns, ten cons tables. -/
structure ETables where
  bvars : Tbl BVarNode EIdx UInt64
  fvars : Tbl FVarNode EIdx UInt64
  sorts : Tbl SortNode EIdx UInt64
  consts : Tbl ConstNode EIdx UInt64
  apps : Tbl AppNode EIdx UInt64
  lams : Tbl BindNode EIdx UInt64
  foralls : Tbl BindNode EIdx UInt64
  lets : Tbl LetNode EIdx UInt64
  lits : Tbl LitNode EIdx UInt64
  projs : Tbl ProjNode EIdx UInt64

/-- con-leche: none — the expression store, over the level-list store.  Two
tiers: persistent (parse + installed environment) and scratch (one
declaration's check), the tier bit of a handle selecting between them
(DESIGN §8.3). -/
structure EStore where
  lss : LsStore
  pers : ETables
  scr : ETables
  scratchOn : Bool

/-! ## The name store's operations -/

namespace NTables

/-- con-leche: none — the empty tier. -/
def empty : NTables := ⟨.empty, .empty, .empty⟩

instance : Inhabited NTables := ⟨empty⟩

/-- con-leche: none — nodes in this tier, over all constructors. -/
def count (t : NTables) : Nat := t.anons.size + t.strs.size + t.nums.size

/-- con-leche: none — decode one handle against this tier's arrays.  The tier
bit is *not* consulted: `NStore.view` selects the tier first. -/
@[inline] def get (t : NTables) (i : NIdx) : Option NNodeView :=
  if i.tag == NTag.anonymous then (t.anons.node? i.idxNat).map fun _ => .anonymous
  else if i.tag == NTag.str then (t.strs.node? i.idxNat).map fun r => .str r.pre r.s
  else if i.tag == NTag.num then (t.nums.node? i.idxNat).map fun r => .num r.pre r.n
  else none

/-- con-leche: none — the derived word of one handle in this tier. -/
@[inline] def derAt (t : NTables) (i : NIdx) : UInt64 :=
  if i.tag == NTag.anonymous then t.anons.derAt i.idxNat
  else if i.tag == NTag.str then t.strs.derAt i.idxNat
  else if i.tag == NTag.num then t.nums.derAt i.idxNat
  else 0

/-- con-leche: none — the cons-table probe for a whole node view. -/
def find? (t : NTables) (v : NNodeView) : Option NIdx :=
  match v with
  | .anonymous => t.anons.find? .mk
  | .str p s => t.strs.find? ⟨p, s⟩
  | .num p n => t.nums.find? ⟨p, n⟩

/-- con-leche: none — the size of the constructor array `v` would land in;
`StoreWF`'s capacity clause is stated on it. -/
def sizeOf (t : NTables) (v : NNodeView) : Nat :=
  match v with
  | .anonymous => t.anons.size
  | .str _ _ => t.strs.size
  | .num _ _ => t.nums.size

/-- con-leche: none — append a node to this tier, returning its handle.
Detach-before-update on the one table touched (DESIGN §8.4 lesson 14). -/
@[noinline] def push (t : NTables) (v : NNodeView) (d : UInt64) (tier : UInt32) :
    NTables × NIdx :=
  match v with
  | .anonymous =>
    let tb := t.anons
    let i : NIdx := Idx.mk NTag.anonymous tier (UInt32.ofNat tb.size)
    let t := { t with anons := Tbl.empty }
    ({ t with anons := tb.push .mk d i }, i)
  | .str p s =>
    let tb := t.strs
    let i : NIdx := Idx.mk NTag.str tier (UInt32.ofNat tb.size)
    let t := { t with strs := Tbl.empty }
    ({ t with strs := tb.push ⟨p, s⟩ d i }, i)
  | .num p n =>
    let tb := t.nums
    let i : NIdx := Idx.mk NTag.num tier (UInt32.ofNat tb.size)
    let t := { t with nums := Tbl.empty }
    ({ t with nums := tb.push ⟨p, n⟩ d i }, i)

end NTables

namespace NStore

/-- con-leche: none — the empty name store. -/
def empty : NStore := ⟨.empty, .empty, false⟩

instance : Inhabited NStore := ⟨empty⟩

/-- con-leche: none — nodes in the persistent tier. -/
@[inline] def persCount (st : NStore) : Nat := st.pers.count
/-- con-leche: none — nodes in the scratch tier. -/
@[inline] def scrCount (st : NStore) : Nat := st.scr.count
/-- con-leche: none — nodes in both tiers; the fuel bound `denoteN` uses. -/
@[inline] def nodeCount (st : NStore) : Nat := st.persCount + st.scrCount

/-- con-leche: none — decode a handle: the tier bit selects the array set,
and a scratch handle reads as absent while the scratch tier is off. -/
@[inline] def view (st : NStore) (i : NIdx) : Option NNodeView :=
  if i.isPersistent then st.pers.get i
  else if st.scratchOn then st.scr.get i else none

/-- con-leche: ConLeche/Kernel/Name.lean:34-44 Name — the `hashData` computed
field, lines 41-44: the derived word of a handle. -/
@[inline] def derived (st : NStore) (i : NIdx) : UInt64 :=
  if i.isPersistent then st.pers.derAt i
  else if st.scratchOn then st.scr.derAt i else 0

/-- con-leche: ConLeche/Kernel/Name.lean:34-44 Name — the `hashData` computed
field, lines 41-44: the derived word a node view *would* get, computed in
`O(1)` from the children's. -/
def derOfView (st : NStore) (v : NNodeView) : UInt64 :=
  match v with
  | .anonymous => 1723
  | .str p s => mixHash (mixHash 1 (st.derived p)) (hash s)
  | .num p n => mixHash (mixHash 2 (st.derived p)) (hash n)

/-- con-leche: none — probe both tiers, persistent first (nanoda's
`alloc_name`, `util.rs:372-378`: "checks the longer-lived storage first"). -/
def find? (st : NStore) (v : NNodeView) : Option NIdx :=
  match st.pers.find? v with
  | some i => some i
  | none => if st.scratchOn then st.scr.find? v else none

/-- con-leche: none — hash-cons a name node: probe persistent, then scratch,
then append to the tier the store is in. -/
def intern (st : NStore) (v : NNodeView) : NStore × NIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    if st.scratchOn then
      match st.scr.find? v with
      | some i => (st, i)
      | none =>
        let d := st.derOfView v
        let tb := st.scr
        let st := { st with scr := NTables.empty }
        let (tb, i) := tb.push v d Idx.tierS
        ({ st with scr := tb }, i)
    else
      let d := st.derOfView v
      let tb := st.pers
      let st := { st with pers := NTables.empty }
      let (tb, i) := tb.push v d Idx.tierP
      ({ st with pers := tb }, i)

/-- con-leche: none — open the scratch tier (DESIGN §8.3's per-declaration
bracket). -/
def enableScratch (st : NStore) : NStore :=
  { st with scr := NTables.empty, scratchOn := true }

/-- con-leche: none — drop the scratch tier: truncate its arrays and clear its
tables.  Persistent handles keep their bits (DESIGN §8.3, lesson 6). -/
def dropScratch (st : NStore) : NStore :=
  { st with scr := NTables.empty, scratchOn := false }

/-- con-leche: none — the capacity precondition of `intern`: the constructor's
array in the tier being appended to has room for one more node.  The checker
tier (P2c) tests it and raises `Native`; the pure store op assumes it. -/
def capOK (st : NStore) (v : NNodeView) : Prop :=
  (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

end NStore

/-! ## The level store's operations -/

namespace LTables

/-- con-leche: none — the empty tier. -/
def empty : LTables := ⟨.empty, .empty, .empty, .empty, .empty⟩

instance : Inhabited LTables := ⟨empty⟩

/-- con-leche: none — nodes in this tier, over all constructors. -/
def count (t : LTables) : Nat :=
  t.zeros.size + t.succs.size + t.maxs.size + t.imaxs.size + t.params.size

/-- con-leche: none — decode one handle against this tier's arrays. -/
@[inline] def get (t : LTables) (i : LIdx) : Option LNodeView :=
  if i.tag == LTag.zero then (t.zeros.node? i.idxNat).map fun _ => .zero
  else if i.tag == LTag.succ then (t.succs.node? i.idxNat).map fun r => .succ r.u
  else if i.tag == LTag.max then (t.maxs.node? i.idxNat).map fun r => .max r.u r.v
  else if i.tag == LTag.imax then (t.imaxs.node? i.idxNat).map fun r => .imax r.u r.v
  else if i.tag == LTag.param then (t.params.node? i.idxNat).map fun r => .param r.n
  else none

/-- con-leche: none — the derived record of one handle in this tier. -/
@[inline] def derAt (t : LTables) (i : LIdx) : LDer :=
  if i.tag == LTag.zero then t.zeros.derAt i.idxNat
  else if i.tag == LTag.succ then t.succs.derAt i.idxNat
  else if i.tag == LTag.max then t.maxs.derAt i.idxNat
  else if i.tag == LTag.imax then t.imaxs.derAt i.idxNat
  else if i.tag == LTag.param then t.params.derAt i.idxNat
  else default

/-- con-leche: none — the cons-table probe for a whole node view. -/
def find? (t : LTables) (v : LNodeView) : Option LIdx :=
  match v with
  | .zero => t.zeros.find? .mk
  | .succ u => t.succs.find? ⟨u⟩
  | .max u v => t.maxs.find? ⟨u, v⟩
  | .imax u v => t.imaxs.find? ⟨u, v⟩
  | .param n => t.params.find? ⟨n⟩

/-- con-leche: none — the size of the constructor array `v` would land in. -/
def sizeOf (t : LTables) (v : LNodeView) : Nat :=
  match v with
  | .zero => t.zeros.size
  | .succ _ => t.succs.size
  | .max _ _ => t.maxs.size
  | .imax _ _ => t.imaxs.size
  | .param _ => t.params.size

/-- con-leche: none — append a level node to this tier. -/
@[noinline] def push (t : LTables) (v : LNodeView) (d : LDer) (tier : UInt32) :
    LTables × LIdx :=
  match v with
  | .zero =>
    let tb := t.zeros
    let i : LIdx := Idx.mk LTag.zero tier (UInt32.ofNat tb.size)
    let t := { t with zeros := Tbl.empty }
    ({ t with zeros := tb.push .mk d i }, i)
  | .succ u =>
    let tb := t.succs
    let i : LIdx := Idx.mk LTag.succ tier (UInt32.ofNat tb.size)
    let t := { t with succs := Tbl.empty }
    ({ t with succs := tb.push ⟨u⟩ d i }, i)
  | .max u v =>
    let tb := t.maxs
    let i : LIdx := Idx.mk LTag.max tier (UInt32.ofNat tb.size)
    let t := { t with maxs := Tbl.empty }
    ({ t with maxs := tb.push ⟨u, v⟩ d i }, i)
  | .imax u v =>
    let tb := t.imaxs
    let i : LIdx := Idx.mk LTag.imax tier (UInt32.ofNat tb.size)
    let t := { t with imaxs := Tbl.empty }
    ({ t with imaxs := tb.push ⟨u, v⟩ d i }, i)
  | .param n =>
    let tb := t.params
    let i : LIdx := Idx.mk LTag.param tier (UInt32.ofNat tb.size)
    let t := { t with params := Tbl.empty }
    ({ t with params := tb.push ⟨n⟩ d i }, i)

end LTables

namespace LStore

/-- con-leche: none — the empty level store. -/
def empty : LStore := ⟨.empty, .empty, .empty, false⟩

instance : Inhabited LStore := ⟨empty⟩

/-- con-leche: none — nodes in the persistent tier. -/
@[inline] def persCount (st : LStore) : Nat := st.pers.count
/-- con-leche: none — nodes in the scratch tier. -/
@[inline] def scrCount (st : LStore) : Nat := st.scr.count
/-- con-leche: none — the fuel bound `denoteL` uses. -/
@[inline] def nodeCount (st : LStore) : Nat := st.persCount + st.scrCount

/-- con-leche: none — decode a level handle. -/
@[inline] def view (st : LStore) (i : LIdx) : Option LNodeView :=
  if i.isPersistent then st.pers.get i
  else if st.scratchOn then st.scr.get i else none

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the `hashData` computed
field, lines 47-53: the derived record of a level handle. -/
@[inline] def derived (st : LStore) (i : LIdx) : LDer :=
  if i.isPersistent then st.pers.derAt i
  else if st.scratchOn then st.scr.derAt i else default

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the `hashData` computed
field, lines 47-53, and `Kernel/Expr.lean:114-122 levelHasParam`: the derived
record a node view would get, in `O(1)` from the children's. -/
def derOfView (st : LStore) (v : LNodeView) : LDer :=
  match v with
  | .zero => ⟨1, false⟩
  | .succ u => ⟨mixHash 3 (st.derived u).hash, (st.derived u).hasParam⟩
  | .max u v =>
    ⟨mixHash 5 (mixHash (st.derived u).hash (st.derived v).hash),
     (st.derived u).hasParam || (st.derived v).hasParam⟩
  | .imax u v =>
    ⟨mixHash 7 (mixHash (st.derived u).hash (st.derived v).hash),
     (st.derived u).hasParam || (st.derived v).hasParam⟩
  | .param n => ⟨mixHash 11 (st.ns.derived n), true⟩

/-- con-leche: none — probe both tiers, persistent first. -/
def find? (st : LStore) (v : LNodeView) : Option LIdx :=
  match st.pers.find? v with
  | some i => some i
  | none => if st.scratchOn then st.scr.find? v else none

/-- con-leche: none — hash-cons a level node. -/
def intern (st : LStore) (v : LNodeView) : LStore × LIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    if st.scratchOn then
      match st.scr.find? v with
      | some i => (st, i)
      | none =>
        let d := st.derOfView v
        let tb := st.scr
        let st := { st with scr := LTables.empty }
        let (tb, i) := tb.push v d Idx.tierS
        ({ st with scr := tb }, i)
    else
      let d := st.derOfView v
      let tb := st.pers
      let st := { st with pers := LTables.empty }
      let (tb, i) := tb.push v d Idx.tierP
      ({ st with pers := tb }, i)

/-- con-leche: none — open the scratch tier, here and in the name store. -/
def enableScratch (st : LStore) : LStore :=
  { st with ns := st.ns.enableScratch, scr := LTables.empty, scratchOn := true }

/-- con-leche: none — drop the scratch tier, here and in the name store. -/
def dropScratch (st : LStore) : LStore :=
  { st with ns := st.ns.dropScratch, scr := LTables.empty, scratchOn := false }

/-- con-leche: none — `intern`'s capacity precondition. -/
def capOK (st : LStore) (v : LNodeView) : Prop :=
  (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

end LStore

/-! ## The level-list store's operations -/

namespace LsTables

/-- con-leche: none — the empty tier. -/
def empty : LsTables := ⟨.empty⟩

instance : Inhabited LsTables := ⟨empty⟩

/-- con-leche: none — nodes in this tier. -/
def count (t : LsTables) : Nat := t.lists.size

/-- con-leche: none — decode one handle against this tier's array. -/
@[inline] def get (t : LsTables) (i : LsIdx) : Option LsNodeView :=
  if i.tag == LsTag.list then (t.lists.node? i.idxNat).map fun r => r.us
  else none

/-- con-leche: none — the derived record of one handle in this tier. -/
@[inline] def derAt (t : LsTables) (i : LsIdx) : LDer :=
  if i.tag == LsTag.list then t.lists.derAt i.idxNat else default

/-- con-leche: none — the cons-table probe. -/
def find? (t : LsTables) (v : LsNodeView) : Option LsIdx := t.lists.find? ⟨v⟩

/-- con-leche: none — the size of the array `v` would land in. -/
def sizeOf (t : LsTables) (_v : LsNodeView) : Nat := t.lists.size

/-- con-leche: none — append a level-list node to this tier. -/
@[noinline] def push (t : LsTables) (v : LsNodeView) (d : LDer) (tier : UInt32) :
    LsTables × LsIdx :=
  let tb := t.lists
  let i : LsIdx := Idx.mk LsTag.list tier (UInt32.ofNat tb.size)
  let t := { t with lists := Tbl.empty }
  ({ t with lists := tb.push ⟨v⟩ d i }, i)

end LsTables

namespace LsStore

/-- con-leche: none — the empty level-list store. -/
def empty : LsStore := ⟨.empty, .empty, .empty, false⟩

instance : Inhabited LsStore := ⟨empty⟩

/-- con-leche: none — nodes in the persistent tier. -/
@[inline] def persCount (st : LsStore) : Nat := st.pers.count
/-- con-leche: none — nodes in the scratch tier. -/
@[inline] def scrCount (st : LsStore) : Nat := st.scr.count
/-- con-leche: none — the fuel bound `denoteLs` uses. -/
@[inline] def nodeCount (st : LsStore) : Nat := st.persCount + st.scrCount

/-- con-leche: none — the name store underneath. -/
@[inline] def ns (st : LsStore) : NStore := st.ls.ns

/-- con-leche: none — decode a level-list handle. -/
@[inline] def view (st : LsStore) (i : LsIdx) : Option LsNodeView :=
  if i.isPersistent then st.pers.get i
  else if st.scratchOn then st.scr.get i else none

/-- con-leche: ConLeche/Kernel/Expr.lean:137-140 levelsHash — the derived
record of a level-list handle. -/
@[inline] def derived (st : LsStore) (i : LsIdx) : LDer :=
  if i.isPersistent then st.pers.derAt i
  else if st.scratchOn then st.scr.derAt i else default

/-- con-leche: ConLeche/Kernel/Expr.lean:137-140 levelsHash — and
`Kernel/Expr.lean:125-127 levelsHaveParam`: the derived record a level list
would get.  `O(n)` in the list, as con-leche's own fold is. -/
def derOfView (st : LsStore) : LsNodeView → LDer
  | [] => ⟨13, false⟩
  | u :: us =>
    let hu := st.ls.derived u
    let hr := derOfView st us
    ⟨mixHash hu.hash hr.hash, hu.hasParam || hr.hasParam⟩

/-- con-leche: none — probe both tiers, persistent first. -/
def find? (st : LsStore) (v : LsNodeView) : Option LsIdx :=
  match st.pers.find? v with
  | some i => some i
  | none => if st.scratchOn then st.scr.find? v else none

/-- con-leche: none — hash-cons a level list. -/
def intern (st : LsStore) (v : LsNodeView) : LsStore × LsIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    if st.scratchOn then
      match st.scr.find? v with
      | some i => (st, i)
      | none =>
        let d := st.derOfView v
        let tb := st.scr
        let st := { st with scr := LsTables.empty }
        let (tb, i) := tb.push v d Idx.tierS
        ({ st with scr := tb }, i)
    else
      let d := st.derOfView v
      let tb := st.pers
      let st := { st with pers := LsTables.empty }
      let (tb, i) := tb.push v d Idx.tierP
      ({ st with pers := tb }, i)

/-- con-leche: none — open the scratch tier, here and below. -/
def enableScratch (st : LsStore) : LsStore :=
  { st with ls := st.ls.enableScratch, scr := LsTables.empty, scratchOn := true }

/-- con-leche: none — drop the scratch tier, here and below. -/
def dropScratch (st : LsStore) : LsStore :=
  { st with ls := st.ls.dropScratch, scr := LsTables.empty, scratchOn := false }

/-- con-leche: none — `intern`'s capacity precondition. -/
def capOK (st : LsStore) (v : LsNodeView) : Prop :=
  (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

end LsStore

/-! ## The expression store's operations -/

namespace ETables

/-- con-leche: none — the empty tier. -/
def empty : ETables :=
  ⟨.empty, .empty, .empty, .empty, .empty, .empty, .empty, .empty, .empty, .empty⟩

instance : Inhabited ETables := ⟨empty⟩

/-- con-leche: none — nodes in this tier, over all ten constructors. -/
def count (t : ETables) : Nat :=
  t.bvars.size + t.fvars.size + t.sorts.size + t.consts.size + t.apps.size
    + t.lams.size + t.foralls.size + t.lets.size + t.lits.size + t.projs.size

/-- con-leche: none — decode one handle against this tier's arrays: read the
tag, index one array, build the view.  There is no node enum in the store
(DESIGN §8.3). -/
@[inline] def get (t : ETables) (i : EIdx) : Option ENodeView :=
  if i.tag == ETag.bvar then (t.bvars.node? i.idxNat).map fun r => .bvar r.i
  else if i.tag == ETag.fvar then (t.fvars.node? i.idxNat).map fun r => .fvar r.idx r.ty
  else if i.tag == ETag.sort then (t.sorts.node? i.idxNat).map fun r => .sort r.u
  else if i.tag == ETag.const then (t.consts.node? i.idxNat).map fun r => .const r.n r.us
  else if i.tag == ETag.app then (t.apps.node? i.idxNat).map fun r => .app r.f r.a
  else if i.tag == ETag.lam then (t.lams.node? i.idxNat).map fun r => .lam r.ty r.body r.m
  else if i.tag == ETag.forallE then
    (t.foralls.node? i.idxNat).map fun r => .forallE r.ty r.body r.m
  else if i.tag == ETag.letE then
    (t.lets.node? i.idxNat).map fun r => .letE r.ty r.val r.body
  else if i.tag == ETag.lit then (t.lits.node? i.idxNat).map fun r => .lit r.l
  else if i.tag == ETag.proj then (t.projs.node? i.idxNat).map fun r => .proj r.n r.i r.e
  else none

/-- con-leche: none — the derived word of one handle in this tier. -/
@[inline] def derAt (t : ETables) (i : EIdx) : UInt64 :=
  if i.tag == ETag.bvar then t.bvars.derAt i.idxNat
  else if i.tag == ETag.fvar then t.fvars.derAt i.idxNat
  else if i.tag == ETag.sort then t.sorts.derAt i.idxNat
  else if i.tag == ETag.const then t.consts.derAt i.idxNat
  else if i.tag == ETag.app then t.apps.derAt i.idxNat
  else if i.tag == ETag.lam then t.lams.derAt i.idxNat
  else if i.tag == ETag.forallE then t.foralls.derAt i.idxNat
  else if i.tag == ETag.letE then t.lets.derAt i.idxNat
  else if i.tag == ETag.lit then t.lits.derAt i.idxNat
  else if i.tag == ETag.proj then t.projs.derAt i.idxNat
  else 0

/-- con-leche: none — the cons-table probe for a whole node view. -/
def find? (t : ETables) (v : ENodeView) : Option EIdx :=
  match v with
  | .bvar i => t.bvars.find? ⟨i⟩
  | .fvar idx ty => t.fvars.find? ⟨idx, ty⟩
  | .sort u => t.sorts.find? ⟨u⟩
  | .const n us => t.consts.find? ⟨n, us⟩
  | .app f a => t.apps.find? ⟨f, a⟩
  | .lam ty b m => t.lams.find? ⟨ty, b, m⟩
  | .forallE ty b m => t.foralls.find? ⟨ty, b, m⟩
  | .letE ty v b => t.lets.find? ⟨ty, v, b⟩
  | .lit l => t.lits.find? ⟨l⟩
  | .proj n i e => t.projs.find? ⟨n, i, e⟩

/-- con-leche: none — the size of the constructor array `v` would land in. -/
def sizeOf (t : ETables) (v : ENodeView) : Nat :=
  match v with
  | .bvar _ => t.bvars.size
  | .fvar _ _ => t.fvars.size
  | .sort _ => t.sorts.size
  | .const _ _ => t.consts.size
  | .app _ _ => t.apps.size
  | .lam _ _ _ => t.lams.size
  | .forallE _ _ _ => t.foralls.size
  | .letE _ _ _ => t.lets.size
  | .lit _ => t.lits.size
  | .proj _ _ _ => t.projs.size

/-- con-leche: none — append an expression node to this tier. -/
@[noinline] def push (t : ETables) (v : ENodeView) (d : UInt64) (tier : UInt32) :
    ETables × EIdx :=
  match v with
  | .bvar i =>
    let tb := t.bvars
    let h : EIdx := Idx.mk ETag.bvar tier (UInt32.ofNat tb.size)
    let t := { t with bvars := Tbl.empty }
    ({ t with bvars := tb.push ⟨i⟩ d h }, h)
  | .fvar idx ty =>
    let tb := t.fvars
    let h : EIdx := Idx.mk ETag.fvar tier (UInt32.ofNat tb.size)
    let t := { t with fvars := Tbl.empty }
    ({ t with fvars := tb.push ⟨idx, ty⟩ d h }, h)
  | .sort u =>
    let tb := t.sorts
    let h : EIdx := Idx.mk ETag.sort tier (UInt32.ofNat tb.size)
    let t := { t with sorts := Tbl.empty }
    ({ t with sorts := tb.push ⟨u⟩ d h }, h)
  | .const n us =>
    let tb := t.consts
    let h : EIdx := Idx.mk ETag.const tier (UInt32.ofNat tb.size)
    let t := { t with consts := Tbl.empty }
    ({ t with consts := tb.push ⟨n, us⟩ d h }, h)
  | .app f a =>
    let tb := t.apps
    let h : EIdx := Idx.mk ETag.app tier (UInt32.ofNat tb.size)
    let t := { t with apps := Tbl.empty }
    ({ t with apps := tb.push ⟨f, a⟩ d h }, h)
  | .lam ty b m =>
    let tb := t.lams
    let h : EIdx := Idx.mk ETag.lam tier (UInt32.ofNat tb.size)
    let t := { t with lams := Tbl.empty }
    ({ t with lams := tb.push ⟨ty, b, m⟩ d h }, h)
  | .forallE ty b m =>
    let tb := t.foralls
    let h : EIdx := Idx.mk ETag.forallE tier (UInt32.ofNat tb.size)
    let t := { t with foralls := Tbl.empty }
    ({ t with foralls := tb.push ⟨ty, b, m⟩ d h }, h)
  | .letE ty v b =>
    let tb := t.lets
    let h : EIdx := Idx.mk ETag.letE tier (UInt32.ofNat tb.size)
    let t := { t with lets := Tbl.empty }
    ({ t with lets := tb.push ⟨ty, v, b⟩ d h }, h)
  | .lit l =>
    let tb := t.lits
    let h : EIdx := Idx.mk ETag.lit tier (UInt32.ofNat tb.size)
    let t := { t with lits := Tbl.empty }
    ({ t with lits := tb.push ⟨l⟩ d h }, h)
  | .proj n i e =>
    let tb := t.projs
    let h : EIdx := Idx.mk ETag.proj tier (UInt32.ofNat tb.size)
    let t := { t with projs := Tbl.empty }
    ({ t with projs := tb.push ⟨n, i, e⟩ d h }, h)

end ETables

namespace EStore

/-- con-leche: none — the empty expression store. -/
def empty : EStore := ⟨.empty, .empty, .empty, false⟩

instance : Inhabited EStore := ⟨empty⟩

/-- con-leche: none — nodes in the persistent tier. -/
@[inline] def persCount (st : EStore) : Nat := st.pers.count
/-- con-leche: none — nodes in the scratch tier. -/
@[inline] def scrCount (st : EStore) : Nat := st.scr.count
/-- con-leche: none — the fuel bound `denoteE` uses. -/
@[inline] def nodeCount (st : EStore) : Nat := st.persCount + st.scrCount

/-- con-leche: none — the level-list store underneath. -/
@[inline] def lsS (st : EStore) : LsStore := st.lss
/-- con-leche: none — the level store underneath. -/
@[inline] def ls (st : EStore) : LStore := st.lss.ls
/-- con-leche: none — the name store underneath. -/
@[inline] def ns (st : EStore) : NStore := st.lss.ls.ns

/-- con-leche: none — a name's derived word, read through the nesting. -/
@[inline] def nder (st : EStore) (i : NIdx) : UInt64 := st.ns.derived i
/-- con-leche: none — a level's derived record. -/
@[inline] def lder (st : EStore) (i : LIdx) : LDer := st.ls.derived i
/-- con-leche: none — a level list's derived record. -/
@[inline] def lsder (st : EStore) (i : LsIdx) : LDer := st.lss.derived i

/-- con-leche: none — decode an expression handle: the tier bit selects the
array set, the tag selects the array, the index reads it. -/
@[inline] def view (st : EStore) (i : EIdx) : Option ENodeView :=
  if i.isPersistent then st.pers.get i
  else if st.scratchOn then st.scr.get i else none

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `data` computed
field, lines 357-402: the packed derived word of an expression handle. -/
@[inline] def derived (st : EStore) (i : EIdx) : UInt64 :=
  if i.isPersistent then st.pers.derAt i
  else if st.scratchOn then st.scr.derAt i else 0

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `data` computed
field, lines 357-402: **the formulas, verbatim**, with `e.data` replaced by
`st.derived h` and the level/name reads replaced by the corresponding
stores' derived columns:

* `levelHash u` ↦ `(st.lder u).hash`, `levelHasParam u` ↦ `(st.lder u).hasParam`;
* `Hashable.hash (n : Name)` ↦ `st.nder n` (the `Hashable Name` instance
  *is* `Name.hashData`, `Kernel/Name.lean:49`);
* `levelsHash us` ↦ `(st.lsder us).hash`, `levelsHaveParam us` ↦
  `(st.lsder us).hasParam`.

`derived_exact` (`WFProofs.lean`) is then one `simp` per constructor. -/
def derOfView (st : EStore) (v : ENodeView) : UInt64 :=
  match v with
  | .bvar i =>
    packData (hash32 (mixHash 3 (hash i))) (satSucc i) 0 false
  | .fvar idx ty =>
    packData (hash32 (mixHash 5 (mixHash (hash idx) (hashOfData (st.derived ty)))))
      0 (satSucc idx) (lpOfData (st.derived ty))
  | .sort u =>
    packData (hash32 (mixHash 7 (st.lder u).hash)) 0 0 (st.lder u).hasParam
  | .const n us =>
    packData (hash32 (mixHash 11 (mixHash (st.nder n) (st.lsder us).hash)))
      0 0 (st.lsder us).hasParam
  | .app f a =>
    packData (hash32 (mixHash 17
        (mixHash (hashOfData (st.derived f)) (hashOfData (st.derived a)))))
      (max (bvarOfData (st.derived f)) (bvarOfData (st.derived a)))
      (max (fvarOfData (st.derived f)) (fvarOfData (st.derived a)))
      (lpOfData (st.derived f) || lpOfData (st.derived a))
  | .lam ty b m =>
    packData (hash32 (mixHash 19
        (mixHash (hashOfData (st.derived ty))
          (mixHash (hashOfData (st.derived b)) (hash m.pw)))))
      (max (bvarOfData (st.derived ty)) (satPred (bvarOfData (st.derived b))))
      (max (fvarOfData (st.derived ty)) (fvarOfData (st.derived b)))
      (lpOfData (st.derived ty) || lpOfData (st.derived b) || m.pw.hasParams)
  | .forallE ty b m =>
    packData (hash32 (mixHash 23
        (mixHash (hashOfData (st.derived ty))
          (mixHash (hashOfData (st.derived b)) (hash m.pw)))))
      (max (bvarOfData (st.derived ty)) (satPred (bvarOfData (st.derived b))))
      (max (fvarOfData (st.derived ty)) (fvarOfData (st.derived b)))
      (lpOfData (st.derived ty) || lpOfData (st.derived b) || m.pw.hasParams)
  | .letE ty v b =>
    packData (hash32 (mixHash 29
        (mixHash (hashOfData (st.derived ty))
          (mixHash (hashOfData (st.derived v)) (hashOfData (st.derived b))))))
      (max (max (bvarOfData (st.derived ty)) (bvarOfData (st.derived v)))
        (satPred (bvarOfData (st.derived b))))
      (max (max (fvarOfData (st.derived ty)) (fvarOfData (st.derived v)))
        (fvarOfData (st.derived b)))
      (lpOfData (st.derived ty) || lpOfData (st.derived v) || lpOfData (st.derived b))
  | .lit l =>
    packData (hash32 (mixHash 31 (hash l))) 0 0 false
  | .proj s i e =>
    packData (hash32 (mixHash 37 (mixHash (st.nder s)
        (mixHash (hash i) (hashOfData (st.derived e))))))
      (bvarOfData (st.derived e)) (fvarOfData (st.derived e)) (lpOfData (st.derived e))

/-- con-leche: none — probe both tiers, persistent first (nanoda's
`alloc_expr`, `util.rs:391-400`). -/
def find? (st : EStore) (v : ENodeView) : Option EIdx :=
  match st.pers.find? v with
  | some i => some i
  | none => if st.scratchOn then st.scr.find? v else none

/-- con-leche: none — hash-cons an expression node: probe the persistent cons
table, then the scratch one, then append to the tier the store is in
(DESIGN §8.3; nanoda `util.rs:391-400`). -/
def intern (st : EStore) (v : ENodeView) : EStore × EIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    if st.scratchOn then
      match st.scr.find? v with
      | some i => (st, i)
      | none =>
        let d := st.derOfView v
        let tb := st.scr
        let st := { st with scr := ETables.empty }
        let (tb, i) := tb.push v d Idx.tierS
        ({ st with scr := tb }, i)
    else
      let d := st.derOfView v
      let tb := st.pers
      let st := { st with pers := ETables.empty }
      let (tb, i) := tb.push v d Idx.tierP
      ({ st with pers := tb }, i)

/-- con-leche: none — open the scratch tier, in all four stores.  DESIGN §8.3:
"each tier has its own array set and cons tables, both indexed from 0". -/
def enableScratch (st : EStore) : EStore :=
  { st with lss := st.lss.enableScratch, scr := ETables.empty, scratchOn := true }

/-- con-leche: none — drop the scratch tier, in all four stores: truncate the
arrays to length 0 and clear the tables.  Persistent handles keep their bits,
so everything that denoted before still denotes (DESIGN §8.3, lesson 6). -/
def dropScratch (st : EStore) : EStore :=
  { st with lss := st.lss.dropScratch, scr := ETables.empty, scratchOn := false }

/-- con-leche: none — `intern`'s capacity precondition (2^27 nodes per
constructor per tier).  The checker tier (P2c) tests it and raises `Native`;
the pure store op assumes it, which is what keeps `intern`'s signature
total. -/
def capOK (st : EStore) (v : ENodeView) : Prop :=
  (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap

end EStore

/-! ## Interning through the nesting

The parser and the checker hold one `EStore` and intern into all four levels
of it, so each level gets a lifted `intern*`.  Every one detaches the nested
store before handing it to the level below (DESIGN §8.4 lesson 14) and is
`@[noinline]` (lesson 15). -/

/-- con-leche: none — intern a name from the level store. -/
@[noinline] def LStore.internName (st : LStore) (v : NNodeView) : LStore × NIdx :=
  let ns := st.ns
  let st := { st with ns := NStore.empty }
  let (ns, i) := ns.intern v
  ({ st with ns := ns }, i)

/-- con-leche: none — intern a name from the level-list store. -/
@[noinline] def LsStore.internName (st : LsStore) (v : NNodeView) :
    LsStore × NIdx :=
  let ls := st.ls
  let st := { st with ls := LStore.empty }
  let (ls, i) := ls.internName v
  ({ st with ls := ls }, i)

/-- con-leche: none — intern a level from the level-list store. -/
@[noinline] def LsStore.internLevel (st : LsStore) (v : LNodeView) :
    LsStore × LIdx :=
  let ls := st.ls
  let st := { st with ls := LStore.empty }
  let (ls, i) := ls.intern v
  ({ st with ls := ls }, i)

/-- con-leche: none — intern a name from the expression store. -/
@[noinline] def EStore.internName (st : EStore) (v : NNodeView) : EStore × NIdx :=
  let lss := st.lss
  let st := { st with lss := LsStore.empty }
  let (lss, i) := lss.internName v
  ({ st with lss := lss }, i)

/-- con-leche: none — intern a level from the expression store. -/
@[noinline] def EStore.internLevel (st : EStore) (v : LNodeView) : EStore × LIdx :=
  let lss := st.lss
  let st := { st with lss := LsStore.empty }
  let (lss, i) := lss.internLevel v
  ({ st with lss := lss }, i)

/-- con-leche: none — intern a universe-argument list from the expression
store. -/
@[noinline] def EStore.internLevels (st : EStore) (v : LsNodeView) :
    EStore × LsIdx :=
  let lss := st.lss
  let st := { st with lss := LsStore.empty }
  let (lss, i) := lss.intern v
  ({ st with lss := lss }, i)

/-! ## Interning into the PERSISTENT tier while the scratch tier is on

DESIGN §8.3, "Phase A runs in the scratch tier too, with promotion": the
install phase opens the scratch tier exactly as phase B does, and the handles
the environment KEEPS are **promoted** before the tier is dropped — a memoised
structural copy scratch → persistent (`Arena/Promote.lean`).  The copy's
target is the persistent tier while the scratch tier is still live, and
`intern` cannot say that: it appends to the tier the store is IN.  So each
store gets a twin of `intern`'s `else` branch, `internPersistent`, and nothing
else about the store changes.  An ADDITIVE API change (DESIGN §8.6 P6-2).

**The probe order is `intern`'s own, minus the scratch probe**: the persistent
cons table first, and an entry found there is the answer — so a node the parse
already interned promotes to ITSELF and a node promoted once is never
duplicated.  The scratch table is deliberately NOT probed: a hit there would
hand back a SCRATCH handle, which is the one thing the promotion exists to get
rid of.

**The WF obligations** (`Arena/WF.lean`), for P3:

* `internPersistent` preserves every clause of `StoreWF` by the persistent
  branch of `intern`'s own argument — it IS that branch — with ONE added
  precondition and ONE transient exception.
* **Added precondition**: `childOK` carries `i.isPersistent → c.isPersistent`,
  so the view handed to `internPersistent` must have PERSISTENT CHILDREN.
  `intern`'s persistent branch gets this for free (it runs only when
  `scratchOn = false`, where `scrOff` makes every live handle persistent);
  promotion gets it by construction, since it promotes the children first.
* **Transient exception — `fresh`**: `fresh` says a view in the scratch cons
  table is not in the persistent one.  A node BUILT in the scratch tier out of
  already-persistent children (an `app` of two parse handles, say) sits in the
  scratch table under a view whose children are persistent, and promoting it
  appends that same view to the persistent table.  So `fresh` is broken while
  the promotion runs.  It is not observable — nothing between the promotion
  and the `dropScratch` that follows it reads the store — and `dropScratch`
  empties the scratch tier, which restores `fresh` vacuously.  The obligation
  P3 owes is therefore stated for the BRACKET: `StoreWF` minus `fresh` is
  preserved by each `internPersistent`, and `promote … dropScratch` as a whole
  takes `StoreWF` to `StoreWF`.
* The denotation obligation is `denote (promote h) = denote h`, by induction
  on the promotion's own recursion (each `internPersistent` is exact by
  `consP`/`derExact`, and the children are exact by the induction hypothesis).
-/

/-- con-leche: none — arena infrastructure; hash-cons a name node into the
PERSISTENT tier whatever tier the store is in.  `intern`'s `else` branch,
verbatim. -/
def NStore.internPersistent (st : NStore) (v : NNodeView) : NStore × NIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    let d := st.derOfView v
    let tb := st.pers
    let st := { st with pers := NTables.empty }
    let (tb, i) := tb.push v d Idx.tierP
    ({ st with pers := tb }, i)

/-- con-leche: none — arena infrastructure; `internPersistent`'s capacity
precondition: the constructor's PERSISTENT array has room for one more node. -/
def NStore.capOKPersistent (st : NStore) (v : NNodeView) : Prop :=
  st.pers.sizeOf v < Idx.idxCap

/-- con-leche: none — arena infrastructure; hash-cons a level node into the
persistent tier. -/
def LStore.internPersistent (st : LStore) (v : LNodeView) : LStore × LIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    let d := st.derOfView v
    let tb := st.pers
    let st := { st with pers := LTables.empty }
    let (tb, i) := tb.push v d Idx.tierP
    ({ st with pers := tb }, i)

/-- con-leche: none — arena infrastructure; the level store's capacity
precondition for `internPersistent`. -/
def LStore.capOKPersistent (st : LStore) (v : LNodeView) : Prop :=
  st.pers.sizeOf v < Idx.idxCap

/-- con-leche: none — arena infrastructure; hash-cons a level list into the
persistent tier. -/
def LsStore.internPersistent (st : LsStore) (v : LsNodeView) : LsStore × LsIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    let d := st.derOfView v
    let tb := st.pers
    let st := { st with pers := LsTables.empty }
    let (tb, i) := tb.push v d Idx.tierP
    ({ st with pers := tb }, i)

/-- con-leche: none — arena infrastructure; the level-list store's capacity
precondition for `internPersistent`. -/
def LsStore.capOKPersistent (st : LsStore) (v : LsNodeView) : Prop :=
  st.pers.sizeOf v < Idx.idxCap

/-- con-leche: none — arena infrastructure; hash-cons an expression node into
the persistent tier whatever tier the store is in. -/
def EStore.internPersistent (st : EStore) (v : ENodeView) : EStore × EIdx :=
  match st.pers.find? v with
  | some i => (st, i)
  | none =>
    let d := st.derOfView v
    let tb := st.pers
    let st := { st with pers := ETables.empty }
    let (tb, i) := tb.push v d Idx.tierP
    ({ st with pers := tb }, i)

/-- con-leche: none — arena infrastructure; the expression store's capacity
precondition for `internPersistent`. -/
def EStore.capOKPersistent (st : EStore) (v : ENodeView) : Prop :=
  st.pers.sizeOf v < Idx.idxCap

/-! ### The same, through the nesting

One lifted entry per level, each detaching the nested store before handing it
down (DESIGN §8.4 lesson 14) and `@[noinline]` (lesson 15) — the shape of the
`intern*` family above it. -/

/-- con-leche: none — arena infrastructure; promote-intern a name from the
level store. -/
@[noinline] def LStore.internNamePersistent (st : LStore) (v : NNodeView) :
    LStore × NIdx :=
  let ns := st.ns
  let st := { st with ns := NStore.empty }
  let (ns, i) := ns.internPersistent v
  ({ st with ns := ns }, i)

/-- con-leche: none — arena infrastructure; promote-intern a name from the
level-list store. -/
@[noinline] def LsStore.internNamePersistent (st : LsStore) (v : NNodeView) :
    LsStore × NIdx :=
  let ls := st.ls
  let st := { st with ls := LStore.empty }
  let (ls, i) := ls.internNamePersistent v
  ({ st with ls := ls }, i)

/-- con-leche: none — arena infrastructure; promote-intern a level from the
level-list store. -/
@[noinline] def LsStore.internLevelPersistent (st : LsStore) (v : LNodeView) :
    LsStore × LIdx :=
  let ls := st.ls
  let st := { st with ls := LStore.empty }
  let (ls, i) := ls.internPersistent v
  ({ st with ls := ls }, i)

/-- con-leche: none — arena infrastructure; promote-intern a name from the
expression store. -/
@[noinline] def EStore.internNamePersistent (st : EStore) (v : NNodeView) :
    EStore × NIdx :=
  let lss := st.lss
  let st := { st with lss := LsStore.empty }
  let (lss, i) := lss.internNamePersistent v
  ({ st with lss := lss }, i)

/-- con-leche: none — arena infrastructure; promote-intern a level from the
expression store. -/
@[noinline] def EStore.internLevelPersistent (st : EStore) (v : LNodeView) :
    EStore × LIdx :=
  let lss := st.lss
  let st := { st with lss := LsStore.empty }
  let (lss, i) := lss.internLevelPersistent v
  ({ st with lss := lss }, i)

/-- con-leche: none — arena infrastructure; promote-intern a universe-argument
list from the expression store. -/
@[noinline] def EStore.internLevelsPersistent (st : EStore) (v : LsNodeView) :
    EStore × LsIdx :=
  let lss := st.lss
  let st := { st with lss := LsStore.empty }
  let (lss, i) := lss.internPersistent v
  ({ st with lss := lss }, i)

end ConRon.Arena
