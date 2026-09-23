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
array.  The binder datum is a HANDLE (task #97-P6-16), so the record is three
handles and its cons key is three words. -/
structure BindNode where
  ty : EIdx
  body : EIdx
  m : BMIdx
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the **binder
datum store**'s one record (task #97-P6-16): a `BinderMeta`'s `PropWhen`,
hash-consed exactly as every other node of the arena is, so that a `BindNode`
names it by a handle.

**Why the datum leaves the node record.**  A `PropWhen` is a value with a
`List Name` inside it at `many`, so the binder record carried a structure the
cons table compared and hashed at every probe of the two hottest tables after
`apps`.  Interned, the record is three handles and the datum is compared,
hashed and copied ONCE per distinct value instead of once per binder node.

The cons discipline is the store's own (DESIGN §8.3): the persistent table is
probed before the scratch one, so a scratch datum never duplicates a
persistent one and `BMIdx` equality IS `PropWhen` equality — which is what
keeps `denote` injective on `lam`/`forallE` now that the node record names the
datum rather than holding it. -/
structure BMNode where
  pw : ConLeche.PropWhen
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
instance : BEq BMNode := instBEqOfDecidableEq
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
  /-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the tier's
  **binder-datum store** (task #97-P6-16): the hash-consed `PropWhen`s the
  `lam` and `forallE` records name by a `BMIdx`, with the derived column
  holding `PropWhen`'s own hash so that `derOfBind`'s two scalars are one
  indexed read.  It rides in `ETables` rather than beside it because it lives
  and dies with the tier exactly as the ten node arrays do. -/
  bms : Tbl BMNode BMIdx UInt64

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

/-- con-leche: none — the LENGTH projection of `LsTables.get` (task
#97-P6-10): most callers compare a universe-argument list's length with a
declaration's level-parameter count, and that is one read off the record. -/
@[inline] def getLen (t : LsTables) (i : LsIdx) : Option Nat :=
  if i.tag == LsTag.list then (t.lists.node? i.idxNat).map fun r => r.us.length
  else none

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

/-- con-leche: none — the persistent arm of `LsStore.viewLen`. -/
@[inline] def persGetLen (st : LsStore) (i : LsIdx) : Option Nat := st.pers.getLen i

/-- con-leche: none — the LENGTH projection of `LsStore.view` (task
#97-P6-10): the tier bit selects the array set and the record's own length
comes back, with no list copied. -/
@[inline] def viewLen (st : LsStore) (i : LsIdx) : Option Nat :=
  if i.isPersistent then st.persGetLen i
  else if st.scratchOn then st.scr.getLen i else none

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
  ⟨.empty, .empty, .empty, .empty, .empty, .empty, .empty, .empty, .empty, .empty,
    .empty⟩

instance : Inhabited ETables := ⟨empty⟩

/-- con-leche: none — nodes in this tier, over all ten constructors. -/
def count (t : ETables) : Nat :=
  t.bvars.size + t.fvars.size + t.sorts.size + t.consts.size + t.apps.size
    + t.lams.size + t.foralls.size + t.lets.size + t.lits.size + t.projs.size

/-- con-leche: none — decode one handle against this tier's arrays: read the
tag, index one array, build the view.  There is no node enum in the store
(DESIGN §8.3).

**The two binder arms answer `none`** (task #97-P6-16): a `lam` or `forallE`
record names its datum by a `BMIdx`, and that handle carries its OWN tier bit
— a scratch binder may name a persistent datum — so one tier cannot resolve a
binder on its own.  `EStore.view` dispatches those two tags through
`viewBindI` and `viewBM`, which is where the two tier selects meet. -/
@[inline] def get (t : ETables) (i : EIdx) : Option ENodeView :=
  if i.tag == ETag.bvar then (t.bvars.node? i.idxNat).map fun r => .bvar r.i
  else if i.tag == ETag.fvar then (t.fvars.node? i.idxNat).map fun r => .fvar r.idx r.ty
  else if i.tag == ETag.sort then (t.sorts.node? i.idxNat).map fun r => .sort r.u
  else if i.tag == ETag.const then (t.consts.node? i.idxNat).map fun r => .const r.n r.us
  else if i.tag == ETag.app then (t.apps.node? i.idxNat).map fun r => .app r.f r.a
  else if ETag.isBind i.tag then none
  else if i.tag == ETag.letE then
    (t.lets.node? i.idxNat).map fun r => .letE r.ty r.val r.body
  else if i.tag == ETag.lit then (t.lits.node? i.idxNat).map fun r => .lit r.l
  else if i.tag == ETag.proj then (t.projs.node? i.idxNat).map fun r => .proj r.n r.i r.e
  else none

/-! ### The per-constructor projections of `get`

`get` decodes a handle of any tag into an `ENodeView`; each projection below
reads the fields of ONE constructor and nothing else.  A caller that has
already decided the tag — off the handle word, which carries it (DESIGN §8.3)
— wants only this, and it saves the callee's ten-way tag dispatch, the view
and the second dispatch on the same tag (tasks #97-P6-10 and #97-P6-13).
`none` is the same "out of range" `get` reports, i.e. a dangling handle.

The exactness lemma the bridge owes for each is `getApp t i = (t.get i).bind
appParts` and its siblings — a `match` over the same `if` chain. -/

/-- con-leche: none — the `app` projection of `ETables.get`. -/
@[inline] def getApp (t : ETables) (i : EIdx) : Option (EIdx × EIdx) :=
  (t.apps.node? i.idxNat).map fun r => (r.f, r.a)

/-- con-leche: none — the `sort` projection of `ETables.get`. -/
@[inline] def getSort (t : ETables) (i : EIdx) : Option LIdx :=
  (t.sorts.node? i.idxNat).map fun r => r.u

/-- con-leche: none — the `const` projection of `ETables.get`. -/
@[inline] def getConst (t : ETables) (i : EIdx) : Option (NIdx × LsIdx) :=
  (t.consts.node? i.idxNat).map fun r => (r.n, r.us)

/-- con-leche: none — the head NAME of a `const` node, which is all a name
comparison wants of it. -/
@[inline] def getConstName (t : ETables) (i : EIdx) : Option NIdx :=
  (t.consts.node? i.idxNat).map fun r => r.n

/-- con-leche: none — the `bvar` projection of `ETables.get`. -/
@[inline] def getBVar (t : ETables) (i : EIdx) : Option Nat :=
  (t.bvars.node? i.idxNat).map fun r => r.i

/-- con-leche: none — the `fvar` INDEX, the de Bruijn level. -/
@[inline] def getFVarIdx (t : ETables) (i : EIdx) : Option Nat :=
  (t.fvars.node? i.idxNat).map fun r => r.idx

/-- con-leche: none — the `fvar` binder TYPE, the second field. -/
@[inline] def getFVarTy (t : ETables) (i : EIdx) : Option EIdx :=
  (t.fvars.node? i.idxNat).map fun r => r.ty

/-- con-leche: none — the `lit` projection of `ETables.get`. -/
@[inline] def getLit (t : ETables) (i : EIdx) : Option ConLeche.Literal :=
  (t.lits.node? i.idxNat).map fun r => r.l

/-- con-leche: none — the binder projection of `ETables.get`, at the datum's
HANDLE: `lam` and `forallE` share one record shape and this reads either, the
caller's tag having already told the two apart. -/
@[inline] def getBind (t : ETables) (i : EIdx) : Option (EIdx × EIdx × BMIdx) :=
  if i.tag == ETag.lam then (t.lams.node? i.idxNat).map fun r => (r.ty, r.body, r.m)
  else if i.tag == ETag.forallE then
    (t.foralls.node? i.idxNat).map fun r => (r.ty, r.body, r.m)
  else none

/-- con-leche: none — the `letE` projection of `ETables.get`. -/
@[inline] def getLet (t : ETables) (i : EIdx) : Option (EIdx × EIdx × EIdx) :=
  (t.lets.node? i.idxNat).map fun r => (r.ty, r.val, r.body)

/-- con-leche: none — the `proj` projection of `ETables.get`. -/
@[inline] def getProj (t : ETables) (i : EIdx) : Option (NIdx × Nat × EIdx) :=
  (t.projs.node? i.idxNat).map fun r => (r.n, r.i, r.e)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — read one binder
datum out of this tier's store (task #97-P6-16). -/
@[inline] def getBM (t : ETables) (i : BMIdx) : Option ConLeche.BinderMeta :=
  (t.bms.node? i.idxNat).map fun r => ⟨r.pw⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the binder
datum's two DERIVED scalars, its hash (the column) and its has-a-parameter bit
(a read of the record), which is all `derOfBind` wants of it. -/
@[inline] def getBMDer (t : ETables) (i : BMIdx) : UInt64 × Bool :=
  match t.bms.node? i.idxNat with
  | none => (0, false)
  | some r => (t.bms.derAt i.idxNat, r.pw.hasParams)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the binder
datum's cons probe in THIS tier. -/
def findBM (t : ETables) (m : ConLeche.BinderMeta) : Option BMIdx :=
  t.bms.find? ⟨m.pw⟩

/-- con-leche: none — the cons probe at a binder RECORD whose datum is
already a handle (task #97-P6-16): the tag picks the array, the record is the
key.  `find?`'s two binder arms are this at `⟨ty, b, mi⟩`. -/
def findBind (t : ETables) (tag : UInt32) (r : BindNode) : Option EIdx :=
  if tag == ETag.lam then t.lams.find? r
  else if tag == ETag.forallE then t.foralls.find? r
  else none

/-- con-leche: none — append a binder RECORD to this tier, at the tag that
says which of the two arrays it goes in.  `push`'s two binder arms are this. -/
@[noinline] def pushBind (t : ETables) (tag : UInt32) (r : BindNode) (d : UInt64)
    (tier : UInt32) : ETables × EIdx :=
  if tag == ETag.lam then
    let tb := t.lams
    let h : EIdx := Idx.mk ETag.lam tier (UInt32.ofNat tb.size)
    let t := { t with lams := Tbl.empty }
    ({ t with lams := tb.push r d h }, h)
  else
    let tb := t.foralls
    let h : EIdx := Idx.mk ETag.forallE tier (UInt32.ofNat tb.size)
    let t := { t with foralls := Tbl.empty }
    ({ t with foralls := tb.push r d h }, h)

/-- con-leche: none — the size of the binder array `tag` names; `intern`'s
capacity test at the two binder arms is stated on it. -/
def bindSizeOf (t : ETables) (tag : UInt32) : Nat :=
  if tag == ETag.lam then t.lams.size else t.foralls.size

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — how many binder
data this tier holds; `internBM`'s capacity test is stated on it. -/
@[inline] def bmSize (t : ETables) : Nat := t.bms.size

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — append a binder
datum to this tier, returning its handle.  `BMIdx`'s tag field is `0`: the
store has one constructor. -/
@[noinline] def pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tier : UInt32) : ETables × BMIdx :=
  let tb := t.bms
  let i : BMIdx := Idx.mk 0 tier (UInt32.ofNat tb.size)
  let t := { t with bms := Tbl.empty }
  ({ t with bms := tb.push ⟨m.pw⟩ d i }, i)

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

/-- con-leche: none — the cons-table probe for a whole node view, at the
binder datum's already-probed handle (task #97-P6-16: `mi` is what
`EStore.findBMOfView` answered, and is ignored at the eight non-binder
arms). -/
def find? (t : ETables) (v : ENodeView) (mi : BMIdx) : Option EIdx :=
  match v with
  | .bvar i => t.bvars.find? ⟨i⟩
  | .fvar idx ty => t.fvars.find? ⟨idx, ty⟩
  | .sort u => t.sorts.find? ⟨u⟩
  | .const n us => t.consts.find? ⟨n, us⟩
  | .app f a => t.apps.find? ⟨f, a⟩
  | .lam ty b _ => t.lams.find? ⟨ty, b, mi⟩
  | .forallE ty b _ => t.foralls.find? ⟨ty, b, mi⟩
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
@[noinline] def push (t : ETables) (v : ENodeView) (d : UInt64) (mi : BMIdx)
    (tier : UInt32) : ETables × EIdx :=
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
  | .lam ty b _ =>
    let tb := t.lams
    let h : EIdx := Idx.mk ETag.lam tier (UInt32.ofNat tb.size)
    let t := { t with lams := Tbl.empty }
    ({ t with lams := tb.push ⟨ty, b, mi⟩ d h }, h)
  | .forallE ty b _ =>
    let tb := t.foralls
    let h : EIdx := Idx.mk ETag.forallE tier (UInt32.ofNat tb.size)
    let t := { t with foralls := Tbl.empty }
    ({ t with foralls := tb.push ⟨ty, b, mi⟩ d h }, h)
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

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `lam` (hash tag
19) and `forallE` (23) arms of `derOfView` as a function of five scalars: the
two children's derived words, the datum's hash and its has-a-parameter bit.
A function rather than the arm itself because `derOfBindAt` (which holds a
`BinderMeta`) and `derOfBindAtI` (which holds its HANDLE) run the same
arithmetic on scalars they read differently. -/
@[inline] def derOfBind (tag : UInt64) (dt db hm : UInt64) (pm : Bool) : UInt64 :=
  packData (hash32 (mixHash tag (mixHash (hashOfData dt) (mixHash (hashOfData db) hm))))
    (max (bvarOfData dt) (satPred (bvarOfData db)))
    (max (fvarOfData dt) (fvarOfData db))
    (lpOfData dt || lpOfData db || pm)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `letE` arm of
`derOfView` over the three children's derived words.  A function for the
reason `derOfBind` is one. -/
@[inline] def derOfLet (dt dv db : UInt64) : UInt64 :=
  packData (hash32 (mixHash 29
      (mixHash (hashOfData dt) (mixHash (hashOfData dv) (hashOfData db)))))
    (max (max (bvarOfData dt) (bvarOfData dv)) (satPred (bvarOfData db)))
    (max (max (fvarOfData dt) (fvarOfData dv)) (fvarOfData db))
    (lpOfData dt || lpOfData dv || lpOfData db)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the inverse of
`EStore.viewBind` (task #97-P6-10): rebuild the binder view a walk decoded
with `viewBind`, at the tag it decoded it at.  `lam` (line 349) and `forallE`
(line 350) have one record shape and the projection reads either; this is the
one place the two arms are told apart again, so a walk that dispatches on the
handle's own tag keeps the twin's two clauses as one clause each. -/
@[inline] def eBindView (tag : UInt32) (ty body : EIdx) (m : ConLeche.BinderMeta) :
    ENodeView :=
  if tag == ETag.lam then .lam ty body m else .forallE ty body m

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

/-! ### The per-constructor projections of `view`

Each is `ETables`' own projection under the tier select `view` does — the
handle's tier bit picks the array set, and the caller's already-decided tag
picks the array (tasks #97-P6-10 and #97-P6-13).  The `persGet*` half is the
persistent arm on its own: in the Rust it is where the frozen-tier READER is
consulted instead of the store's own `pers` field, which is the one shape
difference the refinement absorbs (DESIGN §8's `#97-LC` ledger).

Exactness, for each: `viewApp st h = (view st h).bind appParts` and its
siblings, with `view`'s own tier test in front. -/

/-- con-leche: none — the persistent arm of `EStore.viewApp`. -/
@[inline] def persGetApp (st : EStore) (i : EIdx) : Option (EIdx × EIdx) :=
  st.pers.getApp i

/-- con-leche: none — the `app` projection of `EStore.view`. -/
@[inline] def viewApp (st : EStore) (i : EIdx) : Option (EIdx × EIdx) :=
  if i.isPersistent then st.persGetApp i
  else if st.scratchOn then st.scr.getApp i else none

/-- con-leche: none — the persistent arm of `EStore.viewSort`. -/
@[inline] def persGetSort (st : EStore) (i : EIdx) : Option LIdx := st.pers.getSort i

/-- con-leche: none — the `sort` projection of `EStore.view`. -/
@[inline] def viewSort (st : EStore) (i : EIdx) : Option LIdx :=
  if i.isPersistent then st.persGetSort i
  else if st.scratchOn then st.scr.getSort i else none

/-- con-leche: none — the persistent arm of `EStore.viewConst`. -/
@[inline] def persGetConst (st : EStore) (i : EIdx) : Option (NIdx × LsIdx) :=
  st.pers.getConst i

/-- con-leche: none — the `const` projection of `EStore.view`. -/
@[inline] def viewConst (st : EStore) (i : EIdx) : Option (NIdx × LsIdx) :=
  if i.isPersistent then st.persGetConst i
  else if st.scratchOn then st.scr.getConst i else none

/-- con-leche: none — the persistent arm of `EStore.viewConstName`. -/
@[inline] def persGetConstName (st : EStore) (i : EIdx) : Option NIdx :=
  st.pers.getConstName i

/-- con-leche: none — the head NAME of a `const` node. -/
@[inline] def viewConstName (st : EStore) (i : EIdx) : Option NIdx :=
  if i.isPersistent then st.persGetConstName i
  else if st.scratchOn then st.scr.getConstName i else none

/-- con-leche: none — the persistent arm of `EStore.viewBVar`. -/
@[inline] def persGetBVar (st : EStore) (i : EIdx) : Option Nat := st.pers.getBVar i

/-- con-leche: none — the `bvar` projection of `EStore.view`. -/
@[inline] def viewBVar (st : EStore) (i : EIdx) : Option Nat :=
  if i.isPersistent then st.persGetBVar i
  else if st.scratchOn then st.scr.getBVar i else none

/-- con-leche: none — the persistent arm of `EStore.viewFVarIdx`. -/
@[inline] def persGetFVarIdx (st : EStore) (i : EIdx) : Option Nat :=
  st.pers.getFVarIdx i

/-- con-leche: none — the `fvar` INDEX projection of `EStore.view`. -/
@[inline] def viewFVarIdx (st : EStore) (i : EIdx) : Option Nat :=
  if i.isPersistent then st.persGetFVarIdx i
  else if st.scratchOn then st.scr.getFVarIdx i else none

/-- con-leche: none — the persistent arm of `EStore.viewFVarTy`. -/
@[inline] def persGetFVarTy (st : EStore) (i : EIdx) : Option EIdx :=
  st.pers.getFVarTy i

/-- con-leche: none — the `fvar` binder-TYPE projection of `EStore.view`. -/
@[inline] def viewFVarTy (st : EStore) (i : EIdx) : Option EIdx :=
  if i.isPersistent then st.persGetFVarTy i
  else if st.scratchOn then st.scr.getFVarTy i else none

/-- con-leche: none — the persistent arm of `EStore.viewLit`. -/
@[inline] def persGetLit (st : EStore) (i : EIdx) : Option ConLeche.Literal :=
  st.pers.getLit i

/-- con-leche: none — the `lit` projection of `EStore.view`. -/
@[inline] def viewLit (st : EStore) (i : EIdx) : Option ConLeche.Literal :=
  if i.isPersistent then st.persGetLit i
  else if st.scratchOn then st.scr.getLit i else none

/-- con-leche: none — the persistent arm of `EStore.viewLet`. -/
@[inline] def persGetLet (st : EStore) (i : EIdx) : Option (EIdx × EIdx × EIdx) :=
  st.pers.getLet i

/-- con-leche: none — the `letE` projection of `EStore.view`. -/
@[inline] def viewLet (st : EStore) (i : EIdx) : Option (EIdx × EIdx × EIdx) :=
  if i.isPersistent then st.persGetLet i
  else if st.scratchOn then st.scr.getLet i else none

/-- con-leche: none — the persistent arm of `EStore.viewProj`. -/
@[inline] def persGetProj (st : EStore) (i : EIdx) : Option (NIdx × Nat × EIdx) :=
  st.pers.getProj i

/-- con-leche: none — the `proj` projection of `EStore.view`. -/
@[inline] def viewProj (st : EStore) (i : EIdx) : Option (NIdx × Nat × EIdx) :=
  if i.isPersistent then st.persGetProj i
  else if st.scratchOn then st.scr.getProj i else none

/-- con-leche: none — the persistent arm of `EStore.viewBindI`. -/
@[inline] def persGetBind (st : EStore) (i : EIdx) : Option (EIdx × EIdx × BMIdx) :=
  st.pers.getBind i

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the binder
projection that stops at the datum's HANDLE (task #97-P6-16).  This is what
the rebuilding walks want: a walk that takes a binder apart and puts it back
together never looks inside the datum, it only carries it across. -/
@[inline] def viewBindI (st : EStore) (i : EIdx) : Option (EIdx × EIdx × BMIdx) :=
  if i.isPersistent then st.persGetBind i
  else if st.scratchOn then st.scr.getBind i else none

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the persistent
arm of `EStore.viewBM`. -/
@[inline] def persGetBM (st : EStore) (i : BMIdx) : Option ConLeche.BinderMeta :=
  st.pers.getBM i

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — decode a binder
datum handle, the tier bit selecting the array set as it does for every other
handle kind (task #97-P6-16). -/
@[inline] def viewBM (st : EStore) (i : BMIdx) : Option ConLeche.BinderMeta :=
  if i.isPersistent then st.persGetBM i
  else if st.scratchOn then st.scr.getBM i else none

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the persistent
arm of `EStore.bmDer`. -/
@[inline] def persGetBMDer (st : EStore) (i : BMIdx) : UInt64 × Bool :=
  st.pers.getBMDer i

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the binder
datum's two derived scalars, which is everything `derOfBind` asks of it. -/
@[inline] def bmDer (st : EStore) (i : BMIdx) : UInt64 × Bool :=
  if i.isPersistent then st.persGetBMDer i
  else if st.scratchOn then st.scr.getBMDer i else (0, false)

/-- con-leche: none — the binder projection of `EStore.view`, with the datum
DECODED: `viewBindI` and then `viewBM` at the handle it answers. -/
@[inline] def viewBind (st : EStore) (i : EIdx) :
    Option (EIdx × EIdx × ConLeche.BinderMeta) :=
  match st.viewBindI i with
  | none => none
  | some (ty, b, mi) =>
    match st.viewBM mi with
    | none => none
    | some m => some (ty, b, m)

/-- con-leche: none — decode an expression handle: the tier bit selects the
array set, the tag selects the array, the index reads it.  The two binder tags
go through `viewBind`, because a binder's datum carries its own tier bit and
one tier cannot resolve it (task #97-P6-16). -/
@[inline] def view (st : EStore) (i : EIdx) : Option ENodeView :=
  if ETag.isBind i.tag then
    match st.viewBind i with
    | none => none
    | some (ty, b, m) => some (eBindView i.tag ty b m)
  else if i.isPersistent then st.pers.get i
  else if st.scratchOn then st.scr.get i else none

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `data` computed
field, lines 357-402: the packed derived word of an expression handle. -/
@[inline] def derived (st : EStore) (i : EIdx) : UInt64 :=
  if i.isPersistent then st.pers.derAt i
  else if st.scratchOn then st.scr.derAt i else 0

/-! ### The derived word, arm by arm

con-leche's `Expr.data` formulas verbatim (`Kernel/Expr.lean:357-402`), with
`e.data` replaced by `st.derived h` and the level/name reads replaced by the
corresponding stores' derived columns:

* `levelHash u` ↦ `(st.lder u).hash`, `levelHasParam u` ↦ `(st.lder u).hasParam`;
* `Hashable.hash (n : Name)` ↦ `st.nder n` (the `Hashable Name` instance
  *is* `Name.hashData`, `Kernel/Name.lean:49`);
* `levelsHash us` ↦ `(st.lsder us).hash`, `levelsHaveParam us` ↦
  `(st.lsder us).hasParam`.

**One function per arm** (task #97-P6-15).  `derOfView` used to write the ten
arms inline and be their only caller; `intern`'s ten per-constructor paths
need the same arithmetic off the node RECORD, and a `match` on a view they
have already taken apart is exactly the dispatch that task's lever removes.
Each arm is a function of that arm's own fields, called from both, and
`derOfView` is their dispatch — so `derOfView v = derOf<C> (fields of v)` is
`rfl` per constructor and `derived_exact` (`WFProofs.lean`) is still one
`simp` per constructor. -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `bvar` arm. -/
@[inline] def derOfBVar (_st : EStore) (i : Nat) : UInt64 :=
  packData (hash32 (mixHash 3 (hash i))) (satSucc i) 0 false

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `fvar` arm. -/
@[inline] def derOfFVar (st : EStore) (idx : Nat) (ty : EIdx) : UInt64 :=
  packData (hash32 (mixHash 5 (mixHash (hash idx) (hashOfData (st.derived ty)))))
    0 (satSucc idx) (lpOfData (st.derived ty))

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `sort` arm. -/
@[inline] def derOfSort (st : EStore) (u : LIdx) : UInt64 :=
  packData (hash32 (mixHash 7 (st.lder u).hash)) 0 0 (st.lder u).hasParam

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `const` arm. -/
@[inline] def derOfConst (st : EStore) (n : NIdx) (us : LsIdx) : UInt64 :=
  packData (hash32 (mixHash 11 (mixHash (st.nder n) (st.lsder us).hash)))
    0 0 (st.lsder us).hasParam

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `app` arm. -/
@[inline] def derOfApp (st : EStore) (f a : EIdx) : UInt64 :=
  packData (hash32 (mixHash 17
      (mixHash (hashOfData (st.derived f)) (hashOfData (st.derived a)))))
    (max (bvarOfData (st.derived f)) (bvarOfData (st.derived a)))
    (max (fvarOfData (st.derived f)) (fvarOfData (st.derived a)))
    (lpOfData (st.derived f) || lpOfData (st.derived a))

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `lam` (tag 19) and
`forallE` (tag 23) arms at a datum held as a VALUE. -/
@[inline] def derOfBindAt (st : EStore) (tag : UInt64) (ty b : EIdx)
    (m : ConLeche.BinderMeta) : UInt64 :=
  derOfBind tag (st.derived ty) (st.derived b) (hash m.pw) m.pw.hasParams

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the `lam`/
`forallE` arm over the datum's HANDLE (task #97-P6-16): the two scalars
`derOfBind` wants of the datum are the binder-datum store's own derived column
and a read of its record, so the arithmetic is unchanged and no `PropWhen` is
walked.  The exactness obligation is `derOfBindAtI … mi = derOfBindAt … m`
whenever `viewBM mi = some m`, by the datum column's own `derExact`. -/
@[inline] def derOfBindAtI (st : EStore) (tag : UInt64) (ty b : EIdx)
    (mi : BMIdx) : UInt64 :=
  let bd := st.bmDer mi
  derOfBind tag (st.derived ty) (st.derived b) bd.1 bd.2

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `letE` arm. -/
@[inline] def derOfLetAt (st : EStore) (ty v b : EIdx) : UInt64 :=
  derOfLet (st.derived ty) (st.derived v) (st.derived b)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `lit` arm. -/
@[inline] def derOfLit (_st : EStore) (l : ConLeche.Literal) : UInt64 :=
  packData (hash32 (mixHash 31 (hash l))) 0 0 false

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `proj` arm. -/
@[inline] def derOfProj (st : EStore) (s : NIdx) (i : Nat) (e : EIdx) : UInt64 :=
  packData (hash32 (mixHash 37 (mixHash (st.nder s)
      (mixHash (hash i) (hashOfData (st.derived e))))))
    (bvarOfData (st.derived e)) (fvarOfData (st.derived e)) (lpOfData (st.derived e))

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `data` computed
field, lines 357-402: the derived word a node view *would* get, computed in
`O(1)` from the children's, as the ten arms' dispatch. -/
def derOfView (st : EStore) (v : ENodeView) : UInt64 :=
  match v with
  | .bvar i => st.derOfBVar i
  | .fvar idx ty => st.derOfFVar idx ty
  | .sort u => st.derOfSort u
  | .const n us => st.derOfConst n us
  | .app f a => st.derOfApp f a
  | .lam ty b m => st.derOfBindAt 19 ty b m
  | .forallE ty b m => st.derOfBindAt 23 ty b m
  | .letE ty v b => st.derOfLetAt ty v b
  | .lit l => st.derOfLit l
  | .proj s i e => st.derOfProj s i e

/-! ### The binder datum's own hash-cons

The datum store is `intern`'s own clauses at a store with ONE constructor and
no children (task #97-P6-16): probe the persistent cons table, then the
scratch one, then append to the tier the store is in.  `BMIdx` equality is
therefore `PropWhen` equality, which is what keeps `denote` injective on
`lam`/`forallE` now that the node record names the datum rather than holding
it — the exactness lemma the bridge owes is `denoteBM` injective, and its
proof is the argument `denoteE`'s injectivity already runs, at a store with no
children. -/

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the persistent
arm of `EStore.findBM`. -/
def persFindBM (st : EStore) (m : ConLeche.BinderMeta) : Option BMIdx :=
  st.pers.findBM m

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the datum's cons
probe over both tiers, persistent first (the store's own order).  A datum that
is not interned names no binder node, so `none` here is `none` for the whole
`find?`. -/
def findBM (st : EStore) (m : ConLeche.BinderMeta) : Option BMIdx :=
  match st.persFindBM m with
  | some i => some i
  | none => if st.scratchOn then st.scr.findBM m else none

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — hash-cons a
binder datum. -/
def internBM (st : EStore) (m : ConLeche.BinderMeta) : EStore × BMIdx :=
  match st.persFindBM m with
  | some i => (st, i)
  | none =>
    if st.scratchOn then
      match st.scr.findBM m with
      | some i => (st, i)
      | none =>
        let d := hash m.pw
        let tb := st.scr
        let st := { st with scr := ETables.empty }
        let (tb, i) := tb.pushBM m d Idx.tierS
        ({ st with scr := tb }, i)
    else
      let d := hash m.pw
      let tb := st.pers
      let st := { st with pers := ETables.empty }
      let (tb, i) := tb.pushBM m d Idx.tierP
      ({ st with pers := tb }, i)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the datum's
promote-intern: `internPersistent`'s clauses at the datum store, so that a
promoted binder names a PERSISTENT datum. -/
def internBMPersistent (st : EStore) (m : ConLeche.BinderMeta) : EStore × BMIdx :=
  match st.persFindBM m with
  | some i => (st, i)
  | none =>
    let d := hash m.pw
    let tb := st.pers
    let st := { st with pers := ETables.empty }
    let (tb, i) := tb.pushBM m d Idx.tierP
    ({ st with pers := tb }, i)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — `internBM`'s
capacity precondition. -/
def capOKBM (st : EStore) : Prop :=
  (if st.scratchOn then st.scr.bmSize else st.pers.bmSize) < Idx.idxCap

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta —
`internBMPersistent`'s capacity precondition. -/
def capOKBMPersistent (st : EStore) : Prop := st.pers.bmSize < Idx.idxCap

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — does interning
this view also intern a binder DATUM?  Only the two binder arms do, and they
are the only ones whose capacity test must also look at `bms` — which is why
`internE`'s wrapper tests `capOKBM` exactly here (the Rust's `intern_bm` makes
the same test inside itself, and raises the same `Native`). -/
@[inline] def eViewNeedsBM : ENodeView → Bool
  | .lam _ _ _ => true
  | .forallE _ _ _ => true
  | _ => false

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the datum handle
a view's cons key needs, PROBED and not interned: a binder whose datum has
never been interned is in neither table, so `none` here is `none` for the whole
`find?`.  A non-binder view names no datum and the value is never read. -/
def findBMOfView (st : EStore) (v : ENodeView) : Option BMIdx :=
  match v with
  | .lam _ _ m => st.findBM m
  | .forallE _ _ m => st.findBM m
  | _ => some (Idx.ofWord 0)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the datum handle
a view's cons key needs, INTERNED.  `intern`'s first step. -/
def internBMOfView (st : EStore) (v : ENodeView) : EStore × BMIdx :=
  match v with
  | .lam _ _ m => st.internBM m
  | .forallE _ _ m => st.internBM m
  | _ => (st, Idx.ofWord 0)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the datum handle
a view names, made PERSISTENT, so that `internPersistent` goes on working over
the view while the record names the datum by a handle. -/
def internBMOfViewPersistent (st : EStore) (v : ENodeView) : EStore × BMIdx :=
  match v with
  | .lam _ _ m => st.internBMPersistent m
  | .forallE _ _ m => st.internBMPersistent m
  | _ => (st, Idx.ofWord 0)

/-- con-leche: none — probe both tiers, persistent first (nanoda's
`alloc_expr`, `util.rs:391-400`), at an already-probed datum handle. -/
def findAt (st : EStore) (v : ENodeView) (mi : BMIdx) : Option EIdx :=
  match st.pers.find? v mi with
  | some i => some i
  | none => if st.scratchOn then st.scr.find? v mi else none

/-- con-leche: none — the PERSISTENT tier's cons probe for a whole node view:
the datum's handle first (it is part of the cons key), then the node.  The
store invariant's `consP` clause is stated on it. -/
def persFind? (st : EStore) (v : ENodeView) : Option EIdx :=
  match st.findBMOfView v with
  | none => none
  | some mi => st.pers.find? v mi

/-- con-leche: none — the SCRATCH tier's cons probe for a whole node view.
The store invariant's `consS` clause is stated on it. -/
def scrFind? (st : EStore) (v : ENodeView) : Option EIdx :=
  match st.findBMOfView v with
  | none => none
  | some mi => st.scr.find? v mi

/-- con-leche: none — probe both tiers for a whole node view: the datum first
(it is part of the cons key), then the node. -/
def find? (st : EStore) (v : ENodeView) : Option EIdx :=
  match st.findBMOfView v with
  | none => none
  | some mi => st.findAt v mi

/-- con-leche: none — hash-cons an expression node at an already-interned
datum handle: probe the persistent cons table, then the scratch one, then
append to the tier the store is in (DESIGN §8.3; nanoda `util.rs:391-400`). -/
def internAt (st : EStore) (v : ENodeView) (mi : BMIdx) : EStore × EIdx :=
  match st.pers.find? v mi with
  | some i => (st, i)
  | none =>
    if st.scratchOn then
      match st.scr.find? v mi with
      | some i => (st, i)
      | none =>
        let d := st.derOfView v
        let tb := st.scr
        let st := { st with scr := ETables.empty }
        let (tb, i) := tb.push v d mi Idx.tierS
        ({ st with scr := tb }, i)
    else
      let d := st.derOfView v
      let tb := st.pers
      let st := { st with pers := ETables.empty }
      let (tb, i) := tb.push v d mi Idx.tierP
      ({ st with pers := tb }, i)

/-- con-leche: none — hash-cons an expression node: the binder datum first,
then the node at its handle. -/
def intern (st : EStore) (v : ENodeView) : EStore × EIdx :=
  let (st, mi) := st.internBMOfView v
  st.internAt v mi

/-! ### `intern`'s clauses over the node RECORD, one entry per constructor

Task #97-P6-15.  The Rust dispatches the tag ONCE and runs `intern`'s four
clauses — the persistent probe, the scratch probe, the capacity test, the
append — over a node record it builds once and shares with all four, because
each of `find?`, `derOfView` and `push` used to re-dispatch on the same tag
and rebuild the same record.  Lean's value semantics pays none of that: the
view IS the record and is shared, not copied.  So the twin's per-constructor
entry is `intern` at that constructor's view, which is exactly the equation
the ledger asks for (`internC r = intern (viewOf r)`, `rfl` after the
`match`), and the ten entries below make the one-to-one correspondence with
the Rust's ten paths explicit. -/

/-- con-leche: none — `intern` at the `bvar` constructor. -/
@[inline] def internBVar (st : EStore) (i : Nat) : EStore × EIdx := st.intern (.bvar i)
/-- con-leche: none — `intern` at the `fvar` constructor. -/
@[inline] def internFVar (st : EStore) (idx : Nat) (ty : EIdx) : EStore × EIdx :=
  st.intern (.fvar idx ty)
/-- con-leche: none — `intern` at the `sort` constructor. -/
@[inline] def internSort (st : EStore) (u : LIdx) : EStore × EIdx := st.intern (.sort u)
/-- con-leche: none — `intern` at the `const` constructor. -/
@[inline] def internConst (st : EStore) (n : NIdx) (us : LsIdx) : EStore × EIdx :=
  st.intern (.const n us)
/-- con-leche: none — `intern` at the `app` constructor. -/
@[inline] def internApp (st : EStore) (f a : EIdx) : EStore × EIdx := st.intern (.app f a)
/-- con-leche: none — `intern` at the `letE` constructor. -/
@[inline] def internLetE (st : EStore) (ty val b : EIdx) : EStore × EIdx :=
  st.intern (.letE ty val b)
/-- con-leche: none — `intern` at the `lit` constructor. -/
@[inline] def internLit (st : EStore) (l : ConLeche.Literal) : EStore × EIdx :=
  st.intern (.lit l)
/-- con-leche: none — `intern` at the `proj` constructor. -/
@[inline] def internProj (st : EStore) (n : NIdx) (i : Nat) (e : EIdx) : EStore × EIdx :=
  st.intern (.proj n i e)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the two-tier
cons probe at a binder record whose datum is already a HANDLE: literally
`internBindI`'s own two `match` scrutinees, in `internBindI`'s order
(persistent first, scratch only when the scratch tier is open).

It exists so that `Arena/Monad.lean`'s `internLamIE` / `internForallEIE` can
PROBE BEFORE they test the capacity, which is what the Rust does — see
`internE`'s note there (task #97-P5-1's finding 9, at the `_i` family by task
#97-P5-Twin).  `Bridge/StoreBind.lean` proves it is `EStore.findAt` at the
view the datum spells out, exactly as `internBindI` is `internAt`. -/
def findBindI (st : EStore) (tag : UInt32) (ty b : EIdx) (mi : BMIdx) :
    Option EIdx :=
  let r : BindNode := ⟨ty, b, mi⟩
  match st.pers.findBind tag r with
  | some hp => some hp
  | none => if st.scratchOn then st.scr.findBind tag r else none

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — `intern`'s
clauses at a binder record whose datum is already a HANDLE (task #97-P6-16).

This is what the rebuilding walks call: they take a binder apart with
`viewBindI` and put it back with this, so the datum is never decoded and never
compared on the way through.  `internLam` is this with the datum interned
first, which is what a caller holding a `BinderMeta` — the parser, the
modeller, a fresh binder — wants. -/
def internBindI (st : EStore) (tag : UInt32) (ty b : EIdx) (mi : BMIdx) :
    EStore × EIdx :=
  let r : BindNode := ⟨ty, b, mi⟩
  match st.pers.findBind tag r with
  | some hp => (st, hp)
  | none =>
    if st.scratchOn then
      match st.scr.findBind tag r with
      | some hs => (st, hs)
      | none =>
        let d := st.derOfBindAtI (if tag == ETag.lam then 19 else 23) ty b mi
        let tb := st.scr
        let st := { st with scr := ETables.empty }
        let (tb, h) := tb.pushBind tag r d Idx.tierS
        ({ st with scr := tb }, h)
    else
      let d := st.derOfBindAtI (if tag == ETag.lam then 19 else 23) ty b mi
      let tb := st.pers
      let st := { st with pers := ETables.empty }
      let (tb, h) := tb.pushBind tag r d Idx.tierP
      ({ st with pers := tb }, h)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — `intern` at the
`lam` constructor over a datum HANDLE. -/
@[inline] def internLamI (st : EStore) (ty b : EIdx) (mi : BMIdx) : EStore × EIdx :=
  st.internBindI ETag.lam ty b mi
/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — `intern` at the
`forallE` constructor over a datum HANDLE. -/
@[inline] def internForallEI (st : EStore) (ty b : EIdx) (mi : BMIdx) : EStore × EIdx :=
  st.internBindI ETag.forallE ty b mi
/-- con-leche: none — `intern` at the `lam` constructor. -/
@[inline] def internLam (st : EStore) (ty b : EIdx) (m : ConLeche.BinderMeta) :
    EStore × EIdx :=
  let (st, mi) := st.internBM m
  st.internLamI ty b mi
/-- con-leche: none — `intern` at the `forallE` constructor. -/
@[inline] def internForallE (st : EStore) (ty b : EIdx) (m : ConLeche.BinderMeta) :
    EStore × EIdx :=
  let (st, mi) := st.internBM m
  st.internForallEI ty b mi

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the binder
`intern` at a tag the caller already read off the handle, which is
`eBindView`'s own choice made one step earlier. -/
@[inline] def internEBindI (st : EStore) (tag : UInt32) (ty b : EIdx) (mi : BMIdx) :
    EStore × EIdx :=
  st.internBindI tag ty b mi

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
total.

**The datum store is part of it** (task #97-LC finding 1, made good here):
`intern` of a `lam`/`forallE` view also pushes a binder DATUM, and a datum
array at `Idx.idxCap` would hand back a `BMIdx` whose index has wrapped into
the TIER bit — a persistent handle reading as scratch, which breaks
`bmConsP` and, with it, `view` of the node just interned.

**…but only where the datum is actually APPENDED** (task #97-P5-Twin round 2).
`internBMOfView` probes before it pushes, so a view whose datum is already
interned (`findBMOfView v = some _`) needs no room in `bms` at all — which is
exactly where the Rust's `intern_bm` tests `full`, inside its own miss arm.
A NON-binder view has `findBMOfView v = some (Idx.ofWord 0)` by definition, so
the conjunct is vacuous there and `eViewNeedsBM` need not appear in it. -/
def capOK (st : EStore) (v : ENodeView) : Prop :=
  (if st.scratchOn then st.scr.sizeOf v else st.pers.sizeOf v) < Idx.idxCap
    ∧ (st.findBMOfView v = none → st.capOKBM)

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
  let (st, mi) := st.internBMOfViewPersistent v
  match st.pers.find? v mi with
  | some i => (st, i)
  | none =>
    let d := st.derOfView v
    let tb := st.pers
    let st := { st with pers := ETables.empty }
    let (tb, i) := tb.push v d mi Idx.tierP
    ({ st with pers := tb }, i)

/-- con-leche: none — arena infrastructure; the expression store's capacity
precondition for `internPersistent`, the datum store included for the reason
`EStore.capOK` states. -/
def EStore.capOKPersistent (st : EStore) (v : ENodeView) : Prop :=
  st.pers.sizeOf v < Idx.idxCap
    ∧ (EStore.eViewNeedsBM v = true → st.capOKBMPersistent)

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
