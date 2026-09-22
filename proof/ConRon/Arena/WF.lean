/-
# Store well-formedness and the store layer's theorems (DESIGN.md §8.3, P2a)

`StoreWF` is the arena's own invariant — con-leche's `TWF`
(`Setlec/Kernel/ArenaWF.lean:900`, 28 clauses) redrawn for the
per-constructor, high-tag representation.  It lives here, beside the
implementation, importing nothing from `ConRon.Refine`: con-leche's lesson 27,
"implementation may import a *self-contained* data-structure verification".

Each store's invariant is `∃ rank, …WFAt st rank`.  The rank is existential
because nothing at runtime stores it (DESIGN §8.3: "zero runtime cost, and no
global array order is needed with per-constructor arrays"); what it buys is

* **acyclicity**, hence a terminating `denote`;
* **a fuel bound**: a persistent node's rank is below the persistent node
  count and a scratch node's below the total, so `nodeCount + 1` — the fuel
  `denoteE` uses — is always enough, and `dropScratch` shrinks both sides of
  the persistent clause together.

The clauses, in the order a reader meets them:

| clause | what it says |
|---|---|
| `childOK` | every child is in range, ranked below its parent, and persistent if the parent is |
| `rankP` / `rankS` | ranks are below the tier's node count (the fuel bound) |
| `consP` / `consS` | each tier's cons table is exactly the inverse of that tier's `get` |
| `fresh` | a scratch cons entry never duplicates a persistent one (DESIGN §8.3's cross-tier canonicity; con-leche's `t_cons_fresh`) |
| `derExact` | the derived column is `derOfView` of the node — *locally*; the global `derived st i = e.data` is a theorem (`derived_exact`) |
| `sized` | the derived array is as long as the node array |
| `cap` | no constructor array exceeds 2^27 entries, so a handle's 27-bit index is injective on it |
| `bmKey` | every binder key a cons table holds names a datum the store can decode |
| `scrOff` | the scratch tier is empty while the scratch flag is off |
| `sync` | the nesting's scratch flags move together (task #97a) |

`childOK`'s third conjunct — *persistent parents have persistent children* —
is what makes `dropScratch` sound: without it a persistent node could point
into a tier that is about to vanish.  It needs no hypothesis at `intern`,
because `scrOff` makes a scratch handle undecodable while the flag is off, so
a valid child of a node appended to the persistent tier is persistent already.
-/
import ConRon.Arena.Denote

namespace ConRon.Arena

open ConLeche

/-! ## Children of a node view -/

/-- con-leche: none — the name handles a name node points at. -/
def NNodeView.children : NNodeView → List NIdx
  | .anonymous => []
  | .str p _ => [p]
  | .num p _ => [p]

/-- con-leche: none — the level handles a level node points at. -/
def LNodeView.lchildren : LNodeView → List LIdx
  | .zero => []
  | .succ u => [u]
  | .max u v => [u, v]
  | .imax u v => [u, v]
  | .param _ => []

/-- con-leche: none — the name handles a level node points at. -/
def LNodeView.nchildren : LNodeView → List NIdx
  | .param n => [n]
  | _ => []

/-- con-leche: none — the expression handles an expression node points at. -/
def ENodeView.echildren : ENodeView → List EIdx
  | .bvar _ | .sort _ | .const _ _ | .lit _ => []
  | .fvar _ ty => [ty]
  | .app f a => [f, a]
  | .lam ty b _ | .forallE ty b _ => [ty, b]
  | .letE ty v b => [ty, v, b]
  | .proj _ _ e => [e]

/-- con-leche: none — the name handles an expression node points at. -/
def ENodeView.nchildren : ENodeView → List NIdx
  | .const n _ => [n]
  | .proj n _ _ => [n]
  | _ => []

/-- con-leche: none — the level handles an expression node points at. -/
def ENodeView.lchildren : ENodeView → List LIdx
  | .sort u => [u]
  | _ => []

/-- con-leche: none — the level-list handles an expression node points at. -/
def ENodeView.lschildren : ENodeView → List LsIdx
  | .const _ us => [us]
  | _ => []

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the datum a node
view carries, if it carries one.  `EStore.findBMOfView` is `findBM` at this
(task #97-P6-16). -/
def ENodeView.bmOf : ENodeView → Option ConLeche.BinderMeta
  | .lam _ _ m => some m
  | .forallE _ _ m => some m
  | _ => none

/-! ## Table shape predicates -/

/-- con-leche: none — the derived column is as long as the node array. -/
def Tbl.Sized {α ι δ : Type} [BEq α] [Hashable α] (t : Tbl α ι δ) : Prop :=
  t.der.size = t.nodes.size

/-- con-leche: none — every constructor array of a name tier is sized. -/
def NTables.Sized (t : NTables) : Prop :=
  t.anons.Sized ∧ t.strs.Sized ∧ t.nums.Sized

/-- con-leche: none — every constructor array of a level tier is sized. -/
def LTables.Sized (t : LTables) : Prop :=
  t.zeros.Sized ∧ t.succs.Sized ∧ t.maxs.Sized ∧ t.imaxs.Sized ∧ t.params.Sized

/-- con-leche: none — the level-list tier's array is sized. -/
def LsTables.Sized (t : LsTables) : Prop := t.lists.Sized

/-- con-leche: none — every constructor array of an expression tier is sized. -/
def ETables.Sized (t : ETables) : Prop :=
  t.bvars.Sized ∧ t.fvars.Sized ∧ t.sorts.Sized ∧ t.consts.Sized ∧ t.apps.Sized
    ∧ t.lams.Sized ∧ t.foralls.Sized ∧ t.lets.Sized ∧ t.lits.Sized ∧ t.projs.Sized
    ∧ t.bms.Sized

/-! ## The name store's invariant -/

/-- con-leche: none — arena infrastructure; the name store's well-formedness
at an explicit rank.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:900 EStore.TWF` (at 94a1cf78). -/
structure NWFAt (st : NStore) (rk : NIdx → Nat) : Prop where
  childOK : ∀ i v, st.view i = some v → ∀ c ∈ v.children,
    (st.view c).isSome = true ∧ rk c < rk i ∧
      (i.isPersistent = true → c.isPersistent = true)
  rankP : ∀ i, i.isPersistent = true → (st.view i).isSome = true →
    rk i < st.persCount
  rankS : ∀ i, i.isPersistent = false → (st.view i).isSome = true →
    rk i < st.nodeCount
  consP : ∀ v i, st.pers.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scr.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  fresh : ∀ v i, st.scr.find? v = some i → st.pers.find? v = none
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = NTables.empty

/-- con-leche: none — arena infrastructure; the name store is well formed.
Precedent: con-leche's retired `Setlec/Kernel/ArenaWF.lean:900 EStore.TWF`
(at 94a1cf78). -/
def NStoreWF (st : NStore) : Prop := ∃ rk, NWFAt st rk

/-! ## The level store's invariant -/

/-- con-leche: none — arena infrastructure; the level store's
well-formedness at an explicit rank; it carries the name store's.
Precedent: con-leche's retired `Setlec/Kernel/ArenaWF.lean:900 EStore.TWF`
(at 94a1cf78). -/
structure LWFAt (st : LStore) (rk : LIdx → Nat) : Prop where
  ns : NStoreWF st.ns
  childOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lchildren,
    (st.view c).isSome = true ∧ rk c < rk i ∧
      (i.isPersistent = true → c.isPersistent = true)
  nchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.nchildren,
    (st.ns.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  rankP : ∀ i, i.isPersistent = true → (st.view i).isSome = true →
    rk i < st.persCount
  rankS : ∀ i, i.isPersistent = false → (st.view i).isSome = true →
    rk i < st.nodeCount
  consP : ∀ v i, st.pers.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scr.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  fresh : ∀ v i, st.scr.find? v = some i → st.pers.find? v = none
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = LTables.empty
  sync : st.scratchOn = st.ns.scratchOn

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:900 EStore.TWF` (at 94a1cf78). -/
def LStoreWF (st : LStore) : Prop := ∃ rk, LWFAt st rk

/-! ## The level-list store's invariant

A list node has no `LsIdx` children, so there is no rank clause: the store is
one level deep by construction. -/

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:900 EStore.TWF` (at 94a1cf78). -/
structure LsWF (st : LsStore) : Prop where
  ls : LStoreWF st.ls
  lchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v,
    (st.ls.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  consP : ∀ v i, st.pers.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scr.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  fresh : ∀ v i, st.scr.find? v = some i → st.pers.find? v = none
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = LsTables.empty
  sync : st.scratchOn = st.ls.scratchOn

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:900 EStore.TWF` (at 94a1cf78). -/
def LsStoreWF (st : LsStore) : Prop := LsWF st

/-! ## The expression store's invariant -/

/-- con-leche: none — arena infrastructure; the expression store's
well-formedness at an explicit rank; it carries the three stores below it.
Precedent: con-leche's retired `Setlec/Kernel/ArenaWF.lean:900 EStore.TWF`
(at 94a1cf78).

**Why the three binder-datum clauses say `tag = 0`** (task #97-LC).  The
datum store has ONE constructor, so `ETables.getBM` has no tag dispatch —
it reads `bms` at the handle's index and nothing else, exactly as the Rust's
`ETables::get_bm` does, and `BMIdx::pack` passes tag `0` unconditionally.
The other three stores get the handle's tag back for free, because their
`get` dispatches on it: there, `(tag, tier, index)` determines the word, and
a cons table's `↔` is satisfiable.  Here it is not — two handles differing
only in their tag bits decode to the SAME datum, so without `tag = 0` the
`bmConsP`/`bmConsS` equivalences would force `findBM` to answer both, and
`EWFAt` would hold only of a store whose datum tables are empty.  The
invariant says instead what the dispatch would have said, and both sides
establish it by construction: `ETables.pushBM` builds its handle as
`Idx.mk 0 tier _`, and `Idx.tag_mk` gives `tag = 0`. -/
structure EWFAt (st : EStore) (rk : EIdx → Nat) : Prop where
  lss : LsStoreWF st.lss
  childOK : ∀ i v, st.view i = some v → ∀ c ∈ v.echildren,
    (st.view c).isSome = true ∧ rk c < rk i ∧
      (i.isPersistent = true → c.isPersistent = true)
  nchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.nchildren,
    (st.ns.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  lchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lchildren,
    (st.ls.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  lschildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lschildren,
    (st.lss.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  rankP : ∀ i, i.isPersistent = true → (st.view i).isSome = true →
    rk i < st.persCount
  rankS : ∀ i, i.isPersistent = false → (st.view i).isSome = true →
    rk i < st.nodeCount
  bmChildOK : ∀ i ty b mi, st.viewBindI i = some (ty, b, mi) →
    (st.viewBM mi).isSome = true ∧ (i.isPersistent = true → mi.isPersistent = true)
      ∧ mi.tag = 0
  consP : ∀ v i, st.persFind? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scrFind? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  fresh : ∀ v i, st.scrFind? v = some i → st.persFind? v = none
  bmConsP : ∀ m i, st.pers.findBM m = some i ↔
    (st.viewBM i = some m ∧ i.isPersistent = true ∧ i.tag = 0)
  bmConsS : ∀ m i, st.scr.findBM m = some i ↔
    (st.viewBM i = some m ∧ i.isPersistent = false ∧ i.tag = 0)
  bmFresh : ∀ m i, st.scr.findBM m = some i → st.pers.findBM m = none
  bmKeyP : ∀ v mj i, st.pers.find? v mj = some i →
    v.bmOf = none ∨ ∃ m, st.pers.findBM m = some mj
  bmKeyS : ∀ v mj i, st.scr.find? v mj = some i →
    v.bmOf = none ∨ ∃ m, st.findBM m = some mj
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  bmDerExact : ∀ i m, st.viewBM i = some m → st.bmDer i = (hash m.pw, m.pw.hasParams)
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  bmCapP : st.pers.bmSize ≤ Idx.idxCap
  bmCapS : st.scr.bmSize ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = ETables.empty
  sync : st.scratchOn = st.lss.scratchOn

/-- con-leche: none — arena infrastructure; **the** store invariant: the
arena is well formed.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:900 EStore.TWF` (at 94a1cf78). -/
def StoreWF (st : EStore) : Prop := ∃ rk, EWFAt st rk

/-! ## `intern`'s preconditions -/

/-- con-leche: none — `intern`'s children precondition: every handle the node
view mentions decodes in the store it belongs to. -/
def NStore.ViewOK (st : NStore) (v : NNodeView) : Prop :=
  ∀ c ∈ v.children, (st.view c).isSome = true

/-- con-leche: none — `intern`'s children precondition for a level node. -/
structure LStore.ViewOK (st : LStore) (v : LNodeView) : Prop where
  lvl : ∀ c ∈ v.lchildren, (st.view c).isSome = true
  nm : ∀ c ∈ v.nchildren, (st.ns.view c).isSome = true

/-- con-leche: none — `intern`'s children precondition for a level list. -/
def LsStore.ViewOK (st : LsStore) (v : LsNodeView) : Prop :=
  ∀ c ∈ v, (st.ls.view c).isSome = true

/-- con-leche: none — `intern`'s children precondition for an expression
node. -/
structure EStore.ViewOK (st : EStore) (v : ENodeView) : Prop where
  expr : ∀ c ∈ v.echildren, (st.view c).isSome = true
  nm : ∀ c ∈ v.nchildren, (st.ns.view c).isSome = true
  lvl : ∀ c ∈ v.lchildren, (st.ls.view c).isSome = true
  lst : ∀ c ∈ v.lschildren, (st.lss.view c).isSome = true

/-! ## What a node view denotes

`denote*View` assembles the children's denotations exactly as `denote*Aux`
does one step down.  `denote*_unfold` (`WFProofs.lean`) is the equation that
replaces the fuel by the rank once and for all. -/

/-- con-leche: none — the denotation of a name node view. -/
def denoteNView (st : NStore) : NNodeView → Option ConLeche.Name
  | .anonymous => some .anonymous
  | .str p s => (denoteN st p).map fun q => .str q s
  | .num p n => (denoteN st p).map fun q => .num q n

/-- con-leche: none — the denotation of a level node view. -/
def denoteLView (st : LStore) : LNodeView → Option Level
  | .zero => some .zero
  | .succ u => (denoteL st u).map Level.succ
  | .max u v => opt2 Level.max (denoteL st u) (denoteL st v)
  | .imax u v => opt2 Level.imax (denoteL st u) (denoteL st v)
  | .param n => (denoteN st.ns n).map Level.param

/-- con-leche: none — the denotation of a level-list node view. -/
def denoteLsView (st : LsStore) (v : LsNodeView) : Option (List Level) :=
  denoteLList st.ls v

/-- con-leche: none — the denotation of an expression node view. -/
def denoteEView (st : EStore) : ENodeView → Option Expr
  | .bvar k => some (.bvar k)
  | .fvar k ty => (denoteE st ty).map (Expr.fvar k)
  | .sort u => (denoteL st.ls u).map Expr.sort
  | .const n us => opt2 Expr.const (denoteN st.ns n) (denoteLs st.lss us)
  | .app g a => opt2 Expr.app (denoteE st g) (denoteE st a)
  | .lam ty b m => opt2 (fun x y => Expr.lam x y m) (denoteE st ty) (denoteE st b)
  | .forallE ty b m =>
    opt2 (fun x y => Expr.forallE x y m) (denoteE st ty) (denoteE st b)
  | .letE ty w b => opt3 Expr.letE (denoteE st ty) (denoteE st w) (denoteE st b)
  | .lit l => some (.lit l)
  | .proj n k e => opt2 (fun nm x => Expr.proj nm k x) (denoteN st.ns n) (denoteE st e)

/-! ## ============================================================
    `fresh` HOLDS ONLY LOCALLY — the promote window's invariant
    (task #97-P5-Fresh)

**This section is additive: `NWFAt`/`LWFAt`/`LsWF`/`EWFAt` above are
untouched, `fresh` included.**  What it adds is the strictly weaker sibling of
each, without the freshness clauses, and the forgetful map into it.

### Why `fresh` is not a global invariant

`fresh` says *"a view in the scratch cons table is not in the persistent
one"*.  Task #97-P5-Specs round 2's **finding 17** proved it incompatible with
promotion — `NStore.internPersistent_breaks_fresh` (`Arena/WFProofs.lean`) is
that proof — and the incompatibility is in the running code, not in the model:
`NStore::intern_persistent` probes the PERSISTENT cons table only, so
promoting a scratch node whose view is not yet persistent genuinely creates a
second handle for that view, until `dropScratch`.

The transient reading of that — *"`fresh` is broken only between a promotion
and the `dropScratch` that follows it"* — is what `Arena/Store.lean`'s
`internPersistent` note already says, and it is true but not the whole
reason.  **The deciding reason is parallel checking.**  DESIGN §8.3's arena
design gives each worker of a parallel check its OWN scratch tier over one
shared, immutable persistent tier: the persistent tier does not move during
phase B, and each worker appends to a scratch tier of its own.  With several
scratch tiers live at once, each may hold its own handle for the same view —
two workers that both build `app f a` out of the same persistent children get
two scratch handles for one view, and neither is in the persistent table.  A
GLOBALLY quantified `fresh` was therefore never coherent with the design the
arena is built for; the promote collision is only where it surfaced first.

So `fresh` is a **local** fact — true of a store that has not promoted into a
live scratch tier, which is every store the checker's phase B reads — and the
proofs that consume it (`denoteN_inj`, `denoteE_inj`, `denoteL_inj`, and the
ten-plus files above them) keep consuming it exactly where they do today.
What moves is only the promote window: `internPersistent` and the walks that
call it are stated at the weak invariant below, and `dropScratch` closes the
bracket by restoring `fresh` vacuously.

### The shape

One weak sibling per store, clause for clause with the strong one minus
`fresh` (and minus `bmFresh` at the expression store), each nesting the WEAK
invariant of the store below it — because the name, level and level-list
promotions append to those nested tiers and break their `fresh` too.
`Bridge/Promote/StoreP.lean`'s `EWFAtP` is the same idea one tier up; it
nests the STRONG `LsStoreWF`, which is right for `EStore.internPersistent`
alone and wrong for the walk that promotes names and levels (see this task's
DESIGN section). -/

/-- con-leche: none — arena infrastructure; `NWFAt` minus `fresh`: the name
store's invariant while a promotion is in flight. -/
structure NWFAt' (st : NStore) (rk : NIdx → Nat) : Prop where
  childOK : ∀ i v, st.view i = some v → ∀ c ∈ v.children,
    (st.view c).isSome = true ∧ rk c < rk i ∧
      (i.isPersistent = true → c.isPersistent = true)
  rankP : ∀ i, i.isPersistent = true → (st.view i).isSome = true →
    rk i < st.persCount
  rankS : ∀ i, i.isPersistent = false → (st.view i).isSome = true →
    rk i < st.nodeCount
  consP : ∀ v i, st.pers.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scr.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = NTables.empty

/-- con-leche: none — arena infrastructure; the name store is
promotion-well-formed. -/
def NStoreWF' (st : NStore) : Prop := ∃ rk, NWFAt' st rk

/-- con-leche: none — arena infrastructure; `LWFAt` minus `fresh`, over the
weak name invariant. -/
structure LWFAt' (st : LStore) (rk : LIdx → Nat) : Prop where
  ns : NStoreWF' st.ns
  childOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lchildren,
    (st.view c).isSome = true ∧ rk c < rk i ∧
      (i.isPersistent = true → c.isPersistent = true)
  nchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.nchildren,
    (st.ns.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  rankP : ∀ i, i.isPersistent = true → (st.view i).isSome = true →
    rk i < st.persCount
  rankS : ∀ i, i.isPersistent = false → (st.view i).isSome = true →
    rk i < st.nodeCount
  consP : ∀ v i, st.pers.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scr.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = LTables.empty
  sync : st.scratchOn = st.ns.scratchOn

/-- con-leche: none — arena infrastructure; the level store is
promotion-well-formed. -/
def LStoreWF' (st : LStore) : Prop := ∃ rk, LWFAt' st rk

/-- con-leche: none — arena infrastructure; `LsWF` minus `fresh`, over the
weak level invariant. -/
structure LsWF' (st : LsStore) : Prop where
  ls : LStoreWF' st.ls
  lchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v,
    (st.ls.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  consP : ∀ v i, st.pers.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scr.find? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = LsTables.empty
  sync : st.scratchOn = st.ls.scratchOn

/-- con-leche: none — arena infrastructure; the level-list store is
promotion-well-formed. -/
def LsStoreWF' (st : LsStore) : Prop := LsWF' st

/-- con-leche: none — arena infrastructure; `EWFAt` minus `fresh` and
`bmFresh`, over the weak level-list invariant. -/
structure EWFAt' (st : EStore) (rk : EIdx → Nat) : Prop where
  lss : LsStoreWF' st.lss
  childOK : ∀ i v, st.view i = some v → ∀ c ∈ v.echildren,
    (st.view c).isSome = true ∧ rk c < rk i ∧
      (i.isPersistent = true → c.isPersistent = true)
  nchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.nchildren,
    (st.ns.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  lchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lchildren,
    (st.ls.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  lschildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lschildren,
    (st.lss.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  rankP : ∀ i, i.isPersistent = true → (st.view i).isSome = true →
    rk i < st.persCount
  rankS : ∀ i, i.isPersistent = false → (st.view i).isSome = true →
    rk i < st.nodeCount
  bmChildOK : ∀ i ty b mi, st.viewBindI i = some (ty, b, mi) →
    (st.viewBM mi).isSome = true ∧ (i.isPersistent = true → mi.isPersistent = true)
      ∧ mi.tag = 0
  consP : ∀ v i, st.persFind? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  /-- **Only the forward half of `consS` survives a promotion** (task
  #97-P5-Fresh's second finding): `EStore.internBMPersistent` moves a binder
  view's CONS KEY, because the key holds the datum HANDLE and `findBM` probes
  the persistent datum table first.  Promote a datum that only the scratch
  tier held and every scratch binder node interned under the old (scratch)
  handle becomes unreachable through `scrFind?` — `consS`'s `←` direction
  fails at it, while the node itself still decodes.  What is still true, and
  what canonicity actually rests on, is that the scratch cons table never
  LIES: a handle it does answer decodes to the view it was asked about. -/
  consSof : ∀ v i, st.scrFind? v = some i →
    (st.view i = some v ∧ i.isPersistent = false)
  bmConsP : ∀ m i, st.pers.findBM m = some i ↔
    (st.viewBM i = some m ∧ i.isPersistent = true ∧ i.tag = 0)
  bmConsS : ∀ m i, st.scr.findBM m = some i ↔
    (st.viewBM i = some m ∧ i.isPersistent = false ∧ i.tag = 0)
  bmKeyP : ∀ v mj i, st.pers.find? v mj = some i →
    v.bmOf = none ∨ ∃ m, st.pers.findBM m = some mj
  /-- `bmKeyS` weakened for the same reason: *"the scratch cons table's datum
  keys DECODE"* rather than *"`findBM` answers them"*, because promoting a
  datum is exactly what stops `findBM` answering the scratch handle. -/
  bmKeyS : ∀ v mj i, st.scr.find? v mj = some i →
    v.bmOf = none ∨ (st.viewBM mj).isSome = true
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  bmDerExact : ∀ i m, st.viewBM i = some m → st.bmDer i = (hash m.pw, m.pw.hasParams)
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  bmCapP : st.pers.bmSize ≤ Idx.idxCap
  bmCapS : st.scr.bmSize ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = ETables.empty
  sync : st.scratchOn = st.lss.scratchOn

/-- con-leche: none — arena infrastructure; **the promotion-window store
invariant**: `StoreWF` with the freshness clauses dropped at every tier. -/
def StoreWF' (st : EStore) : Prop := ∃ rk, EWFAt' st rk

/-! ### Forgetting the freshness clauses

Four one-liners: the strong invariant is the weak one.  Every consumer of the
weak invariant can therefore be fed by a caller that holds the strong one,
which is what makes the whole restatement additive. -/

theorem NWFAt'.of_wf {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    NWFAt' st rk :=
  { childOK := h.childOK, rankP := h.rankP, rankS := h.rankS, consP := h.consP,
    consS := h.consS, derExact := h.derExact, sizedP := h.sizedP,
    sizedS := h.sizedS, capP := h.capP, capS := h.capS, scrOff := h.scrOff }

theorem NStoreWF'.of_wf {st : NStore} (h : NStoreWF st) : NStoreWF' st :=
  let ⟨rk, h⟩ := h; ⟨rk, NWFAt'.of_wf h⟩

theorem LWFAt'.of_wf {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    LWFAt' st rk :=
  { ns := NStoreWF'.of_wf h.ns, childOK := h.childOK, nchildOK := h.nchildOK,
    rankP := h.rankP, rankS := h.rankS, consP := h.consP, consS := h.consS,
    derExact := h.derExact, sizedP := h.sizedP, sizedS := h.sizedS,
    capP := h.capP, capS := h.capS, scrOff := h.scrOff, sync := h.sync }

theorem LStoreWF'.of_wf {st : LStore} (h : LStoreWF st) : LStoreWF' st :=
  let ⟨rk, h⟩ := h; ⟨rk, LWFAt'.of_wf h⟩

theorem LsWF'.of_wf {st : LsStore} (h : LsWF st) : LsWF' st :=
  { ls := LStoreWF'.of_wf h.ls, lchildOK := h.lchildOK, consP := h.consP,
    consS := h.consS, derExact := h.derExact, sizedP := h.sizedP,
    sizedS := h.sizedS, capP := h.capP, capS := h.capS, scrOff := h.scrOff,
    sync := h.sync }

theorem LsStoreWF'.of_wf {st : LsStore} (h : LsStoreWF st) : LsStoreWF' st :=
  LsWF'.of_wf h

/-! The expression store's own `of_wf` is in `Arena/WFProofs.lean`'s
append-only section, not here: the weakened `bmKeyS` needs
`EWFAt.viewBM_of_findBM` to turn *"`findBM` answers this handle"* into
*"this handle decodes"*, and that lemma lives one file up. -/

/-! ### A promotion's added precondition: the view's children are persistent

`Arena/Store.lean`'s `internPersistent` note: *"`childOK` carries
`i.isPersistent → c.isPersistent`, so the view handed to `internPersistent`
must have PERSISTENT CHILDREN"*.  `intern`'s persistent branch gets this for
free from `scrOff`; a promotion gets it by construction, because it promotes
the children first. -/

/-- con-leche: none — arena infrastructure; a name view's handles are all
persistent. -/
def NViewPers (v : NNodeView) : Prop := ∀ c ∈ v.children, c.isPersistent = true

/-- con-leche: none — arena infrastructure; a level view's handles are all
persistent. -/
structure LViewPers (v : LNodeView) : Prop where
  lvl : ∀ c ∈ v.lchildren, c.isPersistent = true
  nm : ∀ c ∈ v.nchildren, c.isPersistent = true

/-- con-leche: none — arena infrastructure; a level-list view's handles are
all persistent. -/
def LsViewPers (v : LsNodeView) : Prop := ∀ c ∈ v, c.isPersistent = true

/-- con-leche: none — arena infrastructure; an expression view's handles are
all persistent, at all four handle kinds. -/
structure EViewPers (v : ENodeView) : Prop where
  expr : ∀ c ∈ v.echildren, c.isPersistent = true
  nm : ∀ c ∈ v.nchildren, c.isPersistent = true
  lvl : ∀ c ∈ v.lchildren, c.isPersistent = true
  lst : ∀ c ∈ v.lschildren, c.isPersistent = true

end ConRon.Arena
