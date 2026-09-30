/-
The refinement of `crates/con-ron-core/src/kernel/expr_ops.rs` (task #13) on
its generated model `ConRon.Generated.kernel.expr_ops.*` (DESIGN.md §3.5, P3.3
of §5; task #21).

**What the statements are against.**  Every Rust item of the module implements
the `*Fast` member of one of con-leche's `@[csimp]` families (task #13): the
executed, memoized walk.  The lemma per function is therefore stated against
the **logical** definition of `ConLeche/Kernel/ExprOps.lean` -- `instantiate1`,
`instantiateList`, `liftLooseBVars`, … -- with the memoized walk's own lemma
(`*_go_refines`) as the step, and the `@[csimp]` equation is never needed: a
`*Go_spec`-shaped induction proves the walk equal to the logical function
directly, which is the same argument con-leche's own `@[csimp]` lemma makes.

**Memos.**  Every memo here is local (created empty in the wrapper, dropped on
return).  The invariant is con-leche's own `*MemoInv` -- "every recorded answer
is the real one" (`Inst1MemoInv`, `InstLMemoInv`, … , the eleven `Prop`s task
#13 skipped as not executable) -- transposed onto the port's table through the
*entry list* `ConRon.Refine.HashMap.al_v` rather than through `toFun`.  That is
the one deliberate departure from task #16's `toFun`/`Rel` bridge, and the
reason is `Eq2Spec`: `toFun` is a lookup by *Lean* equality, so every lemma
about it assumes `eq2` decides equality on the whole key type, while
`expr::beq` is exact only on **well-formed** nodes (`Expr.beq_exact`).  The
entry-list view needs no such assumption: `get_mem` says a hit returns a value
that is *in* the table under an `eq2`-equal key, `insert_mem` says an insert
adds nothing but its own pair, and both are proved here without `Eq2Spec` and
without the table invariant `Inv`.  A key recorded in the memo is well formed
(that is a clause of every `MemoInv` below), so `beq`'s exactness applies at
exactly the pairs the walks compare.
-/
import ConRon.Refine.Expr
import ConRon.Refine.HashMap
import ConLeche.Kernel.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## Two plumbing steps the repacked node added (task #38)

Since the node was repacked, every place that used to write the binder datum
inline calls the smart constructor `expr::binder_meta`; and the `Vec`
accumulators are pre-sized (`Vec::with_capacity`, task #34).  Both are the
identity in the model, and both are stated as `simp` lemmas so that the bind
they add collapses inside the `simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, …]` step
every walk below already runs.  (Task #38 made `BinderMeta.pw` an
`Arc<PropWhen>`; task #90 shrank `PropWhen` to one word's payload and put the
datum back by value, so `binder_meta` no longer allocates -- but it is still
the one constructor every binder goes through, and this lemma is unchanged.) -/

/-- `expr::binder_meta` is the datum wrapper, i.e. the identity. -/
@[simp, rust_reduce, rust_invert] theorem binder_meta_eq (pw : prop_when.PropWhen) :
    expr.binder_meta pw = ok ⟨pw⟩ := by
  simp [expr.binder_meta]

/-- `Vec::with_capacity` is `Vec::new` in the model: an empty list. -/
@[simp] theorem with_capacity_val {α : Type} (c : Std.Usize) :
    (alloc.vec.Vec.with_capacity α c).val = [] := rfl

/-! ## Memo tables as entry lists

The facts every memoized walk below uses, about any key type and with no
assumption on the `Hashable` or `Eq2` dictionary. -/

section Memo

variable {K V : Type} {HashableInst : ron.hashmap.Hashable K}
  {Eq2Inst : ron.hashmap.Eq2 K}

/-! ### Inserts add nothing but their own pair

`Compat` is the one side condition: a *recorded* entry whose key the dictionary
equates to the key being inserted accepts the inserted answer.  It is what
`list_insert`'s replacing arm needs — that arm keeps the *old* key and the new
value — and it holds for every invariant below because `expr::beq` is exact on
well-formed nodes and the invariants only ever speak about a key's
abstraction. -/

/-! ### The memo invariant

`MemoInv KWF absK Q m` is con-leche's `*MemoInv` on the port's table: every
recorded entry has a well-formed key, and its value is what the logical
function gives for the key's *abstraction*.  `KeyExact` is the single fact
about the key dictionary the two hit/insert lemmas need. -/

/-! ### The same two, keyed on the Rust equation (task #71)

`MemoInv.hit`/`MemoInv.set` take the invariant first, which is what a hand
proof wants; a `grind [→ …]` lemma needs the **Rust equation first**, so that
its E-matching trigger is the probe or the insert the inverted body provides
rather than every memo invariant in scope (`Refine/README.md` §"Writing a new
refinement lemma", the first keying rule).  These two are what every memoised
walk registers. -/

end Memo

/-! ## The two memo key types

Five of this file's memos are keyed by `(node, cursor)` (`ExprNatKey`, whose
`Eq2` is `expr::beq` then the `u64`), three by the node alone.  `KeyExact` for
both is `Expr.beq`'s exactness on well-formed nodes (task #20). -/

/-- The `(node, cursor)` key's abstraction: con-leche's `(Expr × Nat)`. -/
def absKey (k : expr_ops.ExprNatKey) : ConLeche.Expr × Nat := (absExpr k.e, k.d.val)

/-- A memo key is well formed when its node is. -/
def KeyWF (k : expr_ops.ExprNatKey) : Prop := ExprWF k.e

@[simp] theorem absKey_mk (e : expr.Expr) (d : Std.U64) :
    absKey ⟨e, d⟩ = (absExpr e, d.val) := rfl

@[simp] theorem KeyWF_mk (e : expr.Expr) (d : Std.U64) : KeyWF ⟨e, d⟩ ↔ ExprWF e := Iff.rfl

/-! ## The memo probes

`memo1_get`/`memo_e_get`/`memo_n_get` are the owning probes of task #13's
deviation 1; each is `HashMap.get` with a `dup` on the hit, so a hit is a
recorded answer and a miss says nothing. -/

/-! ## `instantiate1` (`ExprOps.lean:29-189`)

The recipe every memoized walk of this file follows:

* the statement is **against the logical definition** (`Expr.instantiate1`),
  generalised over the memo and the cursor, and proved by induction on the
  `ExprWF` derivation — which is what supplies both the node's shape
  (`Expr.app_inv` and friends) and the children's well-formedness in one step,
  where the `partial_fixpoint`'s own `fixpoint_induct` would want an admissible
  motive and supply neither (task #20; DESIGN.md task #99-PFIX);
* the five leaf constructors skip the memo, as in the cited code;
* the five rebuilding ones probe it (`MemoInv.hit`), and on a miss recurse and
  write the answer back (`MemoInv.set`).

The generated body destructures *tuples* at every bind (`let (memo1, r) ← …`,
`let (_, memo2) ← insert …`), which `bind_eq_ok_iff` does not see through, so
every such bind is inverted in two steps: `bind_eq_ok_iff.mp` and then
`obtain ⟨_, _⟩` on the pair (task #16's trap). -/

/-! ## Plumbing for the `Vec` walks -/

/-- A `usize`-to-`u64` cast is the identity in the model: `usize` is never
wider than 64 bits (`System.Platform.numBits_eq`). -/
theorem usize_cast_u64_val (x : Std.Usize) :
    (Std.UScalar.cast .U64 x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_greater_numBits_eq _ _ ?_
  rw [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> omega

/-- A `u64`-to-`usize` cast is the identity on values that fit a `usize` --
which is what an in-range index is. -/
theorem u64_cast_usize_val {x : Std.U64} (h : x.val ≤ Std.Usize.max) :
    (Std.UScalar.cast .Usize x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_
  have hpos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  have hmax : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    simp only [Std.Usize.max, Std.Usize.numBits]
    omega
  omega

/-- The empty `Vec` abstracts to the empty list. -/
@[simp] theorem absExprs_new : absExprs (alloc.vec.Vec.new expr.Expr) = [] := rfl

/-- `Vec::index` without an `Inhabited` instance on the element type (the
`getElem!` form of `HashMap.vec_index_eq` is unavailable for `expr::Expr`). -/
theorem vec_index_getElem? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-! ## The `Vec` copies

`levels_copy` and `cons_expr` have no Lean counterpart at all: they are the
`Vec` copies that stand for Lean's shared lists (task #13's deviation 3), so
their lemmas are *raw* `Vec` equations -- the copy is the same list, because
`level::dup` and `expr::dup` are the identity in the model (DESIGN.md §3.2) --
and the abstraction equation follows by `congrArg`. -/

end ConRon.Refine.ExprOps

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`instantiate1_refines` is the file's headline lemma and the deepest chain in it
-- the `(node, cursor)` memo through `HashMap.insert`'s resize, `expr::beq`'s
exactness on well-formed nodes, and the ten smart constructors -- so it is the
one worth pinning. -/

