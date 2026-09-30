/-
`CORE_PLAN.md` step 4 (task #49), the **literal-reduction** leaves of
`crates/con-ron-core/src/kernel/core_k.rs`, refined against
`ConLeche/Kernel/Core.lean`:

* the `Nat`-literal readers and builders --- `natLitToConstructor` (`:266`),
  `rawNatLit?` (`:341`, whose `Cached/StateC.lean:98` twin `rawNatLitC?` is the
  same function), `litToCtorIfNat` (`:334`, twin `Cached/CoreC.lean:84`
  `litToCtorIfNatI` under a `pure`) and the `defeqStep` (`:2371-2631`)
  predecessor probe `succ_of`;
* the `String`-literal constructor form `strLitToConstructor` (`:360`), whose
  `s.toList.foldr` the port spells as the downward index recursion
  `str_lit_cons_from`;
* the equation table `natOpEquations` (`:597`) with its three spine builders
  `nat_eq_s`/`nat_eq_ap1`/`nat_eq_ap2` (the `let`-bound closures of the cited
  block, named because §3.4 forbids closures), and
* **`natOpResult` (`:628`)**, the `Nat`-operation fast path --- the headline
  lemma of this file, and the one pinned in the axiom census;
* `Expr.isBoolTrue` (`:524`), the `Bool`-constructor reader the equation table
  and the fast path both name.

Three things carry the proofs.

**The pinned names are hypotheses.**  Every function here mentions pinned
names (`basis_names::nat_zero_name`, `core_k::nat_add_name`, ...), whose
refinements are landed in `Refine/CoreKNames.lean` and `Refine/BasisNames.lean`
by sibling agents of the same task.  Rather than duplicate them, each lemma
takes what it needs as a `PinnedName` hypothesis --- literally the shape those
files prove (`∀ n, f = ok n → absName n = ln ∧ NameWF n`), so that discharging
them at merge is `exact ⟨fun _ h => nat_add_name_refines h, ...⟩`.  The
seventeen the fast path and the equation table need are bundled as
`NatOpPinned`.

**Exactness of `name::beq`** (`Refine/Name.lean`'s `beq_refines`) is what turns
the port's `if name::beq c &nat_add_name()` cascade into the cited
`if c = natAddName` cascade; it needs `NameWF` on both sides, which is why the
name arguments carry `NameWF` and the `PinnedName` hypotheses carry the
`∧ NameWF n` conjunct.

**No arithmetic is re-proved.**  Every operation `nat_op_result` dispatches on
is `Refine/Nat.lean`'s, used as a black box, and `OpSpec` is an exact
refinement in both directions.  The shifts take the bignum amount unbounded
(task #98-SHIFT; tasks #61/#67 had made an amount beyond `u64` a `Native`
failure), so the port has no failure left here: `nat_op_result_native` still
states that any `Err` is the port's own (`absErrKind ce = none`, what a caller
feeds to `ErrSim.of_none`), and now holds because there is none.

Two local helpers, `const_wf_inv` and `lit_wf_inv`, invert `ExprWF` at a `Const`
and at a `Lit` node (the head name's `NameWF`, the payload's `LiteralWF`); they
belong in `Refine/Expr.lean` beside the `*_inv` family and are *not* added there
by this file, so they are `private` here.  Every other generically named helper
is `private` for the same reason.

**On merge**: `PinnedName` is defined here *and*, character for character, in
`Refine/CoreKNatOps.lean` -- one of the two copies goes, and the vocabulary is
deliberately the same.  `lit_to_ctor_if_nat_refines`'s `hsupp` hypothesis is
`CoreKNatOps.lean`'s `NatLitSupportedSpec` spelled out, at whichever of the two
guard readings the caller has.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## The pinned names, as hypotheses

`PinnedName f ln` is exactly the statement `Refine/CoreKNames.lean` and
`Refine/BasisNames.lean` prove of a pinned name, so a hypothesis of this shape
is discharged by the corresponding `*_name_refines` and nothing else. -/

/-! ## Two plumbing facts -/

/-! ## The `Bool`-constructor reader

`Core.lean:524-529` -- `Expr.isBoolTrue`.  A plain `Bool` equation (§3.5): the
port reads the node's kind and compares the head name, so the content is
`name::beq`'s exactness at the pinned `Bool.true`. -/

/-! ## The three spine builders of the equation table

`Core.lean:597-626` -- the `let`-bound `s`/`ap1`/`ap2` of `natOpEquations`.
§3.4 forbids closures, so the port names them; each is one `mk_const` and one
or two `app`s, and each therefore gets a plain refinement plus `ExprWF`. -/

/-! ## `Nat` literals

`Core.lean:266-346`.  The cited `match n with | 0 | k + 1` of
`natLitToConstructor` is `nat::is_zero` plus `nat::pred` on the bignum
(DESIGN.md §3.3), so the two arms are decided by `Refine/Nat.lean`'s
`is_zero_refines` and closed by its `pred_refines`. -/

/-! ## String literals

`Core.lean:360-371` -- `strLitToConstructor`.  The cited `s.toList.foldr` is the
port's downward index recursion `str_lit_cons_from`, so the statement is on
`s.val.take i` in the task-#5 accumulator shape: at `i = s.len()` that is the
whole list, which is `str_lit_to_constructor`.

The one real content is the code point: the cited Lean builds
`Char.ofNat (lit c.toNat)` from the `Char`s of the `String`, while the port's
code point *is* `c.toNat` (DESIGN.md §3.3).  `StrWF s` -- every stored word is a
valid code point -- is what makes `(Char.ofNat c.val).toNat = c.val`, i.e. what
makes the two agree. -/

/-! ## The `Nat`-operation fast path

`Core.lean:628-654` -- `natOpResult`, **the headline lemma of this file**.  The
port is a fifteen-rung `if name::beq c &nat_X_name()` cascade over `ron::nat`'s
arithmetic; `op_step` below turns one rung into the cited `if c = natXName`
(this is where `name::beq`'s exactness is spent), the `natOpResult_*` bank
evaluates the cited cascade at each pinned name, and `lit_arm_done` /
`const_arm_done` close an arm from the corresponding `Refine/Nat.lean` lemma.
No arithmetic is re-proved here. -/

/-! ## The equation table

`Core.lean:597-626` -- `natOpEquations`, the defining recurrence equations of a
structural-`Nat` operation over constructor forms with free variables `d`,
`d + 1`.  The cited block's `let`-bound locals are spelled out below as
`eqNatTy`/`eqX`/`eqY`/`eqZ`/`eqS`/`eqAp1`/`eqAp2`/`eqBT`/`eqBF` (the port names
the three closures as functions, §3.4), the `natOpEquations_*` bank evaluates
the cited seven-rung cascade at each pinned name, and the arms are then a
transcription: `expr::dup` is the identity, so each pair is exactly one of the
cited ones. -/

/-! The cited cascade at each pinned name. -/

/-! The `Vec::push` chains the port builds the list with. -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The headline lemma: nothing beyond Lean's own three -- no Aeneas library axiom,
nothing from the `Arc` model, nothing from con-leche. -/

end ConRon.Refine.CoreK
