/-
`ConRon.Refine.FEnv` — the refinement of `crates/con-ron-core/src/kernel/fenv.rs`
against `ConLeche/Kernel/FEnv.lean` (task #46, `Refine/CORE_PLAN.md` step 2).

`FEnv` is the second thing the port cannot abstract by a *function*: its index
is a `ron::HashMap` and con-leche's is a `Std.HashMap`, whose internal layout no
function of ours reproduces.  So the tier's currency here is a **relation**,
`FEnvRel fe lfe`, with three clauses:

* `absEnv fe.env = lfe.env` — an equation, because `Env.consts` is a list on
  both sides (the port stores it reversed, which `absEnv` reverses back: task
  #50);
* `fe.visible_below.val = lfe.visibleBelow` — the installation counter bound
  (`u64` in the port, `Nat` in the Lean, DESIGN.md §3.3);
* `HashMap.RelOn NameWF fe.idx lfe.idx absName absIdxEntry` — task #16's
  abstract-map relation, restricted to well-formed keys (`Refine/HashMapWF.lean`
  explains why the restriction is forced).

`find`/`findProj?` agreement is then a *lemma*, not a clause, which is what
con-leche's `coreKnotI_congr` consumes.

`FEnvWF` is the hereditary invariant: the environment is well formed, the index
satisfies `ron::HashMap`'s own `Inv`, its keys are well-formed names and its
stored constants are well-formed records.
-/
import ConRon.Refine.HashMapWF
import ConRon.Refine.Env
import ConLeche.Kernel.FEnv

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.FEnv

/-! ## The index entry, and the key dictionary's exactness -/

/-! ## Values in a table

`HashMap.KeysOk` says what the keys are; the index also has to say what the
*values* are, because a lookup hands its caller a stored `ConstantInfo` and the
knot's induction needs it well formed.  Stated over `toFun`, so that
`insert`'s conclusion (`toFun m' = Function.update (toFun m) k (some v)`)
discharges it in one step. -/

/-! ## The relation and the invariant -/

/-! ## The indexed lookup -/

/-! ## The index build

The port builds the index *forward* over `env.consts`, which is the cited list
**reversed** (task #50), threading the table and the counter down; the cited
`mkFEnvGo` recurses over the cited list, i.e. from this `Vec`'s back.  The
invariant that connects them is `absPrefixIdx`: the abstract index of the first
`i` stored constants. -/

/-! ## `push`

`ci :: fe.env.consts` is `Vec::push` in the port: `Env.consts` is the cited list
**reversed** (task #50, `env.rs`'s `Env` deviation), so the cons is a push at the
back — `O(1)` amortised, as Lean's is, and modelled exactly
(`Aeneas/Std/Vec.lean:152-159`: `List.concat`).

This is where the tier earned its keep.  Until task #50 the port wrote the cons
as `consts.insert(0, rc)`, i.e. Rust's `Vec::insert`, and
`Aeneas/Std/Vec.lean:167-172` models *that* as `v.val.set i x` — an **overwrite**
where Rust inserts, failing outright at `i = len`.  The `idx` and
`visible_below` clauses were provable (`push_idx_refines` below), the `absEnv`
clause was *false of the model*, and `push_refines` was this tier's one `sorry`
with nothing wrong in the Rust.  The library bug is `AENEAS_FINDINGS.md` §3.9 and
ask #1, and the port's answer is to store the list the other way round: no
function of `crates/con-ron-core` calls `Vec::insert` any more, so no model of
ours depends on that primitive. -/

/-! ## `dup` -/

/-! ### The bridge the callers of `dup` need (task #59)

`dup_refines` relates the copy to the *canonical* Lean `FEnv` — `mkFEnv` of the
copied environment, restricted to the visibility counter — because that is what
the rebuild computes.  But `ConLeche/Cached/CheckerC.lean`'s stages pass their
own persistent `lfe` across the copy (`checkNativePassS` is the first one), so
what those compositions need is `FEnvRel fe lfe → FEnvRel (dup fe) lfe`.

That is **not** true of an arbitrary `lfe`: `FEnvRel` pins `lfe.idx` only on
the image of the well-formed names, so an `lfe` whose index disagrees with its
own environment is related to `fe` and not to the rebuild.  The missing
ingredient is a property of `fe` alone — that `fe`'s index already *is* the
rebuild of `fe`'s environment — and that is exactly `dup_refines`' own
conclusion, so it is named here and carried:

* `dup` establishes it (`dup_canon`), and so does `mk_fenv` (`mk_fenv_canon`),

which is how every `FEnv` a stage copies was built, so the hypothesis is
discharged at the call sites and nothing is weakened.  (`push` does *not*
preserve it on a **restricted** view: `FEnv.push` stamps the new entry with
`visibleBelow`, while the rebuild stamps it with the constant count, and the
two differ exactly when the view hides something.  The stages that copy an
index copy a `dup`/`mk_fenv` product, so that gap is not in the way.) -/

/-! ### The index key *is* the stored constant's name (task #59)

`ConLeche/Kernel/Env.lean:636` defines `Env.find? env n = env.consts.find?
(·.name == n)`, so a found record's name is the name it was found under.  The
*indexed* reading cannot see that on its own — `FEnv.find?` reads a hash map,
and `FEnvRel` says nothing about which key a value sits at — but the rebuild
`mkFEnvGo` only ever inserts `ci` at `ci.name`, so it holds of every canonical
view.  `modeled::check_proj_iota_body` needs exactly this: it builds the
constructor spine head from the *looked-up* `cvj.name` where `checkProjIotaF`
writes the name it looked up under. -/

/-! ## The projection lookup and the slot queries -/

/-! ## What is not here

`fenv::tower_slots_all_f`/`_from` and `fenv::rec_slots_all_f`/`_from` are
`ConLeche/Kernel/Core.lean`'s `towerSlotsAll`/`recSlotsAll` read through the
index (`fenv.rs`'s citations say so), i.e. `(List.range nF).all …`.  Their
refinement is the `List.range'` suffix bookkeeping of a `u64` index recursion
and nothing to do with the relation this file is about, so they go with the rest
of `Core.lean`'s readers in `Refine/CoreK/` (`CORE_PLAN.md` step 4).
`rec_slot_ok_refines` above is the one of the four the relation *does* settle.

`andRescueSlotsF` and the four indexed guard twins (`natLitSupportedF`,
`strLitSupportedF`, `natOpGuardF`, `natOpStoredF`) are not ported yet
(`fenv.rs`'s module note), so they have nothing to refine.

## Axiom census (DESIGN.md §5, the P3 gate)

Lean's own three axioms and no more.  `Classical.choice` appears because the
abstract map `HashMap.toFun` is defined with `DecidableEq` on the port's key
type, which `Refine/Abs.lean` supplies classically (see the note there); nothing
here reaches `ConRon.Generated.kernel.pins_text.PINS_TEXT`, whose string
constant carries a `native_decide` axiom (task #43).  Task #46 left
`push_refines` a `sorry` because it was false of the model of `Vec::insert`;
task #50 removed that call from the port and the lemma is now in the census
with the rest. -/

end ConRon.Refine.FEnv
