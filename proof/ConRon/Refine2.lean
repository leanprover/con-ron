/-
# `ConRon.Refine2` — **Theorem 2**, the Aeneas refinement of the arena checker

DESIGN.md §8.2's second theorem: *the Aeneas model of the Rust `check_decls`
accepting implies (B) accepting with the abstracted state/result, over the
whole outcome; the port's `Native` error claims nothing.*  Task #97 P5.

`ConRon.Refine` is the `Expr`-tree checker's refinement tier, of which 47
modules survived the arena swap (task #97-SWAP §5) because their SUBJECT
survived — `ron::{nat,hashmap,hashmap2}`, `kernel::{name,level,prop_when,
expr,…}` and the pinned data the arena interns at startup.  **This tier reuses
them and does not duplicate them**: `Refine/Abs.lean`'s idiom (`rust_norm`,
`rust_grind`, the two simp sets, `ErrSim`/`RunOk`), `Refine/HashMap2{,WF}`'s
`Inv`/`RelOn`/`Eq2Fwd`/`DupId` kit, `Refine/{Name,Level,PropWhen,Expr}`'s
value abstractions and their WF predicates, and `Refine/Nat.lean`'s forward
readings of the machine-word operations are all imported rather than rebuilt.

## The layout

| file | what |
|---|---|
| `Refine2/Idiom.lean` | round 3's three asks: the `@[grind ext]` erasure, `rust_grind2`'s `(splits := 40)`, and the `u32`/`u64` conversions |
| `Refine2/AbsStore.lean` | the handles, the node records, the four node views, `TblRel` and the four stores — `absStore (pers, st)` |
| `Refine2/Inv.lean` | the Rust-side invariant: `HashMap2.Inv` and `KeysOk` per table, and the eighteen `Eq2Fwd` + five `DupId` obligations, discharged |
| `Refine2/AbsState.lean` | `Memos`, `Caches`, `Pins`, `AStateRel`/`AStateInv`, and the `arena::env` declaration layer |
| `Refine2/Shape.lean` | `AErrSim`/`AOut`/`Sim`/`SimR`/`SimS` — the shape of a Theorem-2 lemma |
| `Refine2/Specs.lean` | the inversion layer, one `_run` lemma per primitive, keyed on the Rust equation |
| `Refine2/Dup.lean` | the `arena::env` record copies are identities (the `*_dup_abs` family, moved down by task #97-P5-Front round 2) |
| `Refine2/ExprOps/*.lean` | the `arena::expr_ops` tier: 120 functions, one `_refines` each |
| `Refine2/Core/*.lean` | the `arena::core` tier: `KnotRel`, the knot's memo floor, the fuel induction and the six entry points |
| `Refine2/Inductives/*.lean` | the `arena::inductives` tier: 306 functions, one `_refines` each, and `IndRel` |
| `Refine2/Frontend/*.lean` | the `arena::frontend` tier: the syntax vocabulary, `StateDRel`, the six Rust modules, and `parse_chunks_refines` / `builtin_prelude_e_refines` |
| `Refine2/Tactic/*.lean` | task #97-T2-TACTIC: the `lockstep` tactic and `@[lockstep]` attribute (`Lockstep.lean`, `Attr.lean`), the primitive pairs (`Prims.lean`), and the measured sample (`Sample*.lean`); built by the library's `globs`, imported by nothing |
-/
import ConRon.Refine2.Idiom
import ConRon.Refine2.AbsStore
import ConRon.Refine2.Inv
import ConRon.Refine2.AbsState
import ConRon.Refine2.Shape
import ConRon.Refine2.Specs
import ConRon.Refine2.Dup
import ConRon.Refine2.ExprOps.Pure
import ConRon.Refine2.ExprOps.Read
import ConRon.Refine2.ExprOps.Mut
import ConRon.Refine2.Core
import ConRon.Refine2.Checker.Shape
import ConRon.Refine2.Promote.Intern
import ConRon.Refine2.Promote.Promote
import ConRon.Refine2.Checker.KnotHyp
import ConRon.Refine2.Checker.Pins
import ConRon.Refine2.Checker.Canon
import ConRon.Refine2.Checker.Axioms
import ConRon.Refine2.Checker.Spec
import ConRon.Refine2.Checker.Base
import ConRon.Refine2.Checker.DeclCheck
import ConRon.Refine2.Checker.Top
import ConRon.Refine2.Checker.Init
import ConRon.Refine2.Checker.PinsWF
import ConRon.Refine2.Inductives.Top
import ConRon.Refine2.Frontend.Abs
import ConRon.Refine2.Frontend.Text
import ConRon.Refine2.Frontend.Shape
import ConRon.Refine2.Frontend.Types
import ConRon.Refine2.Frontend.Prepare
import ConRon.Refine2.Frontend.NatOpGround
import ConRon.Refine2.Frontend.Spec
import ConRon.Refine2.Frontend.ProjRec
import ConRon.Refine2.Frontend.ExportC
import ConRon.Refine2.Frontend.ExportCInd
import ConRon.Refine2.Frontend.PreludeText
import ConRon.Refine2.Frontend.Top
