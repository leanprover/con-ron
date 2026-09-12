/-
`con-ron-gen-tables`: write the Rust core's build-time tables (DESIGN.md
§5 P1.5, task #22).

  cd proof && lake exe con-ron-gen-tables            # write the file
  cd proof && lake exe con-ron-gen-tables --stdout   # print it instead
  cd proof && lake exe con-ron-gen-tables --count    # the DAG census only

The tables con-leche computes at *elaboration* time and the Rust core
therefore has to carry as source.  Today: the annotated basis blocks
(`ConLeche.BasisKind.declsA`).  The Nat-op pin variants
(`ConLeche.natOpPinSets`) are two orders of magnitude bigger; the
task-#22 log records the measurement and the recommendation, and the
emitter in `ConRon/Gen/Emit.lean` already handles every `Expr`
constructor they use.

The output is deterministic: the emission order is the interning
worklist's, which is a function of the value alone.
-/
import ConRon.Gen.Emit
import ConLeche.Kernel.NatOpPins

namespace ConRon.Gen

open ConLeche

/-- The basis blocks, with the Rust function name for each. -/
def basisBlocks : List (BasisKind × String × String) :=
  [(.eqK, "EqK", "eq"), (.natK, "NatK", "nat"), (.punitK, "PunitK", "punit"),
   (.emptyK, "EmptyK", "empty"), (.falseK, "FalseK", "false"),
   (.quotK, "QuotK", "quot")]

/-- The generated file's module header: the module-level `con-leche:`
citation (DESIGN.md §3.7) and the imports the bodies need. -/
def basisHeader : Array String := #[
  "//! The annotated basis blocks, generated (DESIGN.md §5 P1.5, task #22).",
  "//!",
  "//! con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA",
  "//!",
  "//! **Generated file — do not edit.**  Written by",
  "//! `proof/ConRon/Gen/Main.lean` (`cd proof && lake exe con-ron-gen-tables`)",
  "//! from con-leche's own `BasisKind.declsA`, which con-leche computes while",
  "//! `ConLeche/Kernel/BasisA.lean` elaborates: the `#annotate_basis` command",
  "//! (`ConLeche/Kernel/BasisGen.lean`) runs the checker's annotation pass over",
  "//! the hand-written raw pins (`ConLeche/Kernel/Basis/*.lean`) in install",
  "//! order.  The Rust core has no elaborator, so the *result* is carried as",
  "//! source; `proof/ConRon/Refine/BasisTables.lean` proves that what these",
  "//! functions build abstracts to `ConLeche.BasisKind.declsA`.",
  "//!",
  "//! The module-level citation above covers every item in the file: the whole",
  "//! module is one Lean declaration's value (DESIGN.md §3.7, task #22).",
  "//!",
  "//! Shape: one `let` per distinct interned node (`Name`, `Level`,",
  "//! `PropWhen`, `Expr`), in dependency order, each a call to the port's own",
  "//! smart constructor, each use a `dup` — so the table is the same DAG",
  "//! con-leche's value is, and the generated Lean model is a `do` chain of",
  "//! constructor calls that the refinement lemmas evaluate.",
  "",
  "use crate::kernel::env::BasisKind;",
  "use crate::kernel::env::ConstantInfo;",
  "use crate::kernel::env::ConstantVal;",
  "use crate::kernel::env::IndCaps;",
  "use crate::kernel::env::RecRule;",
  "use crate::kernel::env::RecRuleFire;",
  "use crate::kernel::expr;",
  "use crate::kernel::expr::BinderMeta;",
  "use crate::kernel::level;",
  "use crate::kernel::level::Level;",
  "use crate::kernel::name;",
  "use crate::kernel::name::Name;",
  "use crate::kernel::prop_when;",
  ""]

/-- The dispatcher, `BasisKind.declsA` itself. -/
def basisDispatch : Array String :=
  #["/// The annotated constants of one basis block, in dependency order.",
    "pub fn basis_decls_a(k: &BasisKind) -> Vec<ConstantInfo> {",
    "    match k {"]
  ++ (basisBlocks.map fun (_, ctor, nm) =>
        s!"        BasisKind::{ctor} => basis_decls_{nm}(),").toArray
  ++ #["    }", "}", ""]

/-- The whole generated file. -/
def basisTables : String :=
  let fns := basisBlocks.flatMap fun (k, _, nm) =>
    (gDeclsFn s!"basis_decls_{nm}"
      s!"/// The annotated `{nm}` block (`BasisKind.declsA .{nm}K`)."
      (BasisKind.declsA k)).toList
  String.intercalate "\n" ((basisHeader.toList ++ fns ++ basisDispatch.toList)) ++ "\n"

/-! ## The census

`--count` reports how many distinct interned nodes each table reaches —
the number of `let`s a generated function would carry, which is the
number the task-#22 sizing rests on. -/

def censusOf (act : G Unit) : String :=
  let st := (act.run {}).2
  s!"names={st.names.size} levels={st.levels.size} pws={st.pws.size} \
exprs={st.exprs.size} total={st.names.size + st.levels.size + st.pws.size + st.exprs.size} \
lines={st.out.size}"

def pinSetAct (s : NatOpPinSet) : G Unit := do
  let _ ← [s.divPin, s.modPin, s.gcdPin, s.landPin, s.lorPin, s.xorPin,
           s.shiftLeftPin, s.shiftRightPin].mapM gExpr
  let _ ← (s.divProofs ++ s.modProofs ++ s.gcdProofs ++ s.landProofs ++ s.lorProofs
           ++ s.xorProofs ++ s.shiftLeftProofs ++ s.shiftRightProofs).mapM gExpr
  return ()

def census : String :=
  let basis := basisBlocks.map fun (k, _, nm) =>
    s!"basis {nm}: " ++ censusOf (do let _ ← (BasisKind.declsA k).mapM gConstantInfo; return ())
  let pins := natOpPinSets.map fun s => s!"pinset {s.toolchain}: " ++ censusOf (pinSetAct s)
  String.intercalate "\n" (basis ++ pins)

/-- One toolchain's pin variant as Rust, flattened to the `Vec<Expr>` of its
eight pins followed by its certificate blobs — **measurement only** (task
#22): the crate has no `NatOpPinSet` yet, and what the sizing needs is the
cost of the node DAG, which this reproduces exactly.  Written to `_tmp/`,
never to the crate. -/
def pinTable (i : Nat) (s : NatOpPinSet) : String :=
  let pins := [s.divPin, s.modPin, s.gcdPin, s.landPin, s.lorPin, s.xorPin,
               s.shiftLeftPin, s.shiftRightPin]
  let proofs := s.divProofs ++ s.modProofs ++ s.gcdProofs ++ s.landProofs
             ++ s.lorProofs ++ s.xorProofs ++ s.shiftLeftProofs ++ s.shiftRightProofs
  let body := runBody do
    let v ← gExprVec (pins ++ proofs)
    line s!"{v}"
  String.intercalate "\n"
    (["//! con-leche: none — task-#22 sizing spike for the Nat-op pins",
      "",
      "use crate::kernel::expr;",
      "use crate::kernel::expr::Expr;",
      "use crate::kernel::expr::Literal;",
      "use crate::kernel::level;",
      "use crate::kernel::level::Level;",
      "use crate::kernel::name;",
      "use crate::kernel::name::Name;",
      "use crate::kernel::prop_when;",
      "use crate::ron::nat;",
      "",
      s!"pub fn nat_op_pins_v{i}() -> Vec<Expr> {lb}"] ++ body.toList ++ ["}", ""])

def usage : String :=
  "usage: con-ron-gen-tables [--stdout | --count | --pins <i> <out>]"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => do
    let out := "../crates/con-ron-core/src/kernel/basis_tables.rs"
    IO.FS.writeFile out basisTables
    IO.println s!"wrote {out} ({basisTables.length} chars)"
    return 0
  | ["--stdout"] => do IO.print basisTables; return 0
  | ["--count"] => do IO.println census; return 0
  | ["--pins", i, out] => do
    match i.toNat?, natOpPinSets[i.toNat?.getD 0]? with
    | some k, some s => do
      IO.FS.writeFile out (pinTable k s)
      IO.println s!"wrote {out} for {s.toolchain}"
      return 0
    | _, _ => do IO.eprintln usage; return 2
  | _ => do IO.eprintln usage; return 2

end ConRon.Gen

def main (args : List String) : IO UInt32 := ConRon.Gen.main args
