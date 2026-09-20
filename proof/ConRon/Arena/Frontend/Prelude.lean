/-
# `ConRon.Arena.Frontend.Prelude` — the built-in prelude (task #97e)

con-leche's `ConLeche/Frontend/Prelude.lean`: the checker's own little prelude
— the six pinned basis blocks (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, `Quot`
with its soundness axiom), the `Bool` block, and the `And` block pinned by
design — as a lean4export-format stream parsed by the ORDINARY parser
(`parseExportD`) into declaration records.  `preparePrelude` puts them at the
front of every stream it prepares, which is what "in the env initially and
unconditionally" means in practice.

**Where the text comes from.**  con-leche's `builtinPreludeText` is an
`include_str` of its own committed `pins/<toolchain>.prelude.ndjson`; this is
the same `include_str` of the same file, reached through the con-leche lake
package directory (`proof/.lake/packages/con-leche`, `lake-manifest.json`'s
`packagesDir`).  That makes this module's `.olean` depend on a path outside
the repository, which is exactly the objection `scripts/gen-prelude.sh` raised
for the Rust port — where the answer was a generated constant committed inside
the crate (`crates/con-ron-core/src/frontend/prelude_text.rs`) with a
`--check` gate.  (B) will want the same; the brief for task #97e part 1 says
reading it from the package directory is fine for now, and it is recorded as a
follow-up rather than left unsaid.

**Why the parse is monadic where con-leche's is a 0-ary `def`.**  con-leche
parses the text once at module initialisation, because its parse is pure and
its result owns nothing but `Expr` trees.  The arena's parse INTERNS into the
`EStore` the `AM` state carries, so the prelude's nodes must land in the same
store the stream's do — that is the whole point of the persistent tier — and
the driver runs this once, first, before the stream's own chunks.  It is the
same deviation `crates/con-ron-core/src/frontend/prelude.rs` records for the
Rust port, for the same reason.

The prelude has no mutual or nested block, so the `Modeller` it is parsed with
cannot change the result; the driver passes the same one it parses the stream
with, as the Rust port does.
-/
import ConRon.Arena.Frontend.Prepare

namespace ConRon.Arena.Frontend

/-- con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText — the
committed prelude for the pinned toolchain (`lean-toolchain`), embedded at
build time.  The path is con-leche's own `pins/` directory inside its lake
package; a toolchain bump regenerates that file and re-points both spellings
(con-leche's `include_str` and this one). -/
def builtinPreludeText : String :=
  include_str "../../../.lake/packages/con-leche/pins/leanprover-lean4-v4.33.0.prelude.ndjson"

/-- con-leche: ConLeche/Frontend/Prelude.lean:64-68 builtinPreludeE — the
parsed, indexed prelude: an error channel because a committed file can in
principle be corrupted, and a prelude that does not parse must be a loud error
rather than a silently empty prelude. -/
def builtinPreludeE (md : Modeller) : AM (Except (CheckError × Nat) PreludeIx) := do
  match ← parseExportD md builtinPreludeText with
  | .error e => pure (.error e)
  | .ok r => pure (.ok ⟨r.decls⟩)

end ConRon.Arena.Frontend
