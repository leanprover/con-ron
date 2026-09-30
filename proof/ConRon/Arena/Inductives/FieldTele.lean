/-
# `ConRon.Arena.Inductives.FieldTele` — constructor fields' telescopes
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/FieldTele.lean` over handles, as far as the
executed checker reads it: `Expr.piBinders` (the recogniser's telescope
reading, the positivity check's container telescopes, the recursor pre-pass).
The rest of con-leche's module — `RecFieldKind`, `recIdxOf`, `Expr.mkPisOf`,
`Expr.mentionsFvar` and its memo — is read by con-leche's model tier only, so
it has neither a Rust nor a twin counterpart (`scripts/provenance-skip.txt`
names each).  The Rust twin is `arena::inductives::field_tele`.
-/
import ConRon.Arena.Monad

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/FieldTele.lean:45-52 Expr.piBinders
All leading `∀` binders of an expression (outermost first) and the body.  The
fuel is the store walk's (the telescope is a chain of nodes).  The Rust pushes
on the way in where this conses on the way out, which is the same list. -/
def piBinders : Nat → EIdx → AM (List (EIdx × BinderMeta) × EIdx)
  | 0, _ => fail (.internal "fuel exhausted: piBinders")
  | fuel + 1, h => do
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (ty, b, m) => do
        let (bs, e) ← piBinders fuel b
        pure ((ty, m) :: bs, e)
    else pure ([], h)

end ConRon.Arena
