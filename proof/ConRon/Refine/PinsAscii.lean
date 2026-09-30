/-
Every byte `ConRon.Refine.PinsDec` accepts is ASCII (task #64).

The decoder's refinement is about `absText t`, and `absText` is a
UTF-8 *decode*: to turn a byte suffix into a character suffix at all, the text
has to be ASCII.  It is — every byte the decoder looks at it either compares to
a fixed value (`32`, `10`, `92`, `59`, a record letter) or bounds into
`33 … 126` — but that is a fact about the *program*, not about the format, so
it has to be proved.

Proving it over the Aeneas model would be a second walk over fifty functions.
Proving it over `PinsDec` is one `Consumes` predicate and one lemma per reader,
which is what this file is: `Consumes bs r` says that every byte of `bs` is
either still to be read (it is a byte of `r`) or ASCII, every reader preserves
it, and the pass consumes the *whole* text (`runFooter` insists the remainder
is empty), so `decode_ascii` gets ASCII for all of `bs`.
-/
import ConRon.Refine.PinsDec

namespace ConRon.Refine.PinsDec

open ConLeche

/-! ## The predicate

The "what has been read so far was ASCII" invariant, stated as a `∀` and not
as the `∃ pre, bs = pre ++ r ∧ …` one might write first: `refl`, `trans` and
`cons` are then one-line terms, and each is all a reader's lemma needs. -/

/-! ## The two tactics

Every reader is a chain of `match … with | none => none | some … => …` over
the previous one, so every proof below is the same two steps: `crush` splits
the chain and throws away the arms that fail, leaving one equation per step in
the context, and `consumes` (below, once the steps' lemmas exist) folds those
equations with `Consumes.trans`.  `byte_lt` is for the one byte a record
dispatch compares to a literal rather than passing to a reader. -/

/-- Split every `match`/`if` of a decoder equation `h : f … = some …`,
discharging the arms that return `none`, and read off the result equation. -/
macro "crush" h:ident : tactic => `(tactic|
  ((repeat' (first
      | contradiction
      | split at $h:ident
      | dsimp only at $h:ident)) <;>
    (try (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident
          first
            | (obtain ⟨-, hr⟩ := $h:ident; subst hr)
            | subst $h:ident))))

/-- The record and sub-kind letters: a byte the dispatch compared to a literal
is ASCII. -/
macro "byte_lt" : tactic => `(tactic|
  first
    | omega
    | (simp only [Bool.or_eq_true, decide_eq_true_eq] at *; omega))

/-! ## Bytes and scalars -/

/-! ## Strings -/

/-! ## Backward references -/

/-! ## The counted lists -/

/-! ## Composing the readers

Every record below is a straight chain of the readers above, so its proof is
`crush` followed by a `Consumes.trans` fold over the equations `crush` left in
the context.  The fold is greedy and deterministic — at each point exactly one
hypothesis reads the byte string the goal is still at — which is why this is a
`repeat` over `refine`s rather than a `solve_by_elim`: the search version has
to guess `Consumes.trans`' middle and does not terminate in practice. -/

/-- Fold the chain of reader equations in the context into the goal's
`Consumes`. -/
macro "consumes" : tactic => `(tactic|
  repeat (first
    | exact Consumes.refl _
    | refine Consumes.trans (afterSpace_consumes (by assumption)) ?_
    | refine Consumes.trans (afterNewline_consumes (by assumption)) ?_
    | refine Consumes.trans (readNat_consumes (by assumption)) ?_
    | refine Consumes.trans (readIndex_consumes (by assumption)) ?_
    | refine Consumes.trans (readBigNat_consumes (by assumption)) ?_
    | refine Consumes.trans (expectId_consumes (by assumption)) ?_
    | refine Consumes.trans (readString_consumes (by assumption)) ?_
    | refine Consumes.trans (nameRef_consumes (by assumption)) ?_
    | refine Consumes.trans (levelRef_consumes (by assumption)) ?_
    | refine Consumes.trans (pwRef_consumes (by assumption)) ?_
    | refine Consumes.trans (exprRef_consumes (by assumption)) ?_
    | refine Consumes.trans (nameList_consumes (by assumption)) ?_
    | refine Consumes.trans (levelList_consumes (by assumption)) ?_
    | refine Consumes.trans (exprList_consumes (by assumption)) ?_
    | refine Consumes.trans (pinsEight_consumes (by assumption)) ?_
    | refine Consumes.trans (proofsEight_consumes (by assumption)) ?_))

end ConRon.Refine.PinsDec
