/-
`ConRon.Refine.PinsDec` against `ConRon.Dump.parsePins` — half (B) of task
#64's decoder refinement, the tokenizer bridge.

`PinsDec` walks a byte suffix; `parsePins` splits the text into lines, each
line into space-separated tokens, and reads the tokens out of an array with a
cursor.  The bridge is the pair of invariants

* **lines**: the bytes left at a record boundary are the characters of the
  lines `runLines` has left, joined by `'\n'`;
* **fields**: inside a record, the bytes left are the characters of the tokens
  `st.toks.drop st.pos` holds, joined by `' '`.

Both are maintained by `Refine/PinsSplit.lean`'s two `splitOn` lemmas, and both
are *equalities*, not inequalities: the decoder is the stricter of the two
readers (single spaces, one newline per record, nothing after the footer), so
whenever it accepts, the reader sees exactly the tokens the decoder read.

`parsePins_of_decode` is this file's product and the whole of (B).
-/
import ConRon.Refine.PinsAscii
import ConRon.Refine.PinsSplit

namespace ConRon.Refine.PinsRead

open ConRon.Dump ConRon.Refine.PinsDec

/-! ## Bytes as characters

Every byte the decoder accepts is ASCII, so `Char.ofNat` is injective on them
and the byte-level side conditions (`32 ∉ f`, `10 ∉ f`) become the character
side conditions `Refine/PinsSplit.lean`'s two lemmas ask for. -/

/-! ### The two token equations, on bytes -/

/-! ## Splitting a byte list at its first separator -/

/-! ## The reader's state, against the decoder's -/

/-! ## One field -/

/-! ## The scalar readers -/

/-! ### What the byte readers consume -/

/-! ## Strings (FORMAT.md §3's escape) -/

/-! ## Backward references -/

/-! ## Counted lists -/

/-! ## The records -/

/-! `reader_simp` is the `StateT RState (Except String)` plumbing, the kind
dispatch's string comparisons and the boolean reductions every record proof
unfolds; its arguments are the record's own field equations. -/

open Lean.Parser.Tactic in
syntax "reader_simp" "[" simpLemma,* "]" : tactic

open Lean.Parser.Tactic in
macro_rules
  | `(tactic| reader_simp [$ts,*]) =>
    `(tactic| simp only [parseRecord, ite_apply, bind, StateT.bind, Except.bind, get,
        getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, modify,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, String.reduceBEq,
        Bool.false_and, Bool.and_false, Bool.and_true, Bool.true_and, if_true,
        if_false, Bool.false_eq_true, reduceIte,
        ConLeche.Expr.mkBvar_eq, ConLeche.Expr.mkFVar_eq,
        ConLeche.Expr.mkSort_eq, ConLeche.Expr.mkConst_eq,
        ConLeche.Expr.mkApp_eq, ConLeche.Expr.mkLam_eq,
        ConLeche.Expr.mkForallE_eq, ConLeche.Expr.mkLetE_eq,
        ConLeche.Expr.mkLit_eq, ConLeche.Expr.mkProj_eq,
        $ts,*])

/-! ## The pass -/

open Lean.Parser.Tactic in
syntax "lines_simp" "[" simpLemma,* "]" : tactic

open Lean.Parser.Tactic in
macro_rules
  | `(tactic| lines_simp [$ts,*]) =>
    `(tactic| simp only [ite_apply, bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
        String.reduceBEq, Bool.false_and, Bool.and_false, Bool.and_true,
        Bool.true_and, if_true, if_false, Bool.false_eq_true, reduceIte, $ts,*])

end ConRon.Refine.PinsRead

