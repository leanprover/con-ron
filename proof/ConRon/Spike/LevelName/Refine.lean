/-! # Lemma-shape spike: `Name`/`Level` refinement statements (task #5)

Statements only (Fable).  Conventions fixed here become DESIGN.md §3.5:

* **Exact-result refinement on success.**  A Rust function that returns
  `ok y` computes exactly what the Lean function computes on the abstracted
  inputs: `rust_f x = ok y → lean_f (abs x) = abs y`.  Nothing is claimed
  when Rust fails (`fail`/`div`).  "Accept-direction" at the top level is a
  corollary of exactness at every level, not a weaker per-function claim.
* **Well-formedness of stored derived data.**  `NameWF`/`LevelWF` say the
  stored hash word is the one the (model's own, computable) hash function
  gives for the node.  Every constructor preserves it; `beq` is exact under
  it.  `abs` ignores the word.
* **`ptr_eq` is `false` in the model** (`FunsExternal.lean`); the reflexivity
  lemmas `*_beq_refl` are what make the real program's fast path agree.
-/
import ConRon.Spike.LevelName.Funs
import ConRon.Spike.LevelName.Abs
import ConLeche.Kernel.Level

open Aeneas Aeneas.Std Result
open level_name

namespace ConRon.Spike.LevelName

/-! ## Well-formedness of the stored hash words

`nameHashOf`/`levelHashOf` recompute the hash the smart constructors store,
using the model's `name.mix_hash` (which is fully defined in `Funs.lean`,
unlike Lean's opaque `mixHash`).  State them as the fixpoint of the
constructors' formulas; the exact shape follows `src/name.rs`/`src/level.rs`. -/

def NameWF : name.Name → Prop := sorry     -- hereditary: node hash = formula(children), valid code points, children WF
def LevelWF : level.Level → Prop := sorry   -- likewise, with `NameWF` at `.Param`

theorem level_zero_wf : level.zero = ok u → LevelWF u := sorry
theorem level_succ_wf (h : LevelWF u) : level.succ u = ok v → LevelWF v := sorry
theorem level_max_wf (hu : LevelWF u) (hv : LevelWF v) : level.max u v = ok w → LevelWF w := sorry
theorem level_imax_wf (hu : LevelWF u) (hv : LevelWF v) : level.imax u v = ok w → LevelWF w := sorry
theorem level_param_wf (hn : NameWF n) : level.param n = ok u → LevelWF u := sorry

/-! ## Abstraction is injective (needed for exactness of `beq`) -/

/-- Injective *under WF*: `absString` sends an invalid code point to `'\0'`,
so `NameWF` must include "every stored code point is a valid `Char`"
(`Nat.isValidChar`), which the parser establishes; and the hash word is a
function of the children under WF. -/
theorem absName_injective (ha : NameWF a) (hb : NameWF b) :
    absName a = absName b → a = b := sorry
theorem absLevel_injective (ha : LevelWF a) (hb : LevelWF b) :
    absLevel a = absLevel b → a = b := sorry

/-! ## Constructors abstract to constructors -/

theorem level_zero_abs : level.zero = ok u → absLevel u = .zero := sorry
theorem level_succ_abs : level.succ u = ok v → absLevel v = .succ (absLevel u) := sorry
theorem level_max_abs : level.max u v = ok w → absLevel w = .max (absLevel u) (absLevel v) := sorry
theorem level_imax_abs : level.imax u v = ok w → absLevel w = .imax (absLevel u) (absLevel v) := sorry
theorem level_param_abs : level.param n = ok u → absLevel u = .param (absName n) := sorry

/-! ## Structural equality is exact under WF, and reflexive -/

theorem name_beq_refl (h : NameWF a) : name.beq a a = ok true := sorry
theorem name_beq_exact (ha : NameWF a) (hb : NameWF b) :
    name.beq a b = ok c → c = decide (absName a = absName b) := sorry

theorem level_beq_refl (h : LevelWF a) : level.beq a a = ok true := sorry
theorem level_beq_exact (ha : LevelWF a) (hb : LevelWF b) :
    level.beq a b = ok c → c = decide (absLevel a = absLevel b) := sorry

/-! ## The Level operations, exact on success -/

theorem level_has_param_refines :
    level.level_has_param u = ok b → b = ConLeche.levelHasParam (absLevel u) := sorry

theorem subst_refines (hu : LevelWF u) (hvs : ∀ v ∈ vs.toList, LevelWF v) :
    level.subst ks vs u = ok u' →
      absLevel u' = ConLeche.Level.subst (ks.toList.map absName) (vs.toList.map absLevel) (absLevel u)
      ∧ LevelWF u' := sorry

theorem is_never_zero_refines :
    level.is_never_zero u = ok b → b = ConLeche.Level.isNeverZero (absLevel u) := sorry

theorem simplify_refines (hu : LevelWF u) :
    level.simplify u = ok u' →
      absLevel u' = ConLeche.Level.simplify (absLevel u) ∧ LevelWF u' := sorry

/-- The mutual block: one statement per function, proved together by
induction on `fuel` (the Rust `fuel : U64` abstracts to `fuel.val`; the
Rust `diff : I64` to `diff.val : Int`).  `imaxRules` is a four-function
cascade on the Rust side (task #3); its four lemmas compose to the one
Lean function. -/
theorem leq_core_refines (hl : LevelWF l) (hr : LevelWF r) :
    level.leq_core fuel l r diff = ok o →
      ConLeche.Level.leqCore fuel.val (absLevel l) (absLevel r) diff.val = o := sorry

theorem rest_refines (hl : LevelWF l) (hr : LevelWF r) :
    level.rest fuel l r diff = ok o →
      ConLeche.Level.rest fuel.val (absLevel l) (absLevel r) diff.val = o := sorry

theorem by_cases_refines (hl : LevelWF l) (hr : LevelWF r) (hp : NameWF p) :
    level.by_cases fuel p l r diff = ok o →
      ConLeche.Level.byCases fuel.val (absName p) (absLevel l) (absLevel r) diff.val = o := sorry

theorem leq_refines (hl : LevelWF l) (hr : LevelWF r) :
    level.leq l r = ok o → ConLeche.Level.leq (absLevel l) (absLevel r) = o := sorry

theorem is_equiv_refines (hl : LevelWF l) (hr : LevelWF r) :
    level.is_equiv l r = ok o → ConLeche.Level.isEquiv (absLevel l) (absLevel r) = o := sorry

end ConRon.Spike.LevelName
