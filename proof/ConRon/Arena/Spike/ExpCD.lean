/-
# Experiments C and D — the two-layer route and the one-layer alternative

DESIGN §8.6's experiments C and D ask for Theorem 2 on the same function —
the Aeneas model of `crates/arena-spike` refining the Lean twin (C1), the
twin refining con-leche's pure `instantiate1` (C2), and the Aeneas model
refining the pure `instantiate1` *directly* (D), with no twin in between.

Round 1 left all three `sorry` and argued the recommendation from structure.
Round 2 closes them, and this module is where the three statements meet:

* **C1** — `Spike/ExpC1.lean`, on `Spike/MiniAbs.lean`'s abstraction layer.
  Representation only: no `Expr` occurs.
* **C2** — `Spike/ExpC2.lean`, on `Spike/MiniSpecs.lean`'s `@[spec]` layer.
  Denotation only: no `Vec` and no `u32` occur.  This is experiment A's
  recipe (`mvcgen` + the seven-rule template) at three constructors.
* **D** — `Spike/ExpD.lean`, on `Spike/GenDenote.lean`'s *Rust-side*
  denotation.  It mentions neither `MState` nor `absState`: one induction
  that carries the representation change and the denotation at once.

What established the spike's other claims stays here for the record:

1. **The Rust translates, first try, with no external holes.**
   `crates/arena-spike/src/lib.rs` (394 lines, 4 tests green) through
   `scripts/extract-spike.sh` gives `Spike/Generated/{Types,Funs}.lean`,
   51 + 433 lines, in 0.5 s of Charon and 0.5 s of Aeneas.  There is **no**
   `TypesExternal_Template.lean` and **no** `FunsExternal_Template.lean`.
2. **The `WP Result` instance the brief asks for already exists upstream**
   (`_tmp/aeneas-lean/Aeneas/Std/WP.lean:878`), with `Result.instWPMonad`,
   `Result.of_wp` and `spec_to_mvcgen`.  Round 2's finding is that C1 and D
   do not *need* it: the Aeneas model threads its state by hand, so the two
   programs are matched equationally rather than through a Hoare logic — see
   `ExpC1.lean`'s module doc.
3. **The recursion is `partial_fixpoint` and it unfolds.**
   `Generated.instantiate1.eq_def` is an unconditional equation.
-/
import ConRon.Arena.Spike.ExpC1
import ConRon.Arena.Spike.ExpC2
import ConRon.Arena.Spike.ExpD

namespace ConRon.Arena.Spike

open ConLeche

/-! ## The handle arithmetic

The two lemmas that say the Rust's handle decoding *is* the twin's, on the
nose.  They are `rfl`, which is DESIGN §8.3's "arithmetic, not shifts"
decision paying off. -/

theorem absU_lt (x : Aeneas.Std.U32) : absU x < 4294967296 := x.hBounds

/-- con-leche: none — `tag_of` is the packed-word division. -/
theorem abs_tag_of (h : Aeneas.Std.U32) :
    Generated.tag_of h = h / Generated.IDX_CAP := rfl

/-- con-leche: none — `idx_of` is the packed-word remainder. -/
theorem abs_idx_of (h : Aeneas.Std.U32) :
    Generated.idx_of h = h % Generated.IDX_CAP := rfl

/-! ## The comparison

`C1` composed with `C2` has exactly `D`'s conclusion: the two-layer route
does not weaken the theorem, and the round-2 report's table compares their
costs side by side. -/

/-- The composition, which is what makes the comparison a comparison: given
C1 and C2, D is one term. -/
theorem absState_MWF {st : Generated.State} (hwf : GWF st) : MWF (absState st) :=
  ⟨by simpa [absState] using hwf.bvars, by simpa [absState] using hwf.apps,
   by simpa [absState] using hwf.lams⟩

theorem instantiate1_D_of_C1_C2 (st st' : Generated.State)
    (v fuel h d r : Aeneas.Std.U32) (ve e : Expr) (hwf : GWF st)
    (hmemo : Inst1MemoM ve (absState st))
    (hv : DenotesM (absState st) (absU v) ve)
    (he : DenotesM (absState st) (absU h) e)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) :
    DenotesM (absState st') (absU r) (e.instantiate1 ve (absU d)) :=
  (instantiate1_C2 (absState st) (absState st') (absU v) (absU fuel) (absU h)
    (absU d) (absU r) ve e (absState_MWF hwf) hmemo hv he
    (instantiate1_C1 st st' v fuel h d r hwf hrun)).2.2

end ConRon.Arena.Spike
