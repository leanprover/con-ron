/-
# Experiments C and D — the Rust side, and what the spike could and could not
# price

DESIGN §8.6's experiments C and D ask for Theorem 2 on the same functions —
the Aeneas model of `crates/arena-spike` refining the Lean twin (C), and
refining con-leche's pure `instantiate1` directly (D).  What this module
contains, and what it does not, is stated plainly here and in
`_tmp/t97/spike-report.md`; the honest summary is that experiment A consumed
the spike's budget and **the C/D proofs were not closed**.  What *was*
established:

1. **The Rust translates, first try, with no external holes.**
   `crates/arena-spike/src/lib.rs` (395 lines, 4 tests green) through
   `scripts/extract-spike.sh` gives `Spike/Generated/{Types,Funs}.lean`,
   51 + 433 lines, in 0.5 s of Charon and 0.5 s of Aeneas.  There is **no**
   `TypesExternal_Template.lean` and **no** `FunsExternal_Template.lean`: the
   arena's Rust, unlike today's `con-ron-core`, has nothing outside Aeneas's
   subset — no `Arc`, no tagged pointer, no `unsafe`.  That is DESIGN §8.5's
   claim, measured: sixteen holes become zero.
2. **The `WP Result` instance the brief asks for already exists upstream.**
   `_tmp/aeneas-lean/Aeneas/Std/WP.lean:878` declares
   `Result.instWP : WP Result (.except (ULift Error) (.except PUnit (.except PUnit .pure)))`
   — three exception layers: `fail`, a dummy for any other effect, and `div` —
   with `Result.instWPMonad`, the soundness step `Result.of_wp`, and
   `spec_to_mvcgen`/`dspec_to_mvcgen`, which lift Aeneas's own `@[progress]`
   specs into `mvcgen`'s `@[spec]` set.  So the P4 spike does not have to
   write it; it has to *use* it.
3. **The recursion is `partial_fixpoint` and it unfolds.**
   `Generated.instantiate1.eq_def` exists and is an unconditional equation,
   so the fuel induction Theorem 2 needs is available (checked).

What is below: the abstraction from the Aeneas state to the Lean twin's
state, the three statements, and the handle-arithmetic lemmas that show what
the `Std.U32`/`alloc.vec.Vec` gap actually costs per primitive.  The three
theorems are `sorry` — deliberately, and the report says so.
-/
import ConRon.Arena.Spike.Mini
import ConRon.Arena.Spike.Generated.Funs

namespace ConRon.Arena.Spike

open ConLeche

/-! ## The abstraction

`Std.U32 → Nat` and `alloc.vec.Vec α → List α`: the whole representation gap
between (C) and (B) in this spike, and the shape the real Theorem 2 will
have (`absStore : Arena → EStore`). -/

/-- con-leche: none — a machine word as a number. -/
def absU (x : Aeneas.Std.U32) : Nat := x.val

/-- con-leche: none — the Aeneas state as the twin's state. -/
def absState (st : Generated.State) : MState :=
  ⟨st.bvars.val.map absU,
   st.apps.val.map (fun n => (absU n.f, absU n.a)),
   st.lams.val.map (fun n => (absU n.ty, absU n.body)),
   st.memo.val.map (fun e => (absU e.key_h, absU e.key_d, absU e.val))⟩

/-! ## The handle arithmetic

The three lemmas that say the Rust's checked `u32` arithmetic computes the
twin's `Nat` arithmetic whenever it succeeds.  They are the *whole* content
of the representation change for a handle, and they are two lines each — the
measurement DESIGN §8.3's "arithmetic, not shifts" decision predicted. -/

theorem absU_lt (x : Aeneas.Std.U32) : absU x < 4294967296 := x.hBounds

/-- con-leche: none — `tag_of` never fails and computes `mTagOf`. -/
theorem abs_tag_of (h : Aeneas.Std.U32) :
    Generated.tag_of h = h / Generated.IDX_CAP := rfl

/-- con-leche: none — `idx_of` never fails and computes `mIdxOf`. -/
theorem abs_idx_of (h : Aeneas.Std.U32) :
    Generated.idx_of h = h % Generated.IDX_CAP := rfl

/-! ## The three statements

`C1` and `D` are about the same Rust function; `C2` is experiment A's recipe
at three constructors.  `C1` composed with `C2` has exactly `D`'s conclusion,
which is the comparison DESIGN §8.6 asks the spike to price. -/

/-- **Experiment C1** — the Aeneas model of the Rust refines the Lean twin.
No `Expr` occurs: this half is *representation only*.

NOT PROVED (the spike's budget went to experiment A).  The shape is a strong
induction on `fuel.val` with `Generated.instantiate1.eq_def` and the twin's
equation lemma, and one abstraction lemma per primitive
(`view_*`, `find_*_from`, `intern_*`, `memo_*`) — eight of them, each an
induction over the corresponding `alloc.vec.Vec`. -/
theorem instantiate1_C1 (st st' : Generated.State) (v fuel h d r : Aeneas.Std.U32)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) :
    (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
      = .ok (absU r, absState st') := by
  sorry

/-- **Experiment C2** — the Lean twin refines con-leche's `instantiate1`.
No `Vec` and no `u32` occur: this half is *denotation only*, and it is
experiment A's theorem with ten constructors cut to three.

NOT PROVED: it is `instantiate1A_spec` (`ExpA.lean`) at the mini store, and
would need the mini store's own copy of `Specs.lean`'s layer. -/
theorem instantiate1_C2 (s s' : MState) (v fuel h d r : Nat) (ve e : Expr)
    (hv : denoteM s v = some ve) (he : denoteM s h = some e)
    (hrun : (mInstantiate1 v fuel h d).run s = .ok (r, s')) :
    denoteM s' r = some (e.instantiate1 ve d) := by
  sorry

/-- **Experiment D** — the one-layer alternative: the Aeneas model of the Rust
against con-leche's pure `instantiate1`, with no twin in between.  The
denotation is `denoteM ∘ absState`; the induction has to carry the
representation change *and* the denotation at once.

NOT PROVED.  Note that its statement is literally `C1` composed with `C2`:
the two-layer route does not weaken the conclusion. -/
theorem instantiate1_D (st st' : Generated.State) (v fuel h d r : Aeneas.Std.U32)
    (ve e : Expr)
    (hv : denoteM (absState st) (absU v) = some ve)
    (he : denoteM (absState st) (absU h) = some e)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) :
    denoteM (absState st') (absU r) = some (e.instantiate1 ve (absU d)) := by
  sorry

/-- The composition, which is what makes the comparison a comparison: given
C1 and C2, D is three lines. -/
theorem instantiate1_D_of_C1_C2 (st st' : Generated.State)
    (v fuel h d r : Aeneas.Std.U32) (ve e : Expr)
    (hv : denoteM (absState st) (absU v) = some ve)
    (he : denoteM (absState st) (absU h) = some e)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) :
    denoteM (absState st') (absU r) = some (e.instantiate1 ve (absU d)) :=
  instantiate1_C2 (absState st) (absState st') (absU v) (absU fuel) (absU h)
    (absU d) (absU r) ve e hv he (instantiate1_C1 st st' v fuel h d r hrun)

end ConRon.Arena.Spike
