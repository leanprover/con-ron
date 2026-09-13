/-
# The `whnf` body (task #55, `CORE_PLAN.md` step 6)

`crates/con-ron-core/src/cached/core_c.rs`'s three `whnf` helpers —
`whnf_step_i` (`:2535`), `whnf_loop_i` (`:2562`) and `whnf_body_i` (`:2588`) —
against `ConLeche/Cached/CoreC.lean`'s `whnfStepI` (`:1094`), `whnfLoopI`
(`:1105`) and `whnfBodyI` (`:1111`).

This is the smallest of the six bodies and the *shape* of every fuelled loop
in the block: the con-leche twin recurses structurally on a `Nat` budget
(`whnfLoopI 0` throws, `whnfLoopI (n+1)` runs one step with `whnfLoopI n` as
the continuation) where the Rust threads a `U64` and tests it against `0`.
So the loop lemma is an induction on the budget's `val`, with the *step*
lemma taking the continuation's refinement as a hypothesis
(`whnf_step_of_loop` below): the step is where the continuation appears as
con-leche's `k`, and the induction is what supplies it.

Two callees live in `Arms/Lits.lean` and travel as `WhnfDeps`:
`reduce_nat_i` (`reduceNatI`, `CoreC.lean:93`) and `unfold_definition_i`
(`unfoldDefinitionI`, `CoreC.lean:69`), both `Option`-valued.  The
`.M`-suffixed code-point tables are the `.Err` message of the exhausted
budget; nothing is claimed about them (DESIGN.md §3.5).
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKVec
import ConRon.Refine.Nat

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## The two foreign callees

`Arms/Lits.lean` owns them; here they are hypotheses, each field the exact
statement that file's `<fn>_refines` has.  Both are `Option`-valued, so the
abstraction is `Option.map absExpr` and the well-formedness "whatever is
returned is well formed". -/

/-- The `Arms/Lits.lean` helpers `whnf_step_i` calls. -/
structure WhnfDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `CoreC.lean:93` — `reduce_nat_i` refines `reduceNatI` (`core_c.rs:226`). -/
  reduceNat : ∀ (d : Std.U64) {e : expr.Expr}, ExprWF e →
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.reduce_nat_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.reduceNatI (knot mode lfe fuel.val) lfe d.val (absExpr e))
  /-- `CoreC.lean:69` — `unfold_definition_i` refines `unfoldDefinitionI`
  (`core_c.rs:180`).  It reads neither `mode` nor the knot. -/
  unfoldDefinition : ∀ {e : expr.Expr}, ExprWF e →
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.unfold_definition_i st fe e)
      (fun lfe => ConLeche.Cached.unfoldDefinitionI lfe (absExpr e))

/-! ## One `CheckCM` bind, run

`Refine/StateC.lean`'s note applies: `simp` will not push a state argument
through a `match`, so the composition of the arms is done one bind at a time
by this single lemma rather than by a `simp` set. -/

/-- `(x >>= f).run lst` at a known `x.run lst`: the whole of the monad
plumbing the arms below need. -/
theorem run_bind {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {lst lst' : ConLeche.Cached.CState} {a : α}
    (h : x.run lst = .ok (a, lst')) :
    (x >>= f).run lst = (f a).run lst' := by
  simp only [StateT.run, Bind.bind, StateT.bind] at h ⊢
  rw [h]
  rfl

/-- `CoreC.lean:1105-1107` — one unrolling of `whnfLoopI`: the step at the
decremented budget. -/
theorem whnfLoopI_succ (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv) (depth m : Nat)
    (e : ConLeche.Expr) :
    ConLeche.Cached.whnfLoopI r fe depth (m + 1) e
      = ConLeche.Cached.whnfStepI r fe depth (ConLeche.Cached.whnfLoopI r fe depth m) e := by
  rw [ConLeche.Cached.whnfLoopI]

/-! ## The three helpers -/

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:1094` — **`whnf_step_i` refines `whnfStepI`
at a given continuation** (`core_c.rs:2535`).  `whnfStepI`'s `k` is the loop
at the decremented budget; the Rust passes that budget along instead, so the
correspondence is parametric in `k` and its refinement `hk`, which the
induction of `whnf_loop_i_refines` supplies. -/
private theorem whnf_step_of_loop (hw : Wrappers mode fuel) (hd : WhnfDeps mode fuel)
    (d n : Std.U64)
    (k : ConLeche.FEnv → ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr)
    (hk : ∀ e' : expr.Expr, ExprWF e' →
      Sim absExpr ExprWF (fun st fe => cached.core_c.whnf_loop_i mode fuel st fe d n e')
        (fun lfe => k lfe (absExpr e')))
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_step_i mode fuel st fe d n e)
      (fun lfe => ConLeche.Cached.whnfStepI (knot mode lfe fuel.val) lfe d.val
        (k lfe) (absExpr e)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.whnf_step_i at hok
  obtain ⟨⟨rc, st1⟩, hc, hok⟩ := bind_eq_ok_iff.mp hok
  cases rc with
  | Err err => simp at hok
  | Ok e1 =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hwe1⟩ :=
      (hw.whnfCoreSim d he).apply hwf hfe hc hrel hfrel
    simp only [ConLeche.Cached.whnfStepI, run_bind hrun1]
    obtain ⟨⟨rn, st2⟩, hn2, hok⟩ := bind_eq_ok_iff.mp hok
    cases rn with
    | Err err => simp at hok
    | Ok o =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwo⟩ :=
        (hd.reduceNat d hwe1).apply hwf1 hfe hn2 hrel1 hfrel
      cases o with
      | some e2 =>
        simp only [Option.map_some] at hrun2
        obtain ⟨lst3, hrun3, hrel3, hwf3, hwr⟩ :=
          (hk e2 (hwo e2 rfl)).apply hwf2 hfe hok hrel2 hfrel
        refine ⟨lst3, ?_, hrel3, hwf3, hwr⟩
        rw [run_bind hrun2]
        exact hrun3
      | none =>
        simp only [Option.map_none] at hrun2
        rw [run_bind hrun2]
        obtain ⟨⟨ru, st3⟩, hu, hok⟩ := bind_eq_ok_iff.mp hok
        cases ru with
        | Err err => simp at hok
        | Ok o1 =>
          obtain ⟨lst3, hrun3, hrel3, hwf3, hwo1⟩ :=
            (hd.unfoldDefinition hwe1).apply hwf2 hfe hu hrel2 hfrel
          cases o1 with
          | some e2 =>
            simp only [Option.map_some] at hrun3
            obtain ⟨lst4, hrun4, hrel4, hwf4, hwr⟩ :=
              (hk e2 (hwo1 e2 rfl)).apply hwf3 hfe hok hrel3 hfrel
            refine ⟨lst4, ?_, hrel4, hwf4, hwr⟩
            rw [run_bind hrun3]
            exact hrun4
          | none =>
            simp only [Option.map_none] at hrun3
            obtain ⟨rfl, rfl⟩ : e1 = res ∧ st3 = st' := by
              simpa using Result.ok_injective hok
            refine ⟨lst3, ?_, hrel3, hwf3, hwe1⟩
            rw [run_bind hrun3]
            rfl

/-- The induction that makes the budget a `Nat`: `whnf_loop_i` at a `U64`
whose `val` is `m` refines `whnfLoopI … m`. -/
private theorem whnf_loop_aux (hw : Wrappers mode fuel) (hd : WhnfDeps mode fuel)
    (d : Std.U64) :
    ∀ (m : Nat) (n : Std.U64), n.val = m → ∀ e : expr.Expr, ExprWF e →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.whnf_loop_i mode fuel st fe d n e)
        (fun lfe => ConLeche.Cached.whnfLoopI (knot mode lfe fuel.val) lfe d.val m
          (absExpr e)) := by
  intro m
  induction m with
  | zero =>
    -- the budget is spent: the Rust answers `.Err`, so there is nothing to show
    intro n hn e he fe lfe hfe hfrel st res st' hwf hok lst hrel
    have hz : n = 0#u64 := Std.UScalar.eq_of_val_eq (by simp [hn])
    unfold cached.core_c.whnf_loop_i at hok
    simp [hz, bind_eq_ok_iff] at hok
  | succ m ih =>
    intro n hn e he fe lfe hfe hfrel st res st' hwf hok lst hrel
    have hz : ¬ (n = 0#u64) := by
      intro hc
      rw [hc] at hn
      simp at hn
    dsimp only at hok
    unfold cached.core_c.whnf_loop_i at hok
    rw [if_neg hz] at hok
    obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
    have hiv : i.val = m := by
      have h1 := ConRon.Refine.Nat.usub_val hi
      have h2 : ((1#u64 : Std.U64)).val = 1 := rfl
      omega
    have hstep := whnf_step_of_loop hw hd d i
      (fun lfe => ConLeche.Cached.whnfLoopI (knot mode lfe fuel.val) lfe d.val m)
      (fun e' he' => by simpa [hiv] using ih i hiv e' he') he
    dsimp only
    rw [whnfLoopI_succ]
    exact hstep.apply hwf hfe hok hrel hfrel

/-- `ConLeche/Cached/CoreC.lean:1105` — **`whnf_loop_i` refines `whnfLoopI`**
(`core_c.rs:2562`): the `U64` budget is con-leche's `Nat` one. -/
theorem whnf_loop_i_refines (hw : Wrappers mode fuel) (hd : WhnfDeps mode fuel)
    (d n : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_loop_i mode fuel st fe d n e)
      (fun lfe => ConLeche.Cached.whnfLoopI (knot mode lfe fuel.val) lfe d.val n.val
        (absExpr e)) :=
  whnf_loop_aux hw hd d n.val n rfl e he

/-- `ConLeche/Cached/CoreC.lean:1094` — **`whnf_step_i` refines `whnfStepI`**
(`core_c.rs:2535`), the continuation being the loop at the budget it carries. -/
theorem whnf_step_i_refines (hw : Wrappers mode fuel) (hd : WhnfDeps mode fuel)
    (d n : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_step_i mode fuel st fe d n e)
      (fun lfe => ConLeche.Cached.whnfStepI (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.whnfLoopI (knot mode lfe fuel.val) lfe d.val n.val)
        (absExpr e)) :=
  whnf_step_of_loop hw hd d n _ (fun _ he' => whnf_loop_i_refines hw hd d n he') he

/-- `ConLeche/Cached/CoreC.lean:1111` — **`whnf_body_i` refines `whnfBodyI`**
(`core_c.rs:2588`): the loop at the closed budget, which task #49's
`CoreK.whnf_loop_fuel_refines` says is con-leche's `whnfLoopFuel`. -/
theorem whnf_body_i_refines (hw : Wrappers mode fuel) (hd : WhnfDeps mode fuel)
    (d : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfBodyI (knot mode lfe fuel.val) lfe d.val
        (absExpr e)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.whnf_body_i at hok
  obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
  have hiv : i.val = ConLeche.whnfLoopFuel := CoreK.whnf_loop_fuel_refines hi
  have := (whnf_loop_i_refines hw hd d i he).apply hwf hfe hok hrel hfrel
  rw [hiv] at this
  simpa [ConLeche.Cached.whnfBodyI] using this

end

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Lean's own three and nothing else: no `sorry`, nothing from Aeneas's library.
-/

/-- info: 'ConRon.Refine.Core.whnf_body_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_body_i_refines

/-- info: 'ConRon.Refine.Core.whnf_step_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_step_i_refines

end ConRon.Refine.Core
