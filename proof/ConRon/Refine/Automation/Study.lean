import ConRon.Refine.Level
import ConRon.Refine.ExprOps
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.CoreKSupport
import ConRon.Refine.Core.Arms.Lits
import ConRon.Refine.Automation.SimpSets
/-! # Task #69 — can the refinement proofs be automatic?  (Fable's study)

Three representative lemmas of the tower, re-proved with one idiom:

    ⟨shape⟩ ; rust_inv h ; all_goals grind [⟨the lemma set⟩]

where `rust_inv` is the deterministic Rust-side normaliser defined below and
the lemma set is (a) the induction hypothesis packaged as a *predicate* with a
`use` lemma whose first hypothesis is the Rust success equation, (b) the
con-leche arm-selection equations *without side conditions*, (c) the
abstraction/WF facts of the constructors as forward (`→`) lemmas triggered by
the smart-constructor equation, and (d) the bind inversion `bind_eq_ok_iff`.

Each experiment is stated beside the name and length of the hand proof it
replaces.  Nothing here is imported by the tower; the file is evidence, and
`AUTOMATION.md` next to it is the write-up. -/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine

namespace ConRon.Refine.Automation

/-! ## The Rust-side normaliser

`grind` inverts binds and splits `match`es itself, but when the chain is
deep (a state-passing walk, two wrapper calls in a row) its E-matching
budget runs out on junk instances first.  Peeling the hypothesis
deterministically before `grind` — `simp` (which knows `bind_eq_ok_iff` and
`Prod.exists`), then one `∃`/`∧` layer at a time, then `split` on the
`match`/`if` that guards the rest, `simp` closing the branches it refutes
(`ok (.Err e, s) = ok (.Ok r, s')`) — leaves one goal per reachable success
path, each with plain equations in context. -/
syntax "rust_inv " ident : tactic
macro_rules
  | `(tactic| rust_inv $h) => `(tactic| repeat' (first
      | (split at $h:ident)
      | (simp at $h:ident)
      | (obtain ⟨_, $h⟩ := $h)))

/-! ## Experiment 1: `Level.rest_refines_aux` (hand proof: 268 lines, 25 cases)

State-free, but with an induction hypothesis (`LeqCoreSpec fuel`) that has to
be applied at the children.  Two things were needed beyond the obvious lemma
list:

* the IH as a **named lemma with the Rust equation among its hypotheses**
  (`LeqCoreSpec.use`).  `grind` also E-matches local `∀`s, but infers their
  patterns from the *conclusion*, `leqCore ↑fuel (absLevel l) (absLevel r)
  ↑d`, which never appears in a goal once `absLevel ⟨_, .Succ t⟩` has been
  reduced to `.succ (absLevel t)`; with `→` the trigger is
  `level.leq_core fuel l r d = ok o`, which the inverted bind provides;
* arm-selection equations **without side conditions**.  `Level.rest_max`
  carries `(h : ∀ s, r ≠ .succ s)`; given to `grind` it makes the `Max/_`
  cases diverge (`whnf` timeout at any heartbeat budget: the `∀` side
  condition becomes an E-matching theorem of its own).  The twelve
  specialisations below, one per constructor pair, are `rfl`-level and
  harmless. -/
section Level
open ConRon.Refine.Level

theorem LeqCoreSpec.use {fuel : Std.U64} (hQ : LeqCoreSpec fuel) {l r : level.Level}
    (hl : LevelWF l) (hr : LevelWF r) {d : Std.I64} {o : Option Bool}
    (h : level.leq_core fuel l r d = ok o) :
    ConLeche.Level.leqCore fuel.val (absLevel l) (absLevel r) d.val = o := hQ l r hl hr d o h

theorem rest_max_zero {fuel a b diff} : ConLeche.Level.rest fuel (.max a b) .zero diff
    = (do if ← ConLeche.Level.leqCore fuel a .zero diff then ConLeche.Level.leqCore fuel b .zero diff else pure false) :=
  rest_max (by simp)
theorem rest_max_max {fuel a b x y diff} : ConLeche.Level.rest fuel (.max a b) (.max x y) diff
    = (do if ← ConLeche.Level.leqCore fuel a (.max x y) diff then ConLeche.Level.leqCore fuel b (.max x y) diff else pure false) :=
  rest_max (by simp)
theorem rest_max_imax {fuel a b x y diff} : ConLeche.Level.rest fuel (.max a b) (.imax x y) diff
    = (do if ← ConLeche.Level.leqCore fuel a (.imax x y) diff then ConLeche.Level.leqCore fuel b (.imax x y) diff else pure false) :=
  rest_max (by simp)
theorem rest_max_param {fuel a b p diff} : ConLeche.Level.rest fuel (.max a b) (.param p) diff
    = (do if ← ConLeche.Level.leqCore fuel a (.param p) diff then ConLeche.Level.leqCore fuel b (.param p) diff else pure false) :=
  rest_max (by simp)
theorem rest_imax_zero {fuel a b diff} : ConLeche.Level.rest fuel (.imax a b) .zero diff
    = ConLeche.Level.imaxRules fuel (.imax a b) .zero diff := rest_imax_r (by simp) (by simp)
theorem rest_imax_max {fuel a b x y diff} : ConLeche.Level.rest fuel (.imax a b) (.max x y) diff
    = ConLeche.Level.imaxRules fuel (.imax a b) (.max x y) diff := rest_imax_r (by simp) (by simp)
theorem rest_imax_param {fuel a b p diff} : ConLeche.Level.rest fuel (.imax a b) (.param p) diff
    = ConLeche.Level.imaxRules fuel (.imax a b) (.param p) diff := rest_imax_r (by simp) (by simp)
theorem rest_zero_succ {fuel s diff} : ConLeche.Level.rest fuel .zero (.succ s) diff
    = ConLeche.Level.leqCore fuel .zero s (diff + 1) := rest_r_succ (by simp)
theorem rest_max_succ {fuel a b s diff} : ConLeche.Level.rest fuel (.max a b) (.succ s) diff
    = ConLeche.Level.leqCore fuel (.max a b) s (diff + 1) := rest_r_succ (by simp)
theorem rest_imax_succ {fuel a b s diff} : ConLeche.Level.rest fuel (.imax a b) (.succ s) diff
    = ConLeche.Level.leqCore fuel (.imax a b) s (diff + 1) := rest_r_succ (by simp)
theorem rest_param_succ {fuel p s diff} : ConLeche.Level.rest fuel (.param p) (.succ s) diff
    = ConLeche.Level.leqCore fuel (.param p) s (diff + 1) := rest_r_succ (by simp)

/-- The hand proof is `Level.rest_refines_aux` (`Refine/Level.lean`, 268
lines); this one is ten. -/
theorem rest_refines_auto {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool} :
    level.rest fuel l r diff = ok o →
      ConLeche.Level.rest fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  rw [level.rest.eq_def] at h
  obtain ⟨⟨hhl, kl⟩⟩ := l
  obtain ⟨⟨hhr, kr⟩⟩ := r
  cases kl <;> cases kr <;> simp at h <;>
    grind [rest_succ, rest_zero_succ, rest_max_succ, rest_imax_succ, rest_param_succ,
      rest_max_zero, rest_max_max, rest_max_imax, rest_max_param,
      rest_zero_max, rest_param_max, rest_param_param,
      rest_param_zero, rest_zero_param, rest_imax_imax, rest_zero_zero, rest_zero_imax,
      rest_imax_zero, rest_imax_max, rest_imax_param, rest_param_imax,
      absLevel_mk, absLevelKind, → i64_add_val, → i64_sub_val,
      → LevelWF.succ_inv, → LevelWF.max_inv, → LevelWF.imax_inv, → LevelWF.param_inv,
      → imax_rules_refines, → level_beq_exact', → name_beq_exact, → LeqCoreSpec.use]

end Level

/-! ## Experiment 2: `ExprOps.instantiate1_go_refines` (hand proof: 340 lines, 10 cases)

A memoised walk: state (the memo table) threaded through every call, a probe
and a write-back per rebuilding constructor, the induction on `ExprWF`.

What the automatic proof needs, and why:

* **the IH as a predicate** (`Inst1Spec`) with a `use` lemma whose first
  hypothesis is the recursive call's success equation.  `grind [→ thm]`
  takes its patterns from the propositional hypotheses *in order*, so the
  equation must come first — `Expr.app_wf hf ha : expr.app f a = ok e →
  ExprWF e`, whose first two hypotheses are `ExprWF f`/`ExprWF a`, would be
  instantiated at every pair of well-formed terms (it was: quadratic junk,
  and the real instance never reached).  The primed variants below reorder;
  `grind_pattern` cannot help because an `Eq` is not an admissible pattern;
* **one shape line per constructor** (`obtain ⟨d1, rfl, -, -, -⟩ :=
  Expr.app_inv h1`).  The fully uniform `induction he <;> …` fails: the
  generated body matches on `e._0.kind` and neither `simp` nor `grind`
  reduces it while `e` is a variable, and the inversion lemmas differ per
  constructor.  The line is mechanical (the constructor names it);
* **`rust_inv` before `grind`**.  With `simp at h` alone the pattern-`let`
  Aeneas emits for every pair (`let (f2, memo2) ← …`) stays folded under the
  next bind and `grind` spends its term-generation budget on the junk above
  before unfolding it. -/
section ExprOps
open ConRon.Refine.ExprOps

/-- The induction hypothesis of `instantiate1_go_refines`, as a predicate on
the node. -/
def Inst1Spec (v e : expr.Expr) : Prop :=
  ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr) (d : Std.U64) (r : expr.Expr),
    MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo →
    expr_ops.instantiate1_go v memo e d = ok (r, memo') →
    (ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1 (absExpr e) (absExpr v) d.val) ∧
      MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo'

theorem Inst1Spec.use {v e : expr.Expr} {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    {d : Std.U64} {r : expr.Expr}
    (h : expr_ops.instantiate1_go v memo e d = ok (r, memo')) (hs : Inst1Spec v e)
    (hm : MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo) :
    (ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1 (absExpr e) (absExpr v) d.val) ∧
      MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo' := hs memo memo' d r hm h

theorem Inst1Q_iff (v : ConLeche.Expr) (e : ConLeche.Expr) (d : Nat) (r : expr.Expr) :
    Inst1Q v (e, d) r ↔ (ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1 e v d) := Iff.rfl

theorem app_wf' {f a e : expr.Expr} (h : expr.app f a = ok e) (hf : ExprWF f) (ha : ExprWF a) :
    ExprWF e := Expr.app_wf hf ha h
theorem lam_wf' {ty bo e : expr.Expr} {m : expr.BinderMeta} (h : expr.lam ty bo m = ok e)
    (hty : ExprWF ty) (hbo : ExprWF bo) (hm : BinderMetaWF m) : ExprWF e := Expr.lam_wf hty hbo hm h
theorem forall_e_wf' {ty bo e : expr.Expr} {m : expr.BinderMeta} (h : expr.forall_e ty bo m = ok e)
    (hty : ExprWF ty) (hbo : ExprWF bo) (hm : BinderMetaWF m) : ExprWF e :=
  Expr.forall_e_wf hty hbo hm h
theorem let_e_wf' {ty v bo e : expr.Expr} (h : expr.let_e ty v bo = ok e)
    (hty : ExprWF ty) (hv : ExprWF v) (hbo : ExprWF bo) : ExprWF e := Expr.let_e_wf hty hv hbo h
theorem proj_wf' {s : name.Name} {i : Std.U64} {x e : expr.Expr} (h : expr.proj s i x = ok e)
    (hs : NameWF s) (hx : ExprWF x) : ExprWF e := Expr.proj_wf hs hx h
theorem hit' {K V A : Type} {Eq2Inst : ron.hashmap.Eq2 K} {HashableInst : ron.hashmap.Hashable K}
    {KWF : K → Prop} {absK : K → A} {Q : A → V → Prop}
    {m : ron.hashmap.HashMap K V} {k : K} {r : V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok (some r))
    (hm : MemoInv KWF absK Q m) (hx : KeyExact Eq2Inst KWF absK) (hk : KWF k) :
    Q (absK k) r := MemoInv.hit hx hm hk h
theorem set' {K V A : Type} {Eq2Inst : ron.hashmap.Eq2 K} {HashableInst : ron.hashmap.Hashable K}
    {KWF : K → Prop} {absK : K → A} {Q : A → V → Prop}
    {m m' : ron.hashmap.HashMap K V} {k : K} {v : V} {old : Option V}
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m'))
    (hm : MemoInv KWF absK Q m) (hx : KeyExact Eq2Inst KWF absK) (hk : KWF k)
    (hq : Q (absK k) v) : MemoInv KWF absK Q m' := MemoInv.set hx hm hk hq h

/-- The closing tactic, the same in all ten cases. -/
macro "inst1_close" : tactic => `(tactic| (
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    rust_inv h
    all_goals grind [→ Inst1Spec.use, → expr_nat_key_eq, → Expr.dup_eq, → Expr.binder_meta_dup_eq,
      name_dup_eq,
      → Expr.bvar_refines, → Expr.bvar_wf, → Expr.app_refines, → app_wf',
      → Expr.lam_refines, → lam_wf', → Expr.forall_e_refines, → forall_e_wf',
      → Expr.let_e_refines, → let_e_wf', → Expr.proj_refines, → proj_wf',
      → hit', → set', → memo1_get_hit, KeyWF_mk, absKey_mk, Inst1Q_iff,
      ConLeche.Expr.instantiate1, absExpr_mk, absExprKind, bind_eq_ok_iff,
      → HashMap.uscalar_sub_eq, → HashMap.uscalar_add_eq]))

/-- The hand proof is `ExprOps.instantiate1_go_refines` (`Refine/ExprOps.lean`,
340 lines); this one is one shape line per constructor. -/
theorem instantiate1_go_auto {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr} (he : ExprWF e) :
    Inst1Spec v e := by
  have hx := key_exact
  have he' := he
  induction he with
  | @bvar i e h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; inst1_close
  | @fvar idx ty e hty h1 ih => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; inst1_close
  | @sort u e hu h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; inst1_close
  | @mk_const n us e hn hus h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; inst1_close
  | @app f a e hf ha h1 ihf iha => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; inst1_close
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; inst1_close
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo => obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; inst1_close
  | @let_e ty vv bo e hty hvv hbo h1 ihty ihvv ihbo => obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; inst1_close
  | @lit l e hl h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; inst1_close
  | @proj s i x e hs hxx h1 ih => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; inst1_close

/-- And the original statement follows in one line. -/
theorem instantiate1_go_refines' {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr) (d : Std.U64) (r : expr.Expr),
      MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo →
      expr_ops.instantiate1_go v memo e d = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1 (absExpr e) (absExpr v) d.val) ∧
        MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo' := instantiate1_go_auto hv he

end ExprOps

/-! ## Experiment 3: a knot arm, `Core.reduce_nat_lits_i_refines` (hand proof: 75 + 4 lines)

Two wrapper calls in a row, the state threaded through `StateRel`, the
con-leche side a `StateT CState (Except _)` computation run at a related
state.  Beyond the recipe of experiment 2, two things about the *statement*:

* **`Sim`/`SimS` end in an existential** (`∃ lst', g.run lst = .ok (A r, lst')
  ∧ …`).  `grind` negates the goal into `∀ lst', …`, whose body is not in the
  E-graph, so nothing it derives about `g.run lst` ever meets it.  `RunOk`
  below is the same claim as a predicate *on the run result* — no witness
  to find — and `Sim.ofRun` turns it back into `Sim`;
* the con-leche monad plumbing as **unconditional equations** (`run` of a
  bind is the bind of the runs; `Except.ok a >>= f = f a`): conditional
  rewrites such as `Lits.runBind` (`x.run lst = ok (a, lst') → (x >>= f).run
  lst = (f a).run lst'`) have variables `a`, `lst'` outside their left-hand
  side and never fire;
* the wrapper hypothesis `Wrappers mode fuel` as a `use` lemma
  (`Wrappers.whnf_use`), and the chain is long enough that `grind`'s default
  term-generation limit (`gen := 8`) stops it one rewrite short — `(gen := 24)`. -/
section Arm
open ConRon.Refine.State ConRon.Refine.FEnv ConRon.Refine.Core

/-- `SimS`'s conclusion as a predicate on the run result. -/
def RunOk {ε β σ : Type} (x : Except ε (β × σ)) (P : β → σ → Prop) : Prop :=
  match x with
  | .ok (v, s) => P v s
  | .error _ => False

theorem RunOk_ok {ε β σ : Type} (v : β) (s : σ) (P : β → σ → Prop) :
    RunOk (ε := ε) (.ok (v, s)) P ↔ P v s := Iff.rfl
theorem RunOk_error {ε β σ : Type} (e : ε) (P : β → σ → Prop) :
    RunOk (β := β) (σ := σ) (.error e) P ↔ False := Iff.rfl

/-- **The accept half of `Sim`**, which is what experiment 3 measures.

Task #67 restated `Sim` over the *whole* outcome (`Out`, `Refine/State.lean`),
so a `Sim` now also carries a failure half — con-leche throws at the same kind
whenever the port throws a mirrored error.  Proving that half is the tower's
business (`Refine/Core/Arms/Lits.lean` does it by hand), not this study's: the
measurement here is about the accept direction's *shape*, and it is unchanged.
So the experiment concludes `SimOk`, the accept half on its own, and the
tower's own `RunOk` introduction rules — `ConRon.Refine.Core.Sim.ofRun` and
`SimS.ofRun` in `Core/Arms/Shape.lean`, which take both halves — are where the
shape is carried for real. -/
def SimOk {α β : Type} (A : α → β) (WF : α → Prop)
    (f : cached.state_c.CState → fenv.FEnv →
      Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
    (g : ConLeche.FEnv → ConLeche.Cached.CheckCM β) : Prop :=
  ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe → ∀ st r st', StateWF st →
    f st fe = ok (.Ok r, st') → ∀ lst, StateRel st lst →
      ∃ lst', (g lfe).run lst = .ok (A r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r

theorem SimOk.ofRun {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe → ∀ st r st', StateWF st →
      f st fe = ok (.Ok r, st') → ∀ lst, StateRel st lst →
        RunOk ((g lfe).run lst) (fun v lst' => v = A r ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r)) :
    SimOk A WF f g := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  have := h fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold RunOk at this
  split at this
  · rename_i v s hv
    obtain ⟨rfl, h1, h2, h3⟩ := this
    exact ⟨s, hv, h1, h2, h3⟩
  · exact this.elim

theorem run_bind_eq {α β : Type} (x : ConLeche.Cached.CheckCM α)
    (f : α → ConLeche.Cached.CheckCM β) (lst : ConLeche.Cached.CState) :
    (x >>= f).run lst = (x.run lst >>= fun p => (f p.1).run p.2) := rfl
theorem run_pure_eq {α : Type} (a : α) (lst : ConLeche.Cached.CState) :
    (pure a : ConLeche.Cached.CheckCM α).run lst = .ok (a, lst) := rfl
theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- `Cached/StateC.lean:99-103` — `rawNatLitC?` *is* `rawNatLit?` (a copy of
`Lits.rawNatLitC_eq`, which is `private`). -/
theorem rawNatLitC_eq' (e : ConLeche.Expr) :
    ConLeche.Cached.rawNatLitC? e = ConLeche.rawNatLit? e := by
  cases e with
  | lit l => cases l <;> rfl
  | const c us =>
    cases us with
    | nil => simp only [ConLeche.Cached.rawNatLitC?, ConLeche.rawNatLit?, beq_iff_eq]
    | cons => rfl
  | _ => rfl

/-- The wrapper hypothesis as an E-matching entry point: fires on a successful
`whnf` call. -/
theorem Wrappers.whnf_use {mode : env.CheckMode} {fuel : Std.U64}
    {st : cached.state_c.CState} {fe : fenv.FEnv} {d : Std.U64} {e r : expr.Expr}
    {st' : cached.state_c.CState}
    (hok : cached.core_c.whnf mode fuel st fe d e = ok (.Ok r, st'))
    (hw : Wrappers mode fuel)
    {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    (hrel : StateRel st lst) (hfrel : FEnvRel fe lfe)
    (hwf : StateWF st) (hfe : FEnvWF fe) (he : ExprWF e) :
    ∃ lst', ((knot mode lfe fuel.val).whnf d.val (absExpr e)).run lst = .ok (absExpr r, lst')
      ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r :=
  (hw.whnfSim d he).apply hwf hfe hok hrel hfrel

/-- `raw_nat_lit`, with the pin discharged and the WF clause stated without
`Membership` (which `grind` does not unfold on `Option`). -/
theorem raw_nat_lit_use {e : expr.Expr} {o : Option ron.nat.Nat} (h : core_k.raw_nat_lit e = ok o)
    (he : ExprWF e) :
    ConLeche.rawNatLit? (absExpr e) = o.map Nat.toNat ∧ ∀ m, o = some m → Nat.NatWF m :=
  let r := CoreK.raw_nat_lit_refines he CoreK.pinned_nat_zero_name h
  ⟨r.1.symm, fun m hm => r.2 m (Option.mem_def.mpr hm)⟩

/-- The hand proof of the accept half is `Core.lits_replay` +
`reduce_nat_lits_i_refines` (`Refine/Core/Arms/Lits.lean`, 75 + 4 lines before
task #67 gave them their failure halves); this one is five lines. -/
theorem reduce_nat_lits_i_auto {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    SimOk (Option.map (fun p : ron.nat.Nat × ron.nat.Nat => (Nat.toNat p.1, Nat.toNat p.2)))
      (fun o => ∀ p, o = some p → Nat.NatWF p.1 ∧ Nat.NatWF p.2)
      (fun st fe => cached.core_c.reduce_nat_lits_i mode fuel st fe d a b)
      (fun lfe => natLitsI (knot mode lfe fuel.val) d.val (absExpr a) (absExpr b)) := by
  refine SimOk.ofRun fun fe lfe hfwf hfrel st r st' hwf hok lst hrel => ?_
  unfold cached.core_c.reduce_nat_lits_i at hok
  rust_inv hok
  all_goals simp only [natLitsI]
  all_goals grind (gen := 24) [→ Wrappers.whnf_use, → raw_nat_lit_use, run_bind_eq, except_bind_ok,
    except_bind_error, run_pure_eq, rawNatLitC_eq', bind_eq_ok_iff, RunOk_ok, RunOk_error]

end Arm


/-! ## Task #70: the cost, and the tuned idiom

The idiom above elaborates 4–8× slower than the hand proofs it replaces
(net of imports: 6.9 s, 4.7 s, 0.84 s against 2.0 s, 0.65 s, 0.16 s).  Where
the time goes, by `profiler`/`diagnostics` (the write-up is `AUTOMATION.md`
§"Cost"):

1. **The `grind [thirty lemmas]` list is elaborated at every call**, once per
   goal — 25 goals for `rest`: 3.9 s of its 6.9 s.  `grind`'s own categories
   (E-matching, its simp, the solvers) total 0.4 s.  Fix: the set as
   `attribute [local grind …]` in a section, elaborated once; equations as
   `grind =` (a bare `grind` on an equation prints a "try these" suggestion).
2. **`rust_inv`'s `simp at h` is the default simp set** on the whole unfolded
   body, and the `repeat'` loop retries it after every `obtain` (~60 ms a
   call, mostly Mathlib's `bind` lemmas failing to unify): 1.6 s / 2.5 s of
   the first two.  Fix: two registered simp sets (`SimpSets.lean`), the loop
   ordered `obtain`/`split`/`simp` so nothing is retried on an unchanged
   hypothesis, and the head reduction (the `Arc::deref` bind, the node
   projections) as *pre-order* rewrites, so that the body's `match` on the
   known node reduces before `simp` has visited its dead arms.
3. **`grind`'s E-matching round limit** (`ematch := 5`) is one round short on
   the Option-monad plumbing of `rest` once the normaliser has done the
   splits, and `gen := 8` one term short on a two-wrapper arm.  `(ematch := 12)
   (gen := 24)` passes every lemma here and is the closing macro's fixed
   configuration — no per-lemma tuning.
4. What is left is `grind`'s per-call internalisation of the context (~100 ms
   a goal in the walks; a trivial goal costs 1.5 ms, so it is proportional to
   the context), of which ~40 ms is the arithmetic modules probing `ℤ` and
   `Result` for ring/order instances (`-ring -linarith -order -lia` buys
   10–15 %, not taken).

The maintainer's additions, in short (the numbers are in `AUTOMATION.md`):
the per-constructor shape line *is* avoidable — `ExprWF.ind_node` below is a
node-shaped induction principle, and the walks become one line; `grind
cases`/`grind ext` on the node types cannot help, because the stuck
discriminant is `e._0.kind` with `e` a variable and only the induction opens
it; and `grind =>`/`sym =>` doing the bind inversion itself is 15× slower and
fails on the smallest lemma — the whole body is internalised before the first
split, and every split branch carries it. -/

/-! ### The two simp sets (`SimpSets.lean` registers them) -/
attribute [rust_reduce] arc_deref_eq bind_tc_ok lift_eq ptr_new_eq ptr_clone_eq arc_new_eq
  arc_clone_eq expr_dup_eq name_dup_eq level_dup_eq ExprOps.binder_meta_eq
  name.NameNode.hash._simpLemma_ name.NameNode.kind._simpLemma_ name.Name._0._simpLemma_
  level.LevelNode.hash._simpLemma_ level.LevelNode.kind._simpLemma_ level.Level._0._simpLemma_
  expr.ExprNode.data._simpLemma_ expr.ExprNode.kind._simpLemma_ expr.Expr._0._simpLemma_
attribute [rust_invert] arc_deref_eq bind_tc_ok lift_eq ptr_new_eq ptr_clone_eq arc_new_eq
  arc_clone_eq expr_dup_eq name_dup_eq level_dup_eq ExprOps.binder_meta_eq
  name.NameNode.hash._simpLemma_ name.NameNode.kind._simpLemma_ name.Name._0._simpLemma_
  level.LevelNode.hash._simpLemma_ level.LevelNode.kind._simpLemma_ level.Level._0._simpLemma_
  expr.ExprNode.data._simpLemma_ expr.ExprNode.kind._simpLemma_ expr.Expr._0._simpLemma_
  bind_eq_ok_iff Result.ok.injEq Prod.mk.injEq Prod.exists uncurry_apply_pair
  core.result.Result.Ok.injEq false_and and_false exists_false true_and and_true
  exists_eq_left exists_eq_right Option.some.injEq

/-- The head of every generated body, reduced in one pre-order step: `let en ←
Arc::deref e._0; …` is `… e._0 …`.  (`arc_deref_eq` alone is a post-order
rewrite, so `simp` would visit all the dead arms of the `match` first.) -/
theorem bind_arc_deref {T β : Type} (A : Type) (x : T) (f : T → Result β) :
    (do let y ← alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x; f y) = f x := by
  rw [arc_deref_eq, bind_tc_ok]

open Lean Elab Tactic Meta in
/-- Destructure every local hypothesis whose type is syntactically a pair: the
`let (n, n1) := val` a Rust `Some((n, n1))` pattern produces is a
one-alternative `match` that neither `split` nor `simp` opens while `val` is a
variable.  Fails when there is nothing to do, so that it can sit last in a
`first`.  (Not `‹_ × _›`: elaborating that unifies every hypothesis type with
`?a × ?b` and unfolds the `Wrappers`/`Spec` predicates on the way — a `whnf`
timeout.) -/
elab "rust_pairs" : tactic => do
  let g ← getMainGoal
  let mut fvs : Array FVarId := #[]
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Prod 2 then fvs := fvs.push d.fvarId
  if fvs.isEmpty then throwError "rust_pairs: no pair in the context"
  let mut g := g
  for fv in fvs do
    let subgoals ← g.cases fv
    match subgoals with
    | #[sg] => g := sg.mvarId
    | _ => throwError "rust_pairs: unexpected number of goals"
  replaceMainGoal [g]

/-- The tuned normaliser: `rust_inv` with the cheap sets, the loop ordered so
nothing is retried on an unchanged hypothesis, and the pair fallback. -/
syntax "rust_norm " ident : tactic
macro_rules
  | `(tactic| rust_norm $h) => `(tactic| (
      try simp only [↓bind_arc_deref, ↓expr.Expr._0._simpLemma_, ↓expr.ExprNode.kind._simpLemma_,
        ↓level.Level._0._simpLemma_, ↓level.LevelNode.kind._simpLemma_,
        ↓name.Name._0._simpLemma_, ↓name.NameNode.kind._simpLemma_, rust_reduce] at $h:ident
      repeat' (first
        | (obtain ⟨_, $h⟩ := $h)
        | (split at $h:ident)
        | (simp only [rust_invert, reduceCtorEq, ↓existsAndEq] at $h:ident)
        | rust_pairs)))

/-- The closing call, one fixed configuration for every lemma. -/
macro "rust_grind" : tactic => `(tactic| grind (ematch := 12) (gen := 24))

/-! ### The node-shaped induction (no shape line per constructor)

`induction he` leaves `e` a variable and the constructor's equation
`expr.app f a = ok e` as a hypothesis; the body matches on `e._0.kind`, which
nothing reduces until the inversion lemma has been applied — the per-constructor
line of experiment 2.  Stating the motive on `.mk (.mk d k)` moves that
inversion into the principle, once.  The motive depends on the derivation
(`motive e he`) because `induction e, he using …` needs the targets explicit;
the induction hypotheses come out as `∀ h, motive f h`, which `grind` uses like
any local implication. -/
theorem ExprWF.ind_node {motive : (e : expr.Expr) → ExprWF e → Prop}
    (bvar : ∀ d i (h : ExprWF (.mk (.mk d (.Bvar i)))), motive (.mk (.mk d (.Bvar i))) h)
    (fvar : ∀ d idx ty (h : ExprWF (.mk (.mk d (.Fvar idx ty)))), (∀ h, motive ty h) →
      motive (.mk (.mk d (.Fvar idx ty))) h)
    (sort : ∀ d u (h : ExprWF (.mk (.mk d (.«Sort» u)))), motive (.mk (.mk d (.«Sort» u))) h)
    (mk_const : ∀ d n us (h : ExprWF (.mk (.mk d (.Const n us)))),
      motive (.mk (.mk d (.Const n us))) h)
    (app : ∀ d f a (h : ExprWF (.mk (.mk d (.App f a)))), (∀ h, motive f h) → (∀ h, motive a h) →
      motive (.mk (.mk d (.App f a))) h)
    (lam : ∀ d ty b m (h : ExprWF (.mk (.mk d (.Lam ty b m)))), (∀ h, motive ty h) →
      (∀ h, motive b h) → motive (.mk (.mk d (.Lam ty b m))) h)
    (forall_e : ∀ d ty b m (h : ExprWF (.mk (.mk d (.ForallE ty b m)))), (∀ h, motive ty h) →
      (∀ h, motive b h) → motive (.mk (.mk d (.ForallE ty b m))) h)
    (let_e : ∀ d ty v b (h : ExprWF (.mk (.mk d (.LetE ty v b)))), (∀ h, motive ty h) →
      (∀ h, motive v h) → (∀ h, motive b h) → motive (.mk (.mk d (.LetE ty v b))) h)
    (lit : ∀ d l (h : ExprWF (.mk (.mk d (.Lit l)))), motive (.mk (.mk d (.Lit l))) h)
    (proj : ∀ d s i x (h : ExprWF (.mk (.mk d (.Proj s i x)))), (∀ h, motive x h) →
      motive (.mk (.mk d (.Proj s i x))) h)
    (e : expr.Expr) (he : ExprWF e) : motive e he := by
  induction he with
  | @bvar i e h1 => obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1; exact bvar d i (.bvar h1)
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1; exact fvar d idx ty (.fvar hty h1) (fun _ => ih)
  | @sort u e hu h1 => obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; exact sort d u (.sort hu h1)
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    exact mk_const d n us (.mk_const hn hus h1)
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    exact app d f a (.app hf ha h1) (fun _ => ihf) (fun _ => iha)
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    exact lam d ty bo m (.lam hty hbo hm h1) (fun _ => ihty) (fun _ => ihbo)
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    exact forall_e d ty bo m (.forall_e hty hbo hm h1) (fun _ => ihty) (fun _ => ihbo)
  | @let_e ty vv bo e hty hvv hbo h1 ihty ihvv ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    exact let_e d ty vv bo (.let_e hty hvv hbo h1) (fun _ => ihty) (fun _ => ihvv) (fun _ => ihbo)
  | @lit l e hl h1 => obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1; exact lit d l (.lit hl h1)
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1; exact proj d s i x (.proj hs hx h1) (fun _ => ih)

/-- The children of a well-formed node, one forward lemma per kind: the trigger
is the node itself (`CoreK.ExprWF.children` says the same through the kind). -/
theorem ExprWF.fvar_kids {d idx ty} (h : ExprWF (.mk (.mk d (.Fvar idx ty)))) : ExprWF ty := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.sort_kids {d u} (h : ExprWF (.mk (.mk d (.«Sort» u)))) : LevelWF u := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.const_kids {d n us} (h : ExprWF (.mk (.mk d (.Const n us)))) :
    NameWF n ∧ LevelsWF us := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.app_kids {d f a} (h : ExprWF (.mk (.mk d (.App f a)))) : ExprWF f ∧ ExprWF a := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.lam_kids {d ty b m} (h : ExprWF (.mk (.mk d (.Lam ty b m)))) :
    ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.forall_e_kids {d ty b m} (h : ExprWF (.mk (.mk d (.ForallE ty b m)))) :
    ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.let_e_kids {d ty v b} (h : ExprWF (.mk (.mk d (.LetE ty v b)))) :
    ExprWF ty ∧ ExprWF v ∧ ExprWF b := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.lit_kids {d l} (h : ExprWF (.mk (.mk d (.Lit l)))) : LiteralWF l := by
  have := CoreK.ExprWF.children h; simpa using this
theorem ExprWF.proj_kids {d s i x} (h : ExprWF (.mk (.mk d (.Proj s i x)))) :
    NameWF s ∧ ExprWF x := by
  have := CoreK.ExprWF.children h; simpa using this

/-! ### Experiment 1, tuned: 6.9 s → 2.3 s (hand 2.0 s); no `cases` line either,
`split` opens the `match` on the node kinds.  And a fourth leaf of the same
kind, `Level.by_cases_refines_aux` (75 lines by hand, 0.44 s): four lines, 0.8 s. -/
section Level70
open ConRon.Refine.Level
attribute [local grind =] rest_succ rest_zero_succ rest_max_succ rest_imax_succ rest_param_succ
  rest_max_zero rest_max_max rest_max_imax rest_max_param rest_zero_max rest_param_max
  rest_param_param rest_param_zero rest_zero_param rest_imax_imax rest_zero_zero rest_zero_imax
  rest_imax_zero rest_imax_max rest_imax_param rest_param_imax absLevel_mk absLevelKind
attribute [local grind →] i64_add_val i64_sub_val LevelWF.succ_inv LevelWF.max_inv
  LevelWF.imax_inv LevelWF.param_inv imax_rules_refines level_beq_exact' name_beq_exact
  LeqCoreSpec.use

theorem rest_refines_tuned {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool} :
    level.rest fuel l r diff = ok o →
      ConLeche.Level.rest fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  rw [level.rest.eq_def] at h
  obtain ⟨⟨_, kl⟩⟩ := l
  obtain ⟨⟨_, kr⟩⟩ := r
  rust_norm h
  all_goals rust_grind

/-- `Vec::push` on the empty vector, as a use lemma. -/
theorem push_new_val {α : Type} {x : α} {w : alloc.vec.Vec α}
    (h : alloc.vec.Vec.push (alloc.vec.Vec.new α) x = ok w) : w.val = [x] := by
  obtain ⟨w', h', hv⟩ := vec_singleton x
  cases Result.ok_injective (h.symm.trans h'); exact hv
theorem subst_use {u u' : level.Level} {ks : alloc.vec.Vec name.Name} {vs : alloc.vec.Vec level.Level}
    (h : level.subst ks vs u = ok u') (hu : LevelWF u)
    (hks : ∀ k ∈ ks.val, NameWF k) (hvs : ∀ v ∈ vs.val, LevelWF v) :
    absLevel u' = ConLeche.Level.subst (ks.val.map absName) (vs.val.map absLevel) (absLevel u)
      ∧ LevelWF u' :=
  subst_refines' u hu ks vs hks hvs u' h
theorem simplify_use {u u' : level.Level} (h : level.simplify u = ok u') (hu : LevelWF u) :
    absLevel u' = ConLeche.Level.simplify (absLevel u) ∧ LevelWF u' := simplify_refines' u hu u' h
theorem zero_wf' {u : level.Level} (h : level.zero = ok u) : LevelWF u := LevelWF.zero h
theorem succ_wf' {a u : level.Level} (h : level.succ a = ok u) (ha : LevelWF a) : LevelWF u :=
  LevelWF.succ ha h
theorem param_wf' {n : name.Name} {u : level.Level} (h : level.param n = ok u) (hn : NameWF n) :
    LevelWF u := LevelWF.param hn h
attribute [local grind →] push_new_val subst_use simplify_use zero_wf' succ_wf' param_wf'
  zero_refines succ_refines param_refines
attribute [local grind =] List.map_cons List.map_nil List.mem_singleton List.mem_cons
  List.mem_nil_iff
attribute [local grind] ConLeche.Level.byCases

/-- The hand proof is `Level.by_cases_refines_aux` (`Refine/Level.lean`, 75 lines). -/
theorem by_cases_refines_tuned {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {p : name.Name} {l r : level.Level} (hp : NameWF p) (hl : LevelWF l) (hr : LevelWF r)
    {diff : Std.I64} {o : Option Bool} :
    level.by_cases fuel p l r diff = ok o →
      ConLeche.Level.byCases fuel.val (absName p) (absLevel l) (absLevel r) diff.val = o := by
  intro h
  rw [level.by_cases.eq_def] at h
  simp only [name.singleton, level.singleton] at h
  rust_norm h
  all_goals rust_grind
end Level70

/-! ### Experiment 2, tuned: 4.7 s → 2.2 s (hand 0.65 s), and one line.  And a
fourth walk of the same kind, `ExprOpsMeta.reset_meta_go_refines` (330 lines by
hand, 0.62 s): one line, 2.0 s. -/
section ExprOps70
open ConRon.Refine.ExprOps
attribute [local grind =] KeyWF_mk absKey_mk Inst1Q_iff absExpr_mk bind_eq_ok_iff name_dup_eq
attribute [local grind] ConLeche.Expr.instantiate1 absExprKind
attribute [local grind →] Inst1Spec.use expr_nat_key_eq Expr.dup_eq Expr.binder_meta_dup_eq
  Expr.bvar_refines Expr.bvar_wf Expr.app_refines app_wf' Expr.lam_refines lam_wf'
  Expr.forall_e_refines forall_e_wf' Expr.let_e_refines let_e_wf' Expr.proj_refines proj_wf'
  hit' set' memo1_get_hit HashMap.uscalar_sub_eq HashMap.uscalar_add_eq
attribute [local grind →] ExprWF.fvar_kids ExprWF.sort_kids ExprWF.const_kids ExprWF.app_kids
  ExprWF.lam_kids ExprWF.forall_e_kids ExprWF.let_e_kids ExprWF.lit_kids ExprWF.proj_kids

/-- The closing tactic, the same in all ten cases: the `Spec`'s binders, the
unfolding, the idiom. -/
macro "inst1_close_tuned" : tactic => `(tactic| (
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    rust_norm h
    all_goals rust_grind))

/-- One line: the node-shaped induction and the idiom (`instantiate1_go_auto` above
is the ten-shape-line version; `ExprOps.instantiate1_go_refines` the hand one). -/
theorem instantiate1_go_tuned {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr} (he : ExprWF e) :
    Inst1Spec v e := by
  have hx := key_exact
  induction e, he using ExprWF.ind_node <;> inst1_close_tuned

/-- The induction hypothesis of `reset_meta_go_refines` as a predicate on the node. -/
def ResetSpec (e : expr.Expr) : Prop :=
  ∀ (memo memo' : ron.hashmap.HashMap expr.Expr expr.Expr) (r : expr.Expr),
    MemoInv ExprWF absExpr ResetQ memo →
    expr_ops.reset_meta_go memo e = ok (r, memo') →
    (ExprWF r ∧ absExpr r = ConLeche.Expr.resetMeta (absExpr e)) ∧ MemoInv ExprWF absExpr ResetQ memo'

theorem ResetSpec.use {e : expr.Expr} {memo memo' : ron.hashmap.HashMap expr.Expr expr.Expr}
    {r : expr.Expr} (h : expr_ops.reset_meta_go memo e = ok (r, memo')) (hs : ResetSpec e)
    (hm : MemoInv ExprWF absExpr ResetQ memo) :
    (ExprWF r ∧ absExpr r = ConLeche.Expr.resetMeta (absExpr e)) ∧
      MemoInv ExprWF absExpr ResetQ memo' :=
  hs memo memo' r hm h
theorem ResetQ_iff (k : ConLeche.Expr) (r : expr.Expr) :
    ResetQ k r ↔ (ExprWF r ∧ absExpr r = ConLeche.Expr.resetMeta k) := Iff.rfl
theorem never_meta' {pw : prop_when.PropWhen} (h : prop_when.never = ok pw) :
    BinderMetaWF ⟨pw⟩ ∧ absBinderMeta ⟨pw⟩ = (⟨.never⟩ : ConLeche.BinderMeta) := never_meta h
theorem fvar_wf' {idx : Std.U64} {ty e : expr.Expr} (h : expr.fvar idx ty = ok e)
    (hty : ExprWF ty) : ExprWF e := Expr.fvar_wf hty h
attribute [local grind →] ResetSpec.use never_meta' memo_e_get_hit Expr.fvar_refines fvar_wf'
attribute [local grind =] ResetQ_iff
attribute [local grind] ConLeche.Expr.resetMeta

macro "reset_close_tuned" : tactic => `(tactic| (
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    rust_norm h
    all_goals rust_grind))

/-- The hand proof is `ExprOpsMeta.reset_meta_go_refines` (330 lines). -/
theorem reset_meta_go_tuned {e : expr.Expr} (he : ExprWF e) : ResetSpec e := by
  have hx := expr_key_exact
  induction e, he using ExprWF.ind_node <;> reset_close_tuned
end ExprOps70

/-! ### Experiment 3, tuned: 0.84 s → 0.6 s (hand 0.16 s). -/
section Arm70
open ConRon.Refine.State ConRon.Refine.FEnv ConRon.Refine.Core
attribute [local grind =] run_bind_eq except_bind_ok except_bind_error run_pure_eq rawNatLitC_eq'
  bind_eq_ok_iff RunOk_ok RunOk_error
attribute [local grind →] Wrappers.whnf_use raw_nat_lit_use

theorem reduce_nat_lits_i_tuned {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim (Option.map (fun p : ron.nat.Nat × ron.nat.Nat => (Nat.toNat p.1, Nat.toNat p.2)))
      (fun o => ∀ p, o = some p → Nat.NatWF p.1 ∧ Nat.NatWF p.2)
      (fun st fe => cached.core_c.reduce_nat_lits_i mode fuel st fe d a b)
      (fun lfe => natLitsI (knot mode lfe fuel.val) d.val (absExpr a) (absExpr b)) := by
  refine Sim.ofRun fun fe lfe hfwf hfrel st r st' hwf hok lst hrel => ?_
  unfold cached.core_c.reduce_nat_lits_i at hok
  rust_norm hok
  all_goals simp only [natLitsI]
  all_goals rust_grind

/-! A fourth arm of the same kind, `Lits.reduce_nat_bin_i_refines` (73 lines by hand on top
of the 75-line `lits_replay`; 0.51 s here).  It is the one that needed *statement-shape*
work rather than lemma-set work, and the two rules it taught are the ones to remember:

* **the inlined fragment**: con-leche writes the two-literal read inline under a different
  continuation, and the Rust factors it into `reduce_nat_lits_i`; the hand proof quantifies
  the continuation (`lits_replay`), the automatic one states once that `natBinI` *is*
  `natLitsI >>= k` (`natBinI_eq`, a monad-law `rfl` per branch) and lets `grind` chain the
  refinement of `reduce_nat_lits_i` through it;
* **quantified clauses inside a `Spec` do not fire** — `OpSpec`'s `∀ e, o = some e → …`
  takes its E-matching pattern from its conclusion (`absExpr e`) and instantiates at every
  expression in sight but the right one; and a WF clause `∀ p, o = some p → NatWF p.1 ∧ …`
  instantiates at the pair and leaves `(fst, snd).1` unreduced.  Both become use lemmas
  keyed on the Rust equation *with the constructor in it* (`nat_op_some_use`,
  `nat_op_none_use`) or quantified over the components (`lits_use`). -/

theorem natBinI_eq (r : ConLeche.Cached.CoreFnsI) (depth : Nat) (c : ConLeche.Name)
    (a b : ConLeche.Expr) :
    natBinI r depth c a b = (natLitsI r depth a b >>= fun o => match o with
      | some p => match ConLeche.natOpResult c p.1 p.2 with
        | some x => pure (some x)
        | none => pure none
      | none => pure none) := by
  unfold natBinI natLitsI
  simp only [bind_assoc, pure_bind]
  congr 1; funext w₁
  cases ConLeche.Cached.rawNatLitC? w₁ with
  | none => simp only [pure_bind]
  | some n₁ =>
    simp only [bind_assoc]
    congr 1; funext w₂
    cases ConLeche.Cached.rawNatLitC? w₂ with
    | none => simp only [pure_bind]
    | some n₂ =>
      simp only [pure_bind]
      cases ConLeche.natOpResult c n₁ n₂ <;> simp only []

theorem nat_op_result_use {c : name.Name} {a b : ron.nat.Nat} {o : Option expr.Expr}
    (h : core_k.nat_op_result c a b = ok (.Ok o)) (hc : NameWF c) (ha : Nat.NatWF a)
    (hb : Nat.NatWF b) : CoreK.OpSpec c a b o :=
  CoreK.nat_op_result_refines hc ha hb CoreK.natOpPinned h
theorem nat_op_some_use {c : name.Name} {a b : ron.nat.Nat} {e : expr.Expr}
    (h : core_k.nat_op_result c a b = ok (.Ok (some e))) (hc : NameWF c) (ha : Nat.NatWF a)
    (hb : Nat.NatWF b) :
    ConLeche.natOpResult (absName c) (Nat.toNat a) (Nat.toNat b) = some (absExpr e) ∧ ExprWF e :=
  (nat_op_result_use h hc ha hb).1 e rfl
theorem nat_op_none_use {c : name.Name} {a b : ron.nat.Nat}
    (h : core_k.nat_op_result c a b = ok (.Ok none)) (hc : NameWF c) (ha : Nat.NatWF a)
    (hb : Nat.NatWF b) :
    ConLeche.natOpResult (absName c) (Nat.toNat a) (Nat.toNat b) = none :=
  (nat_op_result_use h hc ha hb).2 rfl

/-- `reduce_nat_lits_i`'s refinement as a use lemma (from the tower's `Sim` statement,
here from `reduce_nat_lits_i_refines`), the WF clause quantified over the components. -/
theorem lits_use {mode : env.CheckMode} {fuel : Std.U64} {st st1 : cached.state_c.CState}
    {fe : fenv.FEnv} {d : Std.U64} {a b : expr.Expr} {o : Option (ron.nat.Nat × ron.nat.Nat)}
    (h : cached.core_c.reduce_nat_lits_i mode fuel st fe d a b = ok (.Ok o, st1))
    (hw : Wrappers mode fuel) (ha : ExprWF a) (hb : ExprWF b)
    {lfe : ConLeche.FEnv} (hfwf : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    (hwf : StateWF st) {lst : ConLeche.Cached.CState} (hrel : StateRel st lst) :
    ∃ lst1, (natLitsI (knot mode lfe fuel.val) d.val (absExpr a) (absExpr b)).run lst
        = .ok (o.map (fun p => (Nat.toNat p.1, Nat.toNat p.2)), lst1)
      ∧ StateRel st1 lst1 ∧ StateWF st1 ∧ ∀ m n, o = some (m, n) → Nat.NatWF m ∧ Nat.NatWF n := by
  obtain ⟨lst1, h1, h2, h3, h4⟩ :=
    reduce_nat_lits_i_refines hw d ha hb fe lfe hfwf hfrel st o st1 hwf h lst hrel
  exact ⟨lst1, h1, h2, h3, fun m n hmn => h4 (m, n) hmn⟩

attribute [local grind →] nat_op_some_use nat_op_none_use lits_use
attribute [local grind =] natBinI_eq Option.map.eq_def

/-- The hand proof is `Lits.reduce_nat_bin_i_refines` (`Refine/Core/Arms/Lits.lean`). -/
theorem reduce_nat_bin_i_tuned {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {c : name.Name} {a b : expr.Expr}
    (hc : NameWF c) (ha : ExprWF a) (hb : ExprWF b) :
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.reduce_nat_bin_i mode fuel st fe d c a b)
      (fun lfe => natBinI (knot mode lfe fuel.val) d.val (absName c) (absExpr a) (absExpr b)) := by
  refine Sim.ofRun fun fe lfe hfwf hfrel st r st' hwf hok lst hrel => ?_
  unfold cached.core_c.reduce_nat_bin_i at hok
  rust_norm hok
  all_goals rust_grind
end Arm70

end ConRon.Refine.Automation
