import ConRon.Refine.Level
import ConRon.Refine.ExprOps
import ConRon.Refine.Core.Arms.Lits
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

theorem Sim.ofRun {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : ∀ fe lfe, FEnvWF fe → FEnvRel fe lfe → ∀ st r st', StateWF st →
      f st fe = ok (.Ok r, st') → ∀ lst, StateRel st lst →
        RunOk ((g lfe).run lst) (fun v lst' => v = A r ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r)) :
    Sim A WF f g := by
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

/-- The hand proof is `Core.lits_replay` + `reduce_nat_lits_i_refines`
(`Refine/Core/Arms/Lits.lean`, 75 + 4 lines); this one is five lines. -/
theorem reduce_nat_lits_i_auto {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim (Option.map (fun p : ron.nat.Nat × ron.nat.Nat => (Nat.toNat p.1, Nat.toNat p.2)))
      (fun o => ∀ p, o = some p → Nat.NatWF p.1 ∧ Nat.NatWF p.2)
      (fun st fe => cached.core_c.reduce_nat_lits_i mode fuel st fe d a b)
      (fun lfe => natLitsI (knot mode lfe fuel.val) d.val (absExpr a) (absExpr b)) := by
  refine Sim.ofRun fun fe lfe hfwf hfrel st r st' hwf hok lst hrel => ?_
  unfold cached.core_c.reduce_nat_lits_i at hok
  rust_inv hok
  all_goals simp only [natLitsI]
  all_goals grind (gen := 24) [→ Wrappers.whnf_use, → raw_nat_lit_use, run_bind_eq, except_bind_ok,
    except_bind_error, run_pure_eq, rawNatLitC_eq', bind_eq_ok_iff, RunOk_ok, RunOk_error]

end Arm

end ConRon.Refine.Automation
