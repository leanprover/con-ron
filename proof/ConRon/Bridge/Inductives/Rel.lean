/-
# `ConRon.Bridge.Inductives.Rel` — the inductive tier's core-grade vocabulary

DESIGN §8.2's **Theorem 1** at the uniform inductive route (task #105).
`Run.lean` holds the pure grade; this module adds what the stages that call
the knot, switch the environment index or read it are phrased with, and the
run forms those stages share.

* **The core grade**: `CSpec` (invariant `CheckOK`, frame
  `Bridge/Checker/Hyp.lean`'s `CoreStep`) and `CSpecF` (its answer related to
  a con-leche function run at `fueledOpsM .verified`, through `FOk`).  `PStep.toCore`
  is the bridge from the pure grade.
* **The install frame**: `InstStep`, `ReadOK`, `IFEnvOKS`, for runs that push
  constants and call the knot at the pushed index.
* **The environment relations**: `EnvRel` (an index answers for an
  environment), `InstRel` (an install's answer), `IndOut` (the route's
  conclusion, what `IndSpec` reads).
* **Run forms**: `stripPis`/`stripLams`, the spine readers, the interners the
  generators call, `lvlEq?`/`readLevelM` at the pure frame, `List.mapM`/
  `allM`/`anyM` of a pure-grade step, `fvarB` (with `FvarBSpec` discharged),
  the knot's entry points (`whnf_crun`, `infer_crun`, `ensureSort_crun`,
  `defeq_crun`, `lvlEq?_crun`) and the telescope opener.

**Why `lvlEq?` sits at the core grade** (task #97-P3-Frame): it is a CACHED
verdict walk — it probes `caches.lvlEqC` and on a miss reads both handles
back through `readLevelM` (writing `readLC`) and records the verdict (writing
`lvlEqC`), exactly as the Rust's `core::lvl_eq` does.  `PStep`'s cache clause
(`Bridge/StateOK.lean`'s `CacheFrame`) lets those two tables move, so its
FRAME is pure (`lvlEq?_pstep`); but its ANSWER is the verdict only under
`LvlEqCacheOK`, which `StateOK` does not carry, so a twin whose answer
contains the verdict (`BlockShape.withSort`'s `isProp`) is `CSpec`.
-/
module

public import ConRon.Bridge.Inductives.Run
public import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Core.Walks.Cached
public import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.ExprOps.Ranges
public import ConRon.Bridge.ExprOps.Subst
import ConRon.Bridge.ExprOps.Owed
public import ConRon.Bridge.ExprOps.Spine
/- `simp only [List.allM]`/`[List.anyM]` unfold the toolchain's monadic list
folds, whose bodies `Init.Data.List.Control` does not expose. -/
import all Init.Data.List.Control
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.ExprOps.Inst1
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The core grade -/

/-- con-leche: none — **the bridge between the two grades**: a pure step
preserves the whole checking invariant, by `Bridge/StateOK.lean`'s
`CheckOK.mono`.  This is what lets a core-grade function call a pure-grade one
and keep its own hypothesis. -/
theorem PStep.toCore {env : Env} {fe : IFEnv} {s s' : AState}
    (h : PStep s s') (hc : CheckOK false env fe s) : CoreStep env fe s s' :=
  ⟨hc.monoF h.ok h.ext h.cframe h.pins, h.ext, h.pins⟩

/-- con-leche: ConLeche/Verify/Cached/SimC.lean:366 SimC — **the CORE grade's
statement**: the same at a function that calls the knot, so the invariant is
`CheckOK` and the frame is `CoreStep`.  The pure side's fuel existential lives
inside `R`, as `Bridge/Core/Knot.lean`'s `SimE` has it. -/
@[expose] def CSpec (env : Env) (fe : IFEnv) {α : Type}
    (P : EStore → Prop) (c : AM α) (R : EStore → α → Prop) : Prop :=
  ∀ (s₀ s' : AState) (r : α), CheckOK false env fe s₀ → P s₀.store →
    c s₀ = .ok (r, s') → CoreStep env fe s₀ s' ∧ R s'.store r

/-- con-leche: ConLeche/Verify/Cached/BlockRunC.lean:335 SimG — **the core
grade against a monad-generic con-leche function** (task #105): the twin's
answer is related by `R` to SOME value the pure side, run at the monotone
fueled operations `fueledOpsM .verified`, produces at some fuel (`FOk`,
`Bridge/Inductives/Records.lean`).  Composing two such runs needs no
monotonicity lemma of the composed functions: `FOk.bind` takes the maximum. -/
@[expose] def CSpecF (env : Env) (fe : IFEnv) {α β : Type}
    (P : EStore → Prop) (c : AM α) (R : EStore → α → β → Prop) (p : FueledM β) : Prop :=
  CSpec env fe P c (fun st r => ∃ v, R st r v ∧ FOk p v)

/-! ## The install frame

A run that SWITCHES the environment index part-way — pushes a constant and
calls the knot at the pushed index (the constructors' stage after the formers'
push, the recursor stage, the tail) — leaves cache rows valid for the NEW environment only (`ConstTyCacheOK env`
asks `env.find?` of every cached constant type).  `CoreStep` at the ENTRY
index is then false.  What such a run owes the consumer
(`Bridge/Inductives/Decl.lean` reads `.state`, `.ext` and `.pins` alone) is
the install frame below; where the next stage runs knot calls at the index
the run ended on, the statement adds `CheckOK` at that index itself. -/

/-- con-leche: ConLeche/Verify/Cached/SimC.lean:366 SimC (the frame half) —
**the install frame**: the state invariant, an append and an untouched pin
table.  `CoreStep` without the caches' environment. -/
structure InstStep (s s' : AState) : Prop where
  state : StateOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins

theorem InstStep.trans {a b c : AState} (h₁ : InstStep a b) (h₂ : InstStep b c) :
    InstStep a c :=
  ⟨h₂.state, h₁.ext.trans h₂.ext, by rw [h₂.pins, h₁.pins]⟩

theorem _root_.ConRon.Bridge.CoreStep.toInst {env : Env} {fe : IFEnv} {s s' : AState}
    (h : CoreStep env fe s s') : InstStep s s' :=
  ⟨h.ok.state, h.ext, h.pins⟩

theorem PStep.toInst {s s' : AState} (h : PStep s s') : InstStep s s' :=
  ⟨h.ok, h.ext, h.pins⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (without the caches) —
**`CheckOK` less its cache clause**: what a state is known to satisfy at an
index whose environment the caches were NOT computed for (after an install
pushed, before the next flush).  Every read-only twin of the tier (the index
lookups, the name and pin reads) needs only this; a knot call needs the
caches too, and gets them from the flush that precedes it
(`ReadOK.flush`). -/
structure ReadOK (env : Env) (fe : IFEnv) (s : AState) : Prop where
  state : StateOK s
  pins : PinsOK s
  ienv : IFEnvOK env fe s

theorem _root_.ConRon.Bridge.CheckOK.toR {env : Env} {fe : IFEnv} {s : AState}
    (h : CheckOK false env fe s) : ReadOK env fe s :=
  ⟨h.state, h.pins, h.ienv⟩

theorem ReadOK.mono {env : Env} {fe : IFEnv} {s s' : AState} (h : ReadOK env fe s)
    (hok : StateOK s') (hx : Ext s.store s'.store) (hp : s'.pins = s.pins) :
    ReadOK env fe s' :=
  ⟨hok, h.pins.mono hx hp, h.ienv.mono hx⟩

/-- con-leche: ConLeche/Cached/CheckerC.lean flushC — **the flush restores
`CheckOK` at any index the state reads correctly**: the caches go, and the
empty cache set is sound at every environment (`CacheOK.of_empty`). -/
theorem ReadOK.flush {env : Env} {fe : IFEnv} {s s' : AState}
    (h : ReadOK env fe s) (hrun : Arena.flushCaches s = .ok ((), s')) :
    CheckOK false env fe s' ∧ InstStep s s' ∧ s'.store = s.store := by
  have e : Arena.flushCaches s = .ok ((), { s with caches := Caches.empty }) := rfl
  rw [e] at hrun
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hrun)
  exact ⟨⟨⟨h.state.wf⟩, CacheOK.of_empty rfl, ⟨h.pins.1, h.pins.2, h.pins.3, h.pins.4,
      h.pins.5, h.pins.6, h.pins.7⟩, ⟨h.ienv.1, h.ienv.2, h.ienv.3, h.ienv.4⟩⟩,
    ⟨⟨h.state.wf⟩, Ext.refl _, rfl⟩, rfl⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `ienv` clause) — the
index spec as a predicate on the STORE (it reads nothing else), so a
`CSpec`'s store precondition can name it at an index OTHER than the one the
caches serve (the iota family reads `fe'`'s lookups and runs its knot calls
at `feSelf`). -/
@[expose] def IFEnvOKS (env : Env) (fe : IFEnv) (st : EStore) : Prop :=
  ∀ s : AState, s.store = st → IFEnvOK env fe s

theorem _root_.ConRon.Bridge.IFEnvOK.toS {env : Env} {fe : IFEnv} {s : AState} (h : IFEnvOK env fe s) :
    IFEnvOKS env fe s.store := by
  intro s' hs
  exact ⟨fun n ci hf => by rw [hs]; exact h.hit n ci hf,
    fun nm c he => by rw [hs]; exact h.cover nm c he,
    fun n t hf => by rw [hs]; exact h.tblHit n t hf,
    fun nm pt he => by rw [hs]; exact h.tblCover nm pt he⟩

theorem IFEnvOKS.mono {env : Env} {fe : IFEnv} {st st' : EStore}
    (h : IFEnvOKS env fe st) (hx : Ext st st') : IFEnvOKS env fe st' := by
  intro s hs
  have h0 : IFEnvOK env fe { s with store := st } := h _ rfl
  have h1 := h0.mono (s' := s) (by rw [hs]; exact hx)
  exact h1

/-- con-leche: none — **`Bridge/ExprOps/Spine.lean`'s `denoteBL` IS
`Frontend.denoteEList`**: a binder telescope is its list of domains (in con-leche
a binder carries its type and nothing else), and the two tiers each write
the readback.  One induction identifies them, and it is what lets
this tier read the BINDERS off `stripPis` rather than only the residual. -/
theorem denoteBL_eq_denoteEList {st : EStore} :
    ∀ (bs : List EIdx), ExprOps.denoteBL st bs = Frontend.denoteEList st bs := by
  intro bs
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [ExprOps.denoteBL, Frontend.denoteEList, ih]
    cases denoteE st a <;> cases Frontend.denoteEList st as <;> rfl

/-! ### `stripPis`, in run form

`Bridge/ExprOps/Spine.lean`'s `stripPis_spec` is closed; here is its run
form with the two inversions of `denoteBP` its readers need, and the other
spine readers and interners the generators call, in run form. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — the run form
at this tier's frame; `stripPis` is read-only, so the state does not move at
all. -/
theorem stripPis_pstep {k : Nat} {s₀ s' : AState} {c : EIdx} {cP : Expr}
    {r : Option (List EIdx × EIdx)} (hok : StateOK s₀)
    (hd : denoteE s₀.store c = some cP)
    (hrun : Arena.stripPis k c s₀ = .ok (r, s')) :
    s' = s₀ ∧ ExprOps.denoteBP s₀.store r = some (Expr.stripPis k cP) := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.stripPis_spec k s₀ c hok (by rw [hd]; rfl))
  exact ⟨h1, h2 cP hd⟩

/-- con-leche: none — a `none` answer is `none` on the pure side too: the
two-sidedness `stripPis`' dispatch needs. -/
theorem stripPis_none {st : EStore} {k : Nat} {cP : Expr}
    (h : ExprOps.denoteBP st none = some (Expr.stripPis k cP)) :
    Expr.stripPis k cP = none := (Option.some.inj h).symm

/-- con-leche: none — and a `some` answer of a telescope peel (`stripPis`,
`stripLams`) names the pure answer: its binders and its residual denote. -/
theorem denoteBP_some {st : EStore} {v : Option (List Expr × Expr)}
    {bs : List EIdx} {e : EIdx}
    (h : ExprOps.denoteBP st (some (bs, e)) = some v) :
    ∃ xs x, v = some (xs, x) ∧ Frontend.denoteEList st bs = some xs ∧
      denoteE st e = some x := by
  simp only [ExprOps.denoteBP] at h
  cases hb : ExprOps.denoteBL st bs with
  | none => rw [hb] at h; simp at h
  | some xs =>
    cases he : denoteE st e with
    | none => rw [hb, he] at h; simp at h
    | some x =>
      rw [hb, he] at h
      refine ⟨xs, x, (Option.some.inj h).symm, ?_, rfl⟩
      rw [← denoteBL_eq_denoteEList]; exact hb

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1355-1357 piResult — the run form of
`Bridge/ExprOps/Spine.lean`'s `piResult_spec`. -/
theorem piResult_run {fuel : Nat} {s s' : AState} {h r : EIdx} {e : Expr}
    (hok : StateOK s) (hd : denoteE s.store h = some e)
    (hrun : Arena.piResult fuel h s = .ok (r, s')) :
    s' = s ∧ denoteE s.store r = some e.piResult := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s) rfl hrun
    (ExprOps.piResult_spec fuel s h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 e hd⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean getAppFn — the run form of
`Bridge/ExprOps/Spine.lean`'s closed `getAppFn_spec`. -/
theorem getAppFn_run {fuel : Nat} {s₀ s' : AState} {h r : EIdx} {hP : Expr}
    (hok : StateOK s₀) (hd : denoteE s₀.store h = some hP)
    (hrun : Arena.getAppFn fuel h s₀ = .ok (r, s')) :
    s' = s₀ ∧ denoteE s₀.store r = some hP.getAppFn := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.getAppFn_spec fuel s₀ h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 hP hd⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean getAppArgs — the same for the
argument list. -/
theorem getAppArgs_run {fuel : Nat} {s₀ s' : AState} {h : EIdx}
    {rs : List EIdx} {hP : Expr} (hok : StateOK s₀)
    (hd : denoteE s₀.store h = some hP)
    (hrun : Arena.getAppArgs fuel h s₀ = .ok (rs, s')) :
    s' = s₀ ∧ Frontend.denoteEList s₀.store rs = some hP.getAppArgs := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.getAppArgs_spec fuel s₀ h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 hP hd⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD — the run
form of `Bridge/ExprOps/Spine.lean`'s closed `fvarTypeD_spec`. -/
theorem fvarTypeD_run {s₀ s' : AState} {h r : EIdx} {hP : Expr}
    (hok : StateOK s₀) (hd : denoteE s₀.store h = some hP)
    (hrun : Arena.fvarTypeD h s₀ = .ok (r, s')) :
    s' = s₀ ∧ denoteE s₀.store r = some hP.fvarTypeD := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.fvarTypeD_spec s₀ h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 hP hd⟩

/-- con-leche: none — **`internLsNode`, as a run**: a universe-argument list
node, which is what `paramLevels` answers. -/
theorem internLsNode_run {s s' : AState} {v : LsNodeView} {vP : List Level}
    {h : LsIdx} (hok : StateOK s) (hv : denoteLList s.store.ls v = some vP)
    (hrun : internLsNode v s = .ok (h, s')) :
    PStep s s' ∧ denoteLs s'.store.lss h = some vP := by
  have hvok : s.store.lss.ViewOK v := by
    intro c hc
    obtain ⟨u, hu⟩ := denoteLList_mem hv hc
    exact lview_isSome_of_denote hu
  obtain ⟨h1, h2, _h3, _h4, _h5, _h6, h7, h8, _h9, h10⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLsNode_spec s v hok.wf hvok)
  have hstep : PStep s s' :=
    PStep.of_caches ⟨h1⟩ h2 h7 h8
  refine ⟨hstep, ?_⟩
  rw [h10]
  exact denoteLList_ext hstep.ext.lss.ls _ _ hv

/-- con-leche: none — **`internNNode`, as a run**. -/
theorem internNNode_run {s s' : AState} {v : NNodeView} {h : NIdx}
    (hok : StateOK s) (hv : s.store.ns.ViewOK v)
    (hrun : internNNode v s = .ok (h, s')) :
    PStep s s' ∧ denoteN s'.store.ns h = denoteNView s'.store.ns v := by
  obtain ⟨h1, h2, _h3, _h4, _h5, _h6, h7, h8, _h9, h10⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internNNode_spec s v hok.wf hv)
  exact ⟨PStep.of_caches ⟨h1⟩ h2 h7 h8, h10⟩

/-- con-leche: none — `internNNode` at a `.str`: every name this tier builds
(`N._model`, `T.proj`, `T._model.proj_i`) goes through it. -/
theorem internStrN_run {s s' : AState} {p : NIdx} {pm : ConLeche.Name}
    {str : String} {h : NIdx} (hok : StateOK s)
    (hp : denoteN s.store.ns p = some pm)
    (hrun : internNNode (.str p str) s = .ok (h, s')) :
    PStep s s' ∧ denoteN s'.store.ns h = some (pm.str str) := by
  obtain ⟨hstep, hd⟩ := internNNode_run hok
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc
        exact nview_isSome_of_denote hp) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteNView, denoteN_ext hp hstep.ext, Option.map_some]

/-- con-leche: none — a handle list's denotation splits over an append, which
is what the two-spine generators (`structCtorSpine`, `structFamI`) need before
`mkAppN`.  Belongs in `Bridge/Rel.lean` beside `denoteEList_snoc`. -/
theorem denoteEList_append {st : EStore} :
    ∀ {a : List EIdx} {as : List Expr} {b : List EIdx} {bs : List Expr},
      Frontend.denoteEList st a = some as →
      Frontend.denoteEList st b = some bs →
      Frontend.denoteEList st (a ++ b) = some (as ++ bs) := by
  intro a
  induction a with
  | nil =>
    intro as b bs ha hb
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha
    simpa using hb
  | cons x xs ih =>
    intro as b bs ha hb
    simp only [Frontend.denoteEList] at ha
    cases hx : denoteE st x with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : Frontend.denoteEList st xs with
      | none => rw [hx, hxs] at ha; simp at ha
      | some ys =>
        rw [hx, hxs] at ha
        obtain rfl := Option.some.inj ha
        simp only [List.cons_append, Frontend.denoteEList, hx, ih hxs hb]

/-! ## One reader on loan from the `ExprOps` tier

`Arena/Env.lean`'s `piSortTeleLen?` is the syntactic Π-telescope's length, and
its Theorem 1 **belongs in `Bridge/ExprOps/Spine.lean`** beside
`stripPis`' — but that tier has not stated it, and
`Bridge/Inductives/Decl.lean`'s `indParamsOk_spec` (the arm's own gate) needs
it.  It is proved here, at this tier's frame. -/

/-- con-leche: ConLeche/Kernel/Env.lean:583-586 Expr.piSortTeleLen? —
**THEOREM 1 for `piSortTeleLen?`**: the number of `∀`-binders before a `Sort`
residual, or `none`.  A fuel induction whose ten-way arm is the `view`
dispatch; the eight arms that are neither a binder nor a sort answer `none` on
both sides, which is the dispatch's own soundness (a handle's view and its
denotation have the same constructor). -/
theorem piSortTeleLen?_spec : ∀ (fuel : Nat) (h : EIdx) (hP : Expr),
    PSpec (fun st => denoteE st h = some hP) (Arena.piSortTeleLen? fuel h)
      (RV hP.piSortTeleLen?) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piSortTeleLen?] at hrun
    exact absurd hrun (fun hc => AM.fail_ok hc)
  | succ fuel ih =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piSortTeleLen?] at hrun
    obtain ⟨v, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hw⟩ := view_run h1
    rw [hs1] at h2
    have hde : denoteEView s₀.store v = some hP := by
      rw [denoteE_view_eq hok.wf hw] at hd; exact hd
    cases v
    case forallE ty body =>
      obtain ⟨et, eb, rfl, hty, hb⟩ := denote_forallE_inv hok.wf hw hd
      obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨hstep, ho⟩ := ih body eb s₀ s₂ o hok hb h3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
      exact ⟨hstep, by rw [ho]; rfl⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨uP, _, rfl⟩ := Option.map_eq_some_iff.mp hde
      exact ⟨PStep.refl hok, rfl⟩
    all_goals
      (obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
       refine ⟨PStep.refl hok, ?_⟩
       simp only [denoteEView] at hde
       first
       | (obtain ⟨x, y, z, _, _, _, rfl⟩ := opt3_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, y, _, _, rfl⟩ := opt2_eq_some_iff.mp hde; rfl)
       | (obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp hde; rfl)
       | (obtain rfl := Option.some.inj hde; rfl))

/-- con-leche: none — **`denoteCI` preserves the constant's KIND**: a handle
record that is not a constructor denotes a constant that is not one.  The
shape a twin that DISPATCHES on the stored constant's kind needs at its
fallthrough arm (`ctorResidualOk`'s `| _ => false`). -/
theorem denoteCI_not_ctor {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c)
    (hne : ∀ v n1 n2, ci ≠ .ctorInfo v n1 n2) :
    ∀ v n1 n2, c ≠ .ctorInfo v n1 n2 := by
  cases ci <;>
    simp_all [Frontend.denoteCI, Option.map_eq_some_iff] <;> grind

/-! ## Two transports the spec layer does not have

`Bridge/Rel.lean` stops at `denoteCI_ext`; `Bridge/Checker/Inv.lean` has the
`…_pext` twins at the WEAKER extension but not the plain `Ext` ones for the
list and the environment.  This tier needs both, because every install
function grows the arena while the environment it was handed stands still. -/

/-! ## The environment's own relation

An install's argument and answer are `IFEnv`s, and the pure side's are
`Env`s.  There is no denotation of a whole index (the stream's index under a
job's layer is frozen and never read back as a list): an index is related to an
environment by its LOOKUPS (`IFEnvOK`), and that is what every knot call of the
tier needs of it.  `EnvRel` adds the two facts a push needs to carry the
lookups across (`IFEnvOK.pushStored`): no table without its structure, on both
sides.  `InstRel` is what an install function concludes, `IndOut` what the
route concludes. -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `ienv` clause) — **an
index answers for an environment**, at a store: the lookups agree
(`IFEnvOKS`), the index has no table without its structure (`TblGate`), and
neither has the environment (`TablesStored`). -/
structure EnvRel (env : Env) (fe : IFEnv) (st : EStore) : Prop where
  ienv : IFEnvOKS env fe st
  gate : TblGate fe
  stored : TablesStored env

/-- con-leche: none — `EnvRel` survives the arena's growth. -/
theorem EnvRel.mono {env : Env} {fe : IFEnv} {st st' : EStore}
    (h : EnvRel env fe st) (hx : Ext st st') : EnvRel env fe st' :=
  ⟨h.ienv.mono hx, h.gate, h.stored⟩

/-- con-leche: none — the relation at a checking state. -/
theorem EnvRel.ofCheck {env : Env} {fe : IFEnv} {s : AState}
    (h : CheckOK false env fe s) (hg : TblGate fe) (henv : EnvWF env) :
    EnvRel env fe s.store :=
  ⟨h.ienv.toS, hg, TablesStored.of_envWF henv⟩

/-- con-leche: none — the lookups at a state whose store is the relation's. -/
theorem EnvRel.ifenv {env : Env} {fe : IFEnv} {s : AState}
    (h : EnvRel env fe s.store) : IFEnvOK env fe s :=
  h.ienv s rfl

/-- con-leche: ConLeche/Kernel/FEnv.lean:189-197 FEnv.push — **a pushed
constant**: the lookups by `IFEnvOK.pushStored`, the gates by their push
lemmas. -/
theorem EnvRel.push {env : Env} {fe : IFEnv} {st : EStore} {ci : IConstantInfo}
    {c : ConstantInfo} (h : EnvRel env fe st) (hwf : StoreWF st)
    (hci : Frontend.denoteCI st ci = some c) :
    EnvRel ⟨c :: env.consts, env.tables⟩ (fe.push ci) st where
  ienv := fun s hs => (h.ienv s hs).pushStored ⟨hs ▸ hwf⟩ h.gate h.stored (hs ▸ hci)
  gate := h.gate.push ci
  stored := h.stored.cons

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**an INSTALL function's answer relation**: the new index answers for an
environment con-leche's own install produces (`P` names that install).

Every install twin of this tier (the formers' and constructors' pushes, the
recursor stage's pushes) answers an `IFEnv`, and this is the one relation all
of them use. -/
structure InstRel (P : Env → Prop) (st : EStore) (fe' : IFEnv) : Prop where
  denote : ∃ env', EnvRel env' fe' st ∧ P env'

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**what the inductive route leaves behind**: `IndSpec.run`'s conclusion, the
state's frame and the pure side's run (`run`, instantiated by
`Bridge/Inductives/Decl.lean` at `ConLeche.checkDecl … (.indDecl b nP)`).
Nothing about the route's environment: the job's index is dropped with its
scratch tier. -/
structure IndOut (s s' : AState) (run : Prop) : Prop where
  state : StateOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins
  run : run

/-! ## The recognisers' readers

The reader (`readBlock`) and the generated recursors read the pin table,
peel a rule's right-hand side with `stripLams`, and ask `lvlEq?` for
`isProp`.  The run forms below put each of those at THIS
tier's frame. -/

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
**the reserved list at this tier's frame**: `Bridge/Checker/Names.lean`'s
`reservedBasisNames_run` gives `PinStep` and the list. -/
theorem reservedBasisNames_pstep {s s' : AState} {hs : List NIdx}
    (hok : StateOK s) (hp : PinsOK s)
    (hr : Arena.reservedBasisNames s = .ok (hs, s')) :
    PStep s s' ∧
      Frontend.denoteNList s'.store.ns hs = some ConLeche.reservedBasisNames := by
  obtain ⟨hps, hd⟩ := reservedBasisNames_run hok.wf hp hr
  refine ⟨PStep.of_caches ⟨hps.wf⟩ hps.ext hps.caches hps.pins, ?_⟩
  rw [← reservedBasisNameValues_eq]
  exact denoteNL_toList _ _ hd

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams — the run form
of `Bridge/ExprOps/Spine.lean`'s closed `stripLams_spec`, `stripPis_pstep`'s
λ twin. -/
theorem stripLams_pstep {k : Nat} {s₀ s' : AState} {c : EIdx} {cP : Expr}
    {r : Option (List EIdx × EIdx)} (hok : StateOK s₀)
    (hd : denoteE s₀.store c = some cP)
    (hrun : Arena.stripLams k c s₀ = .ok (r, s')) :
    s' = s₀ ∧ ExprOps.denoteBP s₀.store r = some (Expr.stripLams k cP) := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.stripLams_spec k s₀ c hok (by rw [hd]; rfl))
  exact ⟨h1, h2 cP hd⟩

/-- con-leche: none — **`lvlEq?` at the pure frame**: it moves only the two
caches `CacheFrame` names (`Core.lvlEq?_frame`). -/
theorem lvlEq?_pstep {s s' : AState} {u v : LIdx} {r : Option Bool}
    (hok : StateOK s) (hrun : Arena.lvlEq? u v s = .ok (r, s')) : PStep s s' := by
  obtain ⟨hst, -, hp, hcf⟩ := Core.lvlEq?_frame hrun
  exact ⟨⟨by rw [hst]; exact hok.wf⟩, by rw [hst]; exact Ext.refl _,
    hcf, hp⟩

/-- con-leche: none — **`readLevelM` at the pure grade's frame** (the twin
reads a level back through the CACHED readback, as the port's `read_level_m`
does).  The frame
needs nothing: the store, memos and pins stand still and the one table that
moves is `readLC` (`Core.CacheFrame.ofReadLevelM`). -/
theorem readLevelM_pstep {s s' : AState} {h : LIdx} {u : Level}
    (hok : StateOK s) (hrun : readLevelM h s = .ok (u, s')) : PStep s s' := by
  obtain ⟨hst, -, hp, -⟩ := Core.readLevelM_frame hrun
  exact ⟨⟨by rw [hst]; exact hok.wf⟩, by rw [hst]; exact Ext.refl _,
    Core.CacheFrame.ofReadLevelM hrun, hp⟩

/-- con-leche: none — `readLevelM`'s ANSWER, which is the denotation only
under `ReadLCacheOK`, carried from the statement's along the pure steps before
it (`CacheFrame.readL`). -/
theorem readLevelM_denote_L {s₀ s s' : AState} {h : LIdx} {u : Level}
    (hrl : ReadLCacheOK s₀.caches.readLC s₀.store)
    (q : PStep s₀ s) (hrun : readLevelM h s = .ok (u, s')) :
    denoteL s.store.ls h = some u :=
  (Core.readLevelM_denote (q.cframe.readL hrl) hrun).1

/-! ## `List.mapM` at the pure frame

The generators map a pure-grade twin over a list.  `mapM_pstep` is the one
induction; the answer is a pointwise relation `ListRel`, which
`ListRel.toEList` turns into `denoteEList`. -/

/-- con-leche: none — a relation lifted pointwise to two lists of the same
length. -/
@[expose] def ListRel {β γ : Type} (R : EStore → β → γ → Prop) (st : EStore) :
    List β → List γ → Prop
  | [], [] => True
  | b :: bs, c :: cs => R st b c ∧ ListRel R st bs cs
  | _, _ => False

/-- con-leche: none — **`List.mapM` of a pure-grade step**: the frame
composes and the answers relate pointwise. -/
theorem mapM_pstep {α β γ : Type} (f : α → AM β) (g : α → γ)
    (R : EStore → β → γ → Prop) (P : α → EStore → Prop)
    (hRx : ∀ {st st' : EStore} {b : β} {c : γ}, Ext st st' → R st b c → R st' b c)
    (hPx : ∀ {a : α} {st st' : EStore}, Ext st st' → P a st → P a st')
    (hf : ∀ (a : α) (s₀ s' : AState) (b : β), StateOK s₀ → P a s₀.store →
      f a s₀ = .ok (b, s') → PStep s₀ s' ∧ R s'.store b (g a)) :
    ∀ (xs : List α) (s₀ s' : AState) (bs : List β), StateOK s₀ →
      (∀ a ∈ xs, P a s₀.store) → xs.mapM f s₀ = .ok (bs, s') →
      PStep s₀ s' ∧ ListRel R s'.store bs (xs.map g) := by
  intro xs
  induction xs with
  | nil =>
    intro s₀ s' bs hok _ hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, trivial⟩
  | cons a as ih =>
    intro s₀ s' bs hok hP hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨b, s1, k1, hz1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hb⟩ := hf a s₀ s1 b hok (hP a (by simp)) k1
    obtain ⟨cs, s2, k2, hz2⟩ := AM.bind_ok hz1
    obtain ⟨p2, hcs⟩ := ih s1 s2 cs p1.ok
      (fun x hx => hPx p1.ext (hP x (by simp [hx]))) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hz2
    exact ⟨p1.trans p2, hRx p2.ext hb, hcs⟩

/-- con-leche: none — `List.allM` of a pure-grade test over a denoting
handle list, with a store invariant `Q` the test may read (the name a
`mentionsConst` looks for, say): the verdict is the pure `List.all`. -/
theorem allM_E_pstep {f : EIdx → AM Bool} {F : Expr → Bool} (Q : EStore → Prop)
    (hQx : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (hf : ∀ (e : EIdx) (eP : Expr) (s₀ s' : AState) (b : Bool), StateOK s₀ →
      Q s₀.store → denoteE s₀.store e = some eP → f e s₀ = .ok (b, s') →
      PStep s₀ s' ∧ b = F eP) :
    ∀ (hs : List EIdx) (xs : List Expr) (s₀ s' : AState) (b : Bool),
      StateOK s₀ → Q s₀.store → Frontend.denoteEList s₀.store hs = some xs →
      hs.allM f s₀ = .ok (b, s') → PStep s₀ s' ∧ b = xs.all F := by
  intro hs
  induction hs with
  | nil =>
    intro xs s₀ s' b hok _ h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.allM] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons e es ih =>
    intro xs s₀ s' b hok hq h hrun
    simp only [Frontend.denoteEList] at h
    cases he : denoteE s₀.store e with
    | none => rw [he] at h; simp at h
    | some eP =>
      cases hes : Frontend.denoteEList s₀.store es with
      | none => rw [he, hes] at h; simp at h
      | some esP =>
        rw [he, hes] at h
        obtain rfl := (Option.some.inj h).symm
        simp only [List.allM] at hrun
        obtain ⟨c, s1, k1, z1⟩ := AM.bind_ok hrun
        obtain ⟨p1, hc⟩ := hf e eP s₀ s1 c hok hq he k1
        cases c with
        | false =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
          refine ⟨p1, ?_⟩
          simp only [List.all_cons, ← hc, Bool.false_and]
        | true =>
          obtain ⟨p2, hb⟩ := ih esP s1 s' b p1.ok (hQx p1.ext hq)
            (denoteEList_ext p1.ext _ _ hes) z1
          refine ⟨p1.trans p2, ?_⟩
          simp only [List.all_cons, ← hc, Bool.true_and, hb]

/-- con-leche: none — and `List.anyM`: the verdict is the pure `List.any`. -/
theorem anyM_E_pstep {f : EIdx → AM Bool} {F : Expr → Bool} (Q : EStore → Prop)
    (hQx : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (hf : ∀ (e : EIdx) (eP : Expr) (s₀ s' : AState) (b : Bool), StateOK s₀ →
      Q s₀.store → denoteE s₀.store e = some eP → f e s₀ = .ok (b, s') →
      PStep s₀ s' ∧ b = F eP) :
    ∀ (hs : List EIdx) (xs : List Expr) (s₀ s' : AState) (b : Bool),
      StateOK s₀ → Q s₀.store → Frontend.denoteEList s₀.store hs = some xs →
      hs.anyM f s₀ = .ok (b, s') → PStep s₀ s' ∧ b = xs.any F := by
  intro hs
  induction hs with
  | nil =>
    intro xs s₀ s' b hok _ h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.anyM] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons e es ih =>
    intro xs s₀ s' b hok hq h hrun
    simp only [Frontend.denoteEList] at h
    cases he : denoteE s₀.store e with
    | none => rw [he] at h; simp at h
    | some eP =>
      cases hes : Frontend.denoteEList s₀.store es with
      | none => rw [he, hes] at h; simp at h
      | some esP =>
        rw [he, hes] at h
        obtain rfl := (Option.some.inj h).symm
        simp only [List.anyM] at hrun
        obtain ⟨c, s1, k1, z1⟩ := AM.bind_ok hrun
        obtain ⟨p1, hc⟩ := hf e eP s₀ s1 c hok hq he k1
        cases c with
        | true =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
          refine ⟨p1, ?_⟩
          simp only [List.any_cons, ← hc, Bool.true_or]
        | false =>
          obtain ⟨p2, hb⟩ := ih esP s1 s' b p1.ok (hQx p1.ext hq)
            (denoteEList_ext p1.ext _ _ hes) z1
          refine ⟨p1.trans p2, ?_⟩
          simp only [List.any_cons, ← hc, Bool.false_or, hb]

/-- con-leche: none — `ListRel` at a handle denotation is `denoteEList`. -/
theorem ListRel.toEList {st : EStore} :
    ∀ {bs : List EIdx} {cs : List Expr},
      ListRel (fun st b c => denoteE st b = some c) st bs cs →
      Frontend.denoteEList st bs = some cs := by
  intro bs
  induction bs with
  | nil => intro cs h; cases cs with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons b bs ih =>
    intro cs h
    cases cs with
    | nil => exact h.elim
    | cons c cs =>
      obtain ⟨h1, h2⟩ := h
      simp only [Frontend.denoteEList, h1, ih h2]

/-! ## `FvarBSpec`, discharged

`Bridge/ExprOps/Abs.lean` takes `fvarB`'s Theorem 1 as the hypothesis
`FvarBSpec`, and `Bridge/ExprOps/Ranges.lean`'s `fvarB_spec` states everything
it asks EXCEPT the `abs1C` frame (`fvarB` writes only `fvarBC`).  This section
supplies that frame — a program-level fact, proved over `fvarRangeGo`'s
mutual block — and assembles
the record, so `abstract1Fast_spec` has its hypothesis and `closeTelescope`
(`FieldTele.lean`) can call it; `fvarB_pstep` is the run form the walks read.  **On loan from the `ExprOps` tier**, whose
module it belongs in: `Ranges.lean`'s `fvarB_spec` gaining the conjunct makes
this section one line. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1714 fvarB — **the free-variable
cutoff's run form** at this tier's frame: `Bridge/ExprOps/Ranges.lean`'s
`fvarB_spec` answers `fvarRange`, which is `Expr.fvarB` (`Expr.fvarB_eq`). -/
theorem fvarB_pstep {fuel : Nat} {s₀ s' : AState} {e : EIdx} {eP : Expr}
    {r : Nat} (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.fvarB fuel e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ s'.store = s₀.store ∧ r = Expr.fvarB eP := by
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.fvarB_spec fuel s₀ e hok (by rw [hd]; rfl))
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.wf⟩ ?_ h2 h3, h1, ?_⟩
  · rw [h1]; exact Ext.refl _
  · rw [h4 eP hd, Expr.fvarB_eq]

/-! ## Reading the index at `ReadOK` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean constsResolveFFast — `Bridge/Checker/Names.lean`'s
`constsResolveFFast_run` at `ReadOK`: the walk reads the store, the pins and
the index, never the caches. -/
theorem constsResolveFFast_runR {env : Env} {fe : IFEnv}
    {e : EIdx} {x : Expr} {r : Bool} {s s' : AState}
    (hck : ReadOK env fe s) (hd : denoteE s.store e = some x)
    (hrun : Arena.constsResolveFFast fe e s = .ok (r, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      r = Expr.constsResolve env x := by
  simp only [Arena.constsResolveFFast] at hrun
  obtain ⟨p, s1, g1, k1⟩ :=
    AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) hrun
  obtain ⟨b, tb⟩ := p
  obtain ⟨rfl, hb, -⟩ := constsResolveFGo_run coreWalkFuel hck.state
    hck.pins hck.ienv CRMemoOK.empty hd g1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
  exact ⟨rfl, rfl, rfl, hb⟩

/-- con-leche: none — `constsResolveFFast` at the pure-grade frame: it moves
neither the store, the caches nor the pins. -/
theorem constsResolveFFast_pstep {env : Env} {fe : IFEnv}
    {s₀ s' : AState} {e : EIdx} {eP : Expr} {r : Bool} (hok : ReadOK env fe s₀)
    (he : denoteE s₀.store e = some eP)
    (hrun : Arena.constsResolveFFast fe e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r = eP.constsResolve env := by
  obtain ⟨h1, h2, h3, h4⟩ := constsResolveFFast_runR hok he hrun
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.state.wf⟩ (by rw [h1]; exact Ext.refl _)
    h2 h3, h4⟩

/-- con-leche: none — `allM_E_ck` with a store invariant the body may read. -/
theorem allM_E_ckQ {env : Env} {fe : IFEnv} {f : EIdx → AM Bool}
    {F : Expr → Bool} (Q : EStore → Prop)
    (hQ : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (hf : ∀ (e : EIdx) (eP : Expr) (s₀ s' : AState) (x : Bool), ReadOK env fe s₀ →
      Q s₀.store → denoteE s₀.store e = some eP → f e s₀ = .ok (x, s') →
      PStep s₀ s' ∧ x = F eP) :
    ∀ (es : List EIdx) (esP : List Expr) (s₀ s' : AState) (x : Bool),
      ReadOK env fe s₀ → Q s₀.store → Frontend.denoteEList s₀.store es = some esP →
      es.allM f s₀ = .ok (x, s') → PStep s₀ s' ∧ x = esP.all F := by
  intro es
  induction es with
  | nil =>
    intro esP s₀ s' x hok _ h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.allM] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok.state, rfl⟩
  | cons e es ih =>
    intro esP s₀ s' x hok hq h hrun
    simp only [Frontend.denoteEList] at h
    cases he : denoteE s₀.store e with
    | none => rw [he] at h; simp at h
    | some eP =>
    cases hr : Frontend.denoteEList s₀.store es with
    | none => rw [he, hr] at h; simp at h
    | some rest =>
    rw [he, hr] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.allM] at hrun
    obtain ⟨c, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hc⟩ := hf e eP s₀ s1 c hok hq he k1
    cases c with
    | false =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      exact ⟨p1, by simp only [List.all_cons, ← hc, Bool.false_and]⟩
    | true =>
      obtain ⟨p2, hx⟩ := ih rest s1 s' x (hok.mono p1.ok p1.ext p1.pins) (hQ p1.ext hq)
        (denoteEList_ext p1.ext _ _ hr) z1
      exact ⟨p1.trans p2, by simp only [List.all_cons, ← hc, Bool.true_and, hx]⟩

/-! ## The knot's entry points, in run form

Each answer is an `FOk` of `fueledOpsM`'s operation, the frame a `CoreStep`. -/

section Knot

variable {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:27 CheckerOps.whnf — the knot's
`whnf` slot in run form, its answer an `FOk` of `fueledOpsM`'s. -/
theorem whnf_crun (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    {s s' : AState} {d : Nat} {e r : EIdx} {eP : Expr}
    (hok : CheckOK false env fe s) (he : denoteE s.store e = some eP)
    (hw : Expr.WScoped d eP)
    (hrun : Arena.whnf .verified fe Arena.checkFuel d e s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∃ w, denoteE s'.store r = some w ∧ Expr.WScoped d w ∧
      FOk ((fueledOpsM .verified).whnf env d eP) w := by
  obtain ⟨h1, h2, h3, v, hv, hwv, hF⟩ := AM.of_run (P := fun u => u = s)
    (Q := fun r u => CheckOK false env fe u ∧ Ext s.store u.store ∧ u.pins = s.pins ∧
      Core.SimE (ConLeche.whnf .verified false env) d eP u.store r)
    rfl hrun ((hk.knot env fe henv).whnf s d e eP hok he hw)
  exact ⟨⟨h1, h2, h3⟩, v, hv, hwv, FOk.whnf hF⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:27 CheckerOps.inferType — the
knot's `infer` slot in run form. -/
theorem infer_crun (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    {s s' : AState} {d : Nat} {e r : EIdx} {eP : Expr}
    (hok : CheckOK false env fe s) (he : denoteE s.store e = some eP)
    (hw : Expr.WScoped d eP)
    (hrun : Arena.inferTypeCore .verified fe Arena.checkFuel d e s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∃ w, denoteE s'.store r = some w ∧ Expr.WScoped d w ∧
      FOk ((fueledOpsM .verified).inferType env d eP) w := by
  obtain ⟨h1, h2, h3, v, hv, hwv, hF⟩ := AM.of_run (P := fun u => u = s)
    (Q := fun r u => CheckOK false env fe u ∧ Ext s.store u.store ∧ u.pins = s.pins ∧
      Core.SimE (ConLeche.inferTypeCore .verified false env) d eP u.store r)
    rfl hrun ((hk.knot env fe henv).infer s d e eP hok he hw)
  exact ⟨⟨h1, h2, h3⟩, v, hv, hwv, FOk.inferType hF⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:27 CheckerOps.ensureSort — the
seventh entry point in run form. -/
theorem ensureSort_crun (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    {s s' : AState} {d : Nat} {e : EIdx} {r : LIdx} {eP : Expr}
    (hok : CheckOK false env fe s) (he : denoteE s.store e = some eP)
    (hw : Expr.WScoped d eP)
    (hrun : Arena.ensureSortCore .verified fe Arena.checkFuel d e s = .ok (r, s')) :
    CoreStep env fe s s' ∧ ∃ u, denoteL s'.store.ls r = some u ∧
      FOk ((fueledOpsM .verified).ensureSort env d eP) u := by
  obtain ⟨h1, h2, h3, u, hu, hF⟩ := AM.of_run (P := fun u => u = s)
    (Q := fun r u => CheckOK false env fe u ∧ Ext s.store u.store ∧ u.pins = s.pins ∧
      SimL (ConLeche.ensureSortCore .verified false env) d eP u.store r)
    rfl hrun (hk.sort env fe henv s d e eP hok he hw)
  exact ⟨⟨h1, h2, h3⟩, u, hu, FOk.ensureSort hF⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean instantiateLevelParams — the
executed level instantiation at the checking invariant (it writes the three
readback caches, so the frame is a `CoreStep`). -/
theorem instLPFast_cstep {s s' : AState}
    {ks : List NIdx} {us : LsIdx} {e r : EIdx} {ksv : List ConLeche.Name}
    {usv : List Level} {eP : Expr} (hok : CheckOK false env fe s)
    (hks : Frontend.denoteNList s.store.ns ks = some ksv)
    (hus : denoteLs s.store.lss us = some usv) (he : denoteE s.store e = some eP)
    (hrun : Arena.instLPFast Arena.coreWalkFuel ks us e s = .ok (r, s')) :
    CoreStep env fe s s' ∧
      denoteE s'.store r = some (eP.instantiateLevelParams ksv usv) := by
  obtain ⟨hst, hx, hL, hLs, hN, hc, hp, -, hrel⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun
    (ExprOps.instLPFast_spec _ s ks us e ksv usv hok.state hok.caches.readN hok.caches.readL
      hok.caches.readLs hks hus (by rw [he]; rfl))
  exact ⟨⟨Core.CheckOK.ofInstLP hok hst hx hL hLs hN hc hp, hx, hp⟩, hrel eP he⟩

/-- con-leche: none — `lvlEq?` at the core grade: the store stands still and
the verdict is `Level.isEquiv` of the denotations (`Core.lvlEq?_spec`). -/
theorem lvlEq?_crun {env : Env} {fe : IFEnv} {s s' : AState}
    {u v : LIdx} {uP vP : Level} {r : Option Bool} (hok : CheckOK false env fe s)
    (hu : denoteL s.store.ls u = some uP) (hv : denoteL s.store.ls v = some vP)
    (hrun : Arena.lvlEq? u v s = .ok (r, s')) :
    CoreStep env fe s s' ∧ r = Level.isEquiv uP vP := by
  obtain ⟨h1, h2, h3, lu, lv, hlu, hlv, ha⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (Core.lvlEq?_spec s u v hok)
  rw [hu] at hlu; rw [hv] at hlv
  cases hlu; cases hlv
  exact ⟨⟨h1, by rw [h2]; exact Ext.refl _, h3⟩, ha⟩

/-- con-leche: ConLeche/Verify/BridgeDecl.lean fueledOpsM — **a knot defeq,
in run form**. -/
theorem defeq_crun {env : Env} {fe : IFEnv}
    (hknot : Core.KnotSpec false env fe Arena.checkFuel) {s₀ s' : AState} {d : Nat}
    {a b : EIdx} {aP bP : Expr} {r : Bool} (hok : CheckOK false env fe s₀)
    (ha : denoteE s₀.store a = some aP) (hb : denoteE s₀.store b = some bP)
    (hwa : Expr.WScoped d aP) (hwb : Expr.WScoped d bP)
    (hrun : Arena.isDefEqCore .verified fe Arena.checkFuel d a b s₀ = .ok (r, s')) :
    CoreStep env fe s₀ s' ∧ FOk ((fueledOpsM .verified).isDefEq env d aP bP) r := by
  obtain ⟨h1, h2, h3, hF⟩ := AM.of_run (P := fun u => u = s₀)
    (Q := fun x u => CheckOK false env fe u ∧ Ext s₀.store u.store ∧ u.pins = s₀.pins ∧
      Core.SimV (ConLeche.isDefEqCore .verified false env) d aP bP x)
    rfl hrun (hknot.defeq s₀ d a b aP bP hok ha hb hwa hwb)
  exact ⟨⟨h1, h2, h3⟩, FOk.isDefEq hF⟩

end Knot

/-! ## The telescope opener

`Arena/CheckerBase.lean`'s `openPisAtFvars` / `openPisAtFvarsFGo` /
`openPisAtFvarsF`, read by the constructors' stage, the recursor pre-pass and
the generated recursors.  The one-pass form is related to con-leche's one-pass
form walk for walk (the arena's push-order vector is `ExprOps.InstLVec` of con-leche's cons-order
list), and con-leche's own `openPisAtFvarsF_eq` turns the answer into the
binder-at-a-time `openPisAtFvars` that con-leche's callers read. -/

/-- con-leche: none — the denotation of an opener's answer: `none` is
`none`, a `some` denotes when its free variables and its residual do. -/
@[expose] def denoteOpen (st : EStore) :
    Option (List EIdx × EIdx) → Option (Option (List Expr × Expr))
  | none => some none
  | some (fvs, e) =>
    (Frontend.denoteEList st fvs).bind fun xs => (denoteE st e).map fun x => some (xs, x)

/-- con-leche: none — `denoteOpen` at a `some`, from its two halves. -/
theorem denoteOpen_some {st : EStore} {fvs : List EIdx} {e : EIdx}
    {xs : List Expr} {x : Expr} (h1 : Frontend.denoteEList st fvs = some xs)
    (h2 : denoteE st e = some x) : denoteOpen st (some (fvs, e)) = some (some (xs, x)) := by
  simp [denoteOpen, h1, h2]

/-- con-leche: none — and read back into its two halves. -/
theorem denoteOpen_some_inv {st : EStore} {fvs : List EIdx} {e : EIdx}
    {o : Option (List Expr × Expr)} (h : denoteOpen st (some (fvs, e)) = some o) :
    ∃ xs x, o = some (xs, x) ∧ Frontend.denoteEList st fvs = some xs ∧
      denoteE st e = some x := by
  simp only [denoteOpen, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨xs, h1, x, h2, rfl⟩ := h
  exact ⟨xs, x, rfl, h1, h2⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars — **the
binder-at-a-time opener, as a run**: pure grade, and the answer denotes
con-leche's. -/
theorem openPisAtFvars_run : ∀ (n : Nat) {i : Nat} {h : EIdx} {hP : Expr}
    {s₀ s' : AState} {r : Option (List EIdx × EIdx)},
    StateOK s₀ → denoteE s₀.store h = some hP →
    Arena.openPisAtFvars n h i s₀ = .ok (r, s') →
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvars n hP i) := by
  intro n
  induction n with
  | zero =>
    intro i h hP s₀ s' r hok hh hrun
    simp only [Arena.openPisAtFvars] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, by simp [denoteOpen, Frontend.denoteEList, hh,
      ConLeche.openPisAtFvars]⟩
  | succ n ih =>
    intro i h hP s₀ s' r hok hh hrun
    simp only [Arena.openPisAtFvars] at hrun
    -- the tag-first twin
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨fv, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨p2, hfv⟩ := internE_run hok (viewOK_fvar (by rw [hd]; rfl)) k2
      have hfv' : denoteE s2.store fv = some (.fvar i domP) := by
        rw [hfv]; simp [denoteEView, denote_ext hd p2.ext]
      obtain ⟨op, s3, k3, z3⟩ := AM.bind_ok z2
      have hb2 : denoteE s2.store body = some bodyP := denote_ext hb p2.ext
      obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run p2.ok hfv'
        (by rw [hb2]; rfl) k3
      have p3 : PStep s2 s3 := PStep.of_caches h1 h2 h4 h5
      have hop : denoteE s3.store op = some (bodyP.instantiate1 (.fvar i domP) 0) :=
        h7 _ hb2
      obtain ⟨o, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨p4, ho⟩ := ih p3.ok hop k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvars]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvars n (bodyP.instantiate1 (.fvar i domP)) (i + 1)
            = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' (p3.ext.trans p4.ext),
            h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo — **the
one-pass opener's core, as a run**: the arena's push-order vector is
`InstLVec` of con-leche's cons-order list. -/
theorem openPisAtFvarsFGo_run : ∀ (n : Nat) {acc : Array EIdx} {ws : List Expr}
    {i : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState} {r : Option (List EIdx × EIdx)},
    StateOK s₀ → ExprOps.InstLVec s₀.store acc ws → denoteE s₀.store h = some hP →
    Arena.openPisAtFvarsFGo acc n h i s₀ = .ok (r, s') →
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvarsFGo ws n hP i) := by
  intro n
  induction n with
  | zero =>
    intro acc ws i h hP s₀ s' r hok hacc hh hrun
    simp only [Arena.openPisAtFvarsFGo] at hrun
    obtain ⟨e, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
      (by rw [hh]; rfl) k1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨PStep.of_caches h1 h2 h4 h5, ?_⟩
    simp [denoteOpen, Frontend.denoteEList, h7 _ hh, ConLeche.openPisAtFvarsFGo]
  | succ n ih =>
    intro acc ws i h hP s₀ s' r hok hacc hh hrun
    simp only [Arena.openPisAtFvarsFGo] at hrun
    -- the tag-first twin
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨dd, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
        (by rw [hd]; rfl) k2
      have p2 : PStep s₀ s2 := PStep.of_caches h1 h2 h4 h5
      have hdd : denoteE s2.store dd = some (domP.instantiateList ws 0) := h7 _ hd
      obtain ⟨fv, s3, k3, z3⟩ := AM.bind_ok z2
      obtain ⟨p3, hfv⟩ := internE_run p2.ok (viewOK_fvar (by rw [hdd]; rfl)) k3
      have hfv' : denoteE s3.store fv = some (.fvar i (domP.instantiateList ws 0)) := by
        rw [hfv]; simp [denoteEView, denote_ext hdd p3.ext]
      obtain ⟨o, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨p4, ho⟩ := ih p3.ok (Core.InstLVec.push (hacc.ext (p2.ext.trans p3.ext)) hfv')
        (denote_ext hb (p2.ext.trans p3.ext)) k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvarsFGo]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvarsFGo (.fvar i (domP.instantiateList ws) :: ws) n
            bodyP (i + 1) = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' p4.ext, h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF — **the
one-pass opener, as a run**, answering con-leche's binder-at-a-time
`openPisAtFvars` (through con-leche's `openPisAtFvarsF_eq`), which is what
con-leche's `checkSumCtor` calls. -/
theorem openPisAtFvarsF_run {n i : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState}
    {r : Option (List EIdx × EIdx)} (hok : StateOK s₀)
    (hh : denoteE s₀.store h = some hP)
    (hrun : Arena.openPisAtFvarsF n h i s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvars n hP i) := by
  rw [← ConLeche.openPisAtFvarsF_eq]
  simp only [Arena.openPisAtFvarsF] at hrun
  obtain ⟨o, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, ho⟩ := openPisAtFvarsFGo_run n hok
    (show ExprOps.InstLVec s₀.store #[] [] from rfl) hh k1
  simp only [ConLeche.openPisAtFvarsF]
  cases o with
  | some q =>
    obtain ⟨fvs, e⟩ := q
    obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨p1, ?_⟩
    rw [hx]
    exact denoteOpen_some h1 h2
  | none =>
    have hn : ConLeche.openPisAtFvarsFGo [] n hP i = none := (Option.some.inj ho).symm
    rw [hn]
    obtain ⟨p2, h2⟩ := openPisAtFvars_run n p1.ok (denote_ext hh p1.ext) z1
    exact ⟨p1.trans p2, h2⟩

end ConRon.Bridge.Inductives
