/-
# `ConRon.Bridge.Core.Arms.InferIO` — Theorem 1 for `inferBodyIO`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1276-1404
inferBodyIO` — **the io grade** (con-leche's task #170/#172 B4).  The body is
`inferBody` with two clauses changed, and those two are the only lemmas that
differ from `Bridge/Core/Arms/Infer.lean`'s:

| clause | exit | lemma |
|---|---|---|
| `.lam` | **no domain-sort run** (official's `infer_lambda` at `infer_only`) | `inferIO_lam` |
| `.app` | **no argument check** (official's `infer_only`, con-leche's task #346) | the batched `inferSpineIO` |
| `.letE` | the body at its value, no check (con-leche's task #342 R-C) | `inferIO_letE` |

Everything else (`.sort`, `.fvar`, `.const`, the two literals, `.forallE`,
`.proj`, the throw) is `inferBody`'s, and the io lemmas for those clauses are
the same proofs at `inferTypeIO`.  The io slot is the io body at EVERY mode
(con-leche's task #346: the gate is gone), so nothing here is conditional on
the mode.

## The grade propagates through the RECORD, not through a flag

`inferBodyIO` recurses through `r.infer`, and the knot hands it
`CoreFns.ioView (coreKnot … fuel)` — the record whose `infer` slot is the io
slot.  So every `r.infer` below is `ConLeche.inferTypeIO mode env F`, which
is what the hypotheses say.  This is official's `infer_type_core` passing
`infer_only` down, without a textual twin.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.Core.Arms.Infer
import ConRon.Bridge.Core.Walks.FvarB
import ConRon.Bridge.ExprOps.Walks
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env}

/-! ## 1. The λ and `let` clauses -/

/-- con-leche: ConLeche/Kernel/Core.lean:1225-1234 inferBodyIO — the io λ
clause: no domain-sort run (official's `infer_lambda` skips it at
`infer_only`), the body's io type abstracted. -/
theorem inferIO_lam {F d : Nat} {ty body bt : Expr}
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lam ty body) =
      .ok (.forallE ty (bt.abstract1 d)) := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    hb, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1267-1270 inferBodyIO — the io
`let` clause, official `infer_let` at `infer_only`: the body at its value, no
check of the type or the value (con-leche's task #342 R-C). -/
theorem inferIO_letE {F d : Nat} {ty v b res : Expr}
    (hr : ConLeche.inferTypeIO mode env F d (b.instantiate1 v) = .ok res) :
    ConLeche.inferTypeIO mode env (F + 1) d (.letE ty v b) = .ok res := by
  rw [ConLeche.inferTypeIO_succ]
  exact hr

/-! ## 3. The body theorem -/


/-- con-leche: ConLeche/Kernel/Core.lean:1374-1399 inferBodyIO — the
projection at a **non-`Prop`** structure, at the io grade: `inferBody`'s
clause verbatim, with the subject's type read through the io slot. -/
theorem inferIO_proj_nonprop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.inferTypeIO mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : ¬ (Level.isEquiv entry.structSort .zero == some true)) :
    ConLeche.inferTypeIO mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, hpe, hw, hh, ht, bind, Except.bind]
  rw [ite_eq_left hg]
  simp only [ite_eq_right hp, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1374-1399 inferBodyIO — the
projection at a **`Prop`** structure, at the io grade. -/
theorem inferIO_proj_prop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.inferTypeIO mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : (Level.isEquiv entry.structSort .zero == some true))
    (hf : (Level.isEquiv
      (Level.subst entry.levelParams us entry.fieldSort) .zero
        == some true)) :
    ConLeche.inferTypeIO mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, hpe, hw, hh, ht, bind, Except.bind]
  rw [ite_eq_left hg]
  simp only [ite_eq_left hp, hf, pure, Except.pure]
  simp
/-! ### The leaf clauses at the io grade (task #97-P3-Core round 5)

`inferBodyIO`'s `.sort`/`.fvar`/`.const`/literal clauses are `inferBody`'s
verbatim, so at either value of the gate bit the io entry answers what
`Infer.lean`'s `infer_*` lemmas say.  Stated once here, at any mode. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1295 inferBodyIO — a sort's type is
the next sort, at the io grade. -/
theorem inferIO_sort {F d : Nat} {u : Level} :
    ConLeche.inferTypeIO mode env (F + 1) d (.sort u) =
      .ok (.sort (.succ u)) := by
  rw [ConLeche.inferTypeIO_succ]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1296-1298 inferBodyIO — the scope
check, at the io grade. -/
theorem inferIO_fvar {F d idx : Nat} {ty : Expr} (h : idx < d) :
    ConLeche.inferTypeIO mode env (F + 1) d (.fvar idx ty) = .ok ty := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, ite_eq_left h,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1299-1310 inferBodyIO — a stored
constant's type at its universe instantiation, at the io grade. -/
theorem inferIO_const {F d : Nat} {n : Name} {us : List Level}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (ht : ci.isTowerEntry = false)
    (hl : us.length = ci.toConstantVal.levelParams.length) :
    ConLeche.inferTypeIO mode env (F + 1) d (.const n us) =
      .ok (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, hf, ht, hl,
    bind, Except.bind, pure, Except.pure]
  simp

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1313 inferBodyIO — a `Nat`
literal types as `Nat`, at the io grade. -/
theorem inferIO_natLit {F d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lit (.natVal n)) =
      .ok (.const ConLeche.natName []) := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, h, ite_true,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1314-1317 inferBodyIO — a string
literal types as `String`, at the io grade. -/
theorem inferIO_strLit {F d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lit (.strVal s)) =
      .ok (.const ConLeche.stringName []) := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, h, ite_true,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1313 inferBodyIO — the `Nat`
literal clause as an answer, at the io grade (a `grind` lemma, task #123). -/
@[bridge_grind ←] theorem SimE.of_natLitIO {st : EStore} {r : EIdx} {d n : Nat}
    (hd : denoteE st r = some (.const ConLeche.natName []))
    (h : ConLeche.natLitSupported env = true) :
    SimE (ConLeche.inferTypeIO mode env) d (.lit (.natVal n)) st r :=
  ⟨_, hd, by unfold Expr.WScoped; trivial, 1, inferIO_natLit h⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1314-1317 inferBodyIO — the string
literal clause as an answer, at the io grade. -/
@[bridge_grind ←] theorem SimE.of_strLitIO {st : EStore} {r : EIdx} {d : Nat} {str : String}
    (hd : denoteE st r = some (.const ConLeche.stringName []))
    (h : ConLeche.strLitSupported env = true) :
    SimE (ConLeche.inferTypeIO mode env) d (.lit (.strVal str)) st r :=
  ⟨_, hd, by unfold Expr.WScoped; trivial, 1, inferIO_strLit h⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1299-1310 inferBodyIO — the constant
clause as an answer, at the io grade, at the denoted level list's length
(task #123: the twin's arity guard reads the level list's LENGTH word, which
`viewLen_of_denoteLs`, a `grind` rule, identifies; passed instantiated at the
constant, as `Infer.lean`'s `SimE.of_constTy`). -/
theorem SimE.of_constTyIO {st : EStore} {r : EIdx} {d : Nat} {n : Name}
    {ls : List Level} {c : ConstantInfo} (henv : ConLeche.EnvWF env)
    (hfind : env.find? n = some c) (hct : c.isTowerEntry = false)
    (hl : ls.length = c.toConstantVal.levelParams.length)
    (hd : denoteE st r = some (c.toConstantVal.type.instantiateLevelParams
      c.toConstantVal.levelParams ls)) :
    SimE (ConLeche.inferTypeIO mode env) d (.const n ls) st r :=
  ⟨_, hd, Expr.WScoped.of_not_hasFvar (const_ty_hasFvar henv hfind _), 1,
    inferIO_const hfind hct hl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1296-1298 inferBodyIO — the free
variable clause as an answer, at the io grade (task #123). -/
@[bridge_grind ←] theorem SimE.of_fvarIO {st : EStore} {r : EIdx} {d k : Nat} {t : Expr}
    (hk : k < d) (hd : denoteE st r = some t) (hw : Expr.WScoped d t) :
    SimE (ConLeche.inferTypeIO mode env) d (.fvar k t) st r :=
  ⟨_, hd, hw, 1, inferIO_fvar hk⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1318-1327 inferBodyIO — **the io
∀-formation rule**: `Infer.lean`'s `infer_forallE` with both inferences at
the io grade (the record `CoreFns.ioView` passes down). -/
theorem inferIO_forallE {F d : Nat} {ty body tty bt : Expr}
    {u v : Level} (hty : ConLeche.inferTypeIO mode env F d ty = .ok tty)
    (hw : ConLeche.whnf mode env F d tty = .ok (.sort u))
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : ConLeche.whnf mode env F (d + 1) bt = .ok (.sort v)) :
    ConLeche.inferTypeIO mode env (F + 1) d (.forallE ty body) =
      .ok (.sort (.imax u v)) := by
  rw [ConLeche.inferTypeIO_succ]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.ensureSort, ConLeche.whnf_def, hty, hw, hb, hv, bind, Except.bind,
    pure, Except.pure]

/-- con-leche: none — **a `pure` exit** at a pinned state (`Defeq.lean`'s
`triple_pure_post`, which this module does not import). -/
theorem triple_pure_lam {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => s = s₀⦄ (pure v : AM α) ⦃fun r s => Q r s; ⊤⦄ := by
  sym only [bridge_grind] => vcgen <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody — the λ
clause's result `.forallE ty (bt.abstract1 depth)`, the twin's
`inferLamResult`: `abstract1Fast` (over the Core tier's `fvarBSpec`,
`Walks/FvarB.lean`) then one intern. -/
theorem inferLamResult_spec {fe : IFEnv} (s₀ : AState) (ty bt : EIdx) (d : Nat)
    (et vbt : Expr) (hok : CheckOK mode env fe s₀)
    (hdt : denoteE s₀.store ty = some et) (hdb : denoteE s₀.store bt = some vbt) :
    ⦃fun s => s = s₀⦄ inferLamResult ty bt d
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (.forallE et (vbt.abstract1 d)); ⊤⦄ := by
  unfold inferLamResult
  refine triple_seq (ExprOps.abstract1Fast_spec fvarBSpec coreWalkFuel s₀ bt d 0
    hok.state (by rw [hdb]; rfl)) ?_
  rintro ab s1 ⟨hso1, hx1, hc1, hp1, _, hrel⟩
  have hok1 := hok.mono hso1 hx1 hc1 hp1
  have hdab : denoteE s1.store ab = some (vbt.abstract1 d 0) := hrel vbt hdb
  have hdt1 := denote_ext hdt hx1
  refine triple_mono (internForallEE_spec s1 ty ab hok1.state.wf
    (by rw [hdt1]; rfl) (by rw [hdab]; rfl)) ?_
  rintro r s2 ⟨hwf2, hx2, _, _, _, hc2, hp2, _, hd2⟩
  refine ⟨hok1.mono ⟨hwf2⟩ hx2 hc2 hp2, hx1.trans hx2, hp2.trans hp1, ?_⟩
  rw [hd2]
  simp [denoteEView, denote_ext hdt1 hx2, denote_ext hdab hx2]

/-- con-leche: ConLeche/Kernel/Core.lean:1101-1107 ensureSort — the twin's
`ensureSort` through the io record (`CoreFnsA.ioView`, whose `whnf` slot is
the knot's): the answer denotes the level a `whnf` of the subject reached. -/
theorem ensureSort_ioView_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (j : EIdx)
    (t : Expr) (hok : CheckOK mode env fe s₀)
    (hd : denoteE s₀.store j = some t) (hw : Expr.WScoped d t) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.ensureSort (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d j
    ⦃fun u s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ U, denoteL s'.store.ls u = some U ∧
          ∃ F, ConLeche.whnf mode env F d t = .ok (.sort U); ⊤⦄ := by
  unfold ConRon.Arena.ensureSort
  have hn : ⦃fun s => s = s₀⦄
      (CoreFnsA.ioView (coreKnot mode fe id fuel)).whnf d j
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnf mode env) d t s'.store r; ⊤⦄ :=
    hsim.whnf s₀ d j t hok hd hw
  refine triple_seq hn ?_
  rintro wr s1 ⟨hok1, hx1, hp1, W, hW, _, F, hF⟩
  obtain ⟨vw, hvw⟩ := denoteE_view hW
  refine tag_view_bind_triple hvw ?_
    (fun hne => by cases vw <;> first | rfl | exact absurd rfl hne)
  cases vw
  case sort u =>
    obtain ⟨U, rfl, hU⟩ := denote_sort_inv hok1.state.wf hvw hW
    exact triple_pure_lam ⟨hok1, hx1, hp1, U, hU, F, hF⟩
  all_goals exact triple_fail

/-! ### The dispatch's children (task #97-P3-Core round 5)

`inferBodyIO_spec` below is a case split on the tag: one child per group of
the twin's `view` dispatch.  The io lane keeps CHAINED binder clauses, so
`.forallE` and `.lam` are two children here where `Infer.lean` has one
batched one. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1350-1373 inferBodyIO — **the io
`.app` clause**: the batched `inferAppIOAt`/`inferSpineIO` (task #97-P6-9)
against the chained `inferIO_app_licensed`/`inferIO_app_cert`.
**CLOSED** (task #97-P3-Core round 6): `headAndArgs_app_spec`, the knot's
io slot at the head, the carry `inferSpineIO_go` (`Walks/InferSpine.lean`;
no argument is checked), then con-leche's `inferSpineIO_sound` and
`Expr.mkAppN_getApp`. -/
theorem inferBodyIO_app {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.app) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case app f a =>
    dsimp only
    unfold ConRon.Arena.inferAppIOAt
    -- stage 1: the spine's head and argument vector
    refine triple_seq (headAndArgs_app_spec s₀ i e hok.state hden
      (by simp [htag])) ?_
    rintro ⟨hd, args⟩ s1 ⟨hs1, hhd, hargs⟩
    subst s1
    dsimp only at hhd hargs ⊢
    -- stage 2: the head's io-grade type, once
    refine triple_seq (hsim.inferIO s₀ d hd e.getAppFn hok hhd
      (Expr.WScoped.getAppFn hw)) ?_
    rintro tf s2 ⟨hok2, hx2, hp2, th, hth, hwth, F1, hF1⟩
    -- stage 3: the batched io spine, then con-leche's identification
    refine triple_mono (inferSpineIO_go hsim d args _ tf #[] 0 s2 th []
      e.getAppArgs rfl hok2 hth (InstLVec.empty _)
      (by rw [ConLeche.Expr.instantiateList_nil]; exact hwth)
      (by rw [List.drop_zero]; exact denoteEList_ext hx2 _ _ hargs)
      (Expr.WScoped.getAppArgs hw)) ?_
    rintro r s3 ⟨hok3, hx3, hp3, v, hv, hwv, F2, hF2⟩
    refine ⟨hok3, hx2.trans hx3, hp3.trans hp2, v, hv, hwv, ?_⟩
    obtain ⟨F', hF'⟩ := ConLeche.inferSpineIO_sound e.getAppArgs e.getAppFn
      th v F1 F2 hF1 hF2
    rw [ConLeche.Expr.mkAppN_getApp] at hF'
    exact ⟨F', hF'⟩
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-! `inferBodyIO_app`: sorry-free (task #97-P3-Core round 6). -/
#print axioms inferBodyIO_app

/-- con-leche: ConLeche/Kernel/Core.lean:1318-1327 inferBodyIO — **the `.forallE`
clause**, chained: the domain's io type and its sort, the free variable,
`instantiate1Fast`, the codomain's io type and `ensureSort`, the `imax`;
pure side `inferIO_forallE`. -/
theorem inferBodyIO_forallE {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.forallE) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case forallE ty b =>
    obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hv hden
    have hwt : Expr.WScoped d et := by unfold Expr.WScoped at hw; exact hw.1
    have hwb : Expr.WScoped d eb := by unfold Expr.WScoped at hw; exact hw.2
    dsimp only
    -- the domain's io type, reduced to a sort
    refine triple_seq (hsim.inferIO s₀ d ty et hok hdt hwt) ?_
    rintro tty s1 ⟨hok1, hx1, hp1, T, hT, hwT, F1, hF1⟩
    refine triple_seq (hsim.whnf s1 d tty T hok1 hT hwT) ?_
    rintro hh s2 ⟨hok2, hx2, hp2, W, hW, _, F2, hF2⟩
    obtain ⟨vw, hvw⟩ := denoteE_view hW
    refine tag_view_bind_triple hvw ?_
      (fun hne => by cases vw <;> first | rfl | exact absurd rfl hne)
    cases vw
    case sort u =>
      obtain ⟨U1, rfl, hU1⟩ := denote_sort_inv hok2.state.wf hvw hW
      dsimp only
      have hx02 := hx1.trans hx2
      have hdt2 := denote_ext hdt hx02
      -- the free variable
      refine triple_seq (internE_spec s2 (.fvar d ty) hok2.state.wf
        (viewOK_fvar (by rw [hdt2]; rfl))) ?_
      rintro fv s3 ⟨hwf3, hx3, -, -, -, hc3, hp3, -, hd3⟩
      have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
      have hfv : denoteE s3.store fv = some (.fvar d et) := by
        rw [hd3]; simp [denoteEView, denote_ext hdt2 hx3]
      have hx03 := hx02.trans hx3
      -- the codomain, opened
      refine triple_seq (instantiate1Fast_ok_spec s3 b fv eb (.fvar d et) hok3
        (denote_ext hdb hx03) hfv) ?_
      rintro ob s4 ⟨hok4, hx4, hp4, hob⟩
      -- its io type, a sort
      refine triple_seq (hsim.inferIO s4 (d + 1) ob _ hok4 hob
        (Expr.WScoped.instantiate1 hwt 0 hwb)) ?_
      rintro bt s5 ⟨hok5, hx5, hp5, TB, hTB, hwTB, F3, hF3⟩
      refine triple_seq (ensureSort_ioView_spec hsim s5 (d + 1) bt TB hok5 hTB
        hwTB) ?_
      rintro v s6 ⟨hok6, hx6, hp6, U0, hU0, F4, hF4⟩
      have hx26 := hx3.trans (hx4.trans (hx5.trans hx6))
      have hU1' := denoteL_ext hU1 hx26
      -- the `imax`, and the sort node
      refine triple_seq (internLNode_spec s6 (.imax u v) hok6.state.wf
        ⟨fun c hc => by
          simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil,
            or_false] at hc
          rcases hc with rfl | rfl
          · exact lview_isSome_of_denote hU1'
          · exact lview_isSome_of_denote hU0,
         fun c hc => by simp [LNodeView.nchildren] at hc⟩) ?_
      rintro iu s7 ⟨hwf7, hx7, -, -, -, -, hc7, hp7, -, hd7⟩
      have hok7 := hok6.mono ⟨hwf7⟩ hx7 hc7 hp7
      have hl : denoteL s7.store.ls iu = some (.imax U1 U0) := by
        rw [hd7]
        simp [denoteLView, opt2, denoteL_ext hU1' hx7, denoteL_ext hU0 hx7]
      refine triple_mono (internE_spec s7 (.sort iu) hwf7
        (viewOK_sort (lview_isSome_of_denote hl))) ?_
      rintro r s8 ⟨hwf8, hx8, -, -, -, hc8, hp8, -, hd8⟩
      refine ⟨hok7.mono ⟨hwf8⟩ hx8 hc8 hp8,
        hx02.trans (hx26.trans (hx7.trans hx8)),
        by rw [hp8, hp7, hp6, hp5, hp4, hp3, hp2, hp1], .sort (.imax U1 U0),
        by rw [hd8]; simp [denoteEView, denoteL_ext hl hx8],
        by unfold Expr.WScoped; trivial, F1 + F2 + F3 + F4 + 1, ?_⟩
      exact inferIO_forallE
        (ConLeche.inferTypeIO_mono (by omega) hF1)
        (ConLeche.whnf_mono (by omega) hF2)
        (ConLeche.inferTypeIO_mono (by omega) hF3)
        (ConLeche.whnf_mono (by omega) hF4)
    all_goals (dsimp only; exact triple_fail)
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1328-1349 inferBodyIO — **the `.lam`
clause**, with no domain-sort run: `internE` of the free variable,
`instantiate1Fast_specE`, the io knot slot, then `inferLamResult_spec`, whose
`abstract1Fast` needs the Core tier's `fvarBSpec` (`Walks/FvarB.lean`); pure
side `inferIO_lam`. -/
theorem inferBodyIO_lam {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lam) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  unfold ConRon.Arena.inferBodyIO
  refine view_bind_triple hv ?_
  cases v
  case lam ty b =>
    obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hv hden
    have hwt : Expr.WScoped d et := by unfold Expr.WScoped at hw; exact hw.1
    have hwb : Expr.WScoped d eb := by unfold Expr.WScoped at hw; exact hw.2
    dsimp only
    -- stage 1: the free variable
    refine triple_seq (internE_spec s₀ (.fvar d ty) hwf
      (viewOK_fvar (by rw [hdt]; rfl))) ?_
    rintro fv s1 ⟨hwf1, hx1, _, _, _, hc1, hp1, _, hd1⟩
    have hok1 := hok.mono ⟨hwf1⟩ hx1 hc1 hp1
    have hfv : denoteE s1.store fv = some (.fvar d et) := by
      rw [hd1]; simp [denoteEView, denote_ext hdt hx1]
    -- stage 2: open the body
    refine triple_seq (instantiate1Fast_specE coreWalkFuel s1 b fv 0 hok1.state
      (by rw [hfv]; rfl) (by rw [denote_ext hdb hx1]; rfl)) ?_
    rintro ob s2 ⟨hso2, hx2, hc2, hp2, _, hia⟩
    have hok2 := hok1.mono hso2 hx2 hc2 hp2
    have hob : denoteE s2.store ob = some (eb.instantiate1 (.fvar d et) 0) :=
      hia _ hfv eb (denote_ext hdb hx1)
    have hwob : Expr.WScoped (d + 1) (eb.instantiate1 (.fvar d et) 0) :=
      Expr.WScoped.instantiate1 hwt 0 hwb
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    -- stage 3: the body's io type
    have hi3 : ⦃fun s => s = s2⦄
        (CoreFnsA.ioView (coreKnot mode fe id fuel)).infer (d + 1) ob
        ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s2.store s'.store ∧
          s'.pins = s2.pins ∧
          SimE (ConLeche.inferTypeIO mode env) (d + 1)
            (eb.instantiate1 (.fvar d et) 0) s'.store r; ⊤⦄ :=
      hsim.inferIO s2 (d + 1) ob _ hok2 hob hwob
    refine triple_seq hi3 ?_
    rintro bt s3 ⟨hok3, hx3, hp3, vbt, hvbt, hwvbt, F1, hF1⟩
    have hx03 : Ext s₀.store s3.store := hx02.trans hx3
    have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp1)
    have hwres : Expr.WScoped d (.forallE et (vbt.abstract1 d)) := by
      unfold Expr.WScoped; exact ⟨hwt, ConLeche.WScoped.abstract1 0 hwvbt⟩
    refine triple_mono (inferLamResult_spec s3 ty bt d et vbt hok3
      (denote_ext hdt hx03) hvbt) ?_
    rintro r s' ⟨hok', hx', hp', hd'⟩
    exact ⟨hok', hx03.trans hx', hp'.trans hp03, _, hd', hwres, F1 + 1,
      inferIO_lam hF1⟩
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

/-- con-leche: ConLeche/Kernel/Core.lean:1299-1310 inferBodyIO — **the `.const`
clause**, `inferBody`'s verbatim at the io grade.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBodyIO_const {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.const) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case const n us =>
    obtain ⟨nm, ls, rfl, hn, hus⟩ := denote_const_inv hwf hv hden
    dsimp only
    cases hf : fe.find? n with
    | none =>
      sym only [bridge_grind] =>
        vcgen [ConRon.Arena.unknownConstError, ConRon.Arena.pinSorryAx] <;> finish
    | some ci =>
      obtain ⟨nm', c, hn', hci, hfind⟩ := hok.ienv.hit n ci hf
      obtain rfl := Option.some.inj (hn.symm.trans hn')
      cases ht : ci.isTowerEntry
      · obtain ⟨hct, cv, hcv_eq, hcv⟩ := denoteCI_nonTower hci ht
        have hname : denoteN s₀.store.ns cv.name = some nm := by
          rw [denoteCV_name hcv]; exact congrArg some (env_find_name hfind)
        have hlp := denoteNList_len (denoteCV_inv hcv).2.1
        simp only [hcv_eq]
        -- the arity guard passed: con-leche's instantiated type
        sym only [bridge_grind, SimE.of_constTyIO (mode := mode) (d := d) henv hfind hct] =>
          vcgen [constTyAt_spec (mode := mode) (env := env) (fe := fe) s₀ cv us nm ls c
            hok hname hus hfind hcv] <;> finish
      · -- `vcgen` does not read the case hypothesis: the guard is rewritten
        -- first, and the failing branch then leaves no condition at all
        simp only [ht, ite_true]
        vcgen
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1317 inferBodyIO — **the two
literal clauses**, `inferBody`'s verbatim at the io grade.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBodyIO_lit {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    -- the pin's name is the basis constant's (`Infer.lean`'s `pinNames_nat`)
    cases l with
    | natVal n =>
      sym only [bridge_grind] =>
        vcgen [natLitSupported_spec (mode := mode) (env := env) (fe := fe) s₀ hok,
          ConRon.Arena.pinNat,
          constE_spec (mode := mode) (env := env) (fe := fe) (nm := ConLeche.natName)] <;>
          finish
    | strVal str =>
      sym only [bridge_grind] =>
        vcgen [strLitSupported_spec (mode := mode) (env := env) (fe := fe) s₀ hok,
          ConRon.Arena.pinString,
          constE_spec (mode := mode) (env := env) (fe := fe) (nm := ConLeche.stringName)] <;>
          finish
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1374-1399 inferBodyIO — **the `.proj`
clause**, `inferBody`'s verbatim at the io grade.

**CLOSED** (round 5), staged by `triple_seq` (`Memo.lean`): every
callee is applied at a subject whose denotation the previous stage NAMED,
and every callee rule it needs was already closed. -/
theorem inferBodyIO_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.proj) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  cases v
  case proj sn k pe =>
    obtain ⟨nm, es, rfl, hsn, hpe⟩ := denote_proj_inv hwf hv hden
    have hwes : Expr.WScoped d es := by simpa [Expr.WScoped] using hw
    refine view_bind_triple hv ?_
    dsimp only
    refine triple_mono (inferProj_spec henv
      (CoreFnsA.ioView (coreKnot mode fe id fuel)) (ConLeche.inferTypeIO mode env)
      hsim.inferIO hsim.whnf s₀ d sn k pe nm es hok hsn hpe hwes) ?_
    rintro r s' ⟨hok', hx', hp', v, hv', hwv, F1, F2, vt, vte, T, ls, p, hF1,
      hF2, hgf, hfp, hgP, hpr, rfl⟩
    refine ⟨hok', hx', hp', _, hv', hwv, max F1 F2 + 1, ?_⟩
    have hinf := ConLeche.inferTypeIO_mono (Nat.le_max_left F1 F2) hF1
    have hwhnf := ConLeche.whnf_mono (Nat.le_max_right F1 F2) hF2
    rcases hpr with hnp | ⟨hpp, hfield⟩
    · exact inferIO_proj_nonprop hinf hwhnf hgf hfp hgP (by simp [hnp])
    · exact inferIO_proj_prop hinf hwhnf hgf hfp hgP hpp hfield
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

#print axioms inferBodyIO_proj

/-- con-leche: ConLeche/Kernel/Core.lean:1267-1270 inferBodyIO — **the `let`
clause** at the io grade: the body at its value. -/
theorem inferBodyIO_letE {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : i.tag = ETag.letE) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case letE ty w b =>
    obtain ⟨et, ew, eb, rfl, _, hdw, hdb⟩ := denote_letE_inv hwf hv hden
    have hww : Expr.WScoped d ew := by unfold Expr.WScoped at hw; exact hw.2.1
    have hwb : Expr.WScoped d eb := by unfold Expr.WScoped at hw; exact hw.2.2
    dsimp only
    refine triple_seq (instantiate1Fast_ok_spec s₀ b w eb ew hok hdb hdw) ?_
    rintro ob s1 ⟨hok1, hx1, hp1, hdob⟩
    have hi : ⦃fun s => s = s1⦄
        (CoreFnsA.ioView (coreKnot mode fe id fuel)).infer d ob
        ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s1.store s'.store ∧
          s'.pins = s1.pins ∧
          SimE (ConLeche.inferTypeIO mode env) d (eb.instantiate1 ew)
            s'.store r; ⊤⦄ :=
      hsim.inferIO s1 d ob _ hok1 hdob (Expr.WScoped.instantiate1_gen hww 0 hwb)
    refine triple_mono hi ?_
    rintro r s' ⟨hok', hx', hp', R, hdR, hwR, F, hF⟩
    exact ⟨hok', hx1.trans hx', hp'.trans hp1, R, hdR, hwR, F + 1,
      inferIO_letE hF⟩
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

/-- con-leche: ConLeche/Kernel/Core.lean:1295-1298 inferBodyIO — **the leaf
clauses**: `.sort`, `.fvar`, and the throw.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem inferBodyIO_leaf {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnp : i.tag ≠ ETag.proj)
    (hnf : i.tag ≠ ETag.forallE) (hnm : i.tag ≠ ETag.lam)
    (hnc : i.tag ≠ ETag.const) (hnl : i.tag ≠ ETag.lit)
    (hnlet : i.tag ≠ ETag.letE) :
    ⦃fun s => s = s₀⦄
      inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | lit l => exact absurd htg hnl
  | const n us => exact absurd htg hnc
  | proj n k sub => exact absurd htg hnp
  | lam ty b => exact absurd htg hnm
  | forallE ty b => exact absurd htg hnf
  | letE ty w b => exact absurd htg hnlet
  | bvar k => vcgen
  | fvar k t =>
    obtain ⟨t', rfl, ht⟩ := denote_fvar_inv hwf hv hden
    have hk : k < d := by unfold Expr.WScoped at hw; exact hw.1
    have hwt : Expr.WScoped d t' := by
      unfold Expr.WScoped at hw; exact Expr.WScoped.mono (Nat.le_of_lt hk) hw.2
    sym only [bridge_grind] => vcgen <;> finish
  | sort u =>
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hv hden
    dsimp only
    refine triple_seq (internLNode_spec s₀ (.succ u) hwf
      ⟨fun c hc => by
        simp [LNodeView.lchildren] at hc; subst hc
        exact lview_isSome_of_denote hl,
       fun c hc => by simp [LNodeView.nchildren] at hc⟩) ?_
    rintro su s1 ⟨hwf1, hx1, -, -, -, -, hc1, hp1, -, hd1⟩
    have hs1 : denoteL s1.store.ls su = some (Level.succ l) := by
      rw [hd1]; simp [denoteLView, denoteL_ext hl hx1]
    refine triple_mono (internE_spec s1 (.sort su) hwf1
      (viewOK_sort (lview_isSome_of_denote hs1))) ?_
    rintro r s2 ⟨hwf2, hx2, -, -, -, hc2, hp2, -, hd2⟩
    refine ⟨hok.mono ⟨hwf2⟩ (hx1.trans hx2) (hc2.trans hc1) (hp2.trans hp1),
      hx1.trans hx2, hp2.trans hp1, .sort (.succ l), ?_,
      by unfold Expr.WScoped; trivial, 1, inferIO_sort⟩
    rw [hd2]; simp [denoteEView, denoteL_ext hs1 hx2]

/-- con-leche: ConLeche/Verify/Cached/DiscC5.lean inferBodyIOC_sim —
**THEOREM 1 for `inferBodyIO`**.

**CLOSED** (the Core tier is `sorry`-free since task #97-P3-Core round 6).
It was open for the same reasons as `inferBody_spec`:
the twin's io `.app` clause is the batched `inferSpineIO`/`inferAppIOAt`
(task #97-P6-9) and its `.proj` clause needs the same three callee rules.
The io lane keeps CHAINED binder clauses — con-leche's `inferBodyIOI` does
(task #97-P6-12's own note), so `infer_lam_open`/`_cod`/`_result` survive as
this lane's λ clause and the batched-telescope debt of `Infer.lean` does NOT
apply here. -/
theorem inferBodyIO_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe
      (inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe)
      (ConLeche.inferTypeIO mode env) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact inferBodyIO_app henv hμ hsim s₀ d i e hok hden hw ha
  by_cases hp : i.tag = ETag.proj
  · exact inferBodyIO_proj henv hμ hsim s₀ d i e hok hden hw hp
  by_cases hf : i.tag = ETag.forallE
  · exact inferBodyIO_forallE henv hμ hsim s₀ d i e hok hden hw hf
  by_cases hm : i.tag = ETag.lam
  · exact inferBodyIO_lam henv hμ hsim s₀ d i e hok hden hw hm
  by_cases hc : i.tag = ETag.const
  · exact inferBodyIO_const henv hμ hsim s₀ d i e hok hden hw hc
  by_cases hl : i.tag = ETag.lit
  · exact inferBodyIO_lit henv hμ hsim s₀ d i e hok hden hw hl
  by_cases hlt : i.tag = ETag.letE
  · exact inferBodyIO_letE hsim s₀ d i e hok hden hw hlt
  exact inferBodyIO_leaf henv hμ hsim s₀ d i e hok hden hw ha hp hf hm hc hl hlt

/-! ## The axiom census of the closed children (task #97-P3-Core round 5,
sub-lane Leaves) -/

section Census

#print axioms inferIO_sort
#print axioms inferIO_fvar
#print axioms inferIO_const
#print axioms inferIO_natLit
#print axioms inferIO_strLit
#print axioms inferBodyIO_const
#print axioms inferBodyIO_lit
#print axioms inferBodyIO_leaf
#print axioms inferIO_forallE
#print axioms inferBodyIO_forallE
end Census

/-! Lane `lam` (task #97-P3-Core round 6): the `.lam` clause, sorry-free. -/

section CensusLam
#print axioms inferLamResult_spec
#print axioms ensureSort_ioView_spec
#print axioms inferBodyIO_lam
end CensusLam

end ConRon.Bridge.Core
