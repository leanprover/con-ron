/-
# `ConRon.Bridge.Core.Arms.Infer` — Theorem 1 for `inferBody`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1057-1170
inferBody`.  Eleven SUCCESS exits over ten clauses; the failing exits need no
lemma, because a twin failure makes Theorem 1's partial-correctness postcondition vacuous and
a twin SUCCESS is what each success lemma is the licence for.

| clause | exit | lemma |
|---|---|---|
| `.sort u` | `Sort (u+1)` | `infer_sort` |
| `.fvar idx ty` | in scope | `infer_fvar` |
| `.const n us` | stored, not a tower entry, level arity matches | `infer_const` |
| `.lit (.natVal _)` | the `Nat` basis is installed | `infer_natLit` |
| `.lit (.strVal _)` | the `String` basis is installed | `infer_strLit` |
| `.forallE` | domain and codomain sorts | the batched `inferPis` (`Walks/BinderLoop.lean`) |
| `.lam` | the domain a type, the body's type | the batched `inferLams` (`Walks/BinderLoop.lean`) |
| `.app` | every argument checked against its domain | the batched `inferSpine` (`Walks/InferSpine.lean`) |
| `.proj` | the table entry, at a `Prop` and at a non-`Prop` structure | `infer_proj_prop`, `infer_proj_nonprop` |
| `.letE` | official `infer_let` (con-leche's task #342) | `infer_letE` |

## The deviations the twin carries at this body

1. **The binder-telescope loops** (DESIGN, task #97-P6-12): the twin's
   `.lam` and `.forallE` clauses are `inferLams`/`inferPis`, con-leche's own CACHED-tier
   `inferLamsI`/`inferPisI`, which peel and open the whole chain in one walk.
   The identification is con-leche's — `Verify/Cached/BinderLoopC.lean` and
   `Verify/BinderLoop.lean` — and what this library owes is the denotation
   carry, `inferBody_binders_batched` below (over `Walks/BinderLoop.lean`).
2. **The batched application spine** (DESIGN, task #97-P6-9):
   `inferSpine`/`inferApp` in place of the per-argument chain, identified by
   `Verify/BetaSpine.lean`'s `inferSpine_*` family
   (`inferBody_app_batched` below).
3. `env : Env` is `fe : IFEnv` throughout (DESIGN, task #97c, deviation 1),
   which `Bridge/StateOK.lean`'s `IFEnvOK` absorbs with no clause of its own here.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.InferSpine
import ConRon.Bridge.Core.Walks.BinderLoop
import ConRon.Bridge.Core.EnsureSort
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env}

/-! ## 1. The five leaf clauses -/

/-- con-leche: ConLeche/Kernel/Core.lean:1115 inferBody — a sort's type is the
next sort. -/
theorem infer_sort {F d : Nat} {u : Level} :
    ConLeche.inferTypeCore mode env (F + 1) d (.sort u) =
      .ok (.sort (.succ u)) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1116-1125 inferBody — a free
variable's type is the one its node carries (DESIGN §8.3, "Free variables":
this is what makes every handle-keyed cache sound). -/
theorem infer_fvar {F d idx : Nat} {ty : Expr} (h : idx < d) :
    ConLeche.inferTypeCore mode env (F + 1) d (.fvar idx ty) = .ok ty := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ite_eq_left h, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1126-1137 inferBody — a stored
constant's type at its universe instantiation. -/
theorem infer_const {F d : Nat} {n : Name} {us : List Level}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (ht : ci.isTowerEntry = false)
    (hl : us.length = ci.toConstantVal.levelParams.length) :
    ConLeche.inferTypeCore mode env (F + 1) d (.const n us) =
      .ok (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, hf, ht, hl, bind, Except.bind, pure,
    Except.pure]
  simp

/-- con-leche: ConLeche/Kernel/Core.lean:1138-1140 inferBody — a `Nat`
literal types as `Nat`, once the basis declarations are pinned. -/
theorem infer_natLit {F d n : Nat} (h : ConLeche.natLitSupported env = true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.lit (.natVal n)) =
      .ok (.const ConLeche.natName []) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, h, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1141-1147 inferBody — a string
literal types as `String`. -/
theorem infer_strLit {F d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    ConLeche.inferTypeCore mode env (F + 1) d (.lit (.strVal s)) =
      .ok (.const ConLeche.stringName []) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, h, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1138-1140 inferBody — the `Nat`
literal clause as an answer (a `grind` lemma: its conclusion is its
pattern). -/
@[bridge_grind ←] theorem SimE.of_natLit {st : EStore} {r : EIdx} {d n : Nat}
    (hd : denoteE st r = some (.const ConLeche.natName []))
    (h : ConLeche.natLitSupported env = true) :
    SimE (ConLeche.inferTypeCore mode env) d (.lit (.natVal n)) st r :=
  ⟨_, hd, by unfold Expr.WScoped; trivial, 1, infer_natLit h⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1141-1147 inferBody — the string
literal clause as an answer. -/
@[bridge_grind ←] theorem SimE.of_strLit {st : EStore} {r : EIdx} {d : Nat} {str : String}
    (hd : denoteE st r = some (.const ConLeche.stringName []))
    (h : ConLeche.strLitSupported env = true) :
    SimE (ConLeche.inferTypeCore mode env) d (.lit (.strVal str)) st r :=
  ⟨_, hd, by unfold Expr.WScoped; trivial, 1, infer_strLit h⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1126-1137 inferBody — the constant
clause as an answer, at the denoted level list's length (the
twin's arity guard on the level list's VIEW reaches it through
`Core/Walks/Spine.lean`'s `lsLenAt`; the constant is not in the
conclusion, so the arm passes this lemma instantiated at it). -/
theorem SimE.of_constTy {st : EStore} {r : EIdx} {d : Nat} {n : Name}
    {ls : List Level} {c : ConstantInfo} (henv : ConLeche.EnvWF env)
    (hfind : env.find? n = some c) (hct : c.isTowerEntry = false)
    (hl : ls.length = c.toConstantVal.levelParams.length)
    (hd : denoteE st r = some (c.toConstantVal.type.instantiateLevelParams
      c.toConstantVal.levelParams ls)) :
    SimE (ConLeche.inferTypeCore mode env) d (.const n ls) st r :=
  ⟨_, hd, Expr.WScoped.of_not_hasFvar (const_ty_hasFvar henv hfind _), 1,
    infer_const hfind hct hl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1116-1125 inferBody — the free
variable clause as an answer. -/
@[bridge_grind ←] theorem SimE.of_fvar {st : EStore} {r : EIdx} {d k : Nat} {t : Expr}
    (hk : k < d) (hd : denoteE st r = some t) (hw : Expr.WScoped d t) :
    SimE (ConLeche.inferTypeCore mode env) d (.fvar k t) st r :=
  ⟨_, hd, hw, 1, infer_fvar hk⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1166-1171 inferBody — **the `let`
clause**, official `infer_let` (con-leche's task #342 S0): the type is a
type, the value's type is the type, then the body at the value. -/
theorem infer_letE {F d : Nat} {ty v b tty tv res : Expr} {u : Level}
    (htty : ConLeche.inferTypeCore mode env F d ty = .ok tty)
    (hs : ConLeche.ensureSortCore mode env F d tty = .ok u)
    (htv : ConLeche.inferTypeCore mode env F d v = .ok tv)
    (hde : ConLeche.isDefEqCore mode env F d tv ty = .ok true)
    (hr : ConLeche.inferTypeCore mode env F d (b.instantiate1 v) = .ok res) :
    ConLeche.inferTypeCore mode env (F + 1) d (.letE ty v b) = .ok res := by
  have e1 : (ConLeche.pureFns mode env F).infer d ty = .ok tty := htty
  have e2 : ConLeche.ensureSort (ConLeche.pureFns mode env F) env d tty = .ok u := hs
  have e3 : (ConLeche.pureFns mode env F).infer d v = .ok tv := htv
  have e4 : (ConLeche.pureFns mode env F).defeq d tv ty = .ok true := hde
  have e5 : (ConLeche.pureFns mode env F).infer d (b.instantiate1 v) = .ok res := hr
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, e1, e2, e3, e4, e5, bind, Except.bind]
  rfl


/-! ## 4. The projection clause

Two success exits, and the guard that separates them is con-leche's task #175
W4c/O4 fence: at a `Prop`-declared structure the field's sort must itself be
`Prop` at this instantiation. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1229-1262 inferBody — the
projection at a **non-`Prop`** structure: the fence does not apply. -/
theorem infer_proj_nonprop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.inferTypeCore mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : ¬ (Level.isEquiv entry.structSort .zero == some true)) :
    ConLeche.inferTypeCore mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    hpe, hw, hh, ht, bind, Except.bind]
  rw [ite_eq_left hg]
  simp only [ite_eq_right hp, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1248-1259 inferBody — the projection
at a **`Prop`** structure, where the field's own sort must be `Prop` too. -/
theorem infer_proj_prop {F d i : Nat} {sn T : Name} {pe te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.inferTypeCore mode env F d pe = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hg : T = sn ∧ te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length)
    (hp : (Level.isEquiv entry.structSort .zero == some true))
    (hf : (Level.isEquiv
      (Level.subst entry.levelParams us entry.fieldSort) .zero
        == some true)) :
    ConLeche.inferTypeCore mode env (F + 1) d (.proj sn i pe) =
      .ok (entry.typeAt us te.getAppArgs pe) := by
  rw [ConLeche.inferTypeCore_succ]
  simp only [ConLeche.inferBody, ConLeche.infer_def, ConLeche.whnf_def,
    hpe, hw, hh, ht, bind, Except.bind]
  rw [ite_eq_left hg]
  simp only [ite_eq_left hp, hf, pure, Except.pure]
  simp

/-! ## 5. The two batched clauses' identification, and the body theorem -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1288-1373 inferSpine_* —
the twin's `.app` clause is `inferSpine`/`inferApp`, con-leche's own
cached-tier clause, against the chained `infer_app` above.  Staged: `headAndArgs_app_spec`, the
knot's `infer` at the head, the carry `inferSpine_go`
(`Walks/InferSpine.lean`), then con-leche's own identification
`inferSpine_sound` and `Expr.mkAppN_getApp`. -/
theorem inferBody_app_batched {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : (i.tag == ETag.app) = true) :
    ⦃fun s => s = s₀⦄ inferApp (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  unfold ConRon.Arena.inferApp
  -- stage 1: the spine's head and argument vector
  refine triple_seq (headAndArgs_app_spec s₀ i e hok.state hden htag) ?_
  rintro ⟨hd, args⟩ s1 ⟨hs1, hhd, hargs⟩
  subst s1
  dsimp only at hhd hargs ⊢
  -- stage 2: the head's type, once
  refine triple_seq (hsim.infer s₀ d hd e.getAppFn hok hhd
    (Expr.WScoped.getAppFn hw)) ?_
  rintro tf s2 ⟨hok2, hx2, hp2, th, hth, hwth, F1, hF1⟩
  -- stage 3: the batched spine, then con-leche's identification
  refine triple_mono (inferSpine_go hsim d args _ tf #[] 0 s2 th []
    e.getAppArgs rfl hok2 hth (InstLVec.empty _)
    (by rw [ConLeche.Expr.instantiateList_nil]; exact hwth)
    (by rw [List.drop_zero]; exact denoteEList_ext hx2 _ _ hargs)
    (Expr.WScoped.getAppArgs hw)) ?_
  rintro r s3 ⟨hok3, hx3, hp3, v, hv, hwv, F2, hF2⟩
  refine ⟨hok3, hx2.trans hx3, hp3.trans hp2, v, hv, hwv, ?_⟩
  obtain ⟨F', hF'⟩ := ConLeche.inferSpine_sound e.getAppArgs e.getAppFn th v
    F1 F2 hF1 hF2
  rw [ConLeche.Expr.mkAppN_getApp] at hF'
  exact ⟨F', hF'⟩

#print axioms inferBody_app_batched

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:595/790
inferLamsC_tail_sim / inferPisC_tail_sim — the twin's `.lam`/`.forallE`
clauses are `inferLams`/`inferPis`, con-leche's own cached-tier telescope
loops, against the chained `infer_lam_*`/`infer_forallE` above: the carries are `Walks/BinderLoop.lean`'s `inferLam_spec` and
`inferForall_spec`, over con-leche's `inferLams_sound`/`inferPis_sound`. -/
theorem inferBody_binders_batched {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : ETag.isBind i.tag = true) :
    ⦃fun s => s = s₀⦄
      inferBody (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case forallE ty b =>
    obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hv hden
    exact inferForall_spec henv hsim s₀ d ty b et eb hok hdt hdb hw
  case lam ty b =>
    obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hv hden
    exact inferLam_spec henv hsim s₀ d ty b et eb hok hdt hdb hw
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))


/-! ### The dispatch's children

`inferBody_spec` below is a case split on the tag and nothing else: one
child per group of the twin's `view` dispatch, each a triple at the same
body under its tag hypothesis.  The two batched clauses above are two of
them (`inferBody_app` reaches `inferBody_app_batched` through the dispatch);
the other four are here. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1216-1228 inferBody — **the `.app`
clause**, at the body: the dispatch hands the node to `inferApp`, whose
carry is `inferBody_app_batched`. -/
theorem inferBody_app {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.app) :
    ⦃fun s => s = s₀⦄
      inferBody (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case app f a =>
    exact inferBody_app_batched henv hsim s₀ d i e hok hden hw (by simp [htag])
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1126-1137 inferBody — **the `.const`
clause**: the index lookup, the tower-entry and level-arity guards, and the
stored type through `constTyAt` (`Walks/Cached.lean`'s `constTyAt_spec`);
pure side `infer_const`. -/
theorem inferBody_const {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.const) :
    ⦃fun s => s = s₀⦄
      inferBody (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
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
        sym only [bridge_grind, SimE.of_constTy (mode := mode) (d := d) henv hfind hct] =>
          vcgen [constTyAt_spec (mode := mode) (env := env) (fe := fe) s₀ cv us nm ls c
            hok hname hus hfind hcv] <;> finish
      · -- `vcgen` does not read the case hypothesis: the guard is rewritten
        -- first, and the failing branch then leaves no condition at all
        simp only [ht, ite_true]
        vcgen
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1138-1147 inferBody — **the two
literal clauses**: `natLitSupported_spec` (`Walks/Nat.lean`) and
`strLitSupported_spec` (`Walks/StrLit.lean`), then `constE_spec`; pure side
`infer_natLit`/`infer_strLit`. -/
theorem inferBody_lit {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => s = s₀⦄
      inferBody (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    -- the pin's name is the basis constant's (`Bridge/Grind.lean`'s `pinNames_eq_natName`/`_stringName`)
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

/-! ### The `.proj` clause, shared with the io body

The twin's `.proj` clause is `inferProj`, which `inferBody` and `inferBodyIO`
both call; the two differ only in the record's `infer` slot.  So the walk is
proved once, over ANY record whose `infer` slot denotes some pure inference
`inf` and whose `whnf` slot denotes `whnf`, and it answers the FACTS the pure
clause reads; `inferBody_proj` and `Arms/InferIO.lean`'s `inferBodyIO_proj`
close with their own `infer_proj_*` lemma. -/

/-- con-leche: none — a run that cannot answer: `fail`. -/
theorem fail_noOk {α : Type} (e : ConRon.Arena.CheckError) (s : AState)
    (r : α) (s' : AState) : (fail e : AM α) s ≠ .ok (r, s') := by
  intro h; cases h

/-- con-leche: none — a run whose continuation cannot answer cannot answer. -/
theorem bind_noOk {α β : Type} {x : AM α} {f : α → AM β}
    (h : ∀ a s r s', f a s ≠ .ok (r, s')) :
    ∀ s₀ r s', (x >>= f) s₀ ≠ .ok (r, s') := by
  intro s₀ r s' hx
  change (x s₀ >>= fun p => f p.1 p.2) = _ at hx
  cases hxs : x s₀ with
  | error e => rw [hxs] at hx; cases hx
  | ok p => rw [hxs] at hx; exact h p.1 p.2 r s' hx

/-- con-leche: none — a run that cannot answer satisfies every
partial-correctness postcondition. -/
theorem triple_of_noOk {α : Type} {x : AM α} {s₀ : AState}
    {Q : α → AState → Prop} (h : ∀ r s', x s₀ ≠ .ok (r, s')) :
    ⦃fun s => s = s₀⦄ x ⦃fun r s' => Q r s'; ⊤⦄ :=
  AM.triple_of_run_at fun r s' hx => absurd hx (h r s')

/-- con-leche: ConLeche/Kernel/Core.lean:1127-1162 inferBody — **the twin's
`inferProj`**, at a record whose two slots denote `inf` and `whnf`: the
answer is the table entry's type at the subject type's arguments, and the
facts the pure clause reads hold at some fuels. -/
theorem inferProj_spec {fe : IFEnv} (henv : ConLeche.EnvWF env)
    (r : CoreFnsA) (inf : Nat → Nat → Expr → CheckM Expr)
    (hinf : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
      CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
      Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ r.infer d i
      ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ SimE inf d e s'.store x; ⊤⦄)
    (hwh : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
      CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
      Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ r.whnf d i
      ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ SimE (ConLeche.whnf mode env) d e s'.store x; ⊤⦄)
    (s₀ : AState) (d : Nat) (sn : NIdx) (k : Nat) (pe : EIdx)
    (nm : Name) (es : Expr) (hok : CheckOK mode env fe s₀)
    (hsn : denoteN s₀.store.ns sn = some nm)
    (hpe : denoteE s₀.store pe = some es) (hwes : Expr.WScoped d es) :
    ⦃fun s => s = s₀⦄ inferProj r fe d sn k pe
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store x = some v ∧
        Expr.WScoped d v ∧
        ∃ F1 F2 vt vte T ls p, inf F1 d es = .ok vt ∧
          ConLeche.whnf mode env F2 d vt = .ok vte ∧
          vte.getAppFn = .const T ls ∧ env.findProj? T k = some p ∧
          (T = nm ∧ vte.getAppArgs.length = p.numParams ∧
            ls.length = p.levelParams.length) ∧
          ((Level.isEquiv p.structSort .zero == some true) = false ∨
            ((Level.isEquiv p.structSort .zero == some true) = true ∧
             (Level.isEquiv (Level.subst p.levelParams ls p.fieldSort) .zero
                == some true) = true)) ∧
          v = p.typeAt ls vte.getAppArgs es; ⊤⦄ := by
  unfold ConRon.Arena.inferProj
  -- stage 1: the subject's type
  refine triple_seq (hinf s₀ d pe es hok hpe hwes) ?_
  rintro t1 s1 ⟨hok1, hx1, hp1, vt, hvt, hwvt, F1, hF1⟩
  -- stage 2: its head normal form
  refine triple_seq (hwh s1 d t1 vt hok1 hvt hwvt) ?_
  rintro te s2 ⟨hok2, hx2, hp2, vte, hvte, hwvte, F2, hF2⟩
  have hx02 : Ext s₀.store s2.store := hx1.trans hx2
  have hp02 : s2.pins = s₀.pins := hp2.trans hp1
  have hwf2 := hok2.state.wf
  -- stage 3: its head
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s2 te hok2.state
    (by rw [hvte]; rfl)) ?_
  rintro hd s3 ⟨hs3, hrelF⟩
  subst s3
  have hdd : denoteE s2.store hd = some vte.getAppFn := hrelF vte hvte
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple_else hvh ?_ (fun _ => triple_fail)
  cases vh
  case const T us =>
    obtain ⟨Tn, ls, hgf, hTn, hus⟩ := denote_const_inv hwf2 hvh hdd
    dsimp only
    -- stage 4: the table
    refine triple_seq (IFEnv.findProj?_spec s2 T k Tn hok2 hTn) ?_
    rintro oe s4 ⟨hok4, hx4, _hm4, _hc4, hp4, hsome, _hnone⟩
    cases oe with
    | none =>
      dsimp only
      exact triple_of_noOk (bind_noOk (fun _ s r s' => bind_noOk
        (fun _ s r s' => fail_noOk _ s r s') s r s') _)
    | some entry =>
      obtain ⟨p, hpd, hfp⟩ := hsome entry rfl
      dsimp only
      have hvte4 := denote_ext hvte hx4
      have hx04 : Ext s₀.store s4.store := hx02.trans hx4
      have hp04 : s4.pins = s₀.pins := hp4.trans hp02
      -- stage 5: the type's arguments
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s4 te
        hok4.state (by rw [hvte4]; rfl)) ?_
      rintro targs s5 ⟨hs5, hrelA⟩
      subst s5
      have hargs : Frontend.denoteEList s4.store targs = some vte.getAppArgs :=
        hrelA vte hvte4
      have hus4 := denoteLs_ext hus hx4
      obtain ⟨_hsnp, hlps, _hctor, _hbody, hfs, hss, _hidx, hnp, _hnf, _hoff⟩ :=
        denoteProjEntry_inv hpd
      split
      next => exact triple_fail
      next hT0 =>
      split
      next => exact triple_fail
      next hlenA0 =>
      have hT : T = sn := by simpa using hT0
      have hlenA : targs.length = entry.numParams := by simpa using hlenA0
      -- stage 6: the level list's length
      refine triple_seq (viewLsLen_spec s4 us) ?_
      rintro ol s6 ⟨hs6, hol⟩
      subst s6
      rw [viewLen_of_denoteLs hus4] at hol
      subst hol
      dsimp only
      split
      next hlenL =>
        have hTnm : Tn = nm := by
          have h1 := denoteN_ext hsn (hx02.trans hx4)
          have h2 := denoteN_ext hTn hx4
          rw [hT] at h2
          exact Option.some.inj (h2.symm.trans h1)
        have hlen' : vte.getAppArgs.length = p.numParams := by
          rw [denoteEList_len hargs, hlenA, hnp]
        have hlenL' : ls.length = p.levelParams.length := by
          rw [hlenL, denoteNList_len hlps]
        have hgP : Tn = nm ∧ vte.getAppArgs.length = p.numParams ∧
            ls.length = p.levelParams.length := ⟨hTnm, hlen', hlenL'⟩
        have hwty : Expr.WScoped d (p.typeAt ls vte.getAppArgs es) :=
          ConLeche.projEntry_typeAt_WScoped henv hfp ls hlen'
            (Expr.WScoped.getAppArgs hwvte) hwes
        -- the answer, at any state the fence leaves behind
        have hfin : ∀ (s : AState), CheckOK mode env fe s →
            s.store = s4.store → s.pins = s₀.pins →
            ((Level.isEquiv p.structSort .zero == some true) = false ∨
              ((Level.isEquiv p.structSort .zero == some true) = true ∧
               (Level.isEquiv (Level.subst p.levelParams ls p.fieldSort) .zero
                  == some true) = true)) →
            ⦃fun s' => s' = s⦄ entry.typeAt us targs pe
            ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
                s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store x = some v ∧
                Expr.WScoped d v ∧
                ∃ F1 F2 vt vte T ls p, inf F1 d es = .ok vt ∧
                  ConLeche.whnf mode env F2 d vt = .ok vte ∧
                  vte.getAppFn = .const T ls ∧ env.findProj? T k = some p ∧
                  (T = nm ∧ vte.getAppArgs.length = p.numParams ∧
                    ls.length = p.levelParams.length) ∧
                  ((Level.isEquiv p.structSort .zero == some true) = false ∨
                    ((Level.isEquiv p.structSort .zero == some true) = true ∧
                     (Level.isEquiv (Level.subst p.levelParams ls p.fieldSort)
                        .zero == some true) = true)) ∧
                  v = p.typeAt ls vte.getAppArgs es; ⊤⦄ := by
          intro s hs hst hps hpr
          refine triple_mono (IProjEntry.typeAt_spec s entry us targs pe p ls
            vte.getAppArgs es hs (by rw [hst]; exact hpd)
            (by rw [hst]; exact hus4) (by rw [hst]; exact hargs)
            (by rw [hst]; exact denote_ext hpe hx04)) ?_
          rintro x s' ⟨hok', hx', hp', hd'⟩
          exact ⟨hok', by rw [hst] at hx'; exact hx04.trans hx',
            hp'.trans hps, _, hd', hwty, F1, F2, vt, vte, Tn, ls, p, hF1, hF2,
            hgf, hfp, hgP, hpr, rfl⟩
        -- stage 7: the possibly-`Prop` fence
        refine triple_seq (pinZeroLevel_spec s4 hok4.pins) ?_
        rintro z s7 ⟨hs7, hz⟩
        subst s7
        refine triple_seq (lvlEq?_spec s4 entry.structSort z hok4) ?_
        rintro rq s8 ⟨hok8, hst8, hp8, lu, lv, hlu, hlv, hrq⟩
        rw [hss] at hlu
        rw [hz] at hlv
        obtain rfl : lu = p.structSort := (Option.some.inj hlu).symm
        obtain rfl : lv = Level.zero := (Option.some.inj hlv).symm
        subst hrq
        split
        next hprop =>
          -- a `Prop` structure: the field's sort must be `Prop` too
          refine triple_seq (readNamesM_spec s8 entry.levelParams
            hok8.caches.readN) ?_
          rintro ks s9 ⟨hst9, hm9, hp9, hc9, hks, hN9⟩
          have hok9 := CheckOK.ofReadbackFrame hok8
            (ReadbackFrame.ofReadN hst9 hm9 hp9 hc9 hN9)
          refine triple_seq (readLevelsM_spec s9 us hok9.caches.readLs) ?_
          rintro vs s10 ⟨hst10, hm10, hp10, hc10, hvs, hLs10⟩
          have hok10 := CheckOK.ofReadbackFrame hok9
            (ReadbackFrame.ofReadLs hst10 hm10 hp10 hc10 hLs10)
          refine triple_seq (readLevelM_spec s10 entry.fieldSort
            hok10.caches.readL) ?_
          rintro fs s11 ⟨hst11, hm11, hp11, hc11, hfs11, hL11⟩
          have hok11 := CheckOK.ofReadbackFrame hok10
            (ReadbackFrame.ofReadL hst11 hm11 hp11 hc11 hL11)
          have hst411 : s11.store = s4.store :=
            hst11.trans (hst10.trans (hst9.trans hst8))
          rw [hst8, hlps] at hks
          rw [hst9, hst8, hus4] at hvs
          rw [hst10, hst9, hst8, hfs] at hfs11
          obtain rfl : ks = p.levelParams := (Option.some.inj hks).symm
          obtain rfl : vs = ls := (Option.some.inj hvs).symm
          obtain rfl : fs = p.fieldSort := (Option.some.inj hfs11).symm
          split
          next => exact triple_fail
          next hfield =>
            exact hfin s11 hok11 hst411
              (hp11.trans (hp10.trans (hp9.trans (hp8.trans hp04))))
              (Or.inr ⟨by simpa using hprop, by simpa using hfield⟩)
        next hprop =>
          exact hfin s8 hok8 hst8 (hp8.trans hp04)
            (Or.inl (by simpa using hprop))
      next => exact triple_fail
  all_goals (dsimp only; exact triple_fail)

/-- con-leche: ConLeche/Kernel/Core.lean:1127-1162 inferBody — **the `.proj`
clause**: `inferProj_spec` at the knot, then `infer_proj_prop`/
`infer_proj_nonprop`. -/
theorem inferBody_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.proj) :
    ⦃fun s => s = s₀⦄
      inferBody (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  cases v
  case proj sn k pe =>
    obtain ⟨nm, es, rfl, hsn, hpe⟩ := denote_proj_inv hwf hv hden
    have hwes : Expr.WScoped d es := by simpa [Expr.WScoped] using hw
    refine view_bind_triple hv ?_
    dsimp only
    refine triple_mono (inferProj_spec henv _ (ConLeche.inferTypeCore mode env)
      hsim.infer hsim.whnf s₀ d sn k pe nm es hok hsn hpe hwes) ?_
    rintro r s' ⟨hok', hx', hp', v, hv', hwv, F1, F2, vt, vte, T, ls, p, hF1,
      hF2, hgf, hfp, hgP, hpr, rfl⟩
    refine ⟨hok', hx', hp', _, hv', hwv, max F1 F2 + 1, ?_⟩
    have hinf := ConLeche.inferTypeCore_mono (Nat.le_max_left F1 F2) hF1
    have hwhnf := ConLeche.whnf_mono (Nat.le_max_right F1 F2) hF2
    rcases hpr with hnp | ⟨hpp, hfield⟩
    · exact infer_proj_nonprop hinf hwhnf hgf hfp hgP (by simp [hnp])
    · exact infer_proj_prop hinf hwhnf hgf hfp hgP hpp hfield
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

#print axioms inferProj_spec
#print axioms inferBody_proj

/-- con-leche: ConLeche/Kernel/Core.lean:1166-1171 inferBody — **the `let`
clause** (official `infer_let`, con-leche's task #342 S0): the type's type is
a sort, the value's type is the type, then the body at the value. -/
theorem inferBody_letE {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : i.tag = ETag.letE) :
    ⦃fun s => s = s₀⦄
      inferBody (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case letE ty w b =>
    obtain ⟨et, ew, eb, rfl, hdt, hdw, hdb⟩ := denote_letE_inv hwf hv hden
    have hwt : Expr.WScoped d et := by unfold Expr.WScoped at hw; exact hw.1
    have hww : Expr.WScoped d ew := by unfold Expr.WScoped at hw; exact hw.2.1
    have hwb : Expr.WScoped d eb := by unfold Expr.WScoped at hw; exact hw.2.2
    dsimp only
    -- the type's type
    refine triple_seq (hsim.infer s₀ d ty et hok hdt hwt) ?_
    rintro tty s1 ⟨hok1, hx1, hp1, Tty, hdtty, hwtty, F1, hF1⟩
    -- is a sort
    refine triple_seq (ensureSortK_spec hsim s1 d tty Tty hok1 hdtty hwtty) ?_
    rintro u s2 ⟨hok2, hx2, hp2, U, _, F2, hF2'⟩
    have hF2 := ensureSortCore_of_whnf hF2'
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    -- the value's type
    refine triple_seq (hsim.infer s2 d w ew hok2 (denote_ext hdw hx02) hww) ?_
    rintro tv s3 ⟨hok3, hx3, hp3, Tv, hdtv, hwtv, F3, hF3⟩
    have hx03 : Ext s₀.store s3.store := hx02.trans hx3
    -- against the type
    refine triple_seq (hsim.defeq s3 d tv ty Tv et hok3 hdtv
      (denote_ext hdt hx03) hwtv hwt) ?_
    rintro ok s4 ⟨hok4, hx4, hp4, F4, hF4⟩
    have hx04 : Ext s₀.store s4.store := hx03.trans hx4
    cases ok with
    | false => exact triple_fail
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      -- the body at the value
      refine triple_seq (instantiate1Fast_ok_spec s4 b w eb ew hok4
        (denote_ext hdb hx04) (denote_ext hdw hx04)) ?_
      rintro ob s5 ⟨hok5, hx5, hp5, hdob⟩
      have hx05 : Ext s₀.store s5.store := hx04.trans hx5
      refine triple_mono (hsim.infer s5 d ob (eb.instantiate1 ew) hok5 hdob
        (Expr.WScoped.instantiate1_gen hww 0 hwb)) ?_
      rintro r s6 ⟨hok6, hx6, hp6, R, hdR, hwR, F5, hF5⟩
      refine ⟨hok6, hx05.trans hx6,
        by rw [hp6, hp5, hp4, hp3, hp2, hp1], R, hdR, hwR,
        max F1 (max F2 (max F3 (max F4 F5))) + 1, ?_⟩
      exact infer_letE
        (ConLeche.inferTypeCore_mono (by omega) hF1)
        (ConLeche.ensureSortCore_mono (by omega) hF2)
        (ConLeche.inferTypeCore_mono (by omega) hF3)
        (ConLeche.isDefEqCore_mono (by omega) hF4)
        (ConLeche.inferTypeCore_mono (by omega) hF5)
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

/-- con-leche: ConLeche/Kernel/Core.lean:1115-1125 inferBody — **the leaf
clauses**: `.sort` (one level intern and one node intern), `.fvar` (the
scope check), and the throw (`.bvar`). -/
theorem inferBody_leaf {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnp : i.tag ≠ ETag.proj)
    (hnb : ETag.isBind i.tag = false) (hnc : i.tag ≠ ETag.const)
    (hnl : i.tag ≠ ETag.lit) (hnlet : i.tag ≠ ETag.letE) :
    ⦃fun s => s = s₀⦄
      inferBody (coreKnot mode fe id fuel) fe d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | lit l => exact absurd htg hnl
  | const n us => exact absurd htg hnc
  | proj n k sub => exact absurd htg hnp
  | lam ty b =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
  | forallE ty b =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
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
      by unfold Expr.WScoped; trivial, 1, infer_sort⟩
    rw [hd2]; simp [denoteEView, denoteL_ext hs1 hx2]

/-- con-leche: ConLeche/Verify/Cached/DiscC5.lean inferBodyC_sim — **THEOREM 1
for `inferBody`**: a case split on the tag, one dispatch child per arm. -/
theorem inferBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe (inferBody (coreKnot mode fe id fuel) fe)
      (ConLeche.inferTypeCore mode env) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact inferBody_app henv hμ hsim s₀ d i e hok hden hw ha
  by_cases hp : i.tag = ETag.proj
  · exact inferBody_proj henv hμ hsim s₀ d i e hok hden hw hp
  by_cases hb : ETag.isBind i.tag = true
  · exact inferBody_binders_batched henv hsim s₀ d i e hok hden hw hb
  by_cases hc : i.tag = ETag.const
  · exact inferBody_const henv hμ hsim s₀ d i e hok hden hw hc
  by_cases hl : i.tag = ETag.lit
  · exact inferBody_lit henv hμ hsim s₀ d i e hok hden hw hl
  by_cases hlt : i.tag = ETag.letE
  · exact inferBody_letE hsim s₀ d i e hok hden hw hlt
  exact inferBody_leaf henv hμ hsim s₀ d i e hok hden hw ha hp
    (Bool.eq_false_iff.mpr hb) hc hl hlt

/-! ## The axiom census of the dispatch's children -/

section Census

#print axioms inferBody_app
#print axioms inferBody_binders_batched
#print axioms inferBody_const
#print axioms inferBody_lit
#print axioms inferBody_leaf

end Census

end ConRon.Bridge.Core
