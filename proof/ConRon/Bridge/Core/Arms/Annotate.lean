/-
# `ConRon.Bridge.Core.Arms.Annotate` — Theorem 1 for `annotateBody`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1805-1915
annotateBody` — the one pass that meets raw stream input, and therefore the
one pass whose `.letE` clause runs the official `infer_let` triple and returns
the ζ reduct (con-leche's task #217).

| clause | exit | lemma |
|---|---|---|
| `.bvar` | itself | `annot_bvar` |
| `.fvar` | in scope, itself | `annot_fvar` |
| `.sort` / `.const` | itself | `annot_sort`, `annot_const` |
| `.lit (.natVal _)` | the `Nat` basis is installed | `annot_natLit` |
| `.lit (.strVal _)` | the `String` basis is installed | `annot_strLit` |
| `.app` | structural | `annot_app` |
| `.forallE` | the node carries a real datum | `annot_forallE_written` |
| `.forallE` | the datum is computed (`annotPwPi`) | `annot_forallE_computed` |
| `.lam` | the node carries a real datum | `annot_lam_written` |
| `.lam` | the datum is computed (`annotPwLam`) | `annot_lam_computed` |
| `.letE` | the `infer_let` triple, then the ζ reduct | `annot_letE` |
| `.proj` | the table entry and the two name/arity premises | `annot_proj` |

## The deviations the twin carries at this body

1. **The binder-telescope loops** (task #97-P6-11): the twin's `.forallE`
   clause and its bvar-closed `.lam` clause are `annotatePis`/`annotateLams`,
   con-leche's own CACHED-tier `annotatePisI`/`annotateLamsI` with
   `annotateBindersOut`'s outward rebuild.  The single-binder clause survives
   as `annotateBinder`, con-leche's λ residual, entered zero times on `Init`.
   con-leche's identification is `Verify/BinderLoop.lean` and its cached port;
   the carry is `annotateBody_binders_batched` below.
2. **The EXECUTED `abstractRange`** (the same task): the rebuild calls
   `abstractRangeFast`, whose spec is `Bridge/ExprOps/Owed.lean`'s (still
   `sorry` — task #97-P3-0's open list) and whose identification with the
   spec descent is `Bridge/ExprOps/Abs.lean`'s.
3. `internRebuiltApp` at the `.app` clause (task #97-P6-7's lever 4), whose
   `@[spec]` theorem is `Bridge/Specs.lean`'s `internRebuiltApp_spec` and
   which claims exactly `RelE`'s `.self` when the children did not move.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Arms.Infer

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The six leaf clauses -/

/-- con-leche: ConLeche/Kernel/Core.lean:1808 annotateBody. -/
theorem annot_bvar {F d i : Nat} :
    ConLeche.annotateCore mode env (F + 1) d (.bvar i) = .ok (.bvar i) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1809-1814 annotateBody — the leaf
scope check, which is where a dangling free variable in RAW input is
rejected (at depth 0, any `fvar` fails). -/
theorem annot_fvar {F d idx : Nat} {ty : Expr} (h : idx < d) :
    ConLeche.annotateCore mode env (F + 1) d (.fvar idx ty) =
      .ok (.fvar idx ty) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, if_pos h, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1815 annotateBody. -/
theorem annot_sort {F d : Nat} {u : Level} :
    ConLeche.annotateCore mode env (F + 1) d (.sort u) = .ok (.sort u) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1816 annotateBody. -/
theorem annot_const {F d : Nat} {n : Name} {us : List Level} :
    ConLeche.annotateCore mode env (F + 1) d (.const n us) =
      .ok (.const n us) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1817-1821 annotateBody — a literal
is well formed exactly when its type's declarations are stored. -/
theorem annot_natLit {F d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    ConLeche.annotateCore mode env (F + 1) d (.lit (.natVal n)) =
      .ok (.lit (.natVal n)) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, h, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1822-1827 annotateBody. -/
theorem annot_strLit {F d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    ConLeche.annotateCore mode env (F + 1) d (.lit (.strVal s)) =
      .ok (.lit (.strVal s)) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, h, if_true, pure, Except.pure]

/-! ## 2. The application clause -/

/-- con-leche: ConLeche/Kernel/Core.lean:1828-1835 annotateBody — structural:
the application rule's checks are the driver's inference sweep's (con-leche's
task #100 stage 6). -/
theorem annot_app {F d : Nat} {f a f' a' : Expr}
    (hf : ConLeche.annotateCore mode env F d f = .ok f')
    (ha : ConLeche.annotateCore mode env F d a = .ok a') :
    ConLeche.annotateCore mode env (F + 1) d (.app f a) = .ok (.app f' a') := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hf, ha, bind,
    Except.bind, pure, Except.pure]

/-! ## 3. The two binder clauses

Each has two exits: the node already carries a real input annotation (which
validation judges and the pass never overwrites — con-leche's
`pwWritten`/`annotBinderMeta`), or the datum is computed from the annotated
body. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1836-1845 annotateBody — the ∀
clause at a node that **already carries** a datum. -/
theorem annot_forallE_written {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = true) :
    ConLeche.annotateCore mode env (F + 1) d (.forallE ty body mb) =
      .ok (.forallE ty' (body'.abstract1 d) ⟨mb.pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, bind,
    Except.bind, Bool.not_eq_true', Bool.true_eq_false, if_false, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1836-1845 annotateBody — the ∀
clause whose datum is **computed** by `annotPwPi` from the annotated body. -/
theorem annot_forallE_computed {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta} {pw : PropWhen}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = false)
    (hpw : ConLeche.annotPwPi (ConLeche.pureFns mode env F) env (d + 1) body'
      = .ok pw) :
    ConLeche.annotateCore mode env (F + 1) d (.forallE ty body mb) =
      .ok (.forallE ty' (body'.abstract1 d) ⟨pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, hpw,
    bind, Except.bind, Bool.not_eq_true', if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1846-1853 annotateBody — the λ
clause at a node that **already carries** a datum. -/
theorem annot_lam_written {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = true) :
    ConLeche.annotateCore mode env (F + 1) d (.lam ty body mb) =
      .ok (.lam ty' (body'.abstract1 d) ⟨mb.pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, bind,
    Except.bind, Bool.not_eq_true', Bool.true_eq_false, if_false, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1846-1853 annotateBody — the λ
clause whose datum is **computed** by `annotPwLam`. -/
theorem annot_lam_computed {F d : Nat} {ty body ty' body' : Expr}
    {mb : BinderMeta} {pw : PropWhen}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (hb : ConLeche.annotateCore mode env F (d + 1)
      (body.instantiate1 (.fvar d ty')) = .ok body')
    (hw : ConLeche.pwWritten mb.pw = false)
    (hpw : ConLeche.annotPwLam (ConLeche.pureFns mode env F) env (d + 1) body'
      = .ok pw) :
    ConLeche.annotateCore mode env (F + 1) d (.lam ty body mb) =
      .ok (.lam ty' (body'.abstract1 d) ⟨pw⟩) := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, hty, hb, hw, hpw,
    bind, Except.bind, Bool.not_eq_true', if_true, pure, Except.pure]

/-! ## 4. The `let` clause — the one place the official `infer_let` triple
runs

con-leche's task #217: this clause returns the ζ REDUCT, so every term the
checker stores is let-free and `inferBody`'s and `whnfCoreBody`'s `.letE` arms
are unreachable by construction.  Dropping the triple as redundant with
`inferBody`'s own `.letE` clause was con-leche's task #161 item C2, and it was
wrong — the witness is in that clause's doc comment. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1854-1886 annotateBody — the `let`
clause: `ensureSort (infer ty')`, `infer v'`, `defeq tv ty'`, then annotate
the ζ reduct. -/
theorem annot_letE {F d : Nat} {ty v b ty' v' tty tv res : Expr} {u : Level}
    (hty : ConLeche.annotateCore mode env F d ty = .ok ty')
    (htty : ConLeche.inferTypeCore mode env F d ty' = .ok tty)
    (hs : ConLeche.ensureSortCore mode env F d tty = .ok u)
    (hv : ConLeche.annotateCore mode env F d v = .ok v')
    (htv : ConLeche.inferTypeCore mode env F d v' = .ok tv)
    (hde : ConLeche.isDefEqCore mode env F d tv ty' = .ok true)
    (hr : ConLeche.annotateCore mode env F d (b.instantiate1 v) = .ok res) :
    ConLeche.annotateCore mode env (F + 1) d (.letE ty v b) = .ok res := by
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, ConLeche.infer_def,
    ConLeche.ensureSort_def, ConLeche.defeq_def, hty, htty, hs, hv, htv, hde,
    bind, Except.bind]
  simpa using hr

/-! ## 5. The projection clause -/

/-- con-leche: ConLeche/Kernel/Core.lean:1887-1915 annotateBody — the
projection rule, run HERE and nowhere else: the node's own structure name is
official's `infer_proj` premise (con-leche's task #271, its issue #7), and the
display name is normalized to the type's head so that reduction's table lookup
is complete on annotated terms. -/
theorem annot_proj {F d i : Nat} {sn T : Name} {pe e' te tpe : Expr}
    {us : List Level} {entry : ProjEntry}
    (hpe : ConLeche.annotateCore mode env F d pe = .ok e')
    (hipe : ConLeche.inferTypeIO mode env F d e' = .ok tpe)
    (hw : ConLeche.whnf mode env F d tpe = .ok te)
    (hh : te.getAppFn = .const T us)
    (ht : env.findProj? T i = some entry)
    (hn : T = sn)
    (ha : te.getAppArgs.length = entry.numParams) :
    ConLeche.annotateCore mode env (F + 1) d (.proj sn i pe) =
      .ok (.proj T i e') := by
  subst hn
  rw [ConLeche.annotateCore_succ]
  simp only [ConLeche.annotateBody, ConLeche.annotate_def, ConLeche.whnf_def,
    ConLeche.inferTypeIO_def, hpe, hipe, hw, hh, ht, ha, bind, Except.bind,
    pure, Except.pure]
  simp

/-! ## 6. The batched clause's identification, and the body theorem -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean — **OPEN** (task
#97-P3-Core): the twin's binder clauses are `annotatePis`/`annotateLams`
(task #97-P6-11), con-leche's own cached-tier telescope loops with
`annotateBindersOut`'s outward rebuild, against the chained
`annot_forallE_*`/`annot_lam_*` above.  What is owed is the denotation carry,
and it needs `Bridge/ExprOps/Owed.lean`'s `abstractRangeFast_spec` — still
`sorry` (task #97-P3-0's open list) — because the rebuild is the EXECUTED
`abstractRange` and not the spec descent. -/
theorem annotateBody_binders_batched {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) (htag : ETag.isBind i.tag = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  sorry


/-! ### The dispatch's children (task #97-P3-Core round 5)

`annotateBody_spec` below is a case split on the tag: one child per group of
the twin's `view` dispatch, each a triple at the same body under its tag
hypothesis; the batched binder clause above is one of them. -/

/-- con-leche: none — DESIGN §8.3 at an application node: a handle that
denotes `.app ef ea` VIEWS as the application of any two handles denoting
`ef` and `ea` (index equality is structural equality).  `internRebuiltApp`'s
upward cutoff needs the view at the subject when neither child moved, and a
knot slot's postcondition carries the denotation, not the view. -/
theorem view_app_of_denote {st : EStore} (hwf : StoreWF st) {i f a : EIdx}
    {ef ea : Expr} (hi : denoteE st i = some (.app ef ea))
    (hf : denoteE st f = some ef) (ha : denoteE st a = some ea) :
    st.view i = some (.app f a) := by
  obtain ⟨w, hw⟩ := denoteE_view hi
  cases w with
  | app x y =>
    obtain ⟨ef', ea', he, hx, hy⟩ := denote_app_inv hwf hw hi
    cases he
    rw [hw, denoteE_inj hwf hx hf, denoteE_inj hwf hy ha]
  | bvar k => cases denote_bvar_inv hwf hw hi
  | fvar k t => obtain ⟨_, h, _⟩ := denote_fvar_inv hwf hw hi; cases h
  | sort u => obtain ⟨_, h, _⟩ := denote_sort_inv hwf hw hi; cases h
  | const n us => obtain ⟨_, _, h, _⟩ := denote_const_inv hwf hw hi; cases h
  | lit l => cases denote_lit_inv hwf hw hi
  | lam ty b m => obtain ⟨_, _, h, _⟩ := denote_lam_inv hwf hw hi; cases h
  | forallE ty b m =>
    obtain ⟨_, _, h, _⟩ := denote_forallE_inv hwf hw hi; cases h
  | letE ty v b => obtain ⟨_, _, _, h, _⟩ := denote_letE_inv hwf hw hi; cases h
  | proj n k sub => obtain ⟨_, _, h, _⟩ := denote_proj_inv hwf hw hi; cases h

/-- con-leche: ConLeche/Kernel/Core.lean:1828-1834 annotateBody — **the
`.app` clause**: two `KnotSpec.annotate` calls and the rebuilt node
(`internRebuiltApp`, task #97-P6-7's upward cutoff); pure side `annot_app`.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem annotateBody_app {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.app) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case app f a =>
    obtain ⟨ef, ea, rfl, hdf, hda⟩ := denote_app_inv hwf hv hden
    have hwf' : Expr.WScoped d ef := by unfold Expr.WScoped at hw; exact hw.1
    have hwa : Expr.WScoped d ea := by unfold Expr.WScoped at hw; exact hw.2
    have h1 := hsim.annotate s₀ d f ef hok hdf hwf'
    have h2 := fun (s : AState) (hck : CheckOK mode env fe s)
        (hd : denoteE s.store a = some ea) => hsim.annotate s d a ea hck hd hwa
    mvcgen [h1, h2]
    all_goals (bridge_peel; subst_vars)
    case vc2.hck => rename_i _ _ _ hck1 _ _ _; exact hck1
    case vc3.hd => rename_i _ _ _ _ _ hx1 _; exact denote_ext hda hx1
    case vc4.post.success.post.success.post.success =>
      rename_i _ r1 _ r2 _ _ _ hck1 hck2 hx12 hs1 hp21 hs2 hx01 hp10
      intro hwf3 hx3 _ _ hc3 hp3 _ _ hd3
      obtain ⟨v1, hd1, hw1, F1, hF1⟩ := hs1
      obtain ⟨v2, hd2, hw2, F2, hF2⟩ := hs2
      refine ⟨hck2.mono ⟨hwf3⟩ hx3 hc3 hp3, hx01.trans (hx12.trans hx3),
        hp3.trans (hp21.trans hp10), .app v1 v2, ?_,
        by unfold Expr.WScoped; exact ⟨hw1, hw2⟩, max F1 F2 + 1,
        annot_app (ConLeche.annotateCore_mono (Nat.le_max_left _ _) hF1)
          (ConLeche.annotateCore_mono (Nat.le_max_right _ _) hF2)⟩
      rw [hd3]
      simp [denoteEView, opt2, denote_ext (denote_ext hd1 hx12) hx3,
        denote_ext hd2 hx3]
    case vc5 => intro s hck _ _ _; exact hck.state.wf
    case vc6 =>
      rename_i _ _ _ _ _ hs1 _ _
      intro s _ hx _ _
      obtain ⟨v1, hd1, _⟩ := hs1
      rw [denote_ext hd1 hx]; rfl
    case vc7 => intro s _ _ _ hs2; exact hs2.denote
    case vc8 =>
      rename_i _ _ _ _ _ _ hx01 _
      intro s hck hx _ _ hsame
      simp only [Bool.and_eq_true, beq_iff_eq] at hsame
      obtain ⟨rfl, rfl⟩ := hsame
      have hx' := hx01.trans hx
      exact view_app_of_denote hck.state.wf (denote_ext hden hx')
        (denote_ext hdf hx') (denote_ext hda hx')
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1817-1827 annotateBody — **the two
literal clauses**: `natLitSupported_spec` (CLOSED) and `strLitSupported_spec`
(`Walks/StrLit.lean`, CLOSED); pure side `annot_natLit`/`annot_strLit`.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem annotateBody_lit {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.lit) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    cases l with
    | natVal n =>
      have hn := natLitSupported_spec (mode := mode) (env := env) (fe := fe)
        s₀ hok
      mvcgen [hn]
      all_goals (bridge_peel; subst_vars)
      all_goals first
        | exact fun h => h.elim
        | (rename_i s1 s0 ck_s0 x_s1_s0 p_s0_s1 hsup
           exact ⟨ck_s0, x_s1_s0, p_s0_s1, _, denote_ext hden x_s1_s0, hw, 1,
             annot_natLit hsup.symm⟩)
    | strVal str =>
      have hn := strLitSupported_spec (mode := mode) (env := env) (fe := fe)
        s₀ hok
      mvcgen [hn]
      all_goals (bridge_peel; subst_vars)
      all_goals first
        | exact fun h => h.elim
        | (rename_i s1 s0 ck_s0 x_s1_s0 p_s0_s1 hsup
           exact ⟨ck_s0, x_s1_s0, p_s0_s1, _, denote_ext hden x_s1_s0, hw, 1,
             annot_strLit hsup.symm⟩)
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: ConLeche/Kernel/Core.lean:1103-1107 ensureSort — at the pure
knot, `ensureSort` answers the level of a `whnf` that reached a sort. -/
theorem ensureSortCore_of_whnf {F d : Nat} {t : Expr} {u : Level}
    (h : ConLeche.whnf mode env F d t = .ok (.sort u)) :
    ConLeche.ensureSortCore mode env F d t = .ok u := by
  rw [← ConLeche.ensureSort_def]
  simp only [ConLeche.ensureSort, ConLeche.whnf_def, h, bind, Except.bind,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1852-1881 annotateBody — **the `.letE`
clause** (con-leche's task #217): `KnotSpec.annotate`, `ensureSort`,
`KnotSpec.infer`, `KnotSpec.defeq'`, `instantiate1Fast`; pure side
`annot_letE`.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem annotateBody_letE {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.letE) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
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
    have h1 := hsim.annotate s₀ d ty et hok hdt hwt
    have hi := hsim.infer'
    have hn := hsim.whnf'
    have h4 := fun (s : AState) (hck : CheckOK mode env fe s)
        (hd : denoteE s.store w = some ew) => hsim.annotate s d w ew hck hd hww
    have hdq := hsim.defeq'
    have hin := fun (s : AState) (hs : StateOK s)
        (hvs : (denoteE s.store w).isSome = true)
        (hbs : (denoteE s.store b).isSome = true) =>
      instantiate1Fast_specE coreWalkFuel s b w 0 hs hvs hbs
    have h7 := hsim.annotate'
    mvcgen [ConRon.Arena.ensureSort, h1, hi, hn, h4, hdq, hin, h7]
    all_goals (bridge_peel; subst_vars)
    case vc2.hdw => exact ⟨et, hdt, hwt⟩
    case vc4.hdw =>
      rename_i s1 r0 s0 ck_s0 x_s1_s0 p_s0_s1 hse
      exact SimE.exists_denote (hse et hdt)
    case vc6.hdw =>
      rename_i s2 r1 s1 r0 s0 ck_s1 ck_s0 x_s2_s1 x_s1_s0 p_s1_s2 hse p_s0_s1 hse_2
      obtain ⟨v1, hv1, _⟩ := hse et hdt
      exact SimE.exists_denote (hse_2 v1 hv1)
    case vc8.hdw =>
      rename_i s3 r2 s2 r1 s1 r0 u0 s0 ck_s2 ck_s1 x_s3_s2 x_s2_s1 p_s2_s3 hse
        p_s1_s2 hse_2 ck_s0 v_r0_s0 x_s1_s0 p_s0_s1 hse_3
      exact ⟨ew, denote_ext hdw (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)), hww⟩
    case vc10.hdw =>
      rename_i s4 r3 s3 r2 s2 r1 u0 s1 r0 s0 ck_s3 ck_s2 ck_s0 x_s4_s3 x_s3_s2
        x_s1_s0 p_s3_s4 hse p_s2_s3 hse_2 p_s0_s1 hse_3 ck_s1 v_r1_s1 x_s2_s1
        p_s1_s2 hse_4
      exact SimE.exists_denote
        (hse_3 ew (denote_ext hdw (x_s4_s3.trans (x_s3_s2.trans x_s2_s1))))
    case vc12.hda =>
      rename_i s5 r4 s4 r3 s3 r2 u0 s2 r1 s1 r0 s0 ck_s4 ck_s3 ck_s1 ck_s0 x_s5_s4
        x_s4_s3 x_s2_s1 x_s1_s0 p_s4_s5 hse p_s3_s4 hse_2 p_s1_s2 hse_3 p_s0_s1
        hse_4 ck_s2 v_r2_s2 x_s3_s2 p_s2_s3 hse_5
      obtain ⟨v4, hv4, _⟩ := hse_3 ew (denote_ext hdw
        (x_s5_s4.trans (x_s4_s3.trans x_s3_s2)))
      exact SimE.exists_denote (hse_4 v4 hv4)
    case vc13.hdb =>
      rename_i s5 r4 s4 r3 s3 r2 u0 s2 r1 s1 r0 s0 ck_s4 ck_s3 ck_s1 ck_s0 x_s5_s4
        x_s4_s3 x_s2_s1 x_s1_s0 p_s4_s5 hse p_s3_s4 hse_2 p_s1_s2 hse_3 p_s0_s1
        hse_4 ck_s2 v_r2_s2 x_s3_s2 p_s2_s3 hse_5
      obtain ⟨v1, hv1, hw1, _⟩ := hse et hdt
      exact ⟨v1, denote_ext hv1
        (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))), hw1⟩
    case vc16.hvs =>
      rename_i s6 r5 s5 r4 s4 r3 u0 s3 r2 s2 r1 s1 _ hneg0 s0 ck_s5 ck_s4 ck_s2 ck_s1
        ck_s0 x_s6_s5 x_s5_s4 x_s3_s2 x_s2_s1 x_s1_s0 p_s5_s6 hse p_s4_s5 hse_2
        p_s2_s3 hse_3 p_s1_s2 hse_4 p_s0_s1 hsv ck_s3 v_r3_s3 x_s4_s3 p_s3_s4 hse_5
      rw [denote_ext hdw (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans
        (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))]; rfl
    case vc17.hbs =>
      rename_i s6 r5 s5 r4 s4 r3 u0 s3 r2 s2 r1 s1 _ hneg0 s0 ck_s5 ck_s4 ck_s2 ck_s1
        ck_s0 x_s6_s5 x_s5_s4 x_s3_s2 x_s2_s1 x_s1_s0 p_s5_s6 hse p_s4_s5 hse_2
        p_s2_s3 hse_3 p_s1_s2 hse_4 p_s0_s1 hsv ck_s3 v_r3_s3 x_s4_s3 p_s3_s4 hse_5
      rw [denote_ext hdb (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans
        (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))]; rfl
    case vc18.post.success.post.success.post.success.post.success.h_1.post.success.post.success.post.success.isFalse.post.success.post.success =>
      rename_i s8 r7 s7 r6 s6 r5 u0 s5 r4 s4 r3 s3 bq hneg0 s2 r1 s1 r0 s0 ck_s7
        ck_s6 ck_s4 ck_s3 ck_s2 sok x_s8_s7 x_s7_s6 x_s5_s4 x_s4_s3 x_s3_s2
        x_s2_s1 p_s7_s8 hse p_s6_s7 hse_2 p_s4_s5 hse_3 p_s3_s4 hse_4 p_s2_s3 hsv
        c_s1_s2 p_s1_s2 _ hia ck_s5 v_r5_s5 x_s6_s5 p_s5_s6 hse_5
      intro ck_s0 x_s1_s0 p_s0_s1 hfin
      have x82 := x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans
        (x_s4_s3.trans x_s3_s2))))
      obtain ⟨v1, hv1, _, F1, hF1⟩ := hse et hdt
      obtain ⟨v2, hv2, _, F2, hF2⟩ := hse_2 v1 hv1
      obtain ⟨v3, hv3, _, F3, hF3⟩ := hse_5 v2 hv2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv ck_s5.state.wf v_r5_s5 hv3
      obtain ⟨v4, hv4, _, F4, hF4⟩ := hse_3 ew
        (denote_ext hdw (x_s8_s7.trans (x_s7_s6.trans x_s6_s5)))
      obtain ⟨v5, hv5, _, F5, hF5⟩ := hse_4 v4 hv4
      obtain ⟨F6, hF6⟩ := hsv v5 v1 hv5 (denote_ext hv1
        (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans x_s4_s3))))
      have hbq : bq = true := by simpa using hneg0
      subst hbq
      have hbz := hia ew (denote_ext hdw x82) eb (denote_ext hdb x82)
      obtain ⟨v7, hv7, hwv7, F7, hF7⟩ := hfin _ hbz
      refine ⟨ck_s0, x82.trans (x_s2_s1.trans x_s1_s0),
        p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans
          (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans p_s7_s8)))))),
        v7, hv7, hwv7,
        max F1 (max F2 (max F3 (max F4 (max F5 (max F6 F7))))) + 1, ?_⟩
      exact annot_letE
        (ConLeche.annotateCore_mono (by omega) hF1)
        (ConLeche.inferTypeCore_mono (by omega) hF2)
        (ensureSortCore_of_whnf (ConLeche.whnf_mono (by omega) hF3))
        (ConLeche.annotateCore_mono (by omega) hF4)
        (ConLeche.inferTypeCore_mono (by omega) hF5)
        (ConLeche.isDefEqCore_mono (by omega) hF6)
        (ConLeche.annotateCore_mono (by omega) hF7)
    case vc19 =>
      rename_i s6 r6 s5 r5 s4 r4 u0 s3 r3 s2 r2 s1 _ hneg0 s0 r0 ck_s5 ck_s4 ck_s2
        ck_s1 ck_s0 x_s6_s5 x_s5_s4 x_s3_s2 x_s2_s1 x_s1_s0 p_s5_s6 hse p_s4_s5
        hse_2 p_s2_s3 hse_3 p_s1_s2 hse_4 p_s0_s1 hsv ck_s3 v_r4_s3 x_s4_s3
        p_s3_s4 hse_5
      intro s hs hx hc hp _ _
      exact ck_s0.mono hs hx hc hp
    case vc20 =>
      rename_i s6 r6 s5 r5 s4 r4 u0 s3 r3 s2 r2 s1 _ hneg0 s0 r0 ck_s5 ck_s4 ck_s2
        ck_s1 ck_s0 x_s6_s5 x_s5_s4 x_s3_s2 x_s2_s1 x_s1_s0 p_s5_s6 hse p_s4_s5
        hse_2 p_s2_s3 hse_3 p_s1_s2 hse_4 p_s0_s1 hsv ck_s3 v_r4_s3 x_s4_s3
        p_s3_s4 hse_5
      intro s hs hx hc hp _ hia
      have x60 := x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans
        (x_s2_s1.trans x_s1_s0))))
      exact ⟨_, hia ew (denote_ext hdw x60) eb (denote_ext hdb x60),
        Expr.WScoped.instantiate1_gen hww 0 hwb⟩
    all_goals first
      | assumption
      | exact fun h => h.elim
      | (apply CheckOK.state; assumption)
  all_goals (rw [htg] at htag; exact absurd htag (by simp [ENodeView.tagOf]; decide))

/-- con-leche: none — `Walks/Proj.lean`'s `IFEnv.findProj?_spec` in ANSWER
shape: the looked-up name is read off a `view` of a `whnf`'s head, so its
denotation goes in as an existential and out as a universal (round 3's
rule). -/
theorem IFEnv.findProj?_spec' {fe : IFEnv} (s₀ : AState) (T : NIdx) (i : Nat)
    (hok : CheckOK mode env fe s₀)
    (hT : ∃ Tn, denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ fe.findProj? T i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        ∀ Tn, denoteN s₀.store.ns T = some Tn →
          ∀ e, r = some e → ∃ p, denoteProjEntry s'.store e = some p ∧
            env.findProj? Tn i = some p⌝⦄ := by
  obtain ⟨Tn, hTn⟩ := hT
  have h := IFEnv.findProj?_spec (mode := mode) (env := env) (fe := fe)
    s₀ T i Tn hok hTn
  mvcgen [h]
  intro hck hx _ hc hp hsome _
  refine ⟨hck, hx, hc, hp, fun Tn' hTn' => ?_⟩
  rw [hTn] at hTn'; obtain rfl := Option.some.inj hTn'; exact hsome

/-- con-leche: ConLeche/Kernel/Core.lean:1882-1900 annotateBody — **the `.proj`
clause**: `KnotSpec.annotate`, `KnotSpec.inferIO'`, `KnotSpec.whnf'`,
`getAppFn`/`getAppArgs`, `IFEnv.findProj?_spec`; pure side `annot_proj`.

**CLOSED** (round 5), staged by `triple_seq` (`Memo.lean`): every
callee is applied at a subject whose denotation the previous stage NAMED,
and every callee rule it needs was already closed. -/
theorem annotateBody_proj {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (htag : i.tag = ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  cases v
  case proj sn k pe =>
    obtain ⟨nm, es, rfl, hsn, hpe⟩ := denote_proj_inv hwf hv hden
    have hwes : Expr.WScoped d es := by simpa [Expr.WScoped] using hw
    refine view_bind_triple hv ?_
    dsimp only
    -- stage 1: annotate the subject
    refine triple_seq (hsim.annotate s₀ d pe es hok hpe hwes) ?_
    rintro e' s1 ⟨hok1, hx1, hp1, v', hv', hwv', F1, hF1⟩
    -- stage 2: its io-grade type
    refine triple_seq (hsim.inferIO s1 d e' v' hok1 hv' hwv') ?_
    rintro t s2 ⟨hok2, hx2, hp2, vt, hvt, hwvt, F2, hF2⟩
    -- stage 3: that type's head normal form
    refine triple_seq (hsim.whnf s2 d t vt hok2 hvt hwvt) ?_
    rintro te s3 ⟨hok3, hx3, hp3, vte, hvte, _hwvte, F3, hF3⟩
    have hx03 : Ext s₀.store s3.store := hx1.trans (hx2.trans hx3)
    have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp1)
    have hwf3 := hok3.state.wf
    -- stage 4: its head
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s3 te hok3.state
      (by rw [hvte]; rfl)) ?_
    rintro hd s4 ⟨hs4, hrelF⟩
    subst s4
    have hdd : denoteE s3.store hd = some vte.getAppFn := hrelF vte hvte
    obtain ⟨vh, hvh⟩ := denoteE_view hdd
    refine tag_view_bind_triple hvh ?_
      (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
    cases vh
    case const T us =>
      obtain ⟨Tn, ls, hgf, hTn, _hus⟩ := denote_const_inv hwf3 hvh hdd
      dsimp only
      -- stage 5: the table
      refine triple_seq (IFEnv.findProj?_spec s3 T k Tn hok3 hTn) ?_
      rintro oe s5 ⟨hok5, hx5, _hm5, _hc5, hp5, hsome, _hnone⟩
      cases oe with
      | none =>
        dsimp only
        refine triple_seq (IFEnv.findProj?_spec s5 T 0 Tn hok5
          (denoteN_ext hTn hx5)) ?_
        intro _ _ _
        exact triple_fail
      | some entry =>
        obtain ⟨p, hpd, hfp⟩ := hsome entry rfl
        obtain ⟨_hsnp, _hlps, _hctor, _hbody, _hfs, _hss, _hidx, hnp, _hnf,
          _hoff⟩ := denoteProjEntry_inv hpd
        dsimp only
        split
        next => exact triple_fail
        next hT =>
          have hT' : T = sn := by simpa using hT
          subst hT'
          have hTnm : Tn = nm := by
            have h1 := denoteN_ext hsn hx03
            exact Option.some.inj (hTn.symm.trans h1)
          subst hTnm
          have hvte5 := denote_ext hvte hx5
          -- stage 6: the type's arguments
          refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s5 te
            hok5.state (by rw [hvte5]; rfl)) ?_
          rintro targs s6 ⟨hs6, hrelA⟩
          subst s6
          have hargs : Frontend.denoteEList s5.store targs =
              some vte.getAppArgs := hrelA vte hvte5
          split
          next => exact triple_fail
          next hlen =>
            have hlen' : vte.getAppArgs.length = p.numParams := by
              rw [denoteEList_len hargs, hnp]; simpa using hlen
            have hx05 : Ext s₀.store s5.store := hx03.trans hx5
            have hv'5 := denote_ext hv' (hx2.trans (hx3.trans hx5))
            have hsn5 := denoteN_ext hsn hx05
            have hvw : s5.store.ViewOK (.proj T k e') :=
              viewOK_proj (nview_isSome_of_denote hsn5) (by rw [hv'5]; rfl)
            refine triple_mono (internE_spec s5 _ hok5.state.wf hvw) ?_
            rintro r s' ⟨hwf', hx', _hbm, _hl, _hsc, _hm, hc', hp', _hview,
              hden'⟩
            refine ⟨hok5.mono ⟨hwf'⟩ hx' hc' hp', hx05.trans hx',
              hp'.trans (hp5.trans hp03), .proj Tn k v', ?_,
              by simpa [Expr.WScoped] using hwv', ?_⟩
            · rw [hden']
              simp only [denoteEView, denoteN_ext hsn5 hx', denote_ext hv'5 hx',
                opt2]
            · refine ⟨max F1 (max F2 F3) + 1, annot_proj
                (ConLeche.annotateCore_mono (Nat.le_max_left _ _) hF1)
                (ConLeche.inferTypeIO_mono (Nat.le_trans (Nat.le_max_left F2 F3)
                  (Nat.le_max_right _ _)) hF2)
                (ConLeche.whnf_mono (Nat.le_trans (Nat.le_max_right F2 F3)
                  (Nat.le_max_right _ _)) hF3) hgf hfp rfl hlen'⟩
    all_goals (dsimp only; exact triple_fail)
  all_goals
    exfalso
    rw [htag] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

#print axioms annotateBody_proj

/-- con-leche: ConLeche/Kernel/Core.lean:1808-1816 annotateBody — **the leaf
clauses**: `.bvar`, `.fvar` (the scope check), `.sort` and `.const` answer
themselves; pure side `annot_bvar`/`_fvar`/`_sort`/`_const`.
**CLOSED** (task #97-P3-Core round 5, sub-lane Leaves). -/
theorem annotateBody_leaf {fe : IFEnv} {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (_hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e)
    (hna : i.tag ≠ ETag.app) (hnl : i.tag ≠ ETag.lit)
    (hnb : ETag.isBind i.tag = false) (hne : i.tag ≠ ETag.letE)
    (hnp : i.tag ≠ ETag.proj) :
    ⦃fun s => ⌜s = s₀⌝⦄
      annotateBody (coreKnot mode fe id fuel) fe d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  have htg := EStore.tagOf_of_view hv
  refine view_bind_triple hv ?_
  cases v with
  | app f a => exact absurd htg hna
  | lit l => exact absurd htg hnl
  | letE ty w b => exact absurd htg hne
  | proj n k sub => exact absurd htg hnp
  | lam ty b m =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
  | forallE ty b m =>
    rw [htg] at hnb; simp [ENodeView.tagOf, ETag.isBind] at hnb
  | bvar k =>
    obtain rfl := denote_bvar_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_bvar⟩
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hden
    have hk : k < d := by unfold Expr.WScoped at hw; exact hw.1
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_fvar hk⟩
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_sort⟩
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hden
    mvcgen; bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, _, hden, hw, 1, annot_const⟩

/-- con-leche: ConLeche/Verify/Cached/DiscC6.lean annotateBodyC_sim —
**THEOREM 1 for `annotateBody`**.

**OPEN** (task #97-P3-Core).  What is missing: the batched binder clause
above, the `.proj` arm's callee rules, and `annotPwPi`/`annotPwLam` — two
`Arena/Core.lean` walks that read the head symbol before falling back to
inference and that need `BodySpec`-shaped theorems of their own.  The twelve
step lemmas above are closed. -/
theorem annotateBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe (annotateBody (coreKnot mode fe id fuel) fe)
      (ConLeche.annotateCore mode env) := by
  intro s₀ d i e hok hden hw
  by_cases ha : i.tag = ETag.app
  · exact annotateBody_app henv hμ hsim s₀ d i e hok hden hw ha
  by_cases hb : ETag.isBind i.tag = true
  · exact annotateBody_binders_batched henv hsim s₀ d i e hok hden hw hb
  by_cases hl : i.tag = ETag.lit
  · exact annotateBody_lit henv hμ hsim s₀ d i e hok hden hw hl
  by_cases he : i.tag = ETag.letE
  · exact annotateBody_letE henv hμ hsim s₀ d i e hok hden hw he
  by_cases hp : i.tag = ETag.proj
  · exact annotateBody_proj henv hμ hsim s₀ d i e hok hden hw hp
  exact annotateBody_leaf henv hμ hsim s₀ d i e hok hden hw ha hl
    (Bool.eq_false_iff.mpr hb) he hp

/-! ## The axiom census of the closed children (task #97-P3-Core round 5,
sub-lane Leaves) -/

section Census

#print axioms view_app_of_denote
#print axioms annotateBody_app
#print axioms annotateBody_lit
#print axioms annotateBody_leaf
#print axioms ensureSortCore_of_whnf
#print axioms annotateBody_letE
#print axioms IFEnv.findProj?_spec'
end Census

end ConRon.Bridge.Core
