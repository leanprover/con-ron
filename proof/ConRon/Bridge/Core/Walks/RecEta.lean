/-
# `ConRon.Bridge.Core.Walks.RecEta` — recursor η and the stuck fallback

con-leche's task #632 (lean4#15374): a partially applied recursor of a K-like
type or of a type with η, compared with a term that is no λ, is η-expanded
along its io-inferred type, the full application ι-reduced, and the λ that
results compared with the other side.  It is the first step of `stuckIrrel`,
in both orientations, so `stuckIrrel`'s theorem lives here, after the ι step
(`Walks/BetaSpine.lean`'s `whnfAppIota_specE`), as upstream moved its bridge
after `iotaRec_bridge`.

| walk | twin (`Arena/Core.lean`) | con-leche | proof |
|---|---|---|---|
| `recMajorEta_eq` | `recMajorEta` | `CoreDefs.lean` `recMajorEta` | an equation, two lookups |
| `recEtaPartial_spec` | `recEtaPartial` | `CoreDefs.lean` `recEtaPartial` | staged, an equation with the reader |
| `iotaRecSpine_spec` | `iotaRecSpine` | `iotaRec` (`Cached/CoreC.lean` `iotaRecAtI`) | `headAndArgs_spec`, `whnfAppIota_specE` |
| `recEtaTele_spec` | `recEtaTele` | `recEtaTele` | induction on the missing arguments, staged, exits `recEtaTeleFueled_*` |
| `recEtaCert_specA` | `recEtaCert` | `recEtaCert` | `vcgen`/`grind`, exits `RecEtaE.*` |
| `stuckIrrel_specA` | `stuckIrrel` | `stuckIrrel` | `vcgen`/`grind` over the six exits (`StuckE.*`) |

`henv : EnvWF env` is con-leche's own hypothesis of `recEtaTele_WScoped` (the
λ's scoping) and of the ι step's.
-/
module

public import ConRon.Bridge.Core.Walks.Stuck
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.IotaLeaves
public import ConRon.Bridge.Core.Walks.BetaSpine
import ConRon.Bridge.Core.Walks.Iota
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Former
import ConRon.Bridge.Core.Walks.FvarB
import ConRon.Bridge.Core.Walks.Nat
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.ExprOps.Owed
import ConRon.Bridge.Core.Memo
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Deep
import ConLeche.Verify.PropRead
public import ConLeche.Verify.EnvWF
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env} {fe : IFEnv}

/-! ## 1. The gate: `recMajorEta`, `recEtaPartial` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:754-768 recMajorEta — **THEOREM 1
for `recMajorEta`**: pure on both sides, the same two lookups, an equation. -/
theorem recMajorEta_eq {s : AState} (hok : CheckOK eager env fe s)
    {rs : List IRecRule} {drules : List RecRule}
    (hdr : Frontend.denoteRules s.store rs = some drules) :
    ConRon.Arena.recMajorEta fe rs = ConLeche.recMajorEta env.find? drules := by
  have hlen := denoteRules_len hdr
  rcases rs with _ | ⟨rl, _ | ⟨rl2, rs⟩⟩ <;>
    rcases drules with _ | ⟨rl', _ | ⟨rl2', drs⟩⟩ <;>
    simp only [List.length_nil, List.length_cons] at hlen <;>
    try omega
  · rfl
  · have hrl : Frontend.denoteRule s.store rl = some rl' := by
      cases hx : Frontend.denoteRule s.store rl <;>
        simp_all [Frontend.denoteRules]
    obtain ⟨-, hrlc, -, -⟩ := rule_denote hrl
    simp only [ConRon.Arena.recMajorEta, ConLeche.recMajorEta]
    split
    next icv nP nF T hfc =>
      obtain ⟨dcv, -, hfind⟩ := env_ctor_of_index hok hrlc hfc
      have hTn := env_ctor_induct_of_index hok hfc
      rw [hfind]
      dsimp only
      split
      next icvT icaps hfdT =>
        obtain ⟨dcvT, dcaps, -, hdcaps, hfindT⟩ := env_ind_of_index hok hTn hfdT
        rw [hfindT]
        exact ((denoteCaps_fields hdcaps).1).symm
      next hnd =>
        have hnf := env_not_ind_of_index hok hTn (fun v c h => hnd v c h)
        generalize henv : env.find? ((denoteN s.store.ns T).getD default) = o
        match o, henv with
        | some (.indInfo cv caps), henv => exact absurd henv (hnf cv caps)
        | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.ctorInfo _ _ _ _), _
        | some (.defnInfo _ _ _), _ | some (.recInfo _ _ _ _ _), _ | none, _ => rfl
    next hnd =>
      have hnc := env_not_ctor_of_index hok hrlc (fun v p q t h => hnd v p q t h)
      generalize henv : env.find? rl'.ctor = o
      match o, henv with
      | some (.ctorInfo cv p q t), henv => exact absurd henv (hnc cv p q t)
      | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.indInfo _ _), _
      | some (.defnInfo _ _ _), _ | some (.recInfo _ _ _ _ _), _ | none, _ => rfl
  · rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:770-786 recEtaPartial
con-leche: ConLeche/Cached/StateC.lean:108-118 recEtaPartialC — **THEOREM 1
for `recEtaPartial`**: read-only, an equation with con-leche's reader; the
spine is counted (`numArgs`, `Expr.numArgs_eq_length`). -/
theorem recEtaPartial_spec (s₀ : AState) (b : EIdx) (y : Expr)
    (hok : CheckOK eager env fe s₀) (hdb : denoteE s₀.store b = some y) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.recEtaPartial fe b
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.recEtaPartial env y; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.recEtaPartial ConLeche.recEtaPartial
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ b hok.state (by rw [hdb]; rfl)) ?_
  rintro hd s1 ⟨rfl, hrelF⟩
  have hdd : denoteE s1.store hd = some y.getAppFn := hrelF y hdb
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
  cases vh
  case const c us =>
    obtain ⟨cn, ls, hgf, hcn, -⟩ := denote_const_inv hwf hvh hdd
    rw [hgf]
    dsimp only
    split
    next icv mI rP isK rules hfc =>
      obtain ⟨dcv, drules, -, hdr, hfind⟩ := env_rec_of_index hok hcn hfc
      rw [hfind]
      dsimp only
      refine triple_seq (numArgs_specA coreWalkFuel s1 b hok (by rw [hdb]; rfl)) ?_
      rintro n s2 ⟨rfl, hn⟩
      rw [hdb] at hn
      have hn' : n = y.getAppArgs.length := by
        simp only [Option.map_some, Option.some.injEq] at hn
        rw [← hn, Expr.numArgs_eq_length]
      subst hn'
      rw [← recMajorEta_eq hok hdr]
      by_cases hl : y.getAppArgs.length ≤ mI
      · rw [ite_eq_left hl]
        cases isK
        · simp only [Bool.false_eq_true, ite_false, false_or]
          by_cases hm : ConRon.Arena.recMajorEta fe rules = true
          · rw [ite_eq_left hm, ite_eq_left (show _ ∧ _ from ⟨hl, hm⟩)]
            exact triple_pureS ⟨rfl, rfl⟩
          · rw [ite_eq_right hm, ite_eq_right (show ¬ (_ ∧ _) from fun h => hm h.2)]
            exact triple_pureS ⟨rfl, rfl⟩
        · simp only [ite_true, true_or, and_true, hl]
          exact triple_pureS ⟨rfl, rfl⟩
      · rw [ite_eq_right hl, ite_eq_right (show ¬ (_ ∧ _) from fun h => hl h.1)]
        exact triple_pureS ⟨rfl, rfl⟩
    next hnd =>
      have hnr := env_not_rec_of_index hok hcn (fun v mI rP k rs h => hnd v mI rP k rs h)
      refine triple_pureS ⟨rfl, ?_⟩
      generalize henv : env.find? cn = o
      match o, henv with
      | some (.recInfo cv mI rP k rs), henv => exact absurd henv (hnr cv mI rP k rs)
      | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.indInfo _ _), _
      | some (.defnInfo _ _ _), _ | some (.ctorInfo _ _ _ _), _ | none, _ => rfl
  all_goals
    dsimp only
    refine triple_pureS ⟨rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    generalize y.getAppFn = g at hnc ⊢
    cases g <;> first | rfl | exact absurd rfl (hnc _ _)

/-! ## 2. The ι step at a spine -/

/-- con-leche: ConLeche/Kernel/Core.lean:867-965 iotaRec
con-leche: ConLeche/Cached/CoreC.lean:1073-1087 iotaRecAtI — **THEOREM 1 for
`iotaRecSpine`**: the head and the arguments read off the spine
(`headAndArgs_spec`), then the ι step at them (`whnfAppIota_specE`). -/
theorem iotaRecSpine_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (s₀ : AState) (d : Nat) (e : EIdx) (E : Expr)
    (hok : CheckOK eager env fe s₀) (hde : denoteE s₀.store e = some E)
    (hw : Expr.WScoped d E) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.iotaRecSpine .verified (coreKnot .verified eager fe id fuel) fe d e
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d E) d
          s'.store r; ⊤⦄ := by
  unfold ConRon.Arena.iotaRecSpine
  refine triple_seq (headAndArgs_spec s₀ e E hok.state hde) ?_
  rintro ⟨hd, args⟩ s1 ⟨rfl, h1, h2⟩
  exact whnfAppIota_specE henv hsim _ d hd args E hok h1 h2 hw

/-! ## 3. `recEtaTele`: the pure side at its exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:967-996 recEtaTele — no argument
missing, the ι step does not fire. -/
theorem recEtaTeleFueled_zero_none {F d : Nat} {x t : Expr}
    (h : ConLeche.iotaRecFueled .verified eager env F d x = .ok none) :
    ConLeche.recEtaTeleFueled .verified eager env F 0 d x t = .ok none := by
  have h' : ConLeche.iotaRec .verified (ConLeche.pureFns .verified eager env F) env d x
      = .ok none := h
  simp only [ConLeche.recEtaTeleFueled, ConLeche.recEtaTele, h', bind, Except.bind,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:967-996 recEtaTele — no argument
missing, the ι step fires, and the typing certificate decides. -/
theorem recEtaTeleFueled_zero_some {F1 F2 F3 d : Nat} {x t e te : Expr} {b : Bool}
    (h1 : ConLeche.iotaRecFueled .verified eager env F1 d x = .ok (some e))
    (h2 : ConLeche.inferTypeCore .verified eager env F2 d e = .ok te)
    (h3 : ConLeche.isDefEqCore .verified eager env F3 d te t = .ok b) :
    ConLeche.recEtaTeleFueled .verified eager env (F1 + F2 + F3) 0 d x t =
      .ok (if b then some e else none) := by
  have h1' : ConLeche.iotaRec .verified (ConLeche.pureFns .verified eager env (F1 + F2 + F3))
      env d x = .ok (some e) := ConLeche.iotaRec_mono (by omega) h1
  have h2' : (ConLeche.pureFns .verified eager env (F1 + F2 + F3)).infer d e = .ok te :=
    ConLeche.inferTypeCore_mono (by omega) h2
  have h3' : (ConLeche.pureFns .verified eager env (F1 + F2 + F3)).defeq d te t = .ok b :=
    ConLeche.isDefEqCore_mono (by omega) h3
  simp only [ConLeche.recEtaTeleFueled, ConLeche.recEtaTele, h1', h2', h3', bind, Except.bind,
    CheckMode.verifiedChecks, ite_true]
  cases b <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:967-996 recEtaTele — an argument
missing, and the type does not reduce to a `∀`. -/
theorem recEtaTeleFueled_nopi {F k d : Nat} {x t w : Expr}
    (h : ConLeche.whnf .verified eager env F d t = .ok w)
    (hw : ∀ dom body, w ≠ .forallE dom body) :
    ConLeche.recEtaTeleFueled .verified eager env F (k + 1) d x t = .ok none := by
  have h' : (ConLeche.pureFns .verified eager env F).whnf d t = .ok w := h
  simp only [ConLeche.recEtaTeleFueled, ConLeche.recEtaTele, h', bind, Except.bind]
  cases w <;> first | rfl | exact absurd rfl (hw _ _)

/-- con-leche: ConLeche/Kernel/Core.lean:967-996 recEtaTele — a `∀`: the
expansion one binder down, abstracted back into a λ. -/
theorem recEtaTeleFueled_pi {F1 F2 k d : Nat} {x t dom body : Expr} {o : Option Expr}
    (h1 : ConLeche.whnf .verified eager env F1 d t = .ok (.forallE dom body))
    (h2 : ConLeche.recEtaTeleFueled .verified eager env F2 k (d + 1) (.app x (.fvar d dom))
      (body.instantiate1 (.fvar d dom)) = .ok o) :
    ConLeche.recEtaTeleFueled .verified eager env (F1 + F2) (k + 1) d x t =
      .ok (o.map fun e => .lam dom (e.abstract1 d)) := by
  have h1' : (ConLeche.pureFns .verified eager env (F1 + F2)).whnf d t = .ok (.forallE dom body) :=
    ConLeche.whnf_mono (by omega) h1
  have h2' : ConLeche.recEtaTele .verified (ConLeche.pureFns .verified eager env (F1 + F2)) env
      k (d + 1) (.app x (.fvar d dom)) (body.instantiate1 (.fvar d dom)) = .ok o :=
    recEtaTeleFueled_mono (by omega) h2
  simp only [ConLeche.recEtaTeleFueled, ConLeche.recEtaTele, h1', h2', bind, Except.bind]
  cases o <;> rfl

/-! ## 4. `recEtaTele`: the walk -/

/-- con-leche: ConLeche/Kernel/Core.lean:967-996 recEtaTele
con-leche: ConLeche/Cached/CoreC.lean:1089-1114 recEtaTeleI — **THEOREM 1 for
`recEtaTele`**: by induction on the missing arguments; at `0` the ι step at the
spine and the typing certificate, at `k + 1` the type head-normalised, opened
at the next free variable, the expansion one binder down and its answer
abstracted into a λ (`abstract1Fast`, `internLamE`).  The answer's scoping is
con-leche's `recEtaTele_WScoped`. -/
theorem recEtaTele_spec {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel) :
    ∀ (k d : Nat) (s₀ : AState) (f T : EIdx) (x t : Expr), CheckOK eager env fe s₀ →
      denoteE s₀.store f = some x → denoteE s₀.store T = some t →
      Expr.WScoped d x → Expr.WScoped d t →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.recEtaTele .verified (coreKnot .verified eager fe id fuel) fe k d f T
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
          SimOOp (fun F => ConLeche.recEtaTeleFueled .verified eager env F k d x t) d
            s'.store r; ⊤⦄ := by
  have hscope : ∀ {F k d : Nat} {x t e : Expr},
      ConLeche.recEtaTeleFueled .verified eager env F k d x t = .ok (some e) →
      Expr.WScoped d x → Expr.WScoped d t → Expr.WScoped d e :=
    fun {F k d x t e} h hx ht => ConLeche.recEtaTele_WScoped (fuel := F) henv k d h hx ht
  intro k
  induction k with
  | zero =>
    intro d s₀ f T x t hok hdf hdt hwx hwt
    simp only [ConRon.Arena.recEtaTele]
    refine triple_seq (iotaRecSpine_spec henv hsim s₀ d f x hok hdf hwx) ?_
    rintro o s1 ⟨hok1, hx1, hp1, ve, hve, -, F1, hF1⟩
    cases o with
    | none =>
      simp only [denoteEO, Option.some.injEq] at hve
      subst hve
      exact triple_pureC ⟨hok1, hx1, hp1, simOOp_none (recEtaTeleFueled_zero_none hF1)⟩
    | some e =>
      dsimp only
      obtain ⟨ex, hde⟩ : ∃ ex, denoteE s1.store e = some ex := by
        cases h : denoteE s1.store e with
        | none => simp [denoteEO, h] at hve
        | some v => exact ⟨v, rfl⟩
      obtain rfl : ve = some ex := by
        simp only [denoteEO, hde, Option.map_some, Option.some.injEq] at hve
        exact hve.symm
      have hwe : Expr.WScoped d ex := ConLeche.iotaRec_WScoped henv hF1 hwx
      simp only [CheckMode.verifiedChecks, ite_true]
      refine triple_seq (hsim.infer s1 d e ex hok1 hde hwe) ?_
      rintro te s2 ⟨hok2, hx2, hp2, vte, hdte, hwte, F2, hF2⟩
      refine triple_seq (hsim.defeq s2 d te T vte t hok2 hdte
        (denote_ext hdt (hx1.trans hx2)) hwte hwt) ?_
      rintro b s3 ⟨hok3, hx3, hp3, F3, hF3⟩
      have hval := recEtaTeleFueled_zero_some (t := t) hF1 hF2 hF3
      have hx03 := hx1.trans (hx2.trans hx3)
      have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp1)
      cases b
      · exact triple_pureC ⟨hok3, hx03, hp03, simOOp_none hval⟩
      · refine triple_pureC ⟨hok3, hx03, hp03, some ex, ?_, ?_, _, hval⟩
        · simp [denoteEO, denote_ext hde (hx2.trans hx3)]
        · intro y hy; cases hy; exact hwe
  | succ k ih =>
    intro d s₀ f T x t hok hdf hdt hwx hwt
    simp only [ConRon.Arena.recEtaTele]
    refine triple_seq (hsim.whnf s₀ d T t hok hdt hwt) ?_
    rintro w s1 ⟨hok1, hx1, hp1, vw, hdw, hww, F1, hF1⟩
    have hwf1 := hok1.state.wf
    by_cases htag : w.tag = ETag.forallE
    · rw [ite_eq_left (by simpa using htag)]
      refine triple_seq (viewBind_spec s1 w) ?_
      rintro rv s2 ⟨hs2, hrv⟩
      subst s2 rv
      cases hvt : s1.store.viewBind w with
      | none => exact triple_failDanglingE
      | some p =>
      obtain ⟨dom, body⟩ := p
      dsimp only
      obtain ⟨tdom, tbody, rfl, hdom, hbody⟩ :=
        denote_forallE_inv hwf1 (view_of_viewBind_forallE htag hvt) hdw
      have hwdom : Expr.WScoped d tdom := by
        simp only [Expr.WScoped] at hww; exact hww.1
      -- the next free variable
      refine triple_seq (internE_specC s1 (.fvar d dom) hok1
        (viewOK_fvar (by rw [hdom]; rfl))) ?_
      rintro fv s2 ⟨hok2, hx2, hp2, hfv⟩
      have hfv' : denoteE s2.store fv = some (.fvar d tdom) := by
        rw [hfv]; simp [denoteEView, denote_ext hdom hx2]
      -- the type's body, opened at it
      refine triple_seq (instantiate1Fast_ok_spec s2 body fv tbody (.fvar d tdom) hok2
        (denote_ext hbody hx2) hfv') ?_
      rintro body2 s3 ⟨hok3, hx3, hp3, hbody2⟩
      -- the spine, applied to it
      refine triple_seq (internE_specC s3 (.app f fv) hok3
        (viewOK_app (by rw [denote_ext hdf (hx1.trans (hx2.trans hx3))]; rfl)
          (by rw [denote_ext hfv' hx3]; rfl))) ?_
      rintro f2 s4 ⟨hok4, hx4, hp4, hf2⟩
      have hf2' : denoteE s4.store f2 = some (.app x (.fvar d tdom)) := by
        rw [hf2]
        simp [denoteEView, opt2, denote_ext hdf (hx1.trans (hx2.trans (hx3.trans hx4))),
          denote_ext hfv' (hx3.trans hx4)]
      have hx04 : Ext s₀.store s4.store := hx1.trans (hx2.trans (hx3.trans hx4))
      have hp04 : s4.pins = s₀.pins := hp4.trans (hp3.trans (hp2.trans hp1))
      -- one binder down
      have hwx2 : Expr.WScoped (d + 1) (.app x (.fvar d tdom)) := by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (by omega) hwx, by omega, hwdom⟩
      have hwb2 : Expr.WScoped (d + 1) (tbody.instantiate1 (.fvar d tdom)) := by
        simp only [Expr.WScoped] at hww
        exact Expr.WScoped.instantiate1 hww.1 0 hww.2
      refine triple_seq (ih (d + 1) s4 f2 body2 _ _ hok4 hf2'
        (denote_ext hbody2 hx4) hwx2 hwb2) ?_
      rintro o s5 ⟨hok5, hx5, hp5, ve, hve, -, F2, hF2⟩
      have hval := recEtaTeleFueled_pi (k := k) (x := x) hF1 hF2
      cases o with
      | none =>
        simp only [denoteEO, Option.some.injEq] at hve
        subst hve
        exact triple_pureC ⟨hok5, hx04.trans hx5, hp5.trans hp04, simOOp_none hval⟩
      | some e =>
        dsimp only
        obtain ⟨ex, hde⟩ : ∃ ex, denoteE s5.store e = some ex := by
          cases h : denoteE s5.store e with
          | none => simp [denoteEO, h] at hve
          | some v => exact ⟨v, rfl⟩
        obtain rfl : ve = some ex := by
          simp only [denoteEO, hde, Option.map_some, Option.some.injEq] at hve
          exact hve.symm
        refine triple_seq (ExprOps.abstract1Fast_spec fvarBSpec coreWalkFuel s5 e d 0
          hok5.state (by rw [hde]; rfl)) ?_
        rintro ea s6 ⟨hso6, hx6, hc6, hp6, _, hrel⟩
        have hok6 := hok5.mono hso6 hx6 hc6 hp6
        have hdea : denoteE s6.store ea = some (ex.abstract1 d 0) := hrel ex hde
        have hdom6 : denoteE s6.store dom = some tdom :=
          denote_ext hdom (hx2.trans (hx3.trans (hx4.trans (hx5.trans hx6))))
        refine triple_seq (internLamE_spec s6 dom ea hok6.state.wf
          (by rw [hdom6]; rfl) (by rw [hdea]; rfl)) ?_
        rintro lam s7 ⟨hwf7, hx7, _, _, _, hc7, hp7, _, hd7⟩
        have hok7 := hok6.mono ⟨hwf7⟩ hx7 hc7 hp7
        have hdl : denoteE s7.store lam = some (.lam tdom (ex.abstract1 d)) := by
          rw [hd7]
          simp [denoteEView, denote_ext hdom6 hx7, denote_ext hdea hx7]
        refine triple_pureC ⟨hok7, hx04.trans (hx5.trans (hx6.trans hx7)),
          hp7.trans (hp6.trans (hp5.trans hp04)), some (.lam tdom (ex.abstract1 d)), ?_, ?_,
          _, hval⟩
        · simp [denoteEO, hdl]
        · intro y hy
          cases hy
          exact hscope hval hwx hwt
    · rw [ite_eq_right (by simpa using htag)]
      refine triple_pureC ⟨hok1, hx1, hp1, simOOp_none (recEtaTeleFueled_nopi (k := k) (x := x)
        hF1 ?_)⟩
      intro dom body hvw
      subst hvw
      exact htag (by rw [tag_of_denote hwf1 hdw]; rfl)

/-! ## 5. `recEtaCert` -/

/-- con-leche: ConLeche/Kernel/Core.lean:998-1015 recEtaCert — its answer at
two subjects. -/
def RecEtaE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x y : Expr) (r : Bool) :
    Prop :=
  SimBOp (fun F => ConLeche.recEtaCertFueled mode eager env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:998-1015 recEtaCert — the first side
is not neutral. -/
theorem recEtaCertFueled_notNeutral {F d : Nat} {x y : Expr} (hn : x.ioNeutral = false) :
    ConLeche.recEtaCertFueled .verified eager env F d x y = .ok false := by
  simp only [ConLeche.recEtaCertFueled, ConLeche.recEtaCert, hn, Bool.not_false, ite_true]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:998-1015 recEtaCert — the other side
is no partially applied recursor that η-expands. -/
theorem recEtaCertFueled_nopartial {F d : Nat} {x y : Expr} (hn : x.ioNeutral = true)
    (hp : ConLeche.recEtaPartial env y = none) :
    ConLeche.recEtaCertFueled .verified eager env F d x y = .ok false := by
  simp only [ConLeche.recEtaCertFueled, ConLeche.recEtaCert, hn, hp, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:998-1015 recEtaCert — the expansion
along the io-grade type: no λ, or the other side compared with it. -/
theorem recEtaCertFueled_tele {F1 F2 d k : Nat} {x y ty : Expr} {o : Option Expr}
    (hn : x.ioNeutral = true) (hp : ConLeche.recEtaPartial env y = some k)
    (h1 : ConLeche.inferTypeIO .verified eager env F1 d y = .ok ty)
    (h2 : ConLeche.recEtaTeleFueled .verified eager env F2 k d y ty = .ok o) :
    ConLeche.recEtaCertFueled .verified eager env (F1 + F2) d x y =
      match o with
      | some lam => ConLeche.isDefEqCore .verified eager env (F1 + F2) d x lam
      | none => .ok false := by
  have h1' : (ConLeche.pureFns .verified eager env (F1 + F2)).inferIO d y = .ok ty :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have h2' : ConLeche.recEtaTele .verified (ConLeche.pureFns .verified eager env (F1 + F2)) env
      k d y ty = .ok o := recEtaTeleFueled_mono (by omega) h2
  simp only [ConLeche.recEtaCertFueled, ConLeche.recEtaCert, hn, hp, Bool.not_true,
    Bool.false_eq_true, ite_false, h1', h2', bind, Except.bind]
  cases o <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:998-1015 recEtaCert
con-leche: ConLeche/Cached/CoreC.lean:1116-1127 recEtaCertI — **THEOREM 1 for
`recEtaCert`**: the first side neutral (`ioNeutral_spec`), the gate
(`recEtaPartial_spec`), the other side's io-grade type, the reduced expansion
along it (`recEtaTele_spec`), and the comparison with the λ. -/
theorem recEtaCert_spec {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.recEtaCert .verified (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ RecEtaE .verified eager env d x y r; ⊤⦄ := by
  unfold ConRon.Arena.recEtaCert
  refine triple_seq (ioNeutral_spec s₀ a x hok hda) ?_
  rintro nb s1 ⟨hs1, rfl⟩
  subst s1
  cases hn : x.ioNeutral
  · simp only [Bool.not_false, ite_true]
    exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, recEtaCertFueled_notNeutral hn⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    refine triple_seq (recEtaPartial_spec s₀ b y hok hdb) ?_
    rintro op s2 ⟨hs2, rfl⟩
    subst s2
    cases hp : ConLeche.recEtaPartial env y with
    | none => exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, recEtaCertFueled_nopartial hn hp⟩
    | some k =>
      dsimp only
      refine triple_seq (hsim.inferIO s₀ d b y hok hdb hwb) ?_
      rintro tb s3 ⟨hok3, hx3, hp3, vtb, hdtb, hwtb, F1, hF1⟩
      refine triple_seq (recEtaTele_spec henv hsim k d s3 b tb y vtb hok3
        (denote_ext hdb hx3) hdtb hwb hwtb) ?_
      rintro o s4 ⟨hok4, hx4, hp4, ve, hve, hws, F2, hF2⟩
      have hval := recEtaCertFueled_tele (x := x) hn hp hF1 hF2
      cases o with
      | none =>
        simp only [denoteEO, Option.some.injEq] at hve
        subst hve
        exact triple_pureC ⟨hok4, hx3.trans hx4, hp4.trans hp3, _, hval⟩
      | some lam =>
        dsimp only
        obtain ⟨vl, hdl⟩ : ∃ vl, denoteE s4.store lam = some vl := by
          cases h : denoteE s4.store lam with
          | none => simp [denoteEO, h] at hve
          | some v => exact ⟨v, rfl⟩
        obtain rfl : ve = some vl := by
          simp only [denoteEO, hdl, Option.map_some, Option.some.injEq] at hve
          exact hve.symm
        refine triple_mono (hsim.defeq s4 d a lam x vl hok4
          (denote_ext hda (hx3.trans hx4)) hdl hwa (hws vl rfl)) ?_
        rintro r s5 ⟨hok5, hx5, hp5, F3, hF3⟩
        refine ⟨hok5, hx3.trans (hx4.trans hx5), hp5.trans (hp4.trans hp3),
          F1 + F2 + F3, ?_⟩
        have hval' := recEtaCertFueled_tele (x := x) hn hp
          (ConLeche.inferTypeIO_mono (show F1 ≤ F1 + F3 by omega) hF1) hF2
        rw [show F1 + F3 + F2 = F1 + F2 + F3 by omega] at hval'
        show ConLeche.recEtaCertFueled .verified eager env (F1 + F2 + F3) d x y = .ok r
        rw [hval']
        exact ConLeche.isDefEqCore_mono (by omega) hF3

/-- con-leche: ConLeche/Kernel/Core.lean:998-1015 recEtaCert —
`recEtaCert_spec` in answer shape (`PairAns` of `RecEtaE`). -/
theorem recEtaCert_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.recEtaCert .verified (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (RecEtaE .verified eager env d) (denoteE s₀.store a) (denoteE s₀.store b) r;
      ⊤⦄ := by
  cases ha : denoteE s₀.store a with
  | none => rw [ha] at hda; exact hda.elim
  | some x =>
  cases hb : denoteE s₀.store b with
  | none => rw [hb] at hdb; exact hdb.elim
  | some y =>
  rw [ha, DenWS.some_eq] at hda; rw [hb, DenWS.some_eq] at hdb
  exact recEtaCert_spec henv hsim s₀ d a b x y hok ha hb hda hdb

/-! ## 6. `stuckIrrel`: the pure side at its six exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel — the step
equation, the six certificates in order. -/
theorem stuckIrrelFueled_eq {F d : Nat} {x y : Expr} :
    ConLeche.stuckIrrelFueled .verified eager env F d x y =
      (do
        if ← ConLeche.recEtaCertFueled .verified eager env F d x y then pure true
        else if ← ConLeche.recEtaCertFueled .verified eager env F d y x then pure true
        else if ← ConLeche.structEtaCertFueled .verified eager env F d x y then pure true
        else if ← ConLeche.structEtaCertFueled .verified eager env F d y x then pure true
        else if ← ConLeche.structUnitCertFueled .verified eager env F d x y then pure true
        else ConLeche.proofIrrelFueled .verified eager env F d x y : CheckM Bool) := rfl

/-! ## 7. `stuckIrrel`: the walk

The six exits as `grind` lemmas over the children's named answers (the fuel
merge inside each). -/

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel — recursor η,
first orientation. -/
@[bridge_grind ←] theorem StuckE.rec1 {d : Nat} {x y : Expr}
    (h : RecEtaE .verified eager env d x y true) : StuckE .verified eager env d x y true := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, by dsimp only at hF ⊢; rw [stuckIrrelFueled_eq, hF]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel — recursor η,
second orientation. -/
@[bridge_grind ←] theorem StuckE.rec2 {d : Nat} {x y : Expr}
    (h1 : RecEtaE .verified eager env d x y false) (h2 : RecEtaE .verified eager env d y x true) :
    StuckE .verified eager env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  refine ⟨F1 + F2, ?_⟩
  dsimp only at *
  rw [stuckIrrelFueled_eq, recEtaCertFueled_mono (by omega) hF1,
    recEtaCertFueled_mono (by omega) hF2]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel — the first
structure-η direction certifies. -/
@[bridge_grind ←] theorem StuckE.eta1 {d : Nat} {x y : Expr}
    (h1 : RecEtaE .verified eager env d x y false) (h2 : RecEtaE .verified eager env d y x false)
    (h3 : EtaCertE .verified eager env d x y true) : StuckE .verified eager env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨F1 + F2 + F3, ?_⟩
  dsimp only at *
  rw [stuckIrrelFueled_eq, recEtaCertFueled_mono (by omega) hF1,
    recEtaCertFueled_mono (by omega) hF2, structEtaCertFueled_mono (by omega) hF3]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel — the second
structure-η direction certifies. -/
@[bridge_grind ←] theorem StuckE.eta2 {d : Nat} {x y : Expr}
    (h1 : RecEtaE .verified eager env d x y false) (h2 : RecEtaE .verified eager env d y x false)
    (h3 : EtaCertE .verified eager env d x y false) (h4 : EtaCertE .verified eager env d y x true) :
    StuckE .verified eager env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  obtain ⟨F4, hF4⟩ := h4
  refine ⟨F1 + F2 + F3 + F4, ?_⟩
  dsimp only at *
  rw [stuckIrrelFueled_eq, recEtaCertFueled_mono (by omega) hF1,
    recEtaCertFueled_mono (by omega) hF2, structEtaCertFueled_mono (by omega) hF3,
    structEtaCertFueled_mono (by omega) hF4]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel — unit-likeness
certifies. -/
@[bridge_grind ←] theorem StuckE.unit {d : Nat} {x y : Expr}
    (h1 : RecEtaE .verified eager env d x y false) (h2 : RecEtaE .verified eager env d y x false)
    (h3 : EtaCertE .verified eager env d x y false) (h4 : EtaCertE .verified eager env d y x false)
    (h5 : UnitCertE .verified eager env d x y true) : StuckE .verified eager env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  obtain ⟨F4, hF4⟩ := h4
  obtain ⟨F5, hF5⟩ := h5
  refine ⟨F1 + F2 + F3 + F4 + F5, ?_⟩
  dsimp only at *
  rw [stuckIrrelFueled_eq, recEtaCertFueled_mono (by omega) hF1,
    recEtaCertFueled_mono (by omega) hF2, structEtaCertFueled_mono (by omega) hF3,
    structEtaCertFueled_mono (by omega) hF4, structUnitCertFueled_mono (by omega) hF5]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel — none of the
five certifies, so proof irrelevance decides. -/
@[bridge_grind ←] theorem StuckE.proof {d : Nat} {x y : Expr} {r : Bool}
    (h1 : RecEtaE .verified eager env d x y false) (h2 : RecEtaE .verified eager env d y x false)
    (h3 : EtaCertE .verified eager env d x y false) (h4 : EtaCertE .verified eager env d y x false)
    (h5 : UnitCertE .verified eager env d x y false) (h6 : PIrrelE .verified eager env d x y r) :
    StuckE .verified eager env d x y r := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  obtain ⟨F4, hF4⟩ := h4
  obtain ⟨F5, hF5⟩ := h5
  obtain ⟨F6, hF6⟩ := h6
  refine ⟨F1 + F2 + F3 + F4 + F5 + F6, ?_⟩
  dsimp only at *
  rw [stuckIrrelFueled_eq, recEtaCertFueled_mono (by omega) hF1,
    recEtaCertFueled_mono (by omega) hF2, structEtaCertFueled_mono (by omega) hF3,
    structEtaCertFueled_mono (by omega) hF4, structUnitCertFueled_mono (by omega) hF5]
  exact proofIrrelFueled_mono (by omega) hF6

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel
con-leche: ConLeche/Cached/CoreC.lean:1129-1138 stuckIrrelI — the walk in
answer shape (`StuckE`). -/
theorem stuckIrrel_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.stuckIrrel .verified (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ StuckE .verified eager env d x y r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.stuckIrrel, recEtaCert_specA henv hsim, structEtaCert_specA henv hsim,
      structUnitCert_specA henv hsim, proofIrrel_specA hsim] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:1017-1028 stuckIrrel
con-leche: ConLeche/Cached/CoreC.lean:1129-1138 stuckIrrelI — **THEOREM 1 for
`stuckIrrel`**, the fallback at two stuck terms: recursor η in both
directions, structure-η in both directions, then the unit certificate, then
proof irrelevance (`stuckIrrel_specA`; `StuckE` is `SimBOp` at the pure
call). -/
theorem stuckIrrel_spec {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.stuckIrrel .verified (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.stuckIrrelFueled .verified eager env F d x y) r; ⊤⦄ :=
  stuckIrrel_specA henv hsim s₀ d a b x y hok hda hdb hwa hwb

/-! ## 8. The axiom census -/

section Census

#print axioms recMajorEta_eq
#print axioms recEtaPartial_spec
#print axioms iotaRecSpine_spec
#print axioms recEtaTele_spec
#print axioms recEtaCert_spec
#print axioms stuckIrrel_specA
#print axioms stuckIrrel_spec

end Census

end ConRon.Bridge.Core
