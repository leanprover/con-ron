/-
# `ConRon.Bridge.Core.Walks.ProjCore` — the projection rule on a reduced scrutinee

Task #109.  con-leche 8afe1815 split the projection rule out of
`whnfCoreBody`'s `.proj` clause into `reduceProjCore` (the official kernel's
`reduce_proj_core`), which two callers share: `whnfCoreBody` (after reducing
the scrutinee by `whnf`, or by the cheap `whnfCore`) and the definitional
equality's `lazyDeltaProjReduction`.  The twin ports it as one walk, so this
module proves it once, as a standalone walk theorem both callers apply.

| theorem | what it is |
|---|---|
| `reduceProjCore_none` … `reduceProjCore_fire` | con-leche's five exits, one equation each |
| `reduceProjCoreFueled_mono` | fuel monotonicity, from con-leche's `reduceProjCore_mono` |
| `reduceProjCore_spec` | **THEOREM 1 for `reduceProjCore`**, in `SimOOp` form |

The walk is the `.proj` clause's former stages 2–9 (`Arms/WhnfCore.lean`
before task #109): `projLitToCtor_spec`, `IFEnv.findProj?_spec`,
`getAppFn_spec`, the head's `view`, `getAppArgs_spec`, `viewLsLen`,
`IProjEntry.fireOk_spec`, the guard, `internE (.bvar 0)`, `projCertAt_spec`.
-/
import ConRon.Bridge.Core.Walks.ProjLit
import ConLeche.Verify.BetaSpine

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. The five exits of con-leche's `reduceProjCore` -/

/-- con-leche: ConLeche/Kernel/Core.lean:978-1010 reduceProjCore — **no table
entry**: the rule does not fire. -/
theorem reduceProjCore_none {F d i : Nat} {sn : Name} {c e' : Expr}
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d c
      = .ok e')
    (ht : env.findProj? sn i = none) :
    ConLeche.reduceProjCoreFueled mode env F d sn i c = .ok none := by
  simp only [ConLeche.reduceProjCoreFueled, ConLeche.reduceProjCore, hl, ht,
    bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:978-1010 reduceProjCore — the table
fires but **the scrutinee's head is not a constant**. -/
theorem reduceProjCore_head {F d i : Nat} {sn : Name} {c e' : Expr}
    {entry : ProjEntry}
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d c
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : ∀ k us, e'.getAppFn ≠ .const k us) :
    ConLeche.reduceProjCoreFueled mode env F d sn i c = .ok none := by
  simp only [ConLeche.reduceProjCoreFueled, ConLeche.reduceProjCore, hl, ht,
    bind, Except.bind]
  first
    | rfl
    | (split
       · rename_i k us heq; exact absurd heq (hh k us)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:996-1008 reduceProjCore — the table
fires but **a guard fails**. -/
theorem reduceProjCore_guard {F d i : Nat} {sn : Name} {c e' : Expr}
    {entry : ProjEntry} {k : Name} {us : List Level}
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d c
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : e'.getAppFn = .const k us)
    (hg : ¬ (k = entry.ctor ∧ i < entry.numFields ∧
      e'.getAppArgs.length = entry.numParams + entry.numFields ∧
      us.length = entry.levelParams.length ∧ entry.fireOk us = true)) :
    ConLeche.reduceProjCoreFueled mode env F d sn i c = .ok none := by
  simp only [ConLeche.reduceProjCoreFueled, ConLeche.reduceProjCore, hl, ht,
    hh, bind, Except.bind]
  rw [ite_eq_right hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:996-1008 reduceProjCore — the table
fires and **the certificate fails**. -/
theorem reduceProjCore_cert_false {F d i : Nat} {sn : Name} {c e' : Expr}
    {entry : ProjEntry} {k : Name} {us : List Level}
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d c
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : e'.getAppFn = .const k us)
    (hg : k = entry.ctor ∧ i < entry.numFields ∧
      e'.getAppArgs.length = entry.numParams + entry.numFields ∧
      us.length = entry.levelParams.length ∧ entry.fireOk us = true)
    (hcert : ConLeche.projCertAt (ConLeche.pureFns mode env F) env d
      mode.verifiedChecks mode.betaGate k us e'.getAppArgs = .ok false) :
    ConLeche.reduceProjCoreFueled mode env F d sn i c = .ok none := by
  simp only [ConLeche.reduceProjCoreFueled, ConLeche.reduceProjCore, hl, ht,
    hh, bind, Except.bind]
  rw [ite_eq_left hg, hcert]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:996-1008 reduceProjCore — the table
fires, the guards hold and **the certificate succeeds**: the selected
field. -/
theorem reduceProjCore_fire {F d i : Nat} {sn : Name} {c e' : Expr}
    {entry : ProjEntry} {k : Name} {us : List Level}
    (hl : ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d c
      = .ok e')
    (ht : env.findProj? sn i = some entry)
    (hh : e'.getAppFn = .const k us)
    (hg : k = entry.ctor ∧ i < entry.numFields ∧
      e'.getAppArgs.length = entry.numParams + entry.numFields ∧
      us.length = entry.levelParams.length ∧ entry.fireOk us = true)
    (hcert : ConLeche.projCertAt (ConLeche.pureFns mode env F) env d
      mode.verifiedChecks mode.betaGate k us e'.getAppArgs = .ok true) :
    ConLeche.reduceProjCoreFueled mode env F d sn i c =
      .ok (some (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0))) := by
  simp only [ConLeche.reduceProjCoreFueled, ConLeche.reduceProjCore, hl, ht,
    hh, bind, Except.bind]
  rw [ite_eq_left hg, hcert]
  rfl

/-- con-leche: ConLeche/Verify/BetaSpine.lean:466 reduceProjCore_mono — at
the pure knot. -/
theorem reduceProjCoreFueled_mono {F F' d i : Nat} {sn : Name} {c : Expr}
    (hle : F ≤ F') {o : Option Expr}
    (h : ConLeche.reduceProjCoreFueled mode env F d sn i c = .ok o) :
    ConLeche.reduceProjCoreFueled mode env F' d sn i c = .ok o :=
  ConLeche.reduceProjCore_mono hle h

/-- con-leche: none — an in-range `getD` is the element, whatever the
default (the twin's default is an interned `.bvar 0` handle, con-leche's the
term `.bvar 0`). -/
theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {a : α}
    (h : i < l.length) : l.getD i a = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## 2. The walk theorem -/

/-- con-leche: ConLeche/Kernel/Core.lean:978-1010 reduceProjCore — **THEOREM
1 for `reduceProjCore`**: at a scrutinee handle `c` denoting a well-scoped
`ce` and a structure name `sn` denoting `nm`, the twin's projection rule
answers what con-leche's `reduceProjCore` answers at some fuel — `none` when
the rule does not fire, and otherwise the selected field, well-scoped.  The
walk both `whnfCoreBody`'s `.proj` clause and `lazyDeltaProjReduction`
consume. -/
theorem reduceProjCore_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (sn : NIdx) (k : Nat) (c : EIdx)
    (nm : Name) (ce : Expr)
    (hok : CheckOK mode env fe s₀) (hsn : denoteN s₀.store.ns sn = some nm)
    (hden : denoteE s₀.store c = some ce) (hw : Expr.WScoped d ce) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.reduceProjCore mode (coreKnot mode fe id fuel) fe d sn k c
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.reduceProjCoreFueled mode env F d nm k ce) d
          s'.store r; ⊤⦄ := by
  unfold ConRon.Arena.reduceProjCore
  -- stage 1: the string-literal expansion
  refine triple_seq (projLitToCtor_spec hsim s₀ d c ce hok hden hw) ?_
  rintro e' s2 ⟨hok2, hx2, hp2, v', hv', hwv', F2, hF2⟩
  have hsn2 : denoteN s2.store.ns sn = some nm := denoteN_ext hsn hx2
  have hplc : ConLeche.projLitToCtor (ConLeche.pureFns mode env F2) env d ce
      = .ok v' := hF2
  -- the `none` exit, shared by four of the five exits
  have hnone : ∀ (s : AState), CheckOK mode env fe s →
      Ext s₀.store s.store → s.pins = s₀.pins →
      (∃ F, ConLeche.reduceProjCoreFueled mode env F d nm k ce = .ok none) →
      ⦃fun s' => s' = s⦄ (pure none : AM (Option EIdx))
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimOOp (fun F => ConLeche.reduceProjCoreFueled mode env F d nm k ce)
            d s'.store r; ⊤⦄ := by
    intro s hs hxs hps hF
    obtain ⟨F, hF⟩ := hF
    vcgen; bridge_peel; subst_vars
    exact ⟨hs, hxs, hps, ⟨none, rfl, (fun _ hx => by simp at hx), F, hF⟩⟩
  -- stage 2: the table
  refine triple_seq (IFEnv.findProj?_spec s2 sn k nm hok2 hsn2) ?_
  rintro oe s3 ⟨hok3, hx3, _hm3, _hc3, hp3, hsome, hnone3⟩
  have hv'3 := denote_ext hv' hx3
  have hx03 : Ext s₀.store s3.store := hx2.trans hx3
  have hp03 : s3.pins = s₀.pins := hp3.trans hp2
  cases oe with
  | none =>
    exact hnone s3 hok3 hx03 hp03 ⟨F2, reduceProjCore_none hplc (hnone3 rfl)⟩
  | some entry =>
    obtain ⟨pe', hpd, hfp⟩ := hsome entry rfl
    have hwf3 := hok3.state.wf
    obtain ⟨rk3, hrk3⟩ := hok3.state.wf
    dsimp only
    -- stage 3: the head of the expanded scrutinee
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s3 e' hok3.state
      (by rw [hv'3]; rfl)) ?_
    rintro hd s4 ⟨hs4, hrelF⟩
    subst s4
    have hdd : denoteE s3.store hd = some v'.getAppFn := hrelF v' hv'3
    obtain ⟨vh, hvh⟩ := denoteE_view hdd
    refine tag_view_bind_triple hvh ?_
      (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
    cases vh
    case const cc us =>
      obtain ⟨cn, ls, hgf, hcn, hus⟩ := denote_const_inv hwf3 hvh hdd
      dsimp only
      -- stage 4: the spine's arguments
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s3 e'
        hok3.state (by rw [hv'3]; rfl)) ?_
      rintro args s5 ⟨hs5, hrelA⟩
      subst s5
      have hargs : Frontend.denoteEList s3.store args = some v'.getAppArgs :=
        hrelA v' hv'3
      -- stage 5: the level list's length
      refine triple_seq (viewLsLen_spec s3 us) ?_
      rintro ol s6 ⟨hs6, hol⟩
      subst s6
      rw [viewLen_of_denoteLs hus] at hol
      subst hol
      dsimp only
      -- stage 6: the possibly-`Prop` fence
      obtain ⟨_hsnp, hlps, hctor, _hbody, _hfs, _hss, _hidx, hnp, hnf, _hoff⟩ :=
        denoteProjEntry_inv hpd
      refine triple_seq (IProjEntry.fireOk_spec s3 entry us pe' ls hok3 hpd
        hus) ?_
      rintro fok s7 ⟨hok7, hst7, hp7, hfok⟩
      subst hfok
      have hc_iff : cc = entry.ctor ↔ cn = pe'.ctor := by
        constructor
        · rintro rfl; exact Option.some.inj (hcn.symm.trans hctor)
        · rintro rfl; exact denoteN_inj hrk3.nsWF hcn hctor
      have hlen_a : args.length = v'.getAppArgs.length :=
        (denoteEList_len hargs).symm
      have hlen_l : ls.length = pe'.levelParams.length ↔
          ls.length = entry.levelParams.length := by
        rw [← denoteNList_len hlps]
      have hguard : (cc = entry.ctor ∧ k < entry.numFields ∧
          args.length = entry.numParams + entry.numFields ∧
          ls.length = entry.levelParams.length ∧ pe'.fireOk ls = true) ↔
          (cn = pe'.ctor ∧ k < pe'.numFields ∧
          v'.getAppArgs.length = pe'.numParams + pe'.numFields ∧
          ls.length = pe'.levelParams.length ∧ pe'.fireOk ls = true) := by
        rw [hc_iff, hlen_a, hnp, hnf, hlen_l]
      have hst : s7.store = s3.store := hst7
      have hx07 : Ext s₀.store s7.store := by rw [hst]; exact hx03
      have hp07 : s7.pins = s₀.pins := hp7.trans hp03
      split
      next hg =>
        obtain ⟨hcE, hkF, hlenA, _hlenL, _hfire⟩ := hg
        have hgP := hguard.mp ⟨hcE, hkF, hlenA, _hlenL, _hfire⟩
        subst hcE
        -- stage 7: the `getD` default
        refine triple_seq (internE_spec s7 (.bvar 0) hok7.state.wf viewOK_bvar) ?_
        rintro b0 s8 ⟨hwf8, hx8, _hbm8, _hl8, _hsc8, _hm8, hc8, hp8, _hv8, _hd8⟩
        have hok8 : CheckOK mode env fe s8 := hok7.mono ⟨hwf8⟩ hx8 hc8 hp8
        have hx38 : Ext s3.store s8.store := by rw [← hst]; exact hx8
        -- the argument the rule selects, in range on both sides
        have hj : entry.numParams + k < args.length := by omega
        have hj' : pe'.numParams + k < v'.getAppArgs.length := by
          rw [← hlen_a, hnp]; exact hj
        have hwargs : ∀ x ∈ v'.getAppArgs, Expr.WScoped d x :=
          Expr.WScoped.getAppArgs hwv'
        have harg3 : denoteE s3.store (args.getD (entry.numParams + k) b0) =
            some (v'.getAppArgs.getD (pe'.numParams + k) (.bvar 0)) := by
          have hj'' : entry.numParams + k < v'.getAppArgs.length := by
            rw [← hlen_a]; exact hj
          have e1 : args.getD (entry.numParams + k) b0 =
              args.getD (entry.numParams + k) default := by
            rw [getD_of_lt hj, getD_of_lt hj]
          have e2 : v'.getAppArgs.getD (entry.numParams + k) (.bvar 0) =
              v'.getAppArgs.getD (entry.numParams + k) default := by
            rw [getD_of_lt hj'', getD_of_lt hj'']
          rw [hnp, e1, e2]
          exact denoteEList_getD hargs hj
        have hwarg : Expr.WScoped d
            (v'.getAppArgs.getD (pe'.numParams + k) (.bvar 0)) := by
          rw [getD_of_lt hj']
          exact hwargs _ (List.getElem_mem _)
        -- stage 8: the certificate
        refine triple_seq (projCertAt_spec hsim henv s8 d mode.verifiedChecks
          mode.betaGate entry.ctor us args cn ls v'.getAppArgs hok8
          (denoteN_ext hcn hx38) (denoteLs_ext hus hx38)
          (denoteEList_ext hx38 _ _ hargs) hwargs) ?_
        rintro cert s9 ⟨hok9, hx9, hp9, F3, hF3⟩
        have hx09 : Ext s₀.store s9.store := hx07.trans (hx8.trans hx9)
        have hp09 : s9.pins = s₀.pins := hp9.trans (hp8.trans hp07)
        have hplc' := projLitToCtorFueled_mono (Nat.le_max_left F2 F3) hplc
        have hcert' := projCertAtFueled_mono (Nat.le_max_right F2 F3) hF3
        cases cert
        · -- the certificate fails
          exact hnone s9 hok9 hx09 hp09
            ⟨max F2 F3, reduceProjCore_cert_false hplc' hfp hgf hgP hcert'⟩
        · -- the rule FIRES: the selected field
          have hfire := reduceProjCore_fire hplc' hfp hgf hgP hcert'
          have hdarg := denote_ext harg3 (hx38.trans hx9)
          vcgen +internalize; bridge_peel; subst_vars
          refine ⟨hok9, hx09, hp09, ⟨_, ?_, ?_, max F2 F3, hfire⟩⟩
          · simp only [denoteEO, hdarg, Option.map_some]
          · intro x hx
            cases hx
            exact hwarg
      next hg =>
        -- a guard fails
        exact hnone s7 hok7 hx07 hp07
          ⟨F2, reduceProjCore_guard hplc hfp hgf
            (fun h => hg (hguard.mpr h))⟩
    -- the head is not a constant
    all_goals
      dsimp only
      exact hnone s3 hok3 hx03 hp03
        ⟨F2, reduceProjCore_head hplc hfp
          (denote_not_const hwf3 hvh hdd (by intro c us h; cases h))⟩

section Census

#print axioms reduceProjCore_fire
#print axioms reduceProjCore_spec

end Census

end ConRon.Bridge.Core
