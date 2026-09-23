/-
# `ConRon.Bridge.Checker.DivMod` — the `Nat.div`/`Nat.mod` pin-variant gate

Moved out of `Bridge/Checker/DeclVal.lean` in task #97-P3-Checker round 10,
when its four pieces were proved: `checkDivModPin` is an environment guard, a
lookup of the stored value, and the variant loop over the interned pin sets,
whose step is two syntactic guards and one attempt.  `DeclVal.lean` keeps the
shared four-walk pin guard (`pinGuardWalk_run`) that the compiler-trust gate
uses too; `Bridge/Checker/Arms.lean`'s `defn` arm consumes
`checkDivModPin_bridge` from here.
-/
import ConRon.Bridge.Checker.DeclVal

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The two pinned-variant gates -/

/-! ## The `Nat.div`/`Nat.mod` variant gate, skeletonised (round 9)

`checkDivModPin` is an environment guard, a lookup of the stored value, and
the variant loop; the loop's step is two syntactic guards and one ATTEMPT
under `orElseAttempt`.  The proof below reads that structure and names the
four pieces it does not prove: the three guards' exactness and the attempt's.

**The loop needs only the `true` direction of each piece.**  Every outcome
but `matched` moves the arena to the next variant, and con-leche's
`(fueledOps μ F).orElse x k` is `match x with | .ok true => pure () | _ => k
none` (`fueledOps_orElse`): whether the pure side's guards or attempt agree or
not, it either stops with `.ok ()` or recurses — and the recursion is the
induction hypothesis, at the SAME fuel.  Only the `matched` step has to line
the two sides up: guards `true` and the pure attempt `.ok true`. -/

/-- con-leche: none — a stored constant's TYPE compared against an interned
expression, as a guard in front of a continuation (`divModEnvGuard`'s `Bool.true`
lookup). -/
theorem RunsB.matchTyAnd {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    (hpn : ∀ ci, x = some ci → Frontend.CIProjNamed s.store ci)
    {ty : EIdx} {T : Expr} (hty : denoteE s.store ty = some T)
    {Y : AM Bool} {B : Bool}
    (hY : ∀ {s₁ : AState}, Frontend.IStepS s s₁ → RunsB Y s₁ B) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv ← ci.toConstantVal
          if (cv.type != ty) = true then pure false else Y
        | none => pure false) s
      ((match (generalizing := false) y with
        | some ci => ci.toConstantVal.type == T
        | none => false) && B) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (hpn ci rfl) hd g1
    refine ⟨hs1, ?_⟩
    obtain ⟨-, -, hvt⟩ := denoteCV_inv hv
    exact RunsB.guard hs1.ok
      (by simp only [bne, beqE_of_denote hs1.ok.wf hvt (denote_ext hty hs1.ext)])
      fun _ => hY hs1

/-- con-leche: none — the same comparison as the chain's last link
(`divModEnvGuard`'s `Bool.false` lookup). -/
theorem RunsB.matchTy {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    (hpn : ∀ ci, x = some ci → Frontend.CIProjNamed s.store ci)
    {ty : EIdx} {T : Expr} (hty : denoteE s.store ty = some T) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv ← ci.toConstantVal
          pure (cv.type == ty)
        | none => pure false) s
      (match (generalizing := false) y with
        | some ci => ci.toConstantVal.type == T
        | none => false) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (hpn ci rfl) hd g1
    refine ⟨hs1, ?_⟩
    obtain ⟨-, -, hvt⟩ := denoteCV_inv hv
    rw [beqE_of_denote hs1.ok.wf hvt (denote_ext hty hs1.ext)]
    exact RunsB.ret hs1.ok

/-- con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard — the
environment prerequisites, read at the extended environment.

**PROVED** (task #97-P3-Checker round 10): `natOpGuard_runsB`,
`natOpDeps_run` + `natOpStoredOkAll_runs`, the `fe2.find? en == some eqA` test
(`IFEnvOK.find_beq_ind` at the freshly interned `eqA`), and the two `Bool`
constructors' types (`RunsB.matchTyAnd`, `RunsB.matchTy`) against the interned
`.const Bool []`. -/
theorem divModEnvGuard_run {env2 : Env} {fe2 : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s) (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns cn = some nm)
    (hr : Arena.divModEnvGuard fe2 cn s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.divModEnvGuard env2 nm := by
  suffices h : RunsB (Arena.divModEnvGuard fe2 cn) s (ConLeche.divModEnvGuard env2 nm) by
    obtain ⟨hs, rfl⟩ := h _ _ hr
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have tr : ∀ {t : AState}, Frontend.IStepS s t →
      StateOK t ∧ PinsOK t ∧ IFEnvOK env2 fe2 t ∧ denoteN t.store.ns cn = some nm :=
    fun ht => ⟨ht.ok, hp.mono ht.ext ht.pins, hie.mono ht.ext, denoteN_ext hn ht.ext⟩
  simp only [ConLeche.divModEnvGuard, Bool.and_assoc]
  unfold Arena.divModEnvGuard
  refine RunsB.bindB (natOpGuard_runsB hok hp hie hn) fun {s1} hs1 => ?_
  obtain ⟨st1, hp1, hie1, hn1⟩ := tr hs1
  refine RunsB.guard st1 (by simp) fun _ => ?_
  refine RunsB.bind fun {ds s2} g2 => ?_
  obtain rfl := natOpDeps_state hp1 g2
  obtain ⟨-, -, -, -, hds⟩ := natOpDeps_run st1 hp1 hn1 g2
  refine ⟨Frontend.IStepS.refl st1, ?_⟩
  refine RunsB.bindB (natOpStoredOkAll_runs ds _ st1 hp1 hie1 hds) fun {s3} hs3 => ?_
  obtain ⟨st3, hp3, hie3, -⟩ := tr (hs1.trans hs3)
  refine RunsB.guard st3 (by simp) fun _ => ?_
  refine RunsB.pin st3 hp3 (x := ConLeche.eqName) (by rfl) fun en den => ?_
  refine RunsB.bind fun {ea s4} g4 => ?_
  obtain ⟨hs4, hea, -⟩ := internCI_fresh st3 g4
  refine ⟨hs4, ?_⟩
  obtain ⟨st4, hp4, hie4, -⟩ := tr ((hs1.trans hs3).trans hs4)
  obtain ⟨cvE, dE, hE⟩ : ∃ cv d, ConLeche.eqA = .indInfo cv d := ⟨_, _, rfl⟩
  rw [hE] at hea ⊢
  refine RunsB.guard st4 (by
    rw [bne, hie4.find_beq_ind st4 (denoteN_ext den hs4.ext) hea]
    cases env2.find? eqName <;> (try simp) <;> rfl) fun _ => ?_
  refine RunsB.pin st4 hp4 (x := ConLeche.boolName) (by rfl) fun bn dbn => ?_
  refine RunsB.bind fun {bty s5} g5 => ?_
  obtain ⟨hs5, hbty⟩ := constE_run st4 hp4 dbn g5
  refine ⟨hs5, ?_⟩
  obtain ⟨st5, hp5, hie5, -⟩ := tr (((hs1.trans hs3).trans hs4).trans hs5)
  refine RunsB.pin st5 hp5 (x := ConLeche.boolTrueName) (by rfl) fun bt dbt => ?_
  refine RunsB.matchTyAnd st5 (hie5.findRel st5 dbt)
    (fun ci hf => CIProjNamed_of_find hie5 hf) hbty fun {s6} hs6 => ?_
  have hie6 := hie5.mono hs6.ext
  refine RunsB.pin hs6.ok (hp5.mono hs6.ext hs6.pins) (x := ConLeche.boolFalseName)
    (by rfl) fun bf dbf => ?_
  exact RunsB.matchTy hs6.ok (hie6.findRel hs6.ok dbf)
    (fun ci hf => CIProjNamed_of_find hie6 hf) (denote_ext hbty hs6.ext)

/-! ## The certificate guards' walks -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:627-638 Expr.substConstAll — the
full substitution of a level-monomorphic constant, under binders too, at any
fuel that succeeds. -/
theorem substConstAll_run {cn : NIdx} {nm : ConLeche.Name} {rh : EIdx} {x : Expr} :
    ∀ (fuel : Nat) {h h' : EIdx} {e : Expr} {s s' : AState}, StateOK s →
      PinsOK s → denoteN s.store.ns cn = some nm → denoteE s.store rh = some x →
      denoteE s.store h = some e →
      Arena.substConstAll cn rh fuel h s = .ok (h', s') →
      Frontend.IStepS s s' ∧
        denoteE s'.store h' = some (Expr.substConstAll nm x e) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h h' e s s' _ _ _ _ _ hrun
    exact absurd hrun (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  | succ fuel ih =>
    intro h h' e s s' hst hp hn hx he hrun
    have hwf := hst.wf
    have hwf' := hwf
    obtain ⟨rk, hrk⟩ := hwf'
    -- one recursive call, transported
    have step : ∀ {t : AState} {a a' : EIdx} {ea : Expr} {t' : AState},
        Frontend.IStepS s t → denoteE s.store a = some ea →
        Arena.substConstAll cn rh fuel a t = .ok (a', t') →
        Frontend.IStepS t t' ∧ denoteE t'.store a' = some (Expr.substConstAll nm x ea) :=
      fun ht ha g => ih ht.ok (hp.mono ht.ext ht.pins) (denoteN_ext hn ht.ext)
        (denote_ext hx ht.ext) (denote_ext ha ht.ext) g
    simp only [Arena.substConstAll] at hrun
    obtain ⟨v, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨e1s, hv⟩ := viewE_run g1
    rw [e1s] at k1
    cases v
    case const c us =>
      obtain ⟨cN, ls, rfl, hcN, hls⟩ := denote_const_inv hwf hv he
      obtain ⟨el, s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨e2s, hel⟩ := AM.of_run (P := fun t => t = s)
        (Q := fun r t => t = s ∧ denoteLs s.store.lss r = some []) rfl g2
        (pinEmptyLevels_spec s hp)
      rw [e2s] at k2
      have e1 := beq_of_denote_inj (fun h1 h2 => denoteN_inj hrk.nsWF h1 h2) hcN hn
      have e2 := beq_of_denote_inj (fun h1 h2 => denoteLs_inj hrk.lss h1 h2) hls hel
      rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        simp only [Bool.and_eq_true, e1, e2, beq_iff_eq] at hc
        refine ⟨Frontend.IStepS.refl hst, ?_⟩
        simp only [Expr.substConstAll, hc, and_self, if_true]
        exact hx
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        simp only [Bool.and_eq_true, e1, e2, beq_iff_eq] at hc
        refine ⟨Frontend.IStepS.refl hst, ?_⟩
        simp only [Expr.substConstAll, if_neg hc]
        exact he
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hv he
      obtain ⟨f', s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, hf'⟩ := step (Frontend.IStepS.refl hst) hf g2
      obtain ⟨a', s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨hs3, ha'⟩ := step hs2 ha g3
      have hf3 := denote_ext hf' hs3.ext
      obtain ⟨hs4, hd⟩ := Frontend.internE_sstep hs3.ok
        (viewOK_app (by rw [hf3]; rfl) (by rw [ha']; rfl)) k3
      refine ⟨(hs2.trans hs3).trans hs4, ?_⟩
      rw [hd]
      simp only [denoteEView, denote_ext hf3 hs4.ext, denote_ext ha' hs4.ext, opt2,
        Expr.substConstAll]
    case lam ty b m =>
      obtain ⟨et, eb, rfl, ht, hb⟩ := denote_lam_inv hwf hv he
      obtain ⟨t', s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, ht'⟩ := step (Frontend.IStepS.refl hst) ht g2
      obtain ⟨b', s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨hs3, hb'⟩ := step hs2 hb g3
      have ht3 := denote_ext ht' hs3.ext
      obtain ⟨hs4, hd⟩ := Frontend.internE_sstep hs3.ok
        (viewOK_lam (by rw [ht3]; rfl) (by rw [hb']; rfl)) k3
      refine ⟨(hs2.trans hs3).trans hs4, ?_⟩
      rw [hd]
      simp only [denoteEView, denote_ext ht3 hs4.ext, denote_ext hb' hs4.ext, opt2,
        Expr.substConstAll]
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, ht, hb⟩ := denote_forallE_inv hwf hv he
      obtain ⟨t', s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, ht'⟩ := step (Frontend.IStepS.refl hst) ht g2
      obtain ⟨b', s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨hs3, hb'⟩ := step hs2 hb g3
      have ht3 := denote_ext ht' hs3.ext
      obtain ⟨hs4, hd⟩ := Frontend.internE_sstep hs3.ok
        (viewOK_forallE (by rw [ht3]; rfl) (by rw [hb']; rfl)) k3
      refine ⟨(hs2.trans hs3).trans hs4, ?_⟩
      rw [hd]
      simp only [denoteEView, denote_ext ht3 hs4.ext, denote_ext hb' hs4.ext, opt2,
        Expr.substConstAll]
    case letE ty w b =>
      obtain ⟨et, ew, eb, rfl, ht, hw, hb⟩ := denote_letE_inv hwf hv he
      obtain ⟨t', s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, ht'⟩ := step (Frontend.IStepS.refl hst) ht g2
      obtain ⟨w', s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨hs3, hw'⟩ := step hs2 hw g3
      obtain ⟨b', s4, g4, k4⟩ := AM.bind_ok k3
      obtain ⟨hs4, hb'⟩ := step (hs2.trans hs3) hb g4
      have ht4 := denote_ext (denote_ext ht' hs3.ext) hs4.ext
      have hw4 := denote_ext hw' hs4.ext
      obtain ⟨hs5, hd⟩ := Frontend.internE_sstep hs4.ok
        (viewOK_letE (by rw [ht4]; rfl) (by rw [hw4]; rfl) (by rw [hb']; rfl)) k4
      refine ⟨((hs2.trans hs3).trans hs4).trans hs5, ?_⟩
      rw [hd]
      simp only [denoteEView, denote_ext ht4 hs5.ext, denote_ext hw4 hs5.ext,
        denote_ext hb' hs5.ext, Expr.substConstAll]
      rfl
    case proj sn i sub =>
      obtain ⟨snm, es, rfl, hsn, hsub⟩ := denote_proj_inv hwf hv he
      obtain ⟨sub', s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, hsub'⟩ := step (Frontend.IStepS.refl hst) hsub g2
      have hsn2 := denoteN_ext hsn hs2.ext
      obtain ⟨hs3, hd⟩ := Frontend.internE_sstep hs2.ok
        (viewOK_proj (nview_isSome_of_denote hsn2) (by rw [hsub']; rfl)) k2
      refine ⟨hs2.trans hs3, ?_⟩
      rw [hd]
      simp only [denoteEView, denoteN_ext hsn2 hs3.ext, denote_ext hsub' hs3.ext,
        Expr.substConstAll]
      rfl
    all_goals first
      | (obtain rfl := denote_bvar_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, rfl, _⟩ := denote_fvar_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, rfl, _⟩ := denote_sort_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain rfl := denote_lit_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)

/-- con-leche: ConLeche/Kernel/Checker.lean:122-130 divModDeclPin — one
variant's pinned defining expression: seven pin reads and handle tests, each
con-leche's name test (`beq_handle_iff`), and the variant's field. -/
theorem divModDeclPin_run {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx}
    {nm : ConLeche.Name} {p : EIdx} {s s' : AState} (hst : StateOK s)
    (hp : PinsOK s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : Arena.divModDeclPin ps cn s = .ok (p, s')) :
    s' = s ∧ denoteE s.store p = some (ConLeche.divModDeclPin psP nm) := by
  simp only [Arena.divModDeclPin] at hrun
  obtain ⟨h0, u0, g0, w0⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d0⟩ := pinAt_run (x := ConLeche.natDivName) hp (by rfl) g0
  have b0 := beq_handle_iff hst.wf hn d0
  rcases AM.ite_ok w0 with ⟨y0, a0⟩ | ⟨z0, v0⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a0
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_pos (b0.mp y0)]
    exact hps.divPin
  have nb0 : ¬ (nm = ConLeche.natDivName) := fun h => z0 (b0.mpr h)
  obtain ⟨h1, u1, g1, w1⟩ := AM.bind_ok v0
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natGcdName) hp (by rfl) g1
  have b1 := beq_handle_iff hst.wf hn d1
  rcases AM.ite_ok w1 with ⟨y1, a1⟩ | ⟨z1, v1⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a1
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_pos (b1.mp y1)]
    exact hps.gcdPin
  have nb1 : ¬ (nm = ConLeche.natGcdName) := fun h => z1 (b1.mpr h)
  obtain ⟨h2, u2, g2, w2⟩ := AM.bind_ok v1
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natLandName) hp (by rfl) g2
  have b2 := beq_handle_iff hst.wf hn d2
  rcases AM.ite_ok w2 with ⟨y2, a2⟩ | ⟨z2, v2⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a2
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_pos (b2.mp y2)]
    exact hps.landPin
  have nb2 : ¬ (nm = ConLeche.natLandName) := fun h => z2 (b2.mpr h)
  obtain ⟨h3, u3, g3, w3⟩ := AM.bind_ok v2
  obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natLorName) hp (by rfl) g3
  have b3 := beq_handle_iff hst.wf hn d3
  rcases AM.ite_ok w3 with ⟨y3, a3⟩ | ⟨z3, v3⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a3
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_pos (b3.mp y3)]
    exact hps.lorPin
  have nb3 : ¬ (nm = ConLeche.natLorName) := fun h => z3 (b3.mpr h)
  obtain ⟨h4, u4, g4, w4⟩ := AM.bind_ok v3
  obtain ⟨rfl, d4⟩ := pinAt_run (x := ConLeche.natXorName) hp (by rfl) g4
  have b4 := beq_handle_iff hst.wf hn d4
  rcases AM.ite_ok w4 with ⟨y4, a4⟩ | ⟨z4, v4⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a4
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_pos (b4.mp y4)]
    exact hps.xorPin
  have nb4 : ¬ (nm = ConLeche.natXorName) := fun h => z4 (b4.mpr h)
  obtain ⟨h5, u5, g5, w5⟩ := AM.bind_ok v4
  obtain ⟨rfl, d5⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp (by rfl) g5
  have b5 := beq_handle_iff hst.wf hn d5
  rcases AM.ite_ok w5 with ⟨y5, a5⟩ | ⟨z5, v5⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a5
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_pos (b5.mp y5)]
    exact hps.shiftLeftPin
  have nb5 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z5 (b5.mpr h)
  obtain ⟨h6, u6, g6, w6⟩ := AM.bind_ok v5
  obtain ⟨rfl, d6⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp (by rfl) g6
  have b6 := beq_handle_iff hst.wf hn d6
  rcases AM.ite_ok w6 with ⟨y6, a6⟩ | ⟨z6, v6⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a6
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_pos (b6.mp y6)]
    exact hps.shiftRightPin
  have nb6 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z6 (b6.mpr h)
  obtain ⟨rfl, rfl⟩ := AM.pure_ok v6
  refine ⟨rfl, ?_⟩
  rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6]
  exact hps.modPin

/-- con-leche: ConLeche/Kernel/Checker.lean:134-142 divModCertProofs — one
variant's certificate proofs, by the same seven tests. -/
theorem divModCertProofs_run {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx}
    {nm : ConLeche.Name} {p : List EIdx} {s s' : AState} (hst : StateOK s)
    (hp : PinsOK s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : Arena.divModCertProofs ps cn s = .ok (p, s')) :
    s' = s ∧ Frontend.denoteEList s.store p = some (ConLeche.divModCertProofs psP nm) := by
  simp only [Arena.divModCertProofs] at hrun
  obtain ⟨h0, u0, g0, w0⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d0⟩ := pinAt_run (x := ConLeche.natDivName) hp (by rfl) g0
  have b0 := beq_handle_iff hst.wf hn d0
  rcases AM.ite_ok w0 with ⟨y0, a0⟩ | ⟨z0, v0⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a0
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_pos (b0.mp y0)]
    exact hps.divProofs
  have nb0 : ¬ (nm = ConLeche.natDivName) := fun h => z0 (b0.mpr h)
  obtain ⟨h1, u1, g1, w1⟩ := AM.bind_ok v0
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natGcdName) hp (by rfl) g1
  have b1 := beq_handle_iff hst.wf hn d1
  rcases AM.ite_ok w1 with ⟨y1, a1⟩ | ⟨z1, v1⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a1
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_pos (b1.mp y1)]
    exact hps.gcdProofs
  have nb1 : ¬ (nm = ConLeche.natGcdName) := fun h => z1 (b1.mpr h)
  obtain ⟨h2, u2, g2, w2⟩ := AM.bind_ok v1
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natLandName) hp (by rfl) g2
  have b2 := beq_handle_iff hst.wf hn d2
  rcases AM.ite_ok w2 with ⟨y2, a2⟩ | ⟨z2, v2⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a2
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_pos (b2.mp y2)]
    exact hps.landProofs
  have nb2 : ¬ (nm = ConLeche.natLandName) := fun h => z2 (b2.mpr h)
  obtain ⟨h3, u3, g3, w3⟩ := AM.bind_ok v2
  obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natLorName) hp (by rfl) g3
  have b3 := beq_handle_iff hst.wf hn d3
  rcases AM.ite_ok w3 with ⟨y3, a3⟩ | ⟨z3, v3⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a3
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_pos (b3.mp y3)]
    exact hps.lorProofs
  have nb3 : ¬ (nm = ConLeche.natLorName) := fun h => z3 (b3.mpr h)
  obtain ⟨h4, u4, g4, w4⟩ := AM.bind_ok v3
  obtain ⟨rfl, d4⟩ := pinAt_run (x := ConLeche.natXorName) hp (by rfl) g4
  have b4 := beq_handle_iff hst.wf hn d4
  rcases AM.ite_ok w4 with ⟨y4, a4⟩ | ⟨z4, v4⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a4
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_pos (b4.mp y4)]
    exact hps.xorProofs
  have nb4 : ¬ (nm = ConLeche.natXorName) := fun h => z4 (b4.mpr h)
  obtain ⟨h5, u5, g5, w5⟩ := AM.bind_ok v4
  obtain ⟨rfl, d5⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp (by rfl) g5
  have b5 := beq_handle_iff hst.wf hn d5
  rcases AM.ite_ok w5 with ⟨y5, a5⟩ | ⟨z5, v5⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a5
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_pos (b5.mp y5)]
    exact hps.shiftLeftProofs
  have nb5 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z5 (b5.mpr h)
  obtain ⟨h6, u6, g6, w6⟩ := AM.bind_ok v5
  obtain ⟨rfl, d6⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp (by rfl) g6
  have b6 := beq_handle_iff hst.wf hn d6
  rcases AM.ite_ok w6 with ⟨y6, a6⟩ | ⟨z6, v6⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a6
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_pos (b6.mp y6)]
    exact hps.shiftRightProofs
  have nb6 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z6 (b6.mpr h)
  obtain ⟨rfl, rfl⟩ := AM.pure_ok v6
  refine ⟨rfl, ?_⟩
  rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6]
  exact hps.modProofs

/-! ## The certificate statements, interned -/

/-- con-leche: ConLeche/Kernel/Checker.lean:155-222 divModCertStmts — **the
interned statements denote con-leche's**, statement by statement: each
hypothesis list and each equation. -/
def StmtsDenote (st : EStore) : List (List EIdx × EIdx) → List (List Expr × Expr) → Prop
  | [], [] => True
  | (hs, e) :: r, (xs, x) :: r' =>
    Frontend.denoteEList st hs = some xs ∧ denoteE st e = some x ∧ StmtsDenote st r r'
  | _, _ => False

theorem StmtsDenote.mono {st st' : EStore} (hx : Ext st st') :
    ∀ (a : List (List EIdx × EIdx)) (b : List (List Expr × Expr)),
      StmtsDenote st a b → StmtsDenote st' a b := by
  intro a
  induction a with
  | nil => intro b h; cases b <;> exact h
  | cons p ps ih =>
    intro b h
    cases b with
    | nil => exact h
    | cons q qs =>
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨denoteEList_ext hx _ _ h1, denote_ext h2 hx, ih qs h3⟩

theorem denoteEList_one {st : EStore} {a : EIdx} {x : Expr}
    (h : denoteE st a = some x) : Frontend.denoteEList st [a] = some [x] := by
  simp [Frontend.denoteEList, h]

theorem denoteEList_two {st : EStore} {a b : EIdx} {x y : Expr}
    (ha : denoteE st a = some x) (hb : denoteE st b = some y) :
    Frontend.denoteEList st [a, b] = some [x, y] := by
  simp [Frontend.denoteEList, ha, hb]

/-- con-leche: ConLeche/Kernel/Checker.lean:155-222 divModCertStmts — the open
statements' variables `fvar i : Nat`. -/
theorem natVar_run {i : Nat} {h : EIdx} {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hr : Arena.natVar i s = .ok (h, s')) :
    Frontend.IStepS s s' ∧
      denoteE s'.store h = some (.fvar i (.const ConLeche.natName [])) := by
  simp only [Arena.natVar] at hr
  obtain ⟨nt, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natName) hp rfl g1
  obtain ⟨ty, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hs2, e2⟩ := constE_run hst hp d1 g2
  obtain ⟨hs3, e3⟩ := internFvar_run hs2.ok e2 r2
  exact ⟨hs2.trans hs3, e3⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:155-222 divModCertStmts — the
numeral `1` as `Nat.succ Nat.zero`. -/
theorem natOne_run {h : EIdx} {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hr : Arena.natOne s = .ok (h, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store h =
      some (.app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName [])) := by
  simp only [Arena.natOne] at hr
  obtain ⟨sc, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natSuccName) hp rfl g1
  obtain ⟨zn, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natZeroName) hp rfl g2
  obtain ⟨z, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hs3, e3⟩ := constE_run hst hp d2 g3
  obtain ⟨hs4, e4⟩ := natAp1_run hs3.ok (hp.mono hs3.ext hs3.pins)
    (denoteN_ext d1 hs3.ext) e3 r3
  exact ⟨hs3.trans hs4, e4⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:155-222 divModCertStmts — the
statements' `Eq.{1} τ a b`. -/
theorem eqAt1_run {ty a b h : EIdx} {T A B : Expr} {s s' : AState} (hst : StateOK s)
    (hp : PinsOK s) (ht : denoteE s.store ty = some T) (ha : denoteE s.store a = some A)
    (hb : denoteE s.store b = some B) (hr : Arena.eqAt1 ty a b s = .ok (h, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store h =
      some (.app (.app (.app (.const ConLeche.eqName [.succ .zero]) T) A) B) := by
  simp only [Arena.eqAt1] at hr
  obtain ⟨z, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨rfl, hz⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteL s.store.ls r = some .zero) rfl g1 (pinZeroLevel_spec s hp)
  obtain ⟨o, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨st2, hd2⟩ := Frontend.internLNode_sstep hst
    ⟨by intro c hc
        simp only [LNodeView.lchildren, List.mem_singleton] at hc
        subst hc; exact lview_isSome_of_denote hz,
     by intro c hc; simp [LNodeView.nchildren] at hc⟩ g2
  have ho : denoteL s2.store.ls o = some (.succ .zero) := by
    rw [hd2]; simp only [denoteLView, denoteL_ext hz st2.ext, Option.map_some]
  obtain ⟨us, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨st3, hd3⟩ := Frontend.internLsNode_sstep st2.ok
    (by intro c hc
        simp only [List.mem_singleton] at hc
        subst hc; exact lview_isSome_of_denote ho) g3
  have hus : denoteLs s3.store.lss us = some [.succ .zero] := by
    rw [hd3]
    show denoteLList s3.store.lss.ls [o] = _
    have ho3 : denoteL s3.store.lss.ls o = some (.succ .zero) := denoteL_ext ho st3.ext
    simp only [denoteLList, ho3, opt2]
  have A3 := st2.trans st3
  obtain ⟨en, s4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨rfl, den⟩ := pinAt_run (x := ConLeche.eqName) (hp.mono A3.ext A3.pins) rfl g4
  obtain ⟨e, s5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨ls, hv, -⟩ := denoteLs_view hus
  obtain ⟨st5, hd5⟩ := Frontend.internE_sstep A3.ok
    (viewOK_const (nview_isSome_of_denote den) (by rw [hv]; rfl)) g5
  have he5 : denoteE s5.store e = some (.const ConLeche.eqName [.succ .zero]) := by
    rw [hd5]
    simp only [denoteEView, denoteN_ext den st5.ext, denoteLs_ext hus st5.ext, opt2]
  have A5 := A3.trans st5
  have ht5 := denote_ext ht A5.ext
  obtain ⟨e1, s6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨st6, hd6⟩ := Frontend.internE_sstep A5.ok
    (viewOK_app (by rw [he5]; rfl) (by rw [ht5]; rfl)) g6
  have he6 : denoteE s6.store e1 = some (.app (.const ConLeche.eqName [.succ .zero]) T) := by
    rw [hd6]; simp only [denoteEView, denote_ext he5 st6.ext, denote_ext ht5 st6.ext, opt2]
  have A6 := A5.trans st6
  have ha6 := denote_ext ha A6.ext
  obtain ⟨e2, s7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨st7, hd7⟩ := Frontend.internE_sstep A6.ok
    (viewOK_app (by rw [he6]; rfl) (by rw [ha6]; rfl)) g7
  have he7 : denoteE s7.store e2 =
      some (.app (.app (.const ConLeche.eqName [.succ .zero]) T) A) := by
    rw [hd7]; simp only [denoteEView, denote_ext he6 st7.ext, denote_ext ha6 st7.ext, opt2]
  have A7 := A6.trans st7
  have hb7 := denote_ext hb A7.ext
  obtain ⟨st8, hd8⟩ := Frontend.internE_sstep A7.ok
    (viewOK_app (by rw [he7]; rfl) (by rw [hb7]; rfl)) r7
  refine ⟨A7.trans st8, ?_⟩
  rw [hd8]; simp only [denoteEView, denote_ext he7 st8.ext, denote_ext hb7 st8.ext, opt2]

/-- con-leche: ConLeche/Kernel/Checker.lean:155-222 divModCertStmts — **the
pinned characterization statements, interned**: seven branches of `natAp1`,
`natAp2` and `eqAt1` over a shared prologue of pins, constants and the two
variables.  Generated text (`_tmp` generator, task #97-P3-Checker round 10):
every denotation fact is carried to the final state by the `Ext` chain behind
it. -/
theorem divModCertStmts_run {cn : NIdx} {nm : ConLeche.Name}
    {stmts : List (List EIdx × EIdx)} {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns cn = some nm)
    (hr : Arena.divModCertStmts cn s = .ok (stmts, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store stmts (ConLeche.divModCertStmts nm) := by
  simp only [Arena.divModCertStmts] at hr
  have A0 := Frontend.IStepS.refl hst
  obtain ⟨v1, u1, g1, w1⟩ := AM.bind_ok hr
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natName) (hp.mono A0.ext A0.pins) rfl g1
  obtain ⟨v3, u3, g3, w3⟩ := AM.bind_ok w1
  obtain ⟨hs4, e5⟩ := constE_run A0.ok (hp.mono A0.ext A0.pins) d2 g3
  have A1 := A0.trans hs4
  obtain ⟨v6, u6, g6, w6⟩ := AM.bind_ok w3
  obtain ⟨hs7, e8⟩ := natVar_run A1.ok (hp.mono A1.ext A1.pins)  g6
  have A2 := A1.trans hs7
  obtain ⟨v9, u9, g9, w9⟩ := AM.bind_ok w6
  obtain ⟨hs10, e11⟩ := natVar_run A2.ok (hp.mono A2.ext A2.pins)  g9
  have A3 := A2.trans hs10
  obtain ⟨v12, u12, g12, w12⟩ := AM.bind_ok w9
  obtain ⟨hs13, e14⟩ := natOne_run A3.ok (hp.mono A3.ext A3.pins)  g12
  have A4 := A3.trans hs13
  obtain ⟨v15, u15, g15, w15⟩ := AM.bind_ok w12
  obtain ⟨rfl, d16⟩ := pinAt_run (x := ConLeche.natBleName) (hp.mono A4.ext A4.pins) rfl g15
  obtain ⟨v17, u17, g17, w17⟩ := AM.bind_ok w15
  obtain ⟨rfl, d18⟩ := pinAt_run (x := ConLeche.boolName) (hp.mono A4.ext A4.pins) rfl g17
  obtain ⟨v19, u19, g19, w19⟩ := AM.bind_ok w17
  obtain ⟨hs20, e21⟩ := constE_run A4.ok (hp.mono A4.ext A4.pins) d18 g19
  have A5 := A4.trans hs20
  obtain ⟨v22, u22, g22, w22⟩ := AM.bind_ok w19
  obtain ⟨rfl, d23⟩ := pinAt_run (x := ConLeche.boolTrueName) (hp.mono A5.ext A5.pins) rfl g22
  obtain ⟨v24, u24, g24, w24⟩ := AM.bind_ok w22
  obtain ⟨hs25, e26⟩ := constE_run A5.ok (hp.mono A5.ext A5.pins) d23 g24
  have A6 := A5.trans hs25
  obtain ⟨v27, u27, g27, w27⟩ := AM.bind_ok w24
  obtain ⟨rfl, d28⟩ := pinAt_run (x := ConLeche.boolFalseName) (hp.mono A6.ext A6.pins) rfl g27
  obtain ⟨v29, u29, g29, w29⟩ := AM.bind_ok w27
  obtain ⟨hs30, e31⟩ := constE_run A6.ok (hp.mono A6.ext A6.pins) d28 g29
  have A7 := A6.trans hs30
  obtain ⟨v32, u32, g32, w32⟩ := AM.bind_ok w29
  obtain ⟨rfl, d33⟩ := pinAt_run (x := ConLeche.natZeroName) (hp.mono A7.ext A7.pins) rfl g32
  obtain ⟨v34, u34, g34, w34⟩ := AM.bind_ok w32
  obtain ⟨hs35, e36⟩ := constE_run A7.ok (hp.mono A7.ext A7.pins) d33 g34
  have A8 := A7.trans hs35
  obtain ⟨v37, u37, g37, w37⟩ := AM.bind_ok w34
  obtain ⟨rfl, d38⟩ := pinAt_run (x := ConLeche.natSuccName) (hp.mono A8.ext A8.pins) rfl g37
  obtain ⟨v39, u39, g39, w39⟩ := AM.bind_ok w37
  obtain ⟨hs40, e41⟩ := natAp1_run A8.ok (hp.mono A8.ext A8.pins) d38 (denote_ext e14 ((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext)) g39
  have A9 := A8.trans hs40
  obtain ⟨v42, u42, g42, w42⟩ := AM.bind_ok w39
  obtain ⟨rfl, d43⟩ := pinAt_run (x := ConLeche.natModName) (hp.mono A9.ext A9.pins) rfl g42
  obtain ⟨v44, u44, g44, w44⟩ := AM.bind_ok w42
  obtain ⟨rfl, d45⟩ := pinAt_run (x := ConLeche.natDivName) (hp.mono A9.ext A9.pins) rfl g44
  obtain ⟨v46, u46, g46, w46⟩ := AM.bind_ok w44
  obtain ⟨rfl, d47⟩ := pinAt_run (x := ConLeche.natAddName) (hp.mono A9.ext A9.pins) rfl g46
  obtain ⟨v48, u48, g48, w48⟩ := AM.bind_ok w46
  obtain ⟨rfl, d49⟩ := pinAt_run (x := ConLeche.natMulName) (hp.mono A9.ext A9.pins) rfl g48
  obtain ⟨v50, u50, g50, w50⟩ := AM.bind_ok w48
  obtain ⟨rfl, d51⟩ := pinAt_run (x := ConLeche.natSubName) (hp.mono A9.ext A9.pins) rfl g50
  obtain ⟨v52, u52, g52, w52⟩ := AM.bind_ok w50
  obtain ⟨rfl, d53⟩ := pinAt_run (x := ConLeche.natGcdName) (hp.mono A9.ext A9.pins) rfl g52
  obtain ⟨v54, u54, g54, w54⟩ := AM.bind_ok w52
  obtain ⟨rfl, d55⟩ := pinAt_run (x := ConLeche.natShiftLeftName) (hp.mono A9.ext A9.pins) rfl g54
  obtain ⟨v56, u56, g56, w56⟩ := AM.bind_ok w54
  obtain ⟨rfl, d57⟩ := pinAt_run (x := ConLeche.natShiftRightName) (hp.mono A9.ext A9.pins) rfl g56
  obtain ⟨v58, u58, g58, w58⟩ := AM.bind_ok w56
  obtain ⟨rfl, d59⟩ := pinAt_run (x := ConLeche.natLandName) (hp.mono A9.ext A9.pins) rfl g58
  obtain ⟨v60, u60, g60, w60⟩ := AM.bind_ok w58
  obtain ⟨rfl, d61⟩ := pinAt_run (x := ConLeche.natLorName) (hp.mono A9.ext A9.pins) rfl g60
  obtain ⟨v62, u62, g62, w62⟩ := AM.bind_ok w60
  obtain ⟨rfl, d63⟩ := pinAt_run (x := ConLeche.natXorName) (hp.mono A9.ext A9.pins) rfl g62
  have b0 := beq_handle_iff A9.ok.wf (denoteN_ext hn (((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) d53
  rcases AM.ite_ok w62 with ⟨y0, w0y⟩ | ⟨z0, w0n⟩
  · -- natGcdName
    obtain ⟨v65, u65, g65, w65⟩ := AM.bind_ok w0y
    obtain ⟨hs66, e67⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) (denoteN_ext d16 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e14 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e8 (((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g65
    have A10 := A9.trans hs66
    obtain ⟨v69, u69, g69, w69⟩ := AM.bind_ok w65
    obtain ⟨hs70, e71⟩ := eqAt1_run A10.ok (hp.mono A10.ext A10.pins) (denote_ext e21 (((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext)) e67 (denote_ext e26 ((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext)) g69
    have A11 := A10.trans hs70
    obtain ⟨v73, u73, g73, w73⟩ := AM.bind_ok w69
    obtain ⟨hs74, e75⟩ := natAp2_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d16 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext)) (denote_ext e14 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext)) (denote_ext e8 (((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext)) g73
    have A12 := A11.trans hs74
    obtain ⟨v77, u77, g77, w77⟩ := AM.bind_ok w73
    obtain ⟨hs78, e79⟩ := eqAt1_run A12.ok (hp.mono A12.ext A12.pins) (denote_ext e21 (((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext)) e75 (denote_ext e31 (((((hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext)) g77
    have A13 := A12.trans hs78
    obtain ⟨v81, u81, g81, w81⟩ := AM.bind_ok w77
    obtain ⟨hs82, e83⟩ := natAp2_run A13.ok (hp.mono A13.ext A13.pins) (denoteN_ext hn (((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext)) (denote_ext e8 (((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext)) (denote_ext e11 ((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext)) g81
    have A14 := A13.trans hs82
    obtain ⟨v85, u85, g85, w85⟩ := AM.bind_ok w81
    obtain ⟨hs86, e87⟩ := natAp2_run A14.ok (hp.mono A14.ext A14.pins) (denoteN_ext d43 (((((hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext)) (denote_ext e11 (((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext)) (denote_ext e8 ((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext)) g85
    have A15 := A14.trans hs86
    obtain ⟨v89, u89, g89, w89⟩ := AM.bind_ok w85
    obtain ⟨hs90, e91⟩ := natAp2_run A15.ok (hp.mono A15.ext A15.pins) (denoteN_ext hn (((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext)) e87 (denote_ext e8 (((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext)) g89
    have A16 := A15.trans hs90
    obtain ⟨v93, u93, g93, w93⟩ := AM.bind_ok w89
    obtain ⟨hs94, e95⟩ := eqAt1_run A16.ok (hp.mono A16.ext A16.pins) (denote_ext e5 (((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext).trans hs90.ext)) (denote_ext e83 ((hs86.ext).trans hs90.ext)) e91 g93
    have A17 := A16.trans hs94
    obtain ⟨v97, u97, g97, w97⟩ := AM.bind_ok w93
    obtain ⟨hs98, e99⟩ := natAp2_run A17.ok (hp.mono A17.ext A17.pins) (denoteN_ext hn (((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext).trans hs90.ext).trans hs94.ext)) (denote_ext e8 (((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext).trans hs90.ext).trans hs94.ext)) (denote_ext e11 ((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext).trans hs90.ext).trans hs94.ext)) g97
    have A18 := A17.trans hs98
    obtain ⟨v101, u101, g101, w101⟩ := AM.bind_ok w97
    obtain ⟨hs102, e103⟩ := eqAt1_run A18.ok (hp.mono A18.ext A18.pins) (denote_ext e5 (((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext).trans hs90.ext).trans hs94.ext).trans hs98.ext)) e99 (denote_ext e11 (((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs66.ext).trans hs70.ext).trans hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext).trans hs90.ext).trans hs94.ext).trans hs98.ext)) g101
    have A19 := A18.trans hs102
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w101
    refine ⟨A19, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_pos (b0.mp y0)]
    exact ⟨denoteEList_one (denote_ext e71 ((((((((hs74.ext).trans hs78.ext).trans hs82.ext).trans hs86.ext).trans hs90.ext).trans hs94.ext).trans hs98.ext).trans hs102.ext)),
        (denote_ext e95 ((hs98.ext).trans hs102.ext)),
        denoteEList_one (denote_ext e79 ((((((hs82.ext).trans hs86.ext).trans hs90.ext).trans hs94.ext).trans hs98.ext).trans hs102.ext)),
        e103,
        trivial⟩
  have n0 : ¬ (nm = ConLeche.natGcdName) := fun h => z0 (b0.mpr h)
  have b1 := beq_handle_iff A9.ok.wf (denoteN_ext hn (((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) d55
  rcases AM.ite_ok w0n with ⟨y1, w1y⟩ | ⟨z1, w1n⟩
  · -- natShiftLeftName
    obtain ⟨v1105, u1105, g1105, w1105⟩ := AM.bind_ok w1y
    obtain ⟨hs1106, e1107⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) (denoteN_ext d16 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e14 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e11 ((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g1105
    have A10 := A9.trans hs1106
    obtain ⟨v1109, u1109, g1109, w1109⟩ := AM.bind_ok w1105
    obtain ⟨hs1110, e1111⟩ := eqAt1_run A10.ok (hp.mono A10.ext A10.pins) (denote_ext e21 (((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext)) e1107 (denote_ext e26 ((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext)) g1109
    have A11 := A10.trans hs1110
    obtain ⟨v1113, u1113, g1113, w1113⟩ := AM.bind_ok w1109
    obtain ⟨hs1114, e1115⟩ := natAp2_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d16 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext)) (denote_ext e14 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext)) (denote_ext e11 ((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext)) g1113
    have A12 := A11.trans hs1114
    obtain ⟨v1117, u1117, g1117, w1117⟩ := AM.bind_ok w1113
    obtain ⟨hs1118, e1119⟩ := eqAt1_run A12.ok (hp.mono A12.ext A12.pins) (denote_ext e21 (((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext)) e1115 (denote_ext e31 (((((hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext)) g1117
    have A13 := A12.trans hs1118
    obtain ⟨v1121, u1121, g1121, w1121⟩ := AM.bind_ok w1117
    obtain ⟨hs1122, e1123⟩ := natAp2_run A13.ok (hp.mono A13.ext A13.pins) (denoteN_ext hn (((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext)) (denote_ext e8 (((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext)) (denote_ext e11 ((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext)) g1121
    have A14 := A13.trans hs1122
    obtain ⟨v1125, u1125, g1125, w1125⟩ := AM.bind_ok w1121
    obtain ⟨hs1126, e1127⟩ := natAp2_run A14.ok (hp.mono A14.ext A14.pins) (denoteN_ext d49 (((((hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext)) (denote_ext e41 (((((hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext)) (denote_ext e8 ((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext)) g1125
    have A15 := A14.trans hs1126
    obtain ⟨v1129, u1129, g1129, w1129⟩ := AM.bind_ok w1125
    obtain ⟨hs1130, e1131⟩ := natAp2_run A15.ok (hp.mono A15.ext A15.pins) (denoteN_ext d51 ((((((hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext)) (denote_ext e11 ((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext)) (denote_ext e14 (((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext)) g1129
    have A16 := A15.trans hs1130
    obtain ⟨v1133, u1133, g1133, w1133⟩ := AM.bind_ok w1129
    obtain ⟨hs1134, e1135⟩ := natAp2_run A16.ok (hp.mono A16.ext A16.pins) (denoteN_ext hn ((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext)) (denote_ext e1127 (hs1130.ext)) e1131 g1133
    have A17 := A16.trans hs1134
    obtain ⟨v1137, u1137, g1137, w1137⟩ := AM.bind_ok w1133
    obtain ⟨hs1138, e1139⟩ := eqAt1_run A17.ok (hp.mono A17.ext A17.pins) (denote_ext e5 ((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext)) (denote_ext e1123 (((hs1126.ext).trans hs1130.ext).trans hs1134.ext)) e1135 g1137
    have A18 := A17.trans hs1138
    obtain ⟨v1141, u1141, g1141, w1141⟩ := AM.bind_ok w1137
    obtain ⟨hs1142, e1143⟩ := natAp2_run A18.ok (hp.mono A18.ext A18.pins) (denoteN_ext hn ((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext).trans hs1138.ext)) (denote_ext e8 ((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext).trans hs1138.ext)) (denote_ext e11 (((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext).trans hs1138.ext)) g1141
    have A19 := A18.trans hs1142
    obtain ⟨v1145, u1145, g1145, w1145⟩ := AM.bind_ok w1141
    obtain ⟨hs1146, e1147⟩ := eqAt1_run A19.ok (hp.mono A19.ext A19.pins) (denote_ext e5 ((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext).trans hs1138.ext).trans hs1142.ext)) e1143 (denote_ext e8 (((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs1106.ext).trans hs1110.ext).trans hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext).trans hs1138.ext).trans hs1142.ext)) g1145
    have A20 := A19.trans hs1146
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w1145
    refine ⟨A20, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_neg n0, if_pos (b1.mp y1)]
    exact ⟨denoteEList_one (denote_ext e1111 (((((((((hs1114.ext).trans hs1118.ext).trans hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext).trans hs1138.ext).trans hs1142.ext).trans hs1146.ext)),
        (denote_ext e1139 ((hs1142.ext).trans hs1146.ext)),
        denoteEList_one (denote_ext e1119 (((((((hs1122.ext).trans hs1126.ext).trans hs1130.ext).trans hs1134.ext).trans hs1138.ext).trans hs1142.ext).trans hs1146.ext)),
        e1147,
        trivial⟩
  have n1 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z1 (b1.mpr h)
  have b2 := beq_handle_iff A9.ok.wf (denoteN_ext hn (((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) d57
  rcases AM.ite_ok w1n with ⟨y2, w2y⟩ | ⟨z2, w2n⟩
  · -- natShiftRightName
    obtain ⟨v2149, u2149, g2149, w2149⟩ := AM.bind_ok w2y
    obtain ⟨hs2150, e2151⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) (denoteN_ext d16 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e14 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e11 ((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g2149
    have A10 := A9.trans hs2150
    obtain ⟨v2153, u2153, g2153, w2153⟩ := AM.bind_ok w2149
    obtain ⟨hs2154, e2155⟩ := eqAt1_run A10.ok (hp.mono A10.ext A10.pins) (denote_ext e21 (((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext)) e2151 (denote_ext e26 ((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext)) g2153
    have A11 := A10.trans hs2154
    obtain ⟨v2157, u2157, g2157, w2157⟩ := AM.bind_ok w2153
    obtain ⟨hs2158, e2159⟩ := natAp2_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d16 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext)) (denote_ext e14 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext)) (denote_ext e11 ((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext)) g2157
    have A12 := A11.trans hs2158
    obtain ⟨v2161, u2161, g2161, w2161⟩ := AM.bind_ok w2157
    obtain ⟨hs2162, e2163⟩ := eqAt1_run A12.ok (hp.mono A12.ext A12.pins) (denote_ext e21 (((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext)) e2159 (denote_ext e31 (((((hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext)) g2161
    have A13 := A12.trans hs2162
    obtain ⟨v2165, u2165, g2165, w2165⟩ := AM.bind_ok w2161
    obtain ⟨hs2166, e2167⟩ := natAp2_run A13.ok (hp.mono A13.ext A13.pins) (denoteN_ext hn (((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext)) (denote_ext e8 (((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext)) (denote_ext e11 ((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext)) g2165
    have A14 := A13.trans hs2166
    obtain ⟨v2169, u2169, g2169, w2169⟩ := AM.bind_ok w2165
    obtain ⟨hs2170, e2171⟩ := natAp2_run A14.ok (hp.mono A14.ext A14.pins) (denoteN_ext d51 (((((hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext)) (denote_ext e11 (((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext)) (denote_ext e14 ((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext)) g2169
    have A15 := A14.trans hs2170
    obtain ⟨v2173, u2173, g2173, w2173⟩ := AM.bind_ok w2169
    obtain ⟨hs2174, e2175⟩ := natAp2_run A15.ok (hp.mono A15.ext A15.pins) (denoteN_ext hn (((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext)) (denote_ext e8 (((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext)) e2171 g2173
    have A16 := A15.trans hs2174
    obtain ⟨v2177, u2177, g2177, w2177⟩ := AM.bind_ok w2173
    obtain ⟨hs2178, e2179⟩ := natAp2_run A16.ok (hp.mono A16.ext A16.pins) (denoteN_ext d45 (((((((hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext)) e2175 (denote_ext e41 (((((((hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext)) g2177
    have A17 := A16.trans hs2178
    obtain ⟨v2181, u2181, g2181, w2181⟩ := AM.bind_ok w2177
    obtain ⟨hs2182, e2183⟩ := eqAt1_run A17.ok (hp.mono A17.ext A17.pins) (denote_ext e5 ((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext)) (denote_ext e2167 (((hs2170.ext).trans hs2174.ext).trans hs2178.ext)) e2179 g2181
    have A18 := A17.trans hs2182
    obtain ⟨v2185, u2185, g2185, w2185⟩ := AM.bind_ok w2181
    obtain ⟨hs2186, e2187⟩ := natAp2_run A18.ok (hp.mono A18.ext A18.pins) (denoteN_ext hn ((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext).trans hs2182.ext)) (denote_ext e8 ((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext).trans hs2182.ext)) (denote_ext e11 (((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext).trans hs2182.ext)) g2185
    have A19 := A18.trans hs2186
    obtain ⟨v2189, u2189, g2189, w2189⟩ := AM.bind_ok w2185
    obtain ⟨hs2190, e2191⟩ := eqAt1_run A19.ok (hp.mono A19.ext A19.pins) (denote_ext e5 ((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext).trans hs2182.ext).trans hs2186.ext)) e2187 (denote_ext e8 (((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs2150.ext).trans hs2154.ext).trans hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext).trans hs2182.ext).trans hs2186.ext)) g2189
    have A20 := A19.trans hs2190
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w2189
    refine ⟨A20, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_neg n0, if_neg n1, if_pos (b2.mp y2)]
    exact ⟨denoteEList_one (denote_ext e2155 (((((((((hs2158.ext).trans hs2162.ext).trans hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext).trans hs2182.ext).trans hs2186.ext).trans hs2190.ext)),
        (denote_ext e2183 ((hs2186.ext).trans hs2190.ext)),
        denoteEList_one (denote_ext e2163 (((((((hs2166.ext).trans hs2170.ext).trans hs2174.ext).trans hs2178.ext).trans hs2182.ext).trans hs2186.ext).trans hs2190.ext)),
        e2191,
        trivial⟩
  have n2 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z2 (b2.mpr h)
  have b3 := beq_handle_iff A9.ok.wf (denoteN_ext hn (((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) d59
  rcases AM.ite_ok w2n with ⟨y3, w3y⟩ | ⟨z3, w3n⟩
  · -- natLandName
    obtain ⟨v3193, u3193, g3193, w3193⟩ := AM.bind_ok w3y
    obtain ⟨hs3194, e3195⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) (denoteN_ext d16 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e14 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e8 (((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g3193
    have A10 := A9.trans hs3194
    obtain ⟨v3197, u3197, g3197, w3197⟩ := AM.bind_ok w3193
    obtain ⟨hs3198, e3199⟩ := eqAt1_run A10.ok (hp.mono A10.ext A10.pins) (denote_ext e21 (((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext)) e3195 (denote_ext e26 ((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext)) g3197
    have A11 := A10.trans hs3198
    obtain ⟨v3201, u3201, g3201, w3201⟩ := AM.bind_ok w3197
    obtain ⟨hs3202, e3203⟩ := natAp2_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d16 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext)) (denote_ext e14 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext)) (denote_ext e8 (((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext)) g3201
    have A12 := A11.trans hs3202
    obtain ⟨v3205, u3205, g3205, w3205⟩ := AM.bind_ok w3201
    obtain ⟨hs3206, e3207⟩ := eqAt1_run A12.ok (hp.mono A12.ext A12.pins) (denote_ext e21 (((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext)) e3203 (denote_ext e31 (((((hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext)) g3205
    have A13 := A12.trans hs3206
    obtain ⟨v3209, u3209, g3209, w3209⟩ := AM.bind_ok w3205
    obtain ⟨hs3210, e3211⟩ := natAp2_run A13.ok (hp.mono A13.ext A13.pins) (denoteN_ext d45 ((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext)) (denote_ext e8 (((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext)) (denote_ext e41 ((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext)) g3209
    have A14 := A13.trans hs3210
    obtain ⟨v3213, u3213, g3213, w3213⟩ := AM.bind_ok w3209
    obtain ⟨hs3214, e3215⟩ := natAp2_run A14.ok (hp.mono A14.ext A14.pins) (denoteN_ext d45 (((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext)) (denote_ext e11 (((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext)) (denote_ext e41 (((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext)) g3213
    have A15 := A14.trans hs3214
    obtain ⟨v3217, u3217, g3217, w3217⟩ := AM.bind_ok w3213
    obtain ⟨hs3218, e3219⟩ := natAp2_run A15.ok (hp.mono A15.ext A15.pins) (denoteN_ext hn (((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext)) (denote_ext e3211 (hs3214.ext)) e3215 g3217
    have A16 := A15.trans hs3218
    obtain ⟨v3221, u3221, g3221, w3221⟩ := AM.bind_ok w3217
    obtain ⟨hs3222, e3223⟩ := natAp2_run A16.ok (hp.mono A16.ext A16.pins) (denoteN_ext hn ((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext)) (denote_ext e8 ((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext)) (denote_ext e11 (((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext)) g3221
    have A17 := A16.trans hs3222
    obtain ⟨v3225, u3225, g3225, w3225⟩ := AM.bind_ok w3221
    obtain ⟨hs3226, e3227⟩ := natAp2_run A17.ok (hp.mono A17.ext A17.pins) (denoteN_ext d49 ((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext)) (denote_ext e41 ((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext)) (denote_ext e3219 (hs3222.ext)) g3225
    have A18 := A17.trans hs3226
    obtain ⟨v3229, u3229, g3229, w3229⟩ := AM.bind_ok w3225
    obtain ⟨hs3230, e3231⟩ := natAp2_run A18.ok (hp.mono A18.ext A18.pins) (denoteN_ext d43 (((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext)) (denote_ext e8 ((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext)) (denote_ext e41 (((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext)) g3229
    have A19 := A18.trans hs3230
    obtain ⟨v3233, u3233, g3233, w3233⟩ := AM.bind_ok w3229
    obtain ⟨hs3234, e3235⟩ := natAp2_run A19.ok (hp.mono A19.ext A19.pins) (denoteN_ext d43 ((((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext)) (denote_ext e11 ((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext)) (denote_ext e41 ((((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext)) g3233
    have A20 := A19.trans hs3234
    obtain ⟨v3237, u3237, g3237, w3237⟩ := AM.bind_ok w3233
    obtain ⟨hs3238, e3239⟩ := natAp2_run A20.ok (hp.mono A20.ext A20.pins) (denoteN_ext d49 (((((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext)) (denote_ext e3231 (hs3234.ext)) e3235 g3237
    have A21 := A20.trans hs3238
    obtain ⟨v3241, u3241, g3241, w3241⟩ := AM.bind_ok w3237
    obtain ⟨hs3242, e3243⟩ := natAp2_run A21.ok (hp.mono A21.ext A21.pins) (denoteN_ext d47 ((((((((((((hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext)) (denote_ext e3227 (((hs3230.ext).trans hs3234.ext).trans hs3238.ext)) e3239 g3241
    have A22 := A21.trans hs3242
    obtain ⟨v3245, u3245, g3245, w3245⟩ := AM.bind_ok w3241
    obtain ⟨hs3246, e3247⟩ := eqAt1_run A22.ok (hp.mono A22.ext A22.pins) (denote_ext e5 (((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext)) (denote_ext e3223 (((((hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext)) e3243 g3245
    have A23 := A22.trans hs3246
    obtain ⟨v3249, u3249, g3249, w3249⟩ := AM.bind_ok w3245
    obtain ⟨hs3250, e3251⟩ := natAp2_run A23.ok (hp.mono A23.ext A23.pins) (denoteN_ext hn (((((((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext).trans hs3246.ext)) (denote_ext e8 (((((((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext).trans hs3246.ext)) (denote_ext e11 ((((((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext).trans hs3246.ext)) g3249
    have A24 := A23.trans hs3250
    obtain ⟨v3253, u3253, g3253, w3253⟩ := AM.bind_ok w3249
    obtain ⟨hs3254, e3255⟩ := eqAt1_run A24.ok (hp.mono A24.ext A24.pins) (denote_ext e5 (((((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext).trans hs3246.ext).trans hs3250.ext)) e3251 (denote_ext e36 ((((((((((((((((hs40.ext).trans hs3194.ext).trans hs3198.ext).trans hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext).trans hs3246.ext).trans hs3250.ext)) g3253
    have A25 := A24.trans hs3254
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w3253
    refine ⟨A25, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_neg n0, if_neg n1, if_neg n2, if_pos (b3.mp y3)]
    exact ⟨denoteEList_one (denote_ext e3199 ((((((((((((((hs3202.ext).trans hs3206.ext).trans hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext).trans hs3246.ext).trans hs3250.ext).trans hs3254.ext)),
        (denote_ext e3247 ((hs3250.ext).trans hs3254.ext)),
        denoteEList_one (denote_ext e3207 ((((((((((((hs3210.ext).trans hs3214.ext).trans hs3218.ext).trans hs3222.ext).trans hs3226.ext).trans hs3230.ext).trans hs3234.ext).trans hs3238.ext).trans hs3242.ext).trans hs3246.ext).trans hs3250.ext).trans hs3254.ext)),
        e3255,
        trivial⟩
  have n3 : ¬ (nm = ConLeche.natLandName) := fun h => z3 (b3.mpr h)
  have b4 := beq_handle_iff A9.ok.wf (denoteN_ext hn (((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) d61
  rcases AM.ite_ok w3n with ⟨y4, w4y⟩ | ⟨z4, w4n⟩
  · -- natLorName
    obtain ⟨v4257, u4257, g4257, w4257⟩ := AM.bind_ok w4y
    obtain ⟨hs4258, e4259⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) (denoteN_ext d16 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e14 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e8 (((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g4257
    have A10 := A9.trans hs4258
    obtain ⟨v4261, u4261, g4261, w4261⟩ := AM.bind_ok w4257
    obtain ⟨hs4262, e4263⟩ := eqAt1_run A10.ok (hp.mono A10.ext A10.pins) (denote_ext e21 (((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext)) e4259 (denote_ext e26 ((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext)) g4261
    have A11 := A10.trans hs4262
    obtain ⟨v4265, u4265, g4265, w4265⟩ := AM.bind_ok w4261
    obtain ⟨hs4266, e4267⟩ := natAp2_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d16 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext)) (denote_ext e14 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext)) (denote_ext e8 (((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext)) g4265
    have A12 := A11.trans hs4266
    obtain ⟨v4269, u4269, g4269, w4269⟩ := AM.bind_ok w4265
    obtain ⟨hs4270, e4271⟩ := eqAt1_run A12.ok (hp.mono A12.ext A12.pins) (denote_ext e21 (((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext)) e4267 (denote_ext e31 (((((hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext)) g4269
    have A13 := A12.trans hs4270
    obtain ⟨v4273, u4273, g4273, w4273⟩ := AM.bind_ok w4269
    obtain ⟨hs4274, e4275⟩ := natAp2_run A13.ok (hp.mono A13.ext A13.pins) (denoteN_ext d45 ((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext)) (denote_ext e8 (((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext)) (denote_ext e41 ((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext)) g4273
    have A14 := A13.trans hs4274
    obtain ⟨v4277, u4277, g4277, w4277⟩ := AM.bind_ok w4273
    obtain ⟨hs4278, e4279⟩ := natAp2_run A14.ok (hp.mono A14.ext A14.pins) (denoteN_ext d45 (((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext)) (denote_ext e11 (((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext)) (denote_ext e41 (((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext)) g4277
    have A15 := A14.trans hs4278
    obtain ⟨v4281, u4281, g4281, w4281⟩ := AM.bind_ok w4277
    obtain ⟨hs4282, e4283⟩ := natAp2_run A15.ok (hp.mono A15.ext A15.pins) (denoteN_ext hn (((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext)) (denote_ext e4275 (hs4278.ext)) e4279 g4281
    have A16 := A15.trans hs4282
    obtain ⟨v4285, u4285, g4285, w4285⟩ := AM.bind_ok w4281
    obtain ⟨hs4286, e4287⟩ := natAp2_run A16.ok (hp.mono A16.ext A16.pins) (denoteN_ext d43 (((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext)) (denote_ext e8 ((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext)) (denote_ext e41 (((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext)) g4285
    have A17 := A16.trans hs4286
    obtain ⟨v4289, u4289, g4289, w4289⟩ := AM.bind_ok w4285
    obtain ⟨hs4290, e4291⟩ := natAp2_run A17.ok (hp.mono A17.ext A17.pins) (denoteN_ext d43 ((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext)) (denote_ext e11 ((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext)) (denote_ext e41 ((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext)) g4289
    have A18 := A17.trans hs4290
    obtain ⟨v4293, u4293, g4293, w4293⟩ := AM.bind_ok w4289
    obtain ⟨hs4294, e4295⟩ := natAp2_run A18.ok (hp.mono A18.ext A18.pins) (denoteN_ext hn ((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext)) (denote_ext e8 ((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext)) (denote_ext e11 (((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext)) g4293
    have A19 := A18.trans hs4294
    obtain ⟨v4297, u4297, g4297, w4297⟩ := AM.bind_ok w4293
    obtain ⟨hs4298, e4299⟩ := natAp2_run A19.ok (hp.mono A19.ext A19.pins) (denoteN_ext d49 ((((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext)) (denote_ext e41 ((((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext)) (denote_ext e4283 (((hs4286.ext).trans hs4290.ext).trans hs4294.ext)) g4297
    have A20 := A19.trans hs4298
    obtain ⟨v4301, u4301, g4301, w4301⟩ := AM.bind_ok w4297
    obtain ⟨hs4302, e4303⟩ := natAp2_run A20.ok (hp.mono A20.ext A20.pins) (denoteN_ext d47 (((((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext)) (denote_ext e4287 (((hs4290.ext).trans hs4294.ext).trans hs4298.ext)) (denote_ext e4291 ((hs4294.ext).trans hs4298.ext)) g4301
    have A21 := A20.trans hs4302
    obtain ⟨v4305, u4305, g4305, w4305⟩ := AM.bind_ok w4301
    obtain ⟨hs4306, e4307⟩ := natAp2_run A21.ok (hp.mono A21.ext A21.pins) (denoteN_ext d49 ((((((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext)) (denote_ext e4287 ((((hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext)) (denote_ext e4291 (((hs4294.ext).trans hs4298.ext).trans hs4302.ext)) g4305
    have A22 := A21.trans hs4306
    obtain ⟨v4309, u4309, g4309, w4309⟩ := AM.bind_ok w4305
    obtain ⟨hs4310, e4311⟩ := natAp2_run A22.ok (hp.mono A22.ext A22.pins) (denoteN_ext d51 (((((((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext)) (denote_ext e4303 (hs4306.ext)) e4307 g4309
    have A23 := A22.trans hs4310
    obtain ⟨v4313, u4313, g4313, w4313⟩ := AM.bind_ok w4309
    obtain ⟨hs4314, e4315⟩ := natAp2_run A23.ok (hp.mono A23.ext A23.pins) (denoteN_ext d47 ((((((((((((((hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext)) (denote_ext e4299 (((hs4302.ext).trans hs4306.ext).trans hs4310.ext)) e4311 g4313
    have A24 := A23.trans hs4314
    obtain ⟨v4317, u4317, g4317, w4317⟩ := AM.bind_ok w4313
    obtain ⟨hs4318, e4319⟩ := eqAt1_run A24.ok (hp.mono A24.ext A24.pins) (denote_ext e5 (((((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext)) (denote_ext e4295 (((((hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext)) e4315 g4317
    have A25 := A24.trans hs4318
    obtain ⟨v4321, u4321, g4321, w4321⟩ := AM.bind_ok w4317
    obtain ⟨hs4322, e4323⟩ := natAp2_run A25.ok (hp.mono A25.ext A25.pins) (denoteN_ext hn (((((((((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext).trans hs4318.ext)) (denote_ext e8 (((((((((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext).trans hs4318.ext)) (denote_ext e11 ((((((((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext).trans hs4318.ext)) g4321
    have A26 := A25.trans hs4322
    obtain ⟨v4325, u4325, g4325, w4325⟩ := AM.bind_ok w4321
    obtain ⟨hs4326, e4327⟩ := eqAt1_run A26.ok (hp.mono A26.ext A26.pins) (denote_ext e5 (((((((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext).trans hs4318.ext).trans hs4322.ext)) e4323 (denote_ext e11 (((((((((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs4258.ext).trans hs4262.ext).trans hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext).trans hs4318.ext).trans hs4322.ext)) g4325
    have A27 := A26.trans hs4326
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w4325
    refine ⟨A27, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_pos (b4.mp y4)]
    exact ⟨denoteEList_one (denote_ext e4263 ((((((((((((((((hs4266.ext).trans hs4270.ext).trans hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext).trans hs4318.ext).trans hs4322.ext).trans hs4326.ext)),
        (denote_ext e4319 ((hs4322.ext).trans hs4326.ext)),
        denoteEList_one (denote_ext e4271 ((((((((((((((hs4274.ext).trans hs4278.ext).trans hs4282.ext).trans hs4286.ext).trans hs4290.ext).trans hs4294.ext).trans hs4298.ext).trans hs4302.ext).trans hs4306.ext).trans hs4310.ext).trans hs4314.ext).trans hs4318.ext).trans hs4322.ext).trans hs4326.ext)),
        e4327,
        trivial⟩
  have n4 : ¬ (nm = ConLeche.natLorName) := fun h => z4 (b4.mpr h)
  have b5 := beq_handle_iff A9.ok.wf (denoteN_ext hn (((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) d63
  rcases AM.ite_ok w4n with ⟨y5, w5y⟩ | ⟨z5, w5n⟩
  · -- natXorName
    obtain ⟨v5329, u5329, g5329, w5329⟩ := AM.bind_ok w5y
    obtain ⟨hs5330, e5331⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) (denoteN_ext d16 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e14 (((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e8 (((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g5329
    have A10 := A9.trans hs5330
    obtain ⟨v5333, u5333, g5333, w5333⟩ := AM.bind_ok w5329
    obtain ⟨hs5334, e5335⟩ := eqAt1_run A10.ok (hp.mono A10.ext A10.pins) (denote_ext e21 (((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext)) e5331 (denote_ext e26 ((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext)) g5333
    have A11 := A10.trans hs5334
    obtain ⟨v5337, u5337, g5337, w5337⟩ := AM.bind_ok w5333
    obtain ⟨hs5338, e5339⟩ := natAp2_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d16 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext)) (denote_ext e14 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext)) (denote_ext e8 (((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext)) g5337
    have A12 := A11.trans hs5338
    obtain ⟨v5341, u5341, g5341, w5341⟩ := AM.bind_ok w5337
    obtain ⟨hs5342, e5343⟩ := eqAt1_run A12.ok (hp.mono A12.ext A12.pins) (denote_ext e21 (((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext)) e5339 (denote_ext e31 (((((hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext)) g5341
    have A13 := A12.trans hs5342
    obtain ⟨v5345, u5345, g5345, w5345⟩ := AM.bind_ok w5341
    obtain ⟨hs5346, e5347⟩ := natAp2_run A13.ok (hp.mono A13.ext A13.pins) (denoteN_ext d45 ((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext)) (denote_ext e8 (((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext)) (denote_ext e41 ((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext)) g5345
    have A14 := A13.trans hs5346
    obtain ⟨v5349, u5349, g5349, w5349⟩ := AM.bind_ok w5345
    obtain ⟨hs5350, e5351⟩ := natAp2_run A14.ok (hp.mono A14.ext A14.pins) (denoteN_ext d45 (((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext)) (denote_ext e11 (((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext)) (denote_ext e41 (((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext)) g5349
    have A15 := A14.trans hs5350
    obtain ⟨v5353, u5353, g5353, w5353⟩ := AM.bind_ok w5349
    obtain ⟨hs5354, e5355⟩ := natAp2_run A15.ok (hp.mono A15.ext A15.pins) (denoteN_ext hn (((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext)) (denote_ext e5347 (hs5350.ext)) e5351 g5353
    have A16 := A15.trans hs5354
    obtain ⟨v5357, u5357, g5357, w5357⟩ := AM.bind_ok w5353
    obtain ⟨hs5358, e5359⟩ := natAp2_run A16.ok (hp.mono A16.ext A16.pins) (denoteN_ext d43 (((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext)) (denote_ext e8 ((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext)) (denote_ext e41 (((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext)) g5357
    have A17 := A16.trans hs5358
    obtain ⟨v5361, u5361, g5361, w5361⟩ := AM.bind_ok w5357
    obtain ⟨hs5362, e5363⟩ := natAp2_run A17.ok (hp.mono A17.ext A17.pins) (denoteN_ext d43 ((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext)) (denote_ext e11 ((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext)) (denote_ext e41 ((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext)) g5361
    have A18 := A17.trans hs5362
    obtain ⟨v5365, u5365, g5365, w5365⟩ := AM.bind_ok w5361
    obtain ⟨hs5366, e5367⟩ := natAp2_run A18.ok (hp.mono A18.ext A18.pins) (denoteN_ext hn ((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext)) (denote_ext e8 ((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext)) (denote_ext e11 (((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext)) g5365
    have A19 := A18.trans hs5366
    obtain ⟨v5369, u5369, g5369, w5369⟩ := AM.bind_ok w5365
    obtain ⟨hs5370, e5371⟩ := natAp2_run A19.ok (hp.mono A19.ext A19.pins) (denoteN_ext d49 ((((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext)) (denote_ext e41 ((((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext)) (denote_ext e5355 (((hs5358.ext).trans hs5362.ext).trans hs5366.ext)) g5369
    have A20 := A19.trans hs5370
    obtain ⟨v5373, u5373, g5373, w5373⟩ := AM.bind_ok w5369
    obtain ⟨hs5374, e5375⟩ := natAp2_run A20.ok (hp.mono A20.ext A20.pins) (denoteN_ext d47 (((((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext)) (denote_ext e5359 (((hs5362.ext).trans hs5366.ext).trans hs5370.ext)) (denote_ext e5363 ((hs5366.ext).trans hs5370.ext)) g5373
    have A21 := A20.trans hs5374
    obtain ⟨v5377, u5377, g5377, w5377⟩ := AM.bind_ok w5373
    obtain ⟨hs5378, e5379⟩ := natAp2_run A21.ok (hp.mono A21.ext A21.pins) (denoteN_ext d43 ((((((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext)) e5375 (denote_ext e41 ((((((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext)) g5377
    have A22 := A21.trans hs5378
    obtain ⟨v5381, u5381, g5381, w5381⟩ := AM.bind_ok w5377
    obtain ⟨hs5382, e5383⟩ := natAp2_run A22.ok (hp.mono A22.ext A22.pins) (denoteN_ext d47 (((((((((((((hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext)) (denote_ext e5371 ((hs5374.ext).trans hs5378.ext)) e5379 g5381
    have A23 := A22.trans hs5382
    obtain ⟨v5385, u5385, g5385, w5385⟩ := AM.bind_ok w5381
    obtain ⟨hs5386, e5387⟩ := eqAt1_run A23.ok (hp.mono A23.ext A23.pins) (denote_ext e5 ((((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext)) (denote_ext e5367 ((((hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext)) e5383 g5385
    have A24 := A23.trans hs5386
    obtain ⟨v5389, u5389, g5389, w5389⟩ := AM.bind_ok w5385
    obtain ⟨hs5390, e5391⟩ := natAp2_run A24.ok (hp.mono A24.ext A24.pins) (denoteN_ext hn ((((((((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext).trans hs5386.ext)) (denote_ext e8 ((((((((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext).trans hs5386.ext)) (denote_ext e11 (((((((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext).trans hs5386.ext)) g5389
    have A25 := A24.trans hs5390
    obtain ⟨v5393, u5393, g5393, w5393⟩ := AM.bind_ok w5389
    obtain ⟨hs5394, e5395⟩ := eqAt1_run A25.ok (hp.mono A25.ext A25.pins) (denote_ext e5 ((((((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext).trans hs5386.ext).trans hs5390.ext)) e5391 (denote_ext e11 ((((((((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs5330.ext).trans hs5334.ext).trans hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext).trans hs5386.ext).trans hs5390.ext)) g5393
    have A26 := A25.trans hs5394
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w5393
    refine ⟨A26, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_pos (b5.mp y5)]
    exact ⟨denoteEList_one (denote_ext e5335 (((((((((((((((hs5338.ext).trans hs5342.ext).trans hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext).trans hs5386.ext).trans hs5390.ext).trans hs5394.ext)),
        (denote_ext e5387 ((hs5390.ext).trans hs5394.ext)),
        denoteEList_one (denote_ext e5343 (((((((((((((hs5346.ext).trans hs5350.ext).trans hs5354.ext).trans hs5358.ext).trans hs5362.ext).trans hs5366.ext).trans hs5370.ext).trans hs5374.ext).trans hs5378.ext).trans hs5382.ext).trans hs5386.ext).trans hs5390.ext).trans hs5394.ext)),
        e5395,
        trivial⟩
  have n5 : ¬ (nm = ConLeche.natXorName) := fun h => z5 (b5.mpr h)
  have bd := beq_handle_iff A9.ok.wf (denoteN_ext hn (((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) d45
  rcases AM.ite_ok w5n with ⟨hd, wdy⟩ | ⟨hd, wdn⟩
  · -- Nat.div
    obtain ⟨v6396, u6396, g6396, w6396⟩ := AM.bind_ok wdy
    obtain ⟨rfl, d6397⟩ := pinAt_run (x := ConLeche.natSuccName) (hp.mono A9.ext A9.pins) rfl g6396
    obtain ⟨v6399, u6399, g6399, w6399⟩ := AM.bind_ok w6396
    obtain ⟨hs6400, e6401⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) d51 (denote_ext e8 (((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e11 ((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g6399
    have A10 := A9.trans hs6400
    obtain ⟨v6403, u6403, g6403, w6403⟩ := AM.bind_ok w6399
    obtain ⟨hs6404, e6405⟩ := natAp2_run A10.ok (hp.mono A10.ext A10.pins) (denoteN_ext hn ((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext)) e6401 (denote_ext e11 (((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext)) g6403
    have A11 := A10.trans hs6404
    obtain ⟨v6406, u6406, g6406, w6406⟩ := AM.bind_ok w6403
    obtain ⟨hs6407, e6408⟩ := natAp1_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d6397 ((hs6400.ext).trans hs6404.ext)) e6405 g6406
    have A12 := A11.trans hs6407
    rcases AM.ite_ok w6406 with ⟨hd2, wi⟩ | ⟨hd2, wi⟩
    rotate_left
    · exact absurd hd hd2
    obtain ⟨v6409, u6409, g6409, w6409⟩ := AM.bind_ok wi
    obtain ⟨rfl, rfl⟩ := AM.pure_ok g6409
    obtain ⟨v6411, u6411, g6411, w6411⟩ := AM.bind_ok w6409
    obtain ⟨hs6412, e6413⟩ := natAp2_run A12.ok (hp.mono A12.ext A12.pins) (denoteN_ext d16 ((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext)) (denote_ext e11 (((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext)) (denote_ext e8 ((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext)) g6411
    have A13 := A12.trans hs6412
    obtain ⟨v6415, u6415, g6415, w6415⟩ := AM.bind_ok w6411
    obtain ⟨hs6416, e6417⟩ := eqAt1_run A13.ok (hp.mono A13.ext A13.pins) (denote_ext e21 ((((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext)) e6413 (denote_ext e26 (((((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext)) g6415
    have A14 := A13.trans hs6416
    obtain ⟨v6419, u6419, g6419, w6419⟩ := AM.bind_ok w6415
    obtain ⟨hs6420, e6421⟩ := natAp2_run A14.ok (hp.mono A14.ext A14.pins) (denoteN_ext d16 ((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext)) (denote_ext e14 ((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext)) (denote_ext e11 (((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext)) g6419
    have A15 := A14.trans hs6420
    obtain ⟨v6423, u6423, g6423, w6423⟩ := AM.bind_ok w6419
    obtain ⟨hs6424, e6425⟩ := eqAt1_run A15.ok (hp.mono A15.ext A15.pins) (denote_ext e21 ((((((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext)) e6421 (denote_ext e26 (((((((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext)) g6423
    have A16 := A15.trans hs6424
    obtain ⟨v6427, u6427, g6427, w6427⟩ := AM.bind_ok w6423
    obtain ⟨hs6428, e6429⟩ := natAp2_run A16.ok (hp.mono A16.ext A16.pins) (denoteN_ext d16 ((((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext)) (denote_ext e11 (((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext)) (denote_ext e8 ((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext)) g6427
    have A17 := A16.trans hs6428
    obtain ⟨v6431, u6431, g6431, w6431⟩ := AM.bind_ok w6427
    obtain ⟨hs6432, e6433⟩ := eqAt1_run A17.ok (hp.mono A17.ext A17.pins) (denote_ext e21 ((((((((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext)) e6429 (denote_ext e31 ((((((((((hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext)) g6431
    have A18 := A17.trans hs6432
    obtain ⟨v6435, u6435, g6435, w6435⟩ := AM.bind_ok w6431
    obtain ⟨hs6436, e6437⟩ := natAp2_run A18.ok (hp.mono A18.ext A18.pins) (denoteN_ext d16 ((((((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext)) (denote_ext e14 ((((((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext)) (denote_ext e11 (((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext)) g6435
    have A19 := A18.trans hs6436
    obtain ⟨v6439, u6439, g6439, w6439⟩ := AM.bind_ok w6435
    obtain ⟨hs6440, e6441⟩ := eqAt1_run A19.ok (hp.mono A19.ext A19.pins) (denote_ext e21 ((((((((((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext)) e6437 (denote_ext e31 ((((((((((((hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext)) g6439
    have A20 := A19.trans hs6440
    obtain ⟨v6443, u6443, g6443, w6443⟩ := AM.bind_ok w6439
    obtain ⟨hs6444, e6445⟩ := natAp2_run A20.ok (hp.mono A20.ext A20.pins) (denoteN_ext hn ((((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext)) (denote_ext e8 ((((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext)) (denote_ext e11 (((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext)) g6443
    have A21 := A20.trans hs6444
    obtain ⟨v6447, u6447, g6447, w6447⟩ := AM.bind_ok w6443
    obtain ⟨hs6448, e6449⟩ := eqAt1_run A21.ok (hp.mono A21.ext A21.pins) (denote_ext e5 ((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext)) e6445 (denote_ext e6408 (((((((((hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext)) g6447
    have A22 := A21.trans hs6448
    obtain ⟨v6451, u6451, g6451, w6451⟩ := AM.bind_ok w6447
    obtain ⟨hs6452, e6453⟩ := natAp2_run A22.ok (hp.mono A22.ext A22.pins) (denoteN_ext hn ((((((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext)) (denote_ext e8 ((((((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext)) (denote_ext e11 (((((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext)) g6451
    have A23 := A22.trans hs6452
    obtain ⟨v6455, u6455, g6455, w6455⟩ := AM.bind_ok w6451
    obtain ⟨hs6456, e6457⟩ := eqAt1_run A23.ok (hp.mono A23.ext A23.pins) (denote_ext e5 ((((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext).trans hs6452.ext)) e6453 (denote_ext e36 (((((((((((((((hs40.ext).trans hs6400.ext).trans hs6404.ext).trans hs6407.ext).trans hs6412.ext).trans hs6416.ext).trans hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext).trans hs6452.ext)) g6455
    have A24 := A23.trans hs6456
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w6455
    refine ⟨A24, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_pos (bd.mp hd)]
    exact ⟨denoteEList_two (denote_ext e6417 ((((((((((hs6420.ext).trans hs6424.ext).trans hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext).trans hs6452.ext).trans hs6456.ext)) (denote_ext e6425 ((((((((hs6428.ext).trans hs6432.ext).trans hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext).trans hs6452.ext).trans hs6456.ext)),
        (denote_ext e6449 ((hs6452.ext).trans hs6456.ext)),
        denoteEList_one (denote_ext e6433 ((((((hs6436.ext).trans hs6440.ext).trans hs6444.ext).trans hs6448.ext).trans hs6452.ext).trans hs6456.ext)),
        e6457,
        denoteEList_one (denote_ext e6441 ((((hs6444.ext).trans hs6448.ext).trans hs6452.ext).trans hs6456.ext)),
        e6457,
        trivial⟩
  · -- Nat.mod
    obtain ⟨v7459, u7459, g7459, w7459⟩ := AM.bind_ok wdn
    obtain ⟨hs7460, e7461⟩ := natAp2_run A9.ok (hp.mono A9.ext A9.pins) d51 (denote_ext e8 (((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) (denote_ext e11 ((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext)) g7459
    have A10 := A9.trans hs7460
    obtain ⟨v7462, u7462, g7462, w7462⟩ := AM.bind_ok w7459
    obtain ⟨hs7463, e7464⟩ := natAp2_run A10.ok (hp.mono A10.ext A10.pins) (denoteN_ext hn ((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext)) e7461 (denote_ext e11 (((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext)) g7462
    have A11 := A10.trans hs7463
    rcases AM.ite_ok w7462 with ⟨hd2, wi⟩ | ⟨hd2, wi⟩
    · exact absurd hd2 hd
    obtain ⟨v7465, u7465, g7465, w7465⟩ := AM.bind_ok wi
    obtain ⟨rfl, rfl⟩ := AM.pure_ok g7465
    obtain ⟨v7467, u7467, g7467, w7467⟩ := AM.bind_ok w7465
    obtain ⟨hs7468, e7469⟩ := natAp2_run A11.ok (hp.mono A11.ext A11.pins) (denoteN_ext d16 (((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext)) (denote_ext e11 ((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext)) (denote_ext e8 (((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext)) g7467
    have A12 := A11.trans hs7468
    obtain ⟨v7471, u7471, g7471, w7471⟩ := AM.bind_ok w7467
    obtain ⟨hs7472, e7473⟩ := eqAt1_run A12.ok (hp.mono A12.ext A12.pins) (denote_ext e21 (((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext)) e7469 (denote_ext e26 ((((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext)) g7471
    have A13 := A12.trans hs7472
    obtain ⟨v7475, u7475, g7475, w7475⟩ := AM.bind_ok w7471
    obtain ⟨hs7476, e7477⟩ := natAp2_run A13.ok (hp.mono A13.ext A13.pins) (denoteN_ext d16 (((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext)) (denote_ext e14 (((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext)) (denote_ext e11 ((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext)) g7475
    have A14 := A13.trans hs7476
    obtain ⟨v7479, u7479, g7479, w7479⟩ := AM.bind_ok w7475
    obtain ⟨hs7480, e7481⟩ := eqAt1_run A14.ok (hp.mono A14.ext A14.pins) (denote_ext e21 (((((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext)) e7477 (denote_ext e26 ((((((((hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext)) g7479
    have A15 := A14.trans hs7480
    obtain ⟨v7483, u7483, g7483, w7483⟩ := AM.bind_ok w7479
    obtain ⟨hs7484, e7485⟩ := natAp2_run A15.ok (hp.mono A15.ext A15.pins) (denoteN_ext d16 (((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext)) (denote_ext e11 ((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext)) (denote_ext e8 (((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext)) g7483
    have A16 := A15.trans hs7484
    obtain ⟨v7487, u7487, g7487, w7487⟩ := AM.bind_ok w7483
    obtain ⟨hs7488, e7489⟩ := eqAt1_run A16.ok (hp.mono A16.ext A16.pins) (denote_ext e21 (((((((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext)) e7485 (denote_ext e31 (((((((((hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext)) g7487
    have A17 := A16.trans hs7488
    obtain ⟨v7491, u7491, g7491, w7491⟩ := AM.bind_ok w7487
    obtain ⟨hs7492, e7493⟩ := natAp2_run A17.ok (hp.mono A17.ext A17.pins) (denoteN_ext d16 (((((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext)) (denote_ext e14 (((((((((((((hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext)) (denote_ext e11 ((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext)) g7491
    have A18 := A17.trans hs7492
    obtain ⟨v7495, u7495, g7495, w7495⟩ := AM.bind_ok w7491
    obtain ⟨hs7496, e7497⟩ := eqAt1_run A18.ok (hp.mono A18.ext A18.pins) (denote_ext e21 (((((((((((((hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext)) e7493 (denote_ext e31 (((((((((((hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext)) g7495
    have A19 := A18.trans hs7496
    obtain ⟨v7499, u7499, g7499, w7499⟩ := AM.bind_ok w7495
    obtain ⟨hs7500, e7501⟩ := natAp2_run A19.ok (hp.mono A19.ext A19.pins) (denoteN_ext hn (((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext)) (denote_ext e8 (((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext)) (denote_ext e11 ((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext)) g7499
    have A20 := A19.trans hs7500
    obtain ⟨v7503, u7503, g7503, w7503⟩ := AM.bind_ok w7499
    obtain ⟨hs7504, e7505⟩ := eqAt1_run A20.ok (hp.mono A20.ext A20.pins) (denote_ext e5 (((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext)) e7501 (denote_ext e7464 (((((((((hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext)) g7503
    have A21 := A20.trans hs7504
    obtain ⟨v7507, u7507, g7507, w7507⟩ := AM.bind_ok w7503
    obtain ⟨hs7508, e7509⟩ := natAp2_run A21.ok (hp.mono A21.ext A21.pins) (denoteN_ext hn (((((((((((((((((((((hs4.ext).trans hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext)) (denote_ext e8 (((((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext)) (denote_ext e11 ((((((((((((((((((hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext)) g7507
    have A22 := A21.trans hs7508
    obtain ⟨v7511, u7511, g7511, w7511⟩ := AM.bind_ok w7507
    obtain ⟨hs7512, e7513⟩ := eqAt1_run A22.ok (hp.mono A22.ext A22.pins) (denote_ext e5 (((((((((((((((((((((hs7.ext).trans hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext).trans hs7508.ext)) e7509 (denote_ext e8 ((((((((((((((((((((hs10.ext).trans hs13.ext).trans hs20.ext).trans hs25.ext).trans hs30.ext).trans hs35.ext).trans hs40.ext).trans hs7460.ext).trans hs7463.ext).trans hs7468.ext).trans hs7472.ext).trans hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext).trans hs7508.ext)) g7511
    have A23 := A22.trans hs7512
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w7511
    refine ⟨A23, ?_⟩
    simp only [ConLeche.divModCertStmts, StmtsDenote, if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg (fun h => hd (bd.mpr h))]
    exact ⟨denoteEList_two (denote_ext e7473 ((((((((((hs7476.ext).trans hs7480.ext).trans hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext).trans hs7508.ext).trans hs7512.ext)) (denote_ext e7481 ((((((((hs7484.ext).trans hs7488.ext).trans hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext).trans hs7508.ext).trans hs7512.ext)),
        (denote_ext e7505 ((hs7508.ext).trans hs7512.ext)),
        denoteEList_one (denote_ext e7489 ((((((hs7492.ext).trans hs7496.ext).trans hs7500.ext).trans hs7504.ext).trans hs7508.ext).trans hs7512.ext)),
        e7513,
        denoteEList_one (denote_ext e7497 ((((hs7500.ext).trans hs7504.ext).trans hs7508.ext).trans hs7512.ext)),
        e7513,
        trivial⟩


/-! ## The certificate guards

A guard chain here reads the store through the Fast walks (which keep the store
and may touch the memos) and interns substitutions, so its frame is the Core
tier's `CoreStep` rather than `IStepS`: `RunsC` is `RunsB` at that frame. -/

/-- con-leche: none — every success of `m` at `s` is a `CoreStep` answering
`b`. -/
def RunsC (μ : CheckMode) (env : Env) (fe : IFEnv) (m : AM Bool) (s : AState) (b : Bool) :
    Prop :=
  ∀ (r : Bool) (s' : AState), m s = .ok (r, s') → CoreStep μ env fe s s' ∧ r = b

theorem RunsC.ret {μ : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (hck : CheckOK μ env fe s) {b : Bool} : RunsC μ env fe (Pure.pure b) s b := by
  intro r s' h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h
  exact ⟨CoreStep.refl hck, rfl⟩

theorem RunsC.bind {μ : CheckMode} {env : Env} {fe : IFEnv} {α : Type} {m : AM α}
    {k : α → AM Bool} {s : AState} {b : Bool}
    (h : ∀ {a : α} {s₁ : AState}, m s = .ok (a, s₁) →
      CoreStep μ env fe s s₁ ∧ RunsC μ env fe (k a) s₁ b) :
    RunsC μ env fe (m >>= k) s b := by
  intro r s' hr
  obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨hs1, hk⟩ := h h1
  obtain ⟨hs2, rfl⟩ := hk _ _ h2
  exact ⟨hs1.trans hs2, rfl⟩

theorem RunsC.bindB {μ : CheckMode} {env : Env} {fe : IFEnv} {m : AM Bool}
    {k : Bool → AM Bool} {s : AState} {A b : Bool}
    (hm : RunsC μ env fe m s A)
    (hk : ∀ {s₁ : AState}, CoreStep μ env fe s s₁ → RunsC μ env fe (k A) s₁ b) :
    RunsC μ env fe (m >>= k) s b :=
  RunsC.bind fun h1 => by
    obtain ⟨hs, rfl⟩ := hm _ _ h1
    exact ⟨hs, hk hs⟩

theorem RunsC.guard {μ : CheckMode} {env : Env} {fe : IFEnv} {c D B : Bool}
    {Y : AM Bool} {s : AState} (hck : CheckOK μ env fe s) (hc : c = !D)
    (hY : D = true → RunsC μ env fe Y s B) :
    RunsC μ env fe (if c then pure false else Y) s (D && B) := by
  cases D with
  | false =>
    subst hc
    simp only [Bool.not_false, if_true, Bool.false_and]
    exact RunsC.ret hck
  | true =>
    subst hc
    simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
    exact hY rfl

theorem RunsC.guardT {μ : CheckMode} {env : Env} {fe : IFEnv} {c D B : Bool}
    {Y : AM Bool} {s : AState} (hck : CheckOK μ env fe s) (hc : c = D)
    (hY : D = true → RunsC μ env fe Y s B) :
    RunsC μ env fe (if c then Y else pure false) s (D && B) := by
  subst hc
  cases c with
  | false =>
    simp only [Bool.false_eq_true, if_false, Bool.false_and]
    exact RunsC.ret hck
  | true =>
    simp only [if_true, Bool.true_and]
    exact hY rfl

/-- con-leche: none — a store-preserving read is a `CoreStep`. -/
theorem CoreStep.of_store {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (hck : CheckOK μ env fe s) (h1 : s'.store = s.store) (h2 : s'.caches = s.caches)
    (h3 : s'.pins = s.pins) : CoreStep μ env fe s s' :=
  ⟨hck.mono ⟨by rw [h1]; exact hck.state.wf⟩ (by rw [h1]; exact Ext.refl _) h2 h3,
    by rw [h1]; exact Ext.refl _, h3⟩

/-- con-leche: none — an `IStepS` is a `CoreStep`. -/
theorem CoreStep.of_istep {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (hck : CheckOK μ env fe s) (h : Frontend.IStepS s s') : CoreStep μ env fe s s' :=
  ⟨hck.mono h.ok h.ext h.caches h.pins, h.ext, h.pins⟩

theorem lbbF_runsC {μ : CheckMode} {env : Env} {fe : IFEnv} {p : EIdx} {E : Expr}
    {s : AState} (hck : CheckOK μ env fe s) (hd : denoteE s.store p = some E) :
    RunsC μ env fe (looseBVarsBoundedFast coreWalkFuel 0 p) s (E.looseBVarsBounded 0) := by
  intro r s' h
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t.store = s.store ∧ t.caches = s.caches ∧
      t.pins = s.pins ∧ RelV (Expr.looseBVarsBounded 0) s.store p r)
    rfl h (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s
      p hck.state (by rw [hd]; rfl))
  exact ⟨CoreStep.of_store hck h1 h2 h3, h4 _ hd⟩

theorem hasFvarF_runsC {μ : CheckMode} {env : Env} {fe : IFEnv} {p : EIdx} {E : Expr}
    {s : AState} (hck : CheckOK μ env fe s) (hd : denoteE s.store p = some E) :
    RunsC μ env fe (hasFvarFast coreWalkFuel p) s E.hasFvar := by
  intro r s' h
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t.store = s.store ∧ t.caches = s.caches ∧
      t.pins = s.pins ∧ RelV Expr.hasFvar s.store p r)
    rfl h (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s p hck.state
      (by rw [hd]; rfl))
  exact ⟨CoreStep.of_store hck h1 h2 h3, h4 _ hd⟩

theorem alpd0_runsC {μ : CheckMode} {env : Env} {fe : IFEnv} {p : EIdx} {E : Expr}
    {s : AState} (hck : CheckOK μ env fe s) (hd : denoteE s.store p = some E) :
    RunsC μ env fe (allLevelParamsDefined [] p) s (E.allLevelParamsDefined []) := by
  intro r s' h
  obtain ⟨h1, h2, h3, h4⟩ := allLevelParamsDefined_run hck.state rfl hd h
  exact ⟨CoreStep.of_store hck h1 h2 h3, h4⟩

theorem crF_runsC {μ : CheckMode} {env : Env} {fe : IFEnv} {p : EIdx} {E : Expr}
    {s : AState} (hck : CheckOK μ env fe s) (hd : denoteE s.store p = some E) :
    RunsC μ env fe (constsResolveFFast fe p) s (E.constsResolve env) := by
  intro r s' h
  obtain ⟨h1, h2, h3, h4⟩ := constsResolveFFast_run hck hd h
  exact ⟨CoreStep.of_store hck h1 h2 h3, h4⟩

theorem constsResolveAll_runsC {μ : CheckMode} {env : Env} {fe : IFEnv} :
    ∀ (hs : List EIdx) (xs : List Expr) {s : AState}, CheckOK μ env fe s →
      Frontend.denoteEList s.store hs = some xs →
      RunsC μ env fe (constsResolveAll fe hs) s (xs.all fun h => h.constsResolve env) := by
  intro hs
  induction hs with
  | nil =>
    intro xs s hck hd
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    exact RunsC.ret hck
  | cons h t ih =>
    intro xs s hck hd
    obtain ⟨x, xt, hx, hxt, rfl⟩ := denoteEList_cons hd
    rw [List.all_cons]
    simp only [Arena.constsResolveAll]
    refine RunsC.bindB (crF_runsC hck hx) fun {s1} hs1 => ?_
    exact RunsC.guardT hs1.ok rfl fun _ =>
      ih xt hs1.ok (denoteEList_ext hs1.ext _ _ hxt)

/-- con-leche: none — `hyps.map (Expr.substConst0 c annVal)`, element by
element. -/
theorem substConst0List_run {cn : NIdx} {nm : ConLeche.Name} {rh : EIdx} {x : Expr} :
    ∀ (hs : List EIdx) (xs : List Expr) {out : List EIdx} {s s' : AState}, StateOK s →
      PinsOK s → denoteN s.store.ns cn = some nm → denoteE s.store rh = some x →
      Frontend.denoteEList s.store hs = some xs →
      Arena.substConst0List cn rh hs s = .ok (out, s') →
      Frontend.IStepS s s' ∧
        Frontend.denoteEList s'.store out = some (xs.map (Expr.substConst0 nm x)) := by
  intro hs
  induction hs with
  | nil =>
    intro xs out s s' hst _ _ _ hd hr
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.substConst0List] at hr
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr
    exact ⟨Frontend.IStepS.refl hst, rfl⟩
  | cons h t ih =>
    intro xs out s s' hst hp hn hx hd hr
    obtain ⟨y, yt, hy, hyt, rfl⟩ := denoteEList_cons hd
    simp only [Arena.substConst0List] at hr
    obtain ⟨h', s1, g1, r1⟩ := AM.bind_ok hr
    obtain ⟨hs1, hh'⟩ := substConst0_run coreWalkFuel hst hp hn hx hy g1
    obtain ⟨t', s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨hs2, ht'⟩ := ih yt hs1.ok (hp.mono hs1.ext hs1.pins) (denoteN_ext hn hs1.ext)
      (denote_ext hx hs1.ext) (denoteEList_ext hs1.ext _ _ hyt) g2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    refine ⟨hs1.trans hs2, ?_⟩
    simp only [Frontend.denoteEList, denote_ext hh' hs2.ext, ht', List.map_cons]

/-- con-leche: ConLeche/Kernel/Checker.lean:239-250 divModCertGuard — one
certificate's syntactic guards: the substituted proof is closed,
level-monomorphic and resolving, and the substituted statement resolves. -/
theorem divModCertGuard_run {μ : CheckMode} {env : Env} {fe : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {val : EIdx} {v : Expr} {hyps : List EIdx} {hx : List Expr}
    {eqE proof : EIdx} {ex px : Expr} {s : AState}
    (hck : CheckOK μ env fe s) (hn : denoteN s.store.ns cn = some nm)
    (hv : denoteE s.store val = some v) (hh : Frontend.denoteEList s.store hyps = some hx)
    (he : denoteE s.store eqE = some ex) (hpf : denoteE s.store proof = some px) :
    RunsC μ env fe (Arena.divModCertGuard fe cn val hyps eqE proof) s
      (ConLeche.divModCertGuard env nm v hx ex px) := by
  unfold Arena.divModCertGuard ConLeche.divModCertGuard
  simp only [Bool.and_assoc]
  refine RunsC.bind fun {p s1} g1 => ?_
  obtain ⟨hs1, hpd⟩ := substConstAll_run coreWalkFuel hck.state hck.pins hn hv hpf g1
  have c1 := CoreStep.of_istep hck hs1
  refine ⟨c1, ?_⟩
  refine RunsC.bindB (lbbF_runsC c1.ok hpd) fun {s2} c2 => ?_
  refine RunsC.guard c2.ok rfl fun _ => ?_
  have hp2 := denote_ext hpd c2.ext
  refine RunsC.bindB (hasFvarF_runsC c2.ok hp2) fun {s3} c3 => ?_
  refine RunsC.guard c3.ok (by simp) fun _ => ?_
  have hp3 := denote_ext hp2 c3.ext
  refine RunsC.bindB (alpd0_runsC c3.ok hp3) fun {s4} c4 => ?_
  refine RunsC.guard c4.ok rfl fun _ => ?_
  have hp4 := denote_ext hp3 c4.ext
  refine RunsC.bindB (crF_runsC c4.ok hp4) fun {s5} c5 => ?_
  refine RunsC.guard c5.ok rfl fun _ => ?_
  have c15 := (((c1.trans c2).trans c3).trans c4).trans c5
  refine RunsC.bind fun {hs' s6} g6 => ?_
  obtain ⟨hs6, hhs⟩ := substConst0List_run hyps hx c5.ok.state c5.ok.pins
    (denoteN_ext hn c15.ext) (denote_ext hv c15.ext) (denoteEList_ext c15.ext _ _ hh) g6
  have c6 := CoreStep.of_istep c5.ok hs6
  refine ⟨c6, ?_⟩
  refine RunsC.bindB (constsResolveAll_runsC _ _ c6.ok hhs) fun {s7} c7 => ?_
  refine RunsC.guard c7.ok rfl fun _ => ?_
  have c17 := (c15.trans c6).trans c7
  refine RunsC.bind fun {e' s8} g8 => ?_
  obtain ⟨hs8, he'⟩ := substConst0_run coreWalkFuel c7.ok.state c7.ok.pins
    (denoteN_ext hn c17.ext) (denote_ext hv c17.ext) (denote_ext he c17.ext) g8
  have c8 := CoreStep.of_istep c7.ok hs8
  exact ⟨c8, crF_runsC c8.ok he'⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:303-306 divModCertsGuard — the
zipped walk over the statements and the proofs. -/
theorem divModCertsGuardGo_run {μ : CheckMode} {env : Env} {fe : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {val : EIdx} {v : Expr} :
    ∀ (stmts : List (List EIdx × EIdx)) (xs : List (List Expr × Expr))
      (proofs : List EIdx) (ps : List Expr) {s : AState}, CheckOK μ env fe s →
      denoteN s.store.ns cn = some nm → denoteE s.store val = some v →
      StmtsDenote s.store stmts xs → Frontend.denoteEList s.store proofs = some ps →
      RunsC μ env fe (Arena.divModCertsGuardGo fe cn val stmts proofs) s
        ((xs.zip ps).all fun p => ConLeche.divModCertGuard env nm v p.1.1 p.1.2 p.2) := by
  intro stmts
  induction stmts with
  | nil =>
    intro xs proofs ps s hck _ _ hsd _
    cases xs with
    | cons _ _ => exact hsd.elim
    | nil => simp only [Arena.divModCertsGuardGo, List.zip_nil_left]; exact RunsC.ret hck
  | cons st srest ih =>
    intro xs proofs ps s hck hn hv hsd hpr
    cases xs with
    | nil => exact hsd.elim
    | cons x xrest =>
      obtain ⟨hyps, eqE⟩ := st
      obtain ⟨hx, ex⟩ := x
      obtain ⟨h1, h2, h3⟩ := hsd
      cases proofs with
      | nil =>
        simp only [Frontend.denoteEList, Option.some.injEq] at hpr
        subst hpr
        simp only [Arena.divModCertsGuardGo, List.zip_nil_right]
        exact RunsC.ret hck
      | cons pf prest =>
        obtain ⟨px, pxs, hpx, hpxs, rfl⟩ := denoteEList_cons hpr
        simp only [Arena.divModCertsGuardGo, List.zip_cons_cons, List.all_cons]
        refine RunsC.bindB (divModCertGuard_run hck hn hv h1 h2 hpx) fun {s1} c1 => ?_
        exact RunsC.guardT c1.ok rfl fun _ =>
          ih xrest prest pxs c1.ok (denoteN_ext hn c1.ext) (denote_ext hv c1.ext)
            (StmtsDenote.mono c1.ext _ _ h3) (denoteEList_ext c1.ext _ _ hpxs)

/-! ## One variant's attempt -/

/-- con-leche: ConLeche/Kernel/Checker.lean:155-222 divModCertStmts — every
hypothesis and every equation of the pinned statements is scoped at depth 2
(`fvar 0`, `fvar 1` at `Nat`). -/
theorem divModCertStmts_wscoped (nm : ConLeche.Name) :
    ∀ q ∈ ConLeche.divModCertStmts nm,
      (∀ h ∈ q.1, Expr.WScoped 2 h) ∧ Expr.WScoped 2 q.2 := by
  intro q hq
  unfold ConLeche.divModCertStmts at hq
  simp only at hq
  repeat' split at hq
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    repeat' rcases hq with rfl | hq
  all_goals first
    | (simp [Expr.WScoped])
    | (constructor <;> (try intro h hh) <;> simp_all [Expr.WScoped] <;> split <;> simp [Expr.WScoped])
    | exact absurd hq (by simp)

/-- con-leche: ConLeche/Kernel/Checker.lean:224-237 divModCertApplied — the
applied certificate is scoped at depth 4 when the proof is closed and the
hypotheses are scoped at depth 2. -/
theorem divModCertApplied_wscoped {P : Expr} {Hs : List Expr}
    (hP : P.hasFvar = false) (hH : ∀ h ∈ Hs, Expr.WScoped 2 h) :
    Expr.WScoped 4 (ConLeche.divModCertApplied P Hs) := by
  have hP4 : Expr.WScoped 4 P := ConLeche.Expr.WScoped.of_not_hasFvar hP
  have hb : Expr.WScoped 4 (.app (.app P (.fvar 0 (.const ConLeche.natName [])))
      (.fvar 1 (.const ConLeche.natName []))) := by
    simp [Expr.WScoped, hP4]
  unfold ConLeche.divModCertApplied
  split
  · rename_i h1
    have := hH h1 (by simp)
    simp only [Expr.WScoped] at hb ⊢
    exact ⟨hb, by omega, this⟩
  · rename_i h1 h2
    have g1 := hH h1 (by simp)
    have g2 := hH h2 (by simp)
    simp only [Expr.WScoped] at hb ⊢
    exact ⟨⟨hb, by omega, g1⟩, by omega, ConLeche.Expr.WScoped.mono (by omega) g2⟩
  · exact hb

/-- con-leche: ConLeche/Kernel/Checker.lean:224-237 divModCertApplied — the
vendored proof applied to the statement's free variables, interned. -/
theorem divModCertApplied_run {p : EIdx} {hs : List EIdx} {P : Expr} {Hs : List Expr}
    {h : EIdx} {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hP : denoteE s.store p = some P) (hH : Frontend.denoteEList s.store hs = some Hs)
    (hr : Arena.divModCertApplied p hs s = .ok (h, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store h = some (ConLeche.divModCertApplied P Hs) := by
  simp only [Arena.divModCertApplied] at hr
  obtain ⟨x, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨hs1, ex⟩ := natVar_run hst hp g1
  obtain ⟨y, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hs2, ey⟩ := natVar_run hs1.ok (hp.mono hs1.ext hs1.pins) g2
  have A2 := hs1.trans hs2
  have hP2 := denote_ext hP A2.ext
  have ex2 := denote_ext ex hs2.ext
  obtain ⟨b1, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hs3, eb1⟩ := Frontend.internE_sstep A2.ok
    (viewOK_app (by rw [hP2]; rfl) (by rw [ex2]; rfl)) g3
  have eb1' : denoteE s3.store b1 = some (.app P (.fvar 0 (.const ConLeche.natName []))) := by
    rw [eb1]; simp only [denoteEView, denote_ext hP2 hs3.ext, denote_ext ex2 hs3.ext, opt2]
  have A3 := A2.trans hs3
  have ey3 := denote_ext ey hs3.ext
  obtain ⟨base, s4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨hs4, eb⟩ := Frontend.internE_sstep A3.ok
    (viewOK_app (by rw [eb1']; rfl) (by rw [ey3]; rfl)) g4
  have eb' : denoteE s4.store base = some (.app (.app P (.fvar 0 (.const ConLeche.natName [])))
      (.fvar 1 (.const ConLeche.natName []))) := by
    rw [eb]; simp only [denoteEView, denote_ext eb1' hs4.ext, denote_ext ey3 hs4.ext, opt2]
  have A4 := A3.trans hs4
  have hH4 := denoteEList_ext A4.ext _ _ hH
  match hs, Hs, hH4, r4 with
  | [], Hs, hH4, r4 =>
    simp only [Frontend.denoteEList, Option.some.injEq] at hH4
    subst hH4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
    exact ⟨A4, eb'⟩
  | [h1], Hs, hH4, r4 =>
    obtain ⟨H1, Ht, hh1, hht, rfl⟩ := denoteEList_cons hH4
    simp only [Frontend.denoteEList, Option.some.injEq] at hht
    subst hht
    obtain ⟨f2, s5, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨hs5, ef2⟩ := internFvar_run A4.ok hh1 g5
    obtain ⟨hs6, e6⟩ := Frontend.internE_sstep hs5.ok
      (viewOK_app (by rw [denote_ext eb' hs5.ext]; rfl) (by rw [ef2]; rfl)) r5
    refine ⟨(A4.trans hs5).trans hs6, ?_⟩
    rw [e6]
    simp only [denoteEView, denote_ext (denote_ext eb' hs5.ext) hs6.ext,
      denote_ext ef2 hs6.ext, opt2, ConLeche.divModCertApplied]
  | [h1, h2], Hs, hH4, r4 =>
    obtain ⟨H1, Ht, hh1, hht, rfl⟩ := denoteEList_cons hH4
    obtain ⟨H2, Ht', hh2, hht', rfl⟩ := denoteEList_cons hht
    simp only [Frontend.denoteEList, Option.some.injEq] at hht'
    subst hht'
    obtain ⟨f2, s5, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨hs5, ef2⟩ := internFvar_run A4.ok hh1 g5
    obtain ⟨a1, s6, g6, r6⟩ := AM.bind_ok r5
    obtain ⟨hs6, e6⟩ := Frontend.internE_sstep hs5.ok
      (viewOK_app (by rw [denote_ext eb' hs5.ext]; rfl) (by rw [ef2]; rfl)) g6
    have e6' : denoteE s6.store a1 = some (.app (.app (.app P (.fvar 0
        (.const ConLeche.natName []))) (.fvar 1 (.const ConLeche.natName []))) (.fvar 2 H1)) := by
      rw [e6]
      simp only [denoteEView, denote_ext (denote_ext eb' hs5.ext) hs6.ext,
        denote_ext ef2 hs6.ext, opt2]
    obtain ⟨f3, s7, g7, r7⟩ := AM.bind_ok r6
    obtain ⟨hs7, ef3⟩ := internFvar_run hs6.ok (denote_ext hh2 (hs5.trans hs6).ext) g7
    obtain ⟨hs8, e8⟩ := Frontend.internE_sstep hs7.ok
      (viewOK_app (by rw [denote_ext e6' hs7.ext]; rfl) (by rw [ef3]; rfl)) r7
    refine ⟨(((A4.trans hs5).trans hs6).trans hs7).trans hs8, ?_⟩
    rw [e8]
    simp only [denoteEView, denote_ext (denote_ext e6' hs7.ext) hs8.ext,
      denote_ext ef3 hs8.ext, opt2, ConLeche.divModCertApplied]
  | h1 :: h2 :: h3 :: t, Hs, hH4, r4 =>
    obtain ⟨H1, Ht, hh1, hht, rfl⟩ := denoteEList_cons hH4
    obtain ⟨H2, Ht', hh2, hht', rfl⟩ := denoteEList_cons hht
    obtain ⟨H3, Ht'', hh3, hht'', rfl⟩ := denoteEList_cons hht'
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
    exact ⟨A4, eb'⟩

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:899 checkDivModCerts_datF. -/
theorem checkDivModCerts_mono {μ : CheckMode} {env : Env} {nm : ConLeche.Name} {v : Expr}
    {xs : List (List Expr × Expr)} {ps : List Expr} {r : Bool} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkDivModCerts (ConLeche.fueledOps μ F) env nm v xs ps = .ok r) :
    ConLeche.checkDivModCerts (ConLeche.fueledOps μ F') env nm v xs ps = .ok r := by
  rw [← ConLeche.checkDivModCerts_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkDivModCerts (ConLeche.fueledOpsM μ) env nm v xs ps).property hle h

/-- con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts — one
certificate's clause, at one fuel. -/
theorem checkDivModCerts_cons_pure {μ : CheckMode} {F : Nat} {env : Env}
    {nm : ConLeche.Name} {v : Expr} {hyps : List Expr} {eqE proof w tp : Expr}
    {srest : List (List Expr × Expr)} {prest : List Expr}
    (hg : ConLeche.divModCertGuard env nm v hyps eqE proof = true)
    (h1 : ConLeche.annotateCore μ env F 4 (ConLeche.divModCertApplied
      (Expr.substConstAll nm v proof) (hyps.map (Expr.substConst0 nm v))) = .ok w)
    (h2 : ConLeche.inferTypeCore μ env F 4 w = .ok tp)
    (h3 : ConLeche.isDefEqCore μ env F 4 tp (Expr.substConst0 nm v eqE) = .ok true)
    (h4 : ConLeche.checkDivModCerts (ConLeche.fueledOps μ F) env nm v srest prest
      = .ok true) :
    ConLeche.checkDivModCerts (ConLeche.fueledOps μ F) env nm v ((hyps, eqE) :: srest)
      (proof :: prest) = .ok true := by
  simp only [ConLeche.checkDivModCerts, hg, if_true, ConLeche.fueledOps, h1, h2, h3,
    bind, Except.bind]
  exact h4

/-- con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts — **the
certificate loop**: per certificate, the guards (`divModCertGuard_run`), the
substituted proof applied to the open statement's variables and annotated,
its type inferred and compared with the substituted equation, all at depth 4
through `KnotSpec`; a `true` answer is con-leche's at one fuel. -/
theorem checkDivModCerts_bridge_aux {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) {cn : NIdx}
    {nm : ConLeche.Name} {val : EIdx} {v : Expr} (hwsv : Expr.WScoped 0 v) :
    ∀ (stmts : List (List EIdx × EIdx)) (xs : List (List Expr × Expr))
      (proofs : List EIdx) (ps : List Expr) (r : Bool) (s s' : AState),
      CheckOK μ env fe s → denoteN s.store.ns cn = some nm →
      denoteE s.store val = some v → StmtsDenote s.store stmts xs →
      Frontend.denoteEList s.store proofs = some ps →
      (∀ q ∈ xs, (∀ h ∈ q.1, Expr.WScoped 2 h) ∧ Expr.WScoped 2 q.2) →
      Arena.checkDivModCerts μ fe cn val stmts proofs s = .ok (r, s') →
      CoreStep μ env fe s s' ∧
        (r = true → ∃ F, ConLeche.checkDivModCerts (ConLeche.fueledOps μ F) env nm v xs ps
          = .ok true) := by
  have hknot := hk.knot env fe henv
  have hws4 : Expr.WScoped 4 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  have hws2 : Expr.WScoped 2 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  intro stmts
  induction stmts with
  | nil =>
    intro xs proofs ps r s s' hck _ _ hsd hpr _ hrun
    cases xs with
    | cons _ _ => exact hsd.elim
    | nil =>
      cases proofs with
      | nil =>
        simp only [Frontend.denoteEList, Option.some.injEq] at hpr
        subst hpr
        simp only [Arena.checkDivModCerts] at hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨CoreStep.refl hck, fun _ => ⟨0, rfl⟩⟩
      | cons _ _ =>
        simp only [Arena.checkDivModCerts] at hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact ⟨CoreStep.refl hck, fun h => absurd h (by simp)⟩
  | cons st srest ih =>
    intro xs proofs ps r s s' hck hn hv hsd hpr hwq hrun
    cases xs with
    | nil => exact hsd.elim
    | cons x xrest =>
    obtain ⟨hyps, eqE⟩ := st
    obtain ⟨hx, ex⟩ := x
    obtain ⟨h1, h2, h3⟩ := hsd
    cases proofs with
    | nil =>
      simp only [Arena.checkDivModCerts] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hck, fun h => absurd h (by simp)⟩
    | cons pf prest =>
    obtain ⟨px, pxs, hpx, hpxs, rfl⟩ := denoteEList_cons hpr
    obtain ⟨hwh, hwe⟩ := hwq (hx, ex) (by simp)
    simp only [Arena.checkDivModCerts] at hrun
    obtain ⟨g, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨c1, rfl⟩ := divModCertGuard_run hck hn hv h1 h2 hpx _ _ g1
    rcases AM.ite_ok r1 with ⟨hg, r2⟩ | ⟨-, r2⟩
    rotate_left
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
      exact ⟨c1, fun h => absurd h (by simp)⟩
    have hg' := hg
    simp only [ConLeche.divModCertGuard, Bool.and_eq_true, Bool.not_eq_true'] at hg'
    have hPf : (Expr.substConstAll nm v px).hasFvar = false := hg'.1.1.1.1.2
    -- the substituted proof and hypotheses
    obtain ⟨p, s2, g2, r3⟩ := AM.bind_ok r2
    obtain ⟨hs2, hpd⟩ := substConstAll_run coreWalkFuel c1.ok.state c1.ok.pins
      (denoteN_ext hn c1.ext) (denote_ext hv c1.ext) (denote_ext hpx c1.ext) g2
    have c2 := CoreStep.of_istep c1.ok hs2
    have c02 := c1.trans c2
    obtain ⟨hs', s3, g3, r4⟩ := AM.bind_ok r3
    obtain ⟨hs3, hhs⟩ := substConst0List_run hyps hx c2.ok.state c2.ok.pins
      (denoteN_ext hn c02.ext) (denote_ext hv c02.ext) (denoteEList_ext c02.ext _ _ h1) g3
    have c3 := CoreStep.of_istep c2.ok hs3
    have c03 := c02.trans c3
    obtain ⟨ap0, s4, g4, r5⟩ := AM.bind_ok r4
    obtain ⟨hs4, hap0⟩ := divModCertApplied_run c3.ok.state c3.ok.pins
      (denote_ext hpd (hs3.ext)) hhs g4
    have c4 := CoreStep.of_istep c3.ok hs4
    have c04 := c03.trans c4
    have hwsA : Expr.WScoped 4 (ConLeche.divModCertApplied (Expr.substConstAll nm v px)
        (hx.map (Expr.substConst0 nm v))) := by
      refine divModCertApplied_wscoped hPf fun h hh => ?_
      obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
      exact substConst0_wscoped hws2 _ (hwh h0 hh0)
    -- annotate, infer
    obtain ⟨ap, s5, g5, r6⟩ := AM.bind_ok r5
    obtain ⟨hck5, hx5, hp5, hsim5⟩ := AM.of_run (P := fun t => t = s4)
      (Q := fun r t => CheckOK μ env fe t ∧ Ext s4.store t.store ∧ t.pins = s4.pins ∧
        Core.SimE (ConLeche.annotateCore μ env) 4 _ t.store r)
      rfl g5 (hknot.annotate s4 4 ap0 _ c4.ok hap0 hwsA)
    obtain ⟨w, hw5, hwsw, F5, hF5⟩ := hsim5
    have c5 : CoreStep μ env fe s4 s5 := ⟨hck5, hx5, hp5⟩
    obtain ⟨tp, s6, g6, r7⟩ := AM.bind_ok r6
    obtain ⟨hck6, hx6, hp6, hsim6⟩ := AM.of_run (P := fun t => t = s5)
      (Q := fun r t => CheckOK μ env fe t ∧ Ext s5.store t.store ∧ t.pins = s5.pins ∧
        Core.SimE (ConLeche.inferTypeCore μ env) 4 w t.store r)
      rfl g6 (hknot.infer s5 4 ap w hck5 hw5 hwsw)
    obtain ⟨tpx, htp6, hwstp, F6, hF6⟩ := hsim6
    have c6 : CoreStep μ env fe s5 s6 := ⟨hck6, hx6, hp6⟩
    have c06 := (c04.trans c5).trans c6
    -- the substituted equation, and the comparison
    obtain ⟨rhs, s7, g7, r8⟩ := AM.bind_ok r7
    obtain ⟨hs7, hrhs⟩ := substConst0_run coreWalkFuel hck6.state hck6.pins
      (denoteN_ext hn c06.ext) (denote_ext hv c06.ext) (denote_ext h2 c06.ext) g7
    have c7 := CoreStep.of_istep hck6 hs7
    have hwsR : Expr.WScoped 4 (Expr.substConst0 nm v ex) :=
      substConst0_wscoped hws4 _ (ConLeche.Expr.WScoped.mono (by omega) hwe)
    obtain ⟨b, s8, g8, r9⟩ := AM.bind_ok r8
    obtain ⟨hck8, hx8, hp8, hsim8⟩ := AM.of_run (P := fun t => t = s7)
      (Q := fun r t => CheckOK μ env fe t ∧ Ext s7.store t.store ∧ t.pins = s7.pins ∧
        Core.SimV (ConLeche.isDefEqCore μ env) 4 tpx (Expr.substConst0 nm v ex) r)
      rfl g8 (hknot.defeq s7 4 tp rhs tpx _ c7.ok (denote_ext htp6 hs7.ext) hrhs hwstp hwsR)
    obtain ⟨F8, hF8⟩ := hsim8
    have c8 : CoreStep μ env fe s7 s8 := ⟨hck8, hx8, hp8⟩
    have c08 := (c06.trans c7).trans c8
    rcases AM.ite_ok r9 with ⟨hb, r10⟩ | ⟨-, r10⟩
    rotate_left
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok r10
      exact ⟨c08, fun h => absurd h (by simp)⟩
    have hb' : b = true := hb
    subst hb'
    obtain ⟨c9, himp⟩ := ih xrest prest pxs r s8 s' c8.ok (denoteN_ext hn c08.ext)
      (denote_ext hv c08.ext) (StmtsDenote.mono c08.ext _ _ h3)
      (denoteEList_ext c08.ext _ _ hpxs) (fun q hq => hwq q (List.mem_cons_of_mem _ hq)) r10
    refine ⟨c08.trans c9, fun hr => ?_⟩
    obtain ⟨F9, hF9⟩ := himp hr
    have l5 : F5 ≤ max (max (max F5 F6) F8) F9 := by omega
    have l6 : F6 ≤ max (max (max F5 F6) F8) F9 := by omega
    have l8 : F8 ≤ max (max (max F5 F6) F8) F9 := by omega
    have l9 : F9 ≤ max (max (max F5 F6) F8) F9 := by omega
    exact ⟨_, checkDivModCerts_cons_pure hg (ConLeche.annotateCore_mono l5 hF5)
      (ConLeche.inferTypeCore_mono l6 hF6) (ConLeche.isDefEqCore_mono l8 hF8)
      (checkDivModCerts_mono l9 hF9)⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:321-328 checkDivModPinAt — the
attempt's clause at one fuel. -/
theorem checkDivModPinAt_pure {μ : CheckMode} {F : Nat} {env : Env}
    {nm : ConLeche.Name} {v pw : Expr} {psP : NatOpPinSet}
    (h1 : ConLeche.annotateCore μ env F 0 (ConLeche.divModDeclPin psP nm) = .ok pw)
    (h2 : ConLeche.isDefEqCore μ env F 0 v pw = .ok true)
    (h3 : ConLeche.checkDivModCerts (ConLeche.fueledOps μ F) env nm v
      (ConLeche.divModCertStmts nm) (ConLeche.divModCertProofs psP nm) = .ok true) :
    ConLeche.checkDivModPinAt (ConLeche.fueledOps μ F) env nm v psP = .ok true := by
  simp only [ConLeche.checkDivModPinAt, ConLeche.fueledOps, h1, h2, if_true, bind,
    Except.bind]
  exact h3

/-- con-leche: ConLeche/Kernel/Checker.lean:292-297 divModPinGuard — one
variant's pin guards.

**PROVED** (task #97-P3-Checker round 10): `divModDeclPin_run` (the
handle-comparison chain against the pins), then `pinGuardWalk_run`, the four
walks `reducePinGuard_run` shares. -/
theorem divModPinGuard_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {r : Bool} {s s' : AState}
    (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm)
    (hr : Arena.divModPinGuard ps fe cn s = .ok (r, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      r = ConLeche.divModPinGuard psP env nm := by
  simp only [Arena.divModPinGuard] at hr
  obtain ⟨p, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨rfl, hpd⟩ := divModDeclPin_run hck.state hck.pins hps hn g1
  simp only [ConLeche.divModPinGuard, Bool.and_assoc]
  exact pinGuardWalk_run hck (Ext.refl _) rfl hpd r1

/-- con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard — one
variant's certificate guards, over the pinned statements.

**PROVED** (task #97-P3-Checker round 10): `divModCertStmts_run` (the pinned
statements, interned), `divModCertProofs_run`, then `divModCertsGuardGo_run`
over the zip — each step `divModCertGuard_run`: `substConstAll_run`, the four
Fast walks, `substConst0List_run` + `constsResolveAll_runsC`, and
`substConst0_run` + `constsResolveFFast_run`. -/
theorem divModCertsGuard_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {val : EIdx} {v : Expr} {r : Bool} {s s' : AState}
    (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm) (hv : denoteE s.store val = some v)
    (hr : Arena.divModCertsGuard ps fe cn val s = .ok (r, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      r = ConLeche.divModCertsGuard psP env nm v := by
  simp only [Arena.divModCertsGuard] at hr
  obtain ⟨stmts, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨hs1, hsd⟩ := divModCertStmts_run hck.state hck.pins hn g1
  have c1 := CoreStep.of_istep hck hs1
  obtain ⟨prs, s2, g2, r2⟩ := AM.bind_ok r1
  have hps1 := (PinsDenote.mono c1.ext [ps] [psP] ⟨hps, trivial⟩).1
  obtain ⟨rfl, hpr⟩ := divModCertProofs_run c1.ok.state c1.ok.pins hps1
    (denoteN_ext hn c1.ext) g2
  obtain ⟨c2, rfl⟩ := divModCertsGuardGo_run _ _ _ _ c1.ok (denoteN_ext hn c1.ext)
    (denote_ext hv c1.ext) hsd hpr _ _ r2
  exact ⟨c2.ok, c1.ext.trans c2.ext, by rw [c2.pins, c1.pins], rfl⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt — one
variant's attempt: on success the invariant stands, and a `true` answer is
con-leche's.

**PROVED** (task #97-P3-Checker round 10): `divModDeclPin_run`, one
`KnotSpec.annotate` and one `KnotSpec.defeq` at depth 0 for the pin, then
`divModCertStmts_run`, `divModCertProofs_run` and the certificate loop
(`checkDivModCerts_bridge_aux`: `KnotSpec.annotate`/`infer`/`defeq` at depth 4
over `divModCertApplied`, scoped by `divModCertApplied_wscoped` and
`divModCertStmts_wscoped`).

**The statement gained `hpg : divModPinGuard psP env nm = true`** (a
precondition repair): the pin is annotated through `KnotSpec.annotate`, which
needs it `WScoped 0`, and nothing else in the hypotheses says the pin is
closed.  The one call site, the variant loop, runs the attempt only after
the pin guard answered `true`. -/
theorem checkDivModPinAt_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {val : EIdx} {v : Expr} {b : Bool} {s s' : AState}
    (_hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm) (hv : denoteE s.store val = some v)
    (hwsv : Expr.WScoped 0 v) (hpg : ConLeche.divModPinGuard psP env nm = true)
    (hr : Arena.checkDivModPinAt μ fe cn val ps s = .ok (b, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      (b = true → ∃ F, ConLeche.checkDivModPinAt (ConLeche.fueledOps μ F) env nm v psP
        = .ok true) := by
  have hknot := hk.knot env fe henv
  have hwsP : Expr.WScoped 0 (ConLeche.divModDeclPin psP nm) := by
    simp only [ConLeche.divModPinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hpg
    exact ConLeche.Expr.WScoped.of_not_hasFvar hpg.1.1.2
  simp only [Arena.checkDivModPinAt] at hr
  obtain ⟨p, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨hs1, hpd⟩ := divModDeclPin_run hck.state hck.pins hps hn g1
  subst s1
  obtain ⟨pa, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hck2, hx2, hp2, hsim2⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s.store t.store ∧ t.pins = s.pins ∧
      Core.SimE (ConLeche.annotateCore μ env) 0 (ConLeche.divModDeclPin psP nm) t.store r)
    rfl g2 (hknot.annotate s 0 p _ hck hpd hwsP)
  obtain ⟨pw, hpw, hwspw, F2, hF2⟩ := hsim2
  obtain ⟨ok, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hck3, hx3, hp3, hsim3⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s2.store t.store ∧ t.pins = s2.pins ∧
      Core.SimV (ConLeche.isDefEqCore μ env) 0 v pw r)
    rfl g3 (hknot.defeq s2 0 val pa v pw hck2 (denote_ext hv hx2) hpw hwsv hwspw)
  obtain ⟨F3, hF3⟩ := hsim3
  have hx03 : Ext s.store s3.store := hx2.trans hx3
  rcases AM.ite_ok r3 with ⟨hok, r4⟩ | ⟨-, r4⟩
  rotate_left
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
    exact ⟨hck3, hx03, by rw [hp3, hp2], fun h => absurd h (by simp)⟩
  have hok' : ok = true := hok
  subst hok'
  obtain ⟨st, s4, g4, r5⟩ := AM.bind_ok r4
  obtain ⟨hs4, hsd⟩ := divModCertStmts_run hck3.state hck3.pins (denoteN_ext hn hx03) g4
  have c4 := CoreStep.of_istep hck3 hs4
  obtain ⟨prs, s5, g5, r6⟩ := AM.bind_ok r5
  have hx04 : Ext s.store s4.store := hx03.trans hs4.ext
  obtain ⟨rfl, hpr⟩ := divModCertProofs_run c4.ok.state c4.ok.pins
    (PinsDenote.mono hx04 [ps] [psP] ⟨hps, trivial⟩).1 (denoteN_ext hn hx04) g5
  obtain ⟨c6, himp⟩ := checkDivModCerts_bridge_aux hk henv hwsv _ _ _ _ _ _ _ c4.ok
    (denoteN_ext hn hx04) (denote_ext hv hx04) hsd hpr (divModCertStmts_wscoped nm) r6
  refine ⟨c6.ok, hx04.trans c6.ext, by rw [c6.pins, hs4.pins, hp3, hp2], fun hb => ?_⟩
  obtain ⟨F6, hF6⟩ := himp hb
  have l2 : F2 ≤ max (max F2 F3) F6 := by omega
  have l3 : F3 ≤ max (max F2 F3) F6 := by omega
  have l6 : F6 ≤ max (max F2 F3) F6 := by omega
  exact ⟨_, checkDivModPinAt_pure (ConLeche.annotateCore_mono l2 hF2)
    (ConLeche.isDefEqCore_mono l3 hF3) (checkDivModCerts_mono l6 hF6)⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:338-360 checkDivModPinLoop — **the
variant loop**: an accepting arena loop is an accepting pure loop, at some
fuel, whatever the two sides' decline messages.  PROVED over the four pieces
above (the module section's note says why only their `true` direction is
spent). -/
theorem checkDivModPinLoop_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cn : NIdx} {nm : ConLeche.Name} {val : EIdx} {v : Expr}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (hwsv : Expr.WScoped 0 v) :
    ∀ (ps : List INatOpPinSet) (psP : List NatOpPinSet) (tried : List String)
      (triedP : List String) (s s' : AState),
      CheckOK μ env fe s → PinsDenote s.store ps psP →
      denoteN s.store.ns cn = some nm → denoteE s.store val = some v →
      Arena.checkDivModPinLoop μ fe cn val ps tried s = .ok ((), s') →
      CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
        ∃ F, ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v psP triedP
          = .ok () := by
  intro ps
  induction ps with
  | nil =>
    intro psP tried triedP s s' _ _ _ _ hrun
    simp only [Arena.checkDivModPinLoop] at hrun
    exact absurd hrun (AM.Never.fail _ s () s')
  | cons p rest ih =>
    intro psP tried triedP s s' hck hps hn hv hrun
    cases psP with
    | nil => exact hps.elim
    | cons q restP =>
    obtain ⟨hq, hrestP⟩ := hps
    simp only [Arena.checkDivModPinLoop] at hrun
    obtain ⟨a, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨hck1, hx1, hp1, rfl⟩ := divModPinGuard_run hck hq hn g1
    have hq1 := (PinsDenote.mono hx1 [p] [q] ⟨hq, trivial⟩).1
    obtain ⟨b, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨hck2, hx2, hp2, rfl⟩ :=
      divModCertsGuard_run hck1 hq1 (denoteN_ext hn hx1) (denote_ext hv hx1) g2
    have hx02 : Ext s.store s2.store := hx1.trans hx2
    have hn2 := denoteN_ext hn hx02
    have hv2 := denote_ext hv hx02
    have hrest2 := PinsDenote.mono hx02 _ _ hrestP
    -- the pure side's step, whichever branch its attempt takes
    have pureStep : ∀ F, (ConLeche.divModPinGuard q env nm &&
        ConLeche.divModCertsGuard q env nm v) = true →
        (ConLeche.checkDivModPinAt (ConLeche.fueledOps μ F) env nm v q = .ok true ∨
          ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v restP
            (triedP ++ [ConLeche.divModAttemptReason q none]) = .ok ()) →
        ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v (q :: restP) triedP
          = .ok () := by
      intro F hg hor
      simp only [ConLeche.checkDivModPinLoop, hg, if_true, fueledOps_orElse]
      split
      · rfl
      · rcases hor with h | h
        · rename_i hne; exact absurd h hne
        · exact h
    -- the rest of the loop, at the state the step left
    have recurse : ∀ (t : AState) (tr : List String), CheckOK μ env fe t →
        Ext s.store t.store → t.pins = s.pins →
        Arena.checkDivModPinLoop μ fe cn val rest tr t = .ok ((), s') →
        CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
          ∃ F, ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v (q :: restP)
            triedP = .ok () := by
      intro t tr hckt hxt hpt hrt
      by_cases hg : (ConLeche.divModPinGuard q env nm &&
          ConLeche.divModCertsGuard q env nm v) = true
      · obtain ⟨hck', hx', hp', F, hF⟩ :=
          ih restP tr (triedP ++ [ConLeche.divModAttemptReason q none]) t s' hckt
            (PinsDenote.mono hxt _ _ hrestP) (denoteN_ext hn hxt) (denote_ext hv hxt) hrt
        exact ⟨hck', hxt.trans hx', by rw [hp', hpt], F, pureStep F hg (Or.inr hF)⟩
      · obtain ⟨hck', hx', hp', F, hF⟩ :=
          ih restP tr (triedP ++ [s!"{q.toolchain}: pin or certificate ground constants \
          absent"]) t s' hckt
            (PinsDenote.mono hxt _ _ hrestP) (denoteN_ext hn hxt) (denote_ext hv hxt) hrt
        refine ⟨hck', hxt.trans hx', by rw [hp', hpt], F, ?_⟩
        rw [Bool.not_eq_true] at hg
        simp only [ConLeche.checkDivModPinLoop, hg, Bool.false_eq_true, if_false]
        exact hF
    have hp02 : s2.pins = s.pins := by rw [hp2, hp1]
    split at r2
    · rename_i hg
      obtain ⟨o, s3, g3, r3⟩ := AM.bind_ok r2
      rcases orElseAttempt_run g3 with ⟨b', ha, ho⟩ | ⟨e, ha, ho, rfl⟩
      · obtain ⟨hck3, hx3, hp3, himp⟩ :=
          checkDivModPinAt_bridge hμ hk henv hck2 (PinsDenote.mono hx2 [p] [q] ⟨hq1, trivial⟩).1
            hn2 hv2 hwsv (Bool.and_eq_true _ _ |>.mp hg).1 ha
        cases b' with
        | true =>
          simp only [orElseStepOf] at ho
          subst ho
          obtain ⟨-, rfl⟩ := AM.pure_ok r3
          obtain ⟨F, hF⟩ := himp rfl
          exact ⟨hck3, hx02.trans hx3, by rw [hp3, hp02], F, pureStep F hg (Or.inl hF)⟩
        | false =>
          simp only [orElseStepOf] at ho
          subst ho
          exact recurse s3 _ hck3 (hx02.trans hx3) (by rw [hp3, hp02]) r3
      · cases e <;> (simp only [orElseStepOf] at ho; subst ho)
        all_goals first
          | exact absurd r3 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
          | exact recurse _ _ hck2 hx02 hp02 r3
    · exact recurse s2 _ hck2 hx02 hp02 r2

/-- con-leche: ConLeche/Kernel/Checker.lean:380-388 checkDivModPin — **the
`Nat.div`/`Nat.mod` variant gate**: the stored value must be definitionally
equal to some committed pin variant and that variant's certificates must
check.  No variant matching is a decline.

**PROVED** (task #97-P3-Checker rounds 9–10): the environment guard
(`divModEnvGuard_run`), the lookup of the stored value through the extended
index's `IFEnvOK` (its `WScoped 0` from `EnvWF env2`), and the variant loop
(`checkDivModPinLoop_bridge`) over its three pieces, `divModPinGuard_run`,
`divModCertsGuard_run` and `checkDivModPinAt_bridge`. -/
theorem checkDivModPin_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env env2 : Env}
    {fe fe2 : IFEnv} {cn : NIdx} {nm : ConLeche.Name} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hck : CheckOK μ env fe s) (henv : EnvWF env) (hok2 : StepOK env2 fe2 s)
    (hpins : PinsDenote s.store pins pinsP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : checkDivModPin μ pins fe fe2 cn s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkDivModPin (ConLeche.fueledOps μ F) pinsP env env2 nm
        = .ok () := by
  simp only [Arena.checkDivModPin] at hrun
  obtain ⟨g, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, hx1, hc1, hp1, rfl⟩ :=
    divModEnvGuard_run hck.state hck.pins hok2.ienv hn g1
  split at r1
  · rename_i hG
    cases hf : fe2.find? cn with
    | none =>
      rw [hf] at r1
      exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
    | some ci =>
    rw [hf] at r1
    match ci, hf, r1 with
    | .defnInfo cvI value' hint', hfind, r1 =>
      obtain ⟨nm0, c, hn0, hci, hfindP⟩ := hok2.ienv.hit cn _ hfind
      rw [hn] at hn0
      obtain rfl := Option.some.inj hn0
      simp only [Frontend.denoteCI] at hci
      cases hcv : Frontend.denoteCV s.store cvI with
      | none => rw [hcv] at hci; simp at hci
      | some cv' =>
      cases hvv : denoteE s.store value' with
      | none => rw [hcv, hvv] at hci; simp at hci
      | some v' =>
      rw [hcv, hvv] at hci
      simp only [Option.some.injEq] at hci
      subst hci
      have hwc := hok2.envWF _ (List.mem_of_find?_eq_some hfindP)
      obtain ⟨hf1, -, -, -⟩ := hwc.2.2.2.2.1 cv' v' hint' rfl
      have hck1 : CheckOK μ env fe s1 := hck.mono hst1 hx1 hc1 hp1
      obtain ⟨hck', hx', hp', F, hF⟩ :=
        checkDivModPinLoop_bridge hμ hk henv (ConLeche.Expr.WScoped.of_not_hasFvar hf1)
          pins pinsP [] [] s1 s' hck1 (PinsDenote.mono hx1 _ _ hpins) (denoteN_ext hn hx1)
          (denote_ext hvv hx1) r1
      refine ⟨hck'.state, hx1.trans hx', by rw [hp', hp1], F, ?_⟩
      simp only [ConLeche.checkDivModPin, hG, hfindP, if_true]
      exact hF
    | .axiomInfo _, _, r1 => exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
    | .thmInfo _ _, _, r1 => exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
    | .indInfo _ _, _, r1 => exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
    | .ctorInfo _ _ _, _, r1 => exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
    | .recInfo _ _ _ _, _, r1 => exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
    | .projInfo _, _, r1 => exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  · exact absurd r1 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)

end ConRon.Bridge
