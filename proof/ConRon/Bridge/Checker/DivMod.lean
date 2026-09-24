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

/-- con-leche: ConLeche/Kernel/Checker.lean:285-290 divModEnvGuard (one
`Bool` constructor's clause) — the twin's `boolCtorTyped` is con-leche's
clause. -/
theorem boolCtorTyped_runsB {env2 : Env} {fe2 : IFEnv} {n : NIdx}
    {nm : ConLeche.Name} {s : AState} (hok : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns n = some nm) :
    RunsB (Arena.boolCtorTyped fe2 n) s
      (match env2.find? nm with
        | some ci => ci.toConstantVal.type == .const ConLeche.boolName []
        | none => false) := by
  unfold Arena.boolCtorTyped
  rcases hie.findRel hok hn with ⟨hx, hy⟩ | ⟨ci, c, hx, hy, hd⟩
  · rw [hx, hy]; exact RunsB.ret hok
  · rw [hx, hy]
    refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (CIProjNamed_of_find hie hx) hd g1
    refine ⟨hs1, ?_⟩
    obtain ⟨-, -, hvt⟩ := denoteCV_inv hv
    refine RunsB.pin hs1.ok (hp.mono hs1.ext hs1.pins) (x := ConLeche.boolName) (by rfl)
      fun bn dbn => ?_
    refine RunsB.bind fun {bty s₂} g2 => ?_
    obtain ⟨hs2, hbty⟩ := constE_run hs1.ok (hp.mono hs1.ext hs1.pins) dbn g2
    refine ⟨hs2, ?_⟩
    rw [beqE_of_denote hs2.ok.wf (denote_ext hvt hs2.ext) hbty]
    exact RunsB.ret hs2.ok

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
  refine RunsB.pin st4 hp4 (x := ConLeche.boolTrueName) (by rfl) fun bt dbt => ?_
  refine RunsB.bindB (boolCtorTyped_runsB st4 hp4 hie4 dbt) fun {s5} hs5 => ?_
  obtain ⟨st5, hp5, hie5, -⟩ := tr (((hs1.trans hs3).trans hs4).trans hs5)
  refine RunsB.guard st5 (by first | rfl | (simp; rfl) | (simp; split <;> rfl)) fun _ => ?_
  refine RunsB.pin st5 hp5 (x := ConLeche.boolFalseName) (by rfl) fun bf dbf => ?_
  exact boolCtorTyped_runsB st5 hp5 hie5 dbf

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

/-! ### `divModCertStmts` in the port's factoring (task #97-T2-LOCKSTEP lane
Checker DeclCheck slice 2): one `_run` per twin helper. -/

/-- The context's twenty-one handles denote con-leche's `let`s. -/
structure CertCtxOK (st : EStore) (cx : CertCtxA) : Prop where
  natTy : denoteE st cx.natTy = some (.const ConLeche.natName [])
  x : denoteE st cx.x = some (.fvar 0 (.const ConLeche.natName []))
  y : denoteE st cx.y = some (.fvar 1 (.const ConLeche.natName []))
  one : denoteE st cx.one = some (.app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName []))
  bleN : denoteN st.ns cx.bleN = some ConLeche.natBleName
  boolTy : denoteE st cx.boolTy = some (.const ConLeche.boolName [])
  bT : denoteE st cx.bT = some (.const ConLeche.boolTrueName [])
  bF : denoteE st cx.bF = some (.const ConLeche.boolFalseName [])
  z : denoteE st cx.z = some (.const ConLeche.natZeroName [])
  two : denoteE st cx.two = some
    (.app (.const ConLeche.natSuccName []) (.app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName [])))
  modN : denoteN st.ns cx.modN = some ConLeche.natModName
  divN : denoteN st.ns cx.divN = some ConLeche.natDivName
  addN : denoteN st.ns cx.addN = some ConLeche.natAddName
  mulN : denoteN st.ns cx.mulN = some ConLeche.natMulName
  subN : denoteN st.ns cx.subN = some ConLeche.natSubName
  gcdN : denoteN st.ns cx.gcdN = some ConLeche.natGcdName
  slN : denoteN st.ns cx.slN = some ConLeche.natShiftLeftName
  srN : denoteN st.ns cx.srN = some ConLeche.natShiftRightName
  landN : denoteN st.ns cx.landN = some ConLeche.natLandName
  lorN : denoteN st.ns cx.lorN = some ConLeche.natLorName
  xorN : denoteN st.ns cx.xorN = some ConLeche.natXorName

theorem CertCtxOK.mono {st st' : EStore} {cx : CertCtxA} (h : CertCtxOK st cx)
    (hx : Ext st st') : CertCtxOK st' cx :=
  ⟨denote_ext h.natTy hx, denote_ext h.x hx, denote_ext h.y hx, denote_ext h.one hx,
   denoteN_ext h.bleN hx, denote_ext h.boolTy hx, denote_ext h.bT hx, denote_ext h.bF hx,
   denote_ext h.z hx, denote_ext h.two hx, denoteN_ext h.modN hx, denoteN_ext h.divN hx,
   denoteN_ext h.addN hx, denoteN_ext h.mulN hx, denoteN_ext h.subN hx,
   denoteN_ext h.gcdN hx, denoteN_ext h.slN hx, denoteN_ext h.srN hx,
   denoteN_ext h.landN hx, denoteN_ext h.lorN hx, denoteN_ext h.xorN hx⟩

open Lean Elab Tactic Meta in
/-- Move every denotation fact (and `StateOK`/`PinsOK`/`CertCtxOK`) along one
`IStepS` step `hs`. -/
elab "dmc_move " hs:term : tactic => withMainContext do
  let names := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail || d.userName.hasMacroScopes then acc else acc.push d.userName
  for n in names do
    let h := mkIdent n
    try
      evalTactic (← `(tactic| first
        | replace $h:ident := denote_ext $h ($hs).ext
        | replace $h:ident := denoteN_ext $h ($hs).ext
        | replace $h:ident := CertCtxOK.mono $h ($hs).ext
        | replace $h:ident := PinsOK.mono $h ($hs).ext ($hs).pins
        | replace $h:ident := denoteEList_ext ($hs).ext _ _ $h))
    catch _ => pure ()

abbrev natTyE : Expr := .const ConLeche.natName []
abbrev xE : Expr := .fvar 0 natTyE
abbrev yE : Expr := .fvar 1 natTyE
abbrev oneE : Expr := .app (.const ConLeche.natSuccName []) (.const ConLeche.natZeroName [])
abbrev twoE : Expr := .app (.const ConLeche.natSuccName []) oneE
abbrev op2E (c : ConLeche.Name) (a b : Expr) : Expr := .app (.app (.const c []) a) b
abbrev eqBE (a b : Expr) : Expr :=
  .app (.app (.app (.const ConLeche.eqName [.succ .zero]) (.const ConLeche.boolName [])) a) b
abbrev eqNE (a b : Expr) : Expr :=
  .app (.app (.app (.const ConLeche.eqName [.succ .zero]) natTyE) a) b

theorem certGuard_run {cx : CertCtxA} {a b r g : EIdx} {A B R : Expr} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (ha : denoteE s.store a = some A) (hb : denoteE s.store b = some B)
    (hr : denoteE s.store r = some R) (h : certGuard cx a b r s = .ok (g, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store g = some (eqBE (op2E ConLeche.natBleName A B) R) := by
  simp only [certGuard] at h
  obtain ⟨v, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := natAp2_run hst hp hcx.bleN ha hb g1
  dmc_move hs1
  obtain ⟨hs2, e2⟩ := eqAt1_run hs1.ok hp hcx.boolTy e1 hr w1
  exact ⟨hs1.trans hs2, e2⟩

theorem certEq_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name} {r g : EIdx} {R : Expr}
    {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm)
    (hr : denoteE s.store r = some R) (h : certEq cx c r s = .ok (g, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store g = some (eqNE (op2E nm xE yE) R) := by
  simp only [certEq] at h
  obtain ⟨v, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := natAp2_run hst hp hn hcx.x hcx.y g1
  dmc_move hs1
  obtain ⟨hs2, e2⟩ := eqAt1_run hs1.ok hp hcx.natTy e1 hr w1
  exact ⟨hs1.trans hs2, e2⟩

theorem certHalves_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name} {g : EIdx}
    {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certHalves cx c s = .ok (g, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store g = some
      (op2E nm (op2E ConLeche.natDivName xE twoE) (op2E ConLeche.natDivName yE twoE)) := by
  simp only [certHalves] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := natAp2_run hst hp hcx.divN hcx.x hcx.two g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := natAp2_run hs1.ok hp hcx.divN hcx.y hcx.two g2
  dmc_move hs2
  obtain ⟨hs3, e3⟩ := natAp2_run hs2.ok hp hn e1 e2 w2
  exact ⟨hs1.trans (hs2.trans hs3), e3⟩

theorem certTwoEqs_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {h1 h2 r1 r2 : EIdx} {H1 H2 R1 R2 : Expr} {out : List (List EIdx × EIdx)}
    {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm)
    (d1 : denoteE s.store h1 = some H1) (d2 : denoteE s.store h2 = some H2)
    (dr1 : denoteE s.store r1 = some R1) (dr2 : denoteE s.store r2 = some R2)
    (h : certTwoEqs cx c h1 h2 r1 r2 s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([H1], eqNE (op2E nm xE yE) R1), ([H2], eqNE (op2E nm xE yE) R2)] := by
  simp only [certTwoEqs] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certEq_run hst hp hcx hn dr1 g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certEq_run hs1.ok hp hcx hn dr2 g2
  dmc_move hs2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok w2
  exact ⟨hs1.trans hs2, denoteEList_one d1, e1, denoteEList_one d2, e2, trivial⟩

theorem certGcd_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certGcd cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([eqBE (op2E ConLeche.natBleName oneE xE) (.const ConLeche.boolTrueName [])],
          eqNE (op2E nm xE yE) (op2E nm (op2E ConLeche.natModName yE xE) xE)),
       ([eqBE (op2E ConLeche.natBleName oneE xE) (.const ConLeche.boolFalseName [])],
          eqNE (op2E nm xE yE) yE)] := by
  simp only [certGcd] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certGuard_run hst hp hcx hcx.one hcx.x hcx.bT g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certGuard_run hs1.ok hp hcx hcx.one hcx.x hcx.bF g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := natAp2_run hs2.ok hp hcx.modN hcx.y hcx.x g3
  dmc_move hs3
  obtain ⟨v4, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, e4⟩ := natAp2_run hs3.ok hp hn e3 hcx.x g4
  dmc_move hs4
  obtain ⟨hs5, e5⟩ := certTwoEqs_run hs4.ok hp hcx hn e1 e2 e4 hcx.y w4
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans hs5))), e5⟩

abbrev bTE : Expr := .const ConLeche.boolTrueName []
abbrev bFE : Expr := .const ConLeche.boolFalseName []
abbrev bleE (a b : Expr) : Expr := op2E ConLeche.natBleName a b

theorem certShiftLeft_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certShiftLeft cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([eqBE (bleE oneE yE) bTE], eqNE (op2E nm xE yE)
          (op2E nm (op2E ConLeche.natMulName twoE xE) (op2E ConLeche.natSubName yE oneE))),
       ([eqBE (bleE oneE yE) bFE], eqNE (op2E nm xE yE) xE)] := by
  simp only [certShiftLeft] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certGuard_run hst hp hcx hcx.one hcx.y hcx.bT g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certGuard_run hs1.ok hp hcx hcx.one hcx.y hcx.bF g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := natAp2_run hs2.ok hp hcx.mulN hcx.two hcx.x g3
  dmc_move hs3
  obtain ⟨v4, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, e4⟩ := natAp2_run hs3.ok hp hcx.subN hcx.y hcx.one g4
  dmc_move hs4
  obtain ⟨v5, s5, g5, w5⟩ := AM.bind_ok w4
  obtain ⟨hs5, e5⟩ := natAp2_run hs4.ok hp hn e3 e4 g5
  dmc_move hs5
  obtain ⟨hs6, e6⟩ := certTwoEqs_run hs5.ok hp hcx hn e1 e2 e5 hcx.x w5
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans hs6)))), e6⟩

theorem certShiftRight_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certShiftRight cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([eqBE (bleE oneE yE) bTE], eqNE (op2E nm xE yE)
          (op2E ConLeche.natDivName (op2E nm xE (op2E ConLeche.natSubName yE oneE)) twoE)),
       ([eqBE (bleE oneE yE) bFE], eqNE (op2E nm xE yE) xE)] := by
  simp only [certShiftRight] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certGuard_run hst hp hcx hcx.one hcx.y hcx.bT g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certGuard_run hs1.ok hp hcx hcx.one hcx.y hcx.bF g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := natAp2_run hs2.ok hp hcx.subN hcx.y hcx.one g3
  dmc_move hs3
  obtain ⟨v4, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, e4⟩ := natAp2_run hs3.ok hp hn hcx.x e3 g4
  dmc_move hs4
  obtain ⟨v5, s5, g5, w5⟩ := AM.bind_ok w4
  obtain ⟨hs5, e5⟩ := natAp2_run hs4.ok hp hcx.divN e4 hcx.two g5
  dmc_move hs5
  obtain ⟨hs6, e6⟩ := certTwoEqs_run hs5.ok hp hcx hn e1 e2 e5 hcx.x w5
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans hs6)))), e6⟩

abbrev halvesE (nm : ConLeche.Name) : Expr :=
  op2E nm (op2E ConLeche.natDivName xE twoE) (op2E ConLeche.natDivName yE twoE)
abbrev modE (a : Expr) : Expr := op2E ConLeche.natModName a twoE

theorem certLand_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certLand cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([eqBE (bleE oneE xE) bTE], eqNE (op2E nm xE yE)
          (op2E ConLeche.natAddName (op2E ConLeche.natMulName twoE (halvesE nm))
            (op2E ConLeche.natMulName (modE xE) (modE yE)))),
       ([eqBE (bleE oneE xE) bFE], eqNE (op2E nm xE yE) (.const ConLeche.natZeroName []))] := by
  simp only [certLand] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certGuard_run hst hp hcx hcx.one hcx.x hcx.bT g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certGuard_run hs1.ok hp hcx hcx.one hcx.x hcx.bF g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := certHalves_run hs2.ok hp hcx hn g3
  dmc_move hs3
  obtain ⟨v4, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, e4⟩ := natAp2_run hs3.ok hp hcx.mulN hcx.two e3 g4
  dmc_move hs4
  obtain ⟨v5, s5, g5, w5⟩ := AM.bind_ok w4
  obtain ⟨hs5, e5⟩ := natAp2_run hs4.ok hp hcx.modN hcx.x hcx.two g5
  dmc_move hs5
  obtain ⟨v6, s6, g6, w6⟩ := AM.bind_ok w5
  obtain ⟨hs6, e6⟩ := natAp2_run hs5.ok hp hcx.modN hcx.y hcx.two g6
  dmc_move hs6
  obtain ⟨v7, s7, g7, w7⟩ := AM.bind_ok w6
  obtain ⟨hs7, e7⟩ := natAp2_run hs6.ok hp hcx.mulN e5 e6 g7
  dmc_move hs7
  obtain ⟨v8, s8, g8, w8⟩ := AM.bind_ok w7
  obtain ⟨hs8, e8⟩ := natAp2_run hs7.ok hp hcx.addN e4 e7 g8
  dmc_move hs8
  obtain ⟨hs9, e9⟩ := certTwoEqs_run hs8.ok hp hcx hn e1 e2 e8 hcx.z w8
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans
    (hs8.trans hs9))))))), e9⟩

theorem certLorRhs_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name} {g : EIdx}
    {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certLorRhs cx c s = .ok (g, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store g = some
      (op2E ConLeche.natAddName (op2E ConLeche.natMulName twoE (halvesE nm))
        (op2E ConLeche.natSubName (op2E ConLeche.natAddName (modE xE) (modE yE))
          (op2E ConLeche.natMulName (modE xE) (modE yE)))) := by
  simp only [certLorRhs] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certHalves_run hst hp hcx hn g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := natAp2_run hs1.ok hp hcx.mulN hcx.two e1 g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := natAp2_run hs2.ok hp hcx.modN hcx.x hcx.two g3
  dmc_move hs3
  obtain ⟨v4, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, e4⟩ := natAp2_run hs3.ok hp hcx.modN hcx.y hcx.two g4
  dmc_move hs4
  obtain ⟨v5, s5, g5, w5⟩ := AM.bind_ok w4
  obtain ⟨hs5, e5⟩ := natAp2_run hs4.ok hp hcx.addN e3 e4 g5
  dmc_move hs5
  obtain ⟨v6, s6, g6, w6⟩ := AM.bind_ok w5
  obtain ⟨hs6, e6⟩ := natAp2_run hs5.ok hp hcx.mulN e3 e4 g6
  dmc_move hs6
  obtain ⟨v7, s7, g7, w7⟩ := AM.bind_ok w6
  obtain ⟨hs7, e7⟩ := natAp2_run hs6.ok hp hcx.subN e5 e6 g7
  dmc_move hs7
  obtain ⟨hs8, e8⟩ := natAp2_run hs7.ok hp hcx.addN e2 e7 w7
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans
    (hs7.trans hs8)))))), e8⟩

theorem certXorRhs_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name} {g : EIdx}
    {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certXorRhs cx c s = .ok (g, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store g = some
      (op2E ConLeche.natAddName (op2E ConLeche.natMulName twoE (halvesE nm))
        (modE (op2E ConLeche.natAddName (modE xE) (modE yE)))) := by
  simp only [certXorRhs] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certHalves_run hst hp hcx hn g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := natAp2_run hs1.ok hp hcx.mulN hcx.two e1 g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := natAp2_run hs2.ok hp hcx.modN hcx.x hcx.two g3
  dmc_move hs3
  obtain ⟨v4, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, e4⟩ := natAp2_run hs3.ok hp hcx.modN hcx.y hcx.two g4
  dmc_move hs4
  obtain ⟨v5, s5, g5, w5⟩ := AM.bind_ok w4
  obtain ⟨hs5, e5⟩ := natAp2_run hs4.ok hp hcx.addN e3 e4 g5
  dmc_move hs5
  obtain ⟨v6, s6, g6, w6⟩ := AM.bind_ok w5
  obtain ⟨hs6, e6⟩ := natAp2_run hs5.ok hp hcx.modN e5 hcx.two g6
  dmc_move hs6
  obtain ⟨hs7, e7⟩ := natAp2_run hs6.ok hp hcx.addN e2 e6 w6
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans hs7))))), e7⟩

theorem certLor_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certLor cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([eqBE (bleE oneE xE) bTE], eqNE (op2E nm xE yE)
          (op2E ConLeche.natAddName (op2E ConLeche.natMulName twoE (halvesE nm))
            (op2E ConLeche.natSubName (op2E ConLeche.natAddName (modE xE) (modE yE))
              (op2E ConLeche.natMulName (modE xE) (modE yE))))),
       ([eqBE (bleE oneE xE) bFE], eqNE (op2E nm xE yE) yE)] := by
  simp only [certLor] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certGuard_run hst hp hcx hcx.one hcx.x hcx.bT g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certGuard_run hs1.ok hp hcx hcx.one hcx.x hcx.bF g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := certLorRhs_run hs2.ok hp hcx hn g3
  dmc_move hs3
  obtain ⟨hs4, e4⟩ := certTwoEqs_run hs3.ok hp hcx hn e1 e2 e3 hcx.y w3
  exact ⟨hs1.trans (hs2.trans (hs3.trans hs4)), e4⟩

theorem certXor_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certXor cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([eqBE (bleE oneE xE) bTE], eqNE (op2E nm xE yE)
          (op2E ConLeche.natAddName (op2E ConLeche.natMulName twoE (halvesE nm))
            (modE (op2E ConLeche.natAddName (modE xE) (modE yE))))),
       ([eqBE (bleE oneE xE) bFE], eqNE (op2E nm xE yE) yE)] := by
  simp only [certXor] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certGuard_run hst hp hcx hcx.one hcx.x hcx.bT g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certGuard_run hs1.ok hp hcx hcx.one hcx.x hcx.bF g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := certXorRhs_run hs2.ok hp hcx hn g3
  dmc_move hs3
  obtain ⟨hs4, e4⟩ := certTwoEqs_run hs3.ok hp hcx hn e1 e2 e3 hcx.y w3
  exact ⟨hs1.trans (hs2.trans (hs3.trans hs4)), e4⟩

abbrev recRhsE (nm : ConLeche.Name) : Expr :=
  if nm = ConLeche.natDivName then
    .app (.const ConLeche.natSuccName []) (op2E nm (op2E ConLeche.natSubName xE yE) yE)
  else op2E nm (op2E ConLeche.natSubName xE yE) yE
abbrev baseRhsE (nm : ConLeche.Name) : Expr :=
  if nm = ConLeche.natDivName then .const ConLeche.natZeroName [] else xE

theorem certRecRhs_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name} {g : EIdx}
    {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certRecRhs cx c s = .ok (g, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store g = some (recRhsE nm) := by
  simp only [certRecRhs] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := natAp2_run hst hp hcx.subN hcx.x hcx.y g1
  dmc_move hs1
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := natAp2_run hs1.ok hp hn e1 hcx.y g2
  dmc_move hs2
  have hb := beq_handle_iff hs2.ok.wf hn hcx.divN
  rcases AM.ite_ok w2 with ⟨y0, k⟩ | ⟨z0, k⟩
  · obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok k
    obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natSuccName) hp rfl g3
    obtain ⟨hs4, e4⟩ := natAp1_run hs2.ok hp d3 e2 w3
    refine ⟨hs1.trans (hs2.trans hs4), ?_⟩
    rw [e4, recRhsE, if_pos (hb.mp y0)]
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    refine ⟨hs1.trans hs2, ?_⟩
    rw [e2, recRhsE, if_neg (fun h => z0 (hb.mpr h))]

theorem certDivMod_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : certDivMod cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out
      [([eqBE (bleE yE xE) bTE, eqBE (bleE oneE yE) bTE], eqNE (op2E nm xE yE) (recRhsE nm)),
       ([eqBE (bleE yE xE) bFE], eqNE (op2E nm xE yE) (baseRhsE nm)),
       ([eqBE (bleE oneE yE) bFE], eqNE (op2E nm xE yE) (baseRhsE nm))] := by
  simp only [certDivMod, certDivModGuards, certDivModEqs] at h
  obtain ⟨v1, s1, g1, w1⟩ := AM.bind_ok h
  obtain ⟨hs1, e1⟩ := certRecRhs_run hst hp hcx hn g1
  dmc_move hs1
  have hbase : denoteE s1.store (if (c == cx.divN) = true then cx.z else cx.x) =
      some (baseRhsE nm) := by
    have hb := beq_handle_iff hs1.ok.wf hn hcx.divN
    by_cases hc : (c == cx.divN) = true
    · rw [if_pos hc, baseRhsE, if_pos (hb.mp hc)]; exact hcx.z
    · rw [if_neg hc, baseRhsE, if_neg (fun h => hc (hb.mpr h))]; exact hcx.x
  obtain ⟨v2, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := certGuard_run hs1.ok hp hcx hcx.y hcx.x hcx.bT g2
  dmc_move hs2
  obtain ⟨v3, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := certGuard_run hs2.ok hp hcx hcx.one hcx.y hcx.bT g3
  dmc_move hs3
  obtain ⟨v4, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, e4⟩ := certGuard_run hs3.ok hp hcx hcx.y hcx.x hcx.bF g4
  dmc_move hs4
  obtain ⟨v5, s5, g5, w5⟩ := AM.bind_ok w4
  obtain ⟨hs5, e5⟩ := certGuard_run hs4.ok hp hcx hcx.one hcx.y hcx.bF g5
  dmc_move hs5
  obtain ⟨v6, s6, g6, w6⟩ := AM.bind_ok w5
  obtain ⟨hs6, e6⟩ := certEq_run hs5.ok hp hcx hn e1 g6
  dmc_move hs6
  obtain ⟨v7, s7, g7, w7⟩ := AM.bind_ok w6
  obtain ⟨hs7, e7⟩ := certEq_run hs6.ok hp hcx hn hbase g7
  dmc_move hs7
  obtain ⟨rfl, rfl⟩ := AM.pure_ok w7
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans hs7))))),
    denoteEList_two e2 e3, e6, denoteEList_one e4, e7, denoteEList_one e5, e7, trivial⟩

set_option maxHeartbeats 2000000 in
theorem certCtx_run {cx : CertCtxA} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (h : certCtx s = .ok (cx, s')) :
    Frontend.IStepS s s' ∧ CertCtxOK s'.store cx := by
  simp only [certCtx] at h
  obtain ⟨v, s0, g, w⟩ := AM.bind_ok h
  obtain ⟨rfl, dnt⟩ := pinAt_run (x := ConLeche.natName) hp rfl g
  obtain ⟨vnt, s1, g1, w1⟩ := AM.bind_ok w
  obtain ⟨hs1, enat⟩ := constE_run hst hp dnt g1
  dmc_move hs1
  obtain ⟨vx, s2, g2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, ex⟩ := natVar_run hs1.ok hp g2
  dmc_move hs2
  obtain ⟨vy, s3, g3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, ey⟩ := natVar_run hs2.ok hp g3
  dmc_move hs3
  obtain ⟨vo, s4, g4, w4⟩ := AM.bind_ok w3
  obtain ⟨hs4, eone⟩ := natOne_run hs3.ok hp g4
  dmc_move hs4
  obtain ⟨vb, s5, g5, w5⟩ := AM.bind_ok w4
  obtain ⟨rfl, dble⟩ := pinAt_run (x := ConLeche.natBleName) hp rfl g5
  obtain ⟨vbn, s6, g6, w6⟩ := AM.bind_ok w5
  obtain ⟨rfl, dbn⟩ := pinAt_run (x := ConLeche.boolName) hp rfl g6
  obtain ⟨vbt, s7, g7, w7⟩ := AM.bind_ok w6
  obtain ⟨hs7, ebool⟩ := constE_run hs4.ok hp dbn g7
  dmc_move hs7
  obtain ⟨vtn, s8, g8, w8⟩ := AM.bind_ok w7
  obtain ⟨rfl, dtn⟩ := pinAt_run (x := ConLeche.boolTrueName) hp rfl g8
  obtain ⟨vt, s9, g9, w9⟩ := AM.bind_ok w8
  obtain ⟨hs9, ebt⟩ := constE_run hs7.ok hp dtn g9
  dmc_move hs9
  obtain ⟨vfn, s10, g10, w10⟩ := AM.bind_ok w9
  obtain ⟨rfl, dfn⟩ := pinAt_run (x := ConLeche.boolFalseName) hp rfl g10
  obtain ⟨vf, s11, g11, w11⟩ := AM.bind_ok w10
  obtain ⟨hs11, ebf⟩ := constE_run hs9.ok hp dfn g11
  dmc_move hs11
  obtain ⟨vzn, s12, g12, w12⟩ := AM.bind_ok w11
  obtain ⟨rfl, dzn⟩ := pinAt_run (x := ConLeche.natZeroName) hp rfl g12
  obtain ⟨vz, s13, g13, w13⟩ := AM.bind_ok w12
  obtain ⟨hs13, ez⟩ := constE_run hs11.ok hp dzn g13
  dmc_move hs13
  obtain ⟨vsn, s14, g14, w14⟩ := AM.bind_ok w13
  obtain ⟨rfl, dsn⟩ := pinAt_run (x := ConLeche.natSuccName) hp rfl g14
  obtain ⟨vtw, s15, g15, w15⟩ := AM.bind_ok w14
  obtain ⟨hs15, etwo⟩ := natAp1_run hs13.ok hp dsn eone g15
  dmc_move hs15
  obtain ⟨n1, s16, g16, w16⟩ := AM.bind_ok w15
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natModName) hp rfl g16
  obtain ⟨n2, s17, g17, w17⟩ := AM.bind_ok w16
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natDivName) hp rfl g17
  obtain ⟨n3, s18, g18, w18⟩ := AM.bind_ok w17
  obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natAddName) hp rfl g18
  obtain ⟨n4, s19, g19, w19⟩ := AM.bind_ok w18
  obtain ⟨rfl, d4⟩ := pinAt_run (x := ConLeche.natMulName) hp rfl g19
  obtain ⟨n5, s20, g20, w20⟩ := AM.bind_ok w19
  obtain ⟨rfl, d5⟩ := pinAt_run (x := ConLeche.natSubName) hp rfl g20
  obtain ⟨n6, s21, g21, w21⟩ := AM.bind_ok w20
  obtain ⟨rfl, d6⟩ := pinAt_run (x := ConLeche.natGcdName) hp rfl g21
  obtain ⟨n7, s22, g22, w22⟩ := AM.bind_ok w21
  obtain ⟨rfl, d7⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp rfl g22
  obtain ⟨n8, s23, g23, w23⟩ := AM.bind_ok w22
  obtain ⟨rfl, d8⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp rfl g23
  obtain ⟨n9, s24, g24, w24⟩ := AM.bind_ok w23
  obtain ⟨rfl, d9⟩ := pinAt_run (x := ConLeche.natLandName) hp rfl g24
  obtain ⟨n10, s25, g25, w25⟩ := AM.bind_ok w24
  obtain ⟨rfl, d10⟩ := pinAt_run (x := ConLeche.natLorName) hp rfl g25
  obtain ⟨n11, s26, g26, w26⟩ := AM.bind_ok w25
  obtain ⟨rfl, d11⟩ := pinAt_run (x := ConLeche.natXorName) hp rfl g26
  obtain ⟨rfl, rfl⟩ := AM.pure_ok w26
  exact ⟨hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs7.trans (hs9.trans (hs11.trans
    (hs13.trans hs15))))))),
    ⟨enat, ex, ey, eone, dble, ebool, ebt, ebf, ez, etwo, d1, d2, d3, d4, d5, d6, d7, d8,
      d9, d10, d11⟩⟩

theorem divModCertStmtsAt_run {cx : CertCtxA} {c : NIdx} {nm : ConLeche.Name}
    {out : List (List EIdx × EIdx)} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hcx : CertCtxOK s.store cx)
    (hn : denoteN s.store.ns c = some nm) (h : divModCertStmtsAt cx c s = .ok (out, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store out (ConLeche.divModCertStmts nm) := by
  simp only [divModCertStmtsAt] at h
  have b0 := beq_handle_iff hst.wf hn hcx.gcdN
  have b1 := beq_handle_iff hst.wf hn hcx.slN
  have b2 := beq_handle_iff hst.wf hn hcx.srN
  have b3 := beq_handle_iff hst.wf hn hcx.landN
  have b4 := beq_handle_iff hst.wf hn hcx.lorN
  have b5 := beq_handle_iff hst.wf hn hcx.xorN
  rcases AM.ite_ok h with ⟨y0, k0⟩ | ⟨z0, k0⟩
  · obtain ⟨hs, e⟩ := certGcd_run hst hp hcx hn k0
    refine ⟨hs, ?_⟩
    simp only [ConLeche.divModCertStmts, if_pos (b0.mp y0)]
    exact e
  have n0 : ¬ nm = ConLeche.natGcdName := fun h => z0 (b0.mpr h)
  rcases AM.ite_ok k0 with ⟨y1, k1⟩ | ⟨z1, k1⟩
  · obtain ⟨hs, e⟩ := certShiftLeft_run hst hp hcx hn k1
    refine ⟨hs, ?_⟩
    simp only [ConLeche.divModCertStmts, if_neg n0, if_pos (b1.mp y1)]
    exact e
  have n1 : ¬ nm = ConLeche.natShiftLeftName := fun h => z1 (b1.mpr h)
  rcases AM.ite_ok k1 with ⟨y2, k2⟩ | ⟨z2, k2⟩
  · obtain ⟨hs, e⟩ := certShiftRight_run hst hp hcx hn k2
    refine ⟨hs, ?_⟩
    simp only [ConLeche.divModCertStmts, if_neg n0, if_neg n1, if_pos (b2.mp y2)]
    exact e
  have n2 : ¬ nm = ConLeche.natShiftRightName := fun h => z2 (b2.mpr h)
  rcases AM.ite_ok k2 with ⟨y3, k3⟩ | ⟨z3, k3⟩
  · obtain ⟨hs, e⟩ := certLand_run hst hp hcx hn k3
    refine ⟨hs, ?_⟩
    simp only [ConLeche.divModCertStmts, if_neg n0, if_neg n1, if_neg n2, if_pos (b3.mp y3)]
    exact e
  have n3 : ¬ nm = ConLeche.natLandName := fun h => z3 (b3.mpr h)
  rcases AM.ite_ok k3 with ⟨y4, k4⟩ | ⟨z4, k4⟩
  · obtain ⟨hs, e⟩ := certLor_run hst hp hcx hn k4
    refine ⟨hs, ?_⟩
    simp only [ConLeche.divModCertStmts, if_neg n0, if_neg n1, if_neg n2, if_neg n3,
      if_pos (b4.mp y4)]
    exact e
  have n4 : ¬ nm = ConLeche.natLorName := fun h => z4 (b4.mpr h)
  rcases AM.ite_ok k4 with ⟨y5, k5⟩ | ⟨z5, k5⟩
  · obtain ⟨hs, e⟩ := certXor_run hst hp hcx hn k5
    refine ⟨hs, ?_⟩
    simp only [ConLeche.divModCertStmts, if_neg n0, if_neg n1, if_neg n2, if_neg n3,
      if_neg n4, if_pos (b5.mp y5)]
    exact e
  have n5 : ¬ nm = ConLeche.natXorName := fun h => z5 (b5.mpr h)
  obtain ⟨hs, e⟩ := certDivMod_run hst hp hcx hn k5
  refine ⟨hs, ?_⟩
  simp only [ConLeche.divModCertStmts, if_neg n0, if_neg n1, if_neg n2, if_neg n3,
    if_neg n4, if_neg n5]
  exact e

/-- con-leche: ConLeche/Kernel/Checker.lean:155-222 divModCertStmts — **the
pinned characterization statements, interned**: the context, then the arm the
operation's name selects.

**PROVED** compositionally (task #97-T2-LOCKSTEP lane Checker DeclCheck slice
2), one `_run` per twin helper, after the twin took the port's factoring.  It
replaces round 10's generated 500-line proof of the old twin. -/
theorem divModCertStmts_run {cn : NIdx} {nm : ConLeche.Name}
    {stmts : List (List EIdx × EIdx)} {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns cn = some nm)
    (hr : Arena.divModCertStmts cn s = .ok (stmts, s')) :
    Frontend.IStepS s s' ∧ StmtsDenote s'.store stmts (ConLeche.divModCertStmts nm) := by
  simp only [Arena.divModCertStmts] at hr
  obtain ⟨cx, s1, g1, w1⟩ := AM.bind_ok hr
  obtain ⟨hs1, hcx⟩ := certCtx_run hst hp g1
  dmc_move hs1
  obtain ⟨hs2, e2⟩ := divModCertStmtsAt_run hs1.ok hp hcx hn w1
  exact ⟨hs1.trans hs2, e2⟩

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
