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

`sorry`: `divModCertStmts`' exactness (eight branches of `natAp*`/`eqAt1`,
the `natOpEquations_run` generator), `divModCertProofs`' handle chain, a
full-walk `substConstAll_run`, `substConst0List`, and the guard walks. -/
theorem divModCertsGuard_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {val : EIdx} {v : Expr} {r : Bool} {s s' : AState}
    (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm) (hv : denoteE s.store val = some v)
    (hr : Arena.divModCertsGuard ps fe cn val s = .ok (r, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      r = ConLeche.divModCertsGuard psP env nm v := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt — one
variant's attempt: on success the invariant stands, and a `true` answer is
con-leche's.

`sorry`: two `KnotSpec.annotate` and one `KnotSpec.defeq` at depth 0 for the
pin, then the certificate loop — `KnotSpec.annotate`/`infer`/`defeq` at
depth 4 over `divModCertApplied`, whose `WScoped 4` preconditions need a
`natOpEquations_wscoped`-style fact about the pinned statements. -/
theorem checkDivModPinAt_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {val : EIdx} {v : Expr} {b : Bool} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm) (hv : denoteE s.store val = some v)
    (hwsv : Expr.WScoped 0 v)
    (hr : Arena.checkDivModPinAt μ fe cn val ps s = .ok (b, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      (b = true → ∃ F, ConLeche.checkDivModPinAt (ConLeche.fueledOps μ F) env nm v psP
        = .ok true) := by
  sorry

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
    exact absurd hrun (AM.Never.bind (fun _ => AM.Never.fail _) s () s')
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
            hn2 hv2 hwsv ha
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
          | exact absurd r3 (AM.Never.fail _ _ _ _)
          | exact recurse _ _ hck2 hx02 hp02 r3
    · exact recurse s2 _ hck2 hx02 hp02 r2

/-- con-leche: ConLeche/Kernel/Checker.lean:380-388 checkDivModPin — **the
`Nat.div`/`Nat.mod` variant gate**: the stored value must be definitionally
equal to some committed pin variant and that variant's certificates must
check.  No variant matching is a decline.

**SKELETONISED** (task #97-P3-Checker round 9): the environment guard
(`divModEnvGuard_run`), the lookup of the stored value through the extended
index's `IFEnvOK` (its `WScoped 0` from `EnvWF env2`), and the variant loop
(`checkDivModPinLoop_bridge`, PROVED) — over the four named pieces above:
`divModEnvGuard_run`, `divModPinGuard_run`, `divModCertsGuard_run`,
`checkDivModPinAt_bridge`. -/
theorem checkDivModPin_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env env2 : Env}
    {fe fe2 : IFEnv} {cn : NIdx} {nm : ConLeche.Name} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hok2 : StepOK env2 fe2 s)
    (hpins : PinsDenote s.store pins pinsP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : checkDivModPin μ pins fe fe2 cn s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkDivModPin (ConLeche.fueledOps μ F) pinsP env env2 nm
        = .ok () := by
  simp only [Arena.checkDivModPin] at hrun
  obtain ⟨g, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, hx1, hc1, hp1, rfl⟩ :=
    divModEnvGuard_run hok.check.state hok.check.pins hok2.ienv hn g1
  split at r1
  · rename_i hG
    cases hf : fe2.find? cn with
    | none =>
      rw [hf] at r1
      exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
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
      have hck1 : CheckOK μ env fe s1 := hok.check.mono hst1 hx1 hc1 hp1
      obtain ⟨hck', hx', hp', F, hF⟩ :=
        checkDivModPinLoop_bridge hμ hk hok.envWF (ConLeche.Expr.WScoped.of_not_hasFvar hf1)
          pins pinsP [] [] s1 s' hck1 (PinsDenote.mono hx1 _ _ hpins) (denoteN_ext hn hx1)
          (denote_ext hvv hx1) r1
      refine ⟨hck'.state, hx1.trans hx', by rw [hp', hp1], F, ?_⟩
      simp only [ConLeche.checkDivModPin, hG, hfindP, if_true]
      exact hF
    | .axiomInfo _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .thmInfo _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .indInfo _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .ctorInfo _ _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .recInfo _ _ _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .projInfo _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  · exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

end ConRon.Bridge
