/-
# `ConRon.Bridge.Compare.Record` — a record's check with a solution is a mixed step

`Arena/Justify.lean`'s `recordCheck` with a solution: the `And` pin, then `checkRecord (some J)`,
which sends a record that offers a statement (`justifiable`) down the justification route
(`checkJustified`: `justifyWhy`, the type's front door, the reserved names' check) and every
other record to its own `checkDecl`.  Its accept is one step of `Compare/Model.lean`'s
`MixedStep` at the environment the view stands for: the own route by `Arena.checkDecl_bridge`,
the justification route by `justifyWhy_run`, `checkConstantVal_bridge_of_fold` (con-leche's
`constantValRun_of`) and `basisNamesOk_run` — exactly the facts con-leche's
`checkRecordC_justified_run` reads off its cached route.
-/
module

public import ConRon.Bridge.Compare.Cone
public import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Specs
import ConLeche.Semantics.Bridge.DeclRun

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-- con-leche: ConLeche/Verify/Cached/JustifyBridge.lean:29 checkRecordC_justified_run — **the
justification route, run**: the statement justified by the solution (con-leche's `justifyWhy`),
the reserved names' check passed, its type's front door run (`ConstantValRun`); the store
invariant, an append and the pins kept. -/
theorem checkJustified_run {env envS : Env} {fe fe' : IFEnv} {J : ISolution}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} {pd : IDeclaration}
    {d : Declaration} {cv : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hk : CoreSpec Arena.checkFuel) (hok : FoldOK env fe s)
    (hsol : IFEnvOK envS (SolView J) s) (hm : MatesDen s.store J.mates matesU)
    (hd : Frontend.denoteDecl s.store pd = some d) (hc : Frontend.denoteCV s.store cv = some c)
    (hrun : checkJustified .verified J fe pd cv s = .ok (fe', s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ConLeche.Cached.justifyWhy ⟨mkFEnv envS, matesU⟩ (mkFEnv env) c = none ∧
      ConLeche.basisNamesOk d = true ∧ ∃ F, ConLeche.Semantics.ConstantValRun F env c c.type := by
  simp only [checkJustified] at hrun
  obtain ⟨w, s₁, h1, k1⟩ := AM.bind_ok hrun
  cases w with
  | some why =>
    exact absurd k1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  | none =>
  obtain ⟨hs1, hwhy⟩ := justifyWhy_run hok.check hsol hm hc h1
  simp only at k1
  have hok₁ : FoldOK env fe s₁ := hok.step (hs1.checkOK hok.check) hs1.pins
  obtain ⟨u, s₂, h2, k2⟩ := AM.bind_ok k1
  obtain ⟨hcs, F, hF⟩ := checkConstantVal_bridge_of_fold hk hok₁ (denoteCV_ext hc hs1.ext) h2
  obtain ⟨b, s₃, h3, k3⟩ := AM.bind_ok k2
  have hx12 := hs1.ext.trans hcs.ext
  obtain ⟨hs3, hb⟩ := basisNamesOk_run hcs.ok.state hcs.ok.readOK hcs.ok.pins
    (Frontend.denoteDecl_ext hx12 hd) h3
  rcases AM.ite_ok k3 with ⟨hy, k⟩ | ⟨-, k⟩
  · obtain ⟨-, rfl⟩ := AM.pure_ok k
    refine ⟨hs3.ok, hx12.trans hs3.ext, by rw [hs3.pins, hcs.pins, hs1.pins], hwhy,
      by rw [← hb]; simpa using hy, F, (ConLeche.Semantics.constantValRun_of hF).2.2⟩
  · exact absurd k (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

/-- con-leche: ConLeche/Cached/StreamIndex.lean:95-104 recordJob
con-leche: ConLeche/Cached/Justify.lean:200-216 checkRecordC — **a record's check at its view, with
a solution, bridged**: from the invariant at the view and the solution's view denoting `envS`
with the challenge's mates, the record's check accepting leaves the store invariant, an append
and the pins, and is one mixed step at the environment the view stands for. -/
@[expose] def RecordSpecC (pins : List INatOpPinSet) (pinsP : List NatOpPinSet) (J : ISolution)
    (envS : Env) (matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)) : Prop :=
  ∀ {env : Env} {I : IStreamIndex} {k : Nat} {pd : IDeclaration} {d : Declaration}
    {s s' : AState},
    FoldOK env (I.view k) s → PinsDenote s.store pins pinsP →
    Frontend.denoteDecl s.store pd = some d →
    IFEnvOK envS (SolView J) s → MatesDen s.store J.mates matesU →
    recordCheck .verified pins (some J) I k pd s = .ok ((), s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ env', Compare.MixedStep pinsP ⟨mkFEnv envS, matesU⟩ env d env'

/-- con-leche: ConLeche/Cached/StreamIndex.lean:95-104 recordJob — `RecordSpecC` discharged: the
`And` pin moves the store and nothing the check reads (`andPinOk_run`), then the record's route
(`justifiable_run`): its own check (`Arena.checkDecl_bridge`) or the justification
(`checkJustified_run`). -/
theorem recordSpecC {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {J : ISolution}
    {envS : Env} {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec) : RecordSpecC pins pinsP J envS matesU := by
  intro env I k pd d s s' hok hpins hd hsol hm hrun
  simp only [recordCheck, checkRecord] at hrun
  obtain ⟨b, s₁, ha, k1⟩ := AM.bind_ok hrun
  obtain ⟨hst₁, hx₁, hc₁, hp₁⟩ := andPinOk_run hok.check.state hok.check.pins hd ha
  rcases AM.ite_ok k1 with ⟨-, k2⟩ | ⟨-, k2⟩
  · obtain ⟨fe', s₂, hc, k3⟩ := AM.bind_ok k2
    obtain ⟨-, rfl⟩ := AM.pure_ok k3
    have hok₁ : FoldOK env (I.view k) s₁ := hok.step (hok.check.mono hst₁ hx₁ hc₁ hp₁) hp₁
    have hd₁ := Frontend.denoteDecl_ext hx₁ hd
    have hpins₁ := PinsDenote.mono hx₁ pins pinsP hpins
    obtain ⟨o, s₃, hj, k4⟩ := AM.bind_ok hc
    obtain ⟨rfl, hjn, hjs⟩ := justifiable_run hok₁.check hd₁ hj
    cases o with
    | none =>
      obtain ⟨hst₂, hx₂, hp₂, env', F, hF⟩ := Arena.checkDecl_bridge hk hind hok₁ hpins₁ hd₁ k4
      exact ⟨hst₂, hx₁.trans hx₂, hp₂.trans hp₁, env', .inl ⟨hjn rfl, F, hF⟩⟩
    | some cv =>
      obtain ⟨-, c, hcv, -, hjc⟩ := hjs cv rfl
      obtain ⟨hst₂, hx₂, hp₂, hwhy, hb, F, hF⟩ := checkJustified_run hk hok₁
        (hsol.mono hx₁) (hm.mono hst₁.wf hx₁) hd₁ hcv k4
      exact ⟨hst₂, hx₁.trans hx₂, hp₂.trans hp₁, _,
        .inr ⟨c, hjc, rfl, hwhy, hb, F, hF⟩⟩
  · exact absurd k2 (AM.Never.fail _ _ _ _)

end ConRon.Bridge
