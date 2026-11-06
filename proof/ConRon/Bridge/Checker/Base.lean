/-
# `ConRon.Bridge.Checker.Base` — `CheckerBase`'s specs

The twin of `ConLeche/Kernel/CheckerBase.lean` is `Arena/CheckerBase.lean`,
and this module is its bridge tier: the two memoised DAG walks the
declaration front door runs, and the per-declaration constant check.

## What it rests on

Everything here bottoms out in `KnotSpec` (the inference call) and in the `ExprOps` tier's walks, and the guards that do
NOT are the memoised ones — `allLevelParamsDefined` and `constsResolveFFast`
— which `Arena/CheckerBase.lean` carries because con-leche's own tree walks do
not terminate on a shared DAG (con-leche's task #210 Part B).  Each is a
memoised walk with an explicitly threaded table, so each needs its own memo
invariant and its own fuel induction, in `Bridge/ExprOps/Walks.lean`'s shape.
-/
module

public import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.ExprOps.Ranges
public import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr
import ConLeche.Verify.BridgeDecl

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The name-shape guards

Pure tests on handles.  Each is a handle comparison where con-leche has a
`Name` comparison, and each is exact for the same reason: `denoteN` is
injective (`Arena/WFProofs.lean`'s `denoteN_inj`, DESIGN §8.3's soundness
obligation).  The LIST membership test of the family,
`denoteNList_contains`, is `Bridge/Grind.lean`'s.

**The `AM` readers, as equations.**  `viewN` is a `get` and a `match`, so its
run form is `rfl`; after `viewN_apply` no proof below mentions `StateT`. -/

/-- con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup — the handle test
is the name test, by `denoteNList_contains` at every tail. -/
theorem nameNodup_spec {st : EStore} (hwf : StoreWF st) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns ns = some xs →
        nameNodup ns = ConLeche.Name.nodup xs := by
  intro ns
  induction ns with
  | nil =>
    intro xs h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [nameNodup, ConLeche.Name.nodup,
          denoteNList_contains hwf as ys has a y ha, ih ys has]

/-! ## The two name guards of the front door

`natOpName` and `litShapeOk` read the pin table and (the second) the record
itself; each is a walk in the `Core/Walks` style. -/

section Walks

set_option experimental.vcgen true

open Std.WP ConRon.Bridge.Core
open scoped Lean.Order

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-! `Bridge/Grind.lean` §6's handle inverses and the tags' values, registered
locally, as `Core/Walks/Nat.lean` registers them (these walks compare handles
against pins and interned terms). -/
local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)
local grind_pattern [bridge_grind] lsIdxAt => denoteLs st.lss n
local grind_pattern [bridge_grind] LsIdxAt.some => LsIdxAt st n (some ls)
local grind_pattern [bridge_grind] eIdxAt => denoteE st n
local grind_pattern [bridge_grind] EIdxAt.some => EIdxAt st n (some e)
attribute [local bridge_grind =] ETag.bvar ETag.fvar ETag.sort ETag.const ETag.app ETag.lam
  ETag.forallE ETag.letE ETag.lit ETag.proj exprTag

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:481-482 natOpName — **THEOREM 1
for `natOpName`**: the fifteen pinned handles answer con-leche's membership
test at a denoted name. -/
theorem natOpName_run (s₀ : AState) (n : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK eager env fe s₀) (hn : denoteN s₀.store.ns n = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpName n
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.natOpName nm; ⊤⦄ := by
  -- `splits := 20`, `gen := 16`: fifteen chained pin reads, each a split of the
  -- membership test
  sym only [bridge_grind, ConLeche.natOpName, ConLeche.natOpNames,
      ConLeche.natDivModNames, List.elem_cons_or, List.elem_nil] =>
    vcgen [ConRon.Arena.natOpName, ConRon.Arena.natOpNames, ConRon.Arena.natDivModNames,
      ConRon.Arena.natPredName, ConRon.Arena.pinNatPred,
      ConRon.Arena.natAddName, ConRon.Arena.pinNatAdd,
      ConRon.Arena.natSubName, ConRon.Arena.pinNatSub,
      ConRon.Arena.natMulName, ConRon.Arena.pinNatMul,
      ConRon.Arena.natPowName, ConRon.Arena.pinNatPow,
      ConRon.Arena.natBeqName, ConRon.Arena.pinNatBeq,
      ConRon.Arena.natBleName, ConRon.Arena.pinNatBle,
      ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv,
      ConRon.Arena.natModName, ConRon.Arena.pinNatMod,
      ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd,
      ConRon.Arena.natLandName, ConRon.Arena.pinNatLand,
      ConRon.Arena.natLorName, ConRon.Arena.pinNatLor,
      ConRon.Arena.natXorName, ConRon.Arena.pinNatXor,
      ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft,
      ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight, pinAt_specE] <;>
      finish (splits := 20) (gen := 16)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:202-206 natIndOk — at an optional
record related by `OptCI`. -/
theorem natIndOk_optRun (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK eager env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natIndOk oc
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.natIndOk oc'; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.natIndOk, ConRon.Arena.sortOne] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk — at an optional
record related by `OptCI`. -/
theorem natZeroOk_optRun (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK eager env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natZeroOk oc
    ⦃fun b s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natZeroOk oc'; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.natZeroOk, ConRon.Arena.pinNat,
      constE_spec (eager := eager) (env := env) (fe := fe) (nm := ConLeche.natName),
      pinAt_specE] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — at an optional
record related by `OptCI`. -/
theorem natSuccOk_optRun (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK eager env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natSuccOk oc
    ⦃fun b s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natSuccOk oc'; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.natSuccOk, ConRon.Arena.pinNat,
      constE_spec (eager := eager) (env := env) (fe := fe) (nm := ConLeche.natName),
      pinAt_specE] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:375-386 litShapeOk — **THEOREM 1
for `litShapeOk`**: the ten-way pinned-name chain, each arm the shape walk of
its name. -/
theorem litShapeOk_run (s₀ : AState) (ci : IConstantInfo) (c : ConstantInfo)
    (hok : CheckOK eager env fe s₀) (hci : Frontend.denoteCI s₀.store ci = some c) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.litShapeOk ci
    ⦃fun b s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.litShapeOk c; ⊤⦄ := by
  have hrel : OptCI s₀.store (some ci) (some c) := ⟨c, hci, rfl⟩
  have hn : denoteN s₀.store.ns ci.name = some c.name := denoteCI_name hci
  -- `splits := 20`: the ten-way pin-name chain splits once per name
  sym only [bridge_grind, ConLeche.litShapeOk] =>
    vcgen [ConRon.Arena.litShapeOk, ConRon.Arena.pinNat, ConRon.Arena.pinNatZero,
      ConRon.Arena.pinNatSucc, ConRon.Arena.pinString, ConRon.Arena.pinStringOfList,
      ConRon.Arena.pinList, ConRon.Arena.pinListNil, ConRon.Arena.pinListCons,
      ConRon.Arena.pinChar, ConRon.Arena.pinCharOfNat, pinAt_specE,
      natIndOk_optRun (eager := eager) (env := env) (fe := fe) (oc' := some c),
      natZeroOk_optRun (eager := eager) (env := env) (fe := fe) (oc' := some c),
      natSuccOk_optRun (eager := eager) (env := env) (fe := fe) (oc' := some c),
      stringTyOk_spec (eager := eager) (env := env) (fe := fe) (oc' := some c),
      stringOfListTyOk_spec (eager := eager) (env := env) (fe := fe) (oc' := some c),
      listTyOk_spec (eager := eager) (env := env) (fe := fe) (oc' := some c),
      listNilTyOk_spec (eager := eager) (env := env) (fe := fe) (oc' := some c),
      listConsTyOk_spec (eager := eager) (env := env) (fe := fe) (oc' := some c),
      charTyOk_spec (eager := eager) (env := env) (fe := fe) (oc' := some c),
      charOfNatTyOk_spec (eager := eager) (env := env) (fe := fe) (oc' := some c)] <;>
      finish (splits := 20)

end Walks

/-! ## The per-declaration constant check -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal —
**THE declaration front door**, and what every arm of
`Bridge/Checker/Decl.lean` bottoms out in: the seven guards, the inference of
the type as stored, and the sort test.  It returns nothing (con-leche e74d32ad:
no annotation pass, `checkConstantVal` returns `Unit`).

The conclusion is a refinement, as everywhere in this tier: an accepting arena
run gives an accepting pure run whose answer the arena's answer denotes.  The
guards are what make it non-trivial — each must be *exact*, not merely sound,
because the arena's acceptance has to imply con-leche's.

Proved: the five guards (`fe.find?` through `IFEnvOK`, `reservedBasisNames`
through the lemma above, `nameNodup`,
`looseBVarsBoundedFast` and `hasFvarFast` through `Bridge/ExprOps/Walks.lean`),
then `allLevelParamsDefined_run`,
`constsResolveFFast_run`, `KnotSpec.infer` and
`EnsureSortSpec.ensureSort`, in that order.  All seven arms rest on it.

**The hypotheses are `CheckOK` and `EnvWF`, not `FoldOK`**, for the
Inductives tier: the inductive routes call it at an index that already holds
a scratch constant, where `FoldOK`'s `PersIFEnv` is false, and the proof
does not read `PersIFEnv`.  The arms use `checkConstantVal_bridge_of_fold`. -/
theorem checkConstantVal_pure {μ : CheckMode} {F : Nat} {env : Env}
    {c : ConstantVal} {a : Bool} {sty : Expr} {u : Level}
    (h1 : env.find? c.name = none)
    (h2 : ConLeche.reservedBasisNames.contains c.name = false)
    (h3 : (ConLeche.natOpName c.name && !a) = false)
    (h3s : ConLeche.litShapeOk (.axiomInfo c) = true)
    (h4 : ConLeche.Name.nodup c.levelParams = true)
    (h5 : c.type.looseBVarsBounded 0 = true)
    (h6 : c.type.hasFvar = false)
    (h8 : c.type.allLevelParamsDefined c.levelParams = true)
    (h9 : c.type.constsResolve env = true)
    (h10 : ConLeche.inferTypeCore μ false env F 0 c.type = .ok sty)
    (h11 : ConLeche.ensureSortCore μ false env F 0 sty = .ok u) :
    ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c a = .ok () := by
  simp only [ConLeche.checkConstantVal, ConLeche.fueledOps, h1, h2, h3, h3s, h4, h5,
    h6, h8, h9, h10, h11, Option.isSome_none, Bool.false_eq_true, ite_false,
    ite_true, bind, Except.bind, pure, Except.pure]

theorem checkConstantVal_bridge {env : Env}
    {fe : IFEnv} {cv : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hk : CoreSpec Arena.checkFuel)
    (hck0 : CheckOK false env fe s) (henv : EnvWF env)
    (hcv : Frontend.denoteCV s.store cv = some c) {allowOp : Bool}
    (hrun : checkConstantVal .verified fe cv allowOp s = .ok ((), s')) :
    CoreStep env fe s s' ∧ ∃ F,
      ConLeche.checkConstantVal (ConLeche.fueledOps .verified F) env c allowOp = .ok () := by
  obtain ⟨hnm, hlps, hty⟩ := denoteCV_inv hcv
  have hknot := hk.knot env fe henv
  have hsortS := hk.sort env fe henv
  have hnever : ∀ {α β γ : Type} {x : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (x >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.checkConstantVal] at hrun
  -- 1. the duplicate-declaration guard
  obtain ⟨hdup, r1⟩ := AM.dguard_ok AM.Never.fail_any hrun
  replace r1 := AM.pure_bind_ok r1
  have hfind : fe.find? cv.name = none := by
    cases hf : fe.find? cv.name with
    | none => rfl
    | some ci => rw [hf] at hdup; exact absurd rfl hdup
  have hfindP : env.find? c.name = none :=
    IFEnvOK.miss hck0.state hck0.ienv hnm hfind
  -- 2. the reserved-name guard
  obtain ⟨rs, s1, g2r, r2⟩ := AM.bind_ok r1
  obtain ⟨hp1, hrs⟩ := reservedBasisNames_run hck0.state.wf hck0.pins g2r
  have hck1 : CheckOK false env fe s1 := hck0.mono ⟨hp1.wf⟩ hp1.ext hp1.caches hp1.pins
  have hnm1 : denoteN s1.store.ns cv.name = some c.name := denoteN_ext hnm hp1.ext
  obtain ⟨hres, r3⟩ := AM.dguard_ok AM.Never.fail_any r2
  replace r3 := AM.pure_bind_ok r3
  have hresP : ConLeche.reservedBasisNames.contains c.name = false := by
    have hc := denoteNList_contains hck1.state.wf rs reservedBasisNameValues
      (denoteNL_toList rs reservedBasisNameValues hrs) cv.name c.name hnm1
    rw [← reservedBasisNameValues_eq, ← hc]
    cases hb : rs.contains cv.name with
    | false => rfl
    | true => rw [hb] at hres; exact absurd rfl hres
  -- 2a. the certified-operation-name guard: a pin read moves nothing
  obtain ⟨bo, sO, gO, rO⟩ := AM.bind_ok r3
  obtain ⟨rfl, hbo⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => t = s1 ∧ r = ConLeche.natOpName c.name)
    rfl gO (natOpName_run s1 cv.name c.name hck1 hnm1)
  obtain ⟨hop, rO2⟩ := AM.dguard_ok
    (AM.Never.bind fun _ => AM.Never.fail_any) rO
  replace rO2 := AM.pure_bind_ok rO2
  have hopP : (ConLeche.natOpName c.name && !allowOp) = false := by
    rw [← hbo]
    cases hb : (bo && !allowOp) with
    | false => rfl
    | true => rw [hb] at hop; exact absurd rfl hop
  -- 2b. the literal-shape guard, at the record as an axiom
  have hciA : Frontend.denoteCI sO.store (.axiomInfo cv) = some (.axiomInfo c) := by
    simp only [Frontend.denoteCI, denoteCV_ext hcv hp1.ext, Option.map_some]
  obtain ⟨bl, s2, gL, rL⟩ := AM.bind_ok rO2
  obtain ⟨hck2, hxL, hpL, hbl⟩ := AM.of_run (P := fun t => t = sO)
    (Q := fun r t => CheckOK false env fe t ∧ Ext sO.store t.store ∧
      t.pins = sO.pins ∧ r = ConLeche.litShapeOk (.axiomInfo c))
    rfl gL (litShapeOk_run sO (.axiomInfo cv) (.axiomInfo c) hck1 hciA)
  obtain ⟨hshape, r3⟩ := AM.dunless_ok AM.Never.fail_any rL
  replace r3 := AM.pure_bind_ok r3
  have hshapeP : ConLeche.litShapeOk (.axiomInfo c) = true := by rw [← hbl]; exact hshape
  have hx02 : Ext s.store s2.store := hp1.ext.trans hxL
  have hp02 : s2.pins = s.pins := by rw [hpL, hp1.pins]
  have hnm2 : denoteN s2.store.ns cv.name = some c.name := denoteN_ext hnm hx02
  have hlps2 : Frontend.denoteNList s2.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx02.lss.ls.ns _ _ hlps
  have hty2 : denoteE s2.store cv.type = some c.type := denote_ext hty hx02
  -- 3. the duplicate-universe-parameter guard
  obtain ⟨hnod, r6⟩ := AM.dunless_ok AM.Never.fail_any r3
  replace r6 := AM.pure_bind_ok r6
  have hnodP : ConLeche.Name.nodup c.levelParams = true := by
    rw [← nameNodup_spec hck2.state.wf cv.levelParams c.levelParams hlps2]
    exact hnod
  -- 4. the loose-bound-variable guard
  obtain ⟨b5, s5, g5r, r7⟩ := AM.bind_ok r6
  obtain ⟨h5st, h5c, h5p, h5r⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => t.store = s2.store ∧ t.caches = s2.caches ∧
      t.pins = s2.pins ∧ RelV (Expr.looseBVarsBounded 0) s2.store cv.type r)
    rfl g5r (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s2 cv.type
      hck2.state (by rw [hty2]; rfl))
  obtain ⟨hlbb, r8⟩ := AM.dunless_ok AM.Never.fail_any r7
  replace r8 := AM.pure_bind_ok r8
  have hlbbP : c.type.looseBVarsBounded 0 = true := by
    rw [← h5r c.type hty2]; exact hlbb
  have hck5 : CheckOK false env fe s5 :=
    hck2.mono ⟨by rw [h5st]; exact hck2.state.wf⟩ (by rw [h5st]; exact Ext.refl _)
      h5c h5p
  have hnm5 : denoteN s5.store.ns cv.name = some c.name := by rw [h5st]; exact hnm2
  have hty5 : denoteE s5.store cv.type = some c.type := by rw [h5st]; exact hty2
  have hlps5 : Frontend.denoteNList s5.store.ns cv.levelParams
      = some c.levelParams := by rw [h5st]; exact hlps2
  -- 5. the free-variable guard
  obtain ⟨b6, s6, g6r, r9⟩ := AM.bind_ok r8
  obtain ⟨h6st, h6c, h6p, h6r⟩ := AM.of_run (P := fun t => t = s5)
    (Q := fun r t => t.store = s5.store ∧ t.caches = s5.caches ∧
      t.pins = s5.pins ∧ RelV Expr.hasFvar s5.store cv.type r)
    rfl g6r (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s5 cv.type hck5.state
      (by rw [hty5]; rfl))
  obtain ⟨hfv, r10⟩ := AM.dguard_ok AM.Never.fail_any r9
  replace r10 := AM.pure_bind_ok r10
  have hfvP : c.type.hasFvar = false := by
    rw [← h6r c.type hty5]
    cases hb : b6 with
    | false => rfl
    | true => rw [hb] at hfv; exact absurd rfl hfv
  have hck6 : CheckOK false env fe s6 :=
    hck5.mono ⟨by rw [h6st]; exact hck5.state.wf⟩ (by rw [h6st]; exact Ext.refl _)
      h6c h6p
  have hnm6 : denoteN s6.store.ns cv.name = some c.name := by rw [h6st]; exact hnm5
  have hty6 : denoteE s6.store cv.type = some c.type := by rw [h6st]; exact hty5
  have hlps6 : Frontend.denoteNList s6.store.ns cv.levelParams
      = some c.levelParams := by rw [h6st]; exact hlps5
  have hws : Expr.WScoped 0 c.type := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  -- 6. the undeclared-universe-parameter guard
  obtain ⟨b8, s8, g8r, r12⟩ := AM.bind_ok r10
  obtain ⟨h8st, h8c, h8p, h8r⟩ :=
    allLevelParamsDefined_run hck6.state hlps6 hty6 g8r
  obtain ⟨hlpd, r13⟩ := AM.dunless_ok AM.Never.fail_any r12
  replace r13 := AM.pure_bind_ok r13
  have hlpdP : c.type.allLevelParamsDefined c.levelParams = true := by
    rw [← h8r]; exact hlpd
  have hck8 : CheckOK false env fe s8 :=
    hck6.mono ⟨by rw [h8st]; exact hck6.state.wf⟩ (by rw [h8st]; exact Ext.refl _)
      h8c h8p
  have hty8 : denoteE s8.store cv.type = some c.type := by rw [h8st]; exact hty6
  -- 7. the unresolved-constant guard
  obtain ⟨b9, s9, g9r, r14⟩ := AM.bind_ok r13
  obtain ⟨h9st, h9c, h9p, h9r⟩ :=
    constsResolveFFast_run hck8 hty8 g9r
  obtain ⟨hcr, r15⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.bind fun _ => AM.Never.fail_any) r14
  replace r15 := AM.pure_bind_ok r15
  have hcrP : c.type.constsResolve env = true := by rw [← h9r]; exact hcr
  have hck9 : CheckOK false env fe s9 :=
    hck8.mono ⟨by rw [h9st]; exact hck8.state.wf⟩ (by rw [h9st]; exact Ext.refl _)
      h9c h9p
  have hty9 : denoteE s9.store cv.type = some c.type := by rw [h9st]; exact hty8
  -- 8. the inference, of the type AS STORED
  obtain ⟨stype, s10, g10r, r16⟩ := AM.bind_ok r15
  obtain ⟨hck10, hx10, hp10, hsim10⟩ := AM.of_run (P := fun t => t = s9)
    (Q := fun r t => CheckOK false env fe t ∧ Ext s9.store t.store ∧
      t.pins = s9.pins ∧
      Core.SimE (ConLeche.inferTypeCore .verified false env) 0 c.type t.store r)
    rfl g10r (hknot.infer s9 0 cv.type c.type hck9 hty9 hws)
  obtain ⟨w, hw10, hwsw, F10, hF10⟩ := hsim10
  -- 9. the sort test
  obtain ⟨u, s11, g11r, r17⟩ := AM.bind_ok r16
  obtain ⟨hck11, hx11, hp11, hsim11⟩ := AM.of_run (P := fun t => t = s10)
    (Q := fun r t => CheckOK false env fe t ∧ Ext s10.store t.store ∧
      t.pins = s10.pins ∧
      SimL (ConLeche.ensureSortCore .verified false env) 0 w t.store r)
    rfl g11r (hsortS s10 0 stype w hck10 hw10 hwsw)
  obtain ⟨uu, huu, F11, hF11⟩ := hsim11
  -- 10. the answer: the run ENDS at the sort test
  obtain ⟨-, rfl⟩ := AM.pure_ok r17
  -- the frame
  have hext : Ext s.store s'.store := by
    refine hx02.trans ?_
    rw [← h5st, ← h6st, ← h8st, ← h9st]
    exact hx10.trans hx11
  have hpins : s'.pins = s.pins := by
    rw [hp11, hp10, h9p, h8p, h6p, h5p, hp02]
  have hle10 : F10 ≤ max F10 F11 := Nat.le_max_left F10 F11
  have hle11 : F11 ≤ max F10 F11 := Nat.le_max_right F10 F11
  refine ⟨⟨hck11, hext, hpins⟩, max F10 F11, ?_⟩
  exact checkConstantVal_pure hfindP hresP hopP hshapeP hnodP hlbbP hfvP
    hlpdP hcrP
    (ConLeche.inferTypeCore_mono hle10 hF10)
    (ConLeche.ensureSortCore_mono hle11 hF11)

/-- con-leche: ConLeche/Verify/Cached/BridgeCS1.lean:43 checkConstantValS_sim —
`checkConstantVal_bridge` at the fold's invariant, which is what the seven
arms hold. -/
theorem checkConstantVal_bridge_of_fold {env : Env}
    {fe : IFEnv} {cv : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hk : CoreSpec Arena.checkFuel)
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    {allowOp : Bool}
    (hrun : checkConstantVal .verified fe cv allowOp s = .ok ((), s')) :
    CoreStep env fe s s' ∧ ∃ F,
      ConLeche.checkConstantVal (ConLeche.fueledOps .verified F) env c allowOp = .ok () :=
  checkConstantVal_bridge hk hok.check hok.envWF hcv hrun

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:279 checkConstantVal_datF —
one fuel for the front door, through con-leche's own monotone family. -/
theorem checkConstantVal_mono {μ : CheckMode} {env : Env} {c : ConstantVal}
    {a : Bool} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c a = .ok ()) :
    ConLeche.checkConstantVal (ConLeche.fueledOps μ F') env c a = .ok () := by
  rw [← ConLeche.checkConstantVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkConstantVal (ConLeche.fueledOpsM μ) env c a).property hle h

/-! ## A list inversion -/

/-- con-leche: none — `Frontend.denoteEList`'s `cons` inversion. -/
theorem denoteEList_cons {st : EStore} {a : EIdx} {as : List EIdx}
    {zs : List Expr} (h : Frontend.denoteEList st (a :: as) = some zs) :
    ∃ x xs, denoteE st a = some x ∧ Frontend.denoteEList st as = some xs ∧
      zs = x :: xs := by
  simp only [Frontend.denoteEList] at h
  cases hx : denoteE st a with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some x =>
    cases hxs : Frontend.denoteEList st as with
    | none => rw [hx, hxs] at h; exact absurd h (by simp)
    | some xs =>
      rw [hx, hxs] at h
      simp only [Option.some.injEq] at h
      exact ⟨x, xs, rfl, rfl, h.symm⟩

end ConRon.Bridge
