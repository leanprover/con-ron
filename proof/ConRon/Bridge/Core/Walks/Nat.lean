/-
# `ConRon.Bridge.Core.Walks.Nat` — the literal acceleration, `reduceNat`

Task #97-P3-Core round 4.  `Bridge/Core/Arms/Whnf.lean`'s `whnfBody_spec`
inherited `sorryAx` (at the time) from exactly one walk after this round closed
`unfoldDefinition`: `reduceNat`.  This module is that walk and the six
state-only walks under it (`rawNatLit?`, `natLitSupported`, `natBinOpName`,
`natOpStored`, `natOpWfNames`, `natOpResult`), each an EQUATION with the
con-leche function of the same name — none of them is fueled on the pure
side.

Every one of them is DESIGN §8.3's *"index equality IS structural
equality"* cashed at a pin: the twin compares an `NIdx` against a pinned
name handle, an `LsIdx` against the empty-levels pin and an `EIdx` against an
interned constant, where con-leche compares the values; `denoteN_inj`,
`denoteLs_inj` and `denoteE_inj` make the two the same test.
-/
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Frame

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Index equality is value equality, at the three stores -/

/-- con-leche: none — DESIGN §8.3 at the level-list store. -/
theorem beq_of_denoteLs {st : LsStore} (hwf : LsStoreWF st) {i j : LsIdx}
    {x y : List Level} (hi : denoteLs st i = some x)
    (hj : denoteLs st j = some y) : (i == j) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; rw [hi] at hj; exact Option.some.inj hj
  · rintro rfl; exact denoteLs_inj hwf hi hj

/-! ## 2. `rawNatLit?` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit? — a handle
whose view is neither a `Nat` literal nor a constant reads as no literal. -/
theorem rawNatLit?_of_view {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hnl : ∀ n, v = .lit (.natVal n) → False)
    (hnc : ∀ c us, v = .const c us → False) :
    ConLeche.rawNatLit? e = none := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; rfl
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; rfl
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; rfl
  | const n us => exact absurd rfl (hnc n us)
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; rfl
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; rfl
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; rfl
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; rfl
  | lit l =>
    rw [denote_lit_inv hwf hv he]
    cases l with
    | natVal n => exact absurd rfl (hnl n)
    | strVal _ => rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit? — **THEOREM 1
for `rawNatLit?`**: the literal reading of a head normal form. -/
theorem rawNatLit?_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.rawNatLit? h
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.rawNatLit? x; ⊤⦄ := by
  have hp := hok.pins
  obtain ⟨rk, hrk⟩ := hok.state.wf
  vcgen [ConRon.Arena.rawNatLit?, ConRon.Arena.emptyLevels,
    ConRon.Arena.pinNatZero]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd [denote_lit_inv]
  bridge_frame
  -- a `Nat` literal
  vc_arm ⊢ some _ = ConLeche.rawNatLit? (.lit _) => rfl
  -- a constant: `Nat.zero` exactly when it is the pinned name at no levels
  vc_arm (hv : EStore.view _ _ = some (.const ?c ?us))
      (hn : denoteN _ ?c = some ?nm) (hls : denoteLs _ ?us = some ?ls)
      (hel : denoteLs _ _ = some [])
      (hnz : ∀ x, pinNames[PIN_NAT_ZERO]? = some x → denoteN _ _ = some x) =>
    rw [beq_of_denoteN hrk.nsWF hn (hnz _ rfl), beq_of_denoteLs hrk.lss hls hel]
    cases ls with
    | nil =>
      simp only [ConLeche.rawNatLit?]
      by_cases hz : nm = ConLeche.natZeroName <;> simp [hz]
    | cons l ls => simp [ConLeche.rawNatLit?]
  -- anything else
  vc_arm (hnl : ∀ n, ?v = ENodeView.lit (.natVal n) → False)
      (hnc : ∀ c us, ?v = ENodeView.const c us → False) (hv : EStore.view _ _ = some ?v) =>
    exact (rawNatLit?_of_view hok.state.wf hv hden hnl hnc).symm

/-! ## 3. The name tests -/

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **THEOREM 1 for
`natBinOpName`**: the binary literal acceleration's fourteen-way name test is
con-leche's disjunction. -/
theorem natBinOpName_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natBinOpName c
    ⦃fun b s' => s' = s₀ ∧ (b = true ↔
        (nm = ConLeche.natAddName ∨
        nm = ConLeche.natSubName ∨
        nm = ConLeche.natMulName ∨
        nm = ConLeche.natPowName ∨
        nm = ConLeche.natBeqName ∨
        nm = ConLeche.natBleName ∨
        nm = ConLeche.natDivName ∨
        nm = ConLeche.natModName ∨
        nm = ConLeche.natGcdName ∨
        nm = ConLeche.natLandName ∨
        nm = ConLeche.natLorName ∨
        nm = ConLeche.natXorName ∨
        nm = ConLeche.natShiftLeftName ∨
        nm = ConLeche.natShiftRightName)); ⊤⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  vcgen [ConRon.Arena.natBinOpName, ConRon.Arena.natAddName, ConRon.Arena.pinNatAdd, ConRon.Arena.natSubName, ConRon.Arena.pinNatSub, ConRon.Arena.natMulName, ConRon.Arena.pinNatMul, ConRon.Arena.natPowName, ConRon.Arena.pinNatPow, ConRon.Arena.natBeqName, ConRon.Arena.pinNatBeq, ConRon.Arena.natBleName, ConRon.Arena.pinNatBle, ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv, ConRon.Arena.natModName, ConRon.Arena.pinNatMod, ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd, ConRon.Arena.natLandName, ConRon.Arena.pinNatLand, ConRon.Arena.natLorName, ConRon.Arena.pinNatLor, ConRon.Arena.natXorName, ConRon.Arena.pinNatXor, ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft, ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight]
  all_goals (bridge_peel; subst_vars)
  all_goals first | exact hp | skip
  refine ⟨rfl, ?_⟩
  have beq_handle_eq := fun {n : NIdx} {y : ConLeche.Name} => @beq_handle_eq _ hwf c n nm y
  rw [beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_ADD]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_SUB]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_MUL]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_POW]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_BEQ]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_BLE]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_DIV]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_MOD]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_GCD]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_LAND]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_LOR]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_XOR]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_SHIFT_LEFT]? = some x → denoteN _ _ = some x› _ rfl),
      beq_handle_eq hn (‹∀ x, pinNames[PIN_NAT_SHIFT_RIGHT]? = some x → denoteN _ _ = some x› _ rfl)]
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]
  exact Iff.rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored — **THEOREM 1
for `natOpStored`**: is the operation stored as a definition. -/
theorem natOpStored_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpStored fe c
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.natOpStored env nm; ⊤⦄ := by
  vcgen [ConRon.Arena.natOpStored]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd [env_defn_of_index, env_not_defn_of_index]
  bridge_frame
  -- stored as a definition
  vc_arm (hfind : env.find? _ = some (.defnInfo _ _ _)) =>
    simp only [ConLeche.natOpStored, hfind]
  -- not stored as one
  vc_arm (hnd : ∀ cv val hint, env.find? nm ≠ some (.defnInfo cv val hint)) =>
    simp only [ConLeche.natOpStored]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:602-612 natOpWfNames — **THEOREM
1 for `natOpWfNames`**: the eight pinned handles answer con-leche's
membership test at every denoted name. -/
theorem natOpWfNames_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpWfNames
    ⦃fun ws s' => s' = s₀ ∧ ∀ c nm, denoteN s₀.store.ns c = some nm →
        ws.contains c = ConLeche.natOpWfNames.contains nm; ⊤⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  vcgen [ConRon.Arena.natOpWfNames, ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv, ConRon.Arena.natModName, ConRon.Arena.pinNatMod, ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd, ConRon.Arena.natLandName, ConRon.Arena.pinNatLand, ConRon.Arena.natLorName, ConRon.Arena.pinNatLor, ConRon.Arena.natXorName, ConRon.Arena.pinNatXor, ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft, ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight]
  all_goals (bridge_peel; subst_vars)
  all_goals first | exact hp | skip
  refine ⟨rfl, fun c nm hn => ?_⟩
  simp only [List.contains_cons, List.contains_nil, Bool.or_false,
    ConLeche.natOpWfNames]
  rw [beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_DIV]? = some x → denoteN _ _ = some x› _ rfl),
    beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_MOD]? = some x → denoteN _ _ = some x› _ rfl),
    beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_GCD]? = some x → denoteN _ _ = some x› _ rfl),
    beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_LAND]? = some x → denoteN _ _ = some x› _ rfl),
    beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_LOR]? = some x → denoteN _ _ = some x› _ rfl),
    beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_XOR]? = some x → denoteN _ _ = some x› _ rfl),
    beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_LEFT]? = some x → denoteN _ _ = some x› _ rfl),
    beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_RIGHT]? = some x → denoteN _ _ = some x› _ rfl)]
  rfl

/-! ## 4. `natOpResult` -/

set_option hygiene false in
/-- con-leche: none — the fifteen name tests of `natOpResult`'s chain, turned
into con-leche's `Name` tests at one arm. -/
local macro "nat_tests" : tactic => `(tactic| (
   have e0 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_PRED]? = some x → denoteN _ _ = some x› _ rfl)
   have e1 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_ADD]? = some x → denoteN _ _ = some x› _ rfl)
   have e2 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_SUB]? = some x → denoteN _ _ = some x› _ rfl)
   have e3 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_MUL]? = some x → denoteN _ _ = some x› _ rfl)
   have e4 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_POW]? = some x → denoteN _ _ = some x› _ rfl)
   have e5 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_BEQ]? = some x → denoteN _ _ = some x› _ rfl)
   have e6 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_BLE]? = some x → denoteN _ _ = some x› _ rfl)
   have e7 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_DIV]? = some x → denoteN _ _ = some x› _ rfl)
   have e8 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_MOD]? = some x → denoteN _ _ = some x› _ rfl)
   have e9 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_GCD]? = some x → denoteN _ _ = some x› _ rfl)
   have e10 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_LAND]? = some x → denoteN _ _ = some x› _ rfl)
   have e11 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_LOR]? = some x → denoteN _ _ = some x› _ rfl)
   have e12 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_XOR]? = some x → denoteN _ _ = some x› _ rfl)
   have e13 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_LEFT]? = some x → denoteN _ _ = some x› _ rfl)
   have e14 := beq_handle_eq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_RIGHT]? = some x → denoteN _ _ = some x› _ rfl)
   simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, beq_iff_eq] at *))

set_option hygiene false in
/-- con-leche: none — the state half of a `natOpResult` arm: one intern
after reads. -/
local macro "nat_frame" : tactic => `(tactic| (
   refine ⟨hok.mono ⟨?_⟩ ?_ ?_ ?_, ?_, ?_, ?_⟩
   rotate_left 5
   all_goals try assumption
   all_goals try exact Ext.refl _
   all_goals try rfl))

set_option hygiene false in
/-- con-leche: none — the answer half of a `natOpResult` arm: the interned
literal (or `Bool` constant, or nothing) IS con-leche's reduct. -/
local macro "nat_answer" : tactic => `(tactic| first
   | (simp only [denoteEO]
      simp (config := { decide := true }) [ConLeche.natOpResult,
        ConLeche.natPredName, ConLeche.natAddName, ConLeche.natSubName,
        ConLeche.natMulName, ConLeche.natPowName, ConLeche.natBeqName,
        ConLeche.natBleName, ConLeche.natDivName, ConLeche.natModName,
        ConLeche.natGcdName, ConLeche.natLandName, ConLeche.natLorName,
        ConLeche.natXorName, ConLeche.natShiftLeftName,
        ConLeche.natShiftRightName, ConLeche.boolTrueName,
        ConLeche.boolFalseName, *]
      done)
   | (rw [denoteEO, ‹denoteE _ _ = denoteEView _ _›]
      simp only [denoteEView, Option.map_some]
      simp (config := { decide := true }) [ConLeche.natOpResult,
        ConLeche.natPredName, ConLeche.natAddName, ConLeche.natSubName,
        ConLeche.natMulName, ConLeche.natPowName, ConLeche.natBeqName,
        ConLeche.natBleName, ConLeche.natDivName, ConLeche.natModName,
        ConLeche.natGcdName, ConLeche.natLandName, ConLeche.natLorName,
        ConLeche.natXorName, ConLeche.natShiftLeftName,
        ConLeche.natShiftRightName, ConLeche.boolTrueName,
        ConLeche.boolFalseName, *]
      done)
   | (rw [denoteEO, ‹denoteE _ _ = denoteEView _ _›]
      have hF := denoteN_ext
        (‹∀ x, pinNames[PIN_BOOL_FALSE]? = some x → denoteN _ _ = some x› _ rfl)
        ‹Ext _ _›
      have hL := denoteLs_ext ‹denoteLs _ _ = some []› ‹Ext _ _›
      simp only [denoteEView, hF, hL, opt2, Option.map_some]
      simp (config := { decide := true }) [ConLeche.natOpResult,
        ConLeche.natPredName, ConLeche.natAddName, ConLeche.natSubName,
        ConLeche.natMulName, ConLeche.natPowName, ConLeche.natBeqName,
        ConLeche.natBleName, ConLeche.natDivName, ConLeche.natModName,
        ConLeche.natGcdName, ConLeche.natLandName, ConLeche.natLorName,
        ConLeche.natXorName, ConLeche.natShiftLeftName,
        ConLeche.natShiftRightName, ConLeche.boolTrueName,
        ConLeche.boolFalseName, *]
      done)
   | (rw [denoteEO, ‹denoteE _ _ = denoteEView _ _›]
      have hT := denoteN_ext
        (‹∀ x, pinNames[PIN_BOOL_TRUE]? = some x → denoteN _ _ = some x› _ rfl)
        ‹Ext _ _›
      have hL := denoteLs_ext ‹denoteLs _ _ = some []› ‹Ext _ _›
      simp only [denoteEView, hT, hL, opt2, Option.map_some]
      simp (config := { decide := true }) [ConLeche.natOpResult,
        ConLeche.natPredName, ConLeche.natAddName, ConLeche.natSubName,
        ConLeche.natMulName, ConLeche.natPowName, ConLeche.natBeqName,
        ConLeche.natBleName, ConLeche.natDivName, ConLeche.natModName,
        ConLeche.natGcdName, ConLeche.natLandName, ConLeche.natLorName,
        ConLeche.natXorName, ConLeche.natShiftLeftName,
        ConLeche.natShiftRightName, ConLeche.boolTrueName,
        ConLeche.boolFalseName, *]
      done))

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult — **THEOREM 1
for `natOpResult`**: the reduct of a binary operation on two literals. -/
theorem natOpResult_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (a b : Nat) (hok : CheckOK mode env fe s₀)
    (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpResult c a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteEO s'.store r = some (ConLeche.natOpResult nm a b); ⊤⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  vcgen [ConRon.Arena.natOpResult, ConRon.Arena.natPredName, ConRon.Arena.pinNatPred, ConRon.Arena.natAddName, ConRon.Arena.pinNatAdd, ConRon.Arena.natSubName, ConRon.Arena.pinNatSub, ConRon.Arena.natMulName, ConRon.Arena.pinNatMul, ConRon.Arena.natPowName, ConRon.Arena.pinNatPow, ConRon.Arena.natBeqName, ConRon.Arena.pinNatBeq, ConRon.Arena.natBleName, ConRon.Arena.pinNatBle, ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv, ConRon.Arena.natModName, ConRon.Arena.pinNatMod, ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd, ConRon.Arena.natLandName, ConRon.Arena.pinNatLand, ConRon.Arena.natLorName, ConRon.Arena.pinNatLor, ConRon.Arena.natXorName, ConRon.Arena.pinNatXor, ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft, ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight, ConRon.Arena.constE,
    ConRon.Arena.emptyLevels, ConRon.Arena.boolTrueName,
    ConRon.Arena.boolFalseName, ConRon.Arena.pinBoolTrue,
    ConRon.Arena.pinBoolFalse]
  all_goals (bridge_peel; subst_vars)
  all_goals first
    | exact hp
    | exact hwf
    | exact viewOK_lit
    | (obtain ⟨w, hw, _⟩ := denoteLs_view ‹denoteLs _ _ = some []›
       exact viewOK_const (nview_isSome_of_denote
         (‹∀ x, pinNames[PIN_BOOL_TRUE]? = some x → denoteN _ _ = some x› _ rfl))
         (by rw [hw]; rfl))
    | (obtain ⟨w, hw, _⟩ := denoteLs_view ‹denoteLs _ _ = some []›
       exact viewOK_const (nview_isSome_of_denote
         (‹∀ x, pinNames[PIN_BOOL_FALSE]? = some x → denoteN _ _ = some x› _ rfl))
         (by rw [hw]; rfl))
    | skip
  all_goals nat_tests
  all_goals nat_frame
  all_goals nat_answer

/-! ## 5. `natLitSupported` — the three stored-declaration shapes -/

/-- con-leche: none — the index's answer at a name, against the
environment's, as ONE relation: a miss is a miss and a hit denotes the hit. -/
def OptCI (st : EStore) : Option IConstantInfo → Option ConstantInfo → Prop
  | none, oc' => oc' = none
  | some ci, oc' => ∃ c, Frontend.denoteCI st ci = some c ∧ oc' = some c

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index's two halves at
one denoted name, packaged as `OptCI`. -/
theorem optCI_find {s : AState} (hok : CheckOK mode env fe s) {n : NIdx}
    {nm : ConLeche.Name} (hn : denoteN s.store.ns n = some nm) :
    OptCI s.store (fe.find? n) (env.find? nm) := by
  cases hf : fe.find? n with
  | none => exact IFEnvOK.miss hok.state hok.ienv hn hf
  | some ci =>
    obtain ⟨nm', c, hn', hci, hfind⟩ := hok.ienv.hit n ci hf
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    exact ⟨c, hci, hfind⟩

/-- con-leche: none — a stored inductive denotes an inductive, and nothing
else does. -/
theorem denoteCI_ind_iff {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) :
    (∃ v caps, ci = .indInfo v caps) ↔ ∃ cv caps, c = .indInfo cv caps := by
  cases ci <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; simp)
    | (split at h
       · cases h; simp
       · simp at h)

/-- con-leche: none — the same at a constructor. -/
theorem denoteCI_ctor_iff {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) :
    (∃ v nP nF, ci = .ctorInfo v nP nF) ↔ ∃ cv nP nF, c = .ctorInfo cv nP nF := by
  cases ci <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; simp)
    | (split at h
       · cases h; simp
       · simp at h)

/-- con-leche: none — `denoteCI` keeps the constructor: an `.indInfo`
(`Inductives/Positivity.lean`'s `denoteCI_indInfo_inv`, which this module
cannot import). -/
theorem denoteCI_indInfo_split {st : EStore} {cv : IConstantVal} {caps : IIndCaps}
    {c : ConstantInfo} (h : Frontend.denoteCI st (.indInfo cv caps) = some c) :
    ∃ cvP capsP, Frontend.denoteCV st cv = some cvP ∧
      Frontend.denoteCaps st caps = some capsP ∧ c = .indInfo cvP capsP := by
  simp only [Frontend.denoteCI] at h
  cases h1 : Frontend.denoteCV st cv with
  | none => rw [h1] at h; exact nomatch h
  | some cvP =>
  cases h2 : Frontend.denoteCaps st caps with
  | none => rw [h1, h2] at h; exact nomatch h
  | some capsP =>
  rw [h1, h2] at h
  exact ⟨cvP, capsP, rfl, rfl, (Option.some.inj h).symm⟩

/-- con-leche: none — a denoting name-handle list is empty exactly when its
denotation is. -/
theorem isEmpty_of_denoteNList {st : NStore} {hs : List NIdx}
    {xs : List ConLeche.Name} (h : Frontend.denoteNList st hs = some xs) :
    hs.isEmpty = xs.isEmpty := by
  have := denoteNList_len h
  cases hs <;> cases xs <;> simp_all

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:202-206 natIndOk — **THEOREM 1
for `natIndOk`**. -/
theorem natIndOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natIndOk oc
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.natIndOk oc'; ⊤⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.natIndOk]
    all_goals (bridge_peel; subst_vars; exact ⟨rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    cases ci
    case indInfo v caps =>
      obtain ⟨cv, caps', hcv, _, rfl⟩ := denoteCI_indInfo_split hci
      obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
      vcgen [ConRon.Arena.natIndOk, ConRon.Arena.sortOne]
      all_goals (bridge_peel; subst_vars)
      bridge_frame
      vc_arm (hs1 : denoteE _ _ = some (.sort _)) =>
        simp only [ConLeche.natIndOk, isEmpty_of_denoteNList hlps,
          beq_of_denoteE hwf hty hs1]
    all_goals
      (have hn : ¬ ∃ cv caps, c = .indInfo cv caps := fun h' => by
         obtain ⟨v, caps, hv⟩ := (denoteCI_ind_iff hci).mpr h'; cases hv
       vcgen [ConRon.Arena.natIndOk]
       bridge_peel; subst_vars
       refine ⟨rfl, ?_⟩
       cases c <;> simp_all [ConLeche.natIndOk])

/-- con-leche: none — `ViewOK` of a constant node whose name and level list
denote (task #120: `bridge_frame`'s side-condition lemma for `constE`). -/
theorem viewOK_const_of_denote {st : EStore} {n : NIdx} {us : LsIdx}
    {nm : ConLeche.Name} {ls : List Level}
    (hn : denoteN st.ns n = some nm) (hl : denoteLs st.lss us = some ls) :
    st.ViewOK (.const n us) := by
  obtain ⟨w, hw, _⟩ := denoteLs_view hl
  exact viewOK_const (nview_isSome_of_denote hn) (by rw [hw]; rfl)

/-- con-leche: none — **THEOREM 1 for `constE`**: the level-monomorphic
constant at a denoted name. -/
theorem constE_spec (s₀ : AState) (n : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns n = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.constE n
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = some (.const nm []); ⊤⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  vcgen [ConRon.Arena.constE, ConRon.Arena.emptyLevels]
  all_goals (bridge_peel; subst_vars)
  bridge_frame [viewOK_const_of_denote]
  -- the interned node denotes the constant
  vc_arm (hd : denoteE _ _ = denoteEView _ _) (hel : denoteLs _ _ = some [])
      (hx : Ext _ _) =>
    rw [hd]
    simp only [denoteEView, denoteN_ext hn hx, denoteLs_ext hel hx, opt2]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk — **THEOREM 1
for `natZeroOk`**. -/
theorem natZeroOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natZeroOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natZeroOk oc'; ⊤⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.natZeroOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    cases ci
    case ctorInfo v nP nF =>
      obtain ⟨cv, hcv, rfl⟩ := denoteCI_ctorInfo_inv hci
      obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
      have hce := fun (s : AState) (n : NIdx) =>
        constE_spec (mode := mode) (env := env) (fe := fe) s n ConLeche.natName
      vcgen [ConRon.Arena.natZeroOk, ConRon.Arena.pinNat, hce]
      all_goals (bridge_peel; subst_vars)
      bridge_frame
      -- the type compared with the interned `Nat` by handle
      vc_arm (hck : CheckOK _ _ _ ?s) (hd : denoteE (AState.store ?s) _ = some (Expr.const _ []))
          (hx : Ext _ (AState.store ?s)) =>
        simp only [ConLeche.natZeroOk, isEmpty_of_denoteNList hlps,
          beq_of_denoteE hck.state.wf (denote_ext hty hx) hd]
    all_goals
      (have hn : ¬ ∃ cv nP nF, c = .ctorInfo cv nP nF := fun h' => by
         obtain ⟨v, nP, nF, hv⟩ := (denoteCI_ctor_iff hci).mpr h'; cases hv
       vcgen [ConRon.Arena.natZeroOk]
       all_goals (bridge_peel; subst_vars)
       refine ⟨hok, Ext.refl _, rfl, ?_⟩
       cases c <;> simp_all [ConLeche.natZeroOk])

/-- con-leche: none — `denote_not_forallE` at the tag-first twin's `else`
arm: a handle whose TAG is not `forallE` denotes no `∀` (task #120: the shape
`bridge_fwd` instantiates). -/
theorem denote_not_forallE_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} (he : denoteE st h = some e)
    (ht : ¬ (h.tag == ETag.forallE) = true) : ∀ ty b, e ≠ .forallE ty b := by
  obtain ⟨v, hv⟩ := denoteE_view he
  exact denote_not_forallE hwf hv he
    (fun ty b hh => view_tagOf_ne hv (t := ETag.forallE) ht (by rw [hh]; rfl))

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — a stored
`Nat.succ` with universe parameters is not the expected shape. -/
theorem natSuccOk_levels {cv : ConstantVal} {nP nF : Nat}
    (h : (!cv.levelParams.isEmpty) = true) :
    ConLeche.natSuccOk (some (.ctorInfo cv nP nF)) = false := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  simp only [ConLeche.natSuccOk, h, Bool.false_and]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — nor is one
whose type is not a `∀`. -/
theorem natSuccOk_not_forallE {cv : ConstantVal} {nP nF : Nat}
    (h : ∀ p q, cv.type ≠ .forallE p q) :
    ConLeche.natSuccOk (some (.ctorInfo cv nP nF)) = false := by
  simp only [ConLeche.natSuccOk]
  split
  · next heq => exact absurd heq (h _ _)
  · simp

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — **THEOREM 1
for `natSuccOk`**. -/
theorem natSuccOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natSuccOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natSuccOk oc'; ⊤⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.natSuccOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    cases ci
    case ctorInfo v nP nF =>
      obtain ⟨cv, hcv, rfl⟩ := denoteCI_ctorInfo_inv hci
      obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
      have hce := fun (s : AState) (n : NIdx) =>
        constE_spec (mode := mode) (env := env) (fe := fe) s n ConLeche.natName
      vcgen [ConRon.Arena.natSuccOk, ConRon.Arena.pinNat, hce]
      all_goals (bridge_peel; subst_vars)
      all_goals clear_tag_hyps
      bridge_frame
      bridge_fwd [denote_not_forallE, denote_not_forallE_of_tag]
      bridge_frame
      -- the type has universe parameters
      vc_arm (hne : (!v.levelParams.isEmpty) = true) =>
        rw [isEmpty_of_denoteNList hlps] at hne
        exact (natSuccOk_levels hne).symm
      -- the type is not a `∀` (by its view or by its tag)
      vc_arm (hnot : ∀ p q, cv.type ≠ .forallE p q) =>
        exact (natSuccOk_not_forallE hnot).symm
      -- the type is a `∀`: both sides compared with the interned `Nat`
      vc_arm (hpq : cv.type = .forallE ?p ?q) (hck : CheckOK _ _ _ ?s)
          (hp1 : denoteE (AState.store ?s) _ = some ?p)
          (hq1 : denoteE (AState.store ?s) _ = some ?q)
          (hd : denoteE (AState.store ?s) _ = some (Expr.const _ []))
          (hne : ¬ (!v.levelParams.isEmpty) = true) =>
        rw [isEmpty_of_denoteNList hlps] at hne
        simp only [ConLeche.natSuccOk, hpq,
          beq_of_denoteE hck.state.wf hp1 hd, beq_of_denoteE hck.state.wf hq1 hd]
        have hle : cv.levelParams.isEmpty = true := by simpa using hne
        rw [hle, Bool.true_and]
        split
        · next c1 c2 heq =>
          simp only [Expr.forallE.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          rw [Bool.eq_iff_iff]; simp
        · next hne' =>
          by_cases hp : p = .const ConLeche.natName []
          · by_cases hq : q = .const ConLeche.natName []
            · subst hp hq; exact absurd rfl (hne' _ _)
            · simp [hq]
          · simp [hp]
    all_goals
      (have hn : ¬ ∃ cv nP nF, c = .ctorInfo cv nP nF := fun h' => by
         obtain ⟨v, nP, nF, hv⟩ := (denoteCI_ctor_iff hci).mpr h'; cases hv
       vcgen [ConRon.Arena.natSuccOk]
       all_goals (bridge_peel; subst_vars)
       refine ⟨hok, Ext.refl _, rfl, ?_⟩
       cases c <;> simp_all [ConLeche.natSuccOk])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:225-233 natLitSupported —
**THEOREM 1 for `natLitSupported`**: the three stored-declaration shapes. -/
theorem natLitSupported_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natLitSupported fe
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natLitSupported env; ⊤⦄ := by
  have hp := hok.pins
  have hi := fun (s : AState) (oc : Option IConstantInfo) =>
    natIndOk_spec (mode := mode) (env := env) (fe := fe) s oc (env.find? ConLeche.natName)
  have hz := fun (s : AState) (oc : Option IConstantInfo) =>
    natZeroOk_spec (mode := mode) (env := env) (fe := fe) s oc (env.find? ConLeche.natZeroName)
  have hs := fun (s : AState) (oc : Option IConstantInfo) =>
    natSuccOk_spec (mode := mode) (env := env) (fe := fe) s oc (env.find? ConLeche.natSuccName)
  vcgen [ConRon.Arena.natLitSupported, ConRon.Arena.pinNat,
    ConRon.Arena.pinNatZero, ConRon.Arena.pinNatSucc, hi, hz, hs]
  all_goals (bridge_peel; subst_vars)
  bridge_frame [optCI_find, CheckOK.pins]
  -- the three declines and the conjunction: con-leche's `&&` at the verdicts
  all_goals
    cases h1 : ConLeche.natIndOk (env.find? ConLeche.natName) <;>
      cases h2 : ConLeche.natZeroOk (env.find? ConLeche.natZeroName) <;>
      simp_all [ConLeche.natLitSupported]

/-! ### The five in ANSWER shape

`reduceNat` reaches every one of them through another call — the reduct of a
`whnf`, or a name read off a `view` — so, by round 3's rule, the subjects'
denotations go in as an existential and come out as a universal.  Four lines
each over the published statements. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit? — answer
shape. -/
theorem rawNatLit?_spec' (s₀ : AState) (h : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.rawNatLit? h
    ⦃fun r s' => s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        r = ConLeche.rawNatLit? x; ⊤⦄ := by
  obtain ⟨x, hx⟩ := hpre
  have hb := rawNatLit?_spec s₀ h x hok hx
  vcgen [hb]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd
  bridge_frame

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — `natBinOpName`
in answer shape. -/
theorem natBinOpName_spec' (s₀ : AState) (c : NIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm, denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natBinOpName c
    ⦃fun b s' => s' = s₀ ∧ ∀ nm, denoteN s₀.store.ns c = some nm →
        (b = true ↔ (nm = ConLeche.natAddName ∨
          nm = ConLeche.natSubName ∨
          nm = ConLeche.natMulName ∨
          nm = ConLeche.natPowName ∨
          nm = ConLeche.natBeqName ∨
          nm = ConLeche.natBleName ∨
          nm = ConLeche.natDivName ∨
          nm = ConLeche.natModName ∨
          nm = ConLeche.natGcdName ∨
          nm = ConLeche.natLandName ∨
          nm = ConLeche.natLorName ∨
          nm = ConLeche.natXorName ∨
          nm = ConLeche.natShiftLeftName ∨
          nm = ConLeche.natShiftRightName)); ⊤⦄ := by
  obtain ⟨nm, hn⟩ := hpre
  have hb := natBinOpName_spec s₀ c nm hok hn
  vcgen [hb]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd
  bridge_frame

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored — answer
shape. -/
theorem natOpStored_spec' (s₀ : AState) (c : NIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm, denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpStored fe c
    ⦃fun b s' => s' = s₀ ∧ ∀ nm, denoteN s₀.store.ns c = some nm →
        b = ConLeche.natOpStored env nm; ⊤⦄ := by
  obtain ⟨nm, hn⟩ := hpre
  have hb := natOpStored_spec s₀ c nm hok hn
  vcgen [hb]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd
  bridge_frame

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult — answer
shape. -/
theorem natOpResult_spec' (s₀ : AState) (c : NIdx) (a b : Nat)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm, denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpResult c a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ nm, denoteN s₀.store.ns c = some nm →
        denoteEO s'.store r = some (ConLeche.natOpResult nm a b); ⊤⦄ := by
  obtain ⟨nm, hn⟩ := hpre
  have hb := natOpResult_spec s₀ c nm a b hok hn
  vcgen [hb]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd
  bridge_frame

/-! ### `reduceNat`'s pure side at its exits

con-leche's `reduceNat` at `pureFns F`, one equation per exit; the knot's
`whnf` slot is `ConLeche.whnf mode env F`. -/

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the binary
test, named. -/
abbrev NatBinOp (c : ConLeche.Name) : Prop :=
  c = ConLeche.natAddName ∨
      c = ConLeche.natSubName ∨
      c = ConLeche.natMulName ∨
      c = ConLeche.natPowName ∨
      c = ConLeche.natBeqName ∨
      c = ConLeche.natBleName ∨
      c = ConLeche.natDivName ∨
      c = ConLeche.natModName ∨
      c = ConLeche.natGcdName ∨
      c = ConLeche.natLandName ∨
      c = ConLeche.natLorName ∨
      c = ConLeche.natXorName ∨
      c = ConLeche.natShiftLeftName ∨
      c = ConLeche.natShiftRightName

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — `Nat.succ` on a
literal-supported environment: the argument's head normal form, read. -/
theorem reduceNatFueled_succ {F d : Nat} {c : ConLeche.Name} {a w : Expr}
    (hg : c = ConLeche.natSuccName ∧ ConLeche.natLitSupported env = true)
    (hw : ConLeche.whnf mode env F d a = .ok w) :
    ConLeche.reduceNatFueled mode env F d (.app (.const c []) a) =
      .ok ((ConLeche.rawNatLit? w).map (fun n => .lit (.natVal (n + 1)))) := by
  have e1 : (ConLeche.pureFns mode env F).whnf d a = .ok w := hw
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, ite_eq_left hg, e1, bind,
    Except.bind]
  cases ConLeche.rawNatLit? w <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the unary guard
declines. -/
theorem reduceNatFueled_succ_no {F d : Nat} {c : ConLeche.Name} {a : Expr}
    (hg : ¬ (c = ConLeche.natSuccName ∧ ConLeche.natLitSupported env = true)) :
    ConLeche.reduceNatFueled mode env F d (.app (.const c []) a) = .ok none := by
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, ite_eq_right hg]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the certified
binary operation: the FIRST argument is head-normalised and read; only on a
literal is the second. -/
theorem reduceNatFueled_bin {F d : Nat} {c : ConLeche.Name} {a b w₁ : Expr}
    (hg : NatBinOp c ∧ ConLeche.natOpStored env c = true)
    (h1 : ConLeche.whnf mode env F d a = .ok w₁) :
    ConLeche.reduceNatFueled mode env F d (.app (.app (.const c []) a) b) =
      (match ConLeche.rawNatLit? w₁ with
        | some n₁ => do
          match ConLeche.rawNatLit? (← ConLeche.whnf mode env F d b) with
          | some n₂ => pure (ConLeche.natOpResult c n₁ n₂)
          | none => pure none
        | none => pure none) := by
  have e1 : (ConLeche.pureFns mode env F).whnf d a = .ok w₁ := h1
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, NatBinOp] at hg ⊢
  rw [ite_eq_left hg]
  simp only [e1, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the WF-pinned
safety net. -/
theorem reduceNatFueled_wf {F d : Nat} {c : ConLeche.Name} {a b w₁ : Expr}
    (hg : ¬ (NatBinOp c ∧ ConLeche.natOpStored env c = true))
    (hw : ConLeche.natOpWfNames.contains c ∧ ConLeche.natLitSupported env = true)
    (h1 : ConLeche.whnf mode env F d a = .ok w₁) :
    ConLeche.reduceNatFueled mode env F d (.app (.app (.const c []) a) b) =
      (match ConLeche.rawNatLit? w₁ with
        | some _ => do
          match ConLeche.rawNatLit? (← ConLeche.whnf mode env F d b) with
          | some _ => throw (.notImplemented
              s!"native Nat computation on literals ({c})")
          | none => pure none
        | none => pure none) := by
  have e1 : (ConLeche.pureFns mode env F).whnf d a = .ok w₁ := h1
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, NatBinOp] at hg ⊢
  rw [ite_eq_right hg, ite_eq_left hw]
  simp only [e1, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — neither guard. -/
theorem reduceNatFueled_bin_no {F d : Nat} {c : ConLeche.Name} {a b : Expr}
    (hg : ¬ (NatBinOp c ∧ ConLeche.natOpStored env c = true))
    (hw : ¬ (ConLeche.natOpWfNames.contains c ∧ ConLeche.natLitSupported env = true)) :
    ConLeche.reduceNatFueled mode env F d (.app (.app (.const c []) a) b) =
      .ok none := by
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, NatBinOp] at hg ⊢
  rw [ite_eq_right hg, ite_eq_right hw]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a subject of
neither shape declines. -/
theorem reduceNatFueled_none_of {F d : Nat} {x : Expr}
    (h1 : ∀ c a, x ≠ .app (.const c []) a)
    (h2 : ∀ c a b, x ≠ .app (.app (.const c []) a) b) :
    ConLeche.reduceNatFueled mode env F d x = .ok none := by
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat]
  rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult — every
reduct is a literal or a `Bool` constant, hence closed. -/
theorem natOpResult_wscoped {c : ConLeche.Name} {a b d : Nat} {y : Expr}
    (h : ConLeche.natOpResult c a b = some y) : Expr.WScoped d y := by
  unfold ConLeche.natOpResult at h
  by_cases h0 : c = ConLeche.natPredName
  · rw [ite_eq_left h0] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h0] at h
  by_cases h1 : c = ConLeche.natAddName
  · rw [ite_eq_left h1] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h1] at h
  by_cases h2 : c = ConLeche.natSubName
  · rw [ite_eq_left h2] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h2] at h
  by_cases h3 : c = ConLeche.natMulName
  · rw [ite_eq_left h3] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h3] at h
  by_cases h4 : c = ConLeche.natPowName
  · rw [ite_eq_left h4] at h
    by_cases hb : b > 16777216
    · rw [ite_eq_left hb] at h; cases h
    · rw [ite_eq_right hb] at h; cases h; simp [Expr.WScoped]
  rw [ite_eq_right h4] at h
  by_cases h5 : c = ConLeche.natDivName
  · rw [ite_eq_left h5] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h5] at h
  by_cases h6 : c = ConLeche.natModName
  · rw [ite_eq_left h6] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h6] at h
  by_cases h7 : c = ConLeche.natGcdName
  · rw [ite_eq_left h7] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h7] at h
  by_cases h8 : c = ConLeche.natLandName
  · rw [ite_eq_left h8] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h8] at h
  by_cases h9 : c = ConLeche.natLorName
  · rw [ite_eq_left h9] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h9] at h
  by_cases h10 : c = ConLeche.natXorName
  · rw [ite_eq_left h10] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h10] at h
  by_cases h11 : c = ConLeche.natShiftLeftName
  · rw [ite_eq_left h11] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h11] at h
  by_cases h12 : c = ConLeche.natShiftRightName
  · rw [ite_eq_left h12] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h12] at h
  by_cases h13 : c = ConLeche.natBeqName
  · rw [ite_eq_left h13] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h13] at h
  by_cases h14 : c = ConLeche.natBleName
  · rw [ite_eq_left h14] at h
    cases h; simp [Expr.WScoped]
  rw [ite_eq_right h14] at h
  cases h

/-- con-leche: none — `CheckOK`'s two projections the precondition goals
of `reduceNat` ask for. -/
theorem CheckOK.wf' {s : AState} (h : CheckOK mode env fe s) : StoreWF s.store :=
  h.state.wf

/-- con-leche: none — the unary shape: an application of a level-free
constant, read off two views. -/
theorem unary_shape {st : EStore} (hwf : StoreWF st) {e f a : EIdx}
    {c : NIdx} {us el : LsIdx} {x : Expr}
    (hve : st.view e = some (.app f a)) (hvc : st.view f = some (.const c us))
    (hden : denoteE st e = some x) (hel : denoteLs st.lss el = some []) :
    ∃ nm ls ax, x = .app (.const nm ls) ax ∧ denoteN st.ns c = some nm ∧
      denoteE st a = some ax ∧ ((us != el) = (ls != [])) := by
  obtain ⟨fx, ax, rfl, hf, ha⟩ := denote_app_inv hwf hve hden
  obtain ⟨nm, ls, rfl, hn, hls⟩ := denote_const_inv hwf hvc hf
  obtain ⟨rk, hrk⟩ := hwf
  exact ⟨nm, ls, ax, rfl, hn, ha, by simp only [bne, beq_of_denoteLs hrk.lss hls hel]⟩

/-- con-leche: none — the binary shape. -/
theorem binary_shape {st : EStore} (hwf : StoreWF st) {e f₂ f a b : EIdx}
    {c : NIdx} {us el : LsIdx} {x : Expr}
    (hve : st.view e = some (.app f₂ b)) (hvf2 : st.view f₂ = some (.app f a))
    (hvc : st.view f = some (.const c us))
    (hden : denoteE st e = some x) (hel : denoteLs st.lss el = some []) :
    ∃ nm ls ax bx, x = .app (.app (.const nm ls) ax) bx ∧
      denoteN st.ns c = some nm ∧ denoteE st a = some ax ∧
      denoteE st b = some bx ∧ ((us != el) = (ls != [])) := by
  obtain ⟨fx, bx, rfl, hf, hb⟩ := denote_app_inv hwf hve hden
  obtain ⟨gx, ax, rfl, hg, ha⟩ := denote_app_inv hwf hvf2 hf
  obtain ⟨nm, ls, rfl, hn, hls⟩ := denote_const_inv hwf hvc hg
  obtain ⟨rk, hrk⟩ := hwf
  exact ⟨nm, ls, ax, bx, rfl, hn, ha, hb,
    by simp only [bne, beq_of_denoteLs hrk.lss hls hel]⟩

/-! ### `reduceNat`'s exits, in the shape `bridge_fwd` leaves them (task #120)

Each verification condition of `reduceNat_spec`, after `bridge_frame` and
`bridge_fwd`, has its subject's shape in `hden`, the guards' pure meaning (the
`*_guard` lemmas below, instantiated by `bridge_fwd`) and every callee's
answer in context; the lemmas here turn that into the `SimOOp` exit in one
`exact`. -/

/-- con-leche: none — a declining exit. -/
theorem simOOp_none {P : Nat → CheckM (Option Expr)} {d : Nat} {st : EStore}
    (F : Nat) (h : P F = .ok none) : SimOOp P d st none :=
  ⟨none, rfl, by simp, F, h⟩

/-- con-leche: none — the level-list test, by handle: the empty list. -/
theorem levels_nil {st : EStore} (hwf : StoreWF st) {us el : LsIdx}
    {ls : List Level} (h : ¬ (us != el) = true) (hls : denoteLs st.lss us = some ls)
    (hel : denoteLs st.lss el = some []) : ls = [] := by
  obtain ⟨rk, hrk⟩ := hwf
  simp only [bne, beq_of_denoteLs hrk.lss hls hel] at h
  simpa using h

/-- con-leche: none — the level-list test, by handle: not the empty list. -/
theorem levels_ne {st : EStore} (hwf : StoreWF st) {us el : LsIdx}
    {ls : List Level} (h : (us != el) = true) (hls : denoteLs st.lss us = some ls)
    (hel : denoteLs st.lss el = some []) : ls ≠ [] := by
  obtain ⟨rk, hrk⟩ := hwf
  simp only [bne, beq_of_denoteLs hrk.lss hls hel] at h
  simpa using h

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the `Nat.succ`
guard, by handle. -/
theorem succ_guard {st : EStore} (hwf : StoreWF st) {c ns : NIdx}
    {nm : ConLeche.Name} {b : Bool} (h : (c == ns && b) = true)
    (hn : denoteN st.ns c = some nm)
    (hs : ∀ x, pinNames[PIN_NAT_SUCC]? = some x → denoteN st.ns ns = some x) :
    nm = ConLeche.natSuccName ∧ b = true := by
  rw [beq_handle_eq hwf hn (hs _ rfl)] at h
  simpa only [Bool.and_eq_true, beq_iff_eq] using h

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the `Nat.succ`
guard declines. -/
theorem succ_guard_no {st : EStore} (hwf : StoreWF st) {c ns : NIdx}
    {nm : ConLeche.Name} {b : Bool} (h : ¬ (c == ns && b) = true)
    (hn : denoteN st.ns c = some nm)
    (hs : ∀ x, pinNames[PIN_NAT_SUCC]? = some x → denoteN st.ns ns = some x) :
    ¬ (nm = ConLeche.natSuccName ∧ b = true) := by
  rw [beq_handle_eq hwf hn (hs _ rfl)] at h
  simpa only [Bool.and_eq_true, beq_iff_eq] using h

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the binary
guard: `natBinOpName`'s answer and `natOpStored`'s. -/
theorem bin_guard {rb s : Bool} {nm : ConLeche.Name}
    (h : (rb && s) = true) (hiff : rb = true ↔ NatBinOp nm) :
    NatBinOp nm ∧ s = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨hiff.mp h.1, h.2⟩

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the binary
guard declines. -/
theorem bin_guard_no {rb s : Bool} {nm : ConLeche.Name}
    (h : ¬ (rb && s) = true) (hiff : rb = true ↔ NatBinOp nm) :
    ¬ (NatBinOp nm ∧ s = true) := fun ⟨c1, c2⟩ => h (by rw [hiff.mpr c1, c2]; rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the WF-pinned
safety net's guard. -/
theorem wf_guard {c : NIdx} {wf : List NIdx} {nm : ConLeche.Name} {b : Bool}
    (h : (wf.elem c && b) = true)
    (he : wf.elem c = ConLeche.natOpWfNames.elem nm) :
    ConLeche.natOpWfNames.contains nm ∧ b = true := by
  rw [he] at h; simpa using h

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the safety net
declines. -/
theorem wf_guard_no {c : NIdx} {wf : List NIdx} {nm : ConLeche.Name} {b : Bool}
    (h : ¬ (wf.elem c && b) = true)
    (he : wf.elem c = ConLeche.natOpWfNames.elem nm) :
    ¬ (ConLeche.natOpWfNames.contains nm ∧ b = true) := by
  rw [he] at h; simpa using h

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a unary
application of a constant WITH universe levels is no operation. -/
theorem reduceNat_unary_levels {F d : Nat} {nm : ConLeche.Name} {ls : List Level}
    {a : Expr} (h : ls ≠ []) :
    ConLeche.reduceNatFueled mode env F d (.app (.const nm ls) a) = .ok none :=
  reduceNatFueled_none_of
    (fun c a' h' => by
      simp only [Expr.app.injEq, Expr.const.injEq] at h'; exact h h'.1.2)
    (fun c a' b' h' => by simp at h')

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — nor is a binary
one. -/
theorem reduceNat_binary_levels {F d : Nat} {nm : ConLeche.Name}
    {ls : List Level} {a b : Expr} (h : ls ≠ []) :
    ConLeche.reduceNatFueled mode env F d (.app (.app (.const nm ls) a) b) = .ok none :=
  reduceNatFueled_none_of
    (fun c a' h' => by simp at h')
    (fun c a' b' h' => by
      simp only [Expr.app.injEq, Expr.const.injEq] at h'; exact h h'.1.1.2)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a binary
application whose head is not a constant. -/
theorem reduceNat_bin_nc {F d : Nat} {f a b : Expr}
    (h : ∀ n us, f ≠ .const n us) :
    ConLeche.reduceNatFueled mode env F d (.app (.app f a) b) = .ok none :=
  reduceNatFueled_none_of
    (fun c a' h' => by simp at h')
    (fun c a' b' h' => by simp only [Expr.app.injEq] at h'; exact h c [] h'.1.1)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a unary
application whose head is neither a constant nor an application. -/
theorem reduceNat_un_ncna {F d : Nat} {f a : Expr}
    (hnc : ∀ n us, f ≠ .const n us) (hna : ∀ g a, f ≠ .app g a) :
    ConLeche.reduceNatFueled mode env F d (.app f a) = .ok none :=
  reduceNatFueled_none_of
    (fun c a' h' => by simp only [Expr.app.injEq] at h'; exact hnc c [] h'.1)
    (fun c a' b' h' => by simp only [Expr.app.injEq] at h'; exact hna _ _ h'.1)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — not an
application at all. -/
theorem reduceNat_na {F d : Nat} {x : Expr} (h : ∀ f a, x ≠ .app f a) :
    ConLeche.reduceNatFueled mode env F d x = .ok none :=
  reduceNatFueled_none_of (fun _ _ h' => h _ _ h') (fun _ _ _ h' => h _ _ h')

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — `Nat.succ`
FIRES on a literal. -/
theorem simOOp_succ_some {F d n : Nat} {a w : Expr}
    {st : EStore} {r : EIdx}
    (hs : ConLeche.natLitSupported env = true)
    (hw : ConLeche.whnf mode env F d a = .ok w) (hr : some n = ConLeche.rawNatLit? w)
    (hx : denoteE st r = denoteEView st (.lit (.natVal (n + 1)))) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.const ConLeche.natSuccName []) a)) d st (some r) := by
  refine ⟨some (.lit (.natVal (n + 1))), ?_, ?_, F, ?_⟩
  · simp only [denoteEO, hx, denoteEView, Option.map_some]
  · intro y hy; cases hy; simp [Expr.WScoped]
  · dsimp only; rw [reduceNatFueled_succ ⟨rfl, hs⟩ hw, ← hr]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — `Nat.succ` on
a non-literal. -/
theorem simOOp_succ_none {F d : Nat} {a w : Expr} {st : EStore}
    (hs : ConLeche.natLitSupported env = true)
    (hw : ConLeche.whnf mode env F d a = .ok w) (hr : none = ConLeche.rawNatLit? w) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.const ConLeche.natSuccName []) a)) d st none :=
  simOOp_none F (by rw [reduceNatFueled_succ ⟨rfl, hs⟩ hw, ← hr]; rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the certified
binary operation FIRES. -/
theorem simOOp_bin_fire {F₁ F₂ d n₁ n₂ : Nat} {nm : ConLeche.Name}
    {a b w₁ w₂ : Expr} {st : EStore} {r : Option EIdx}
    (hb : NatBinOp nm) (hs : ConLeche.natOpStored env nm = true)
    (hw₁ : ConLeche.whnf mode env F₁ d a = .ok w₁)
    (hr₁ : some n₁ = ConLeche.rawNatLit? w₁)
    (hw₂ : ConLeche.whnf mode env F₂ d b = .ok w₂)
    (hr₂ : some n₂ = ConLeche.rawNatLit? w₂)
    (hres : denoteEO st r = some (ConLeche.natOpResult nm n₁ n₂)) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.app (.const nm []) a) b)) d st r := by
  refine ⟨_, hres, fun y hy => natOpResult_wscoped hy, F₁ + F₂, ?_⟩
  dsimp only
  rw [reduceNatFueled_bin ⟨hb, hs⟩ (ConLeche.whnf_mono (by omega) hw₁), ← hr₁]
  simp only [bind, Except.bind, ConLeche.whnf_mono (by omega : F₂ ≤ F₁ + F₂) hw₂,
    ← hr₂]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the second
argument is not a literal. -/
theorem simOOp_bin_snd {F₁ F₂ d n₁ : Nat} {nm : ConLeche.Name}
    {a b w₁ w₂ : Expr} {st : EStore}
    (hb : NatBinOp nm) (hs : ConLeche.natOpStored env nm = true)
    (hw₁ : ConLeche.whnf mode env F₁ d a = .ok w₁)
    (hr₁ : some n₁ = ConLeche.rawNatLit? w₁)
    (hw₂ : ConLeche.whnf mode env F₂ d b = .ok w₂)
    (hr₂ : none = ConLeche.rawNatLit? w₂) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.app (.const nm []) a) b)) d st none := by
  refine simOOp_none (F₁ + F₂) ?_
  rw [reduceNatFueled_bin ⟨hb, hs⟩ (ConLeche.whnf_mono (by omega) hw₁), ← hr₁]
  simp only [bind, Except.bind, ConLeche.whnf_mono (by omega : F₂ ≤ F₁ + F₂) hw₂,
    ← hr₂]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the first
argument is not a literal. -/
theorem simOOp_bin_fst {F₁ d : Nat} {nm : ConLeche.Name} {a b w₁ : Expr}
    {st : EStore}
    (hb : NatBinOp nm) (hs : ConLeche.natOpStored env nm = true)
    (hw₁ : ConLeche.whnf mode env F₁ d a = .ok w₁)
    (hr₁ : none = ConLeche.rawNatLit? w₁) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.app (.const nm []) a) b)) d st none :=
  simOOp_none F₁ (by rw [reduceNatFueled_bin ⟨hb, hs⟩ hw₁, ← hr₁]; rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the safety
net: the second argument is not a literal. -/
theorem simOOp_wf_snd {F₁ F₂ d n₁ : Nat} {nm : ConLeche.Name}
    {a b w₁ w₂ : Expr} {st : EStore}
    (hg : ¬ (NatBinOp nm ∧ ConLeche.natOpStored env nm = true))
    (hc : ConLeche.natOpWfNames.contains nm = true)
    (hs : ConLeche.natLitSupported env = true)
    (hw₁ : ConLeche.whnf mode env F₁ d a = .ok w₁)
    (hr₁ : some n₁ = ConLeche.rawNatLit? w₁)
    (hw₂ : ConLeche.whnf mode env F₂ d b = .ok w₂)
    (hr₂ : none = ConLeche.rawNatLit? w₂) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.app (.const nm []) a) b)) d st none := by
  refine simOOp_none (F₁ + F₂) ?_
  rw [reduceNatFueled_wf hg ⟨hc, hs⟩ (ConLeche.whnf_mono (by omega) hw₁), ← hr₁]
  simp only [bind, Except.bind, ConLeche.whnf_mono (by omega : F₂ ≤ F₁ + F₂) hw₂,
    ← hr₂]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the safety
net: the first argument is not a literal. -/
theorem simOOp_wf_fst {F₁ d : Nat} {nm : ConLeche.Name} {a b w₁ : Expr}
    {st : EStore}
    (hg : ¬ (NatBinOp nm ∧ ConLeche.natOpStored env nm = true))
    (hc : ConLeche.natOpWfNames.contains nm = true)
    (hs : ConLeche.natLitSupported env = true)
    (hw₁ : ConLeche.whnf mode env F₁ d a = .ok w₁)
    (hr₁ : none = ConLeche.rawNatLit? w₁) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.app (.const nm []) a) b)) d st none :=
  simOOp_none F₁ (by rw [reduceNatFueled_wf hg ⟨hc, hs⟩ hw₁, ← hr₁]; rfl)

/-! ## 6. `reduceNat` -/

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **THEOREM 1 for
`reduceNat`**: the literal acceleration, run in the `whnf` loop before
delta-unfolding.  **CLOSED** (round 4; moved here from `Walks/Owed.lean`,
statement unchanged).  The divergence audit's D15 is preserved by the twin —
the FIRST argument is head-normalised and, unless it is a literal, the step
declines without touching the second — so the two call sequences agree and
the proof is a straight walk: fifty verification conditions, one per exit
and per callee precondition. -/
theorem reduceNat_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (e : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store e = some x →
          SimOOp (fun F => ConLeche.reduceNatFueled mode env F d x) d
            s'.store r; ⊤⦄ := by
  obtain ⟨x, hden, hwx⟩ := hdw
  have hp := hok.pins
  have hwf := hok.state.wf
  have hwh := hsim.whnf'
  have hraw := rawNatLit?_spec' (mode := mode) (env := env) (fe := fe)
  have hlit := natLitSupported_spec (mode := mode) (env := env) (fe := fe)
  have hbin := natBinOpName_spec' (mode := mode) (env := env) (fe := fe)
  have hsto := natOpStored_spec' (mode := mode) (env := env) (fe := fe)
  have hwfn := natOpWfNames_spec (mode := mode) (env := env) (fe := fe)
  have hres := natOpResult_spec' (mode := mode) (env := env) (fe := fe)
  vcgen [ConRon.Arena.reduceNat, ConRon.Arena.emptyLevels,
    ConRon.Arena.pinNatSucc, hwh, hraw, hlit, hbin, hsto, hwfn, hres]
  all_goals (bridge_peel; subst_vars)
  -- the twin's two tag tests (task #97-P5-Core round 4) add a hypothesis to
  -- every `then` arm that no arm's proof needs; clear them so the contexts are
  -- the view-first twin's again (the two new `else` arms are vc47 and vc50)
  all_goals clear_tag_hyps
  bridge_frame [viewOK_lit]
  bridge_fwd [denote_not_const, denote_not_const_of_tag, denote_not_app,
    denote_not_app_of_tag, levels_nil, levels_ne, succ_guard, succ_guard_no,
    bin_guard, bin_guard_no, wf_guard, wf_guard_no]
  bridge_frame [viewOK_lit]
  -- a constant WITH universe levels: no operation
  vc_arm (hd : denoteE _ e = some (.app (.const _ ?ls) _)) (h : ?ls ≠ []) =>
    exact simOOp_none 0 (reduceNat_unary_levels h)
  vc_arm (hd : denoteE _ e = some (.app (.app (.const _ ?ls) _) _)) (h : ?ls ≠ []) =>
    exact simOOp_none 0 (reduceNat_binary_levels h)
  -- `Nat.succ`: the guard declines, the argument is a literal, or it is not
  vc_arm (hng : ¬ (_ = ConLeche.natSuccName ∧ _)) =>
    exact simOOp_none 0 (reduceNatFueled_succ_no hng)
  vc_arm (hs : ConLeche.natLitSupported _ = true) (hw : ConLeche.whnf _ _ _ _ _ = .ok ?w)
      (hr : some _ = ConLeche.rawNatLit? ?w) (hx : denoteE _ _ = denoteEView _ (.lit _)) =>
    exact simOOp_succ_some hs hw hr hx
  vc_arm (hd : denoteE _ e = some (.app (.const _ _) _))
      (hs : ConLeche.natLitSupported _ = true) (hw : ConLeche.whnf _ _ _ _ _ = .ok ?w)
      (hr : none = ConLeche.rawNatLit? ?w) =>
    exact simOOp_succ_none hs hw hr
  -- the certified binary operation: fires, or the second or the first
  -- argument is not a literal
  vc_arm (hd : denoteE _ e = some (.app (.app (.const _ _) ?a) ?b)) (hb : NatBinOp _) (hs : ConLeche.natOpStored _ _ = true)
      (hw₁ : ConLeche.whnf _ _ _ _ ?a = .ok ?w₁) (hr₁ : some _ = ConLeche.rawNatLit? ?w₁)
      (hw₂ : ConLeche.whnf _ _ _ _ ?b = .ok ?w₂) (hr₂ : some _ = ConLeche.rawNatLit? ?w₂)
      (hres : denoteEO _ _ = some (ConLeche.natOpResult _ _ _)) =>
    exact simOOp_bin_fire hb hs hw₁ hr₁ hw₂ hr₂ hres
  vc_arm (hd : denoteE _ e = some (.app (.app (.const _ _) ?a) ?b)) (hb : NatBinOp _) (hs : ConLeche.natOpStored _ _ = true)
      (hw₁ : ConLeche.whnf _ _ _ _ ?a = .ok ?w₁) (hr₁ : some _ = ConLeche.rawNatLit? ?w₁)
      (hw₂ : ConLeche.whnf _ _ _ _ ?b = .ok ?w₂) (hr₂ : none = ConLeche.rawNatLit? ?w₂) =>
    exact simOOp_bin_snd hb hs hw₁ hr₁ hw₂ hr₂
  vc_arm (hd : denoteE _ e = some (.app (.app (.const _ _) ?a) _)) (hb : NatBinOp _) (hs : ConLeche.natOpStored _ _ = true)
      (hw₁ : ConLeche.whnf _ _ _ _ ?a = .ok ?w₁) (hr₁ : none = ConLeche.rawNatLit? ?w₁) =>
    exact simOOp_bin_fst hb hs hw₁ hr₁
  -- the WF-pinned safety net: the same two declines, and neither guard
  vc_arm (hd : denoteE _ e = some (.app (.app (.const _ _) ?a) ?b))
      (hg : ¬ (NatBinOp _ ∧ _)) (hc : List.contains _ _ = true) (hs : ConLeche.natLitSupported _ = true)
      (hw₁ : ConLeche.whnf _ _ _ _ ?a = .ok ?w₁) (hr₁ : some _ = ConLeche.rawNatLit? ?w₁)
      (hw₂ : ConLeche.whnf _ _ _ _ ?b = .ok ?w₂) (hr₂ : none = ConLeche.rawNatLit? ?w₂) =>
    exact simOOp_wf_snd hg hc hs hw₁ hr₁ hw₂ hr₂
  vc_arm (hd : denoteE _ e = some (.app (.app (.const _ _) ?a) _))
      (hg : ¬ (NatBinOp _ ∧ _)) (hc : List.contains _ _ = true) (hs : ConLeche.natLitSupported _ = true)
      (hw₁ : ConLeche.whnf _ _ _ _ ?a = .ok ?w₁) (hr₁ : none = ConLeche.rawNatLit? ?w₁) =>
    exact simOOp_wf_fst hg hc hs hw₁ hr₁
  vc_arm (hg : ¬ (NatBinOp _ ∧ _)) (hnw : ¬ (List.contains _ _ = true ∧ _)) =>
    exact simOOp_none 0 (reduceNatFueled_bin_no hg hnw)
  -- the shapes that are not an operation at all
  vc_arm (hd : denoteE _ e = some (.app (.app ?f _) _)) (hnc : ∀ n us, ?f ≠ .const n us) =>
    exact simOOp_none 0 (reduceNat_bin_nc hnc)
  vc_arm (hd : denoteE _ e = some (.app ?f _)) (hnc : ∀ n us, ?f ≠ .const n us)
      (hna : ∀ g a, ?f ≠ .app g a) =>
    exact simOOp_none 0 (reduceNat_un_ncna hnc hna)
  vc_arm (hna : ∀ f a, x ≠ .app f a) =>
    exact simOOp_none 0 (reduceNat_na hna)

/-! ## 7. The axiom census -/

section Census

#print axioms rawNatLit?_spec
#print axioms natBinOpName_spec
#print axioms natOpStored_spec
#print axioms natOpWfNames_spec
#print axioms natOpResult_spec
#print axioms constE_spec
#print axioms natIndOk_spec
#print axioms natZeroOk_spec
#print axioms natSuccOk_spec
#print axioms natLitSupported_spec
#print axioms natOpResult_wscoped
#print axioms reduceNat_spec

end Census

end ConRon.Bridge.Core
