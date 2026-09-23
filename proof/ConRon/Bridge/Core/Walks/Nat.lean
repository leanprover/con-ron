/-
# `ConRon.Bridge.Core.Walks.Nat` — the literal acceleration, `reduceNat`

Task #97-P3-Core round 4.  `Bridge/Core/Arms/Whnf.lean`'s `whnfBody_spec`
inherited `sorryAx` from exactly one walk after this round closed
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

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Index equality is value equality, at the three stores -/

/-- con-leche: none — DESIGN §8.3 at the expression store. -/
theorem beq_of_denoteE {st : EStore} (hwf : StoreWF st) {i j : EIdx}
    {x y : Expr} (hi : denoteE st i = some x) (hj : denoteE st j = some y) :
    (i == j) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; rw [hi] at hj; exact Option.some.inj hj
  · rintro rfl; exact denoteE_inj hwf hi hj

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
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; rfl
  | forallE ty b m =>
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
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.rawNatLit? h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = ConLeche.rawNatLit? x⌝⦄ := by
  have hp := hok.pins
  obtain ⟨rk, hrk⟩ := hok.state.wf
  mvcgen [ConRon.Arena.rawNatLit?, ConRon.Arena.emptyLevels,
    ConRon.Arena.pinNatZero]
  all_goals (bridge_peel; subst_vars)
  case vc1 =>
    rename_i n _ hview
    refine ⟨rfl, ?_⟩
    rw [denote_lit_inv hok.state.wf hview hden]; rfl
  case vc2.hp => exact hp
  case vc3.hp => exact hp
  case vc4 =>
    rename_i c us el nz _ hnz hel hview
    refine ⟨rfl, ?_⟩
    obtain ⟨nm, ls, rfl, hn, hls⟩ := denote_const_inv hok.state.wf hview hden
    rw [beq_of_denoteN hrk.nsWF hn (hnz _ rfl), beq_of_denoteLs hrk.lss hls hel]
    cases ls with
    | nil =>
      simp only [ConLeche.rawNatLit?]
      by_cases hz : nm = ConLeche.natZeroName <;> simp [hz]
    | cons l ls => simp [ConLeche.rawNatLit?]
  case vc5 =>
    rename_i _ hnl hnc _ hview
    exact ⟨rfl, (rawNatLit?_of_view hok.state.wf hview hden hnl hnc).symm⟩

/-! ## 3. The name tests -/

/-- con-leche: none — a pinned name handle against a denoted one: the `==`
of the twin is con-leche's `==` of the names. -/
theorem pinBeq {st : EStore} (hwf : StoreWF st) {c n : NIdx}
    {nm y : ConLeche.Name} (hn : denoteN st.ns c = some nm)
    (hy : denoteN st.ns n = some y) : (c == n) = (nm == y) := by
  obtain ⟨rk, hrk⟩ := hwf
  exact beq_of_denoteN hrk.nsWF hn hy

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **THEOREM 1 for
`natBinOpName`**: the binary literal acceleration's fourteen-way name test is
con-leche's disjunction. -/
theorem natBinOpName_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natBinOpName c
    ⦃⇓? b s' => ⌜s' = s₀ ∧ (b = true ↔
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
        nm = ConLeche.natShiftRightName))⌝⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  mvcgen [ConRon.Arena.natBinOpName, ConRon.Arena.natAddName, ConRon.Arena.pinNatAdd, ConRon.Arena.natSubName, ConRon.Arena.pinNatSub, ConRon.Arena.natMulName, ConRon.Arena.pinNatMul, ConRon.Arena.natPowName, ConRon.Arena.pinNatPow, ConRon.Arena.natBeqName, ConRon.Arena.pinNatBeq, ConRon.Arena.natBleName, ConRon.Arena.pinNatBle, ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv, ConRon.Arena.natModName, ConRon.Arena.pinNatMod, ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd, ConRon.Arena.natLandName, ConRon.Arena.pinNatLand, ConRon.Arena.natLorName, ConRon.Arena.pinNatLor, ConRon.Arena.natXorName, ConRon.Arena.pinNatXor, ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft, ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight]
  all_goals (bridge_peel; subst_vars)
  all_goals first | exact hp | skip
  refine ⟨rfl, ?_⟩
  have pinBeq := fun {n : NIdx} {y : ConLeche.Name} => @pinBeq _ hwf c n nm y
  rw [pinBeq hn (‹∀ x, pinNames[PIN_NAT_ADD]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_SUB]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_MUL]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_POW]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_BEQ]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_BLE]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_DIV]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_MOD]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_GCD]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_LAND]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_LOR]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_XOR]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_SHIFT_LEFT]? = some x → denoteN _ _ = some x› _ rfl),
      pinBeq hn (‹∀ x, pinNames[PIN_NAT_SHIFT_RIGHT]? = some x → denoteN _ _ = some x› _ rfl)]
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]
  exact Iff.rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored — **THEOREM 1
for `natOpStored`**: is the operation stored as a definition. -/
theorem natOpStored_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natOpStored fe c
    ⦃⇓? b s' => ⌜s' = s₀ ∧ b = ConLeche.natOpStored env nm⌝⦄ := by
  mvcgen [ConRon.Arena.natOpStored]
  all_goals (bridge_peel; subst_vars)
  · rename_i icv v hint hfd _
    obtain ⟨_, _, _, _, hfind⟩ := env_defn_of_index hok hn hfd
    refine ⟨rfl, ?_⟩
    simp only [ConLeche.natOpStored, hfind]
  · rename_i hnd
    refine ⟨rfl, ?_⟩
    have h := env_not_defn_of_index hok hn (fun a b c' h => hnd a b c' h)
    simp only [ConLeche.natOpStored]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:602-612 natOpWfNames — **THEOREM
1 for `natOpWfNames`**: the eight pinned handles answer con-leche's
membership test at every denoted name. -/
theorem natOpWfNames_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natOpWfNames
    ⦃⇓? ws s' => ⌜s' = s₀ ∧ ∀ c nm, denoteN s₀.store.ns c = some nm →
        ws.contains c = ConLeche.natOpWfNames.contains nm⌝⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  mvcgen [ConRon.Arena.natOpWfNames, ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv, ConRon.Arena.natModName, ConRon.Arena.pinNatMod, ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd, ConRon.Arena.natLandName, ConRon.Arena.pinNatLand, ConRon.Arena.natLorName, ConRon.Arena.pinNatLor, ConRon.Arena.natXorName, ConRon.Arena.pinNatXor, ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft, ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight]
  all_goals (bridge_peel; subst_vars)
  all_goals first | exact hp | skip
  refine ⟨rfl, fun c nm hn => ?_⟩
  simp only [List.contains_cons, List.contains_nil, Bool.or_false,
    ConLeche.natOpWfNames]
  rw [pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_DIV]? = some x → denoteN _ _ = some x› _ rfl),
    pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_MOD]? = some x → denoteN _ _ = some x› _ rfl),
    pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_GCD]? = some x → denoteN _ _ = some x› _ rfl),
    pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_LAND]? = some x → denoteN _ _ = some x› _ rfl),
    pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_LOR]? = some x → denoteN _ _ = some x› _ rfl),
    pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_XOR]? = some x → denoteN _ _ = some x› _ rfl),
    pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_LEFT]? = some x → denoteN _ _ = some x› _ rfl),
    pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_RIGHT]? = some x → denoteN _ _ = some x› _ rfl)]
  rfl

/-! ## 4. `natOpResult` -/

set_option hygiene false in
/-- con-leche: none — the fifteen name tests of `natOpResult`'s chain, turned
into con-leche's `Name` tests at one arm. -/
local macro "nat_tests" : tactic => `(tactic| (
   have e0 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_PRED]? = some x → denoteN _ _ = some x› _ rfl)
   have e1 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_ADD]? = some x → denoteN _ _ = some x› _ rfl)
   have e2 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_SUB]? = some x → denoteN _ _ = some x› _ rfl)
   have e3 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_MUL]? = some x → denoteN _ _ = some x› _ rfl)
   have e4 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_POW]? = some x → denoteN _ _ = some x› _ rfl)
   have e5 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_BEQ]? = some x → denoteN _ _ = some x› _ rfl)
   have e6 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_BLE]? = some x → denoteN _ _ = some x› _ rfl)
   have e7 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_DIV]? = some x → denoteN _ _ = some x› _ rfl)
   have e8 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_MOD]? = some x → denoteN _ _ = some x› _ rfl)
   have e9 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_GCD]? = some x → denoteN _ _ = some x› _ rfl)
   have e10 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_LAND]? = some x → denoteN _ _ = some x› _ rfl)
   have e11 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_LOR]? = some x → denoteN _ _ = some x› _ rfl)
   have e12 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_XOR]? = some x → denoteN _ _ = some x› _ rfl)
   have e13 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_LEFT]? = some x → denoteN _ _ = some x› _ rfl)
   have e14 := pinBeq hwf hn (‹∀ x, pinNames[PIN_NAT_SHIFT_RIGHT]? = some x → denoteN _ _ = some x› _ rfl)
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
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natOpResult c a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteEO s'.store r = some (ConLeche.natOpResult nm a b)⌝⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  mvcgen [ConRon.Arena.natOpResult, ConRon.Arena.natPredName, ConRon.Arena.pinNatPred, ConRon.Arena.natAddName, ConRon.Arena.pinNatAdd, ConRon.Arena.natSubName, ConRon.Arena.pinNatSub, ConRon.Arena.natMulName, ConRon.Arena.pinNatMul, ConRon.Arena.natPowName, ConRon.Arena.pinNatPow, ConRon.Arena.natBeqName, ConRon.Arena.pinNatBeq, ConRon.Arena.natBleName, ConRon.Arena.pinNatBle, ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv, ConRon.Arena.natModName, ConRon.Arena.pinNatMod, ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd, ConRon.Arena.natLandName, ConRon.Arena.pinNatLand, ConRon.Arena.natLorName, ConRon.Arena.pinNatLor, ConRon.Arena.natXorName, ConRon.Arena.pinNatXor, ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft, ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight, ConRon.Arena.constE,
    ConRon.Arena.emptyLevels, ConRon.Arena.boolTrueName,
    ConRon.Arena.boolFalseName, ConRon.Arena.pinBoolTrue,
    ConRon.Arena.pinBoolFalse]
  all_goals (bridge_peel; subst_vars)
  all_goals first
    | exact hp
    | exact hwf
    | exact viewOK_lit
    | (intro s hs _; subst hs; exact hwf)
    | (intro s hs hel; subst hs
       obtain ⟨w, hw, _⟩ := denoteLs_view hel
       exact viewOK_const (nview_isSome_of_denote
         (‹∀ x, pinNames[PIN_BOOL_TRUE]? = some x → denoteN _ _ = some x› _ rfl))
         (by rw [hw]; rfl))
    | (intro s hs hel; subst hs
       obtain ⟨w, hw, _⟩ := denoteLs_view hel
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
       · rename_i heq1 heq2; cases h; simp
       · simp at h)

/-- con-leche: none — the same at a constructor. -/
theorem denoteCI_ctor_iff {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) :
    (∃ v nP nF, ci = .ctorInfo v nP nF) ↔ ∃ cv nP nF, c = .ctorInfo cv nP nF := by
  cases ci <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; simp)
    | (split at h
       · rename_i heq1 heq2; cases h; simp
       · simp at h)

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
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natIndOk oc
    ⦃⇓? b s' => ⌜s' = s₀ ∧ b = ConLeche.natIndOk oc'⌝⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.natIndOk]
    all_goals (bridge_peel; subst_vars; exact ⟨rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    cases ci
    case indInfo v caps =>
      simp only [Frontend.denoteCI] at hci
      split at hci
      · rename_i cv caps' hcv _hcaps
        cases hci
        obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
        mvcgen [ConRon.Arena.natIndOk, ConRon.Arena.sortOne]
        all_goals (bridge_peel; subst_vars)
        · exact hp
        · rename_i hs1
          refine ⟨rfl, ?_⟩
          simp only [ConLeche.natIndOk, isEmpty_of_denoteNList hlps,
            beq_of_denoteE hwf hty hs1]
      · simp at hci
    all_goals
      (have hn : ¬ ∃ cv caps, c = .indInfo cv caps := fun h' => by
         obtain ⟨v, caps, hv⟩ := (denoteCI_ind_iff hci).mpr h'; cases hv
       mvcgen [ConRon.Arena.natIndOk]
       bridge_peel; subst_vars
       refine ⟨rfl, ?_⟩
       cases c <;> simp_all [ConLeche.natIndOk])

/-- con-leche: none — **THEOREM 1 for `constE`**: the level-monomorphic
constant at a denoted name. -/
theorem constE_spec (s₀ : AState) (n : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns n = some nm) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.constE n
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = some (.const nm [])⌝⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  mvcgen [ConRon.Arena.constE, ConRon.Arena.emptyLevels]
  all_goals (bridge_peel; subst_vars)
  case vc1.hp => exact hp
  case vc2 =>
    rename_i hel
    intro hwf' hx _ _ hc hp' _ _ _ hd
    refine ⟨hok.mono ⟨hwf'⟩ hx hc hp', hx, hp', ?_⟩
    rw [hd]
    simp only [denoteEView, denoteN_ext hn hx, denoteLs_ext hel hx, opt2]
  case vc3 => intro s hs _; subst hs; exact hwf
  case vc4 =>
    intro s hs hel; subst hs
    obtain ⟨w, hw, _⟩ := denoteLs_view hel
    exact viewOK_const (nview_isSome_of_denote hn) (by rw [hw]; rfl)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk — **THEOREM 1
for `natZeroOk`**. -/
theorem natZeroOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natZeroOk oc
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natZeroOk oc'⌝⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.natZeroOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    cases ci
    case ctorInfo v nP nF =>
      obtain ⟨cv, hcv, rfl⟩ := denoteCI_ctorInfo_inv hci
      obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
      have hce := fun (s : AState) (n : NIdx) =>
        constE_spec (mode := mode) (env := env) (fe := fe) s n ConLeche.natName
      mvcgen [ConRon.Arena.natZeroOk, ConRon.Arena.pinNat, hce]
      all_goals (bridge_peel; subst_vars)
      · exact hp
      · exact hok
      · rename_i hnt; exact hnt _ rfl
      · rename_i hck hx hp' hd _
        refine ⟨hck, hx, hp', ?_⟩
        simp only [ConLeche.natZeroOk, isEmpty_of_denoteNList hlps,
          beq_of_denoteE hck.state.wf (denote_ext hty hx) hd]
    all_goals
      (have hn : ¬ ∃ cv nP nF, c = .ctorInfo cv nP nF := fun h' => by
         obtain ⟨v, nP, nF, hv⟩ := (denoteCI_ctor_iff hci).mpr h'; cases hv
       mvcgen [ConRon.Arena.natZeroOk]
       all_goals (bridge_peel; subst_vars)
       refine ⟨hok, Ext.refl _, rfl, ?_⟩
       cases c <;> simp_all [ConLeche.natZeroOk])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — **THEOREM 1
for `natSuccOk`**. -/
theorem natSuccOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natSuccOk oc
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natSuccOk oc'⌝⦄ := by
  have hp := hok.pins
  have hwf := hok.state.wf
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.natSuccOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    cases ci
    case ctorInfo v nP nF =>
      obtain ⟨cv, hcv, rfl⟩ := denoteCI_ctorInfo_inv hci
      obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
      have hce := fun (s : AState) (n : NIdx) =>
        constE_spec (mode := mode) (env := env) (fe := fe) s n ConLeche.natName
      mvcgen [ConRon.Arena.natSuccOk, ConRon.Arena.pinNat, hce]
      all_goals (bridge_peel; subst_vars)
      all_goals clear_tag_hyps
      case vc1.isTrue =>
        rename_i hne _
        refine ⟨hok, Ext.refl _, rfl, ?_⟩
        rw [isEmpty_of_denoteNList hlps] at hne
        simp only [Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true] at hne
        simp only [ConLeche.natSuccOk, hne, Bool.false_and]
      case vc2.hp => exact hp
      case vc3.hok => exact hok
      case vc4.hn => rename_i hnt; exact hnt _ rfl
      case vc5 =>
        rename_i hne _ _ _ _ _ _ _ _ hck hview hx hp' hd
        refine ⟨hck, hx, hp', ?_⟩
        rw [isEmpty_of_denoteNList hlps] at hne
        obtain ⟨p, q, hpq, hp1, hq1⟩ :=
          denote_forallE_inv hck.state.wf hview (denote_ext hty hx)
        simp only [ConLeche.natSuccOk, hpq,
          beq_of_denoteE hck.state.wf hp1 hd, beq_of_denoteE hck.state.wf hq1 hd]
        have hle : cv.levelParams.isEmpty = true := by simpa using hne
        rw [hle, Bool.true_and]
        split
        · rename_i c1 c2 mb heq
          simp only [Expr.forallE.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          rw [Bool.eq_iff_iff]; simp
        · rename_i hne'
          by_cases hp : p = .const ConLeche.natName []
          · by_cases hq : q = .const ConLeche.natName []
            · subst hp hq; exact absurd rfl (hne' _ _ _)
            · simp [hq]
          · simp [hp]
      case vc6 =>
        rename_i hne _ _ _ _ hnf _ _ hck hview hx hp' _
        refine ⟨hck, hx, hp', ?_⟩
        have hnot := denote_not_forallE hck.state.wf hview (denote_ext hty hx) hnf
        simp only [ConLeche.natSuccOk]
        split
        · rename_i heq; exact absurd heq (hnot _ _ _)
        · simp
      -- the type does not carry the `forallE` TAG (round 4's tag-first arm)
      case vc7 =>
        rename_i hne _ _ _ htg _ hck hx hp' _ _
        refine ⟨hck, hx, hp', ?_⟩
        have hty' := denote_ext hty hx
        obtain ⟨vt, hview⟩ := denoteE_view hty'
        have hnot := denote_not_forallE hck.state.wf hview hty'
          (fun ty b m hh => view_tagOf_ne hview (t := ETag.forallE) htg
            (by rw [hh]; rfl))
        simp only [ConLeche.natSuccOk]
        split
        · rename_i heq; exact absurd heq (hnot _ _ _)
        · simp
    all_goals
      (have hn : ¬ ∃ cv nP nF, c = .ctorInfo cv nP nF := fun h' => by
         obtain ⟨v, nP, nF, hv⟩ := (denoteCI_ctor_iff hci).mpr h'; cases hv
       mvcgen [ConRon.Arena.natSuccOk]
       all_goals (bridge_peel; subst_vars)
       refine ⟨hok, Ext.refl _, rfl, ?_⟩
       cases c <;> simp_all [ConLeche.natSuccOk])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:225-233 natLitSupported —
**THEOREM 1 for `natLitSupported`**: the three stored-declaration shapes. -/
theorem natLitSupported_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natLitSupported fe
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natLitSupported env⌝⦄ := by
  have hp := hok.pins
  have hi := fun (s : AState) (oc : Option IConstantInfo) =>
    natIndOk_spec (mode := mode) (env := env) (fe := fe) s oc (env.find? ConLeche.natName)
  have hz := fun (s : AState) (oc : Option IConstantInfo) =>
    natZeroOk_spec (mode := mode) (env := env) (fe := fe) s oc (env.find? ConLeche.natZeroName)
  have hs := fun (s : AState) (oc : Option IConstantInfo) =>
    natSuccOk_spec (mode := mode) (env := env) (fe := fe) s oc (env.find? ConLeche.natSuccName)
  mvcgen [ConRon.Arena.natLitSupported, ConRon.Arena.pinNat,
    ConRon.Arena.pinNatZero, ConRon.Arena.pinNatSucc, hi, hz, hs]
  all_goals (bridge_peel; subst_vars)
  all_goals first
    | exact hp
    | exact hok
    | (apply CheckOK.pins; assumption)
    | (exact optCI_find hok
        (‹∀ x, pinNames[PIN_NAT]? = some x → denoteN _ _ = some x› _ rfl))
    | (exact optCI_find (by assumption)
        (‹∀ x, pinNames[PIN_NAT_ZERO]? = some x → denoteN _ _ = some x› _ rfl))
    | (intro s hs _; subst hs; assumption)
    | (intro s hs hsucc; subst hs
       exact optCI_find (by assumption) (hsucc _ rfl))
    | skip
  -- the three declines and the conjunction
  case vc4 =>
    rename_i hni
    refine ⟨hok, Ext.refl _, rfl, ?_⟩
    simp_all [ConLeche.natLitSupported]
  case vc8 =>
    rename_i hck hx hp' _ _ _ hnz
    refine ⟨hck, hx, hp', ?_⟩
    simp_all [ConLeche.natLitSupported]
  case vc10 =>
    rename_i _ _ _ _ _ _ _ hni _ _ hnz hck1 _ hx01 hp10
    intro hck hx12 hp21 hr
    refine ⟨hck, hx01.trans hx12, hp21.trans hp10, ?_⟩
    subst hr
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
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.rawNatLit? h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        r = ConLeche.rawNatLit? x⌝⦄ := by
  obtain ⟨x, hx⟩ := hpre
  have hb := rawNatLit?_spec s₀ h x hok hx
  mvcgen [hb]
  intro h1 h2
  exact ⟨h1, fun y hy => by rw [hx] at hy; cases hy; exact h2⟩

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — `natBinOpName`
in answer shape. -/
theorem natBinOpName_spec' (s₀ : AState) (c : NIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm, denoteN s₀.store.ns c = some nm) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natBinOpName c
    ⦃⇓? b s' => ⌜s' = s₀ ∧ ∀ nm, denoteN s₀.store.ns c = some nm →
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
          nm = ConLeche.natShiftRightName))⌝⦄ := by
  obtain ⟨nm, hn⟩ := hpre
  have hb := natBinOpName_spec s₀ c nm hok hn
  mvcgen [hb]
  intro h1 h2
  exact ⟨h1, fun y hy => by rw [hn] at hy; cases hy; exact h2⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored — answer
shape. -/
theorem natOpStored_spec' (s₀ : AState) (c : NIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm, denoteN s₀.store.ns c = some nm) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natOpStored fe c
    ⦃⇓? b s' => ⌜s' = s₀ ∧ ∀ nm, denoteN s₀.store.ns c = some nm →
        b = ConLeche.natOpStored env nm⌝⦄ := by
  obtain ⟨nm, hn⟩ := hpre
  have hb := natOpStored_spec s₀ c nm hok hn
  mvcgen [hb]
  intro h1 h2
  exact ⟨h1, fun y hy => by rw [hn] at hy; cases hy; exact h2⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult — answer
shape. -/
theorem natOpResult_spec' (s₀ : AState) (c : NIdx) (a b : Nat)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm, denoteN s₀.store.ns c = some nm) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natOpResult c a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ nm, denoteN s₀.store.ns c = some nm →
        denoteEO s'.store r = some (ConLeche.natOpResult nm a b)⌝⦄ := by
  obtain ⟨nm, hn⟩ := hpre
  have hb := natOpResult_spec s₀ c nm a b hok hn
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, fun y hy => by rw [hn] at hy; cases hy; exact h4⟩

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
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, if_pos hg, e1, bind,
    Except.bind]
  cases ConLeche.rawNatLit? w <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the unary guard
declines. -/
theorem reduceNatFueled_succ_no {F d : Nat} {c : ConLeche.Name} {a : Expr}
    (hg : ¬ (c = ConLeche.natSuccName ∧ ConLeche.natLitSupported env = true)) :
    ConLeche.reduceNatFueled mode env F d (.app (.const c []) a) = .ok none := by
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, if_neg hg]; rfl

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
  rw [if_pos hg]
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
  rw [if_neg hg, if_pos hw]
  simp only [e1, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — neither guard. -/
theorem reduceNatFueled_bin_no {F d : Nat} {c : ConLeche.Name} {a b : Expr}
    (hg : ¬ (NatBinOp c ∧ ConLeche.natOpStored env c = true))
    (hw : ¬ (ConLeche.natOpWfNames.contains c ∧ ConLeche.natLitSupported env = true)) :
    ConLeche.reduceNatFueled mode env F d (.app (.app (.const c []) a) b) =
      .ok none := by
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, NatBinOp] at hg ⊢
  rw [if_neg hg, if_neg hw]; rfl

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
  · rw [if_pos h0] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h0] at h
  by_cases h1 : c = ConLeche.natAddName
  · rw [if_pos h1] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h1] at h
  by_cases h2 : c = ConLeche.natSubName
  · rw [if_pos h2] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h2] at h
  by_cases h3 : c = ConLeche.natMulName
  · rw [if_pos h3] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h3] at h
  by_cases h4 : c = ConLeche.natPowName
  · rw [if_pos h4] at h
    by_cases hb : b > 16777216
    · rw [if_pos hb] at h; cases h
    · rw [if_neg hb] at h; cases h; simp [Expr.WScoped]
  rw [if_neg h4] at h
  by_cases h5 : c = ConLeche.natDivName
  · rw [if_pos h5] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h5] at h
  by_cases h6 : c = ConLeche.natModName
  · rw [if_pos h6] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h6] at h
  by_cases h7 : c = ConLeche.natGcdName
  · rw [if_pos h7] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h7] at h
  by_cases h8 : c = ConLeche.natLandName
  · rw [if_pos h8] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h8] at h
  by_cases h9 : c = ConLeche.natLorName
  · rw [if_pos h9] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h9] at h
  by_cases h10 : c = ConLeche.natXorName
  · rw [if_pos h10] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h10] at h
  by_cases h11 : c = ConLeche.natShiftLeftName
  · rw [if_pos h11] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h11] at h
  by_cases h12 : c = ConLeche.natShiftRightName
  · rw [if_pos h12] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h12] at h
  by_cases h13 : c = ConLeche.natBeqName
  · rw [if_pos h13] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h13] at h
  by_cases h14 : c = ConLeche.natBleName
  · rw [if_pos h14] at h
    cases h; simp [Expr.WScoped]
  rw [if_neg h14] at h
  cases h

/-- con-leche: none — `CheckOK`'s two projections the precondition goals
of `reduceNat` ask for. -/
theorem CheckOK.wf' {s : AState} (h : CheckOK mode env fe s) : StoreWF s.store :=
  h.state.wf

theorem CheckOK.readN' {s : AState} (h : CheckOK mode env fe s) :
    ReadNCacheOK s.caches.readNC s.store := h.caches.readN

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
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store e = some x →
          SimOOp (fun F => ConLeche.reduceNatFueled mode env F d x) d
            s'.store r⌝⦄ := by
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
  mvcgen [ConRon.Arena.reduceNat, ConRon.Arena.emptyLevels,
    ConRon.Arena.pinNatSucc, hwh, hraw, hlit, hbin, hsto, hwfn, hres]
  all_goals (bridge_peel; subst_vars)
  -- the twin's two tag tests (task #97-P5-Core round 4) add a hypothesis to
  -- every `then` arm that no arm's proof needs; clear them so the contexts are
  -- the view-first twin's again (the two new `else` arms are vc48 and vc51)
  all_goals clear_tag_hyps
  -- the plain preconditions
  all_goals first
    | exact hp
    | assumption
    | exact viewOK_lit
    | (apply CheckOK.wf'; assumption)
    | (apply CheckOK.readN'; assumption)
    | (intro h; exact h.elim)
    | (intro s hs _; subst hs; assumption)
    | (apply CheckOK.mono (by assumption) ⟨by assumption⟩ <;> assumption)
    | skip
  -- `Nat.succ`: the level list is not empty
  case vc2 =>
    rename_i _ _ _ _ _ hus s0 hel hvc hve
    obtain ⟨nm, ls, ax, rfl, _, _, hle⟩ := unary_shape hwf hve hvc hden hel
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, 0, reduceNatFueled_none_of ?_ ?_⟩
    · intro c' a' h'
      simp only [Expr.app.injEq, Expr.const.injEq] at h'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h'
      rw [hle] at hus; simp at hus
    · intro c' a' b' h'; simp at h'
  case vc6 =>
    rename_i _ _ _ _ _ hus _ s0 s1 hck1 hx01 hp10 hsucc hel hvc hve hg
    obtain ⟨nm, ls, ax, rfl, _, ha, _⟩ := unary_shape hwf hve hvc hden hel
    simp only [Expr.WScoped, true_and] at hwx
    exact ⟨ax, denote_ext ha hx01, hwx⟩
  case vc8 =>
    rename_i _ _ _ _ _ hus _ s0 s1 _ s2 hck1 hck2 hx01 hx12 hp10 hp21 hwa hsucc hel hvc hve hg
    obtain ⟨nm, ls, ax, rfl, _, ha, _⟩ := unary_shape hwf hve hvc hden hel
    obtain ⟨w, hw, _, _⟩ := hwa ax (denote_ext ha hx01)
    exact ⟨w, hw⟩
  -- `Nat.succ` FIRES
  case vc11 =>
    rename_i _ _ _ _ _ hus _ s0 s1 _ n s2 _ s3 hck1 hwf3 hx01 hx23 hp10 _ _ hc32 hp32 _ _ _ hlit hsucc hel hvc hve hg hck2 hr hx12 hp21 hwa
    obtain ⟨nm, ls, ax, rfl, hn, ha, hle⟩ := unary_shape hwf hve hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    rw [pinBeq hwf hn (hsucc _ rfl)] at hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨w, hw, _, F, hF⟩ := hwa ax (denote_ext ha hx01)
    have hraw := hr w hw
    refine ⟨hck2.mono ⟨hwf3⟩ hx23 hc32 hp32, (hx01.trans hx12).trans hx23,
      by rw [hp32, hp21, hp10], fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨some (.lit (.natVal (n + 1))), ?_, ?_, F, ?_⟩
    · simp only [denoteEO, hlit, denoteEView, Option.map_some]
    · intro y hy; cases hy; simp [Expr.WScoped]
    · dsimp only; rw [reduceNatFueled_succ hg hF, ← hraw]; rfl
  -- `Nat.succ` on a non-literal
  case vc12 =>
    rename_i _ _ _ _ _ hus _ s0 s1 _ s2 hck1 hx01 hp10 hsucc hel hvc hve hg hck2 hr hx12 hp21 hwa
    obtain ⟨nm, ls, ax, rfl, hn, ha, hle⟩ := unary_shape hwf hve hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    rw [pinBeq hwf hn (hsucc _ rfl)] at hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨w, hw, _, F, hF⟩ := hwa ax (denote_ext ha hx01)
    have hraw := hr w hw
    refine ⟨hck2, hx01.trans hx12, by rw [hp21, hp10], fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    exact ⟨none, rfl, by simp, F, by dsimp only; rw [reduceNatFueled_succ hg hF, ← hraw]; rfl⟩
  -- the unary guard declines
  case vc13 =>
    rename_i _ _ _ _ _ hus _ s0 s1 hck1 hx01 hp10 hsucc hel hvc hve hng
    obtain ⟨nm, ls, ax, rfl, hn, ha, hle⟩ := unary_shape hwf hve hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    rw [pinBeq hwf hn (hsucc _ rfl)] at hng
    have hng' : ¬ (nm = ConLeche.natSuccName ∧ ConLeche.natLitSupported env = true) := by
      simpa using hng
    refine ⟨hck1, hx01, hp10, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    exact ⟨none, rfl, by simp, 0, reduceNatFueled_succ_no hng'⟩
  -- the binary shape at a level-carrying constant
  case vc15 =>
    rename_i _ _ _ _ _ _ _ hus s0 hel hvc hvf2 hve
    obtain ⟨nm, ls, ax, bx, rfl, _, _, _, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, 0, reduceNatFueled_none_of ?_ ?_⟩
    · intro c' a' h'; simp at h'
    · intro c' a' b' h'
      simp only [Expr.app.injEq, Expr.const.injEq] at h'
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h'
      rw [hle] at hus; simp at hus
  case vc17 =>
    rename_i _ _ _ _ _ _ _ hus s0 hel hvc hvf2 hve
    obtain ⟨nm, _, _, _, _, hn, _⟩ := binary_shape hwf hve hvf2 hvc hden hel
    exact ⟨nm, hn⟩
  case vc19 =>
    rename_i _ _ _ _ _ _ _ hus rb s0 hbin hel hvc hvf2 hve
    obtain ⟨nm, _, _, _, _, hn, _⟩ := binary_shape hwf hve hvf2 hvc hden hel
    exact ⟨nm, hn⟩
  case vc21 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 hsto hbin hel hvc hvf2 hve
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    exact ⟨ax, ha, hwx.1⟩
  case vc23 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 _ s1 hck1 hx01 hp10 hwa hsto hbin hel hvc hvf2 hve
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    obtain ⟨w, hw, _, _⟩ := hwa ax ha
    exact ⟨w, hw⟩
  case vc25 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 _ n s1 hsto hbin hel hvc hvf2 hve hck1 hr hx01 hp10 hwa
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    exact ⟨bx, denote_ext hb hx01, hwx.2⟩
  case vc27 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 _ n s1 _ s2 hck2 hx12 hp21 hwb hsto hbin hel hvc hvf2 hve hck1 hr hx01 hp10 hwa
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    obtain ⟨w, hw, _, _⟩ := hwb bx (denote_ext hb hx01)
    exact ⟨w, hw⟩
  -- the certified binary operation FIRES
  case vc28 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 _ n s1 _ n2 s2 _ s3 hsto hbin hel hvc hvf2 hve hck1 hr hx01 hp10 hwa hck2 hr2 hx12 hp21 hwb
    intro hck3 hx23 hp32 hres
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    have hcond : NatBinOp nm ∧ ConLeche.natOpStored env nm = true := by
      have h1 := hbin nm hn
      have h2 := hsto nm hn
      simp only [Bool.and_eq_true] at hbg
      exact ⟨h1.mp hbg.1, h2 ▸ hbg.2⟩
    obtain ⟨w₁, hw₁, _, F₁, hF₁⟩ := hwa ax ha
    have hr₁ := hr w₁ hw₁
    obtain ⟨w₂, hw₂, _, F₂, hF₂⟩ := hwb bx (denote_ext hb hx01)
    have hr₂ := hr2 w₂ hw₂
    refine ⟨hck3, ((hx01.trans hx12).trans hx23), by rw [hp32, hp21, hp10],
      fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨_, hres nm (denoteN_ext hn (hx01.trans hx12)),
      fun y hy => natOpResult_wscoped hy, F₁ + F₂, ?_⟩
    dsimp only
    rw [reduceNatFueled_bin hcond (ConLeche.whnf_mono (by omega) hF₁), ← hr₁]
    simp only [bind, Except.bind, ConLeche.whnf_mono (by omega : F₂ ≤ F₁ + F₂) hF₂,
      ← hr₂]
    rfl
  case vc30 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 _ n s1 _ s2 n2 hck2 hx12 hp21 hwb hsto hbin hel hvc hvf2 hve hck1 hr hx01 hp10 hwa
    intro s hs _; subst hs
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    exact ⟨nm, denoteN_ext hn (hx01.trans hx12)⟩
  -- the second argument is not a literal
  case vc31 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 _ n s1 _ s2 hsto hbin hel hvc hvf2 hve hck1 hr hx01 hp10 hwa hck2 hr2 hx12 hp21 hwb
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    have hcond : NatBinOp nm ∧ ConLeche.natOpStored env nm = true := by
      have h1 := hbin nm hn
      have h2 := hsto nm hn
      simp only [Bool.and_eq_true] at hbg
      exact ⟨h1.mp hbg.1, h2 ▸ hbg.2⟩
    obtain ⟨w₁, hw₁, _, F₁, hF₁⟩ := hwa ax ha
    have hr₁ := hr w₁ hw₁
    obtain ⟨w₂, hw₂, _, F₂, hF₂⟩ := hwb bx (denote_ext hb hx01)
    have hr₂ := hr2 w₂ hw₂
    refine ⟨hck2, hx01.trans hx12, by rw [hp21, hp10], fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, F₁ + F₂, ?_⟩
    dsimp only
    rw [reduceNatFueled_bin hcond (ConLeche.whnf_mono (by omega) hF₁), ← hr₁]
    simp only [bind, Except.bind, ConLeche.whnf_mono (by omega : F₂ ≤ F₁ + F₂) hF₂,
      ← hr₂]
    rfl
  -- the first argument is not a literal
  case vc32 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hbg s0 _ s1 hsto hbin hel hvc hvf2 hve hck1 hr hx01 hp10 hwa
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    have hcond : NatBinOp nm ∧ ConLeche.natOpStored env nm = true := by
      have h1 := hbin nm hn
      have h2 := hsto nm hn
      simp only [Bool.and_eq_true] at hbg
      exact ⟨h1.mp hbg.1, h2 ▸ hbg.2⟩
    obtain ⟨w₁, hw₁, _, F₁, hF₁⟩ := hwa ax ha
    have hr₁ := hr w₁ hw₁
    refine ⟨hck1, hx01, hp10, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, F₁, ?_⟩
    dsimp only
    rw [reduceNatFueled_bin hcond hF₁, ← hr₁]
    rfl
  -- the WF-pinned safety net: its preconditions
  case vc36 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hnbg _ s0 s1 hck1 hx01 hp10 hwfn hsto hbin hel hvc hvf2 hve hwg
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    exact ⟨ax, denote_ext ha hx01, hwx.1⟩
  case vc38 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hnbg _ s0 s1 _ s2 hck1 hck2 hx01 hx12 hp10 hp21 hwa hwfn hsto hbin hel hvc hvf2 hve hwg
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    obtain ⟨w, hw, _, _⟩ := hwa ax (denote_ext ha hx01)
    exact ⟨w, hw⟩
  case vc40 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hnbg _ s0 s1 _ n s2 hck1 hx01 hp10 hwfn hsto hbin hel hvc hvf2 hve hwg hck2 hr hx12 hp21 hwa
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    exact ⟨bx, denote_ext hb (hx01.trans hx12), hwx.2⟩
  case vc42 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hnbg _ s0 s1 _ n s2 _ s3 hck1 hck3 hx01 hx23 hp10 hp32 hwb hwfn hsto hbin hel hvc hvf2 hve hwg hck2 hr hx12 hp21 hwa
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    obtain ⟨w, hw, _, _⟩ := hwb bx (denote_ext hb (hx01.trans hx12))
    exact ⟨w, hw⟩
  -- the safety net: the second argument is not a literal
  case vc44 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hnbg _ s0 s1 _ n s2 _ s3 hck1 hx01 hp10 hwfn hsto hbin hel hvc hvf2 hve hwg hck2 hr hx12 hp21 hwa hck3 hr2 hx23 hp32 hwb
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    have hncond : ¬ (NatBinOp nm ∧ ConLeche.natOpStored env nm = true) := by
      have h1 := hbin nm hn
      have h2 := hsto nm hn
      intro ⟨c1, c2⟩
      exact hnbg (by rw [h1.mpr c1, h2, c2]; rfl)
    have hwcond : ConLeche.natOpWfNames.contains nm ∧
        ConLeche.natLitSupported env = true := by
      rw [hwfn _ _ hn] at hwg; simpa using hwg
    obtain ⟨w₁, hw₁, _, F₁, hF₁⟩ := hwa ax (denote_ext ha hx01)
    have hr₁ := hr w₁ hw₁
    obtain ⟨w₂, hw₂, _, F₂, hF₂⟩ := hwb bx (denote_ext hb (hx01.trans hx12))
    have hr₂ := hr2 w₂ hw₂
    refine ⟨hck3, (hx01.trans hx12).trans hx23, by rw [hp32, hp21, hp10],
      fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, F₁ + F₂, ?_⟩
    dsimp only
    rw [reduceNatFueled_wf hncond hwcond (ConLeche.whnf_mono (by omega) hF₁), ← hr₁]
    simp only [bind, Except.bind, ConLeche.whnf_mono (by omega : F₂ ≤ F₁ + F₂) hF₂,
      ← hr₂]
    rfl
  -- the safety net: the first argument is not a literal
  case vc45 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hnbg _ s0 s1 _ s2 hck1 hx01 hp10 hwfn hsto hbin hel hvc hvf2 hve hwg hck2 hr hx12 hp21 hwa
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    have hncond : ¬ (NatBinOp nm ∧ ConLeche.natOpStored env nm = true) := by
      have h1 := hbin nm hn
      have h2 := hsto nm hn
      intro ⟨c1, c2⟩
      exact hnbg (by rw [h1.mpr c1, h2, c2]; rfl)
    have hwcond : ConLeche.natOpWfNames.contains nm ∧
        ConLeche.natLitSupported env = true := by
      rw [hwfn _ _ hn] at hwg; simpa using hwg
    obtain ⟨w₁, hw₁, _, F₁, hF₁⟩ := hwa ax (denote_ext ha hx01)
    have hr₁ := hr w₁ hw₁
    refine ⟨hck2, hx01.trans hx12, by rw [hp21, hp10], fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, F₁, ?_⟩
    dsimp only
    rw [reduceNatFueled_wf hncond hwcond hF₁, ← hr₁]
    rfl
  -- neither guard
  case vc46 =>
    rename_i _ _ _ _ _ _ _ hus rb rb2 hnbg _ s0 s1 hck1 hx01 hp10 hwfn hsto hbin hel hvc hvf2 hve hnwg
    obtain ⟨nm, ls, ax, bx, rfl, hn, ha, hb, hle⟩ :=
      binary_shape hwf hve hvf2 hvc hden hel
    obtain rfl : ls = [] := by rw [hle] at hus; simpa using hus
    simp only [Expr.WScoped, true_and] at hwx
    have hncond : ¬ (NatBinOp nm ∧ ConLeche.natOpStored env nm = true) := by
      have h1 := hbin nm hn
      have h2 := hsto nm hn
      intro ⟨c1, c2⟩
      exact hnbg (by rw [h1.mpr c1, h2, c2]; rfl)
    have hnw : ¬ (ConLeche.natOpWfNames.contains nm ∧
        ConLeche.natLitSupported env = true) := by
      rw [hwfn _ _ hn] at hnwg; simpa using hnwg
    refine ⟨hck1, hx01, hp10, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    exact ⟨none, rfl, by simp, 0, reduceNatFueled_bin_no hncond hnw⟩
  -- the three shapes that are not an operation at all
  case vc47 =>
    rename_i _ _ _ _ _ hnc s0 hvx hvf2 hve
    obtain ⟨fx, bx, rfl, hf, _⟩ := denote_app_inv hwf hve hden
    obtain ⟨gx, ax, rfl, hg, _⟩ := denote_app_inv hwf hvf2 hf
    have hnc' := denote_not_const hwf hvx hg (fun c us h => hnc c us h)
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, 0, reduceNatFueled_none_of ?_ ?_⟩
    · intro c' a' h'; simp at h'
    · intro c' a' b' h'
      simp only [Expr.app.injEq] at h'
      exact hnc' c' [] h'.1.1
  case vc49 =>
    rename_i _ _ _ hnc hna s0 hvx hve
    obtain ⟨fx, ax, rfl, hf, _⟩ := denote_app_inv hwf hve hden
    have hnc' := denote_not_const hwf hvx hf (fun c us h => hnc c us h)
    have hna' := denote_not_app hwf hvx hf (fun f a h => hna f a h)
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, 0, reduceNatFueled_none_of ?_ ?_⟩
    · intro c' a' h'
      simp only [Expr.app.injEq] at h'
      exact hnc' c' [] h'.1
    · intro c' a' b' h'
      simp only [Expr.app.injEq] at h'
      exact hna' _ _ h'.1
  case vc50 =>
    rename_i _ hna s0 hve
    have hna' := denote_not_app hwf hve hden (fun f a h => hna f a h)
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, 0, reduceNatFueled_none_of ?_ ?_⟩
    · intro c' a' h'; exact hna' _ _ h'
    · intro c' a' b' h'; exact hna' _ _ h'
  -- the tag-first `else` arms (round 4): the `app` arm's head `g` does not
  -- carry the `const` tag, and `e` does not carry the `app` tag; the views
  -- come back from the denotations
  case vc48 =>
    rename_i _ _ _ _ htg s0 hvf2 hve
    obtain ⟨fx, bx, rfl, hf, _⟩ := denote_app_inv hwf hve hden
    obtain ⟨gx, ax, rfl, hg, _⟩ := denote_app_inv hwf hvf2 hf
    obtain ⟨vx, hvx⟩ := denoteE_view hg
    have hnc' := denote_not_const hwf hvx hg
      (fun c us hh => view_tagOf_ne hvx (t := ETag.const) htg (by rw [hh]; rfl))
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, 0, reduceNatFueled_none_of ?_ ?_⟩
    · intro c' a' h'; simp at h'
    · intro c' a' b' h'
      simp only [Expr.app.injEq] at h'
      exact hnc' c' [] h'.1.1
  case vc51 =>
    rename_i hta s0
    obtain ⟨vx, hve⟩ := denoteE_view hden
    have hna' := denote_not_app hwf hve hden
      (fun f a hh => view_tagOf_ne hve (t := ETag.app) hta (by rw [hh]; rfl))
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl := Option.some.inj (hx'.symm.trans hden)
    refine ⟨none, rfl, by simp, 0, reduceNatFueled_none_of ?_ ?_⟩
    · intro c' a' h'; exact hna' _ _ h'
    · intro c' a' b' h'; exact hna' _ _ h'

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
