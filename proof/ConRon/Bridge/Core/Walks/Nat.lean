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

end ConRon.Bridge.Core
