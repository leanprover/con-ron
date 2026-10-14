/-
# `ConRon.Bridge.Core.Walks.IotaMajor` — the ι major's preparation

Task #97-P3-Core round 6 (lane `iota`): `litMajorToCtor`, the stuck-major
rescue `majorToCtor` (K, η, the pinned `And`) and `prepareMajor`, which runs
them in the official kernel's order (lean4#15351; restated at con-leche
e74d32ad by task #119: the η rescue is uncertified, K and `And` check the
fabricated constructor's type and, at the verified mode, proof irrelevance).
-/
import ConRon.Bridge.Core.Walks.IotaLeaves

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## Vocabulary candidates (for Bridge/Grind.lean) -/

/-! ### Fuel-free answers -/

/-- a fuelled pure run reaches `v` at some fuel -/
def Runs {α : Type} (P : Nat → CheckM α) (v : α) : Prop := ∃ F, P F = .ok v

/-- a knot slot's pure run at a subject reaches `v` -/
def RunE (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (e v : Expr) : Prop :=
  ∃ F, op F d e = .ok v

/-- a knot slot's result at the answer's denotation: well scoped, and the
pure run's value -/
def SlotRes (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (e : Expr) : Option Expr → Prop
  | some v => Expr.WScoped d v ∧ RunE op d e v
  | none => False

@[bridge_grind =] theorem SlotRes.some_eq (op : Nat → Nat → Expr → CheckM Expr) (d : Nat)
    (e v : Expr) : SlotRes op d e (some v) = (Expr.WScoped d v ∧ RunE op d e v) := rfl

theorem SlotRes.isSome {op : Nat → Nat → Expr → CheckM Expr} {d : Nat} {e : Expr}
    {o : Option Expr} (h : SlotRes op d e o) : o.isSome = true := by
  cases o with
  | none => exact h.elim
  | some _ => rfl
grind_pattern [bridge_grind] SlotRes.isSome => SlotRes op d e o

/-- the knot slot's answer about an optional subject -/
def SlotAns (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (st : EStore) (r : EIdx) :
    Option Expr → Prop
  | some e => SlotRes op d e (denoteE st r)
  | none => True

@[bridge_grind =] theorem SlotAns.some_eq (op : Nat → Nat → Expr → CheckM Expr) (d : Nat)
    (st : EStore) (r : EIdx) (e : Expr) :
    SlotAns op d st r (some e) = SlotRes op d e (denoteE st r) := rfl

theorem slotAns_of_simE {op : Nat → Nat → Expr → CheckM Expr} {d : Nat} {e : Expr}
    {st : EStore} {r : EIdx} (h : SimE op d e st r) : SlotAns op d st r (some e) := by
  obtain ⟨v, hv, hw, hF⟩ := h
  show SlotRes op d e (denoteE st r)
  rw [hv]; exact ⟨hw, hF⟩

/-- a walk's answer at its result denotation -/
def OutE (P : Nat → CheckM Expr) (d : Nat) : Option Expr → Prop
  | some v => Expr.WScoped d v ∧ Runs P v
  | none => False

@[bridge_grind =] theorem OutE.some_eq (P : Nat → CheckM Expr) (d : Nat) (v : Expr) :
    OutE P d (some v) = (Expr.WScoped d v ∧ Runs P v) := rfl

theorem OutE.isSome {P : Nat → CheckM Expr} {d : Nat} {o : Option Expr} (h : OutE P d o) :
    o.isSome = true := by
  cases o with
  | none => exact h.elim
  | some _ => rfl
grind_pattern [bridge_grind] OutE.isSome => OutE P d o

@[bridge_grind =] theorem simEOp_eq (P : Nat → CheckM Expr) (d : Nat) (st : EStore) (r : EIdx) :
    SimEOp P d st r = OutE P d (denoteE st r) := by
  unfold SimEOp; cases h : denoteE st r <;> simp [OutE, Runs]

/-- the `defeq` slot's answer at two optional subjects -/
def DefeqAns (mode : CheckMode) (env : Env) (d : Nat) (x : Bool) :
    Option Expr → Option Expr → Prop
  | some a, some b => SimV (ConLeche.isDefEqCore mode env) d a b x
  | _, _ => True

@[bridge_grind =] theorem DefeqAns.some_eq (d : Nat) (x : Bool) (a b : Expr) :
    DefeqAns mode env d x (some a) (some b) = SimV (ConLeche.isDefEqCore mode env) d a b x := rfl

theorem KnotSpec.inferIOS {f : Nat} (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hw : DenWS d (denoteE s₀.store i)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).inferIO d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        SlotAns (ConLeche.inferTypeIO mode env) d s'.store r (denoteE s₀.store i); ⊤⦄ := by
  cases hd : denoteE s₀.store i with
  | none => rw [hd] at hw; exact hw.elim
  | some e =>
    rw [hd] at hw
    exact triple_mono (hsim.inferIO s₀ d i e hok hd hw)
      (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, slotAns_of_simE h4⟩)

theorem KnotSpec.whnfS {f : Nat} (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hw : DenWS d (denoteE s₀.store i)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).whnf d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        SlotAns (ConLeche.whnf mode env) d s'.store r (denoteE s₀.store i); ⊤⦄ := by
  cases hd : denoteE s₀.store i with
  | none => rw [hd] at hw; exact hw.elim
  | some e =>
    rw [hd] at hw
    exact triple_mono (hsim.whnf s₀ d i e hok hd hw)
      (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, slotAns_of_simE h4⟩)

theorem KnotSpec.defeqS {f : Nat} (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i j : EIdx) (hok : CheckOK mode env fe s₀)
    (hi : DenWS d (denoteE s₀.store i)) (hj : DenWS d (denoteE s₀.store j)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).defeq d i j
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        DefeqAns mode env d r (denoteE s₀.store i) (denoteE s₀.store j); ⊤⦄ := by
  cases hdi : denoteE s₀.store i with
  | none => rw [hdi] at hi; exact hi.elim
  | some a =>
  cases hdj : denoteE s₀.store j with
  | none => rw [hdj] at hj; exact hj.elim
  | some b =>
    rw [hdi] at hi; rw [hdj] at hj
    exact triple_mono (hsim.defeq s₀ d i j a b hok hdi hdj hi hj) (fun _ _ h => h)

/-- con-leche's `proofIrrel` at two subjects, as a fuelled run -/
def proofIrrelOp (mode : CheckMode) (env : Env) (d : Nat) (a b : Expr) : Nat → CheckM Bool :=
  fun F => ConLeche.proofIrrelFueled mode env F d a b

/-- `proofIrrel`'s answer at two optional subjects -/
def PIAns (mode : CheckMode) (env : Env) (d : Nat) (x : Bool) :
    Option Expr → Option Expr → Prop
  | some a, some b => Runs (proofIrrelOp mode env d a b) x
  | _, _ => True

@[bridge_grind =] theorem PIAns.some_eq (d : Nat) (x : Bool) (a b : Expr) :
    PIAns mode env d x (some a) (some b) = Runs (proofIrrelOp mode env d a b) x := rfl

theorem proofIrrel_specS {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK mode env fe s₀)
    (ha : DenWS d (denoteE s₀.store a)) (hb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PIAns mode env d r (denoteE s₀.store a) (denoteE s₀.store b); ⊤⦄ := by
  cases hda : denoteE s₀.store a with
  | none => rw [hda] at ha; exact ha.elim
  | some x =>
  cases hdb : denoteE s₀.store b with
  | none => rw [hdb] at hb; exact hb.elim
  | some y =>
    rw [hda] at ha; rw [hdb] at hb
    exact triple_mono (proofIrrel_spec hsim s₀ d a b x y hok hda hdb ha hb) (fun _ _ h => h)

/-- the fabricated spine's scope check -/
def scopeOkFn (d : Nat) (ef em : Expr) : Bool :=
  ef.wscopedB d && ef.looseBVarsBounded 0 && ef.fvarLeaves.all (fun l => em.fvarLeaves.contains l)

def ScopeAns (d : Nat) (r : Bool) : Option Expr → Option Expr → Prop
  | some ef, some em => r = scopeOkFn d ef em
  | _, _ => True

@[bridge_grind =] theorem ScopeAns.some_eq (d : Nat) (r : Bool) (ef em : Expr) :
    ScopeAns d r (some ef) (some em) = (r = scopeOkFn d ef em) := rfl

theorem fabScopeOk_specS (s₀ : AState) (d : Nat) (fab major : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hf : (denoteE s₀.store fab).isSome = true) (hm : (denoteE s₀.store major).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.fabScopeOk d fab major
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        ScopeAns d r (denoteE s₀.store fab) (denoteE s₀.store major); ⊤⦄ := by
  obtain ⟨ef, hef⟩ := Option.isSome_iff_exists.mp hf
  obtain ⟨em, hem⟩ := Option.isSome_iff_exists.mp hm
  rw [hef, hem]
  exact fabScopeOk_spec s₀ d fab major ef em hok hef hem

theorem scopeOk_wscoped {d : Nat} {ef em : Expr} (h : scopeOkFn d ef em = true) :
    Expr.WScoped d ef := by
  simp only [scopeOkFn, Bool.and_eq_true] at h
  exact Expr.WScoped.of_wscopedB h.1.1
grind_pattern [bridge_grind] scopeOk_wscoped => scopeOkFn d ef em

theorem denoteEList_take_rel (st : EStore) (hs : List EIdx) (n : Nat) :
    MapRel (List.take n) (Frontend.denoteEList st hs) (Frontend.denoteEList st (hs.take n)) := by
  cases h : Frontend.denoteEList st hs with
  | none => trivial
  | some xs => exact ExprOps.denoteEList_take n hs xs h
grind_pattern [bridge_grind] denoteEList_take_rel => Frontend.denoteEList st (hs.take n)

theorem denoteEList_drop_rel (st : EStore) (hs : List EIdx) (n : Nat) :
    MapRel (List.drop n) (Frontend.denoteEList st hs) (Frontend.denoteEList st (hs.drop n)) := by
  cases h : Frontend.denoteEList st hs with
  | none => trivial
  | some xs => exact ExprOps.denoteEList_drop _ _ _ h
grind_pattern [bridge_grind] denoteEList_drop_rel => Frontend.denoteEList st (hs.drop n)

theorem denoteNList_le {st st' : EStore} {hs : List NIdx} (hx : st ≤ st')
    (hd : Frontend.denoteNList st.ns hs ≠ none) :
    Frontend.denoteNList st'.ns hs = Frontend.denoteNList st.ns hs := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteNListE_ext hx _ _ h
grind_pattern [bridge_grind] denoteNList_le => st ≤ st', Frontend.denoteNList st.ns hs

theorem denoteCaps_le {st st' : EStore} {c : IIndCaps} (hx : st ≤ st')
    (hd : Frontend.denoteCaps st c ≠ none) :
    Frontend.denoteCaps st' c = Frontend.denoteCaps st c := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteCaps_ext h hx
grind_pattern [bridge_grind] denoteCaps_le => st ≤ st', Frontend.denoteCaps st c

theorem denoteRules_le {st st' : EStore} {rs : List IRecRule} (hx : st ≤ st')
    (hd : Frontend.denoteRules st rs ≠ none) :
    Frontend.denoteRules st' rs = Frontend.denoteRules st rs := by
  obtain ⟨xs, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteRules_ext hx _ _ h
grind_pattern [bridge_grind] denoteRules_le => st ≤ st', Frontend.denoteRules st rs

theorem denoteCV_le {st st' : EStore} {cv : IConstantVal} (hx : st ≤ st')
    (hd : Frontend.denoteCV st cv ≠ none) :
    Frontend.denoteCV st' cv = Frontend.denoteCV st cv := by
  obtain ⟨c, h⟩ := Option.ne_none_iff_exists'.mp hd
  rw [h]; exact denoteCV_ext h hx
grind_pattern [bridge_grind] denoteCV_le => st ≤ st', Frontend.denoteCV st cv

theorem nidx_eq_of_denote {st : EStore} (hwf : StoreWF st) {a b : NIdx}
    (h : denoteN st.ns a = denoteN st.ns b) (hs : denoteN st.ns a ≠ none) : a = b := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hs
  obtain ⟨rk, hrk⟩ := hwf
  exact denoteN_inj hrk.nsWF hx (h ▸ hx)
grind_pattern [bridge_grind] nidx_eq_of_denote => StoreWF st, denoteN st.ns a, denoteN st.ns b where
  guard denoteN st.ns a = denoteN st.ns b
  a =/= b

/-- a name-handle list's membership test at its denotation -/
def ContainsAt (b : Bool) : Option (List ConLeche.Name) → Option ConLeche.Name → Prop
  | some xs, some x => b = xs.contains x
  | _, _ => True

@[bridge_grind =] theorem ContainsAt.some_eq (b : Bool) (xs : List ConLeche.Name)
    (x : ConLeche.Name) : ContainsAt b (some xs) (some x) = (b = xs.contains x) := rfl

theorem containsAt {st : EStore} (hwf : StoreWF st) (ns : List NIdx) (n : NIdx) :
    ContainsAt (List.elem n ns) (Frontend.denoteNList st.ns ns) (denoteN st.ns n) := by
  cases h1 : Frontend.denoteNList st.ns ns with
  | none => trivial
  | some xs =>
  cases h2 : denoteN st.ns n with
  | none => trivial
  | some x => exact denoteNList_containsC hwf ns xs h1 n x h2
grind_pattern [bridge_grind] containsAt => StoreWF st, List.elem n ns, Frontend.denoteNList st.ns ns

theorem denoteEList_cons_eq (st : EStore) (a : EIdx) (as : List EIdx) :
    Frontend.denoteEList st (a :: as) =
      opt2 List.cons (denoteE st a) (Frontend.denoteEList st as) := by
  simp only [Frontend.denoteEList]
  cases denoteE st a <;> cases Frontend.denoteEList st as <;> rfl

/-- two optional lists, appended -/
def optAppend {α : Type} : Option (List α) → Option (List α) → Option (List α)
  | some a, some b => some (a ++ b)
  | _, _ => none

@[bridge_grind =] theorem optAppend_some {α : Type} (a b : List α) :
    optAppend (some a) (some b) = some (a ++ b) := rfl

theorem denoteEList_append_eq (st : EStore) :
    ∀ (as bs : List EIdx), Frontend.denoteEList st (as ++ bs) =
      optAppend (Frontend.denoteEList st as) (Frontend.denoteEList st bs)
  | [], bs => by
    rw [List.nil_append]; cases Frontend.denoteEList st bs <;> rfl
  | a :: as, bs => by
    rw [List.cons_append, denoteEList_cons_eq, denoteEList_cons_eq, denoteEList_append_eq st as bs]
    cases denoteE st a <;> cases Frontend.denoteEList st as <;>
      cases Frontend.denoteEList st bs <;> rfl

/-- a projection node's denotation at its two children's -/
def optProj (i : Nat) : Option ConLeche.Name → Option Expr → Option Expr
  | some nm, some x => some (.proj nm i x)
  | _, _ => none

@[bridge_grind =] theorem optProj_some (i : Nat) (nm : ConLeche.Name) (x : Expr) :
    optProj i (some nm) (some x) = some (.proj nm i x) := rfl

theorem denoteEView_proj (st : EStore) (n : NIdx) (i : Nat) (e : EIdx) :
    denoteEView st (.proj n i e) = optProj i (denoteN st.ns n) (denoteE st e) := by
  simp only [denoteEView]
  cases denoteN st.ns n <;> cases denoteE st e <;> rfl

theorem denoteEView_const (st : EStore) (n : NIdx) (us : LsIdx) :
    denoteEView st (.const n us) = opt2 Expr.const (denoteN st.ns n) (denoteLs st.lss us) := rfl

theorem view_of_viewLit {st : EStore} {i : EIdx} {l : Literal}
    (htg : i.tag = ETag.lit) (h : st.viewLit i = some l) :
    st.view i = some (.lit l) :=
  EStore.view_of_proj (p := ETables.getLit) (fun t hh => by
    simp only [ETables.getLit, Option.map_eq_some_iff] at hh
    obtain ⟨r, hr, rfl⟩ := hh
    simp [ETables.get, htg, hr, ETag.lit, ETag.sort, ETag.bvar, ETag.fvar, ETag.const,
      ETag.app, ETag.lam, ETag.forallE, ETag.letE]) h
grind_pattern [bridge_grind] view_of_viewLit => st.viewLit i, some l where
  guard st.viewLit i = some l

/-- con-leche: ConLeche/Kernel/Basis/Names.lean andName — the pin table's `And` slot -/
@[bridge_grind =] theorem pinNames_eq_andName : pinNames[PIN_AND]? = some ConLeche.andName := rfl

/-- con-leche: none — is a literal a string. -/
def litIsStr : Literal → Bool | .strVal _ => true | .natVal _ => false
/-- a string literal's string -/
def litStr : Literal → String | .strVal s => s | .natVal _ => ""

theorem isStrLit_eq (e : Expr) :
    e.isStrLit = (exprTag e == ETag.lit && litIsStr (exprLit e)) := by
  cases e <;> try rfl
  rename_i l; cases l <;> rfl

/-! ## The environment index at inductives, constructors and recursors -/

def cIndCaps : Option ConstantInfo → IndCaps | some (.indInfo _ c) => c | _ => {}
def cCtorNP : Option ConstantInfo → Nat | some (.ctorInfo _ n _) => n | _ => 0
def iRec? : Option IConstantInfo → Bool | some (.recInfo _ _ _ _) => true | _ => false
def iRecVal : Option IConstantInfo → IConstantVal | some (.recInfo v _ _ _) => v | _ => default
def iRecMI : Option IConstantInfo → Nat | some (.recInfo _ m _ _) => m | _ => 0
def iRecRP : Option IConstantInfo → Nat | some (.recInfo _ _ r _) => r | _ => 0
def iRecRules : Option IConstantInfo → List IRecRule | some (.recInfo _ _ _ rs) => rs | _ => []
def cRec? : Option ConstantInfo → Bool | some (.recInfo _ _ _ _) => true | _ => false
def cRecVal : Option ConstantInfo → ConstantVal | some (.recInfo v _ _ _) => v | _ => default
def cRecMI : Option ConstantInfo → Nat | some (.recInfo _ m _ _) => m | _ => 0
def cRecRP : Option ConstantInfo → Nat | some (.recInfo _ _ r _) => r | _ => 0
def cRecRules : Option ConstantInfo → List RecRule | some (.recInfo _ _ _ rs) => rs | _ => []

theorem iRec?_eta {o : Option IConstantInfo} (h : iRec? o = true) :
    o = some (.recInfo (iRecVal o) (iRecMI o) (iRecRP o) (iRecRules o)) := by
  match o, h with
  | some (.recInfo _ _ _ _), _ => rfl
local grind_pattern [bridge_grind] iRec?_eta => iRec? o

/-- the index's inductive, constructor and recursor halves at a lookup pair -/
def IotaCI (st : EStore) (oi : Option IConstantInfo) (oc : Option ConstantInfo) : Prop :=
  cInd? oc = iInd? oi ∧
  (iInd? oi = true →
    Frontend.denoteCV st (iIndVal oi) = some (cIndVal oc) ∧
    Frontend.denoteNList st.ns (iIndVal oi).levelParams = some (cIndVal oc).levelParams ∧
    Frontend.denoteCaps st (iIndCaps oi) = some (cIndCaps oc)) ∧
  cCtor? oc = iCtor? oi ∧
  (iCtor? oi = true → Frontend.denoteCV st (iCtorVal oi) = some (cCtorVal oc) ∧
    cCtorNP oc = iCtorNP oi) ∧
  cRec? oc = iRec? oi ∧
  (iRec? oi = true → Frontend.denoteCV st (iRecVal oi) = some (cRecVal oc) ∧
    Frontend.denoteRules st (iRecRules oi) = some (cRecRules oc) ∧
    cRecMI oc = iRecMI oi ∧ cRecRP oc = iRecRP oi)

def IotaAt (env : Env) (fe : IFEnv) (st : EStore) (c : NIdx) : Option ConLeche.Name → Prop
  | some nm => IotaCI st (fe.find? c) (env.find? nm)
  | none => True

theorem iotaAt {s : AState} (hok : CheckOK mode env fe s) (c : NIdx) :
    IotaAt env fe s.store c (denoteN s.store.ns c) := by
  cases hn : denoteN s.store.ns c with
  | none => trivial
  | some nm =>
    show IotaCI _ _ _
    cases hf : fe.find? c with
    | none =>
      rw [IFEnvOK.miss hok.state hok.ienv hn hf]
      exact ⟨rfl, nofun, rfl, nofun, rfl, nofun⟩
    | some ci =>
      obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hf
      obtain rfl := Option.some.inj (hn'.symm.trans hn)
      rw [hfind]
      cases ci <;> simp only [Frontend.denoteCI] at hci
      case indInfo v caps =>
        split at hci
        · rename_i dcv dcaps hdcv hdcaps
          cases hci
          exact ⟨rfl, fun _ => ⟨hdcv, (denoteCV_inv hdcv).2.1, hdcaps⟩, rfl, nofun, rfl, nofun⟩
        · cases hci
      case ctorInfo v nP nF =>
        obtain ⟨dcv, hdcv, rfl⟩ := Option.map_eq_some_iff.mp hci
        exact ⟨rfl, nofun, rfl, fun _ => ⟨hdcv, rfl⟩, rfl, nofun⟩
      case recInfo v mI rP rs =>
        split at hci
        · rename_i dcv drs hdcv hdrs
          cases hci
          exact ⟨rfl, nofun, rfl, nofun, rfl, fun _ => ⟨hdcv, hdrs, rfl, rfl⟩⟩
        · cases hci
      all_goals first
        | (split at hci
           · cases hci; exact ⟨rfl, nofun, rfl, nofun, rfl, nofun⟩
           · cases hci)
        | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hci
           exact ⟨rfl, nofun, rfl, nofun, rfl, nofun⟩)
local grind_pattern [bridge_grind] iotaAt => CheckOK mode env fe s, fe.find? c

theorem IotaAt.some {st : EStore} {c : NIdx} {nm : ConLeche.Name}
    (H : IotaAt env fe st c (some nm)) : IotaCI st (fe.find? c) (env.find? nm) := H
local grind_pattern [bridge_grind] IotaAt.some => IotaAt env fe st c (some nm)

attribute [local bridge_grind =] IotaCI

theorem iInd?_ind (v : IConstantVal) (caps : IIndCaps) :
    iInd? (some (.indInfo v caps)) = true := rfl
theorem iIndVal_ind (v : IConstantVal) (caps : IIndCaps) :
    iIndVal (some (.indInfo v caps)) = v := rfl
theorem iIndCaps_ind (v : IConstantVal) (caps : IIndCaps) :
    iIndCaps (some (.indInfo v caps)) = caps := rfl
theorem iCtor?_ctor (v : IConstantVal) (n f : Nat) :
    iCtor? (some (.ctorInfo v n f)) = true := rfl
theorem iCtorVal_ctor (v : IConstantVal) (n f : Nat) :
    iCtorVal (some (.ctorInfo v n f)) = v := rfl
theorem iCtorNP_ctor (v : IConstantVal) (n f : Nat) :
    iCtorNP (some (.ctorInfo v n f)) = n := rfl
theorem iRec?_rec (v : IConstantVal) (m r : Nat) (rs : List IRecRule) :
    iRec? (some (.recInfo v m r rs)) = true := rfl
theorem iRecVal_rec (v : IConstantVal) (m r : Nat) (rs : List IRecRule) :
    iRecVal (some (.recInfo v m r rs)) = v := rfl
theorem iRecMI_rec (v : IConstantVal) (m r : Nat) (rs : List IRecRule) :
    iRecMI (some (.recInfo v m r rs)) = m := rfl
theorem iRecRP_rec (v : IConstantVal) (m r : Nat) (rs : List IRecRule) :
    iRecRP (some (.recInfo v m r rs)) = r := rfl
theorem iRecRules_rec (v : IConstantVal) (m r : Nat) (rs : List IRecRule) :
    iRecRules (some (.recInfo v m r rs)) = rs := rfl
attribute [local bridge_grind =] iInd?_ind iIndVal_ind iIndCaps_ind iCtor?_ctor iCtorVal_ctor
  iCtorNP_ctor iRec?_rec iRecVal_rec iRecMI_rec iRecRP_rec iRecRules_rec


/-! ## The pure side: con-leche's text at its exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — every
major but a string literal takes the `Nat` conversion. -/
theorem litMajorToCtorFueled_nstr {F d : Nat} {x : Expr}
    (hx : ∀ str, x ≠ .lit (.strVal str)) :
    ConLeche.litMajorToCtorFueled mode env F d x =
      .ok (ConLeche.litToCtorIfNat env x) := by
  cases x with
  | lit l =>
    cases l with
    | strVal str => exact absurd rfl (hx str)
    | natVal n => rfl
  | _ => rfl

/-! ### `majorToCtor`'s pure side, one function per rescue branch

con-leche's `majorToCtor` at `pureFns mode env F`, past the shared prefix
(not a constructor application, a single rule, its constructor's inductive),
split into the three branches — each a copy of the con-leche text that
`majorToCtorFueled_pre` ties to the original by `rfl`, so the copies cannot
drift. -/

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch. -/
def mtcK (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    CheckM Expr :=
  (ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ cvj.levelParams.length = ust.length then
      if cnP ≤ tmaj.getAppArgs.length then
        let fab := Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)
        if fab.wscopedB d && fab.looseBVarsBounded 0 &&
            fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
          (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
          (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
          if rd then
            (if mode.verifiedChecks then
              ConLeche.proofIrrel (ConLeche.pureFns mode env F) d fab major
            else pure true) >>= fun r => if r then pure fab else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the η branch
(no certificate on the fabricated spine, con-leche's task #342 L11b). -/
def mtcEta (mode : CheckMode) (env : Env) (F d : Nat) (cvT : ConstantVal)
    (caps : IndCaps) (T : ConLeche.Name) (major : Expr) : CheckM Expr :=
  (ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        ConLeche.capsNeverZero cvT.levelParams ust caps = true ∧
        ConLeche.reservedBasisNames.contains T = false ∧
        ConLeche.reservedBasisNames.contains caps.etaCtor = false ∧
        ConLeche.towerSlotsAll env T caps.etaFields = true then
      let fab := Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE T tmaj.getAppArgs major caps.etaFields)
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        pure fab
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the pinned
`And` branch. -/
def mtcAnd (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    CheckM Expr :=
  (ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        ConLeche.andRescueSlots env rl.ctor cnP ust = true then
      let fab := Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
        (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
        if rd then
          (if mode.verifiedChecks then
            ConLeche.proofIrrel (ConLeche.pureFns mode env F) d fab major
          else pure true) >>= fun r => if r then pure fab else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — the prefix:
past it, the three branches. -/
theorem majorToCtorFueled_pre {F d : Nat} {cn : ConLeche.Name} {rl : RecRule}
    {x : Expr} {cvj cvT : ConstantVal} {cnP cnF : Nat} {T : ConLeche.Name}
    {lus : List Level} {caps : IndCaps}
    (hnc : ConLeche.isCtorApp env x = false)
    (hfj : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hpr : cvj.type.piResult.getAppFn = .const T lus)
    (hfT : env.find? T = some (.indInfo cvT caps)) :
    ConLeche.majorToCtorFueled mode env F d cn [rl] x =
      if rl.k = true then mtcK mode env F d rl cvj cnP T x
      else if rl.eta = true then mtcEta mode env F d cvT caps T x
      else if T = ConLeche.andName then mtcAnd mode env F d rl cvj cnP T x
      else pure x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hfj, hpr,
    hfT, Bool.false_eq_true, ite_false]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — a constructor
application stays. -/
theorem majorToCtorFueled_ctor {F d : Nat} {cn : ConLeche.Name}
    {rules : List RecRule} {x : Expr} (h : ConLeche.isCtorApp env x = true) :
    ConLeche.majorToCtorFueled mode env F d cn rules x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, ite_true]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — every prefix
miss leaves the major alone. -/
theorem majorToCtorFueled_nrules {F d : Nat} {cn : ConLeche.Name}
    {rules : List RecRule} {x : Expr} (hnc : ConLeche.isCtorApp env x = false)
    (h : ∀ rl, rules ≠ [rl]) :
    ConLeche.majorToCtorFueled mode env F d cn rules x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc,
    Bool.false_eq_true, ite_false]
  match rules, h with
  | [], _ => rfl
  | [rl], h => exact absurd rfl (h rl)
  | _ :: _ :: _, _ => rfl

/-- con-leche: none — a denoted capability record's fields. -/
theorem denoteCaps_fields {st : EStore} {c : IIndCaps} {dc : IndCaps}
    (h : Frontend.denoteCaps st c = some dc) :
    dc.eta = c.eta ∧ denoteN st.ns c.etaCtor = some dc.etaCtor ∧
      dc.etaParams = c.etaParams ∧ dc.etaFields = c.etaFields ∧
      dc.sortZ = c.sortZ := by
  simp only [Frontend.denoteCaps] at h
  split at h
  · rename_i ct _ _ hct _ _; cases h; exact ⟨rfl, hct, rfl, rfl, rfl⟩
  · simp at h

/-- con-leche: none — a denoting rule list has the same K bit. -/
theorem recRuleK_denote {st : EStore} {rules : List IRecRule}
    {rules' : List RecRule} (h : Frontend.denoteRules st rules = some rules') :
    ConRon.Arena.recRuleK rules = ConLeche.recRuleK rules' := by
  match rules, h with
  | [], h =>
    simp only [Frontend.denoteRules] at h; cases h; rfl
  | [r], h =>
    simp only [Frontend.denoteRules] at h
    split at h
    · rename_i x xs hx hxs
      obtain rfl : xs = [] := by
        simp only [Option.some.injEq] at hxs; exact hxs.symm
      cases h
      simp only [Frontend.denoteRule] at hx
      split at hx
      · cases hx; rfl
      · simp at hx
    · simp at h
  | r1 :: r2 :: rs, h =>
    have hl := denoteRules_len h
    match rules', hl with
    | a :: b :: cs, _ => rfl

/-- con-leche: ConLeche/Kernel/Core.lean:782-834 prepareMajor — at a
K-flagged recursor whose rescue produced a constructor application: the
literal conversion of the rescued major. -/
theorem prepareMajorFueled_k {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = true)
    (h1 : ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok m1)
    (hc : ConLeche.isCtorApp env m1 = true)
    (h3 : ConLeche.litMajorToCtorFueled mode env F d m1 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' x = .ok m1 := h1
  have e3 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m1 =
      .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk, ite_true,
    e1, hc, e3, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:782-834 prepareMajor — at a
K-flagged recursor whose rescue did not produce a constructor application:
the major as the rescue left it (con-leche task #334). -/
theorem prepareMajorFueled_kStuck {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 : Expr}
    (hk : ConLeche.recRuleK rules' = true)
    (h1 : ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok m1)
    (hc : ConLeche.isCtorApp env m1 = false) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m1 := by
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' x = .ok m1 := h1
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk, ite_true,
    e1, hc, Bool.false_eq_true, ite_false, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — elsewhere,
the structure rescues on the major AS FOUND (lean4#15351; a `String` literal
skips them) produced a constructor application: that is the major. -/
theorem prepareMajorFueled_nkCtor {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x mE : Expr}
    (hk : ConLeche.recRuleK rules' = false)
    (h0 : (if x.isStrLit then .ok x
      else ConLeche.majorToCtorFueled mode env F d cn rules' x : CheckM Expr)
        = .ok mE)
    (hc : ConLeche.isCtorApp env mE = true) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok mE := by
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk,
    Bool.false_eq_true, ite_false]
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at h0
    have e0 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
        rules' x = .ok mE := h0
    simp only [Bool.false_eq_true, ite_false, e0, hc, ite_true, bind,
      Except.bind]
    rfl
  · simp only [hs, ite_true] at h0
    cases h0
    simp only [ite_true, hc, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — elsewhere,
no constructor yet: `whnf`, the literal conversion, then the rescues once
more on the reduct. -/
theorem prepareMajorFueled_nk {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x mE m1 m2 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = false)
    (h0 : (if x.isStrLit then .ok x
      else ConLeche.majorToCtorFueled mode env F d cn rules' x : CheckM Expr)
        = .ok mE)
    (hc : ConLeche.isCtorApp env mE = false)
    (h1 : ConLeche.whnf mode env F d mE = .ok m1)
    (h2 : ConLeche.litMajorToCtorFueled mode env F d m1 = .ok m2)
    (h3 : ConLeche.majorToCtorFueled mode env F d cn rules' m2 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : (ConLeche.pureFns mode env F).whnf d mE = .ok m1 := h1
  have e2 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m1 =
      .ok m2 := h2
  have e3 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' m2 = .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk,
    Bool.false_eq_true, ite_false]
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at h0
    have e0 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
        rules' x = .ok mE := h0
    simp only [Bool.false_eq_true, ite_false, e0, hc, e1, e2, e3, bind,
      Except.bind]
  · simp only [hs, ite_true] at h0
    cases h0
    simp only [ite_true, hc, Bool.false_eq_true, ite_false, e1, e2, e3, bind,
      Except.bind, pure, Except.pure]

/-! ## `majorToCtor`: the arena's three rescue blocks as named programs -/

/-- the twin's K rescue block (`majorToCtor`'s `rl.k` arm) -/
def majorKA (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule)
    (cvj : IConstantVal) (cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      let ustl ← viewLs ust
      if T' = T ∧ cvj.levelParams.length = ustl.length then do
        let targs ← getAppArgs coreWalkFuel tmaj
        if cnP ≤ targs.length then do
          let hd ← internE (.const rl.ctor ust)
          let fab ← mkAppN hd (targs.take cnP)
          if ← fabScopeOk depth fab major then do
            if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
              let irK ←
                if mode.verifiedChecks then ConRon.Arena.proofIrrel r fe depth fab major
                else pure true
              if irK then pure fab else pure major
            else pure major
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- the twin's η rescue block (`majorToCtor`'s `rl.eta` arm) -/
def majorEtaA (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (cvT : IConstantVal) (caps : IIndCaps)
    (T : NIdx) (major : EIdx) : AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      let ustl ← viewLs ust
      let targs ← getAppArgs coreWalkFuel tmaj
      let nz ← capsNeverZero cvT.levelParams ust caps
      if T' = T ∧ targs.length = caps.etaParams ∧
          ustl.length = cvT.levelParams.length ∧ nz = true then do
        let reserved ← reservedBasisNames
        if reserved.contains T = false ∧
            reserved.contains caps.etaCtor = false then do
          if ← towerSlotsAll fe T caps.etaFields then do
            let fabArgs ← etaFabArgsE T targs major caps.etaFields
            let hd ← internE (.const caps.etaCtor ust)
            let fab ← mkAppN hd fabArgs
            if ← fabScopeOk depth fab major then pure fab
            else pure major
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- the twin's `And` rescue block (`majorToCtor`'s pinned-`And` arm) -/
def majorAndA (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule)
    (cvj : IConstantVal) (cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      match ← viewLsLen ust with
      | none => failDanglingLs
      | some ustl =>
      let targs ← getAppArgs coreWalkFuel tmaj
      let ars ← andRescueSlots fe rl.ctor cnP ust
      if T' = T ∧ targs.length = cnP ∧
          cvj.levelParams.length = ustl ∧ ars = true then do
        let p0 ← internE (.proj T 0 major)
        let p1 ← internE (.proj T 1 major)
        let fabArgs := targs ++ [p0, p1]
        let hd ← internE (.const rl.ctor ust)
        let fab ← mkAppN hd fabArgs
        if ← fabScopeOk depth fab major then do
          if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
            let irA ←
              if mode.verifiedChecks then ConRon.Arena.proofIrrel r fe depth fab major
              else pure true
            if irA then pure fab else pure major
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- the twin's `majorToCtor` at a single rule, its three rescues named -/
theorem majorToCtor_one (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (c : NIdx) (rl : IRecRule) (major : EIdx) :
    ConRon.Arena.majorToCtor mode r fe depth c [rl] major = (do
      if ← isCtorApp fe major then pure major else
      match fe.find? rl.ctor with
      | some (.ctorInfo cvj cnP _cnF) => do
        let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
        if hh.tag == ETag.const then
          match ← view hh with
          | .const T _ =>
            match fe.find? T with
            | some (.indInfo cvT caps) =>
              if rl.k = true then majorKA mode r fe depth rl cvj cnP T major
              else if rl.eta = true then majorEtaA r fe depth cvT caps T major
              else do
                let an ← pinAnd
                if T = an then majorAndA mode r fe depth rl cvj cnP T major
                else pure major
            | _ => pure major
          | _ => pure major
        else pure major
      | _ => pure major) := rfl

/-! ## The K rescue -/

/-- `mtcK` past its two knot calls, as a function of the head-normalised type -/
def mtcKT (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major tmaj : Expr) :
    CheckM Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ cvj.levelParams.length = ust.length then
      if cnP ≤ tmaj.getAppArgs.length then
        let fab := Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)
        if fab.wscopedB d && fab.looseBVarsBounded 0 &&
            fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
          (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
          (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
          if rd then
            (if mode.verifiedChecks then
              ConLeche.proofIrrel (ConLeche.pureFns mode env F) d fab major
            else pure true) >>= fun r => if r then pure fab else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

theorem mtcK_eq (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    mtcK mode env F d rl cvj cnP T major =
      ((ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
       (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
       mtcKT mode env F d rl cvj cnP T major tmaj) := rfl

/-- the K fabrication -/
def kFab (rl : RecRule) (cnP : Nat) (tmaj : Expr) : Expr :=
  Expr.mkAppN (.const rl.ctor (exprConstLevels tmaj.getAppFn)) (tmaj.getAppArgs.take cnP)

def mtcKOp (mode : CheckMode) (env : Env) (d : Nat) (rl : RecRule) (cvj : ConstantVal)
    (cnP : Nat) (T : ConLeche.Name) (x : Expr) : Nat → CheckM Expr :=
  fun F => mtcK mode env F d rl cvj cnP T x

/-- the run of `mtcK` through its prefix: the tail at one merged fuel -/
theorem mtcK_runs {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj v : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (h3 : ∃ F₀, ∀ F, F₀ ≤ F → mtcKT mode env F d rl cvj cnP T x tmaj = .ok v) :
    Runs (mtcKOp mode env d rl cvj cnP T x) v := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨max F1 (max F2 F3), ?_⟩
  have e1 : (ConLeche.pureFns mode env (max F1 (max F2 F3))).inferIO d x = .ok tm :=
    ConLeche.inferTypeIO_mono (by omega) hF1
  have e2 : (ConLeche.pureFns mode env (max F1 (max F2 F3))).whnf d tm = .ok tmaj :=
    ConLeche.whnf_mono (by omega) hF2
  simp only [mtcKOp, mtcK_eq, e1, e2, bind, Except.bind]
  exact hF3 _ (by omega)

theorem mtcK_nohead {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : (exprTag tmaj.getAppFn == ETag.const) = false) :
    Runs (mtcKOp mode env d rl cvj cnP T x) x := by
  refine mtcK_runs h1 h2 ⟨0, fun F _ => ?_⟩
  unfold mtcKT
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | (simp [exprTag] at hg)
grind_pattern [bridge_grind] mtcK_nohead =>
  mtcKOp mode env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode env) d x tm,
    RunE (ConLeche.whnf mode env) d tm tmaj

theorem mtcKT_const {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tmaj : Expr}
    (hg : exprTag tmaj.getAppFn = ETag.const) :
    mtcKT mode env F d rl cvj cnP T x tmaj =
      if exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length then
        if cnP ≤ tmaj.getAppArgs.length then
          if scopeOkFn d (kFab rl cnP tmaj) x then
            (ConLeche.pureFns mode env F).inferIO d (kFab rl cnP tmaj) >>= fun tfab =>
            (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
            if rd then
              (if mode.verifiedChecks then
                ConLeche.proofIrrel (ConLeche.pureFns mode env F) d (kFab rl cnP tmaj) x
              else pure true) >>= fun r => if r then pure (kFab rl cnP tmaj) else pure x
            else pure x
          else pure x
        else pure x
      else pure x := by
  unfold mtcKT kFab scopeOkFn
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | exact absurd hg (by simp only [exprTag]; decide)

theorem mtcK_guard {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : ¬ (exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)) :
    Runs (mtcKOp mode env d rl cvj cnP T x) x := by
  refine mtcK_runs h1 h2 ⟨0, fun F _ => ?_⟩
  rw [mtcKT_const hg]
  by_cases a : exprConstName tmaj.getAppFn = T ∧
      cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length
  · rw [ite_eq_left a]
    by_cases b : cnP ≤ tmaj.getAppArgs.length
    · rw [ite_eq_left b]
      have c : scopeOkFn d (kFab rl cnP tmaj) x = false := by
        cases h : scopeOkFn d (kFab rl cnP tmaj) x
        · rfl
        · exact absurd ⟨a.1, a.2, b, h⟩ hc
      rw [c]; rfl
    · rw [ite_eq_right b]; rfl
  · rw [ite_eq_right a]; rfl
grind_pattern [bridge_grind] mtcK_guard =>
  mtcKOp mode env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode env) d x tm,
    RunE (ConLeche.whnf mode env) d tm tmaj

theorem mtcK_fireR {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b5 b6 : Bool}
    (hμ : mode.verifiedChecks = true)
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)
    (h4 : RunE (ConLeche.inferTypeIO mode env) d (kFab rl cnP tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore mode env) d tmaj tf b5)
    (h6 : b5 = true → Runs (proofIrrelOp mode env d (kFab rl cnP tmaj) x) b6) :
    Runs (mtcKOp mode env d rl cvj cnP T x) (if b5 && b6 then kFab rl cnP tmaj else x) := by
  obtain ⟨F4, hF4⟩ := h4
  obtain ⟨F5, hF5⟩ := h5
  have h6' : ∃ F6, b5 = true →
      ConLeche.proofIrrelFueled mode env F6 d (kFab rl cnP tmaj) x = .ok b6 := by
    cases b5
    · exact ⟨0, nofun⟩
    · obtain ⟨F6, hF6⟩ := h6 rfl; exact ⟨F6, fun _ => hF6⟩
  obtain ⟨F6, hF6⟩ := h6'
  refine mtcK_runs h1 h2 ⟨max F4 (max F5 F6), fun F hF => ?_⟩
  obtain ⟨ha, hb, hb', hs⟩ := hc
  rw [mtcKT_const hg, ite_eq_left ⟨ha, hb⟩, ite_eq_left hb', ite_eq_left hs]
  have e4 : (ConLeche.pureFns mode env F).inferIO d (kFab rl cnP tmaj) = .ok tf :=
    ConLeche.inferTypeIO_mono (by omega) hF4
  have e5 : (ConLeche.pureFns mode env F).defeq d tmaj tf = .ok b5 :=
    ConLeche.isDefEqCore_mono (by omega) hF5
  simp only [e4, e5, bind, Except.bind]
  cases b5
  · rfl
  · have e6 : ConLeche.proofIrrel (ConLeche.pureFns mode env F) d (kFab rl cnP tmaj) x = .ok b6 :=
      proofIrrelFueled_mono (by omega) (hF6 rfl)
    simp only [ite_true, hμ, e6]
    cases b6 <;> rfl

theorem mtcK_df {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr}
    (hμ : mode.verifiedChecks = true)
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)
    (h4 : RunE (ConLeche.inferTypeIO mode env) d (kFab rl cnP tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore mode env) d tmaj tf false) :
    Runs (mtcKOp mode env d rl cvj cnP T x) x :=
  mtcK_fireR (b6 := false) hμ h1 h2 hg hc h4 h5 nofun
grind_pattern [bridge_grind] mtcK_df =>
  mtcKOp mode env d rl cvj cnP T x, RunE (ConLeche.whnf mode env) d tm tmaj,
    SimV (ConLeche.isDefEqCore mode env) d tmaj tf false

theorem mtcK_pi {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b6 : Bool}
    (hμ : mode.verifiedChecks = true)
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)
    (h4 : RunE (ConLeche.inferTypeIO mode env) d (kFab rl cnP tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore mode env) d tmaj tf true)
    (h6 : Runs (proofIrrelOp mode env d (kFab rl cnP tmaj) x) b6) :
    Runs (mtcKOp mode env d rl cvj cnP T x) (if b6 then kFab rl cnP tmaj else x) := by
  have := mtcK_fireR (b5 := true) hμ h1 h2 hg hc h4 h5 (fun _ => h6)
  simpa using this
grind_pattern [bridge_grind] mtcK_pi =>
  mtcKOp mode env d rl cvj cnP T x, RunE (ConLeche.whnf mode env) d tm tmaj,
    SimV (ConLeche.isDefEqCore mode env) d tmaj tf true,
    Runs (proofIrrelOp mode env d (kFab rl cnP tmaj) x) b6

/-- two name handles of one store with one denotation are one handle -/
theorem majorK_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn) :
    ⦃fun s => s = s₁⦄
      majorKA mode (coreKnot mode fe id fuel) fe d rl icvj cnP T major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (mtcKOp mode env d rl' dcvj cnP Tn x) d s'.store r; ⊤⦄ := by
  have hrc := (rule_denote hrl').2.2.1
  sym (gen := 16) only [bridge_grind, kFab, ← viewOK_const] =>
    vcgen [majorKA, hsim.inferIOS, hsim.whnfS, ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec,
      internE_specC (mode := mode) (env := env) (fe := fe),
      mkAppN_specC (mode := mode) (env := env) (fe := fe),
      fabScopeOk_specS (mode := mode) (env := env) (fe := fe), hsim.defeqS,
      proofIrrel_specS hsim] <;> finish

/-! ## The η rescue -/

def mtcEtaT (env : Env) (d : Nat) (cvT : ConstantVal) (caps : IndCaps) (T : ConLeche.Name)
    (major tmaj : Expr) : CheckM Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        ConLeche.capsNeverZero cvT.levelParams ust caps = true ∧
        ConLeche.reservedBasisNames.contains T = false ∧
        ConLeche.reservedBasisNames.contains caps.etaCtor = false ∧
        ConLeche.towerSlotsAll env T caps.etaFields = true then
      let fab := Expr.mkAppN (.const caps.etaCtor ust)
        (ConLeche.etaFabArgsE T tmaj.getAppArgs major caps.etaFields)
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        pure fab
      else pure major
    else pure major
  | _ => pure major

theorem mtcEta_eq (mode : CheckMode) (env : Env) (F d : Nat) (cvT : ConstantVal)
    (caps : IndCaps) (T : ConLeche.Name) (major : Expr) :
    mtcEta mode env F d cvT caps T major =
      ((ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
       (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
       mtcEtaT env d cvT caps T major tmaj) := rfl

/-- the η fabrication -/
def etaFab (caps : IndCaps) (T : ConLeche.Name) (x tmaj : Expr) : Expr :=
  Expr.mkAppN (.const caps.etaCtor (exprConstLevels tmaj.getAppFn))
    (ConLeche.etaFabArgsE T tmaj.getAppArgs x caps.etaFields)

/-- the η rescue's guards, at the head-normalised type -/
def etaRescueOk (env : Env) (d : Nat) (cvT : ConstantVal) (caps : IndCaps) (T : ConLeche.Name)
    (x tmaj : Expr) : Bool :=
  exprConstName tmaj.getAppFn == T && tmaj.getAppArgs.length == caps.etaParams &&
    (exprConstLevels tmaj.getAppFn).length == cvT.levelParams.length &&
    ConLeche.capsNeverZero cvT.levelParams (exprConstLevels tmaj.getAppFn) caps &&
    !ConLeche.reservedBasisNames.contains T &&
    !ConLeche.reservedBasisNames.contains caps.etaCtor &&
    ConLeche.towerSlotsAll env T caps.etaFields &&
    scopeOkFn d (etaFab caps T x tmaj) x

def mtcEtaOp (mode : CheckMode) (env : Env) (d : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (T : ConLeche.Name) (x : Expr) : Nat → CheckM Expr :=
  fun F => mtcEta mode env F d cvT caps T x

theorem mtcEta_runs {d : Nat} {cvT : ConstantVal} {caps : IndCaps}
    {T : ConLeche.Name} {x tm tmaj v : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (h3 : mtcEtaT env d cvT caps T x tmaj = .ok v) :
    Runs (mtcEtaOp mode env d cvT caps T x) v := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  refine ⟨max F1 F2, ?_⟩
  have e1 : (ConLeche.pureFns mode env (max F1 F2)).inferIO d x = .ok tm :=
    ConLeche.inferTypeIO_mono (by omega) hF1
  have e2 : (ConLeche.pureFns mode env (max F1 F2)).whnf d tm = .ok tmaj :=
    ConLeche.whnf_mono (by omega) hF2
  simp only [mtcEtaOp, mtcEta_eq, e1, e2, bind, Except.bind, h3]

theorem mtcEtaT_nohead {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {T : ConLeche.Name}
    {x tmaj : Expr} (hg : (exprTag tmaj.getAppFn == ETag.const) = false) :
    mtcEtaT env d cvT caps T x tmaj = .ok x := by
  unfold mtcEtaT
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | (simp [exprTag] at hg)

theorem mtcEtaT_const {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {T : ConLeche.Name}
    {x tmaj : Expr} (hg : exprTag tmaj.getAppFn = ETag.const) :
    mtcEtaT env d cvT caps T x tmaj =
      if etaRescueOk env d cvT caps T x tmaj then .ok (etaFab caps T x tmaj) else .ok x := by
  unfold mtcEtaT etaRescueOk etaFab scopeOkFn
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first
    | exact absurd hg (by simp only [exprTag]; decide)
    | skip
  simp only [exprConstName, exprConstLevels]
  split <;> rename_i h1 <;> simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1 ⊢
  · split <;> rename_i h2
    · rw [ite_eq_left (by simp_all)]; rfl
    · rw [ite_eq_right (by simp_all)]; rfl
  · rw [ite_eq_right (by simp_all)]; rfl

theorem mtcEta_nohead {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {T : ConLeche.Name}
    {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : (exprTag tmaj.getAppFn == ETag.const) = false) :
    Runs (mtcEtaOp mode env d cvT caps T x) x :=
  mtcEta_runs h1 h2 (mtcEtaT_nohead hg)
grind_pattern [bridge_grind] mtcEta_nohead =>
  mtcEtaOp mode env d cvT caps T x, RunE (ConLeche.inferTypeIO mode env) d x tm,
    RunE (ConLeche.whnf mode env) d tm tmaj

theorem mtcEta_no {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {T : ConLeche.Name}
    {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hn : etaRescueOk env d cvT caps T x tmaj = false) :
    Runs (mtcEtaOp mode env d cvT caps T x) x :=
  mtcEta_runs h1 h2 (by rw [mtcEtaT_const hg, hn]; rfl)
grind_pattern [bridge_grind] mtcEta_no =>
  mtcEtaOp mode env d cvT caps T x, RunE (ConLeche.inferTypeIO mode env) d x tm,
    RunE (ConLeche.whnf mode env) d tm tmaj

theorem mtcEta_fab {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {T : ConLeche.Name}
    {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hy : etaRescueOk env d cvT caps T x tmaj = true) :
    Runs (mtcEtaOp mode env d cvT caps T x) (etaFab caps T x tmaj) :=
  mtcEta_runs h1 h2 (by rw [mtcEtaT_const hg, hy]; rfl)
grind_pattern [bridge_grind] mtcEta_fab =>
  mtcEtaOp mode env d cvT caps T x, RunE (ConLeche.inferTypeIO mode env) d x tm,
    RunE (ConLeche.whnf mode env) d tm tmaj

/-- `capsNeverZero`'s answer at optional subjects -/
def CapsNZ (r : Bool) : Option (List ConLeche.Name) → Option (List Level) → Option IndCaps → Prop
  | some ks, some vs, some c => r = ConLeche.capsNeverZero ks vs c
  | _, _, _ => True

@[bridge_grind =] theorem CapsNZ.some_eq (r : Bool) (ks : List ConLeche.Name) (vs : List Level)
    (c : IndCaps) : CapsNZ r (some ks) (some vs) (some c) = (r = ConLeche.capsNeverZero ks vs c) :=
  rfl

theorem capsNeverZero_specS (s₀ : AState) (lps : List NIdx) (us : LsIdx)
    (icaps : IIndCaps) (hok : CheckOK mode env fe s₀)
    (hks : (Frontend.denoteNList s₀.store.ns lps).isSome = true)
    (hvs : (denoteLs s₀.store.lss us).isSome = true)
    (hcaps : (Frontend.denoteCaps s₀.store icaps).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.capsNeverZero lps us icaps
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        CapsNZ r (Frontend.denoteNList s₀.store.ns lps) (denoteLs s₀.store.lss us)
          (Frontend.denoteCaps s₀.store icaps); ⊤⦄ := by
  obtain ⟨ks, h1⟩ := Option.isSome_iff_exists.mp hks
  obtain ⟨vs, h2⟩ := Option.isSome_iff_exists.mp hvs
  obtain ⟨c, h3⟩ := Option.isSome_iff_exists.mp hcaps
  rw [h1, h2, h3]
  exact capsNeverZero_spec s₀ lps us icaps ks vs c hok h1 h2 h3

/-- con-leche's η spine arguments at a fixed family, major and field count -/
def etaArgsFn (T : ConLeche.Name) (x : Expr) (nF : Nat) (ts : List Expr) : List Expr :=
  ConLeche.etaFabArgsE T ts x nF

theorem etaFabArgsE_specS (s₀ : AState) (T : NIdx) (targs : List EIdx) (major : EIdx) (nF : Nat)
    (Tn : ConLeche.Name) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hts : (Frontend.denoteEList s₀.store targs).isSome = true)
    (hx : denoteE s₀.store major = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaFabArgsE T targs major nF
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        MapRel (etaArgsFn Tn x nF) (Frontend.denoteEList s₀.store targs)
          (Frontend.denoteEList s'.store r); ⊤⦄ := by
  obtain ⟨ts, h1⟩ := Option.isSome_iff_exists.mp hts
  rw [h1]
  exact etaFabArgsE_spec s₀ T targs major nF Tn ts x hok hT h1 hx

theorem majorEta_spec {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (major : EIdx) (x : Expr)
    (icvT : IConstantVal) (dcvT : ConstantVal) (icaps : IIndCaps)
    (dcaps : IndCaps) (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁)
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvT : Frontend.denoteCV s₁.store icvT = some dcvT)
    (hcaps : Frontend.denoteCaps s₁.store icaps = some dcaps)
    (hT : denoteN s₁.store.ns T = some Tn) :
    ⦃fun s => s = s₁⦄
      majorEtaA (coreKnot mode fe id fuel) fe d icvT icaps T major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (mtcEtaOp mode env d dcvT dcaps Tn x) d s'.store r; ⊤⦄ := by
  obtain ⟨_, hctor, hep, hef, _⟩ := denoteCaps_fields hcaps
  sym (gen := 16) only [bridge_grind, etaFab, etaRescueOk, etaArgsFn, ← viewOK_const] =>
    vcgen [majorEtaA, hsim.inferIOS, hsim.whnfS, ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec,
      capsNeverZero_specS (mode := mode) (env := env) (fe := fe),
      reservedBasisNames_spec (mode := mode) (env := env) (fe := fe),
      towerSlotsAll_spec (mode := mode) (env := env) (fe := fe) (Tn := Tn),
      etaFabArgsE_specS (mode := mode) (env := env) (fe := fe) (Tn := Tn) (x := x),
      internE_specC (mode := mode) (env := env) (fe := fe),
      mkAppN_specC (mode := mode) (env := env) (fe := fe),
      fabScopeOk_specS (mode := mode) (env := env) (fe := fe)] <;> finish

/-! ## The `And` rescue -/

def mtcAndT (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major tmaj : Expr) :
    CheckM Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        ConLeche.andRescueSlots env rl.ctor cnP ust = true then
      let fab := Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        (ConLeche.pureFns mode env F).inferIO d fab >>= fun tfab =>
        (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
        if rd then
          (if mode.verifiedChecks then
            ConLeche.proofIrrel (ConLeche.pureFns mode env F) d fab major
          else pure true) >>= fun r => if r then pure fab else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

theorem mtcAnd_eq (mode : CheckMode) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    mtcAnd mode env F d rl cvj cnP T major =
      ((ConLeche.pureFns mode env F).inferIO d major >>= fun tm =>
       (ConLeche.pureFns mode env F).whnf d tm >>= fun tmaj =>
       mtcAndT mode env F d rl cvj cnP T major tmaj) := rfl

/-- the `And` fabrication -/
def andFab (rl : RecRule) (T : ConLeche.Name) (x tmaj : Expr) : Expr :=
  Expr.mkAppN (.const rl.ctor (exprConstLevels tmaj.getAppFn))
    (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])

/-- the `And` rescue's syntactic guards and scope check -/
def andRescueOk (env : Env) (d : Nat) (rl : RecRule) (cvj : ConstantVal) (cnP : Nat)
    (T : ConLeche.Name) (x tmaj : Expr) : Bool :=
  exprConstName tmaj.getAppFn == T && tmaj.getAppArgs.length == cnP &&
    cvj.levelParams.length == (exprConstLevels tmaj.getAppFn).length &&
    ConLeche.andRescueSlots env rl.ctor cnP (exprConstLevels tmaj.getAppFn) &&
    scopeOkFn d (andFab rl T x tmaj) x

def mtcAndOp (mode : CheckMode) (env : Env) (d : Nat) (rl : RecRule) (cvj : ConstantVal)
    (cnP : Nat) (T : ConLeche.Name) (x : Expr) : Nat → CheckM Expr :=
  fun F => mtcAnd mode env F d rl cvj cnP T x

theorem mtcAnd_runs {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj v : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (h3 : ∃ F₀, ∀ F, F₀ ≤ F → mtcAndT mode env F d rl cvj cnP T x tmaj = .ok v) :
    Runs (mtcAndOp mode env d rl cvj cnP T x) v := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨max F1 (max F2 F3), ?_⟩
  have e1 : (ConLeche.pureFns mode env (max F1 (max F2 F3))).inferIO d x = .ok tm :=
    ConLeche.inferTypeIO_mono (by omega) hF1
  have e2 : (ConLeche.pureFns mode env (max F1 (max F2 F3))).whnf d tm = .ok tmaj :=
    ConLeche.whnf_mono (by omega) hF2
  simp only [mtcAndOp, mtcAnd_eq, e1, e2, bind, Except.bind]
  exact hF3 _ (by omega)

theorem mtcAndT_const {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tmaj : Expr}
    (hg : exprTag tmaj.getAppFn = ETag.const) :
    mtcAndT mode env F d rl cvj cnP T x tmaj =
      if andRescueOk env d rl cvj cnP T x tmaj then
        (ConLeche.pureFns mode env F).inferIO d (andFab rl T x tmaj) >>= fun tfab =>
        (ConLeche.pureFns mode env F).defeq d tmaj tfab >>= fun rd =>
        if rd then
          (if mode.verifiedChecks then
            ConLeche.proofIrrel (ConLeche.pureFns mode env F) d (andFab rl T x tmaj) x
          else pure true) >>= fun r => if r then pure (andFab rl T x tmaj) else pure x
        else pure x
      else pure x := by
  unfold mtcAndT andRescueOk andFab scopeOkFn
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first
    | exact absurd hg (by simp only [exprTag]; decide)
    | skip
  rename_i T' ust
  simp only [exprConstName, exprConstLevels]
  by_cases h1 : T' = T ∧ tmaj.getAppArgs.length = cnP ∧ cvj.levelParams.length = ust.length ∧
      ConLeche.andRescueSlots env rl.ctor cnP ust = true
  · rw [ite_eq_left h1]
    obtain ⟨a, b, c, e⟩ := h1
    subst a b
    simp only [beq_self_eq_true, c, e, Bool.true_and]
  · rw [ite_eq_right h1]
    have hb : (T' == T && tmaj.getAppArgs.length == cnP &&
        cvj.levelParams.length == ust.length &&
        ConLeche.andRescueSlots env rl.ctor cnP ust) = false :=
      Bool.eq_false_iff.mpr fun h => h1 (by
        simp only [Bool.and_eq_true, beq_iff_eq] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    simp only [hb, Bool.false_and, Bool.false_eq_true, ite_false]

theorem mtcAnd_nohead {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : (exprTag tmaj.getAppFn == ETag.const) = false) :
    Runs (mtcAndOp mode env d rl cvj cnP T x) x := by
  refine mtcAnd_runs h1 h2 ⟨0, fun F _ => ?_⟩
  unfold mtcAndT
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | (simp [exprTag] at hg)
grind_pattern [bridge_grind] mtcAnd_nohead =>
  mtcAndOp mode env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode env) d x tm,
    RunE (ConLeche.whnf mode env) d tm tmaj

theorem mtcAnd_guard {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = false) :
    Runs (mtcAndOp mode env d rl cvj cnP T x) x := by
  refine mtcAnd_runs h1 h2 ⟨0, fun F _ => ?_⟩
  rw [mtcAndT_const hg, hc]; rfl
grind_pattern [bridge_grind] mtcAnd_guard =>
  mtcAndOp mode env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode env) d x tm,
    RunE (ConLeche.whnf mode env) d tm tmaj

theorem mtcAnd_fireR {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b5 b6 : Bool}
    (hμ : mode.verifiedChecks = true)
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = true)
    (h4 : RunE (ConLeche.inferTypeIO mode env) d (andFab rl T x tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore mode env) d tmaj tf b5)
    (h6 : b5 = true → Runs (proofIrrelOp mode env d (andFab rl T x tmaj) x) b6) :
    Runs (mtcAndOp mode env d rl cvj cnP T x) (if b5 && b6 then andFab rl T x tmaj else x) := by
  obtain ⟨F4, hF4⟩ := h4
  obtain ⟨F5, hF5⟩ := h5
  have h6' : ∃ F6, b5 = true →
      ConLeche.proofIrrelFueled mode env F6 d (andFab rl T x tmaj) x = .ok b6 := by
    cases b5
    · exact ⟨0, nofun⟩
    · obtain ⟨F6, hF6⟩ := h6 rfl; exact ⟨F6, fun _ => hF6⟩
  obtain ⟨F6, hF6⟩ := h6'
  refine mtcAnd_runs h1 h2 ⟨max F4 (max F5 F6), fun F hF => ?_⟩
  rw [mtcAndT_const hg, hc]
  have e4 : (ConLeche.pureFns mode env F).inferIO d (andFab rl T x tmaj) = .ok tf :=
    ConLeche.inferTypeIO_mono (by omega) hF4
  have e5 : (ConLeche.pureFns mode env F).defeq d tmaj tf = .ok b5 :=
    ConLeche.isDefEqCore_mono (by omega) hF5
  simp only [e4, e5, bind, Except.bind, ite_true]
  cases b5
  · rfl
  · have e6 : ConLeche.proofIrrel (ConLeche.pureFns mode env F) d (andFab rl T x tmaj) x =
        .ok b6 := proofIrrelFueled_mono (by omega) (hF6 rfl)
    simp only [ite_true, hμ, e6]
    cases b6 <;> rfl

theorem mtcAnd_df {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr}
    (hμ : mode.verifiedChecks = true)
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = true)
    (h4 : RunE (ConLeche.inferTypeIO mode env) d (andFab rl T x tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore mode env) d tmaj tf false) :
    Runs (mtcAndOp mode env d rl cvj cnP T x) x :=
  mtcAnd_fireR (b6 := false) hμ h1 h2 hg hc h4 h5 nofun
grind_pattern [bridge_grind] mtcAnd_df =>
  mtcAndOp mode env d rl cvj cnP T x, RunE (ConLeche.whnf mode env) d tm tmaj,
    SimV (ConLeche.isDefEqCore mode env) d tmaj tf false

theorem mtcAnd_pi {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b6 : Bool}
    (hμ : mode.verifiedChecks = true)
    (h1 : RunE (ConLeche.inferTypeIO mode env) d x tm)
    (h2 : RunE (ConLeche.whnf mode env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = true)
    (h4 : RunE (ConLeche.inferTypeIO mode env) d (andFab rl T x tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore mode env) d tmaj tf true)
    (h6 : Runs (proofIrrelOp mode env d (andFab rl T x tmaj) x) b6) :
    Runs (mtcAndOp mode env d rl cvj cnP T x) (if b6 then andFab rl T x tmaj else x) := by
  have := mtcAnd_fireR (b5 := true) hμ h1 h2 hg hc h4 h5 (fun _ => h6)
  simpa using this
grind_pattern [bridge_grind] mtcAnd_pi =>
  mtcAndOp mode env d rl cvj cnP T x, RunE (ConLeche.whnf mode env) d tm tmaj,
    SimV (ConLeche.isDefEqCore mode env) d tmaj tf true,
    Runs (proofIrrelOp mode env d (andFab rl T x tmaj) x) b6

/-- `andRescueSlots`'s answer at the level list's denotation -/
def AndSlotsAns (env : Env) (cn : ConLeche.Name) (nP : Nat) (r : Bool) :
    Option (List Level) → Prop
  | some ls => r = ConLeche.andRescueSlots env cn nP ls
  | none => True

@[bridge_grind =] theorem AndSlotsAns.some_eq (cn : ConLeche.Name) (nP : Nat) (r : Bool)
    (ls : List Level) :
    AndSlotsAns env cn nP r (some ls) = (r = ConLeche.andRescueSlots env cn nP ls) := rfl

theorem andRescueSlots_specS (s₀ : AState) (ctor : NIdx) (nP : Nat) (ust : LsIdx)
    (cn : ConLeche.Name) (hok : CheckOK mode env fe s₀)
    (hc : denoteN s₀.store.ns ctor = some cn) (hus : (denoteLs s₀.store.lss ust).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.andRescueSlots fe ctor nP ust
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        AndSlotsAns env cn nP r (denoteLs s₀.store.lss ust); ⊤⦄ := by
  obtain ⟨ls, h1⟩ := Option.isSome_iff_exists.mp hus
  rw [h1]
  exact andRescueSlots_spec s₀ ctor nP ust cn ls hok hc h1

theorem majorAnd_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn) :
    ⦃fun s => s = s₁⦄
      majorAndA mode (coreKnot mode fe id fuel) fe d rl icvj cnP T major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (mtcAndOp mode env d rl' dcvj cnP Tn x) d s'.store r; ⊤⦄ := by
  have hrc := (rule_denote hrl').2.2.1
  sym (gen := 16) only [bridge_grind, -denoteEList_cons_ans, -denoteEView, denoteEView_proj,
      denoteEView_const, andFab, andRescueOk, denoteEList_append_eq,
      denoteEList_cons_eq, ← viewOK_const] =>
    vcgen [majorAndA, hsim.inferIOS, hsim.whnfS, ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec,
      andRescueSlots_specS (mode := mode) (env := env) (fe := fe) (cn := rl'.ctor),
      internE_specC (mode := mode) (env := env) (fe := fe),
      mkAppN_specC (mode := mode) (env := env) (fe := fe),
      fabScopeOk_specS (mode := mode) (env := env) (fe := fe), hsim.defeqS,
      proofIrrel_specS hsim] <;> finish

/-! ## `litMajorToCtor` -/

/-- the twin's `litMajorToCtor` with its literal match one constructor deep -/
theorem litMajorToCtor_split (r : CoreFnsA) (d : Nat) (h : EIdx) :
    ConRon.Arena.litMajorToCtor r fe d h =
      (if h.tag == ETag.lit then do
        let v ← view h
        if litIsStr (nodeLit v) && v.tagOf == ETag.lit then do
          if ← strLitSupported fe then do
            let c ← strLitToConstructor (litStr (nodeLit v))
            r.whnf d c
          else pure h
        else litToCtorIfNat fe h
      else litToCtorIfNat fe h) := by
  unfold ConRon.Arena.litMajorToCtor
  split
  · congr 1; funext v
    cases v <;> try rfl
    rename_i l; cases l <;> rfl
  · rfl

def litMajorOp (mode : CheckMode) (env : Env) (d : Nat) (x : Expr) : Nat → CheckM Expr :=
  fun F => ConLeche.litMajorToCtorFueled mode env F d x

theorem litMajor_nstr {d : Nat} {x : Expr} (h : x.isStrLit = false) :
    Runs (litMajorOp mode env d x) (ConLeche.litToCtorIfNat env x) :=
  ⟨0, litMajorToCtorFueled_nstr (fun s hs => by subst hs; cases h)⟩
grind_pattern [bridge_grind] litMajor_nstr => litMajorOp mode env d x

theorem litMajor_unsup {d : Nat} {x : Expr} (h : x.isStrLit = true)
    (hs : ConLeche.strLitSupported env = false) : Runs (litMajorOp mode env d x) x := by
  refine ⟨0, ?_⟩
  cases x with
  | lit l => cases l with
    | strVal s => simp [litMajorOp, ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hs]; rfl
    | natVal => cases h
  | _ => cases h
grind_pattern [bridge_grind] litMajor_unsup => litMajorOp mode env d x

theorem litMajor_str {d : Nat} {x v : Expr} (h : x.isStrLit = true)
    (hs : ConLeche.strLitSupported env = true)
    (hw : RunE (ConLeche.whnf mode env) d (ConLeche.strLitToConstructor (litStr (exprLit x))) v) :
    Runs (litMajorOp mode env d x) v := by
  obtain ⟨F, hF⟩ := hw
  refine ⟨F, ?_⟩
  cases x with
  | lit l => cases l with
    | strVal s =>
      simp only [litMajorOp, ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hs, ite_true]
      exact hF
    | natVal => cases h
  | _ => cases h
grind_pattern [bridge_grind] litMajor_str =>
  litMajorOp mode env d x, RunE (ConLeche.whnf mode env) d (ConLeche.strLitToConstructor (litStr (exprLit x))) v

theorem litMajorToCtor_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.litMajorToCtor (coreKnot mode fe id fuel) fe d h
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ SimEOp (litMajorOp mode env d x) d s'.store r; ⊤⦄ := by
  sym only [bridge_grind, isStrLit_eq, ConLeche.litToCtorIfNat_WScoped,
      strLitToConstructor_WScoped] =>
    vcgen [litMajorToCtor_split, strLitSupported_spec (mode := mode) (env := env) (fe := fe),
      strLitToConstructor_spec (mode := mode) (env := env) (fe := fe), hsim.whnfS,
      litToCtorIfNat_spec (x := x)] <;> finish

/-! ## `majorToCtor`'s pure side -/

def majorToCtorOp (mode : CheckMode) (env : Env) (d : Nat) (cn : ConLeche.Name)
    (rules : List RecRule) (x : Expr) : Nat → CheckM Expr :=
  fun F => ConLeche.majorToCtorFueled mode env F d cn rules x

/-- the constructor's family name, read off its stored type -/
def mtcFam (env : Env) (rl : RecRule) : ConLeche.Name :=
  exprConstName (cCtorVal (env.find? rl.ctor)).type.piResult.getAppFn

/-- the prefix every rescue shares: a stored constructor whose type ends in
a stored inductive -/
def mtcPrefixOk (env : Env) (rl : RecRule) : Bool :=
  cCtor? (env.find? rl.ctor) &&
    exprTag (cCtorVal (env.find? rl.ctor)).type.piResult.getAppFn == ETag.const &&
    cInd? (env.find? (mtcFam env rl))

theorem majorToCtorFueled_one {F d : Nat} {cn : ConLeche.Name} {rl : RecRule} {x : Expr}
    (hnc : ConLeche.isCtorApp env x = false) :
    ConLeche.majorToCtorFueled mode env F d cn [rl] x =
      if mtcPrefixOk env rl then
        if rl.k = true then
          mtcK mode env F d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
            (mtcFam env rl) x
        else if rl.eta = true then
          mtcEta mode env F d (cIndVal (env.find? (mtcFam env rl)))
            (cIndCaps (env.find? (mtcFam env rl))) (mtcFam env rl) x
        else if mtcFam env rl = ConLeche.andName then
          mtcAnd mode env F d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
            (mtcFam env rl) x
        else .ok x
      else .ok x := by
  unfold mtcPrefixOk mtcFam
  cases hf : env.find? rl.ctor with
  | none =>
    simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, cCtor?,
      Bool.false_eq_true, ite_false, Bool.false_and]; rfl
  | some ci =>
    cases ci with
    | ctorInfo cvj cnP cnF =>
      simp only [cCtor?, cCtorVal, cCtorNP, Bool.true_and]
      generalize hg : cvj.type.piResult.getAppFn = g
      cases g with
      | const T us =>
        simp only [exprTag, exprConstName, beq_self_eq_true, Bool.true_and]
        cases hT : env.find? T with
        | none =>
          simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, hg, hT, cInd?,
            Bool.false_eq_true, ite_false]; rfl
        | some ti =>
          cases ti with
          | indInfo cvT caps =>
            have := majorToCtorFueled_pre (F := F) (d := d) (cn := cn) (mode := mode) hnc hf hg hT
            simp only [cInd?, cIndVal, cIndCaps, ite_true]
            rw [this]; rfl
          | _ =>
            simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, hg, hT, cInd?,
              Bool.false_eq_true, ite_false]; rfl
      | _ =>
        simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, hg]
        first | rfl | (simp only [exprTag]; rfl)
    | _ =>
      simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, cCtor?,
        Bool.false_eq_true, ite_false, Bool.false_and]; rfl

theorem mtc_isCtor {d : Nat} {cn : ConLeche.Name} {rules : List RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = true) : Runs (majorToCtorOp mode env d cn rules x) x :=
  ⟨0, majorToCtorFueled_ctor (mode := mode) (cn := cn) (rules := rules) (d := d) h⟩
grind_pattern [bridge_grind] mtc_isCtor => majorToCtorOp mode env d cn rules x

theorem mtc_nil {d : Nat} {cn : ConLeche.Name} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) : Runs (majorToCtorOp mode env d cn [] x) x :=
  ⟨0, by
    show ConLeche.majorToCtorFueled mode env 0 d cn [] x = .ok x
    simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, Bool.false_eq_true,
      ite_false]; rfl⟩
grind_pattern [bridge_grind] mtc_nil => majorToCtorOp mode env d cn [] x

theorem mtc_many {d : Nat} {cn : ConLeche.Name} {a b : RecRule} {cs : List RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) :
    Runs (majorToCtorOp mode env d cn (a :: b :: cs) x) x :=
  ⟨0, by
    show ConLeche.majorToCtorFueled mode env 0 d cn (a :: b :: cs) x = .ok x
    simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, Bool.false_eq_true,
      ite_false]; rfl⟩
grind_pattern [bridge_grind] mtc_many => majorToCtorOp mode env d cn (a :: b :: cs) x

theorem mtc_skip {d : Nat} {cn : ConLeche.Name} {rl : RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = false) :
    Runs (majorToCtorOp mode env d cn [rl] x) x :=
  ⟨0, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, Bool.false_eq_true, ite_false]⟩
grind_pattern [bridge_grind] mtc_skip => majorToCtorOp mode env d cn [rl] x

theorem mtc_K {d : Nat} {cn : ConLeche.Name} {rl : RecRule} {x v : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : rl.k = true)
    (H : Runs (mtcKOp mode env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v) :
    Runs (majorToCtorOp mode env d cn [rl] x) v :=
  let ⟨F, hF⟩ := H
  ⟨F, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, ite_true]; exact hF⟩
grind_pattern [bridge_grind] mtc_K => majorToCtorOp mode env d cn [rl] x,
  Runs (mtcKOp mode env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v

theorem mtc_Eta {d : Nat} {cn : ConLeche.Name} {rl : RecRule} {x v : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : rl.k = false)
    (he : rl.eta = true)
    (H : Runs (mtcEtaOp mode env d (cIndVal (env.find? (mtcFam env rl)))
      (cIndCaps (env.find? (mtcFam env rl))) (mtcFam env rl) x) v) :
    Runs (majorToCtorOp mode env d cn [rl] x) v :=
  let ⟨F, hF⟩ := H
  ⟨F, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, he, ite_true,
    Bool.false_eq_true, ite_false]; exact hF⟩
grind_pattern [bridge_grind] mtc_Eta => majorToCtorOp mode env d cn [rl] x,
  Runs (mtcEtaOp mode env d (cIndVal (env.find? (mtcFam env rl)))
      (cIndCaps (env.find? (mtcFam env rl))) (mtcFam env rl) x) v

theorem mtc_And {d : Nat} {cn : ConLeche.Name} {rl : RecRule} {x v : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : rl.k = false)
    (he : rl.eta = false) (hT : mtcFam env rl = ConLeche.andName)
    (H : Runs (mtcAndOp mode env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v) :
    Runs (majorToCtorOp mode env d cn [rl] x) v :=
  let ⟨F, hF⟩ := H
  ⟨F, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, he, ite_true,
    Bool.false_eq_true, ite_false]; rw [ite_eq_left hT]; exact hF⟩
grind_pattern [bridge_grind] mtc_And => majorToCtorOp mode env d cn [rl] x,
  Runs (mtcAndOp mode env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v

theorem mtc_none {d : Nat} {cn : ConLeche.Name} {rl : RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : rl.k = false)
    (he : rl.eta = false) (hT : ¬ mtcFam env rl = ConLeche.andName) :
    Runs (majorToCtorOp mode env d cn [rl] x) x :=
  ⟨0, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, he, ite_true,
    Bool.false_eq_true, ite_false]; rw [ite_eq_right hT]⟩
grind_pattern [bridge_grind] mtc_none => majorToCtorOp mode env d cn [rl] x

theorem majorToCtor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.majorToCtor mode (coreKnot mode fe id fuel) fe d c rules major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ SimEOp (majorToCtorOp mode env d cn rules' x) d s'.store r; ⊤⦄ := by
  match rules, rules', hr with
  | [], rules', hr =>
    obtain rfl : rules' = [] := by simpa [Frontend.denoteRules] using hr.symm
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.majorToCtor, isCtorApp_spec (mode := mode) (env := env) (x := x)] <;> finish
  | [rl], rules', hr =>
    obtain ⟨rl', hrl', rfl⟩ : ∃ rl', Frontend.denoteRule s₀.store rl = some rl' ∧
        rules' = [rl'] := by
      simp only [Frontend.denoteRules] at hr
      split at hr
      · rename_i y ys hy hys
        simp only [Option.some.injEq] at hys
        subst hys
        cases hr
        exact ⟨y, hy, rfl⟩
      · simp at hr
    obtain ⟨_, _, hrlc, _, _, hk', he'⟩ := rule_denote hrl'
    sym (gen := 10) only [bridge_grind, -iInd?, -iIndVal, -iIndCaps, -iCtor?, -iCtorVal, -iCtorNP,
        -iCtorNF, mtcPrefixOk, mtcFam] =>
      vcgen [majorToCtor_one, isCtorApp_spec (mode := mode) (env := env) (x := x), ExprOps.piResult_spec,
        ExprOps.getAppFn_spec, ConRon.Arena.pinAnd, pinAt_specE,
        majorK_spec hμ hsim (rl' := rl') (x := x) (dcvj := cCtorVal (env.find? rl'.ctor))
          (Tn := mtcFam env rl'),
        majorEta_spec hsim (x := x) (dcvT := cIndVal (env.find? (mtcFam env rl')))
          (dcaps := cIndCaps (env.find? (mtcFam env rl'))) (Tn := mtcFam env rl'),
        majorAnd_spec hμ hsim (rl' := rl') (x := x) (dcvj := cCtorVal (env.find? rl'.ctor))
          (Tn := mtcFam env rl')] <;> finish
  | r1 :: r2 :: rs, rules', hr =>
    obtain ⟨a, b, cs, rfl⟩ : ∃ a b cs, rules' = a :: b :: cs := by
      have hl := denoteRules_len hr
      match rules', hl with
      | a :: b :: cs, _ => exact ⟨a, b, cs, rfl⟩
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.majorToCtor, isCtorApp_spec (mode := mode) (env := env) (x := x)] <;> finish

/-! ## `isStrLit` -/

/-- the twin's `isStrLit` with its literal match one constructor deep -/
theorem isStrLit_split (h : EIdx) :
    ConRon.Arena.isStrLit h =
      (if h.tag == ETag.lit then do
        match ← viewLit h with
        | none => failDanglingE
        | some l => pure (litIsStr l)
      else pure false) := by
  unfold ConRon.Arena.isStrLit
  split
  · congr 1; funext o
    cases o with
    | none => rfl
    | some l => cases l <;> rfl
  · rfl

theorem isStrLit_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isStrLit h
    ⦃fun b s' => s' = s₀ ∧ b = x.isStrLit; ⊤⦄ := by
  sym only [bridge_grind, isStrLit_eq] =>
    vcgen [isStrLit_split, ConRon.Arena.viewLit] <;> finish

/-! ## `prepareMajor` -/

/-- `majorToCtor`'s answer at an optional subject -/
def MtcAns (mode : CheckMode) (env : Env) (d : Nat) (cn : ConLeche.Name) (rules : List RecRule)
    (st : EStore) (r : EIdx) : Option Expr → Prop
  | some x => SimEOp (majorToCtorOp mode env d cn rules x) d st r
  | none => True

@[bridge_grind =] theorem MtcAns.some_eq (d : Nat) (cn : ConLeche.Name) (rules : List RecRule)
    (st : EStore) (r : EIdx) (x : Expr) :
    MtcAns mode env d cn rules st r (some x) = SimEOp (majorToCtorOp mode env d cn rules x) d st r :=
  rfl

theorem majorToCtor_specS {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hw : DenWS d (denoteE s₀.store major)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.majorToCtor mode (coreKnot mode fe id fuel) fe d c rules major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ MtcAns mode env d cn rules' s'.store r (denoteE s₀.store major); ⊤⦄ := by
  cases hd : denoteE s₀.store major with
  | none => rw [hd] at hw; exact hw.elim
  | some x =>
    rw [hd] at hw
    exact majorToCtor_spec hμ hsim s₀ d c rules major cn rules' x hok hr hd hw

/-- `litMajorToCtor`'s answer at an optional subject -/
def LitAns (mode : CheckMode) (env : Env) (d : Nat) (st : EStore) (r : EIdx) :
    Option Expr → Prop
  | some x => SimEOp (litMajorOp mode env d x) d st r
  | none => True

@[bridge_grind =] theorem LitAns.some_eq (d : Nat) (st : EStore) (r : EIdx) (x : Expr) :
    LitAns mode env d st r (some x) = SimEOp (litMajorOp mode env d x) d st r := rfl

theorem litMajorToCtor_specS {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (hok : CheckOK mode env fe s₀)
    (hw : DenWS d (denoteE s₀.store h)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.litMajorToCtor (coreKnot mode fe id fuel) fe d h
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ LitAns mode env d s'.store r (denoteE s₀.store h); ⊤⦄ := by
  cases hd : denoteE s₀.store h with
  | none => rw [hd] at hw; exact hw.elim
  | some x =>
    rw [hd] at hw
    exact litMajorToCtor_spec hsim s₀ d h x hok hd hw

theorem isCtorApp_specS (s₀ : AState) (a : EIdx) (hok : CheckOK mode env fe s₀)
    (hda : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isCtorApp fe a
    ⦃fun r s' => s' = s₀ ∧ MapRelV (ConLeche.isCtorApp env) (denoteE s₀.store a) r; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hda
  rw [hx]
  exact isCtorApp_spec s₀ a x hok hx

def prepOp (mode : CheckMode) (env : Env) (d : Nat) (cn : ConLeche.Name) (rules : List RecRule)
    (x : Expr) : Nat → CheckM Expr :=
  fun F => ConLeche.prepareMajorFueled mode env F d cn rules x

theorem prep_k {d : Nat} {cn : ConLeche.Name} {rules : List RecRule} {x m1 m3 : Expr}
    (hk : ConLeche.recRuleK rules = true)
    (h1 : Runs (majorToCtorOp mode env d cn rules x) m1)
    (hc : ConLeche.isCtorApp env m1 = true) (h3 : Runs (litMajorOp mode env d m1) m3) :
    Runs (prepOp mode env d cn rules x) m3 :=
  let ⟨F1, hF1⟩ := h1
  let ⟨F3, hF3⟩ := h3
  ⟨max F1 F3, prepareMajorFueled_k hk (majorToCtorFueled_mono (Nat.le_max_left _ _) hF1) hc
    (litMajorToCtorFueled_mono (Nat.le_max_right _ _) hF3)⟩
grind_pattern [bridge_grind] prep_k => prepOp mode env d cn rules x,
  Runs (majorToCtorOp mode env d cn rules x) m1, Runs (litMajorOp mode env d m1) m3

theorem prep_kStuck {d : Nat} {cn : ConLeche.Name} {rules : List RecRule} {x m1 : Expr}
    (hk : ConLeche.recRuleK rules = true)
    (h1 : Runs (majorToCtorOp mode env d cn rules x) m1)
    (hc : ConLeche.isCtorApp env m1 = false) :
    Runs (prepOp mode env d cn rules x) m1 :=
  let ⟨F1, hF1⟩ := h1
  ⟨F1, prepareMajorFueled_kStuck hk hF1 hc⟩
grind_pattern [bridge_grind] prep_kStuck => prepOp mode env d cn rules x,
  Runs (majorToCtorOp mode env d cn rules x) m1

/-- the major as the structure rescues on it as found leave it (a `String`
literal skips them) -/
def PrepE (mode : CheckMode) (env : Env) (d : Nat) (cn : ConLeche.Name) (rules : List RecRule)
    (x mE : Expr) : Prop :=
  ∃ F, (if x.isStrLit then .ok x
    else ConLeche.majorToCtorFueled mode env F d cn rules x : CheckM Expr) = .ok mE

theorem prepE_str {d : Nat} {cn : ConLeche.Name} {rules : List RecRule} {x : Expr}
    (h : x.isStrLit = true) : PrepE mode env d cn rules x x := ⟨0, by simp [h]⟩
grind_pattern [bridge_grind] prepE_str => prepOp mode env d cn rules x

theorem prepE_mtc {d : Nat} {cn : ConLeche.Name} {rules : List RecRule} {x mE : Expr}
    (h : x.isStrLit = false) (h1 : Runs (majorToCtorOp mode env d cn rules x) mE) :
    PrepE mode env d cn rules x mE :=
  let ⟨F, hF⟩ := h1
  ⟨F, by simp only [h, Bool.false_eq_true, ite_false]; exact hF⟩
grind_pattern [bridge_grind] prepE_mtc => prepOp mode env d cn rules x,
  Runs (majorToCtorOp mode env d cn rules x) mE

theorem prep_nkCtor {d : Nat} {cn : ConLeche.Name} {rules : List RecRule} {x mE : Expr}
    (hk : ConLeche.recRuleK rules = false) (hE : PrepE mode env d cn rules x mE)
    (hc : ConLeche.isCtorApp env mE = true) :
    Runs (prepOp mode env d cn rules x) mE :=
  let ⟨F, hF⟩ := hE
  ⟨F, prepareMajorFueled_nkCtor hk hF hc⟩
grind_pattern [bridge_grind] prep_nkCtor => prepOp mode env d cn rules x, PrepE mode env d cn rules x mE

theorem prep_nk {d : Nat} {cn : ConLeche.Name} {rules : List RecRule} {x mE m1 m2 m3 : Expr}
    (hk : ConLeche.recRuleK rules = false) (hE : PrepE mode env d cn rules x mE)
    (hc : ConLeche.isCtorApp env mE = false)
    (h1 : RunE (ConLeche.whnf mode env) d mE m1)
    (h2 : Runs (litMajorOp mode env d m1) m2)
    (h3 : Runs (majorToCtorOp mode env d cn rules m2) m3) :
    Runs (prepOp mode env d cn rules x) m3 := by
  obtain ⟨F0, hF0⟩ := hE
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨max F0 (max F1 (max F2 F3)), prepareMajorFueled_nk hk ?_ hc
    (ConLeche.whnf_mono (by omega) hF1) (litMajorToCtorFueled_mono (by omega) hF2)
    (majorToCtorFueled_mono (by omega) hF3)⟩
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at hF0 ⊢
    exact majorToCtorFueled_mono (by omega) hF0
  · simp only [hs, ite_true] at hF0 ⊢
    exact hF0
grind_pattern [bridge_grind] prep_nk => prepOp mode env d cn rules x, PrepE mode env d cn rules x mE,
  RunE (ConLeche.whnf mode env) d mE m1, Runs (litMajorOp mode env d m1) m2,
  Runs (majorToCtorOp mode env d cn rules m2) m3

theorem prepareMajor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.prepareMajor mode (coreKnot mode fe id fuel) fe d c rules major
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ SimEOp (prepOp mode env d cn rules' x) d s'.store r; ⊤⦄ := by
  sym (gen := 16) only [bridge_grind, recRuleK_denote hr] =>
    vcgen [ConRon.Arena.prepareMajor, majorToCtor_specS hμ hsim (cn := cn) (rules' := rules'),
      isCtorApp_specS (mode := mode) (env := env), isStrLit_spec (mode := mode) (env := env) (fe := fe) (x := x),
      litMajorToCtor_specS hsim, hsim.whnfS] <;> finish


end ConRon.Bridge.Core
