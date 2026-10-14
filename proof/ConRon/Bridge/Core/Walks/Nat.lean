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
interned constant, where con-leche compares the values.

**The proofs are `vcgen` and `grind`**:
`sym only [bridge_grind] => vcgen [f, callee specs…] <;> finish` for every
walk.  What makes them `grind`-shaped:

* the index equality as an inverse function at each store (`idxOfName`,
  `idxOfLs`, `idxOfExpr`, `Bridge/Grind.lean` §6, registered here): a handle test
  `c == ns` is the name test by congruence closure, in both directions;
* every con-leche function the walks compare against as ONE unconditional
  equation over tags and projections (`rawNatLit?_eq`, `natOpStored_eq`,
  `natIndOk_eq`, `natZeroOk_eq`, `natSuccOk_eq`), and the environment's
  stored inductives and constructors as projections (`iInd?`/`cInd?`,
  `OptCI.at`), so that `grind` never splits a `match`;
* `reduceNat`'s answer named (`NatRed`), its fourteen exits as `grind`
  lemmas over the subject's projections (`exprFn`, `exprArg`), and the
  callees it reads at handles it has only just made in answer shape
  (`KnotSpec.whnfA`, `rawNatLit?_specA`, `constE_specA`);
* the binary guards as `Bool`s (`natBinOpB`, `WfNames`), so a fourteen-way
  name test is one equation per pin, not a disjunction.

One `grind` limitation is worked around rather than met: a `vcgen`
fall-through hypothesis with a NESTED constructor pattern
(`∀ n, v = .lit (.natVal n) → False`) is invisible to `grind`
(`_tmp/corpus/vcgen-grind/nested-ctor-fallthrough-hyp.lean`), so
`rawNatLit?_spec` runs `vcgen` on `rawNatLit?_split`, the twin with its
literal arm one constructor deep.
-/
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Grind

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

/-! ## The `Nat` walks' vocabulary

Beyond `Bridge/Grind.lean`: its handle inverses and tag values registered
locally, the literal's `Nat`, the knot's `whnf` slot and `internE` at the
invariant in answer shape, the pin reads as equations, and the index's
answer at a name against the environment's (`OptCI`). -/

/-! `Bridge/Grind.lean` §6's handle inverses and the tags' values, registered
locally (they fire on every denotation; these walks compare handles against
pins and interned lists, and tags as literals). -/
local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)
local grind_pattern [bridge_grind] lsIdxAt => denoteLs st.lss n
local grind_pattern [bridge_grind] LsIdxAt.some => LsIdxAt st n (some ls)
local grind_pattern [bridge_grind] eIdxAt => denoteE st n
local grind_pattern [bridge_grind] EIdxAt.some => EIdxAt st n (some e)
attribute [local bridge_grind =] ETag.bvar ETag.fvar ETag.sort ETag.const ETag.app ETag.lam
  ETag.forallE ETag.letE ETag.lit ETag.proj exprTag

/-- con-leche: none — a literal's `Nat`, if it is one. -/
def litNat? : Literal → Option Nat | .natVal n => some n | .strVal _ => none
attribute [bridge_grind =] litNat?

/-- con-leche: none — membership in a cons as a `||` (`List.elem_cons`'s
`match` is what `grind` would otherwise split). -/
theorem List.elem_cons_or {α : Type} [BEq α] (a b : α) (bs : List α) :
    (b :: bs).elem a = (a == b || bs.elem a) := by
  simp only [List.elem_cons]; cases a == b <;> rfl

/-- con-leche: none — a precondition on an optional subject: it denotes, in
scope at `d`. -/
def DenWS (d : Nat) : Option Expr → Prop | some e => Expr.WScoped d e | none => False

/-- con-leche: none — `DenWS` at a denoting subject. -/
@[bridge_grind =] theorem DenWS.some_eq (d : Nat) (e : Expr) :
    DenWS d (some e) = Expr.WScoped d e := rfl

/-- con-leche: none — an application's argument is in scope where it is. -/
theorem wscoped_exprArg {d : Nat} {x : Expr} (h : Expr.WScoped d x) :
    Expr.WScoped d (exprArg x) := by
  cases x <;> simp_all [Expr.WScoped, exprArg]
grind_pattern [bridge_grind] wscoped_exprArg => Expr.WScoped d x, exprArg x

/-- con-leche: none — an application's function is in scope where it is. -/
theorem wscoped_exprFn {d : Nat} {x : Expr} (h : Expr.WScoped d x) :
    Expr.WScoped d (exprFn x) := by
  cases x <;> simp_all [Expr.WScoped, exprFn]
grind_pattern [bridge_grind] wscoped_exprFn => Expr.WScoped d x, exprFn x

/-- con-leche: none — the `whnf` slot's answer at an optional subject (a
named predicate on the denotation term, `MapRel`'s idea at `SimE`). -/
def WhnfAns (mode : CheckMode) (env : Env) (d : Nat) (st : EStore) (r : EIdx) :
    Option Expr → Prop
  | some e => SimE (ConLeche.whnf mode env) d e st r
  | none => True

/-- con-leche: none — `WhnfAns` at a denoting subject. -/
theorem WhnfAns.some {d : Nat} {st : EStore} {r : EIdx} {e : Expr}
    (H : WhnfAns mode env d st r (some e)) : SimE (ConLeche.whnf mode env) d e st r := H
grind_pattern [bridge_grind] WhnfAns.some => WhnfAns mode env d st r (some e)

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the `whnf`
slot in answer shape (`KnotSpec.whnf'` with a `DenWS` precondition and a
`WhnfAns` post: no `∃` to prove, no `∀` to instantiate). -/
theorem KnotSpec.whnfA {f : Nat} (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hw : DenWS d (denoteE s₀.store i)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).whnf d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ WhnfAns mode env d s'.store r (denoteE s₀.store i); ⊤⦄ := by
  cases hd : denoteE s₀.store i with
  | none => rw [hd] at hw; exact hw.elim
  | some e =>
    rw [hd] at hw
    exact triple_mono (hsim.whnf s₀ d i e hok hd hw) (fun _ _ h => h)

/-- con-leche: none — `Bridge/Specs.lean`'s `internE_spec` at the tier's
invariant (`CheckOK.mono`), so that `grind` need not re-derive `CheckOK`. -/
theorem internE_specC (s₀ : AState) (w : ENodeView)
    (hok : CheckOK mode env fe s₀) (hv : s₀.store.ViewOK w) :
    ⦃fun s => s = s₀⦄ internE w
    ⦃fun h s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        denoteE s'.store h = denoteEView s'.store w; ⊤⦄ :=
  triple_mono (internE_spec s₀ w hok.state.wf hv)
    (fun _ _ ⟨hwf, hx, _, _, _, hc, hp, _, hd⟩ => ⟨hok.mono ⟨hwf⟩ hx hc hp, hx, hp, hd⟩)

attribute [bridge_grind →] CheckOK.pins

/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the pin
table's length. -/
theorem pinNames_length : pinNames.length = pinCount := by decide

/-- con-leche: none — `PinsOK.pinAt` as an equation: the pin at slot `i`
denotes `pinNames[i]?`. -/
theorem PinsOK.pinAtEq {s : AState} (hp : PinsOK s) {i : Nat} (hlt : i < s.pins.names.size) :
    denoteN s.store.ns s.pins.names[i] = pinNames[i]? := by
  have hl : i < pinNames.length := by rw [pinNames_length, ← hp.ready]; exact hlt
  rw [List.getElem?_eq_getElem hl]
  exact hp.pinAt hlt _ (List.getElem?_eq_getElem hl)

/-- con-leche: none — `Bridge/Specs.lean`'s `pinAt_spec` with its answer as an
EQUATION (`pinNames[i]?` is a closed term the `pinNames_eq_*` rules evaluate):
no `∀ x, … → …` whose pattern is every `some` in sight. -/
theorem pinAt_specE (s₀ : AState) (i : Nat) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ pinAt i
    ⦃fun n s' => s' = s₀ ∧ denoteN s₀.store.ns n = pinNames[i]?; ⊤⦄ := by
  sym only [bridge_grind, PinsOK.pinAtEq] =>
    vcgen [pinAt] <;> finish

/-! ### The environment's inductives and constructors as projections

`Bridge/Grind.lean` §8's `iInd?`/`iCtor?` projections, read through `OptCI`
(the index's answer at a name against the environment's). -/

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

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **`OptCI` through the
projections**: the index and the environment agree on "inductive" and
"constructor", and at either the stored record denotes the environment's. -/
theorem OptCI.at {st : EStore} {oc : Option IConstantInfo} {oc' : Option ConstantInfo}
    (h : OptCI st oc oc') : cInd? oc' = iInd? oc ∧ cCtor? oc' = iCtor? oc ∧
    (iInd? oc = true → Frontend.denoteCV st (iIndVal oc) = some (cIndVal oc')) ∧
    (iCtor? oc = true → Frontend.denoteCV st (iCtorVal oc) = some (cCtorVal oc')) := by
  match oc, h with
  | none, h => simp only [OptCI] at h; subst h; exact ⟨rfl, rfl, nofun, nofun⟩
  | some ci, ⟨c, hci, hc⟩ =>
    subst hc
    cases ci with
    | indInfo v caps =>
      obtain ⟨cv, caps', hcv, _, rfl⟩ := denoteCI_indInfo_split hci
      exact ⟨rfl, rfl, fun _ => hcv, nofun⟩
    | ctorInfo v nP nF =>
      obtain ⟨cv, hcv, rfl⟩ := denoteCI_ctorInfo_inv hci
      exact ⟨rfl, rfl, nofun, fun _ => hcv⟩
    | _ =>
      have h1 := denoteCI_ind_iff hci
      have h2 := denoteCI_ctor_iff hci
      refine ⟨?_, ?_, nofun, nofun⟩
      · cases c <;> simp_all [cInd?, iInd?]
      · cases c <;> simp_all [cCtor?, iCtor?]
grind_pattern [bridge_grind] OptCI.at => OptCI st oc oc'

/-- con-leche: none — a denoting name-handle list is empty exactly when its
denotation is. -/
theorem isEmpty_of_denoteNList {st : NStore} {hs : List NIdx}
    {xs : List ConLeche.Name} (h : Frontend.denoteNList st hs = some xs) :
    hs.isEmpty = xs.isEmpty := by
  have := denoteNList_len h
  cases hs <;> cases xs <;> simp_all

/-! ## 2. `rawNatLit?` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:240-243 rawNatLit? — the function
as ONE equation over the tag and the projections. -/
theorem rawNatLit?_eq (x : Expr) : ConLeche.rawNatLit? x =
    if exprTag x = ETag.lit then litNat? (exprLit x)
    else if exprTag x = ETag.const ∧ exprConstLevels x = [] ∧
        exprConstName x = ConLeche.natZeroName then some 0
    else none := by
  cases x with
  | lit l => cases l <;> rfl
  | const n ls =>
    cases ls <;> simp [ConLeche.rawNatLit?, exprTag, exprConstLevels, exprConstName,
      ETag.const, ETag.lit]
  | _ => simp [ConLeche.rawNatLit?, exprTag, ETag.const, ETag.lit, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.proj]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:240-243 rawNatLit? — the twin
with its literal arm one constructor deep (`litNat?` reads the literal): the
shape `vcgen` gives `grind` a usable fall-through for
(`_tmp/corpus/vcgen-grind/nested-ctor-fallthrough-hyp.lean`). -/
theorem rawNatLit?_split (h : EIdx) : ConRon.Arena.rawNatLit? h = (do
    match ← view h with
    | .lit l => pure (litNat? l)
    | .const c us => do
      let e ← emptyLevels
      let nz ← pinNatZero
      pure (if c == nz && us == e then some 0 else none)
    | _ => pure none) := by
  simp only [ConRon.Arena.rawNatLit?]
  congr; funext v
  cases v with
  | lit l => cases l <;> rfl
  | _ => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit? — **THEOREM 1
for `rawNatLit?`**: the literal reading of a head normal form. -/
theorem rawNatLit?_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.rawNatLit? h
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.rawNatLit? x; ⊤⦄ := by
  sym only [bridge_grind, rawNatLit?_eq] =>
    vcgen [rawNatLit?_split, ConRon.Arena.emptyLevels, ConRon.Arena.pinNatZero, pinAt_specE] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit? — answer
shape: the reading of whatever the handle denotes, as an equation through
`Option.map`. -/
theorem rawNatLit?_specA (s₀ : AState) (h : EIdx)
    (hok : CheckOK mode env fe s₀) (hd : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.rawNatLit? h
    ⦃fun r s' => s' = s₀ ∧ (denoteE s₀.store h).map ConLeche.rawNatLit? = some r; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  refine triple_mono (rawNatLit?_spec s₀ h x hok hx) ?_
  rintro r s' ⟨h1, h2⟩
  exact ⟨h1, by rw [hx, h2]; rfl⟩

/-! ## 3. The name tests -/

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

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the binary
test as a `Bool`, one `==` per operation. -/
def natBinOpB (c : ConLeche.Name) : Bool :=
  c == ConLeche.natAddName || c == ConLeche.natSubName || c == ConLeche.natMulName ||
  c == ConLeche.natPowName || c == ConLeche.natBeqName || c == ConLeche.natBleName ||
  c == ConLeche.natDivName || c == ConLeche.natModName || c == ConLeche.natGcdName ||
  c == ConLeche.natLandName || c == ConLeche.natLorName || c == ConLeche.natXorName ||
  c == ConLeche.natShiftLeftName || c == ConLeche.natShiftRightName

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the `Bool` is
con-leche's disjunction. -/
theorem natBinOpB_iff (c : ConLeche.Name) : natBinOpB c = true ↔ NatBinOp c := by
  simp [natBinOpB, NatBinOp, or_assoc]

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **THEOREM 1 for
`natBinOpName`**: the binary literal acceleration's fourteen-way name test is
con-leche's (`natBinOpB`). -/
theorem natBinOpName_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natBinOpName c
    ⦃fun b s' => s' = s₀ ∧ b = natBinOpB nm; ⊤⦄ := by
  sym only [bridge_grind, natBinOpB.eq_1] =>
    vcgen [ConRon.Arena.natBinOpName,
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
      ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight, pinAt_specE] <;> finish (splits := 20)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:700-703 natOpStored — the
function as ONE equation: is the lookup a definition. -/
theorem natOpStored_eq (nm : ConLeche.Name) :
    ConLeche.natOpStored env nm = cDefn? (env.find? nm) := by
  simp only [ConLeche.natOpStored]
  split <;> rename_i h
  · simp_all [cDefn?]
  · cases ho : env.find? nm with
    | none => rfl
    | some ci => cases ci <;> simp_all [cDefn?]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored — **THEOREM 1
for `natOpStored`**: is the operation stored as a definition. -/
theorem natOpStored_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpStored fe c
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.natOpStored env nm; ⊤⦄ := by
  sym only [bridge_grind, natOpStored_eq] =>
    vcgen [ConRon.Arena.natOpStored] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:605-615 natOpWfNames — the
handle list answers con-leche's membership test at every denoted name. -/
def WfNames (st : NStore) (ws : List NIdx) : Prop :=
  ∀ c nm, denoteN st c = some nm → ws.contains c = ConLeche.natOpWfNames.contains nm

/-- con-leche: none — `WfNames` at one handle's optional name. -/
def WfAt (b : Bool) : Option ConLeche.Name → Prop
  | some nm => b = ConLeche.natOpWfNames.contains nm
  | none => True

/-- con-leche: none — `WfNames` at a membership test the walk makes. -/
theorem WfNames.at {st : NStore} {ws : List NIdx} (H : WfNames st ws) (c : NIdx) :
    WfAt (ws.contains c) (denoteN st c) := by
  cases h : denoteN st c with
  | none => trivial
  | some nm => exact H c nm h
grind_pattern [bridge_grind] WfNames.at => WfNames st ws, ws.contains c

/-- con-leche: none — `WfAt` at a denoting handle. -/
theorem WfAt.some {b : Bool} {nm : ConLeche.Name} (H : WfAt b (some nm)) :
    b = ConLeche.natOpWfNames.contains nm := H
grind_pattern [bridge_grind] WfAt.some => WfAt b (some nm)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:602-612 natOpWfNames — **THEOREM
1 for `natOpWfNames`**: the eight pinned handles answer con-leche's
membership test at every denoted name. -/
theorem natOpWfNames_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpWfNames
    ⦃fun ws s' => s' = s₀ ∧ WfNames s₀.store.ns ws; ⊤⦄ := by
  sym only [bridge_grind, WfNames, List.elem_cons_or, List.elem_nil, ConLeche.natOpWfNames] =>
    vcgen [ConRon.Arena.natOpWfNames,
      ConRon.Arena.natDivName, ConRon.Arena.pinNatDiv,
      ConRon.Arena.natModName, ConRon.Arena.pinNatMod,
      ConRon.Arena.natGcdName, ConRon.Arena.pinNatGcd,
      ConRon.Arena.natLandName, ConRon.Arena.pinNatLand,
      ConRon.Arena.natLorName, ConRon.Arena.pinNatLor,
      ConRon.Arena.natXorName, ConRon.Arena.pinNatXor,
      ConRon.Arena.natShiftLeftName, ConRon.Arena.pinNatShiftLeft,
      ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight, pinAt_specE] <;> finish (splits := 20) (gen := 16)

/-! ## 4. `constE` and `natOpResult` -/

/-- con-leche: none — `ViewOK` of a constant node whose name and level list
denote (`constE`'s intern precondition, passed to `grind`). -/
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
  sym only [bridge_grind, viewOK_const_of_denote] =>
    vcgen [ConRon.Arena.constE, ConRon.Arena.emptyLevels,
      internE_specC (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: none — the level-monomorphic constant at a name. -/
def const0 (nm : ConLeche.Name) : Expr := .const nm []

/-- con-leche: none — `const0` unfolded. -/
@[bridge_grind =] theorem const0_eq (nm : ConLeche.Name) : const0 nm = .const nm [] := rfl

/-- con-leche: none — `constE_spec` in answer shape: the constant at
whatever the name handle denotes. -/
theorem constE_specA (s₀ : AState) (n : NIdx)
    (hok : CheckOK mode env fe s₀) (hn : (denoteN s₀.store.ns n).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.constE n
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = (denoteN s₀.store.ns n).map const0; ⊤⦄ := by
  obtain ⟨nm, hnm⟩ := Option.isSome_iff_exists.mp hn
  refine triple_mono (constE_spec s₀ n nm hok hnm) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, by rw [h4, hnm]; rfl⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult — **THEOREM 1
for `natOpResult`**: the reduct of a binary operation on two literals. -/
theorem natOpResult_spec (s₀ : AState) (c : NIdx) (nm : ConLeche.Name)
    (a b : Nat) (hok : CheckOK mode env fe s₀)
    (hn : denoteN s₀.store.ns c = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natOpResult c a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteEO s'.store r = some (ConLeche.natOpResult nm a b); ⊤⦄ := by
  sym only [bridge_grind, ConLeche.natOpResult] =>
    vcgen [ConRon.Arena.natOpResult,
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
      ConRon.Arena.natShiftRightName, ConRon.Arena.pinNatShiftRight,
      ConRon.Arena.boolTrueName, ConRon.Arena.boolFalseName, ConRon.Arena.pinBoolTrue,
      ConRon.Arena.pinBoolFalse, internE_specC (mode := mode) (env := env) (fe := fe),
      constE_specA (mode := mode) (env := env) (fe := fe), pinAt_specE] <;> finish (splits := 20)

/-! ## 5. `natLitSupported` — the three stored-declaration shapes

Each is a twin over the INDEX's lookup at a pinned name and con-leche's over
the environment's at the name it denotes; `OptCI.at` relates the two through
the projections, and con-leche's function is one equation over them. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:173-176 natIndOk — the function as
ONE equation over the projections. -/
@[bridge_grind =] theorem natIndOk_eq (o : Option ConstantInfo) : ConLeche.natIndOk o =
    (cInd? o && (cIndVal o).levelParams.isEmpty &&
      (cIndVal o).type == .sort (.succ .zero)) := by
  match o with
  | some (.indInfo _ _) => rfl
  | none | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
  | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:179-182 natZeroOk — the function
as ONE equation over the projections. -/
@[bridge_grind =] theorem natZeroOk_eq (o : Option ConstantInfo) : ConLeche.natZeroOk o =
    (cCtor? o && (cCtorVal o).levelParams.isEmpty &&
      (cCtorVal o).type == .const ConLeche.natName []) := by
  match o with
  | some (.ctorInfo _ _ _) => rfl
  | none | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:185-192 natSuccOk — the function
as ONE equation over the projections: a `∀` from `Nat` to `Nat`. -/
@[bridge_grind =] theorem natSuccOk_eq (o : Option ConstantInfo) : ConLeche.natSuccOk o =
    (cCtor? o && (cCtorVal o).levelParams.isEmpty &&
      (exprTag (cCtorVal o).type == ETag.forallE &&
        exprBinderType (cCtorVal o).type == .const ConLeche.natName [] &&
        exprBody (cCtorVal o).type == .const ConLeche.natName [])) := by
  match o with
  | some (.ctorInfo cv _ _) =>
    simp only [ConLeche.natSuccOk, cCtor?, cCtorVal, Bool.true_and]
    congr 1
    generalize cv.type = t
    split
    · simp only [exprTag, exprBinderType, exprBody, beq_self_eq_true, Bool.true_and]
      rw [Bool.eq_iff_iff]; simp
    · next hne =>
      cases t <;> simp [exprTag, ETag.forallE, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
        ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]
      next a b =>
      simp only [exprBinderType, exprBody]
      intro h1 h2
      subst h1 h2
      exact hne _ _ rfl
  | none | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:202-206 natIndOk — **THEOREM 1
for `natIndOk`**, at the index's lookup of a denoted name. -/
theorem natIndOk_spec (s₀ : AState) (n : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns n = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natIndOk (fe.find? n)
    ⦃fun b s' => s' = s₀ ∧ b = ConLeche.natIndOk (env.find? nm); ⊤⦄ := by
  have hrel := optCI_find hok hn
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.natIndOk, ConRon.Arena.sortOne] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk — **THEOREM 1
for `natZeroOk`**, at the index's lookup of a denoted name. -/
theorem natZeroOk_spec (s₀ : AState) (n : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns n = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natZeroOk (fe.find? n)
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natZeroOk (env.find? nm); ⊤⦄ := by
  have hrel := optCI_find hok hn
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.natZeroOk, ConRon.Arena.pinNat,
      constE_spec (mode := mode) (env := env) (fe := fe) (nm := ConLeche.natName), pinAt_specE] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — **THEOREM 1
for `natSuccOk`**, at the index's lookup of a denoted name. -/
theorem natSuccOk_spec (s₀ : AState) (n : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK mode env fe s₀) (hn : denoteN s₀.store.ns n = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natSuccOk (fe.find? n)
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natSuccOk (env.find? nm); ⊤⦄ := by
  have hrel := optCI_find hok hn
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.natSuccOk, ConRon.Arena.pinNat,
      constE_spec (mode := mode) (env := env) (fe := fe) (nm := ConLeche.natName), pinAt_specE] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:225-233 natLitSupported —
**THEOREM 1 for `natLitSupported`**: the three stored-declaration shapes. -/
theorem natLitSupported_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natLitSupported fe
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.natLitSupported env; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.natLitSupported] =>
    vcgen [ConRon.Arena.natLitSupported, ConRon.Arena.pinNat,
      ConRon.Arena.pinNatZero, ConRon.Arena.pinNatSucc,
      natIndOk_spec (mode := mode) (env := env) (fe := fe) (nm := ConLeche.natName),
      natZeroOk_spec (mode := mode) (env := env) (fe := fe) (nm := ConLeche.natZeroName),
      natSuccOk_spec (mode := mode) (env := env) (fe := fe) (nm := ConLeche.natSuccName),
      pinAt_specE] <;> finish

/-! ## 6. `reduceNat`'s pure side at its exits

con-leche's `reduceNat` at `pureFns F`, one equation per exit; the knot's
`whnf` slot is `ConLeche.whnf mode env F`. -/

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

/-! ### `reduceNat`'s exits

One `SimOOp` lemma per exit, over the subject and the callees' runs; the
`grind` lemmas of §7 restate them over the subject's projections. -/

/-- con-leche: none — a declining exit. -/
theorem reduceNat_decline {P : Nat → CheckM (Option Expr)} {d : Nat} {st : EStore}
    (F : Nat) (h : P F = .ok none) : SimOOp P d st none :=
  ⟨none, rfl, by simp, F, h⟩

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a unary
application of a constant WITH universe levels is no operation. -/
theorem simOOp_unary_levels {d : Nat} {st : EStore} {nm : ConLeche.Name}
    {ls : List Level} {a : Expr} (h : ls ≠ []) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d (.app (.const nm ls) a))
      d st none :=
  reduceNat_decline 0 <| reduceNatFueled_none_of
    (fun c a' h' => by
      simp only [Expr.app.injEq, Expr.const.injEq] at h'; exact h h'.1.2)
    (fun c a' b' h' => by simp at h')

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — nor is a binary
one. -/
theorem simOOp_binary_levels {d : Nat} {st : EStore} {nm : ConLeche.Name}
    {ls : List Level} {a b : Expr} (h : ls ≠ []) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.app (.const nm ls) a) b)) d st none :=
  reduceNat_decline 0 <| reduceNatFueled_none_of
    (fun c a' h' => by simp at h')
    (fun c a' b' h' => by
      simp only [Expr.app.injEq, Expr.const.injEq] at h'; exact h h'.1.1.2)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the unary guard
declines. -/
theorem simOOp_succ_no {d : Nat} {st : EStore} {c : ConLeche.Name} {a : Expr}
    (hg : ¬ (c = ConLeche.natSuccName ∧ ConLeche.natLitSupported env = true)) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d (.app (.const c []) a))
      d st none :=
  reduceNat_decline 0 (reduceNatFueled_succ_no hg)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — neither binary
guard. -/
theorem simOOp_bin_no {d : Nat} {st : EStore} {c : ConLeche.Name} {a b : Expr}
    (hg : ¬ (NatBinOp c ∧ ConLeche.natOpStored env c = true))
    (hw : ¬ (ConLeche.natOpWfNames.contains c ∧ ConLeche.natLitSupported env = true)) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d
      (.app (.app (.const c []) a) b)) d st none :=
  reduceNat_decline 0 (reduceNatFueled_bin_no hg hw)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a binary
application whose head is not a constant. -/
theorem simOOp_bin_nc {d : Nat} {st : EStore} {f a b : Expr}
    (h : ∀ n us, f ≠ .const n us) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d (.app (.app f a) b))
      d st none :=
  reduceNat_decline 0 <| reduceNatFueled_none_of
    (fun c a' h' => by simp at h')
    (fun c a' b' h' => by simp only [Expr.app.injEq] at h'; exact h c [] h'.1.1)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — not an
application at all. -/
theorem simOOp_na {d : Nat} {st : EStore} {x : Expr} (h : ∀ f a, x ≠ .app f a) :
    SimOOp (fun F => ConLeche.reduceNatFueled mode env F d x) d st none :=
  reduceNat_decline 0 <|
    reduceNatFueled_none_of (fun _ _ h' => h _ _ h') (fun _ _ _ h' => h _ _ h')

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
  refine reduceNat_decline (F₁ + F₂) ?_
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
  reduceNat_decline F₁ (by rw [reduceNatFueled_bin ⟨hb, hs⟩ hw₁, ← hr₁]; rfl)

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
  refine reduceNat_decline (F₁ + F₂) ?_
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
  reduceNat_decline F₁ (by rw [reduceNatFueled_wf hg ⟨hc, hs⟩ hw₁, ← hr₁]; rfl)

/-! ## 7. `reduceNat`'s exits as `grind` lemmas

Over the subject's projections: a unary application `.app (.const c []) a`
is `exprTag x = app`, `exprTag (exprFn x) = const`, `exprConstLevels (exprFn
x) = []`, with `c = exprConstName (exprFn x)` and `a = exprArg x`; a binary
one is the same one `exprFn` deeper.  Each exit's conclusion is its pattern,
with the callees' runs (`whnf`, `rawNatLit?`) whose answers it reads. -/

/-- con-leche: none — a term tagged `app` IS an application of its
projections. -/
theorem exprTag_app {e : Expr} (h : exprTag e = ETag.app) : e = .app (exprFn e) (exprArg e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))

/-- con-leche: none — a term tagged `const` IS a constant of its
projections. -/
theorem exprTag_const {e : Expr} (h : exprTag e = ETag.const) :
    e = .const (exprConstName e) (exprConstLevels e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **`reduceNat`'s
answer, named** (the statement's `SimOOp (fun F => …)`, which `grind` must
not see as a `fun`). -/
def NatRed (mode : CheckMode) (env : Env) (d : Nat) (x : Expr) (st : EStore) (r : Option EIdx) : Prop :=
  SimOOp (fun F => ConLeche.reduceNatFueled mode env F d x) d st r

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the `Nat.succ`
reduct of a literal. -/
def succLit (n : Nat) : Expr := .lit (.natVal (n + 1))
/-- con-leche: none — `succLit` unfolded. -/
@[bridge_grind =] theorem succLit_eq (n : Nat) : succLit n = .lit (.natVal (n + 1)) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the binary reduct
at the two literal readings (`none` unless both are literals). -/
def binRes (c : ConLeche.Name) : Option Nat → Option Nat → Option Expr
  | some a, some b => ConLeche.natOpResult c a b
  | _, _ => none
attribute [bridge_grind =] binRes

/-- con-leche: none — a declining exit. -/
theorem natRed_decline {d : Nat} {x : Expr} {st : EStore} (F : Nat)
    (h : ConLeche.reduceNatFueled mode env F d x = .ok none) : NatRed mode env d x st none :=
  reduceNat_decline F h

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — not an
application. -/
theorem natRed_na {d : Nat} {x : Expr} {st : EStore} (h : exprTag x ≠ ETag.app) :
    NatRed mode env d x st none :=
  simOOp_na (fun f a he => h (by rw [he]; rfl))
grind_pattern [bridge_grind] natRed_na => NatRed mode env d x st none

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the head is
neither a constant nor an application. -/
theorem natRed_un_other {d : Nat} {x : Expr} {st : EStore}
    (h1 : exprTag (exprFn x) ≠ ETag.const) (h2 : exprTag (exprFn x) ≠ ETag.app) :
    NatRed mode env d x st none := by
  refine natRed_decline 0 (reduceNatFueled_none_of ?_ ?_)
  · intro c a he; subst he; exact h1 rfl
  · intro c a b he; subst he; exact h2 rfl
grind_pattern [bridge_grind] natRed_un_other => NatRed mode env d x st none

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a unary
application of a constant with universe levels. -/
theorem natRed_un_levels {d : Nat} {x : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.const)
    (h3 : exprConstLevels (exprFn x) ≠ []) : NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_const h2]
  exact simOOp_unary_levels h3
grind_pattern [bridge_grind] natRed_un_levels => NatRed mode env d x st none

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the unary guard
declines. -/
theorem natRed_succ_no {d : Nat} {x : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.const)
    (h3 : exprConstLevels (exprFn x) = [])
    (hg : ¬ (exprConstName (exprFn x) = ConLeche.natSuccName ∧ ConLeche.natLitSupported env = true)) :
    NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_const h2, h3]
  exact simOOp_succ_no hg
grind_pattern [bridge_grind] natRed_succ_no => NatRed mode env d x st none

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — `Nat.succ`: the
argument's head normal form, read (`none` on a non-literal). -/
theorem natRed_succ {F d : Nat} {x w : Expr} {st : EStore} {r : Option EIdx}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.const)
    (h3 : exprConstLevels (exprFn x) = [])
    (hn : exprConstName (exprFn x) = ConLeche.natSuccName)
    (hs : ConLeche.natLitSupported env = true)
    (hw : ConLeche.whnf mode env F d (exprArg x) = .ok w)
    (hr : denoteEO st r = some ((ConLeche.rawNatLit? w).map succLit)) :
    NatRed mode env d x st r := by
  refine ⟨_, hr, ?_, F, ?_⟩
  · intro y hy
    cases h : ConLeche.rawNatLit? w <;> rw [h] at hy <;> cases hy
    simp [succLit, Expr.WScoped]
  · rw [exprTag_app h1, exprTag_const h2, h3, hn]
    exact reduceNatFueled_succ ⟨rfl, hs⟩ hw
grind_pattern [bridge_grind] natRed_succ =>
  NatRed mode env d x st r, ConLeche.whnf mode env F d (exprArg x), ConLeche.rawNatLit? w

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a binary
application whose head is not a constant. -/
theorem natRed_bin_nc {d : Nat} {x : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.app)
    (h3 : exprTag (exprFn (exprFn x)) ≠ ETag.const) : NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_app h2]
  exact simOOp_bin_nc (fun n us he => h3 (by rw [he]; rfl))
grind_pattern [bridge_grind] natRed_bin_nc => NatRed mode env d x st none

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — a binary
application of a constant with universe levels. -/
theorem natRed_bin_levels {d : Nat} {x : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.app)
    (h3 : exprTag (exprFn (exprFn x)) = ETag.const)
    (h4 : exprConstLevels (exprFn (exprFn x)) ≠ []) : NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_app h2, exprTag_const h3]
  exact simOOp_binary_levels h4
grind_pattern [bridge_grind] natRed_bin_levels => NatRed mode env d x st none

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — neither binary
guard. -/
theorem natRed_bin_no {d : Nat} {x : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.app)
    (h3 : exprTag (exprFn (exprFn x)) = ETag.const)
    (h4 : exprConstLevels (exprFn (exprFn x)) = [])
    (hg : (natBinOpB (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natOpStored env (exprConstName (exprFn (exprFn x)))) = false)
    (hw : (ConLeche.natOpWfNames.contains (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natLitSupported env) = false) : NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_app h2, exprTag_const h3, h4]
  refine simOOp_bin_no ?_ ?_
  · rw [← natBinOpB_iff]; simpa using hg
  · simpa using hw
grind_pattern [bridge_grind] natRed_bin_no => NatRed mode env d x st none

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the certified
operation, the first argument not a literal. -/
theorem natRed_bin_fst {F d : Nat} {x w : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.app)
    (h3 : exprTag (exprFn (exprFn x)) = ETag.const)
    (h4 : exprConstLevels (exprFn (exprFn x)) = [])
    (hg : (natBinOpB (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natOpStored env (exprConstName (exprFn (exprFn x)))) = true)
    (hw : ConLeche.whnf mode env F d (exprArg (exprFn x)) = .ok w)
    (hr : ConLeche.rawNatLit? w = none) : NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_app h2, exprTag_const h3, h4]
  simp only [Bool.and_eq_true, natBinOpB_iff] at hg
  exact simOOp_bin_fst hg.1 hg.2 hw hr.symm
grind_pattern [bridge_grind] natRed_bin_fst =>
  NatRed mode env d x st none, ConLeche.whnf mode env F d (exprArg (exprFn x)), ConLeche.rawNatLit? w

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the certified
operation on a literal first argument: it fires, or the second is not a
literal (`binRes`). -/
theorem natRed_bin {F₁ F₂ d : Nat} {x w₁ w₂ : Expr} {st : EStore} {r : Option EIdx}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.app)
    (h3 : exprTag (exprFn (exprFn x)) = ETag.const)
    (h4 : exprConstLevels (exprFn (exprFn x)) = [])
    (hg : (natBinOpB (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natOpStored env (exprConstName (exprFn (exprFn x)))) = true)
    (hw₁ : ConLeche.whnf mode env F₁ d (exprArg (exprFn x)) = .ok w₁)
    (hs : (ConLeche.rawNatLit? w₁).isSome = true)
    (hw₂ : ConLeche.whnf mode env F₂ d (exprArg x) = .ok w₂)
    (hr : denoteEO st r = some (binRes (exprConstName (exprFn (exprFn x)))
      (ConLeche.rawNatLit? w₁) (ConLeche.rawNatLit? w₂))) : NatRed mode env d x st r := by
  rw [exprTag_app h1, exprTag_app h2, exprTag_const h3, h4]
  simp only [Bool.and_eq_true, natBinOpB_iff] at hg
  obtain ⟨n₁, hn₁⟩ := Option.isSome_iff_exists.mp hs
  rw [hn₁] at hr
  cases hn₂ : ConLeche.rawNatLit? w₂ with
  | none =>
    rw [hn₂] at hr
    simp only [binRes, denoteEO] at hr
    cases r with
    | none => exact simOOp_bin_snd hg.1 hg.2 hw₁ hn₁.symm hw₂ hn₂.symm
    | some r => simp [Option.map_eq_some_iff] at hr
  | some n₂ =>
    rw [hn₂] at hr
    exact simOOp_bin_fire hg.1 hg.2 hw₁ hn₁.symm hw₂ hn₂.symm hr
grind_pattern [bridge_grind] natRed_bin =>
  NatRed mode env d x st r, ConLeche.whnf mode env F₁ d (exprArg (exprFn x)),
  ConLeche.whnf mode env F₂ d (exprArg x), ConLeche.rawNatLit? w₁, ConLeche.rawNatLit? w₂

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the safety net,
the first argument not a literal. -/
theorem natRed_wf_fst {F d : Nat} {x w : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.app)
    (h3 : exprTag (exprFn (exprFn x)) = ETag.const)
    (h4 : exprConstLevels (exprFn (exprFn x)) = [])
    (hg : (natBinOpB (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natOpStored env (exprConstName (exprFn (exprFn x)))) = false)
    (hc : (ConLeche.natOpWfNames.contains (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natLitSupported env) = true)
    (hw : ConLeche.whnf mode env F d (exprArg (exprFn x)) = .ok w)
    (hr : ConLeche.rawNatLit? w = none) : NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_app h2, exprTag_const h3, h4]
  simp only [Bool.and_eq_true] at hc
  refine simOOp_wf_fst ?_ hc.1 hc.2 hw hr.symm
  rw [← natBinOpB_iff]; simpa using hg
grind_pattern [bridge_grind] natRed_wf_fst =>
  NatRed mode env d x st none, ConLeche.whnf mode env F d (exprArg (exprFn x)), ConLeche.rawNatLit? w

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the safety net,
the second argument not a literal. -/
theorem natRed_wf_snd {F₁ F₂ d : Nat} {x w₁ w₂ : Expr} {st : EStore}
    (h1 : exprTag x = ETag.app) (h2 : exprTag (exprFn x) = ETag.app)
    (h3 : exprTag (exprFn (exprFn x)) = ETag.const)
    (h4 : exprConstLevels (exprFn (exprFn x)) = [])
    (hg : (natBinOpB (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natOpStored env (exprConstName (exprFn (exprFn x)))) = false)
    (hc : (ConLeche.natOpWfNames.contains (exprConstName (exprFn (exprFn x))) &&
      ConLeche.natLitSupported env) = true)
    (hw₁ : ConLeche.whnf mode env F₁ d (exprArg (exprFn x)) = .ok w₁)
    (hs : (ConLeche.rawNatLit? w₁).isSome = true)
    (hw₂ : ConLeche.whnf mode env F₂ d (exprArg x) = .ok w₂)
    (hr : ConLeche.rawNatLit? w₂ = none) : NatRed mode env d x st none := by
  rw [exprTag_app h1, exprTag_app h2, exprTag_const h3, h4]
  simp only [Bool.and_eq_true] at hc
  obtain ⟨n₁, hn₁⟩ := Option.isSome_iff_exists.mp hs
  refine simOOp_wf_snd ?_ hc.1 hc.2 hw₁ hn₁.symm hw₂ hr.symm
  rw [← natBinOpB_iff]; simpa using hg
grind_pattern [bridge_grind] natRed_wf_snd =>
  NatRed mode env d x st none, ConLeche.whnf mode env F₁ d (exprArg (exprFn x)),
  ConLeche.whnf mode env F₂ d (exprArg x), ConLeche.rawNatLit? w₁, ConLeche.rawNatLit? w₂

/-! ## 8. `reduceNat` -/

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — `reduceNat` at a
given subject, its answer `NatRed`: fifty verification conditions,
one per exit and per callee precondition, each closed by `grind` from the
exits of §7. -/
theorem reduceNat_specR {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (e : EIdx) (x : Expr) (hok : CheckOK mode env fe s₀)
    (hden : denoteE s₀.store e = some x) (hwx : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ NatRed mode env d x s'.store r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.reduceNat, ConRon.Arena.emptyLevels, ConRon.Arena.pinNatSucc,
      KnotSpec.whnfA hsim, rawNatLit?_specA (mode := mode) (env := env) (fe := fe),
      natLitSupported_spec (mode := mode) (env := env) (fe := fe),
      natBinOpName_spec (mode := mode) (env := env) (fe := fe)
        (nm := exprConstName (exprFn (exprFn x))),
      natOpStored_spec (mode := mode) (env := env) (fe := fe)
        (nm := exprConstName (exprFn (exprFn x))),
      natOpWfNames_spec (mode := mode) (env := env) (fe := fe),
      natOpResult_spec (mode := mode) (env := env) (fe := fe)
        (nm := exprConstName (exprFn (exprFn x))),
      internE_specC (mode := mode) (env := env) (fe := fe), pinAt_specE] <;> finish (gen := 16) (ematch := 10)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **THEOREM 1 for
`reduceNat`**: the literal acceleration, run in the `whnf` loop before
delta-unfolding.  **CLOSED** (round 4; moved here from `Walks/Owed.lean`,
statement unchanged).  The divergence audit's D15 is preserved by the twin —
the FIRST argument is head-normalised and, unless it is a literal, the step
declines without touching the second — so the two call sequences agree and
the proof is a straight walk (`reduceNat_specR`, by `vcgen` and `grind`). -/
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
  refine triple_mono (reduceNat_specR hsim s₀ d e x hok hden hwx) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  rw [hden] at hy
  cases hy
  exact h4

/-! ## 9. The axiom census -/

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
