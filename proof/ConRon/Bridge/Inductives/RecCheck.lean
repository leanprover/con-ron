/-
# `ConRon.Bridge.Inductives.RecCheck` — Theorem 1 for the recursor stage's class kit

`Arena/Inductives/RecCheck.lean` against `ConLeche/Kernel/Inductives/RecCheck.lean`
(task #105, lane B-IND): the member abstraction (`targetAbs`), the holes, the
class record and its default, the two `FvMap` readbacks, the per-component
class match and the three functions over it (`targetParamsDefEq`,
`targetClassMatch`, `targetMajorNfs`), a class resolved and typed
(`targetOutsideInst`, `targetMajorOf`, `targetPinTys`, `targetMajorPins`), the
recursor records' pins, node agreement (`targetCtorAt`, `targetK53`,
`targetPiDomsWith`), and the stored family (`auxRuleFireR`, `tgtStoredRules`,
`blockNestedBit`, `consBlockRecsTF`).

**The twin module note's deviations, as the statements read them:**

* `ShadowOps` is gone: the twin calls the core at the `IFEnv` it is handed.
  Upstream's pure route runs `ShadowOps.ofOps ops`, whose `opsAt fe` is the
  constant `ops`, so every core-grade statement here is `CSpecF` against the
  con-leche function at `fueledOpsM μ` (`Bridge/Inductives/Rel.lean`).
* `targetAbs` is ONE memoised walk; its statement is the STRUCTURAL
  `ConLeche.targetAbs` (con-leche's own `@[csimp]` swaps its memoised
  `targetAbsFast` in), with the memo invariant `TAMemoOK` at handle keys, as
  `Bridge/Inductives/PosWalks.lean`'s `RFMemoOK` is for `replaceFVars`.
* `targetParamsDefEq`'s `absM` is `targetAbs names lvls holes`, at the
  denoted names, levels and holes.
* `Ms.getD c default` is `targetMajorAt`: `targetMajorDefault` denotes
  `(default : ConLeche.TargetMajor)` (`PSpecP`: it reads the empty-levels pin).
* `eraseFVarTys`/`targetCanonParams` are `replaceFVars` at the `.erase` and
  `.canon pfvs` maps (`PosWalks.lean`'s `FvMapRel`).
* `consBlockRecsTF vis₂` reads the rules at `fe.restrictTo vis₂`; the
  statement relates it to `consBlockRecsT env₂.find? (·.constsResolve env₂)`
  at the environment `env₂` that restriction denotes.
-/
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Inductives.StructParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The class record, denoted -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor —
**a resolved class, denoted**: the inductive's name, its level list, its
parameters, its constructors (`dCtors`), the walk's recorded normal forms
(`dCtorNf`) and the recursor prefix's openers; the counts and the member index
are carried verbatim. -/
def dMajor (st : EStore) (m : Arena.TargetMajor) : Option ConLeche.TargetMajor := do
  let ind ← denoteN st.ns m.ind
  let lvls ← denoteLs st.lss m.lvls
  let ds ← Frontend.denoteEList st m.ds
  let ctors ← dCtors st m.ctors
  let nfs ← m.nfs.mapM (dCtorNf st)
  let pfvs ← Frontend.denoteEList st m.pfvs
  pure ⟨ind, lvls, ds, m.nPc, m.nIdx, ctors, m.member, nfs, pfvs⟩

theorem dMajor_ext : DExt dMajor := by
  intro st st' hx m y h
  simp only [dMajor] at h ⊢
  cases h1 : denoteN st.ns m.ind with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : denoteLs st.lss m.lvls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : Frontend.denoteEList st m.ds with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some c =>
  cases h4 : dCtors st m.ctors with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some d =>
  cases h5 : m.nfs.mapM (dCtorNf st) with
  | none => rw [h1, h2, h3, h4, h5] at h; exact nomatch h
  | some e =>
  cases h6 : Frontend.denoteEList st m.pfvs with
  | none => rw [h1, h2, h3, h4, h5, h6] at h; exact nomatch h
  | some f =>
  rw [h1, h2, h3, h4, h5, h6] at h
  rw [denoteN_ext h1 hx, denoteLs_ext h2 hx, denoteEList_ext hx _ _ h3,
    dCtors_ext hx _ _ h4, show m.nfs.mapM (dCtorNf st') = some e from
      dCtorNf_ext.list hx _ _ h5, denoteEList_ext hx _ _ h6]
  exact h

/-- con-leche: none — **a denoted class, taken apart**: every field's
denotation, and the verbatim ones equal. -/
theorem dMajor_inv {st : EStore} {m : Arena.TargetMajor} {mP : ConLeche.TargetMajor}
    (h : dMajor st m = some mP) :
    denoteN st.ns m.ind = some mP.ind ∧ denoteLs st.lss m.lvls = some mP.lvls ∧
      Frontend.denoteEList st m.ds = some mP.ds ∧ m.nPc = mP.nPc ∧ m.nIdx = mP.nIdx ∧
      dCtors st m.ctors = some mP.ctors ∧ m.member = mP.member ∧
      m.nfs.mapM (dCtorNf st) = some mP.nfs ∧
      Frontend.denoteEList st m.pfvs = some mP.pfvs := by
  simp only [dMajor] at h
  cases h1 : denoteN st.ns m.ind with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : denoteLs st.lss m.lvls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : Frontend.denoteEList st m.ds with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some c =>
  cases h4 : dCtors st m.ctors with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some d =>
  cases h5 : m.nfs.mapM (dCtorNf st) with
  | none => rw [h1, h2, h3, h4, h5] at h; exact nomatch h
  | some e =>
  cases h6 : Frontend.denoteEList st m.pfvs with
  | none => rw [h1, h2, h3, h4, h5, h6] at h; exact nomatch h
  | some f =>
  rw [h1, h2, h3, h4, h5, h6] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The member abstraction (`targetAbs`) -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:111-113 TargetAbsMemoInv
The handle-keyed memo of `targetAbs names lvls holes`. -/
def TAMemoOK (names : List ConLeche.Name) (lvls : List Level) (holes : List Expr)
    (tbl : Std.HashMap EIdx EIdx) (st : EStore) : Prop :=
  ∀ (k v : EIdx), tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ denoteE st v = some (ConLeche.targetAbs names lvls holes e)

theorem TAMemoOK.empty {names : List ConLeche.Name} {lvls : List Level}
    {holes : List Expr} {st : EStore} : TAMemoOK names lvls holes ∅ st := by
  intro k v h; simp at h

theorem TAMemoOK.ext {names : List ConLeche.Name} {lvls : List Level}
    {holes : List Expr} {tbl : Std.HashMap EIdx EIdx} {st st' : EStore}
    (hx : Ext st st') (h : TAMemoOK names lvls holes tbl st) :
    TAMemoOK names lvls holes tbl st' := by
  intro k v hk
  obtain ⟨e, h1, h2⟩ := h k v hk
  exact ⟨e, denote_ext h1 hx, denote_ext h2 hx⟩

theorem TAMemoOK.insert {names : List ConLeche.Name} {lvls : List Level}
    {holes : List Expr} {tbl : Std.HashMap EIdx EIdx} {st : EStore}
    (hm : TAMemoOK names lvls holes tbl st) {h r : EIdx} {hP : Expr}
    (hd : denoteE st h = some hP)
    (hr : denoteE st r = some (ConLeche.targetAbs names lvls holes hP)) :
    TAMemoOK names lvls holes (tbl.insert h r) st := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, hr⟩
  · exact hm k v hk

/-- con-leche: none — the abstraction's three arguments, denoted: the store
predicate every `targetAbs` statement carries. -/
def TAArgs (names : List NIdx) (lvls : LsIdx) (holes : List EIdx)
    (namesP : List ConLeche.Name) (lvlsP : List Level) (holesP : List Expr)
    (st : EStore) : Prop :=
  Frontend.denoteNList st.ns names = some namesP ∧ denoteLs st.lss lvls = some lvlsP ∧
    Frontend.denoteEList st holes = some holesP

theorem TAArgs.ext {names : List NIdx} {lvls : LsIdx} {holes : List EIdx}
    {namesP : List ConLeche.Name} {lvlsP : List Level} {holesP : List Expr}
    {st st' : EStore} (hx : Ext st st')
    (h : TAArgs names lvls holes namesP lvlsP holesP st) :
    TAArgs names lvls holes namesP lvlsP holesP st' :=
  ⟨denoteNListE_ext hx _ _ h.1, denoteLs_ext h.2.1 hx, denoteEList_ext hx _ _ h.2.2⟩

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:130-170 targetAbsGo
**The memoised member abstraction computes the structural `targetAbs`**
(con-leche's `targetAbsGo_spec`, over handles): a fuel induction whose leaf
arms answer the node itself, whose `const` arm is the member lookup at
hash-consed level-list and name comparisons, and whose five binder arms go
through the memo. -/
theorem targetAbsGo_spec (names : List NIdx) (lvls : LsIdx) (holes : List EIdx)
    (namesP : List ConLeche.Name) (lvlsP : List Level) (holesP : List Expr) :
    ∀ (fuel : Nat) (memo : Std.HashMap EIdx EIdx) (h : EIdx) (hP : Expr),
    PSpec (fun st => TAArgs names lvls holes namesP lvlsP holesP st ∧
        denoteE st h = some hP ∧ TAMemoOK namesP lvlsP holesP memo st)
      (Arena.targetAbsGo names lvls holes memo fuel h)
      (fun st r => denoteE st r.1 = some (ConLeche.targetAbs namesP lvlsP holesP hP) ∧
        TAMemoOK namesP lvlsP holesP r.2 st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro memo h hP s₀ s' r hok _ hrun
    simp only [Arena.targetAbsGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro memo h hP s₀ s' r hok hp hrun
    obtain ⟨hA, hd, hm⟩ := hp
    simp only [Arena.targetAbsGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    have fin : ∀ {s₂ s₃ : AState} {rr : EIdx} {mm : Std.HashMap EIdx EIdx}
        {r' : EIdx × Std.HashMap EIdx EIdx},
        PStep s₀ s₂ → denoteE s₂.store rr = some (ConLeche.targetAbs namesP lvlsP holesP hP) →
        TAMemoOK namesP lvlsP holesP mm s₂.store →
        (pure ((rr, mm.insert h rr) : EIdx × Std.HashMap EIdx EIdx) :
            AM (EIdx × Std.HashMap EIdx EIdx)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ denoteE s₃.store r'.1 = some (ConLeche.targetAbs namesP lvlsP holesP hP) ∧
          TAMemoOK namesP lvlsP holesP r'.2 s₃.store := by
      intro s₂ s₃ rr mm r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, TAMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : EIdx} {r' : EIdx × Std.HashMap EIdx EIdx},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : EIdx × Std.HashMap EIdx EIdx) :
            AM (EIdx × Std.HashMap EIdx EIdx)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ denoteE s₃.store r'.1 = some (ConLeche.targetAbs namesP lvlsP holesP hP) ∧
          TAMemoOK namesP lvlsP holesP r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case fvar k ty =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case const n us =>
      obtain ⟨nm, ls, rfl, hn, hl⟩ := denote_const_inv hok.wf hw hd
      obtain ⟨hnames, hlvls, hholes⟩ := hA
      have hbeq : (us == lvls) = (ls == lvlsP) := PW.beq_lshandle_eq hok.wf hl hlvls
      have hfi := PW.findIdx_handle_eq hok.wf hn hnames
      simp only [ConLeche.targetAbs]
      dsimp only at h2
      rw [hbeq] at h2
      by_cases hls : (ls == lvlsP) = true
      · rw [if_pos hls] at h2
        rw [if_pos hls]
        rw [hfi] at h2
        cases ht : namesP.findIdx? (· == nm) with
        | some t =>
          rw [ht] at h2
          dsimp only at h2 ⊢
          obtain ⟨hnone, hsome⟩ := PW.denoteEList_getElem? hholes t
          cases hg : holes[t]? with
          | none =>
            rw [hg] at h2
            obtain ⟨rfl, rfl⟩ := pureOk h2
            have hn' : holesP[t]? = none := hnone.1 hg
            refine ⟨PStep.refl hok, ?_, hm⟩
            simp only [List.getD_eq_getElem?_getD, hn', Option.getD_none]
            exact hd
          | some x =>
            rw [hg] at h2
            obtain ⟨rfl, rfl⟩ := pureOk h2
            obtain ⟨xP, hxP, hx⟩ := hsome x hg
            refine ⟨PStep.refl hok, ?_, hm⟩
            simp only [List.getD_eq_getElem?_getD, hxP, Option.getD_some]
            exact hx
        | none =>
          rw [ht] at h2
          obtain ⟨rfl, rfl⟩ := pureOk h2
          exact ⟨PStep.refl hok, hd, hm⟩
      · rw [if_neg hls] at h2
        rw [if_neg hls]
        obtain ⟨rfl, rfl⟩ := pureOk h2
        exact ⟨PStep.refl hok, hd, hm⟩
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo f ef _ _ (a2, m1) hok ⟨hA, hf, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 a ea _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext ha hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internAppE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case lam ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok ⟨hA, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internLamE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok ⟨hA, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internForallEE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et _ _ (a2, m1) hok ⟨hA, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext hval hsA.ext, hmA⟩ hc2
        have hAB := hsA.trans hsB
        obtain ⟨p3, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨c2, m3⟩ := p3
        obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb _ _ (c2, m3) hsB.ok
          ⟨hA.ext hAB.ext, denote_ext hbd hAB.ext, hmB⟩ hc3
        obtain ⟨q, sd, hc4, hn4⟩ := bindOk hn3
        obtain ⟨hsD, hq⟩ := PW.internLetEE_run hsC.ok
          (denote_ext hrA (hsB.ext.trans hsC.ext)) (denote_ext hrB hsC.ext) hrC hc4
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn4
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hAB.trans hsC).trans hsD) (by rw [hq]; rfl) (hmC.ext hsD.ext) hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es _ _ (a2, m1) hok ⟨hA, hsub, hm⟩ hc1
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn1
        obtain ⟨hsC, hq⟩ := internProjE_run hsA.ok (denoteN_ext hn hsA.ext) hrA hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsC) (by rw [hq]; rfl) (hmA.ext hsC.ext) hz

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:240-245 targetAbsFast
**The executed member abstraction** (a fresh memo) computes the structural
`targetAbs` (con-leche's `@[csimp] targetAbs_eq_targetAbsFast`). -/
theorem targetAbs_spec (names : List NIdx) (lvls : LsIdx) (holes : List EIdx)
    (namesP : List ConLeche.Name) (lvlsP : List Level) (holesP : List Expr)
    (e : EIdx) (eP : Expr) :
    PSpec (fun st => TAArgs names lvls holes namesP lvlsP holesP st ∧
        denoteE st e = some eP)
      (Arena.targetAbs names lvls holes e)
      (RE (ConLeche.targetAbs namesP lvlsP holesP eP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hA, hd⟩ := hp
  simp only [Arena.targetAbs] at hrun
  obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ := targetAbsGo_spec names lvls holes namesP lvlsP holesP
    Arena.coreWalkFuel ∅ e eP s₀ s₁ q hok ⟨hA, hd, TAMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, hr⟩

end ConRon.Bridge.Inductives
