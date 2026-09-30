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
import ConLeche.Verify.Inductives.RecCheckScope

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

/-! ## The holes -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:248-251 targetHoles —
the `List.range` map read as the recursion the twin runs: the head hole at
`base`, the rest one further. -/
theorem targetHoles_cons (ty : Expr) (tys : List Expr) (base : Nat) :
    ConLeche.targetHoles (ty :: tys) base =
      .fvar base ty :: ConLeche.targetHoles tys (base + 1) := by
  simp only [ConLeche.targetHoles, List.length_cons, List.range_succ_eq_map,
    List.map_cons, List.map_map, Nat.add_zero, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, List.getD_cons_succ]
  congr 1
  omega

theorem targetHoles_nil (base : Nat) : ConLeche.targetHoles [] base = [] := rfl

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:248-251 targetHoles
**The holes of a rule frame**: member `t` is `.fvar (base + t)` at its
former's type, interned in member order. -/
theorem targetHoles_spec : ∀ (tys : List EIdx) (tysP : List Expr) (base : Nat),
    PSpec (fun st => Frontend.denoteEList st tys = some tysP)
      (Arena.targetHoles tys base) (REL (ConLeche.targetHoles tysP base)) := by
  intro tys
  induction tys with
  | nil =>
    intro tysP base s₀ s' r hok hd hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.targetHoles] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons ty tys ih =>
    intro tysP base s₀ s' r hok hd hrun
    simp only [Frontend.denoteEList] at hd
    cases h1 : denoteE s₀.store ty with
    | none => rw [h1] at hd; simp at hd
    | some tyP =>
    cases h2 : Frontend.denoteEList s₀.store tys with
    | none => rw [h1, h2] at hd; simp at hd
    | some rest =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [Arena.targetHoles] at hrun
    obtain ⟨v, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hv⟩ := PW.internFVarE_run hok h1 k1
    obtain ⟨vs, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hvs⟩ := ih rest (base + 1) s1 s2 vs p1.ok (denoteEList_ext p1.ext _ _ h2) k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, ?_⟩
    show Frontend.denoteEList _ (v :: vs) = _
    rw [targetHoles_cons]
    simp only [Frontend.denoteEList, denote_ext hv p2.ext, hvs]

/-! ## The class record's default, and the class at an index -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
(`deriving Inhabited`) — **the default class record denotes con-leche's
`default`**: the anonymous name, the pinned empty level list, and nothing
else.  `PSpecP`: the level list is the `emptyLevels` pin. -/
theorem targetMajorDefault_spec :
    PSpecP (fun _ => True) Arena.targetMajorDefault
      (fun st r => dMajor st r = some (default : ConLeche.TargetMajor)) := by
  intro s₀ s' r hok hp _ hrun
  simp only [Arena.targetMajorDefault] at hrun
  obtain ⟨a, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ha⟩ := internNNode_run hok
    (by intro c hc; simp [NNodeView.children] at hc) k1
  obtain ⟨ls, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hls⟩ := AM.of_run (P := fun t => t = s1) rfl k2
    (pinEmptyLevels_spec s1 (PinsOK.ofPStep hp p1))
  subst hs2
  obtain ⟨rfl, rfl⟩ := pureOk z2
  refine ⟨p1, ?_⟩
  simp only [denoteNView] at ha
  simp only [dMajor, ha, hls]
  rfl

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
(`Ms.getD c default`) — **the class at an index**: the denoted list's entry,
or the default record. -/
theorem targetMajorAt_spec (ms : List Arena.TargetMajor) (msP : List ConLeche.TargetMajor)
    (c : Nat) :
    PSpecP (fun st => ms.mapM (dMajor st) = some msP) (Arena.targetMajorAt ms c)
      (fun st r => dMajor st r = some (msP.getD c default)) := by
  intro s₀ s' r hok hp hms hrun
  simp only [Arena.targetMajorAt] at hrun
  have hj := mapM_option_getElem? (st := s₀.store) hms c
  rw [List.getD_eq_getElem?_getD]
  cases hc : ms[c]? with
  | none =>
    rw [hc] at hrun hj
    have : msP[c]? = none := hj
    rw [this, Option.getD_none]
    exact targetMajorDefault_spec s₀ s' r hok hp trivial hrun
  | some m =>
    rw [hc] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    rw [hc] at hj
    obtain ⟨mP, hmP, hd⟩ := hj
    rw [hmP, Option.getD_some]
    exact ⟨PStep.refl hok, hd⟩

/-! ## The two `FvMap` readbacks -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:277-281 Expr.eraseFVarTys
**Every free variable's annotation erased**: `replaceFVars` at the `.erase`
map. -/
theorem eraseFVarTys_spec (e : EIdx) (eP : Expr) :
    PSpecP (fun st => denoteE st e = some eP) (Arena.eraseFVarTys e)
      (RE (Expr.eraseFVarTys eP)) := by
  intro s₀ s' r hok hp hd hrun
  simp only [Arena.eraseFVarTys] at hrun
  exact replaceFVars_spec .erase _ e eP s₀ s' r hok hp ⟨rfl, hd⟩ hrun

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:305-308 targetCanonParams
**A term moved to the class's openers**: `replaceFVars` at the `.canon pfvs`
map. -/
theorem targetCanonParams_spec (pfvs : List EIdx) (pfvsP : List Expr) (e : EIdx)
    (eP : Expr) :
    PSpecP (fun st => Frontend.denoteEList st pfvs = some pfvsP ∧ denoteE st e = some eP)
      (Arena.targetCanonParams pfvs e) (RE (ConLeche.targetCanonParams pfvsP eP)) := by
  intro s₀ s' r hok hp hpre hrun
  obtain ⟨hpf, hd⟩ := hpre
  simp only [Arena.targetCanonParams] at hrun
  exact replaceFVars_spec (.canon pfvs) _ e eP s₀ s' r hok hp ⟨⟨pfvsP, hpf, rfl⟩, hd⟩ hrun

/-! ## The knot and the cutoffs, in run form -/

namespace RC

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1714 fvarB — **the free-variable
cutoff's run form** at this tier's frame: `Bridge/ExprOps/Ranges.lean`'s
`fvarB_spec` answers `fvarRange`, which is `Expr.fvarB` (`Expr.fvarB_eq`). -/
theorem fvarB_pstep {fuel : Nat} {s₀ s' : AState} {e : EIdx} {eP : Expr}
    {r : Nat} (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.fvarB fuel e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ s'.store = s₀.store ∧ r = Expr.fvarB eP := by
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.fvarB_spec fuel s₀ e hok (by rw [hd]; rfl))
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.wf⟩ ?_ ?_ h2 h3, h1, ?_⟩
  · rw [h1]; exact Ext.refl _
  · rw [h1]; exact BMExt.refl _
  · rw [h4 eP hd, Expr.fvarB_eq]

/-- con-leche: ConLeche/Verify/BridgeDecl.lean fueledOpsM — **a knot
inference, in run form**: `CoreSpec.knot`'s `infer` slot, its `SimE` answer
read as an `FOk` of the fueled operation. -/
theorem infer_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hknot : Core.KnotSpec μ env fe Arena.checkFuel) {s₀ s' : AState} {d : Nat}
    {e r : EIdx} {eP : Expr} (hok : CheckOK μ env fe s₀)
    (hd : denoteE s₀.store e = some eP) (hw : Expr.WScoped d eP)
    (hrun : Arena.inferTypeCore μ fe Arena.checkFuel d e s₀ = .ok (r, s')) :
    CoreStep μ env fe s₀ s' ∧ ∃ v, denoteE s'.store r = some v ∧ Expr.WScoped d v ∧
      FOk ((fueledOpsM μ).inferType env d eP) v := by
  obtain ⟨h1, h2, h3, v, hv, hwv, hF⟩ := AM.of_run (P := fun u => u = s₀)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s₀.store u.store ∧ u.pins = s₀.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) d eP u.store r)
    rfl hrun (hknot.infer s₀ d e eP hok hd hw)
  exact ⟨⟨h1, h2, h3⟩, v, hv, hwv, FOk.inferType hF⟩

/-- con-leche: ConLeche/Verify/BridgeDecl.lean fueledOpsM — **a knot defeq,
in run form**. -/
theorem defeq_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hknot : Core.KnotSpec μ env fe Arena.checkFuel) {s₀ s' : AState} {d : Nat}
    {a b : EIdx} {aP bP : Expr} {r : Bool} (hok : CheckOK μ env fe s₀)
    (ha : denoteE s₀.store a = some aP) (hb : denoteE s₀.store b = some bP)
    (hwa : Expr.WScoped d aP) (hwb : Expr.WScoped d bP)
    (hrun : Arena.isDefEqCore μ fe Arena.checkFuel d a b s₀ = .ok (r, s')) :
    CoreStep μ env fe s₀ s' ∧ FOk ((fueledOpsM μ).isDefEq env d aP bP) r := by
  obtain ⟨h1, h2, h3, hF⟩ := AM.of_run (P := fun u => u = s₀)
    (Q := fun x u => CheckOK μ env fe u ∧ Ext s₀.store u.store ∧ u.pins = s₀.pins ∧
      Core.SimV (ConLeche.isDefEqCore μ env) d aP bP x)
    rfl hrun (hknot.defeq s₀ d a b aP bP hok ha hb hwa hwb)
  exact ⟨⟨h1, h2, h3⟩, FOk.isDefEq hF⟩

/-- con-leche: none — a pure-grade `PSpecP` step taken at the core grade. -/
theorem pspecP_core {μ : CheckMode} {env : Env} {fe : IFEnv} {α : Type}
    {P : EStore → Prop} {c : AM α} {R : EStore → α → Prop} (h : PSpecP P c R)
    {s₀ s' : AState} {r : α} (hok : CheckOK μ env fe s₀) (hp : P s₀.store)
    (hrun : c s₀ = .ok (r, s')) : CoreStep μ env fe s₀ s' ∧ R s'.store r := by
  obtain ⟨hs, hr⟩ := h s₀ s' r hok.state hok.pins hp hrun
  exact ⟨hs.toCore hok, hr⟩

/-- con-leche: none — and a `PSpec` one. -/
theorem pspec_core {μ : CheckMode} {env : Env} {fe : IFEnv} {α : Type}
    {P : EStore → Prop} {c : AM α} {R : EStore → α → Prop} (h : PSpec P c R)
    {s₀ s' : AState} {r : α} (hok : CheckOK μ env fe s₀) (hp : P s₀.store)
    (hrun : c s₀ = .ok (r, s')) : CoreStep μ env fe s₀ s' ∧ R s'.store r := by
  obtain ⟨hs, hr⟩ := h s₀ s' r hok.state hp hrun
  exact ⟨hs.toCore hok, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:318 targetParamsDefEq
(the guard) — **the four closedness reads**, short-circuiting in the cited
`&&` order, with the continuation `k` the `do` elaborator pushed into every
branch: the run is `k` at con-leche's conjunction. -/
theorem closed4_bind_run {β : Type} {k : Bool → AM β} {s₀ s' : AState} {a b : EIdx}
    {aP bP : Expr} {n : Nat} {r : β}
    (hok : StateOK s₀) (ha : denoteE s₀.store a = some aP)
    (hb : denoteE s₀.store b = some bP)
    (hrun : (bvarB coreWalkFuel a >>= fun x =>
      if (x != 0) = true then (pure false >>= k) else
      (bvarB coreWalkFuel b >>= fun y =>
        if (y != 0) = true then (pure false >>= k) else
        (fvarB coreWalkFuel a >>= fun z =>
          if z > n then (pure false >>= k) else
          (fvarB coreWalkFuel b >>= fun w => pure (decide (w ≤ n)) >>= k)))) s₀
        = .ok (r, s')) :
    ∃ s₁, PStep s₀ s₁ ∧ k (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
      decide (bP.fvarB ≤ n)) s₁ = .ok (r, s') := by
  obtain ⟨x1, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, -, rfl⟩ := bvarB_pstep hok ha k1
  by_cases c1 : (aP.bvarB != 0) = true
  · rw [if_pos c1] at z1
    refine ⟨s1, p1, ?_⟩
    have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
      decide (bP.fvarB ≤ n)) = false := by
      simp only [bne_iff_ne, ne_eq] at c1
      simp [c1]
    rw [e]; exact z1
  · rw [if_neg c1] at z1
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at c1
    obtain ⟨x2, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, -, rfl⟩ := bvarB_pstep p1.ok (denote_ext hb p1.ext) k2
    by_cases c2 : (bP.bvarB != 0) = true
    · rw [if_pos c2] at z2
      refine ⟨s2, p1.trans p2, ?_⟩
      have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
        decide (bP.fvarB ≤ n)) = false := by
        simp only [bne_iff_ne, ne_eq] at c2
        simp [c1, c2]
      rw [e]; exact z2
    · rw [if_neg c2] at z2
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at c2
      obtain ⟨x3, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, -, rfl⟩ := fvarB_pstep (p1.trans p2).ok
        (denote_ext ha (p1.trans p2).ext) k3
      by_cases c3 : aP.fvarB > n
      · rw [if_pos c3] at z3
        refine ⟨s3, (p1.trans p2).trans p3, ?_⟩
        have : ¬ aP.fvarB ≤ n := by omega
        have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
          decide (bP.fvarB ≤ n)) = false := by simp [c1, c2, this]
        rw [e]; exact z3
      · rw [if_neg c3] at z3
        obtain ⟨x4, s4, k4, z4⟩ := bindOk z3
        have p123 := (p1.trans p2).trans p3
        obtain ⟨p4, -, rfl⟩ := fvarB_pstep p123.ok (denote_ext hb p123.ext) k4
        refine ⟨s4, p123.trans p4, ?_⟩
        have : aP.fvarB ≤ n := by omega
        have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
          decide (bP.fvarB ≤ n)) = decide (bP.fvarB ≤ n) := by simp [c1, c2, this]
        rw [e]; exact z4

end RC

/-! ## The class match, per component -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:310-329 targetParamsDefEq
**Per-component parameter defeq**: both sides closed over the openers, moved
to them and member-abstracted, then syntactically equal or inferred and
defeq; the answer is con-leche's at `fueledOpsM μ`, with `absM` the
structural `targetAbs` at the denoted names, levels and holes.

The scoping hypotheses are the cached bridge's (`targetParamsDefEqS_sim`,
`ConLeche/Verify/Cached/TargetRecC.lean`): the openers scoped at the depth,
and the abstraction preserving it. -/
theorem targetParamsDefEq_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (d : Nat)
    (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx)
    (namesP : List ConLeche.Name) (lvlsP : List Level) (holesP pfvsP : List Expr)
    (habs : ∀ e, Expr.WScoped d e → Expr.WScoped d (ConLeche.targetAbs namesP lvlsP holesP e))
    (hp : ∀ x ∈ pfvsP, Expr.WScoped d x) :
    ∀ (as bs : List EIdx) (asP bsP : List Expr),
    CSpecF μ env fe
      (fun st => TAArgs names lvls holes namesP lvlsP holesP st ∧
        Frontend.denoteEList st pfvs = some pfvsP ∧
        Frontend.denoteEList st as = some asP ∧ Frontend.denoteEList st bs = some bsP)
      (Arena.targetParamsDefEq μ fe d names lvls holes pfvs as bs)
      (fun _ r v => r = v)
      (ConLeche.targetParamsDefEq (fueledOpsM μ) env d
        (ConLeche.targetAbs namesP lvlsP holesP) pfvsP asP bsP) := by
  have hknot := hk.knot env fe henv
  intro as
  induction as with
  | nil =>
    intro bs asP bsP s₀ s' r hok hpre hrun
    obtain ⟨-, -, has, hbs⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at has
    subst has
    cases bs with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at hbs
      subst hbs
      simp only [Arena.targetParamsDefEq] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, true, rfl, by
        simp only [ConLeche.targetParamsDefEq]; exact FOk.pure true⟩
    | cons b bs =>
      obtain ⟨y, ys, -, -, rfl⟩ := Core.denoteEList_cons_inv hbs
      simp only [Arena.targetParamsDefEq] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, false, rfl, by
        simp only [ConLeche.targetParamsDefEq]; exact FOk.pure false⟩
  | cons a as ih =>
    intro bs asP bsP s₀ s' r hok hpre hrun
    obtain ⟨hA, hpf, has, hbs⟩ := hpre
    obtain ⟨aP, asP', ha, has', rfl⟩ := Core.denoteEList_cons_inv has
    cases bs with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at hbs
      subst hbs
      simp only [Arena.targetParamsDefEq] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, false, rfl, by
        simp only [ConLeche.targetParamsDefEq]; exact FOk.pure false⟩
    | cons b bs =>
    obtain ⟨bP, bsP', hb, hbs', rfl⟩ := Core.denoteEList_cons_inv hbs
    have hlen : pfvs.length = pfvsP.length := PW.denoteEList_length hpf
    simp only [Arena.targetParamsDefEq] at hrun
    obtain ⟨s1, p1, z1⟩ := RC.closed4_bind_run hok.state ha hb hrun
    generalize hcl : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ pfvs.length) &&
      decide (bP.fvarB ≤ pfvs.length)) = cl at z1
    have c1 := p1.toCore hok
    rw [ConLeche.targetParamsDefEq]
    rw [hlen] at hcl
    by_cases hc : cl = true
    · rw [hc] at z1 hcl
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at z1
      rw [if_pos hcl]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcl
      obtain ⟨⟨⟨_, _⟩, hfa⟩, hfb⟩ := hcl
      have hwa : Expr.WScoped d (ConLeche.targetAbs namesP lvlsP holesP
          (ConLeche.targetCanonParams pfvsP aP)) :=
        habs _ (targetCanonParams_WScoped hp aP (Expr.fvarsBelow_iff.mpr (Expr.fvarB_eq aP ▸ hfa)))
      have hwb : Expr.WScoped d (ConLeche.targetAbs namesP lvlsP holesP
          (ConLeche.targetCanonParams pfvsP bP)) :=
        habs _ (targetCanonParams_WScoped hp bP (Expr.fvarsBelow_iff.mpr (Expr.fvarB_eq bP ▸ hfb)))
      -- the four readbacks
      obtain ⟨ac, s2, k2, z2⟩ := bindOk z1
      obtain ⟨c2, hac⟩ := RC.pspecP_core (targetCanonParams_spec pfvs pfvsP a aP) c1.ok
        ⟨denoteEList_ext c1.ext _ _ hpf, denote_ext ha c1.ext⟩ k2
      obtain ⟨a', s3, k3, z3⟩ := bindOk z2
      have c12 := c1.trans c2
      obtain ⟨c3, ha'⟩ := RC.pspec_core (targetAbs_spec names lvls holes namesP lvlsP holesP
        ac _) c2.ok ⟨hA.ext c12.ext, hac⟩ k3
      have c13 := c12.trans c3
      obtain ⟨bc, s4, k4, z4⟩ := bindOk z3
      obtain ⟨c4, hbc⟩ := RC.pspecP_core (targetCanonParams_spec pfvs pfvsP b bP) c3.ok
        ⟨denoteEList_ext c13.ext _ _ hpf, denote_ext hb c13.ext⟩ k4
      have c14 := c13.trans c4
      obtain ⟨b', s5, k5, z5⟩ := bindOk z4
      obtain ⟨c5, hb'⟩ := RC.pspec_core (targetAbs_spec names lvls holes namesP lvlsP holesP
        bc _) c4.ok ⟨hA.ext c14.ext, hbc⟩ k5
      have c15 := c14.trans c5
      have ha'5 := denote_ext ha' (c4.ext.trans c5.ext)
      have hbeq := beq_ehandle_eq c5.ok.state.wf ha'5 hb'
      by_cases he : (a' == b') = true
      · rw [if_pos he] at z5
        rw [he] at hbeq
        rw [if_pos hbeq.symm]
        obtain ⟨c6, v, rfl, hv⟩ := ih bs asP' bsP' s5 s' r c5.ok
          ⟨hA.ext c15.ext, denoteEList_ext c15.ext _ _ hpf, denoteEList_ext c15.ext _ _ has',
            denoteEList_ext c15.ext _ _ hbs'⟩ z5
        exact ⟨c15.trans c6, r, rfl, hv⟩
      · rw [if_neg he] at z5
        have hne : ¬ (ConLeche.targetAbs namesP lvlsP holesP (ConLeche.targetCanonParams pfvsP aP)
            == ConLeche.targetAbs namesP lvlsP holesP (ConLeche.targetCanonParams pfvsP bP))
              = true := by rw [← hbeq]; exact he
        rw [if_neg hne]
        obtain ⟨t1, s6, k6, z6⟩ := bindOk z5
        obtain ⟨c6, v1, -, -, hF1⟩ := RC.infer_run hknot c5.ok ha'5 hwa k6
        obtain ⟨t2, s7, k7, z7⟩ := bindOk z6
        obtain ⟨c7, v2, -, -, hF2⟩ := RC.infer_run hknot c6.ok (denote_ext hb' c6.ext) hwb k7
        obtain ⟨q, s8, k8, z8⟩ := bindOk z7
        have c57 := c6.trans c7
        obtain ⟨c8, hF3⟩ := RC.defeq_run hknot c7.ok (denote_ext ha'5 c57.ext)
          (denote_ext hb' c57.ext) hwa hwb k8
        have c18 := (c15.trans c57).trans c8
        cases q with
        | true =>
          simp only [↓reduceIte] at z8
          obtain ⟨c9, v, rfl, hv⟩ := ih bs asP' bsP' s8 s' r c8.ok
            ⟨hA.ext c18.ext, denoteEList_ext c18.ext _ _ hpf, denoteEList_ext c18.ext _ _ has',
              denoteEList_ext c18.ext _ _ hbs'⟩ z8
          refine ⟨c18.trans c9, r, rfl, ?_⟩
          exact FOk.bind hF1 (FOk.bind hF2 (FOk.bind hF3 (by simpa using hv)))
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at z8
          obtain ⟨rfl, rfl⟩ := pureOk z8
          refine ⟨c18, false, rfl, ?_⟩
          exact FOk.bind hF1 (FOk.bind hF2 (FOk.bind hF3 (by simpa using FOk.pure false)))
    · have hc' : cl = false := by simpa using hc
      rw [hc'] at z1 hcl
      simp only [Bool.not_false, ↓reduceIte] at z1
      obtain ⟨rfl, rfl⟩ := pureOk z1
      rw [if_neg (by rw [hcl]; simp)]
      exact ⟨c1, false, rfl, FOk.pure false⟩

end ConRon.Bridge.Inductives
