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
  at the environment `env₂` that restriction denotes, under a FRESHNESS
  hypothesis on the recursors' names (see `consBlockRecsTF_spec`).

**Grades.**  The pure walks are `PSpec`/`PSpecP`; everything that calls the
knot or reads the readback caches (`instLPFast`, `lvlEq?`, `lvlsEq?`) is
`CSpec`/`CSpecF`; `nestedRuleSyn` and `auxRuleFireR` read the index but no
cache, so they are at the read grade `RdSpec` (`ReadOK` in, `PStep` out).
The stored-family statements (`sumRules_spec`, `tgtStoredRules_spec`,
`consBlockRecsTF_spec`) carry TWO environments: the knot's caches' (`CheckOK
μ envC feC`) and the lookup index's (`IFEnvOK env fe`), because the rules are
read at the constructors' view while the caches serve whatever index the
recursor stage ended on.  `nestedRuleSyn` had no Theorem-1 statement in any
tier; it is proved here (`nestedRuleSyn_spec` and its five components).
-/
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Inductives.StructParts
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.SumInstall
import ConRon.Bridge.Inductives.BlockParts
import ConRon.Bridge.Inductives.Positivity
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Cached.TargetRecC

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

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
    exact absurd hrun (fun hc => AM.fail_ok hc)
  | succ fuel ih =>
    intro memo h hP s₀ s' r hok hp hrun
    obtain ⟨hA, hd, hm⟩ := hp
    simp only [Arena.targetAbsGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := AM.bind_ok hrun
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
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hz
      exact ⟨hs, hb, TAMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : EIdx} {r' : EIdx × Std.HashMap EIdx EIdx},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : EIdx × Std.HashMap EIdx EIdx) :
            AM (EIdx × Std.HashMap EIdx EIdx)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ denoteE s₃.store r'.1 = some (ConLeche.targetAbs namesP lvlsP holesP hP) ∧
          TAMemoOK namesP lvlsP holesP r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case fvar k ty =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case const n us =>
      obtain ⟨nm, ls, rfl, hn, hl⟩ := denote_const_inv hok.wf hw hd
      obtain ⟨hnames, hlvls, hholes⟩ := hA
      have hbeq : (us == lvls) = (ls == lvlsP) := beq_lshandle_eq hok.wf hl hlvls
      have hfi := findIdx_handle_eq hok.wf hn hnames
      simp only [ConLeche.targetAbs]
      dsimp only at h2
      rw [hbeq] at h2
      by_cases hls : (ls == lvlsP) = true
      · rw [ite_eq_left hls] at h2
        rw [ite_eq_left hls]
        rw [hfi] at h2
        cases ht : namesP.findIdx? (· == nm) with
        | some t =>
          rw [ht] at h2
          dsimp only at h2 ⊢
          obtain ⟨hnone, hsome⟩ := denoteEList_getElem? hholes t
          cases hg : holes[t]? with
          | none =>
            rw [hg] at h2
            obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
            have hn' : holesP[t]? = none := hnone.1 hg
            refine ⟨PStep.refl hok, ?_, hm⟩
            simp only [List.getD_eq_getElem?_getD, hn', Option.getD_none]
            exact hd
          | some x =>
            rw [hg] at h2
            obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
            obtain ⟨xP, hxP, hx⟩ := hsome x hg
            refine ⟨PStep.refl hok, ?_, hm⟩
            simp only [List.getD_eq_getElem?_getD, hxP, Option.getD_some]
            exact hx
        | none =>
          rw [ht] at h2
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
          exact ⟨PStep.refl hok, hd, hm⟩
      · rw [ite_eq_right hls] at h2
        rw [ite_eq_right hls]
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
        exact ⟨PStep.refl hok, hd, hm⟩
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := AM.bind_ok h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo f ef _ _ (a2, m1) hok ⟨hA, hf, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := AM.bind_ok hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 a ea _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext ha hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := AM.bind_ok hn2
        obtain ⟨hsC, hq⟩ := internAppE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := AM.bind_ok hn3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case lam ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := AM.bind_ok h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok ⟨hA, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := AM.bind_ok hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := AM.bind_ok hn2
        obtain ⟨hsC, hq⟩ := internLamE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := AM.bind_ok hn3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := AM.bind_ok h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok ⟨hA, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := AM.bind_ok hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := AM.bind_ok hn2
        obtain ⟨hsC, hq⟩ := internForallEE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := AM.bind_ok hn3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := AM.bind_ok h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et _ _ (a2, m1) hok ⟨hA, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := AM.bind_ok hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev _ _ (b2, m2) hsA.ok
          ⟨hA.ext hsA.ext, denote_ext hval hsA.ext, hmA⟩ hc2
        have hAB := hsA.trans hsB
        obtain ⟨p3, sc, hc3, hn3⟩ := AM.bind_ok hn2
        obtain ⟨c2, m3⟩ := p3
        obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb _ _ (c2, m3) hsB.ok
          ⟨hA.ext hAB.ext, denote_ext hbd hAB.ext, hmB⟩ hc3
        obtain ⟨q, sd, hc4, hn4⟩ := AM.bind_ok hn3
        obtain ⟨hsD, hq⟩ := internLetEE_run hsC.ok
          (denote_ext hrA (hsB.ext.trans hsC.ext)) (denote_ext hrB hsC.ext) hrC hc4
        obtain ⟨y, sy, hy, hz⟩ := AM.bind_ok hn4
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin ((hAB.trans hsC).trans hsD) (by rw [hq]; rfl) (hmC.ext hsD.ext) hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := AM.bind_ok h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es _ _ (a2, m1) hok ⟨hA, hsub, hm⟩ hc1
        obtain ⟨q, sc, hc3, hn3⟩ := AM.bind_ok hn1
        obtain ⟨hsC, hq⟩ := internProjE_run hsA.ok (denoteN_ext hn hsA.ext) hrA hc3
        obtain ⟨y, sy, hy, hz⟩ := AM.bind_ok hn3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
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
  obtain ⟨q, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hstep, hr, _⟩ := targetAbsGo_spec names lvls holes namesP lvlsP holesP
    Arena.coreWalkFuel ∅ e eP s₀ s₁ q hok ⟨hA, hd, TAMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
    obtain ⟨v, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hv⟩ := internFVarE_run hok h1 k1
    obtain ⟨vs, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hvs⟩ := ih rest (base + 1) s1 s2 vs p1.ok (denoteEList_ext p1.ext _ _ h2) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
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
  obtain ⟨a, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, ha⟩ := internNNode_run hok
    (by intro c hc; simp [NNodeView.children] at hc) k1
  obtain ⟨ls, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨hs2, hls⟩ := AM.of_run (P := fun t => t = s1) rfl k2
    (pinEmptyLevels_spec s1 (PinsOK.ofPStep hp p1))
  subst hs2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
  obtain ⟨x1, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, -, rfl⟩ := bvarB_pstep hok ha k1
  by_cases c1 : (aP.bvarB != 0) = true
  · rw [ite_eq_left c1] at z1
    refine ⟨s1, p1, ?_⟩
    have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
      decide (bP.fvarB ≤ n)) = false := by
      simp only [bne_iff_ne, ne_eq] at c1
      simp [c1]
    rw [e]; exact z1
  · rw [ite_eq_right c1] at z1
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at c1
    obtain ⟨x2, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, -, rfl⟩ := bvarB_pstep p1.ok (denote_ext hb p1.ext) k2
    by_cases c2 : (bP.bvarB != 0) = true
    · rw [ite_eq_left c2] at z2
      refine ⟨s2, p1.trans p2, ?_⟩
      have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
        decide (bP.fvarB ≤ n)) = false := by
        simp only [bne_iff_ne, ne_eq] at c2
        simp [c1, c2]
      rw [e]; exact z2
    · rw [ite_eq_right c2] at z2
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at c2
      obtain ⟨x3, s3, k3, z3⟩ := AM.bind_ok z2
      obtain ⟨p3, -, rfl⟩ := fvarB_pstep (p1.trans p2).ok
        (denote_ext ha (p1.trans p2).ext) k3
      by_cases c3 : aP.fvarB > n
      · rw [ite_eq_left c3] at z3
        refine ⟨s3, (p1.trans p2).trans p3, ?_⟩
        have : ¬ aP.fvarB ≤ n := by omega
        have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
          decide (bP.fvarB ≤ n)) = false := by simp [c1, c2, this]
        rw [e]; exact z3
      · rw [ite_eq_right c3] at z3
        obtain ⟨x4, s4, k4, z4⟩ := AM.bind_ok z3
        have p123 := (p1.trans p2).trans p3
        obtain ⟨p4, -, rfl⟩ := fvarB_pstep p123.ok (denote_ext hb p123.ext) k4
        refine ⟨s4, p123.trans p4, ?_⟩
        have : aP.fvarB ≤ n := by omega
        have e : (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ n) &&
          decide (bP.fvarB ≤ n)) = decide (bP.fvarB ≤ n) := by simp [c1, c2, this]
        rw [e]; exact z4

/-! ### The block's shape, taken apart -/

/-- con-leche: none — a denoted constructor list's name test is the pure one. -/
theorem ctors_any_name {st : EStore} (hwf : StoreWF st) {n : NIdx} {nP : ConLeche.Name}
    (hn : denoteN st.ns n = some nP) :
    ∀ {cs : List (IConstantVal × Nat)} {csP : List (ConstantVal × Nat)},
      dCtors st cs = some csP → cs.any (·.1.name == n) = csP.any (·.1.name == nP) := by
  intro cs
  induction cs with
  | nil => intro csP h; simp only [dCtors, List.mapM_nil] at h; cases h; rfl
  | cons c cs ih =>
    intro csP h
    simp only [dCtors, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hc : dCtor st c with
    | none => rw [hc] at h; simp at h
    | some cP =>
      rw [hc] at h
      cases hcs : cs.mapM (dCtor st) with
      | none => rw [hcs] at h; simp at h
      | some rest =>
        rw [hcs] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [dCtor, Option.map_eq_some_iff] at hc
        obtain ⟨cv, hcv, rfl⟩ := hc
        simp only [List.any_cons, beq_handle_eq hwf (denoteCV_name hcv) hn, ih hcs]

/-- con-leche: none — a denoted normal-form entry, field by field. -/
theorem dCtorNf_inv {st : EStore} {n : Arena.NestCtorNf} {nP : ConLeche.NestCtorNf}
    (h : dCtorNf st n = some nP) :
    denoteN st.ns n.ctor = some nP.ctor ∧ denoteLs st.lss n.lvls = some nP.lvls ∧
      Frontend.denoteEList st n.ds = some nP.ds ∧ denoteE st n.ty = some nP.ty := by
  simp only [dCtorNf] at h
  cases h1 : denoteN st.ns n.ctor with
  | none => rw [h1] at h; exact nomatch h
  | some c =>
  cases h2 : denoteLs st.lss n.lvls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some us =>
  cases h3 : Frontend.denoteEList st n.ds with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some ds =>
  cases h4 : denoteE st n.ty with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some ty =>
  rw [h1, h2, h3, h4] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- con-leche: none — `lvlsEq?` in run form at the core grade. -/
theorem lvlsEq?_run {μ : CheckMode} {env : Env} {fe : IFEnv} {s₀ s' : AState}
    {us vs : LsIdx} {usP vsP : List Level} {r : Option Bool}
    (hok : CheckOK μ env fe s₀) (hu : denoteLs s₀.store.lss us = some usP)
    (hv : denoteLs s₀.store.lss vs = some vsP)
    (hrun : Arena.lvlsEq? us vs s₀ = .ok (r, s')) :
    CoreStep μ env fe s₀ s' ∧ r = Level.isEquivList usP vsP := by
  obtain ⟨h1, h2, h3, lus, lvs, hu', hv', hr⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (Core.lvlsEq?_spec s₀ us vs hok)
  rw [hu] at hu'; rw [hv] at hv'
  obtain rfl := Option.some.inj hu'
  obtain rfl := Option.some.inj hv'
  exact ⟨⟨h1, by rw [h2]; exact Ext.refl _, h3⟩, hr⟩

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
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, true, rfl, by
        simp only [ConLeche.targetParamsDefEq]; exact FOk.pure true⟩
    | cons b bs =>
      obtain ⟨y, ys, -, -, rfl⟩ := Core.denoteEList_cons_inv hbs
      simp only [Arena.targetParamsDefEq] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, false, rfl, by
        simp only [ConLeche.targetParamsDefEq]; exact FOk.pure false⟩
    | cons b bs =>
    obtain ⟨bP, bsP', hb, hbs', rfl⟩ := Core.denoteEList_cons_inv hbs
    have hlen : pfvs.length = pfvsP.length := denoteEList_length hpf
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
      rw [ite_eq_left hcl]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcl
      obtain ⟨⟨⟨_, _⟩, hfa⟩, hfb⟩ := hcl
      have hwa : Expr.WScoped d (ConLeche.targetAbs namesP lvlsP holesP
          (ConLeche.targetCanonParams pfvsP aP)) :=
        habs _ (targetCanonParams_WScoped hp aP (Expr.fvarsBelow_iff.mpr (Expr.fvarB_eq aP ▸ hfa)))
      have hwb : Expr.WScoped d (ConLeche.targetAbs namesP lvlsP holesP
          (ConLeche.targetCanonParams pfvsP bP)) :=
        habs _ (targetCanonParams_WScoped hp bP (Expr.fvarsBelow_iff.mpr (Expr.fvarB_eq bP ▸ hfb)))
      -- the four readbacks
      obtain ⟨ac, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨c2, hac⟩ := RC.pspecP_core (targetCanonParams_spec pfvs pfvsP a aP) c1.ok
        ⟨denoteEList_ext c1.ext _ _ hpf, denote_ext ha c1.ext⟩ k2
      obtain ⟨a', s3, k3, z3⟩ := AM.bind_ok z2
      have c12 := c1.trans c2
      obtain ⟨c3, ha'⟩ := RC.pspec_core (targetAbs_spec names lvls holes namesP lvlsP holesP
        ac _) c2.ok ⟨hA.ext c12.ext, hac⟩ k3
      have c13 := c12.trans c3
      obtain ⟨bc, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨c4, hbc⟩ := RC.pspecP_core (targetCanonParams_spec pfvs pfvsP b bP) c3.ok
        ⟨denoteEList_ext c13.ext _ _ hpf, denote_ext hb c13.ext⟩ k4
      have c14 := c13.trans c4
      obtain ⟨b', s5, k5, z5⟩ := AM.bind_ok z4
      obtain ⟨c5, hb'⟩ := RC.pspec_core (targetAbs_spec names lvls holes namesP lvlsP holesP
        bc _) c4.ok ⟨hA.ext c14.ext, hbc⟩ k5
      have c15 := c14.trans c5
      have ha'5 := denote_ext ha' (c4.ext.trans c5.ext)
      have hbeq := beq_of_denoteE c5.ok.state.wf ha'5 hb'
      by_cases he : (a' == b') = true
      · rw [ite_eq_left he] at z5
        rw [he] at hbeq
        rw [ite_eq_left hbeq.symm]
        obtain ⟨c6, v, rfl, hv⟩ := ih bs asP' bsP' s5 s' r c5.ok
          ⟨hA.ext c15.ext, denoteEList_ext c15.ext _ _ hpf, denoteEList_ext c15.ext _ _ has',
            denoteEList_ext c15.ext _ _ hbs'⟩ z5
        exact ⟨c15.trans c6, r, rfl, hv⟩
      · rw [ite_eq_right he] at z5
        have hne : ¬ (ConLeche.targetAbs namesP lvlsP holesP (ConLeche.targetCanonParams pfvsP aP)
            == ConLeche.targetAbs namesP lvlsP holesP (ConLeche.targetCanonParams pfvsP bP))
              = true := by rw [← hbeq]; exact he
        rw [ite_eq_right hne]
        obtain ⟨t1, s6, k6, z6⟩ := AM.bind_ok z5
        obtain ⟨c6, v1, -, -, hF1⟩ := infer_crun hk henv c5.ok ha'5 hwa k6
        obtain ⟨t2, s7, k7, z7⟩ := AM.bind_ok z6
        obtain ⟨c7, v2, -, -, hF2⟩ := infer_crun hk henv c6.ok (denote_ext hb' c6.ext) hwb k7
        obtain ⟨q, s8, k8, z8⟩ := AM.bind_ok z7
        have c57 := c6.trans c7
        obtain ⟨c8, hF3⟩ := defeq_crun hknot c7.ok (denote_ext ha'5 c57.ext)
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
          obtain ⟨rfl, rfl⟩ := AM.pure_ok z8
          refine ⟨c18, false, rfl, ?_⟩
          exact FOk.bind hF1 (FOk.bind hF2 (FOk.bind hF3 (by simpa using FOk.pure false)))
    · have hc' : cl = false := by simpa using hc
      rw [hc'] at z1 hcl
      simp only [Bool.not_false, ↓reduceIte] at z1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      rw [ite_eq_right (by rw [hcl]; simp)]
      exact ⟨c1, false, rfl, FOk.pure false⟩

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:331-340 targetClassMatch
**A class matches a recorded instantiation**: the levels by
`Level.isEquivList` (the cached `lvlsEq?`), then `targetParamsDefEq` over
the class's openers with the members abstracted to the holes on top.  The
scoping hypotheses are the cached bridge's (`targetClassMatchS_sim`): the
formers closed, the openers scoped by their own count. -/
theorem targetClassMatch_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (formerTys pfvs : List EIdx) (formerTysP pfvsP : List Expr)
    (us lvls : LsIdx) (usP lvlsP : List Level) (ds eds : List EIdx) (dsP edsP : List Expr)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t)
    (hp : ∀ x ∈ pfvsP, Expr.WScoped pfvsP.length x) :
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        Frontend.denoteEList st pfvs = some pfvsP ∧ denoteLs st.lss us = some usP ∧
        Frontend.denoteEList st ds = some dsP ∧ denoteLs st.lss lvls = some lvlsP ∧
        Frontend.denoteEList st eds = some edsP)
      (Arena.targetClassMatch μ fe p formerTys pfvs us ds lvls eds)
      (fun _ r v => r = v)
      (ConLeche.targetClassMatch (fueledOpsM μ) env pP formerTysP pfvsP usP dsP lvlsP edsP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hsh, hft, hpf, hus, hds, hlv, heds⟩ := hpre
  simp only [Arena.targetClassMatch] at hrun
  obtain ⟨q, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨c1, rfl⟩ := RC.lvlsEq?_run hok hus hlv k1
  simp only [ConLeche.targetClassMatch]
  cases hq : Level.isEquivList usP lvlsP with
  | none =>
    rw [hq] at z1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    exact ⟨c1, false, rfl, by simp only [reduceCtorEq, beq_iff_eq]; exact FOk.pure false⟩
  | some b =>
    cases b with
    | false =>
      rw [hq] at z1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      exact ⟨c1, false, rfl, by simp; exact FOk.pure false⟩
    | true =>
      rw [hq] at z1
      dsimp only at z1
      obtain ⟨bl, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨c2, hbl⟩ := RC.pspec_core (paramLevels_spec p.lps pP.lps) c1.ok
        (denoteNListE_ext c1.ext _ _ (BlockShape.lps_spec hsh)) k2
      have c12 := c1.trans c2
      obtain ⟨hs, s3, k3, z3⟩ := AM.bind_ok z2
      obtain ⟨c3, hhs⟩ := RC.pspec_core (targetHoles_spec formerTys formerTysP pfvs.length)
        c2.ok (denoteEList_ext c12.ext _ _ hft) k3
      have c13 := c12.trans c3
      have hlen : pfvs.length = pfvsP.length := denoteEList_length hpf
      rw [hlen] at hhs z3
      obtain ⟨c4, v, rfl, hv⟩ := targetParamsDefEq_spec fe hk henv
        (pfvsP.length + formerTysP.length) p.memberNames bl hs pfvs pP.memberNames
        (pP.lps.map Level.param) (ConLeche.targetHoles formerTysP pfvsP.length) pfvsP
        (targetAbs_WScoped (Cached.targetHoles_WScoped hformer pfvsP.length))
        (fun x hx => (hp x hx).mono (by omega)) ds eds dsP edsP s3 s' r c3.ok
        ⟨⟨denoteNListE_ext c13.ext _ _ (BlockShape.memberNames_spec hsh),
            denoteLs_ext hbl c3.ext, hhs⟩,
          denoteEList_ext c13.ext _ _ hpf, denoteEList_ext c13.ext _ _ hds,
          denoteEList_ext c13.ext _ _ heds⟩ (by rw [← denoteEList_length hft]; exact z3)
      exact ⟨c13.trans c4, r, rfl, by simpa using hv⟩

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:342-354 targetMajorNfs
**The walk's recorded constructor normal forms of a class**: the entries of
the class's constructors whose instantiation the class matches, the tail
first. -/
theorem targetMajorNfs_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (formerTys pfvs : List EIdx) (formerTysP pfvsP : List Expr)
    (us : LsIdx) (usP : List Level) (ds : List EIdx) (dsP : List Expr)
    (ctors : List (IConstantVal × Nat)) (ctorsP : List (ConstantVal × Nat))
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t)
    (hp : ∀ x ∈ pfvsP, Expr.WScoped pfvsP.length x) :
    ∀ (es : List Arena.NestCtorNf) (esP : List ConLeche.NestCtorNf),
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        Frontend.denoteEList st pfvs = some pfvsP ∧ denoteLs st.lss us = some usP ∧
        Frontend.denoteEList st ds = some dsP ∧ dCtors st ctors = some ctorsP ∧
        es.mapM (dCtorNf st) = some esP)
      (Arena.targetMajorNfs μ fe p formerTys pfvs us ds ctors es)
      (fun st r v => r.mapM (dCtorNf st) = some v)
      (ConLeche.targetMajorNfs (fueledOpsM μ) env pP formerTysP pfvsP usP dsP ctorsP esP) := by
  intro es
  induction es with
  | nil =>
    intro esP s₀ s' r hok hpre hrun
    obtain ⟨-, -, -, -, -, -, hes⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hes
    subst hes
    simp only [Arena.targetMajorNfs] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, [], rfl, by simp only [ConLeche.targetMajorNfs]; exact FOk.pure _⟩
  | cons e es ih =>
    intro esP s₀ s' r hok hpre hrun
    obtain ⟨hsh, hft, hpf, hus, hds, hcs, hes⟩ := hpre
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hes
    cases he : dCtorNf s₀.store e with
    | none => rw [he] at hes; simp at hes
    | some eP =>
    rw [he] at hes
    cases hes' : es.mapM (dCtorNf s₀.store) with
    | none => rw [hes'] at hes; simp at hes
    | some esP' =>
    rw [hes'] at hes
    simp only [Option.bind_some, Option.some.injEq] at hes
    subst hes
    simp only [Arena.targetMajorNfs] at hrun
    obtain ⟨rest, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, v, hv, hF⟩ := ih esP' s₀ s1 rest hok ⟨hsh, hft, hpf, hus, hds, hcs, hes'⟩ k1
    obtain ⟨hctor, hlv, hed, -⟩ := RC.dCtorNf_inv (dCtorNf_ext c1.ext _ _ he)
    have hany := RC.ctors_any_name c1.ok.state.wf hctor (dCtors_ext c1.ext _ _ hcs)
    simp only [ConLeche.targetMajorNfs]
    by_cases ha : (ctors.any (·.1.name == e.ctor)) = true
    · rw [ite_eq_left ha] at z1
      have ha' : (ctorsP.any (·.1.name == eP.ctor)) = true := by rw [← hany]; exact ha
      obtain ⟨m, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨c2, w, rfl, hW⟩ := targetClassMatch_spec fe hk henv p pP formerTys pfvs
        formerTysP pfvsP us e.lvls usP eP.lvls ds e.ds dsP eP.ds hformer hp s1 s2 m c1.ok
        ⟨dShape_ext c1.ext _ _ hsh, denoteEList_ext c1.ext _ _ hft,
          denoteEList_ext c1.ext _ _ hpf, denoteLs_ext hus c1.ext,
          denoteEList_ext c1.ext _ _ hds, hlv, hed⟩ k2
      have hv2 : rest.mapM (dCtorNf s2.store) = some v := dCtorNf_ext.list c2.ext _ _ hv
      have he2 : dCtorNf s2.store e = some eP := dCtorNf_ext (c1.ext.trans c2.ext) _ _ he
      cases m with
      | true =>
        simp only [↓reduceIte] at z2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
        refine ⟨c1.trans c2, eP :: v, ?_, ?_⟩
        · simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, he2, hv2,
            Option.bind_some]
        · exact FOk.bind hF (by rw [ite_eq_left ha']; exact FOk.bind hW (by simp; exact FOk.pure _))
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at z2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
        refine ⟨c1.trans c2, v, hv2, ?_⟩
        exact FOk.bind hF (by rw [ite_eq_left ha']; exact FOk.bind hW (by simp; exact FOk.pure _))
    · rw [ite_eq_right ha] at z1
      have ha' : ¬ (ctorsP.any (·.1.name == eP.ctor)) = true := by rw [← hany]; exact ha
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      exact ⟨c1, v, hv, FOk.bind hF (by rw [ite_eq_right ha']; exact FOk.pure _)⟩

/-! ## A class's constructors, and the telescope reader -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:522-528 targetCtorAt
**A constructor's type at the major's levels**: as stored at a member, the
level instantiation at an outside inductive.  Core grade: `instLPFast`
reads through the three readback caches `CheckOK` keeps sound. -/
theorem targetCtorAt_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (M : Arena.TargetMajor) (MP : ConLeche.TargetMajor) (c : IConstantVal)
    (cP : ConstantVal) :
    CSpec μ env fe (fun st => dMajor st M = some MP ∧ Frontend.denoteCV st c = some cP)
      (Arena.targetCtorAt M c) (RE (ConLeche.targetCtorAt MP cP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hM, hc⟩ := hpre
  obtain ⟨-, hlv, -, -, -, -, hmem, -, -⟩ := dMajor_inv hM
  simp only [Arena.targetCtorAt] at hrun
  simp only [ConLeche.targetCtorAt, ← hmem]
  cases hm : M.member with
  | some t =>
    rw [hm] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, denoteCV_type hc⟩
  | none =>
    rw [hm] at hrun
    exact instLPFast_cstep hok (denoteCV_lps hc) hlv (denoteCV_type hc) hrun

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:558-563 targetPiDomsWith
**The domains of the first `|xs|` `∀` binders**, each instantiated at the
earlier `xs`; `none` exactly when con-leche's is. -/
theorem targetPiDomsWith_spec : ∀ (xs : List EIdx) (xsP : List Expr) (e : EIdx) (eP : Expr),
    PSpec (fun st => Frontend.denoteEList st xs = some xsP ∧ denoteE st e = some eP)
      (Arena.targetPiDomsWith xs e) (ROp REL (ConLeche.targetPiDomsWith xsP eP)) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP e eP s₀ s' r hok hpre hrun
    obtain ⟨hx, -⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.targetPiDomsWith] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, [], rfl, rfl⟩
  | cons x xs ih =>
    intro xsP e eP s₀ s' r hok hpre hrun
    obtain ⟨hx, hd⟩ := hpre
    obtain ⟨xP, xsP', hxP, hxsP, rfl⟩ := Core.denoteEList_cons_inv hx
    simp only [Arena.targetPiDomsWith] at hrun
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [ite_eq_left htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨hs1, ho⟩ := viewBind_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => AM.fail_ok hc)
      | some q =>
        obtain ⟨d, b, m⟩ := q
        have hw := view_of_viewBind_tag_forallE htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨b', s₂, h3, h4⟩ := AM.bind_ok h2
        obtain ⟨o1, o2, o3, o4, o5, -, o7⟩ := ExprOps.instantiate1Fast_run hok hxP
          (by rw [hbd]; rfl) h3
        have p2 : PStep s₀ s₂ := PStep.of_caches o1 o2 o3 o4 o5
        have hb' : denoteE s₂.store b' = some (bP.instantiate1 xP 0) := o7 bP hbd
        obtain ⟨q, s₃, h5, h6⟩ := AM.bind_ok h4
        obtain ⟨p3, hq⟩ := ih xsP' b' _ s₂ s₃ q p2.ok
          ⟨denoteEList_ext p2.ext _ _ hxsP, hb'⟩ h5
        simp only [ConLeche.targetPiDomsWith]
        cases q with
        | none =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
          refine ⟨p2.trans p3, ?_⟩
          show _ = none
          have : ConLeche.targetPiDomsWith xsP' (bP.instantiate1 xP) = none := hq
          rw [this]; rfl
        | some ds =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
          obtain ⟨dsP, hdsP, hdsR⟩ := hq
          refine ⟨p2.trans p3, dP :: dsP, ?_, ?_⟩
          · have : ConLeche.targetPiDomsWith xsP' (bP.instantiate1 xP) = some dsP := hdsP
            rw [this]; rfl
          · show Frontend.denoteEList _ (d :: ds) = _
            simp only [Frontend.denoteEList, denote_ext hdd (p2.ext.trans p3.ext), hdsR]
    · rw [ite_eq_right htg] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨PStep.refl hok, ?_⟩
      show _ = none
      cases eP with
      | forallE dP bP m =>
        exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => rfl

/-! ## An outside class, typed -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:441-458 targetPinTys
**An outside major's parameters, typed at the rule prefix**, in order.  The
scoping hypothesis is the cached bridge's (`targetPinTysS_sim`). -/
theorem targetPinTys_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (d : Nat) :
    ∀ (xs : List EIdx) (xsP : List Expr), (∀ x ∈ xsP, Expr.WScoped d x) →
    CSpecF μ env fe (fun st => Frontend.denoteEList st xs = some xsP)
      (Arena.targetPinTys μ fe d xs) (fun _ _ _ => True)
      (ConLeche.targetPinTys (fueledOpsM μ) env d xsP) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP _ s₀ s' r hok hx hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.targetPinTys] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, by simp only [ConLeche.targetPinTys]; exact FOk.pure ()⟩
  | cons x xs ih =>
    intro xsP hw s₀ s' r hok hx hrun
    obtain ⟨xP, xsP', hxP, hxsP, rfl⟩ := Core.denoteEList_cons_inv hx
    simp only [Arena.targetPinTys] at hrun
    obtain ⟨t, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, v, -, -, hF⟩ := infer_crun hk henv hok hxP (hw xP (by simp)) k1
    obtain ⟨c2, u, -, hG⟩ := ih xsP' (fun y hy => hw y (by simp [hy])) s1 s' r c1.ok
      (denoteEList_ext c1.ext _ _ hxsP) z1
    exact ⟨c1.trans c2, (), trivial, by
      simp only [ConLeche.targetPinTys]; exact FOk.bind hF (by cases u; exact hG)⟩

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:460-476 targetMajorPins
**The check at a resolved major**: nothing at a member; at an outside major
its parameters typed at the rule prefix and the instantiation `I.{us} D⃗`
typed there.  Scoping as the cached bridge's `targetMajorPinsS_sim`. -/
theorem targetMajorPins_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (rP : Nat)
    (M : Arena.TargetMajor) (MP : ConLeche.TargetMajor)
    (hds : MP.member = none → ∀ x ∈ MP.ds, Expr.WScoped rP x) :
    CSpecF μ env fe (fun st => dMajor st M = some MP)
      (Arena.targetMajorPins μ fe rP M) (fun _ _ _ => True)
      (ConLeche.targetMajorPins (fueledOpsM μ) env rP MP) := by
  intro s₀ s' r hok hM hrun
  obtain ⟨hind, hlv, hdsd, -, -, -, hmem, -, -⟩ := dMajor_inv hM
  simp only [Arena.targetMajorPins] at hrun
  simp only [ConLeche.targetMajorPins, ← hmem]
  cases hm : M.member with
  | some t =>
    rw [hm] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, by simp; exact FOk.pure ()⟩
  | none =>
    rw [hm] at hrun
    have hw := hds (by rw [← hmem, hm])
    obtain ⟨u, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, u', -, hF1⟩ := targetPinTys_spec fe hk henv rP M.ds MP.ds hw s₀ s1 u hok hdsd k1
    obtain ⟨hd, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hhd⟩ := internConstE_run c1.ok.state (denoteN_ext hind c1.ext)
      (denoteLs_ext hlv c1.ext) k2
    have c2 := c1.trans (p2.toCore c1.ok)
    obtain ⟨app, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨p3, happ⟩ := mkAppN_run M.ds MP.ds c2.ok.state hhd
      (denoteEList_ext c2.ext _ _ hdsd) k3
    have c3 := c2.trans (p3.toCore c2.ok)
    obtain ⟨t, s4, k4, z4⟩ := AM.bind_ok z3
    obtain ⟨c4, v, -, -, hF2⟩ := infer_crun hk henv c3.ok happ
      (Expr.WScoped.mkAppN (by simp [Expr.WScoped]) hw) k4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
    refine ⟨c3.trans c4, (), trivial, ?_⟩
    simp only [Option.isNone_none, ↓reduceIte]
    exact FOk.bind hF1 (by cases u'; exact FOk.bind hF2 (FOk.pure ()))

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:362-376 targetOutsideInst
**The instantiated type former of an OUTSIDE major**: its index count and its
result sort, read off the stored inductive at `mkFEnv env` (`CheckOK`'s index
clause relates the twin's lookup).  Core grade for `instLPFast`'s caches; the
pure side performs no operation. -/
theorem targetOutsideInst_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (I : NIdx) (IP : ConLeche.Name) (us : LsIdx) (usP : List Level) (ds : List EIdx)
    (dsP : List Expr) :
    CSpecF μ env fe
      (fun st => denoteN st.ns I = some IP ∧ denoteLs st.lss us = some usP ∧
        Frontend.denoteEList st ds = some dsP)
      (Arena.targetOutsideInst fe I us ds)
      (fun st r v => r.1 = v.1 ∧ denoteL st.ls r.2 = some v.2)
      (ConLeche.targetOutsideInst (m := FueledM) (mkFEnv env) IP usP dsP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hI, hus, hds⟩ := hpre
  simp only [Arena.targetOutsideInst] at hrun
  cases hf : fe.find? I with
  | none => rw [hf] at hrun; exact absurd hrun (fun hc => AM.fail_ok hc)
  | some ci =>
  rw [hf] at hrun
  cases ci with
  | indInfo cvI caps =>
    obtain ⟨c, hc, he⟩ := find_some_rel hok.ienv hI hf
    obtain ⟨cvIP, capsP, hcv, -, rfl⟩ := denoteCI_indInfo_inv hc
    dsimp only at hrun
    obtain ⟨tl, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, htl⟩ := instLPFast_cstep hok (denoteCV_lps hcv) hus (denoteCV_type hcv) k1
    obtain ⟨o, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, ho⟩ := (instPisWith_spec ds dsP tl _) s1 s2 o c1.ok.state
      ⟨denoteEList_ext c1.ext _ _ hds, htl⟩ k2
    have c2 := c1.trans (p2.toCore c1.ok)
    cases o with
    | none => exact absurd z2 (fun hc => AM.fail_ok hc)
    | some ty =>
    obtain ⟨tyP, htyP, hty⟩ := ho
    dsimp only at z2
    obtain ⟨pb, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨ibs, sh⟩ := pb
    obtain ⟨p3, hibs, hsh⟩ := piBinders_spec _ ty tyP s2 s3 _ c2.ok.state hty k3
    have c3 := c2.trans (p3.toCore c2.ok)
    dsimp only at z3
    obtain ⟨v, s4, k4, z4⟩ := AM.bind_ok z3
    obtain ⟨hs4, hv⟩ := view_run k4
    rw [hs4] at z4
    cases v with
    | sort l =>
      obtain ⟨lP, hlP, hl⟩ := denote_sort_inv c3.ok.state.wf hv hsh
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
      refine ⟨c3, ((Expr.piBinders tyP).1.length, lP), ⟨?_, hl⟩, 0, ?_⟩
      · exact denoteBinders_length hibs
      · unfold ConLeche.targetOutsideInst
        rw [mkFEnv_find?_fun, he]
        dsimp only
        rw [htyP]
        dsimp only
        rw [hlP]
        rfl
    | _ => exact absurd z4 (fun hc => AM.fail_ok hc)
  | _ => exact absurd hrun (fun hc => AM.fail_ok hc)

/-! ## The syntactic reading of a nested rule (`nestedRuleSyn`)

`Arena/CheckerBase.lean`'s twin of `ConLeche/Kernel/ExprOps.lean:1521-1559`,
which no tier had stated: the recursor stage is its only reader (through
`auxRuleFireR`).  It reads the index (`constsResolveFFast`), so its grade is
the read grade `RdSpec`: `ReadOK` in, `PStep` out. -/

/-- con-leche: none — **the read grade**: a twin that reads the index but
never the knot's caches (`constsResolveFFast`, `ReadOK`) moves only what a
pure step moves. -/
def RdSpec (env : Env) (fe : IFEnv) {α : Type} (P : EStore → Prop) (c : AM α)
    (R : EStore → α → Prop) : Prop :=
  ∀ (s₀ s' : AState) (r : α), ReadOK env fe s₀ → P s₀.store → c s₀ = .ok (r, s') →
    PStep s₀ s' ∧ R s'.store r

namespace RC

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1709-1710 hasFvarFast — run form. -/
theorem hasFvarFast_pstep {fuel : Nat} {s₀ s' : AState} {e : EIdx} {eP : Expr}
    {r : Bool} (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.hasFvarFast fuel e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r = eP.hasFvar := by
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.hasFvarFast_spec fuel s₀ e hok (by rw [hd]; rfl))
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.wf⟩ ?_ ?_ h2 h3, h4 eP hd⟩
  · rw [h1]; exact Ext.refl _
  · rw [h1]; exact BMExt.refl _

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1718-1719 looseBVarsBoundedFast —
run form. -/
theorem looseBVarsBoundedFast_pstep {fuel k : Nat} {s₀ s' : AState} {e : EIdx}
    {eP : Expr} {r : Bool} (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.looseBVarsBoundedFast fuel k e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r = eP.looseBVarsBounded k := by
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.looseBVarsBoundedFast_spec fuel k s₀ e hok (by rw [hd]; rfl))
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.wf⟩ ?_ ?_ h2 h3, h4 eP hd⟩
  · rw [h1]; exact Ext.refl _
  · rw [h1]; exact BMExt.refl _

end RC

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
(`(args.take cnP).map (lowerBVars k 0)`) — the lowered parameter prefix. -/
theorem lowerList_spec (k : Nat) : ∀ (xs : List EIdx) (xsP : List Expr),
    PSpec (fun st => Frontend.denoteEList st xs = some xsP) (Arena.lowerList k xs)
      (REL (xsP.map (Expr.lowerBVars k 0))) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP s₀ s' r hok hx hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.lowerList] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons x xs ih =>
    intro xsP s₀ s' r hok hx hrun
    obtain ⟨xP, xsP', hxP, hxsP, rfl⟩ := Core.denoteEList_cons_inv hx
    simp only [Arena.lowerList] at hrun
    obtain ⟨y, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨o1, o2, o3, o4, o5, -, o7⟩ := ExprOps.lowerBVarsFast_run hok
      (by rw [hxP]; rfl) k1
    have p1 : PStep s₀ s1 := PStep.of_caches o1 o2 o3 o4 o5
    obtain ⟨ys, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hys⟩ := ih xsP' s1 s2 ys p1.ok (denoteEList_ext p1.ext _ _ hxsP) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨p1.trans p2, ?_⟩
    show Frontend.denoteEList _ (y :: ys) = _
    simp only [List.map_cons, Frontend.denoteEList, denote_ext (o7 xP hxP) p2.ext, hys]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
(`pins.map (liftLooseBVars k 0)`) — the lift back. -/
theorem liftList_spec (k : Nat) : ∀ (xs : List EIdx) (xsP : List Expr),
    PSpec (fun st => Frontend.denoteEList st xs = some xsP) (Arena.liftList k xs)
      (REL (xsP.map (Expr.liftLooseBVars k 0))) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP s₀ s' r hok hx hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.liftList] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons x xs ih =>
    intro xsP s₀ s' r hok hx hrun
    obtain ⟨xP, xsP', hxP, hxsP, rfl⟩ := Core.denoteEList_cons_inv hx
    simp only [Arena.liftList] at hrun
    obtain ⟨y, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hy⟩ := liftFast_pstep hok hxP k1
    obtain ⟨ys, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hys⟩ := ih xsP' s1 s2 ys p1.ok (denoteEList_ext p1.ext _ _ hxsP) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨p1.trans p2, ?_⟩
    show Frontend.denoteEList _ (y :: ys) = _
    simp only [Frontend.denoteEList, List.map_cons, denote_ext hy p2.ext, hys]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn (the pins'
guard) — the four-way `&&` per pin, left to right, at `resolves :=
(·.constsResolve env)`. -/
theorem pinsWf_spec {env : Env} (fe : IFEnv) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (rP : Nat) : ∀ (ps : List EIdx) (psP : List Expr),
    RdSpec env fe (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        Frontend.denoteEList st ps = some psP)
      (Arena.pinsWf fe lps rP ps)
      (RV (psP.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
        p.constsResolve env && p.allLevelParamsDefined lpsP))) := by
  intro ps
  induction ps with
  | nil =>
    intro psP s₀ s' r hok hpre hrun
    obtain ⟨-, hx⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.pinsWf] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok.state, rfl⟩
  | cons q qs ih =>
    intro psP s₀ s' r hok hpre hrun
    obtain ⟨hl, hx⟩ := hpre
    obtain ⟨qP, qsP, hqP, hqsP, rfl⟩ := Core.denoteEList_cons_inv hx
    simp only [Arena.pinsWf] at hrun
    obtain ⟨b1, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, rfl⟩ := RC.hasFvarFast_pstep hok.state hqP k1
    simp only [List.all_cons]
    by_cases c1 : qP.hasFvar = true
    · rw [ite_eq_left c1] at z1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      exact ⟨p1, by simp [c1]⟩
    · rw [ite_eq_right c1] at z1
      obtain ⟨b2, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨p2, rfl⟩ := RC.looseBVarsBoundedFast_pstep p1.ok (denote_ext hqP p1.ext) k2
      have p12 := p1.trans p2
      by_cases c2 : qP.looseBVarsBounded rP = true
      · rw [ite_eq_right (by simp [c2])] at z2
        obtain ⟨b3, s3, k3, z3⟩ := AM.bind_ok z2
        obtain ⟨p3, rfl⟩ := constsResolveFFast_pstep (hok.mono p12.ok p12.ext p12.pins)
          (denote_ext hqP p12.ext) k3
        have p13 := p12.trans p3
        by_cases c3 : qP.constsResolve env = true
        · rw [ite_eq_right (by simp [c3])] at z3
          obtain ⟨b4, s4, k4, z4⟩ := AM.bind_ok z3
          obtain ⟨hs4, hc4, hp4, rfl⟩ := allLevelParamsDefined_run p13.ok
            (denoteNListE_ext p13.ext _ _ hl) (denote_ext hqP p13.ext) k4
          have p4 : PStep s3 s4 := PStep.of_caches ⟨by rw [hs4]; exact p13.ok.wf⟩
            (by rw [hs4]; exact Ext.refl _) (by rw [hs4]; exact BMExt.refl _) hc4 hp4
          have p14 := p13.trans p4
          by_cases c4 : qP.allLevelParamsDefined lpsP = true
          · rw [ite_eq_right (by simp [c4])] at z4
            obtain ⟨p5, hr⟩ := ih qsP s4 s' r (hok.mono p14.ok p14.ext p14.pins)
              ⟨denoteNListE_ext p14.ext _ _ hl, denoteEList_ext p14.ext _ _ hqsP⟩ z4
            exact ⟨p14.trans p5, by rw [hr]; simp [c1, c2, c3, c4]⟩
          · rw [ite_eq_left (by simpa using c4)] at z4
            obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
            exact ⟨p14, by simp [c1, c2, c3, c4]⟩
        · rw [ite_eq_left (by simpa using c3)] at z3
          obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
          exact ⟨p13, by simp [c1, c2, c3]⟩
      · rw [ite_eq_left (by simpa using c2)] at z2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
        exact ⟨p12, by simp [c1, c2]⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
(`lvls.all (Level.allParamsDefined lps)`) — the cursor recursion. -/
theorem levelsDeclaredFrom_spec (ps : List ConLeche.Name) :
    ∀ (ls : List LIdx) (lsP : List Level),
    PSpec (fun st => denoteLList st.ls ls = some lsP) (Arena.levelsDeclaredFrom ps ls)
      (RV (lsP.all (Level.allParamsDefined ps))) := by
  intro ls
  induction ls with
  | nil =>
    intro lsP s₀ s' r hok hx hrun
    simp only [denoteLList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.levelsDeclaredFrom] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons l ls ih =>
    intro lsP s₀ s' r hok hx hrun
    simp only [denoteLList, opt2] at hx
    cases hl : denoteL s₀.store.ls l with
    | none => rw [hl] at hx; simp at hx
    | some lP =>
    cases hls : denoteLList s₀.store.ls ls with
    | none => rw [hl, hls] at hx; simp at hx
    | some lsP' =>
    rw [hl, hls] at hx
    obtain rfl := (Option.some.inj hx).symm
    simp only [Arena.levelsDeclaredFrom] at hrun
    obtain ⟨lv, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hlv⟩ := readLevel_run k1
    rw [hs1] at z1
    rw [hl] at hlv
    obtain rfl := Option.some.inj hlv
    simp only [List.all_cons]
    by_cases c : Level.allParamsDefined ps lP = true
    · rw [ite_eq_left c] at z1
      obtain ⟨p, hr⟩ := ih lsP' s₀ s' r hok hls z1
      exact ⟨p, by rw [hr]; simp [c]⟩
    · rw [ite_eq_right c] at z1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      exact ⟨PStep.refl hok, by simp [c]⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — the
levels' guard, the names read once. -/
theorem levelsDeclared_spec (lps : List NIdx) (lpsP : List ConLeche.Name) (ls : List LIdx)
    (lsP : List Level) :
    PSpec (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteLList st.ls ls = some lsP)
      (Arena.levelsDeclared lps ls) (RV (lsP.all (Level.allParamsDefined lpsP))) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hl, hx⟩ := hpre
  simp only [Arena.levelsDeclared] at hrun
  obtain ⟨ps, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hps⟩ := readNames_run k1
  rw [hs1] at z1
  rw [hl] at hps
  obtain rfl := Option.some.inj hps
  exact levelsDeclaredFrom_spec _ ls lsP s₀ s' r hok hx z1

/-- con-leche: none — the answer relation of `nestedRuleSyn`: the level
handles and the pin handles denote. -/
abbrev RSyn (x : List Level × List Expr) : EStore → List LIdx × List EIdx → Prop :=
  fun st r => denoteLList st.ls r.1 = some x.1 ∧ Frontend.denoteEList st r.2 = some x.2

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — the
pins' and the levels' guards, in the cited `∧` order. -/
theorem nestedRuleSynGuards_spec {env : Env} (fe : IFEnv) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (lvls : LsIdx) (lvlsP : List Level) (rP : Nat)
    (pins : List EIdx) (pinsP : List Expr) :
    RdSpec env fe (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteLs st.lss lvls = some lvlsP ∧ Frontend.denoteEList st pins = some pinsP)
      (Arena.nestedRuleSynGuards fe lps lvls rP pins)
      (ROp RSyn (if pinsP.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
          p.constsResolve env && p.allLevelParamsDefined lpsP) = true ∧
          lvlsP.all (Level.allParamsDefined lpsP) = true then some (lvlsP, pinsP) else none)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hl, hlv, hpins⟩ := hpre
  simp only [Arena.nestedRuleSynGuards] at hrun
  obtain ⟨b, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, rfl⟩ := pinsWf_spec fe lps lpsP rP pins pinsP s₀ s1 b hok ⟨hl, hpins⟩ k1
  by_cases c1 : pinsP.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
      p.constsResolve env && p.allLevelParamsDefined lpsP) = true
  · rw [ite_eq_right (by simp [c1])] at z1
    obtain ⟨ls, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨hs2, hv⟩ := viewLs_run k2
    rw [hs2] at z2
    have hls : denoteLList s1.store.ls ls = some lvlsP :=
      denoteLs_of_view hv (denoteLs_ext hlv p1.ext)
    obtain ⟨b2, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨p3, rfl⟩ := levelsDeclared_spec lps lpsP ls lvlsP s1 s3 b2 p1.ok
      ⟨denoteNListE_ext p1.ext _ _ hl, hls⟩ k3
    have p13 := p1.trans p3
    by_cases c2 : lvlsP.all (Level.allParamsDefined lpsP) = true
    · rw [ite_eq_right (by simp [c2])] at z3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
      refine ⟨p13, (lvlsP, pinsP), by rw [ite_eq_left ⟨c1, c2⟩], ?_, ?_⟩
      · exact denoteLList_ext p3.ext.lss.ls _ _ hls
      · exact denoteEList_ext p13.ext _ _ hpins
    · rw [ite_eq_left (by simpa using c2)] at z3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
      exact ⟨p13, by rw [ite_eq_right (fun h => c2 h.2)]; rfl⟩
  · rw [ite_eq_left (by simpa using c1)] at z1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    exact ⟨p1, by rw [ite_eq_right (fun h => c1 h.1)]; rfl⟩

namespace RC

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1541-1557 nestedRuleSyn — **the
reading at the major's domain** `dom = D.{lvls} args`, as con-leche's
`nestedRuleSyn` computes it once the domain's head is a constant (at
`resolves := (·.constsResolve env)`). -/
def synAt (env : Env) (lps : List ConLeche.Name) (dom : Expr) (lvls : List Level)
    (k rP cnP : Nat) : Option (List Level × List Expr) :=
  let args := dom.getAppArgs
  let pins := (args.take cnP).map (Expr.lowerBVars k 0)
  if args.length = cnP + k ∧
      args.take cnP == pins.map (Expr.liftLooseBVars k 0) ∧
      args.drop cnP == (List.range k).map (fun i => Expr.bvar (k - 1 - i)) ∧
      pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
        p.constsResolve env && p.allLevelParamsDefined lps) ∧
      lvls.all (Level.allParamsDefined lps) then
    some (lvls, pins)
  else none

/-- con-leche: none — `bvarRange`, in run form. -/
theorem bvarRange_pstep {n mI k : Nat} {s₀ s' : AState} {rs : List EIdx}
    (hok : StateOK s₀) (hrun : Arena.bvarRange mI n k s₀ = .ok (rs, s')) :
    PStep s₀ s' ∧ Frontend.denoteEList s'.store rs = some (ExprOps.bvarRangeSpec mI n k) := by
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.bvarRange_spec n s₀ mI k hok)
  exact ⟨PStep.of_caches h1 h2 h3 h5 h6, h7⟩

end RC

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1541-1557 nestedRuleSyn — **at the
major's domain**: the parameter prefix lowered past the `k` indices, the
shape tests in con-leche's `∧` order, then the guards. -/
theorem nestedRuleSynAt_spec {env : Env} (fe : IFEnv) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (dom : EIdx) (domP : Expr) (lvls : LsIdx)
    (lvlsP : List Level) (k rP cnP : Nat) :
    RdSpec env fe (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st dom = some domP ∧ denoteLs st.lss lvls = some lvlsP)
      (Arena.nestedRuleSynAt fe lps dom lvls k rP cnP)
      (ROp RSyn (RC.synAt env lpsP domP lvlsP k rP cnP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hl, hd, hlv⟩ := hpre
  simp only [Arena.nestedRuleSynAt] at hrun
  obtain ⟨args, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hargs⟩ := getAppArgs_run hok.state hd k1
  rw [hs1] at z1
  obtain ⟨pins, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨p2, hpins⟩ := lowerList_spec k (args.take cnP) (domP.getAppArgs.take cnP) s₀ s2 pins
    hok.state (denoteEList_take hargs cnP) k2
  have hlen : args.length = domP.getAppArgs.length := denoteEList_length hargs
  simp only [RC.synAt]
  by_cases c1 : (args.length != cnP + k) = true
  · rw [ite_eq_left c1] at z2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨p2, ?_⟩
    rw [ite_eq_right (by
      intro h
      have : args.length = cnP + k := hlen.trans h.1
      exact absurd c1 (by rw [bne, this]; simp))]; rfl
  · rw [ite_eq_right c1] at z2
    have e1 : domP.getAppArgs.length = cnP + k := by simpa [hlen] using c1
    obtain ⟨back, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨p3, hback⟩ := liftList_spec k pins _ s2 s3 back p2.ok hpins k3
    have p23 := p2.trans p3
    have hpre3 := denoteEList_ext p23.ext _ _ (denoteEList_take hargs cnP)
    have hb1 := beq_of_denoteEList p3.ok.wf hpre3 hback
    by_cases c2 : (args.take cnP != back) = true
    · rw [ite_eq_left c2] at z3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
      refine ⟨p23, ?_⟩
      rw [ite_eq_right (by
        intro h
        have : (args.take cnP == back) = true := by rw [hb1]; exact h.2.1
        exact absurd c2 (by rw [bne, this]; simp))]; rfl
    · rw [ite_eq_right c2] at z3
      have e2 : (domP.getAppArgs.take cnP ==
          ((domP.getAppArgs.take cnP).map (Expr.lowerBVars k 0)).map
            (Expr.liftLooseBVars k 0)) = true := by
        rw [← hb1]; simpa using c2
      obtain ⟨want, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨p4, hwant⟩ := RC.bvarRange_pstep p3.ok k4
      have p24 := p23.trans p4
      have hdrop := denoteEList_ext p24.ext _ _ (denoteEList_drop hargs cnP)
      have hb2 := beq_of_denoteEList p4.ok.wf hdrop hwant
      rw [ExprOps.bvarRangeSpec_eq_range] at hb2
      simp only [Nat.zero_add] at hb2
      by_cases c3 : (args.drop cnP != want) = true
      · rw [ite_eq_left c3] at z4
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        rw [ite_eq_right (by
          intro h
          have : (args.drop cnP == want) = true := by rw [hb2]; exact h.2.2.1
          exact absurd c3 (by rw [bne, this]; simp))]; rfl
      · rw [ite_eq_right c3] at z4
        have e3 : (domP.getAppArgs.drop cnP ==
            (List.range k).map (fun i => Expr.bvar (k - 1 - i))) = true := by
          rw [← hb2]; simpa using c3
        have p34 := p3.trans p4
        obtain ⟨p5, hr⟩ := nestedRuleSynGuards_spec fe lps lpsP lvls lvlsP rP pins _
          s4 s' r (hok.mono p24.ok p24.ext p24.pins)
          ⟨denoteNListE_ext p24.ext _ _ hl, denoteLs_ext hlv p24.ext,
            denoteEList_ext p34.ext _ _ hpins⟩ z4
        refine ⟨p24.trans p5, ?_⟩
        by_cases c4 : ((domP.getAppArgs.take cnP).map (Expr.lowerBVars k 0)).all
            (fun p => !p.hasFvar && p.looseBVarsBounded rP && p.constsResolve env &&
              p.allLevelParamsDefined lpsP) = true ∧
            lvlsP.all (Level.allParamsDefined lpsP) = true
        · rw [ite_eq_left c4] at hr
          rw [ite_eq_left ⟨e1, e2, e3, c4.1, c4.2⟩]
          exact hr
        · rw [ite_eq_right c4] at hr
          rw [ite_eq_right (fun h => c4 ⟨h.2.2.2.1, h.2.2.2.2⟩)]
          exact hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn — **the
syntactic reading of a nested rule's instantiation**, at `resolves :=
(·.constsResolve env)`: the prefix within the major's position, the major's
domain a constant-headed application, then `nestedRuleSynAt`. -/
theorem nestedRuleSyn_spec {env : Env} (fe : IFEnv) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (tyA : EIdx) (tyAP : Expr) (mI rP cnP : Nat) :
    RdSpec env fe (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st tyA = some tyAP)
      (Arena.nestedRuleSyn fe lps tyA mI rP cnP)
      (ROp RSyn (Expr.nestedRuleSyn (·.constsResolve env) lpsP tyAP mI rP cnP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hl, hd⟩ := hpre
  simp only [Arena.nestedRuleSyn] at hrun
  simp only [Expr.nestedRuleSyn]
  by_cases hle : rP ≤ mI
  · rw [ite_eq_left hle] at hrun
    rw [ite_eq_left hle]
    obtain ⟨q, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hq⟩ := stripPis_pstep hok.state hd k1
    rw [hs1] at z1
    cases q with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok.state, ?_⟩
      rw [stripPis_none hq]; rfl
    | some q =>
      obtain ⟨bs, e⟩ := q
      obtain ⟨xs, x, hsx, -, hx⟩ := denoteBP_some hq
      rw [hsx]
      dsimp only at z1
      by_cases htg : (e.tag == ETag.forallE) = true
      · rw [ite_eq_left htg] at z1
        obtain ⟨o, s2, k2, z2⟩ := AM.bind_ok z1
        obtain ⟨hs2, ho⟩ := viewBind_run k2
        rw [hs2] at z2
        cases o with
        | none => exact absurd z2 (fun hc => AM.fail_ok hc)
        | some t =>
          obtain ⟨dom, b, m⟩ := t
          have hw := view_of_viewBind_tag_forallE htg ho.symm
          obtain ⟨domP, bP, rfl, hdom, -⟩ := denote_forallE_inv hok.state.wf hw hx
          dsimp only at z2
          obtain ⟨hd', s3, k3, z3⟩ := AM.bind_ok z2
          obtain ⟨hs3, hhd⟩ := getAppFn_run hok.state hdom k3
          rw [hs3] at z3
          by_cases htc : (hd'.tag == ETag.const) = true
          · rw [ite_eq_left htc] at z3
            obtain ⟨o2, s4, k4, z4⟩ := AM.bind_ok z3
            obtain ⟨hs4, ho2⟩ := viewConst_run k4
            rw [hs4] at z4
            cases o2 with
            | none => exact absurd z4 (fun hc => AM.fail_ok hc)
            | some t2 =>
              obtain ⟨D, lvls⟩ := t2
              have hw2 := view_of_viewConst_tag htc ho2.symm
              obtain ⟨DP, lvlsP, hDP, -, hlvP⟩ := denote_const_inv hok.state.wf hw2 hhd
              dsimp only
              rw [hDP]
              dsimp only at z4
              exact nestedRuleSynAt_spec fe lps lpsP dom domP lvls lvlsP (mI - rP) rP cnP
                s₀ s' r hok ⟨hl, hdom, hlvP⟩ z4
          · rw [ite_eq_right htc] at z3
            obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
            refine ⟨PStep.refl hok.state, ?_⟩
            dsimp only
            cases hg : domP.getAppFn with
            | const D us =>
              rw [hg] at hhd
              exact absurd (tag_const_of_denote hok.state.wf hhd) (by simpa using htc)
            | _ => show _ = none; rfl
      · rw [ite_eq_right htg] at z1
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
        refine ⟨PStep.refl hok.state, ?_⟩
        cases x with
        | forallE dP bP m =>
          exact absurd (tag_forallE_of_denote hok.state.wf hx) (by simpa using htg)
        | _ => show _ = none; rfl
  · rw [ite_eq_right hle] at hrun
    rw [ite_eq_right hle]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok.state, rfl⟩

/-! ## The stored family

The rules are read at the CONSTRUCTORS' index (`fe.restrictTo vis₂` in
`consBlockRecsTF`), while the knot's caches serve whatever index the recursor
stage ended on.  So these statements carry two environments: `CheckOK μ envC
feC` for the caches (the frame is `CoreStep` there), and `IFEnvOK env fe` for
the lookups the rules make — which is `recRuleBits_run`'s shape
(`Bridge/Inductives/SumInstall.lean`). -/

namespace RC

/-- con-leche: none — every rule's firing mode replaced, denoted. -/
theorem denoteRules_map_fire {st : EStore} {f : IRecRuleFire} {fP : RecRuleFire}
    (hf : Frontend.denoteFire st f = some fP) :
    ∀ {rs : List IRecRule} {rsP : List RecRule}, Frontend.denoteRules st rs = some rsP →
      Frontend.denoteRules st (rs.map fun rl => { rl with fire := f }) =
        some (rsP.map fun rl => { rl with fire := fP }) := by
  intro rs
  induction rs with
  | nil =>
    intro rsP h
    simp only [Frontend.denoteRules, Option.some.injEq] at h
    subst h; rfl
  | cons r rs ih =>
    intro rsP h
    simp only [Frontend.denoteRules] at h
    cases h1 : Frontend.denoteRule st r with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : Frontend.denoteRules st rs with
    | none => rw [h1, h2] at h; simp at h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [Frontend.denoteRule] at h1
    cases hc : denoteN st.ns r.ctor with
    | none => rw [hc] at h1; simp at h1
    | some c =>
    cases hfr : Frontend.denoteFire st r.fire with
    | none => rw [hc, hfr] at h1; simp at h1
    | some fr =>
    cases he : denoteE st r.rhs with
    | none => rw [hc, hfr, he] at h1; simp at h1
    | some e =>
    rw [hc, hfr, he] at h1
    obtain rfl := (Option.some.inj h1).symm
    simp only [List.map_cons, Frontend.denoteRules, Frontend.denoteRule, hc, hf, he,
      ih h2]

/-- con-leche: none — `BlockShape.majorIdxAt`/`rulePrefixAt` agree on a
denoted shape. -/
theorem recAt_eq {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) (m : Nat) :
    p.majorIdxAt m = pP.majorIdxAt m ∧ p.rulePrefixAt m = pP.rulePrefixAt m := by
  have hrs := (dShape_inv h).2.1
  have hj := mapM_option_getElem? (st := st) hrs m
  simp only [Arena.BlockShape.majorIdxAt, Arena.BlockShape.rulePrefixAt,
    ConLeche.BlockShape.majorIdxAt, ConLeche.BlockShape.rulePrefixAt,
    List.getD_eq_getElem?_getD]
  cases hr : p.recs[m]? with
  | none =>
    rw [hr] at hj
    have : pP.recs[m]? = none := hj
    rw [this]; exact ⟨rfl, rfl⟩
  | some rc =>
    rw [hr] at hj
    obtain ⟨rcP, hrcP, hd⟩ := hj
    obtain ⟨-, h1, h2, -, -⟩ := dRec_inv hd
    rw [hrcP]
    exact ⟨h2, h1⟩

/-- con-leche: none — the recursors' targets and the member count agree on
a denoted shape: the container bit's second half. -/
theorem recs_any_tgt {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) :
    p.recs.any (fun rc => !(rc.tgt < p.k)) = pP.recs.any (fun rc => !(rc.tgt < pP.k)) := by
  obtain ⟨hms, hrs, -⟩ := dShape_inv h
  have hk : p.k = pP.k := by
    simp only [Arena.BlockShape.k, ConLeche.BlockShape.k, ConLeche.option_mapM_length hms]
  rw [hk]
  generalize pP.k = K
  clear hk hms h
  generalize p.recs = rs at hrs
  generalize pP.recs = rsP at hrs
  induction rs generalizing rsP with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs; subst hrs; rfl
  | cons r rs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hrs
    cases h1 : dRec st r with
    | none => rw [h1] at hrs; simp at hrs
    | some rP =>
    rw [h1] at hrs
    cases h2 : rs.mapM (dRec st) with
    | none => rw [h2] at hrs; simp at hrs
    | some rest =>
    rw [h2] at hrs
    simp only [Option.bind_some, Option.some.injEq] at hrs
    subst hrs
    simp only [List.any_cons, (dRec_inv h1).2.2.2.1, ih rest h2]

end RC

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:168-184 sumRules —
`sumRules_spec` (`Bridge/Inductives/SumInstall.lean`) with the LOOKUP index
apart from the knot's: the rules read `fe` (`IFEnvOK env fe`), the caches serve
`feC` (`CheckOK μ envC feC`), as `recRuleBits_run` states it.  **Belongs in
`SumInstall.lean` beside `sumRules_spec`** (which is this at `feC := fe`). -/
theorem sumRules_spec {μ : CheckMode} {envC env : Env} {feC : IFEnv} (fe : IFEnv)
    (recName : NIdx) (recNameP : ConLeche.Name) (nP mI rP : Nat)
    (recTy : EIdx) (recTyP : Expr) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
      (rhss : List EIdx) (rhssP : List Expr) (s₀ s' : AState) (r : List IRecRule),
      CheckOK μ envC feC s₀ → IFEnvOK env fe s₀ →
      denoteN s₀.store.ns recName = some recNameP → denoteE s₀.store recTy = some recTyP →
      denoteCtors s₀.store cs = some csP → Frontend.denoteEList s₀.store rhss = some rhssP →
      Arena.sumRules fe recName nP mI rP recTy cs rhss s₀ = .ok (r, s') →
      CoreStep μ envC feC s₀ s' ∧ Frontend.denoteRules s'.store r
        = some (ConLeche.sumRules env.find? recNameP nP mI rP recTyP csP rhssP) := by
  intro cs
  induction cs with
  | nil =>
    intro csP rhss rhssP s₀ s' r hok _ _ _ hcs _ hrun
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.sumRules] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨CoreStep.refl hok, ?_⟩
    cases rhssP <;> rfl
  | cons c cs ih =>
    intro csP rhss rhssP s₀ s' r hok hie hrn hrt hcs hrh hrun
    obtain ⟨cv, n⟩ := c
    simp only [denoteCtors] at hcs
    cases hcv : Frontend.denoteCV s₀.store cv with
    | none => rw [hcv] at hcs; simp at hcs
    | some cP =>
    cases hrest : denoteCtors s₀.store cs with
    | none => rw [hcv, hrest] at hcs; simp at hcs
    | some restP =>
    rw [hcv, hrest] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    cases rhss with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at hrh
      subst hrh
      simp only [Arena.sumRules] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, rfl⟩
    | cons rhs rhss =>
    simp only [Frontend.denoteEList] at hrh
    cases hrhs : denoteE s₀.store rhs with
    | none => rw [hrhs] at hrh; simp at hrh
    | some rhsP =>
    cases hrhss : Frontend.denoteEList s₀.store rhss with
    | none => rw [hrhs, hrhss] at hrh; simp at hrh
    | some rhssP' =>
    rw [hrhs, hrhss] at hrh
    obtain rfl := (Option.some.inj hrh).symm
    simp only [Arena.sumRules] at hrun
    obtain ⟨b, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
      (ExprOps.recRulePlain_spec Arena.coreWalkFuel s₀ recTy mI rP nP hok.state
        (by rw [hrt]; rfl))
    have p1 : PStep s₀ s1 := PStep.of_caches h1 h2 h3 h5 h6
    have hb : b = Expr.recRulePlain recTyP mI rP nP := h7 recTyP hrt
    have c1 := p1.toCore hok
    obtain ⟨rl, s2, k2, z2⟩ := AM.bind_ok z1
    have hrl : Frontend.denoteRule s1.store
        { ctor := cv.name, nfields := n, ctorParams := nP,
          fire := (if b then .plain else .inert), rhs := rhs, paramsBlind := true } =
        some { ctor := cP.name, nfields := n, ctorParams := nP,
               fire := (if Expr.recRulePlain recTyP mI rP nP then .plain else .inert),
               rhs := rhsP, paramsBlind := true } := by
      subst hb
      simp only [Frontend.denoteRule, denoteN_ext (denoteCV_name hcv) p1.ext,
        denote_ext hrhs p1.ext]
      cases Expr.recRulePlain recTyP mI rP nP <;> rfl
    obtain ⟨hfr, hrlr⟩ := recRuleBits_run c1.ok (hie.mono p1.ext)
      (denoteN_ext hrn p1.ext) hrl k2
    have c2 : CoreStep μ envC feC s₀ s2 :=
      c1.trans ⟨Core.CheckOK.ofReadbackFrame c1.ok hfr, hfr.ext, hfr.pins⟩
    obtain ⟨rs, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨c3, hrs⟩ := ih restP rhss rhssP' s2 s3 rs c2.ok (hie.mono c2.ext)
      (denoteN_ext hrn c2.ext) (denote_ext hrt c2.ext) (denoteCtors_ext c2.ext _ _ hrest)
      (denoteEList_ext c2.ext _ _ hrhss) k3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
    refine ⟨c2.trans c3, ?_⟩
    simp only [Frontend.denoteRules, denoteRule_ext hrlr c3.ext, hrs]
    rfl

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:574-585 auxRuleFireR
**The firing mode of a rule at an OUTSIDE major**: `.nested` at the
syntactic reading, `.inert` when it fails, at `resolves :=
(·.constsResolve env)` for the index `fe` denotes. -/
theorem auxRuleFireR_spec {env : Env} (fe : IFEnv) (cv : IConstantVal) (cvP : ConstantVal)
    (mI rP nPc : Nat) :
    RdSpec env fe (fun st => Frontend.denoteCV st cv = some cvP)
      (Arena.auxRuleFireR fe cv mI rP nPc)
      (fun st r => Frontend.denoteFire st r =
        some (ConLeche.auxRuleFireR (·.constsResolve env) cvP mI rP nPc)) := by
  intro s₀ s' r hok hcv hrun
  simp only [Arena.auxRuleFireR] at hrun
  obtain ⟨o, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, ho⟩ := nestedRuleSyn_spec fe cv.levelParams cvP.levelParams cv.type cvP.type
    mI rP nPc s₀ s1 o hok ⟨denoteCV_lps hcv, denoteCV_type hcv⟩ k1
  simp only [ConLeche.auxRuleFireR]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    have : Expr.nestedRuleSyn (·.constsResolve env) cvP.levelParams cvP.type mI rP nPc
      = none := ho
    rw [this]
    exact ⟨p1, rfl⟩
  | some q =>
    obtain ⟨lvls, pins⟩ := q
    obtain ⟨⟨lvlsP, pinsP⟩, hq, hl, hp⟩ := ho
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    rw [hq]
    refine ⟨p1, ?_⟩
    simp only [Frontend.denoteFire, hl, hp]

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:587-597 tgtStoredRules
**One checked recursor's stored rules, at its major**: `sumRules` at the
major's parameter count and constructors, every rule firing as
`auxRuleFireR` reads it at an OUTSIDE major.  The pure side at `find? :=
env.find?` and `resolves := (·.constsResolve env)` for the lookup index's
environment `env`; the caches at `feC`. -/
theorem tgtStoredRules_spec {μ : CheckMode} {envC env : Env} {feC : IFEnv} (fe : IFEnv)
    (cv : IConstantVal) (cvP : ConstantVal) (mI rP : Nat) (M : Arena.TargetMajor)
    (MP : ConLeche.TargetMajor) (rhss : List EIdx) (rhssP : List Expr)
    (s₀ s' : AState) (r : List IRecRule) (hok : CheckOK μ envC feC s₀)
    (hie : IFEnvOK env fe s₀) (hcv : Frontend.denoteCV s₀.store cv = some cvP)
    (hM : dMajor s₀.store M = some MP) (hrh : Frontend.denoteEList s₀.store rhss = some rhssP)
    (hrun : Arena.tgtStoredRules fe cv mI rP M rhss s₀ = .ok (r, s')) :
    CoreStep μ envC feC s₀ s' ∧ Frontend.denoteRules s'.store r =
      some (ConLeche.tgtStoredRules env.find? (·.constsResolve env) cvP mI rP MP rhssP) := by
  obtain ⟨-, -, -, hnpc, -, hctors, hmem, -, -⟩ := dMajor_inv hM
  simp only [Arena.tgtStoredRules] at hrun
  obtain ⟨rules, s1, k1, z1⟩ := AM.bind_ok hrun
  rw [dCtors_eq_denoteCtors] at hctors
  obtain ⟨c1, hrules⟩ := sumRules_spec fe cv.name cvP.name M.nPc mI rP cv.type cvP.type
    M.ctors MP.ctors rhss rhssP s₀ s1 rules hok hie (denoteCV_name hcv) (denoteCV_type hcv)
    hctors hrh k1
  simp only [ConLeche.tgtStoredRules, ← hnpc, ← hmem]
  cases hm : M.member with
  | some t =>
    rw [hm] at z1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    exact ⟨c1, hrules⟩
  | none =>
    rw [hm] at z1
    dsimp only at z1
    obtain ⟨f, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hf⟩ := auxRuleFireR_spec fe cv cvP mI rP M.nPc s1 s2 f
      ⟨c1.ok.state, c1.ok.pins, hie.mono c1.ext⟩ (denoteCV_ext hcv c1.ext) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    exact ⟨c1.trans (p2.toCore c1.ok),
      RC.denoteRules_map_fire hf (denoteRules_ext p2.ext _ _ hrules)⟩

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:599-605 blockNestedBit
**The block's container bit**: some field kind not flat, or some recursor's
major not a member — the twin's `if` is con-leche's `||`, the kinds read
through `kindOf`. -/
theorem blockNestedBit_eq {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) (kinds : List (List (List Arena.NestFieldKind))) :
    Arena.blockNestedBit p kinds =
      ConLeche.blockNestedBit pP (kinds.map (·.map (·.map kindOf))) := by
  have hflat : Arena.nestKindsFlat kinds =
      ConLeche.nestKindsFlat (kinds.map (·.map (·.map kindOf))) := by
    simp only [Arena.nestKindsFlat, ConLeche.nestKindsFlat, List.all_map, Function.comp_def,
      kindOf_flat]
  simp only [Arena.blockNestedBit, ConLeche.blockNestedBit, hflat, RC.recs_any_tgt h]
  cases ConLeche.nestKindsFlat (kinds.map (·.map (·.map kindOf))) <;> simp

/-! ## The family consed at its majors (`consBlockRecsTF`) -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:607-617 consBlockRecsTF
(its list) — a checked recursor with its class and right-hand sides,
denoted. -/
def dRecOut (st : EStore) (t : IConstantVal × Arena.TargetMajor × List EIdx) :
    Option (ConstantVal × ConLeche.TargetMajor × List Expr) := do
  let cv ← Frontend.denoteCV st t.1
  let M ← dMajor st t.2.1
  let rh ← Frontend.denoteEList st t.2.2
  pure (cv, M, rh)

theorem dRecOut_ext : DExt dRecOut := by
  intro st st' hx t y h
  simp only [dRecOut] at h ⊢
  cases h1 : Frontend.denoteCV st t.1 with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : dMajor st t.2.1 with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : Frontend.denoteEList st t.2.2 with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some c =>
  rw [h1, h2, h3] at h
  rw [denoteCV_ext h1 hx, dMajor_ext hx _ _ h2, denoteEList_ext hx _ _ h3]
  exact h

namespace RC

/-- con-leche: none — `dRecOut`, taken apart. -/
theorem dRecOut_inv {st : EStore} {t : IConstantVal × Arena.TargetMajor × List EIdx}
    {tP : ConstantVal × ConLeche.TargetMajor × List Expr} (h : dRecOut st t = some tP) :
    Frontend.denoteCV st t.1 = some tP.1 ∧ dMajor st t.2.1 = some tP.2.1 ∧
      Frontend.denoteEList st t.2.2 = some tP.2.2 := by
  simp only [dRecOut] at h
  cases h1 : Frontend.denoteCV st t.1 with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : dMajor st t.2.1 with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : Frontend.denoteEList st t.2.2 with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some c =>
  rw [h1, h2, h3] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:74-86 FEnv.restrictTo / FEnv.push —
**a push above the bound leaves the restricted view alone** when the pushed
name was not visible there: the new row's counter is at or past the bound,
and it shadows nothing the bound let through. -/
theorem restrictTo_push_find? {fe : IFEnv} {k : Nat} (hk : k ≤ fe.visibleBelow)
    {ci : IConstantInfo} (hnone : (fe.restrictTo k).find? ci.name = none) :
    ((fe.push ci).restrictTo k).find? = (fe.restrictTo k).find? := by
  funext n
  simp only [IFEnv.find?, IFEnv.restrictTo, IFEnv.push, Std.HashMap.getElem?_insert]
  by_cases hEq : (ci.name == n) = true
  · rw [ite_eq_left hEq]
    have hn : ci.name = n := eq_of_beq hEq
    subst hn
    simp only [IFEnv.find?, IFEnv.restrictTo] at hnone
    have : ¬ fe.visibleBelow < k := by omega
    simp only [this, ↓reduceIte]
    exact hnone.symm
  · rw [ite_eq_right hEq]

/-- con-leche: none — `IFEnvOK` reads the index only through `find?`. -/
theorem IFEnvOK.of_find? {env : Env} {fe fe' : IFEnv} {s : AState} (h : IFEnvOK env fe s)
    (e : fe'.find? = fe.find?) : IFEnvOK env fe' s :=
  ⟨fun n ci hf => h.hit n ci (by rw [← e]; exact hf),
   fun nm c hc => by
     obtain ⟨n, ci, h1, h2, h3⟩ := h.cover nm c hc
     exact ⟨n, ci, h1, by rw [e]; exact h2, h3⟩,
   fun n t hf => h.proj n t (by rw [← e]; exact hf)⟩

end RC

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:607-617 consBlockRecsTF
con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:93-106 consBlockRecsT
**The checked family consed through the index, at its majors**: each
recursor with its rules at ITS major, read at the constructors' view
`fe.restrictTo vis₂` — con-leche's `consBlockRecsT env₂.find?
(·.constsResolve env₂)`, where `env₂` is what that view denotes.  The answer
is an install (`InstRel`: coherent, only pushed, the bound only rose,
denoting con-leche's cons, no projection table).

**The freshness hypothesis** (`env₂.find? t.1.name = none` at every
recursor) is what keeps the view fixed while the recursors are pushed above
it (`RC.restrictTo_push_find?`): a pushed name that shadowed a constructor-
environment constant would hide it from the later rules' lookups, where
con-leche's `find?` is the fixed `env₂.find?`. -/
theorem consBlockRecsTF_spec {μ : CheckMode} {envC env₂ : Env} {feC : IFEnv} (vis₂ : Nat)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) :
    ∀ (out : List (IConstantVal × Arena.TargetMajor × List EIdx))
      (outP : List (ConstantVal × ConLeche.TargetMajor × List Expr))
      (m : Nat) (fe : IFEnv) (env : Env) (s₀ s' : AState) (fe' : IFEnv),
      CheckOK μ envC feC s₀ → IFEnvOK env₂ (fe.restrictTo vis₂) s₀ →
      vis₂ ≤ fe.visibleBelow → IFEnvCoh fe → denoteFEnv s₀.store fe = some env →
      dShape s₀.store p = some pP → out.mapM (dRecOut s₀.store) = some outP →
      (∀ t ∈ outP, env₂.find? t.1.name = none) →
      Arena.consBlockRecsTF vis₂ p m out fe s₀ = .ok (fe', s') →
      CoreStep μ envC feC s₀ s' ∧
        InstRel fe (fun e => e = consBlockRecsT env₂.find? (·.constsResolve env₂) pP m outP env)
          s'.store fe' := by
  intro out
  induction out with
  | nil =>
    intro outP m fe env s₀ s' fe' hok _ _ hcoh hfe _ hout _ hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hout
    subst hout
    simp only [Arena.consBlockRecsTF] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, rfl⟩,
      ProjOut.refl _ _⟩
  | cons t rest ih =>
    intro outP m fe env s₀ s' fe' hok hie hvis hcoh hfe hsh hout hfresh hrun
    obtain ⟨cv, M, rhss⟩ := t
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hout
    cases ht : dRecOut s₀.store (cv, M, rhss) with
    | none => rw [ht] at hout; simp at hout
    | some tP =>
    rw [ht] at hout
    cases hr : rest.mapM (dRecOut s₀.store) with
    | none => rw [hr] at hout; simp at hout
    | some restP =>
    rw [hr] at hout
    simp only [Option.bind_some, Option.some.injEq] at hout
    subst hout
    obtain ⟨cvP, MP, rhssP⟩ := tP
    obtain ⟨hcv, hM, hrh⟩ := RC.dRecOut_inv ht
    obtain ⟨hmI, hrP⟩ := RC.recAt_eq hsh m
    simp only [Arena.consBlockRecsTF] at hrun
    obtain ⟨rules, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, hrules⟩ := tgtStoredRules_spec (fe.restrictTo vis₂) cv cvP
      (p.majorIdxAt m) (p.rulePrefixAt m) M MP rhss rhssP s₀ s1 rules hok hie hcv hM hrh k1
    rw [hmI, hrP] at hrules
    -- the pushed recursor
    have hci : Frontend.denoteCI s1.store (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) rules)
        = some (.recInfo cvP (pP.majorIdxAt m) (pP.rulePrefixAt m)
          (ConLeche.tgtStoredRules env₂.find? (·.constsResolve env₂) cvP (pP.majorIdxAt m)
            (pP.rulePrefixAt m) MP rhssP)) := by
      simp only [Frontend.denoteCI, denoteCV_ext hcv c1.ext, hrules, hmI, hrP]
    have hfe1 := denoteFEnv_push (denoteFEnv_mono c1.ext hfe) hci
    -- the view stays
    have hnone : (fe.restrictTo vis₂).find?
        (IConstantInfo.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) rules).name = none := by
      cases hf : (fe.restrictTo vis₂).find? cv.name with
      | none => exact hf
      | some ci =>
        obtain ⟨c, -, hc⟩ := find_some_rel hie (denoteCV_name hcv) hf
        rw [hfresh (cvP, MP, rhssP) (by simp)] at hc
        exact nomatch hc
    have hview := RC.restrictTo_push_find? hvis hnone
    have hie1 : IFEnvOK env₂ ((fe.push (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
        rules)).restrictTo vis₂) s1 := RC.IFEnvOK.of_find? (hie.mono c1.ext) hview
    obtain ⟨c2, hrel⟩ := ih restP (m + 1) _ _ s1 s' fe' c1.ok hie1
      (by simp only [IFEnv.push]; omega) (hcoh.push _) hfe1 (dShape_ext c1.ext _ _ hsh)
      (dRecOut_ext.list c1.ext _ _ hr) (fun t ht => hfresh t (by simp [ht])) z1
    refine ⟨c1.trans c2, ?_⟩
    have h1 : InstRel fe (fun e => e = ⟨.recInfo cvP (pP.majorIdxAt m) (pP.rulePrefixAt m)
          (ConLeche.tgtStoredRules env₂.find? (·.constsResolve env₂) cvP (pP.majorIdxAt m)
            (pP.rulePrefixAt m) MP rhssP) :: env.consts⟩) s1.store
        (fe.push (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) rules)) :=
      ⟨hcoh.push _, Pushed.push _ _, by simp only [IFEnv.push]; omega, ⟨_, hfe1, rfl⟩,
        ProjOut.push hcoh _ (by intro t h; cases h)⟩
    exact InstRel.trans c2.ext h1 hrel

/-! ## Node agreement (K.53′) -/

namespace RC

/-- con-leche: none — `denoteEList_inj` at a binder telescope: two telescopes
denoting the same one ARE the same handles. -/
theorem denoteBinders_inj {st : EStore} (hwf : StoreWF st) :
    ∀ {as bs : List (EIdx × BinderMeta)} {xs : List (Expr × BinderMeta)},
      denoteBinders st as = some xs → denoteBinders st bs = some xs → as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs xs ha hb
    simp only [denoteBinders, Option.some.injEq] at ha
    subst ha
    cases bs with
    | nil => rfl
    | cons b bs =>
      obtain ⟨t, m⟩ := b
      simp only [denoteBinders] at hb
      split at hb <;> simp at hb
  | cons a as ih =>
    intro bs xs ha hb
    obtain ⟨t, m⟩ := a
    simp only [denoteBinders] at ha
    cases hx : denoteE st t with
    | none => rw [hx] at ha; simp at ha
    | some y =>
    cases hxs : denoteBinders st as with
    | none => rw [hx, hxs] at ha; simp at ha
    | some ys =>
    rw [hx, hxs] at ha
    obtain rfl := Option.some.inj ha
    cases bs with
    | nil => simp only [denoteBinders] at hb; simp at hb
    | cons b bs =>
      obtain ⟨t', m'⟩ := b
      simp only [denoteBinders] at hb
      cases hy : denoteE st t' with
      | none => rw [hy] at hb; simp at hb
      | some z =>
      cases hys : denoteBinders st bs with
      | none => rw [hy, hys] at hb; simp at hb
      | some zs =>
      rw [hy, hys] at hb
      obtain ⟨h1, rfl⟩ := List.cons.inj (Option.some.inj hb)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      rw [denoteE_inj hwf hx hy, ih hxs hys]

/-- con-leche: none — a binder-telescope comparison over handles is the
structural one. -/
theorem beq_binders_eq {st : EStore} (hwf : StoreWF st)
    {as bs : List (EIdx × BinderMeta)} {xs ys : List (Expr × BinderMeta)}
    (ha : denoteBinders st as = some xs) (hb : denoteBinders st bs = some ys) :
    (as == bs) = (xs == ys) := by
  cases h1 : as == bs with
  | true =>
    obtain rfl := eq_of_beq h1
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (as == bs) = true := beq_iff_eq.mpr (denoteBinders_inj hwf ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:541 targetK53 (the
erased telescopes) — every binder's domain with its free variables'
annotations erased, the metadata kept. -/
theorem eraseBinders_spec : ∀ (bs : List (EIdx × BinderMeta)) (bsP : List (Expr × BinderMeta)),
    PSpecP (fun st => denoteBinders st bs = some bsP)
      (bs.mapM fun b => do pure ((← Arena.eraseFVarTys b.1), b.2))
      (RB (bsP.map fun b => (b.1.eraseFVarTys, b.2))) := by
  intro bs
  induction bs with
  | nil =>
    intro bsP s₀ s' r hok _ h hrun
    simp only [denoteBinders, Option.some.injEq] at h
    subst h
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons b bs ih =>
    intro bsP s₀ s' r hok hp h hrun
    obtain ⟨t, m⟩ := b
    simp only [denoteBinders] at h
    cases ht : denoteE s₀.store t with
    | none => rw [ht] at h; simp at h
    | some tP =>
    cases hbs : denoteBinders s₀.store bs with
    | none => rw [ht, hbs] at h; simp at h
    | some rest =>
    rw [ht, hbs] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.mapM_cons] at hrun
    obtain ⟨x, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨e, s1', k1', z1'⟩ := AM.bind_ok k1
    obtain ⟨p1, he⟩ := eraseFVarTys_spec t tP s₀ s1' e hok hp ht k1'
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1'
    obtain ⟨xs, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hxs⟩ := ih rest s1 s2 xs p1.ok (PinsOK.ofPStep hp p1)
      (denoteBinders_ext p1.ext _ _ hbs) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨p1.trans p2, ?_⟩
    show denoteBinders _ ((e, m) :: xs) = _
    have hxs' : denoteBinders _ xs = some (rest.map fun b => (b.1.eraseFVarTys, b.2)) := hxs
    simp only [denoteBinders, List.map_cons, denote_ext he p2.ext, hxs']

end RC

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
**K.53′ at one recorded field**: its telescope is the call's up to the free
variables' annotations, its leaf's head and arity the major's, its indices up
to annotations, its class naming a member, and that class matching the
callee's class per component.  The scoping hypotheses are the cached bridge's
(`targetK53S_sim`): the formers closed and the callee's class scoped
(`TargetMajScoped`). -/
theorem targetK53_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (formerTys : List EIdx)
    (formerTysP : List Expr) (Mc : Arena.TargetMajor) (McP : ConLeche.TargetMajor)
    (tele : List (EIdx × BinderMeta)) (teleP : List (Expr × BinderMeta))
    (majDom f : EIdx) (majDomP fP : Expr)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t) (hMc : Cached.TargetMajScoped McP) :
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        dMajor st Mc = some McP ∧ denoteBinders st tele = some teleP ∧
        denoteE st majDom = some majDomP ∧ denoteE st f = some fP)
      (Arena.targetK53 μ fe p formerTys Mc tele majDom f) (fun _ r v => r = v)
      (ConLeche.targetK53 (fueledOpsM μ) env pP formerTysP McP teleP majDomP fP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hsh, hft, hMc', htele, hmd, hf⟩ := hpre
  obtain ⟨-, hMlv, hMds, hMnpc, -, -, -, -, hMpf⟩ := dMajor_inv hMc'
  have hlen : tele.length = teleP.length := denoteBinders_length htele
  simp only [Arena.targetK53] at hrun
  simp only [ConLeche.targetK53]
  obtain ⟨q, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hq⟩ := stripPis_pstep hok.state hf k1
  rw [hs1] at z1
  rw [← hlen]
  cases q with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    rw [stripPis_none hq]
    exact ⟨CoreStep.refl hok, false, rfl, FOk.pure false⟩
  | some q =>
  obtain ⟨teleW, leafW⟩ := q
  obtain ⟨twP, lwP, hsx, htw, hlw⟩ := denoteBP_some hq
  rw [hsx]
  dsimp only at z1 ⊢
  obtain ⟨ew, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨c2, hew⟩ := RC.pspecP_core (RC.eraseBinders_spec teleW twP) hok htw k2
  obtain ⟨et, s3, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨c3, het⟩ := RC.pspecP_core (RC.eraseBinders_spec tele teleP) c2.ok
    (denoteBinders_ext c2.ext _ _ htele) k3
  have c13 := c2.trans c3
  have hb1 := RC.beq_binders_eq c3.ok.state.wf (denoteBinders_ext c3.ext _ _ hew) het
  by_cases cb : (ew != et) = true
  · rw [ite_eq_left cb] at z3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
    rw [ite_eq_left (by rw [bne, ← hb1]; exact cb)]
    exact ⟨c13, false, rfl, FOk.pure false⟩
  · rw [ite_eq_right cb] at z3
    rw [ite_eq_right (by rw [bne, ← hb1]; exact cb)]
    have hlw3 := denote_ext hlw c13.ext
    have hmd3 := denote_ext hmd c13.ext
    obtain ⟨lh, s4, k4, z4⟩ := AM.bind_ok z3
    obtain ⟨hs4, hlh⟩ := getAppFn_run c3.ok.state hlw3 k4
    rw [hs4] at z4
    obtain ⟨mh, s5, k5, z5⟩ := AM.bind_ok z4
    obtain ⟨hs5, hmh⟩ := getAppFn_run c3.ok.state hmd3 k5
    rw [hs5] at z5
    by_cases ct : (lh.tag == ETag.const && mh.tag == ETag.const) = true
    · rw [ite_eq_left ct] at z5
      simp only [Bool.and_eq_true] at ct
      obtain ⟨ct1, ct2⟩ := ct
      obtain ⟨o1, s6, k6, z6⟩ := AM.bind_ok z5
      obtain ⟨hs6, ho1⟩ := viewConst_run k6
      rw [hs6] at z6
      cases o1 with
      | none => exact absurd z6 (fun hc => AM.fail_ok hc)
      | some t1 =>
      obtain ⟨I', us'⟩ := t1
      obtain ⟨I'P, us'P, hlhP, hI', hus'⟩ := denote_const_inv c3.ok.state.wf
        (view_of_viewConst_tag ct1 ho1.symm) hlh
      dsimp only at z6
      obtain ⟨o2, s7, k7, z7⟩ := AM.bind_ok z6
      obtain ⟨hs7, ho2⟩ := viewConst_run k7
      rw [hs7] at z7
      cases o2 with
      | none => exact absurd z7 (fun hc => AM.fail_ok hc)
      | some t2 =>
      obtain ⟨I, us⟩ := t2
      obtain ⟨IP, usP, hmhP, hI, -⟩ := denote_const_inv c3.ok.state.wf
        (view_of_viewConst_tag ct2 ho2.symm) hmh
      rw [hlhP, hmhP]
      dsimp only at z7 ⊢
      obtain ⟨la, s8, k8, z8⟩ := AM.bind_ok z7
      obtain ⟨hs8, hla⟩ := getAppArgs_run c3.ok.state hlw3 k8
      rw [hs8] at z8
      obtain ⟨ma, s9, k9, z9⟩ := AM.bind_ok z8
      obtain ⟨hs9, hma⟩ := getAppArgs_run c3.ok.state hmd3 k9
      rw [hs9] at z9
      have hII := beq_handle_eq c3.ok.state.wf hI' hI
      have hll : la.length = lwP.getAppArgs.length := denoteEList_length hla
      have hml : ma.length = majDomP.getAppArgs.length := denoteEList_length hma
      have hcA : (I' == I && la.length == ma.length) =
          (I'P == IP && lwP.getAppArgs.length == majDomP.getAppArgs.length) := by
        rw [hII, hll, hml]
      by_cases cA : (!(I' == I && la.length == ma.length)) = true
      · rw [ite_eq_left cA] at z9
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z9
        refine ⟨c13, false, rfl, ?_⟩
        have cA0 : (I'P == IP && lwP.getAppArgs.length == majDomP.getAppArgs.length) = false := by
          rw [← hcA]
          cases hb : (I' == I && la.length == ma.length) with
          | false => rfl
          | true => rw [hb] at cA; exact absurd cA (by decide)
        rw [ite_eq_right (by rw [cA0]; simp)]
        exact FOk.pure false
      · rw [ite_eq_right cA] at z9
        have cA' : (I'P == IP && lwP.getAppArgs.length == majDomP.getAppArgs.length) = true := by
          rw [← hcA]
          cases hb : (I' == I && la.length == ma.length) with
          | true => rfl
          | false => rw [hb] at cA; exact absurd (by decide) cA
        obtain ⟨le, s10, k10, z10⟩ := AM.bind_ok z9
        obtain ⟨c10, hle⟩ := RC.pspecP_core (mapM_RE_P (fun _ => True) (fun _ h => h)
          (fun e eP => fun s₀ s' r hok hp hpre hrun =>
            eraseFVarTys_spec e eP s₀ s' r hok hp hpre.2 hrun) _ _) c3.ok
          ⟨trivial, denoteEList_drop hla McP.nPc⟩ (by rw [hMnpc] at k10; exact k10)
        obtain ⟨me, s11, k11, z11⟩ := AM.bind_ok z10
        obtain ⟨c11, hme⟩ := RC.pspecP_core (mapM_RE_P (fun _ => True) (fun _ h => h)
          (fun e eP => fun s₀ s' r hok hp hpre hrun =>
            eraseFVarTys_spec e eP s₀ s' r hok hp hpre.2 hrun) _ _) c10.ok
          ⟨trivial, denoteEList_ext c10.ext _ _ (denoteEList_drop hma McP.nPc)⟩
          (by rw [hMnpc] at k11; exact k11)
        have c311 := c10.trans c11
        have hb2 := beq_of_denoteEList c11.ok.state.wf (denoteEList_ext c11.ext _ _ hle) hme
        by_cases cB : (le != me) = true
        · rw [ite_eq_left cB] at z11
          obtain ⟨rfl, rfl⟩ := AM.pure_ok z11
          refine ⟨c13.trans c311, false, rfl, ?_⟩
          have cB0 : ((lwP.getAppArgs.drop McP.nPc).map Expr.eraseFVarTys ==
              (majDomP.getAppArgs.drop McP.nPc).map Expr.eraseFVarTys) = false := by
            rw [← hb2]; simpa using cB
          rw [ite_eq_right (by rw [cA', cB0]; simp)]
          exact FOk.pure false
        · rw [ite_eq_right cB] at z11
          have cB' : ((lwP.getAppArgs.drop McP.nPc).map Expr.eraseFVarTys ==
              (majDomP.getAppArgs.drop McP.nPc).map Expr.eraseFVarTys) = true := by
            rw [← hb2]; simpa using cB
          have c111 := c13.trans c311
          obtain ⟨hd, s12, k12, z12⟩ := AM.bind_ok z11
          obtain ⟨p12, hhd⟩ := internConstE_run c11.ok.state
            (denoteN_ext hI' c311.ext) (denoteLs_ext hus' c311.ext) k12
          have c12 := c111.trans (p12.toCore c111.ok)
          obtain ⟨app, s13, k13, z13⟩ := AM.bind_ok z12
          have hlp := denoteEList_ext (c311.ext.trans p12.ext) _ _ (denoteEList_take hla Mc.nPc)
          obtain ⟨p13, happ⟩ := mkAppN_run _ _ c12.ok.state hhd hlp k13
          have c13' := c12.trans (p13.toCore c12.ok)
          obtain ⟨b, s14, k14, z14⟩ := AM.bind_ok z13
          obtain ⟨p14, rfl⟩ := nestOcc_spec p.memberNames pP.memberNames 0 0 app _ s13 s14 b
            c13'.ok.state ⟨denoteNListE_ext c13'.ext _ _ (BlockShape.memberNames_spec hsh), happ⟩ k14
          have c14 := c13'.trans (p14.toCore c13'.ok)
          rw [hMnpc] at z14
          by_cases cC : (Expr.mkAppN (.const I'P us'P) (lwP.getAppArgs.take McP.nPc)).nestOcc
              pP.memberNames 0 0 = true
          · rw [ite_eq_left cC] at z14
            rw [ite_eq_left (by rw [cA', cB', cC]; rfl)]
            obtain ⟨c15, v, rfl, hv⟩ := targetClassMatch_spec fe hk henv p pP formerTys Mc.pfvs
              formerTysP McP.pfvs Mc.lvls us' McP.lvls us'P Mc.ds (la.take McP.nPc) McP.ds
              (lwP.getAppArgs.take McP.nPc) hformer hMc.1 s14 s' r c14.ok
              ⟨dShape_ext c14.ext _ _ hsh, denoteEList_ext c14.ext _ _ hft,
                denoteEList_ext c14.ext _ _ hMpf, denoteLs_ext hMlv c14.ext,
                denoteEList_ext c14.ext _ _ hMds,
                denoteLs_ext hus' (c311.ext.trans (p12.ext.trans (p13.ext.trans p14.ext))),
                denoteEList_ext (c311.ext.trans
                  (p12.ext.trans (p13.ext.trans p14.ext))) _ _ (denoteEList_take hla McP.nPc)⟩
              z14
            exact ⟨c14.trans c15, r, rfl, hv⟩
          · rw [ite_eq_right cC] at z14
            obtain ⟨rfl, rfl⟩ := AM.pure_ok z14
            have cC0 : (Expr.mkAppN (.const I'P us'P) (lwP.getAppArgs.take McP.nPc)).nestOcc
                pP.memberNames 0 0 = false := by simpa using cC
            rw [ite_eq_right (by rw [cA', cB', cC0]; simp)]
            exact ⟨c14, false, rfl, FOk.pure false⟩
    · rw [ite_eq_right ct] at z5
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z5
      refine ⟨c13, false, rfl, ?_⟩
      simp only [Bool.and_eq_true, not_and] at ct
      cases hg1 : lwP.getAppFn with
      | const I' us' =>
        cases hg2 : majDomP.getAppFn with
        | const I us =>
          rw [hg1] at hlh; rw [hg2] at hmh
          exact absurd (ct (by simpa using tag_const_of_denote c3.ok.state.wf hlh))
            (by simpa using tag_const_of_denote c3.ok.state.wf hmh)
        | _ => exact FOk.pure false
      | _ => exact FOk.pure false

/-! ## The recursor records' pins -/

namespace RC

/-- con-leche: none — a failing primitive, then anything, cannot have
accepted. -/
theorem failBindOk {α β : Type} {e : Arena.CheckError} {k : α → AM β} {s s' : AState} {r : β}
    (h : ((Arena.fail e : AM α) >>= k) s = .ok (r, s')) : False := by
  obtain ⟨a, s1, h1, -⟩ := AM.bind_ok h
  exact AM.fail_ok h1

/-- con-leche: none — `Name.nodup` is a sufficient test for `Nodup`. -/
theorem nodup_of : ∀ {xs : List ConLeche.Name}, ConLeche.Name.nodup xs = true →
    decide xs.Nodup = true := by
  intro xs
  induction xs with
  | nil => intro _; decide
  | cons x xs ih =>
    intro h
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    have := of_decide_eq_true (ih h2)
    simp only [decide_eq_true_eq, List.nodup_cons]
    refine ⟨fun hm => ?_, this⟩
    rw [List.contains_iff_mem.mpr hm] at h1
    exact absurd h1 (by decide)

/-- con-leche: none — a denoted recursor list, filtered on the targets. -/
theorem filter_recs {st : EStore} (q : Nat → Bool) :
    ∀ {rs : List Arena.RecShape} {rsP : List ConLeche.RecShape},
      rs.mapM (dRec st) = some rsP →
      (rs.filter (fun rc => q rc.tgt)).mapM (dRec st) = some (rsP.filter (fun rc => q rc.tgt)) := by
  intro rs
  induction rs with
  | nil =>
    intro rsP h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons r rs ih =>
    intro rsP h
    obtain ⟨rP, rsP', rfl, hr, hrs⟩ := mapM_option_cons_inv h
    have ht := (dRec_inv hr).2.2.2.1
    simp only [List.filter_cons, ht]
    cases q rP.tgt with
    | true => exact mapM_option_cons hr (ih hrs)
    | false => exact ih hrs

/-- con-leche: none — a denoted three-tuple constructor list's names. -/
theorem ctors3_names {st : EStore} :
    ∀ {cs : List (IConstantVal × Nat × Nat)} {csP : List (ConstantVal × Nat × Nat)},
      denoteCtors3 st cs = some csP →
      Frontend.denoteNList st.ns (cs.map (·.1.name)) = some (csP.map (·.1.name)) := by
  intro cs
  induction cs with
  | nil => intro csP h; simp only [denoteCtors3, Option.some.injEq] at h; subst h; rfl
  | cons c cs ih =>
    intro csP h
    obtain ⟨cv, a, b⟩ := c
    simp only [denoteCtors3] at h
    cases hcv : Frontend.denoteCV st cv with
    | none => rw [hcv] at h; simp at h
    | some cP =>
    cases hcs : denoteCtors3 st cs with
    | none => rw [hcv, hcs] at h; simp at h
    | some rest =>
    rw [hcv, hcs] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hcv, ih hcs]

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:504 targetRecPins
(`wantAux`) — the generated auxiliary names `n₀.rec_i`, interned. -/
theorem recAuxNames_run (n₀ : NIdx) (n0P : ConLeche.Name) :
    ∀ (is : List Nat) (s₀ s' : AState) (r : List NIdx), StateOK s₀ →
      denoteN s₀.store.ns n₀ = some n0P →
      is.mapM (fun i => internNNode (.str n₀ (toString "rec_" ++ toString (i + 1)))) s₀
        = .ok (r, s') →
      PStep s₀ s' ∧ Frontend.denoteNList s'.store.ns r =
        some (is.map fun i => n0P.str (toString "rec_" ++ toString (i + 1))) := by
  intro is
  induction is with
  | nil =>
    intro s₀ s' r hok _ hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons i is ih =>
    intro s₀ s' r hok hn hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨x, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hx⟩ := internStrN_run hok hn k1
    obtain ⟨xs, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hxs⟩ := ih s1 s2 xs p1.ok (denoteN_ext hn p1.ext) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨p1.trans p2, ?_⟩
    show Frontend.denoteNList _ (x :: xs) = _
    simp only [List.map_cons, Frontend.denoteNList, denoteN_ext hx p2.ext, hxs]

end RC

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:480-518 targetRecPins
**The recursor records' pins**: the level parameters, the reserved names, the
member recursors' name set, the auxiliary names `T_0.rec_1 … T_0.rec_n`, all
names distinct, and the constructor grouping.  An accepting twin run is an
accepting pure run (`PSpecP`: the reserved-name reads are pins). -/
theorem targetRecPins_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    PSpecP (fun st => dShape st p = some pP ∧ Frontend.denoteCIList st block = some blockP)
      (Arena.targetRecPins p block)
      (fun _ _ => FOk (ConLeche.targetRecPins (m := FueledM) pP blockP) ()) := by
  intro s₀ s' r hok hp hpre hrun
  obtain ⟨hsh, hblk⟩ := hpre
  obtain ⟨hmems, hrecs, -⟩ := dShape_inv hsh
  have hk : p.k = pP.k := BlockShape.k_spec hsh
  simp only [Arena.targetRecPins] at hrun
  by_cases c1 : Arena.blockRecLpsOk p = true
  case neg => rw [ite_eq_right c1] at hrun; exact absurd hrun RC.failBindOk
  rw [ite_eq_left c1] at hrun
  have hL : ConLeche.blockRecLpsOk pP = true := by rw [← blockRecLpsOk_spec hok.wf hsh]; exact c1
  obtain ⟨_, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨-, hs1⟩ := AM.pure_ok k1
  rw [hs1] at z1
  obtain ⟨u, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨p2, rfl⟩ := blockRecNamesUnreserved_spec pP p.recs _ _ u hok hp hrecs k2
  by_cases c2 : ConLeche.blockRecNamesUnreserved pP = true
  case neg => rw [ite_eq_right c2] at z2; exact absurd z2 RC.failBindOk
  rw [ite_eq_left c2] at z2
  have hU := c2
  obtain ⟨_, s3, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨-, hs3⟩ := AM.pure_ok k3
  rw [hs3] at z3
  obtain ⟨u3, s4, k4, z4⟩ := AM.bind_ok z3
  have hown := RC.filter_recs (fun t => decide (t < pP.k))
    (mapM_option_ext (fun x y h => dRec_ext p2.ext x y h) _ _ hrecs)
  rw [← hk] at hown
  obtain ⟨p4, rfl⟩ := blockRecNameSetOk_spec p.members
    (p.recs.filter fun rc => decide (rc.tgt < p.k))
    { pP with recs := pP.recs.filter fun rc => decide (rc.tgt < pP.k) } _ _ u3 p2.ok
    ⟨mapM_option_ext (fun x y h => dMember_ext p2.ext x y h) _ _ hmems,
      by rw [hk] at hown ⊢; exact hown⟩ k4
  by_cases c3 : ConLeche.blockRecNameSetOk
      { pP with recs := pP.recs.filter fun rc => decide (rc.tgt < pP.k) } = true
  case neg => rw [ite_eq_right c3] at z4; exact absurd z4 RC.failBindOk
  rw [ite_eq_left c3] at z4
  have hS := c3
  obtain ⟨_, s5, k5, z5⟩ := AM.bind_ok z4
  obtain ⟨-, hs5⟩ := AM.pure_ok k5
  rw [hs5] at z5
  have p24 := p2.trans p4
  clear hown
  cases hm : p.members with
  | nil =>
    rw [hm] at z5
    have hmP : pP.members = [] := by
      rw [hm] at hmems
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hmems
      exact hmems.symm
    obtain ⟨y, s6, k6, z6⟩ := AM.bind_ok z5
    obtain ⟨p6, hy⟩ := internNNode_run p24.ok (by intro c hc; simp [NNodeView.children] at hc) k6
    simp only [denoteNView] at hy
    have hn0 : denoteN s6.store.ns y =
        some ((pP.memberNames.head?).getD ConLeche.Name.anonymous) := by
      rw [hy]; simp [ConLeche.BlockShape.memberNames, hmP]
    generalize hg0 : (pP.memberNames.head?).getD ConLeche.Name.anonymous = n0P at hn0
    have p06 := p24.trans p6
    obtain ⟨want, sB, kB, zB⟩ := AM.bind_ok z6
    obtain ⟨pB, hwant⟩ := RC.recAuxNames_run y n0P
      (List.range (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs).length) _ sB want
      p06.ok hn0 kB
    have pAB := p06.trans pB
    have hrecsB := mapM_option_ext (fun x y h => dRec_ext pAB.ext x y h) _ _ hrecs
    have hgot := recShapeNames_go (RC.filter_recs (fun t => !decide (t < pP.k)) hrecsB)
    rw [← hk] at hgot
    have hlen1 := denoteNList_length _ _ hgot
    have hlen2 := denoteNList_length _ _ hwant
    have hlenF : (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs).length =
        (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length := by
      have := ConLeche.option_mapM_length (RC.filter_recs (fun t => !decide (t < pP.k)) hrecs)
      rw [← hk] at this ⊢; exact this.symm
    have hA : (((List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).length == want.length &&
          want.all (fun x => (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).contains x)) &&
          (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).all
            (fun x => want.contains x)) =
        (((List.map (fun x => x.cvR.name) (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs)).length ==
            (List.map (fun i => n0P.str (toString "rec_" ++ toString (i + 1)))
              (List.range (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length)).length &&
          (List.map (fun i => n0P.str (toString "rec_" ++ toString (i + 1)))
              (List.range (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length)).all
            (fun x => (List.map (fun x => x.cvR.name)
              (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs)).contains x)) &&
          (List.map (fun x => x.cvR.name) (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs)).all
            (fun x => (List.map (fun i => n0P.str (toString "rec_" ++ toString (i + 1)))
              (List.range (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length)).contains x)) := by
      rw [hlen1, hlen2, all_contains_eq pB.ok.wf hgot hwant, all_contains_eq pB.ok.wf hwant hgot,
        hlenF, hk]
    by_cases cA : (((List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).length == want.length &&
          want.all (fun x => (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).contains x)) &&
          (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).all
            (fun x => want.contains x)) = true
    case neg => rw [ite_eq_right cA] at zB; exact absurd zB RC.failBindOk
    rw [ite_eq_left cA] at zB
    rw [hA] at cA
    obtain ⟨_, sC, kC, zC⟩ := AM.bind_ok zB
    obtain ⟨-, hsC⟩ := AM.pure_ok kC
    rw [hsC] at zC
    have hnames := recShapeNames_go hrecsB
    have hnd := nameNodup_spec pB.ok.wf _ _ hnames
    by_cases cN : nameNodup (List.map (fun x => x.cvR.name) p.recs) = true
    case neg => rw [ite_eq_right cN] at zC; exact absurd zC RC.failBindOk
    rw [ite_eq_left cN] at zC
    rw [hnd] at cN
    obtain ⟨_, sD, kD, zD⟩ := AM.bind_ok zC
    obtain ⟨-, hsD⟩ := AM.pure_ok kD
    rw [hsD] at zD
    have hsp := blockSplit_spec sB.store block blockP (denoteCIList_mono pAB.ext _ _ hblk)
    cases hbs : Arena.blockSplit block with
    | none => rw [hbs] at zD; exact absurd zD (fun hc => AM.fail_ok hc)
    | some q =>
    rw [hbs] at zD hsp
    obtain ⟨cvTs, cs, rs⟩ := q
    obtain ⟨⟨cvTsP, csP, rsP⟩, hq, hcv, hcs, hrs⟩ := hsp
    dsimp only at zD
    have hC : (cvTs.length == p.k && rs.length == p.recs.length &&
          List.map (fun x => x.fst.name) p.allCtors == List.map (fun x => x.fst.name) cs) =
        (cvTsP.length == pP.k && rsP.length == pP.recs.length &&
          List.map (fun x => x.fst.name) pP.allCtors == List.map (fun x => x.fst.name) csP) := by
      rw [ConLeche.option_mapM_length hcv, ConLeche.option_mapM_length hrs, hk, ConLeche.option_mapM_length hrecs,
        beq_nhandleList_eq pB.ok.wf
          (dCtors_names (dCtors_ext pAB.ext _ _ (BlockShape.allCtors_spec hsh)))
          (RC.ctors3_names hcs)]
    by_cases cC : (cvTs.length == p.k && rs.length == p.recs.length &&
          List.map (fun x => x.fst.name) p.allCtors == List.map (fun x => x.fst.name) cs) = true
    · rw [ite_eq_left cC] at zD
      obtain ⟨-, rfl⟩ := AM.pure_ok zD
      rw [hC] at cC
      refine ⟨pAB, 0, ?_⟩
      simp only [ConLeche.targetRecPins, hg0]
      rw [ite_eq_left hL, ite_eq_left hU, ite_eq_left hS, ite_eq_left cA, ite_eq_left (of_decide_eq_true (RC.nodup_of cN)), hq]
      dsimp only
      rw [ite_eq_left cC]
      rfl
    · rw [ite_eq_right cC] at zD; exact absurd zD (fun hc => AM.fail_ok hc)
  | cons ms rest =>
    rw [hm] at z5 hmems
    obtain ⟨mP, msP', hmP, hmsP, -⟩ := mapM_option_cons_inv hmems
    obtain ⟨y, s6, k6, z6⟩ := AM.bind_ok z5
    obtain ⟨rfl, hs6⟩ := AM.pure_ok k6
    subst hs6
    have hn0 : denoteN s6.store.ns ms.cvT.name =
        some ((pP.memberNames.head?).getD ConLeche.Name.anonymous) := by
      rw [denoteN_ext (denoteCV_name (dMember_inv hmsP).1) p24.ext]
      simp [ConLeche.BlockShape.memberNames, hmP]
    generalize hg0 : (pP.memberNames.head?).getD ConLeche.Name.anonymous = n0P at hn0
    have p06 := p24
    obtain ⟨want, sB, kB, zB⟩ := AM.bind_ok z6
    obtain ⟨pB, hwant⟩ := RC.recAuxNames_run ms.cvT.name n0P
      (List.range (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs).length) _ sB want
      p06.ok hn0 kB
    have pAB := p06.trans pB
    have hrecsB := mapM_option_ext (fun x y h => dRec_ext pAB.ext x y h) _ _ hrecs
    have hgot := recShapeNames_go (RC.filter_recs (fun t => !decide (t < pP.k)) hrecsB)
    rw [← hk] at hgot
    have hlen1 := denoteNList_length _ _ hgot
    have hlen2 := denoteNList_length _ _ hwant
    have hlenF : (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs).length =
        (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length := by
      have := ConLeche.option_mapM_length (RC.filter_recs (fun t => !decide (t < pP.k)) hrecs)
      rw [← hk] at this ⊢; exact this.symm
    have hA : (((List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).length == want.length &&
          want.all (fun x => (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).contains x)) &&
          (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).all
            (fun x => want.contains x)) =
        (((List.map (fun x => x.cvR.name) (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs)).length ==
            (List.map (fun i => n0P.str (toString "rec_" ++ toString (i + 1)))
              (List.range (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length)).length &&
          (List.map (fun i => n0P.str (toString "rec_" ++ toString (i + 1)))
              (List.range (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length)).all
            (fun x => (List.map (fun x => x.cvR.name)
              (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs)).contains x)) &&
          (List.map (fun x => x.cvR.name) (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs)).all
            (fun x => (List.map (fun i => n0P.str (toString "rec_" ++ toString (i + 1)))
              (List.range (List.filter (fun rc => !decide (rc.tgt < pP.k)) pP.recs).length)).contains x)) := by
      rw [hlen1, hlen2, all_contains_eq pB.ok.wf hgot hwant, all_contains_eq pB.ok.wf hwant hgot,
        hlenF, hk]
    by_cases cA : (((List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).length == want.length &&
          want.all (fun x => (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).contains x)) &&
          (List.map (fun x => x.cvR.name)
            (List.filter (fun rc => !decide (rc.tgt < p.k)) p.recs)).all
            (fun x => want.contains x)) = true
    case neg => rw [ite_eq_right cA] at zB; exact absurd zB RC.failBindOk
    rw [ite_eq_left cA] at zB
    rw [hA] at cA
    obtain ⟨_, sC, kC, zC⟩ := AM.bind_ok zB
    obtain ⟨-, hsC⟩ := AM.pure_ok kC
    rw [hsC] at zC
    have hnames := recShapeNames_go hrecsB
    have hnd := nameNodup_spec pB.ok.wf _ _ hnames
    by_cases cN : nameNodup (List.map (fun x => x.cvR.name) p.recs) = true
    case neg => rw [ite_eq_right cN] at zC; exact absurd zC RC.failBindOk
    rw [ite_eq_left cN] at zC
    rw [hnd] at cN
    obtain ⟨_, sD, kD, zD⟩ := AM.bind_ok zC
    obtain ⟨-, hsD⟩ := AM.pure_ok kD
    rw [hsD] at zD
    have hsp := blockSplit_spec sB.store block blockP (denoteCIList_mono pAB.ext _ _ hblk)
    cases hbs : Arena.blockSplit block with
    | none => rw [hbs] at zD; exact absurd zD (fun hc => AM.fail_ok hc)
    | some q =>
    rw [hbs] at zD hsp
    obtain ⟨cvTs, cs, rs⟩ := q
    obtain ⟨⟨cvTsP, csP, rsP⟩, hq, hcv, hcs, hrs⟩ := hsp
    dsimp only at zD
    have hC : (cvTs.length == p.k && rs.length == p.recs.length &&
          List.map (fun x => x.fst.name) p.allCtors == List.map (fun x => x.fst.name) cs) =
        (cvTsP.length == pP.k && rsP.length == pP.recs.length &&
          List.map (fun x => x.fst.name) pP.allCtors == List.map (fun x => x.fst.name) csP) := by
      rw [ConLeche.option_mapM_length hcv, ConLeche.option_mapM_length hrs, hk, ConLeche.option_mapM_length hrecs,
        beq_nhandleList_eq pB.ok.wf
          (dCtors_names (dCtors_ext pAB.ext _ _ (BlockShape.allCtors_spec hsh)))
          (RC.ctors3_names hcs)]
    by_cases cC : (cvTs.length == p.k && rs.length == p.recs.length &&
          List.map (fun x => x.fst.name) p.allCtors == List.map (fun x => x.fst.name) cs) = true
    · rw [ite_eq_left cC] at zD
      obtain ⟨-, rfl⟩ := AM.pure_ok zD
      rw [hC] at cC
      refine ⟨pAB, 0, ?_⟩
      simp only [ConLeche.targetRecPins, hg0]
      rw [ite_eq_left hL, ite_eq_left hU, ite_eq_left hS, ite_eq_left cA, ite_eq_left (of_decide_eq_true (RC.nodup_of cN)), hq]
      dsimp only
      rw [ite_eq_left cC]
      rfl
    · rw [ite_eq_right cC] at zD; exact absurd zD (fun hc => AM.fail_ok hc)

/-! ## A recursor's class, resolved -/

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:356-360 targetCtorsOf
**The constructors of a stored inductive and its parameter count**:
`nestContainer`'s reading at a context whose lookup is the index's
(`Bridge/Inductives/Positivity.lean`'s `nestContainer_spec`). -/
theorem targetCtorsOf_spec {env : Env} (fe : IFEnv) (I : NIdx) (IP : ConLeche.Name) :
    PSpec (fun st => IFEnvOKS env fe st ∧ denoteN st.ns I = some IP)
      (Arena.targetCtorsOf fe I) (ROp RCont (ConLeche.targetCtorsOf (mkFEnv env) IP)) := by
  intro s₀ s' r hok hp hrun
  simp only [Arena.targetCtorsOf] at hrun
  simp only [ConLeche.targetCtorsOf]
  exact nestContainer_spec (env := env) _ (by simp only [mkFEnv_find?_fun]) I IP s₀ s' r hok hp hrun

namespace RC

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:410 targetMajorOf (the
closedness test) — one parameter closed over the recursor's parameters, the
two reads short-circuiting. -/
theorem closed1_run {s₀ s' : AState} {x : EIdx} {xP : Expr} {n : Nat} {r : Bool}
    (hok : StateOK s₀) (hx : denoteE s₀.store x = some xP)
    (hrun : (do
      if (← bvarB coreWalkFuel x) != 0 then pure false
      else pure (decide ((← fvarB coreWalkFuel x) ≤ n)) : AM Bool) s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r = (xP.bvarB == 0 && decide (xP.fvarB ≤ n)) := by
  obtain ⟨x1, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, -, rfl⟩ := bvarB_pstep hok hx k1
  by_cases c1 : (xP.bvarB != 0) = true
  · rw [ite_eq_left c1] at z1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨p1, ?_⟩
    simp only [bne_iff_ne, ne_eq] at c1
    simp [c1]
  · rw [ite_eq_right c1] at z1
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at c1
    obtain ⟨x2, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, -, rfl⟩ := fvarB_pstep p1.ok (denote_ext hx p1.ext) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    exact ⟨p1.trans p2, by simp [c1]⟩

end RC

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:380-439 targetMajorOf
**A recursor's major, resolved** from its opened type: a MEMBER at the
block's levels and parameters, or an outside stored inductive (not `Quot`,
its parameters closed over the recursor's, naming a member, in the block's
universe).  The class record denotes con-leche's (`dMajor`); the pure side
at `mkFEnv env` performs no operation. -/
theorem targetMajorOf_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (ctorsAs : List (List (IConstantVal × Nat))) (ctorsAsP : List (List (ConstantVal × Nat)))
    (pfvs fvs : List EIdx) (pfvsP fvsP : List Expr) (mty : EIdx) (mtyP : Expr) :
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ ctorsAs.mapM (dCtors st) = some ctorsAsP ∧
        Frontend.denoteEList st pfvs = some pfvsP ∧ Frontend.denoteEList st fvs = some fvsP ∧
        denoteE st mty = some mtyP)
      (Arena.targetMajorOf fe p ctorsAs pfvs fvs mty)
      (fun st r v => dMajor st r = some v)
      (ConLeche.targetMajorOf (m := FueledM) (mkFEnv env) pP ctorsAsP pfvsP fvsP mtyP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hsh, hcas, hpf, hfv, hmty⟩ := hpre
  obtain ⟨hmems, -, hnP, -, hres, -⟩ := dShape_inv hsh
  simp only [Arena.targetMajorOf] at hrun
  obtain ⟨args, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hargs⟩ := getAppArgs_run hok.state hmty k1
  rw [hs1] at z1
  obtain ⟨hd, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨hs2, hhd⟩ := getAppFn_run hok.state hmty k2
  rw [hs2] at z2
  by_cases ct : (hd.tag == ETag.const) = true
  case neg => rw [ite_eq_right ct] at z2; exact absurd z2 (fun hc => AM.fail_ok hc)
  rw [ite_eq_left ct] at z2
  obtain ⟨o, s3, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨hs3, ho⟩ := viewConst_run k3
  rw [hs3] at z3
  cases o with
  | none => exact absurd z3 (fun hc => AM.fail_ok hc)
  | some t0 =>
  obtain ⟨I, us⟩ := t0
  obtain ⟨IP, usP, hg, hI, hus⟩ := denote_const_inv hok.state.wf
    (view_of_viewConst_tag ct ho.symm) hhd
  dsimp only at z3
  simp only [ConLeche.targetMajorOf, hg]
  have hfi := findIdx_handle_eq hok.state.wf hI (BlockShape.memberNames_spec hsh)
  rw [hfi] at z3
  cases hft : pP.memberNames.findIdx? (· == IP) with
  | some t =>
    rw [hft] at z3
    dsimp only at z3 ⊢
    -- the member
    obtain ⟨ms, s4, k4, z4⟩ := AM.bind_ok z3
    obtain ⟨hms, hs4⟩ := unwrapOr_ok k4
    rw [hs4] at z4
    have hj := mapM_option_getElem? (st := s₀.store) hmems t
    rw [hms] at hj
    obtain ⟨msP, hmsP, hdm⟩ := hj
    obtain ⟨cA, s5, k5, z5⟩ := AM.bind_ok z4
    obtain ⟨hcA, hs5⟩ := unwrapOr_ok k5
    rw [hs5] at z5
    have hj2 := mapM_option_getElem? (st := s₀.store) hcas t
    rw [hcA] at hj2
    obtain ⟨cAP, hcAP, hdc⟩ := hj2
    obtain ⟨bl, s6, k6, z6⟩ := AM.bind_ok z5
    obtain ⟨p6, hbl⟩ := paramLevels_spec p.lps pP.lps s₀ s6 bl hok.state
      (BlockShape.lps_spec hsh) k6
    have hb1 := beq_lshandle_eq p6.ok.wf (denoteLs_ext hus p6.ext) hbl
    have hb2 := beq_of_denoteEList p6.ok.wf
      (denoteEList_take (denoteEList_ext p6.ext _ _ hargs) p.nP)
      (denoteEList_take (denoteEList_ext p6.ext _ _ hfv) p.nP)
    rw [hmsP, hcAP]
    by_cases cm : (us == bl && List.take p.nP args == List.take p.nP fvs) = true
    · rw [ite_eq_left cm] at z6
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z6
      rw [hb1, hb2, hnP] at cm
      refine ⟨p6.toCore hok, _, ?_, FOk.bind FOk.unwrapOr (FOk.bind FOk.unwrapOr
        (by rw [ite_eq_left cm]; exact FOk.pure _))⟩
      obtain ⟨-, hnidx, -⟩ := dMember_inv hdm
      simp only [dMajor, denoteN_ext hI p6.ext, denoteLs_ext hus p6.ext,
        denoteEList_take (denoteEList_ext p6.ext _ _ hfv), dCtors_ext p6.ext _ _ hdc,
        denoteEList_ext p6.ext _ _ hpf, hnP, hnidx, List.mapM_nil]
      rfl
    · rw [ite_eq_right cm] at z6; exact absurd z6 (fun hc => AM.fail_ok hc)
  | none =>
    rw [hft] at z3
    dsimp only at z3 ⊢
    -- an outside inductive
    obtain ⟨q, s4, k4, z4⟩ := AM.bind_ok z3
    obtain ⟨hs4, hq⟩ := pinAt_run (x := ConLeche.quotName) hok.pins rfl k4
    rw [hs4] at z4
    have hbq := beq_handle_eq hok.state.wf hI hq
    by_cases cq : (I == q) = true
    · rw [ite_eq_left cq] at z4; exact absurd z4 (fun hc => AM.fail_ok hc)
    rw [ite_eq_right cq] at z4
    rw [hbq] at cq
    rw [ite_eq_right cq]
    obtain ⟨o2, s5, k5, z5⟩ := AM.bind_ok z4
    obtain ⟨p5, ho2⟩ := targetCtorsOf_spec (env := env) fe I IP s₀ s5 o2 hok.state
      ⟨hok.ienv.toS, hI⟩ k5
    cases o2 with
    | none => exact absurd z5 (fun hc => AM.fail_ok hc)
    | some t2 =>
    obtain ⟨nPc, ctors⟩ := t2
    obtain ⟨⟨nPcP, ctorsP⟩, hco, hnpc, hctors⟩ := ho2
    simp only at hnpc
    subst hnpc
    rw [hco]
    dsimp only at z5 ⊢
    have c5 := p5.toCore hok
    have hds := denoteEList_take (denoteEList_ext p5.ext _ _ hargs) nPc
    have hlen : (List.take nPc args).length = (List.take nPc mtyP.getAppArgs).length :=
      denoteEList_length hds
    by_cases cl : ((List.take nPc args).length != nPc) = true
    · rw [ite_eq_left cl] at z5; exact absurd z5 (fun hc => AM.fail_ok hc)
    rw [ite_eq_right cl] at z5
    obtain ⟨cls, s6, k6, z6⟩ := AM.bind_ok z5
    obtain ⟨p6, hcls⟩ := allM_E_pstep (fun _ => True) (fun _ h => h)
      (fun e eP s₀ s' b hok _ he hrun => RC.closed1_run hok he hrun)
      _ _ s5 s6 cls p5.ok trivial hds k6
    have c6 := c5.trans (p6.toCore c5.ok)
    by_cases cc : (!cls) = true
    · rw [ite_eq_left cc] at z6; exact absurd z6 (fun hc => AM.fail_ok hc)
    rw [ite_eq_right cc] at z6
    have hcl1 : ((List.take nPc mtyP.getAppArgs).length == nPc &&
        (List.take nPc mtyP.getAppArgs).all fun x => x.bvarB == 0 && decide (x.fvarB ≤ pP.nP))
          = true := by
      rw [← hlen, ← hnP]
      have e1 : ((List.take nPc args).length == nPc) = true := by simpa using cl
      have e2 : cls = true := by simpa using cc
      rw [e1, ← hcls, e2]; rfl
    rw [ite_eq_left hcl1]
    obtain ⟨an, s7, k7, z7⟩ := AM.bind_ok z6
    obtain ⟨p7, han⟩ := anyM_E_pstep (fun st => Frontend.denoteNList st.ns p.memberNames =
        some pP.memberNames) (fun hx h => denoteNListE_ext hx _ _ h)
      (fun e eP s₀ s' b hok hq he hrun => nestOcc_spec p.memberNames pP.memberNames 0 0 e eP
        s₀ s' b hok ⟨hq, he⟩ hrun)
      _ _ s6 s7 an p6.ok (denoteNListE_ext c6.ext _ _ (BlockShape.memberNames_spec hsh))
      (denoteEList_ext p6.ext _ _ hds) k7
    have c7 := c6.trans (p7.toCore c6.ok)
    by_cases ca : an = true
    case neg => rw [ite_eq_right ca] at z7; exact absurd z7 RC.failBindOk
    rw [ite_eq_left ca] at z7
    rw [han] at ca
    rw [ite_eq_left ca]
    obtain ⟨_, s8, k8, z8⟩ := AM.bind_ok z7
    obtain ⟨-, hs8⟩ := AM.pure_ok k8
    rw [hs8] at z8
    obtain ⟨ni, s9, k9, z9⟩ := AM.bind_ok z8
    obtain ⟨c9, ⟨niP, lP⟩, ⟨hni1, hni2⟩, hFo⟩ := targetOutsideInst_spec fe I IP us usP _ _
      s7 s9 ni c7.ok ⟨denoteN_ext hI c7.ext, denoteLs_ext hus c7.ext,
        denoteEList_ext (p6.ext.trans p7.ext) _ _ hds⟩ k9
    have c79 := c7.trans c9
    obtain ⟨nIdx, sI⟩ := ni
    dsimp only at z9 hni1 hni2
    obtain ⟨lv, s10, k10, z10⟩ := AM.bind_ok z9
    obtain ⟨c10, rfl⟩ := lvlEq?_crun c9.ok hni2
      (denoteL_ext hres (c79.ext)) k10
    obtain ⟨b, s11, k11, z11⟩ := AM.bind_ok z10
    obtain ⟨hlv, hs11⟩ := liftFueled_ok k11
    rw [hs11] at z11
    by_cases cb : b = true
    case neg => rw [ite_eq_right cb] at z11; exact absurd z11 RC.failBindOk
    rw [ite_eq_left cb] at z11
    obtain ⟨_, s12, k12, z12⟩ := AM.bind_ok z11
    obtain ⟨-, hs12⟩ := AM.pure_ok k12
    rw [hs12] at z12
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z12
    have c10' := c79.trans c10
    refine ⟨c10', ConLeche.TargetMajor.mk IP usP (List.take nPc mtyP.getAppArgs) nPc niP ctorsP
      none [] pfvsP, ?_,
      FOk.bind hFo (FOk.bind (hlv ▸ FOk.liftFueled) ?_)⟩
    · simp only [dMajor, denoteN_ext hI c10'.ext, denoteLs_ext hus c10'.ext,
        denoteEList_ext (p6.ext.trans (p7.ext.trans (c9.ext.trans c10.ext))) _ _ hds,
        dCtors_ext (p6.ext.trans (p7.ext.trans (c9.ext.trans c10.ext))) _ _ hctors,
        denoteEList_ext c10'.ext _ _ hpf, hni1, List.mapM_nil]
      rfl
    · rw [ite_eq_left cb]; exact FOk.pure _

end ConRon.Bridge.Inductives
