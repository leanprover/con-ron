/-
# `ConRon.Bridge.Compare.Justify` — the justification's tests denote con-leche's

The twin's `Arena/Justify.lean` against con-leche's `ConLeche/Cached/Justify.lean`, one theorem
per test: which records offer a statement (`builtinAxiomName_run`, `justifiable_run`) and the
comparisons of a challenge constant with the solution's (`levelsRenaming_eq`,
`sameCvUpToLevels_run`, `tableBeqP_eq`, `copyB_run`, `refinesB_run`).  Every comparison is a
handle comparison in the twin and a pointer-first `beqP` upstream; at a well-formed store the
two agree by injectivity (`denoteCI_inj`, `denoteCV_inj`), and a renaming of level parameters is
`IConstantInfo.atLps_run` against `atLpsC`.
-/
module

public import ConRon.Bridge.Checker.Basis
public import ConRon.Arena.Justify
public import ConLeche.Cached.Justify
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Core.Walks.Nat
import ConLeche.Verify.Cached.DeclNames

public section

namespace ConRon.Bridge

set_option autoImplicit false
set_option experimental.vcgen true

open ConLeche ConRon.Arena Std.WP ConRon.Bridge.Core
open scoped Lean.Order

/-! ## Which records offer a statement -/

/-! The seven built-in axioms' pin slots, by name. -/

/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the `PIN_PROPEXT` slot. -/
theorem pinNames_eq_propextName : pinNames[PIN_PROPEXT]? = some ConLeche.propextName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the `PIN_CHOICE` slot. -/
theorem pinNames_eq_choiceName : pinNames[PIN_CHOICE]? = some ConLeche.choiceName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the `PIN_QUOT_SOUND` slot. -/
theorem pinNames_eq_quotSoundName : pinNames[PIN_QUOT_SOUND]? = some ConLeche.quotSoundName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the `PIN_SORRY_AX` slot. -/
theorem pinNames_eq_sorryAxName : pinNames[PIN_SORRY_AX]? = some ConLeche.sorryAxName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the `PIN_TRUST_COMPILER`
slot. -/
theorem pinNames_eq_trustCompilerName :
    pinNames[PIN_TRUST_COMPILER]? = some ConLeche.trustCompilerName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the `PIN_OF_REDUCE_NAT`
slot. -/
theorem pinNames_eq_ofReduceNatName :
    pinNames[PIN_OF_REDUCE_NAT]? = some ConLeche.ofReduceNatName := rfl
/-- con-leche: ConLeche/Kernel/Basis/Names.lean reservedBasisNames — the `PIN_OF_REDUCE_BOOL`
slot. -/
theorem pinNames_eq_ofReduceBoolName :
    pinNames[PIN_OF_REDUCE_BOOL]? = some ConLeche.ofReduceBoolName := rfl


/-- con-leche: ConLeche/Cached/Justify.lean:47-51 builtinAxiomName — the seven pinned handles
answer con-leche's test at a denoted name; the state does not move. -/
theorem builtinAxiomName_run {s s' : AState} {n : NIdx} {nm : ConLeche.Name} {r : Bool}
    (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.builtinAxiomName n s = .ok (r, s')) :
    s' = s ∧ r = ConLeche.Cached.builtinAxiomName nm := by
  simp only [Arena.builtinAxiomName, Arena.propextName, Arena.pinPropext, Arena.choiceName,
    Arena.pinChoice, Arena.pinQuotSound, Arena.pinSorryAx, Arena.trustCompilerName,
    Arena.pinTrustCompiler, Arena.ofReduceNatName, Arena.pinOfReduceNat,
    Arena.ofReduceBoolName, Arena.pinOfReduceBool] at hrun
  obtain ⟨a, s₁, h1, k1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, ha⟩ := pinAt_run hp pinNames_eq_propextName h1
  obtain ⟨b, s₂, h2, k2⟩ := AM.bind_ok k1
  obtain ⟨rfl, hb⟩ := pinAt_run hp pinNames_eq_choiceName h2
  obtain ⟨c, s₃, h3, k3⟩ := AM.bind_ok k2
  obtain ⟨rfl, hc⟩ := pinAt_run hp pinNames_eq_quotSoundName h3
  obtain ⟨d, s₄, h4, k4⟩ := AM.bind_ok k3
  obtain ⟨rfl, hd⟩ := pinAt_run hp pinNames_eq_sorryAxName h4
  obtain ⟨f, s₅, h5, k5⟩ := AM.bind_ok k4
  obtain ⟨rfl, hf⟩ := pinAt_run hp pinNames_eq_trustCompilerName h5
  obtain ⟨g, s₆, h6, k6⟩ := AM.bind_ok k5
  obtain ⟨rfl, hg⟩ := pinAt_run hp pinNames_eq_ofReduceNatName h6
  obtain ⟨h, s₇, h7, k7⟩ := AM.bind_ok k6
  obtain ⟨rfl, hh⟩ := pinAt_run hp pinNames_eq_ofReduceBoolName h7
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k7
  refine ⟨rfl, ?_⟩
  simp only [ConLeche.Cached.builtinAxiomName, denoteN_beqS hok.wf hn ha,
    denoteN_beqS hok.wf hn hb, denoteN_beqS hok.wf hn hc, denoteN_beqS hok.wf hn hd,
    denoteN_beqS hok.wf hn hf, denoteN_beqS hok.wf hn hg, denoteN_beqS hok.wf hn hh]

/-- con-leche: ConLeche/Cached/Justify.lean:69-77 justifiable — **the statement a record offers is
con-leche's**: none where con-leche offers none, and an axiom record's own statement, denoting
con-leche's, where it offers one.  The state does not move. -/
theorem justifiable_run {env : Env} {fe : IFEnv} {pd : IDeclaration} {d : Declaration}
    {r : Option IConstantVal} {s s' : AState} (hck : CheckOK false env fe s)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.justifiable pd s = .ok (r, s')) :
    s' = s ∧ (r = none → ConLeche.Cached.justifiable d = none) ∧
      ∀ cv, r = some cv → pd = .axiomDecl cv ∧ ∃ c, Frontend.denoteCV s.store cv = some c ∧
        d = .axiomDecl c ∧ ConLeche.Cached.justifiable d = some c := by
  cases pd with
  | axiomDecl cv =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    have hn := (denoteCV_inv hc).1
    simp only [Arena.justifiable] at hrun
    obtain ⟨b1, s₁, h1, k1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hb1⟩ := builtinAxiomName_run hck.state hck.pins hn h1
    rcases AM.ite_ok k1 with ⟨hy1, k1⟩ | ⟨hn1, k1⟩
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
      refine ⟨rfl, fun _ => ?_, fun _ h => nomatch h⟩
      simp [ConLeche.Cached.justifiable, ← hb1, hy1]
    obtain ⟨b2, s₂, h2, k2⟩ := AM.bind_ok k1
    obtain ⟨rfl, hb2⟩ := AM.of_run (P := fun t => t = s₁) rfl h2
      (natOpName_run s₁ cv.name c.name hck hn)
    rcases AM.ite_ok k2 with ⟨hy2, k2⟩ | ⟨hn2, k2⟩
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      refine ⟨rfl, fun _ => ?_, fun _ h => nomatch h⟩
      simp [ConLeche.Cached.justifiable, ← hb1, ← hb2, hy2]
    obtain ⟨ns, s₃, h3, k3⟩ := AM.bind_ok k2
    obtain ⟨rfl, hns⟩ := reduceOpNames_run hck.pins h3
    have hcont : ns.contains cv.name = ConLeche.reduceOpNames.contains c.name :=
      denoteNList_contains hck.state.wf _ _ (denoteNL_toList _ _ hns) _ _ hn
    rcases AM.ite_ok k3 with ⟨hy3, k3⟩ | ⟨hn3, k3⟩
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
      refine ⟨rfl, fun _ => ?_, fun _ h => nomatch h⟩
      have h3 : c.name ∈ ConLeche.reduceOpNames := by
        have := hcont ▸ hy3; simpa using this
      simp [ConLeche.Cached.justifiable, h3]
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
      refine ⟨rfl, ?_, ?_⟩
      · intro h; exact nomatch h
      intro cv' h
      obtain rfl := Option.some.inj h
      refine ⟨rfl, c, hc, rfl, ?_⟩
      have h3 : c.name ∉ ConLeche.reduceOpNames := by
        have : ConLeche.reduceOpNames.contains c.name = false := by rw [← hcont]; simpa using hn3
        simpa using this
      simp only [Bool.not_eq_true] at hn1 hn2
      simp [ConLeche.Cached.justifiable, ← hb1, ← hb2, h3, hn1, hn2]
  | defnDecl v e h | thmDecl v e | opaqueDecl v e =>
    simp only [Arena.justifiable] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨rfl, fun _ => ?_, fun _ h => nomatch h⟩
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · obtain rfl := Option.some.inj hd; rfl
    · exact nomatch hd
  | indDecl b nP | quotDecl k v =>
    simp only [Arena.justifiable] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨rfl, fun _ => ?_, fun _ h => nomatch h⟩
    simp only [Frontend.denoteDecl] at hd
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hd; rfl

/-! ## The comparison -/

/-- con-leche: ConLeche/Cached/Justify.lean:81-83 levelsRenaming — the handle test is
con-leche's, on the read-back names. -/
theorem levelsRenaming_eq {st : EStore} (hwf : StoreWF st) {ps ps' : List NIdx}
    {xs xs' : List ConLeche.Name} (h : Frontend.denoteNList st.ns ps = some xs)
    (h' : Frontend.denoteNList st.ns ps' = some xs') :
    Arena.levelsRenaming ps ps' = ConLeche.Cached.levelsRenaming xs xs' := by
  have hnd : ∀ ys : List ConLeche.Name, ConLeche.Name.nodup ys = decide ys.Nodup := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      rw [ConLeche.Name.nodup, ih]
      by_cases hy : y ∈ ys <;> simp [hy, List.nodup_cons]
  simp only [Arena.levelsRenaming, ConLeche.Cached.levelsRenaming,
    nameNodup_denote hwf _ _ h, nameNodup_denote hwf _ _ h', hnd,
    denoteNList_length _ _ h, denoteNList_length _ _ h']

/-- con-leche: none — two denoting name lists compare as their names. -/
theorem denoteNList_beq {st : EStore} (hwf : StoreWF st) {ps ps' : List NIdx}
    {xs xs' : List ConLeche.Name} (h : Frontend.denoteNList st.ns ps = some xs)
    (h' : Frontend.denoteNList st.ns ps' = some xs') : (ps == ps') = (xs == xs') :=
  beq_of_denote_inj (fun {i j x} hi hj => denoteNList_inj hwf i j x hi hj) h h'

/-- con-leche: ConLeche/Cached/Justify.lean:85-91 sameCvUpToLevels — **the statement test is
con-leche's**: the handle comparison at equal level-parameter names, else the renaming
(`IConstantVal.atLps_run`, con-leche's `atLpsC`). -/
theorem sameCvUpToLevels_run {cv cv' : IConstantVal} {c c' : ConstantVal} {r : Bool}
    {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hc : Frontend.denoteCV s.store cv = some c) (hc' : Frontend.denoteCV s.store cv' = some c')
    (hrun : Arena.sameCvUpToLevels cv cv' s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.Cached.sameCvUpToLevels c c' := by
  have hl := (denoteCV_inv hc).2.1
  have hl' := (denoteCV_inv hc').2.1
  have hlb := denoteNList_beq hok.wf hl hl'
  simp only [Arena.sameCvUpToLevels] at hrun
  simp only [ConLeche.Cached.sameCvUpToLevels]
  rcases AM.ite_ok hrun with ⟨hy, k⟩ | ⟨hn, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    have hy' : (c.levelParams == c'.levelParams) = true := by rw [← hlb]; simpa using hy
    simp only [hy', ↓reduceIte, ConstantVal.beqP_eq]
    exact ⟨RStep.refl hok hr, beq_of_denote_inj (denoteCV_inj hok.wf) hc hc'⟩
  · have hn' : (c.levelParams == c'.levelParams) = false := by rw [← hlb]; simpa using hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte]
    rw [← levelsRenaming_eq hok.wf hl hl']
    rcases AM.ite_ok k with ⟨hy2, k⟩ | ⟨hn2, k⟩
    · obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok k
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨hs1, hx⟩ := IConstantVal.atLps_run hok hr hc' hl h1
      refine ⟨hs1, ?_⟩
      rw [hy2, Bool.true_and, ← ConLeche.Cached.ConstantVal.atLps_eq_atLpsC,
        ConstantVal.beqP_eq]
      exact beq_of_denote_inj (denoteCV_inj hs1.ok.wf) hx (denoteCV_ext hc hs1.ext)
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
      simp only [Bool.not_eq_true] at hn2
      exact ⟨RStep.refl hok hr, by rw [hn2, Bool.false_and]⟩

/-- con-leche: ConLeche/Kernel/Env.lean:435-438 isStmtKind — the kind test reads the kind,
which the denotation keeps. -/
theorem isStmtKind_denote {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) : ci.isStmtKind = c.isStmtKind := by
  cases ci with
  | axiomInfo v => obtain ⟨cv, rfl, -⟩ := denoteCI_axiom_inv h; rfl
  | defnInfo v e hh => obtain ⟨cv, x, rfl, -, -⟩ := denoteCI_defn_inv h; rfl
  | thmInfo v => obtain ⟨cv, rfl, -⟩ := denoteCI_thm_inv h; rfl
  | indInfo v cap => obtain ⟨cv, d, rfl, -, -⟩ := denoteCI_ind_inv h; rfl
  | ctorInfo v nP nF T => obtain ⟨cv, rfl, -⟩ := denoteCI_ctor_inv h; rfl
  | recInfo v mI rP k rs => obtain ⟨cv, Rs, rfl, -, -⟩ := denoteCI_rec_inv h; rfl

/-- con-leche: ConLeche/Cached/Justify.lean:105-115 copyB — **the copy test is con-leche's**: the
handle comparison at equal level-parameter names; else, for a definition, theorem or axiom at an
unreserved name, the solution's constant at the input's names (`IConstantInfo.atLps_run`, the
cited `atLpsC`) compared. -/
theorem copyB_run {ci' ci : IConstantInfo} {c' c : ConstantInfo} {r : Bool} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hp : PinsOK s)
    (hc' : Frontend.denoteCI s.store ci' = some c') (hc : Frontend.denoteCI s.store ci = some c)
    (hrun : Arena.copyB ci' ci s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.Cached.copyB c' c := by
  have hv := denoteCV_inv (denoteCI_toConstantVal hc)
  have hv' := denoteCV_inv (denoteCI_toConstantVal hc')
  have hlb := denoteNList_beq hok.wf hv.2.1 hv'.2.1
  simp only [Arena.copyB] at hrun
  simp only [ConLeche.Cached.copyB]
  rcases AM.ite_ok hrun with ⟨hy, k⟩ | ⟨hn, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    have hy' : (c.toConstantVal.levelParams == c'.toConstantVal.levelParams) = true := by
      rw [← hlb]; simpa using hy
    simp only [hy', ↓reduceIte, ConstantInfo.beqP_eq]
    exact ⟨RStep.refl hok hr, beq_of_denote_inj (denoteCI_inj hok.wf) hc hc'⟩
  · have hn' : (c.toConstantVal.levelParams == c'.toConstantVal.levelParams) = false := by
      rw [← hlb]; simpa using hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte]
    rw [← isStmtKind_denote hc']
    rcases AM.ite_ok k with ⟨hy2, k⟩ | ⟨hn2, k⟩
    · obtain ⟨rs, s₁, h1, k1⟩ := AM.bind_ok k
      obtain ⟨rfl, hrs⟩ := reservedBasisNames_runB hp h1
      have hcont : rs.contains ci'.toConstantVal.name =
          ConLeche.reservedBasisNames.contains c'.toConstantVal.name :=
        denoteNList_contains hok.wf _ _ hrs _ _ hv'.1
      have hlr := levelsRenaming_eq hok.wf hv'.2.1 hv.2.1
      rcases AM.ite_ok k1 with ⟨hy3, k1⟩ | ⟨hn3, k1⟩
      · obtain ⟨x, s₂, h2, h3⟩ := AM.bind_ok k1
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
        obtain ⟨hs2, hx⟩ := IConstantInfo.atLps_run hok hr hc' hv.2.1 h2
        refine ⟨hs2, ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy3
        rw [hy2, ← hcont, ← hlr, hy3.1, hy3.2, ← ConLeche.Cached.ConstantInfo.atLps_eq_atLpsC,
          ConstantInfo.beqP_eq]
        simpa using beq_of_denote_inj (denoteCI_inj hs2.ok.wf) hx (denoteCI_ext hc hs2.ext)
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
        refine ⟨RStep.refl hok hr, ?_⟩
        simp only [Bool.not_eq_true] at hn3
        rw [← hcont, ← hlr, hy2, Bool.true_and, hn3, Bool.false_and]
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
      simp only [Bool.not_eq_true] at hn2
      exact ⟨RStep.refl hok hr, by rw [hn2]; rfl⟩

/-- con-leche: ConLeche/Cached/Justify.lean:117-126 refinesB — **the refinement test is
con-leche's**: a copy, or an axiom copying the statement of a solution definition, theorem or
axiom at a name no compiler-trust operation has. -/
theorem refinesB_run {ci ci' : IConstantInfo} {c c' : ConstantInfo} {r : Bool} {s s' : AState}
    (hok : StateOK s) (hr : ReadOK s) (hp : PinsOK s)
    (hc : Frontend.denoteCI s.store ci = some c) (hc' : Frontend.denoteCI s.store ci' = some c')
    (hrun : Arena.refinesB ci ci' s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.Cached.refinesB c c' := by
  simp only [Arena.refinesB] at hrun
  obtain ⟨b, s₁, h1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hb⟩ := copyB_run hok hr hp hc' hc h1
  have hc₁ := denoteCI_ext hc hs1.ext
  have hc₁' := denoteCI_ext hc' hs1.ext
  have hp₁ : PinsOK s₁ := hp.mono hs1.ext hs1.pins
  unfold ConLeche.Cached.refinesB
  rw [← hb]
  rcases AM.ite_ok k1 with ⟨hy, k⟩ | ⟨hn, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    have hy' : b = true := by simpa using hy
    rw [hy', Bool.true_or]
    exact ⟨hs1, rfl⟩
  · simp only [Bool.not_eq_true] at hn
    rw [hn, Bool.false_or]
    cases ci with
    | axiomInfo v =>
      obtain ⟨cv, rfl, hv⟩ := denoteCI_axiom_inv hc
      dsimp only
      rw [← isStmtKind_denote hc']
      rcases AM.ite_ok k with ⟨hy2, k⟩ | ⟨hn2, k⟩
      · obtain ⟨ns, s₂, h2, k2⟩ := AM.bind_ok k
        obtain ⟨hs2, hns⟩ := reduceOpNames_run hp₁ h2
        rw [hs2] at k2
        have hcont : ns.contains ci'.toConstantVal.name =
            ConLeche.reduceOpNames.contains c'.toConstantVal.name :=
          denoteNList_contains hs1.ok.wf _ _ (denoteNL_toList _ _ hns) _ _
            (denoteCV_inv (denoteCI_toConstantVal hc₁')).1
        have hax : Frontend.denoteCI s₁.store (.axiomInfo ci'.toConstantVal) =
            some (.axiomInfo c'.toConstantVal) := by
          simp only [Frontend.denoteCI, denoteCI_toConstantVal hc₁', Option.map_some]
        rcases AM.ite_ok k2 with ⟨hy3, k2⟩ | ⟨hn3, k2⟩
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
          refine ⟨hs1, ?_⟩
          have h3 : ConLeche.reduceOpNames.contains c'.toConstantVal.name = true := hcont ▸ hy3
          rw [hy2, h3]; rfl
        · obtain ⟨hs3, hb3⟩ := copyB_run hs1.ok hs1.read hp₁ hax hc₁ k2
          refine ⟨hs1.trans hs3, ?_⟩
          have h3 : ConLeche.reduceOpNames.contains c'.toConstantVal.name = false := by
            rw [← hcont]; simpa using hn3
          rw [hy2, h3, hb3]; rfl
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
        simp only [Bool.not_eq_true] at hn2
        exact ⟨hs1, by rw [hn2]; rfl⟩
    | defnInfo v e hh =>
      obtain ⟨cv, x, rfl, -, -⟩ := denoteCI_defn_inv hc
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k; exact ⟨hs1, rfl⟩
    | thmInfo v =>
      obtain ⟨cv, rfl, -⟩ := denoteCI_thm_inv hc
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k; exact ⟨hs1, rfl⟩
    | indInfo v cap =>
      obtain ⟨cv, d, rfl, -, -⟩ := denoteCI_ind_inv hc
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k; exact ⟨hs1, rfl⟩
    | ctorInfo v nP nF T =>
      obtain ⟨cv, rfl, -⟩ := denoteCI_ctor_inv hc
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k; exact ⟨hs1, rfl⟩
    | recInfo v mI rP kk rs =>
      obtain ⟨cv, Rs, rfl, -, -⟩ := denoteCI_rec_inv hc
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k; exact ⟨hs1, rfl⟩

/-- con-leche: none — an optional table against an optional denoted one: `none` at `none`, a
denoting table at its denotation. -/
@[expose] def OptTbl (st : EStore) (a : Option IProjTable) (x : Option ProjTable) : Prop :=
  (a = none ∧ x = none) ∨ ∃ t pt, a = some t ∧ x = some pt ∧ Frontend.denoteProjTable st t = some pt

/-- con-leche: ConLeche/Cached/Justify.lean:99-103 tableBeqP — **equal handles give con-leche's
`true`**: the same table, read back the same, is equal to itself. -/
theorem tableBeqP_true {st : EStore} {a b : Option IProjTable} {x y : Option ProjTable}
    (ha : OptTbl st a x) (hb : OptTbl st b y) (h : Arena.tableBeqP a b = true) :
    ConLeche.Cached.tableBeqP x y = true := by
  rcases ha with ⟨rfl, rfl⟩ | ⟨t, pt, rfl, rfl, ht⟩ <;>
    rcases hb with ⟨rfl, rfl⟩ | ⟨u, pu, rfl, rfl, hu⟩
  · rfl
  · exact nomatch h
  · exact nomatch h
  · simp only [Arena.tableBeqP, beq_iff_eq] at h
    subst h
    rw [ht] at hu
    obtain rfl := Option.some.inj hu
    simp [ConLeche.Cached.tableBeqP, ConLeche.ProjTable.beqP]

end ConRon.Bridge
