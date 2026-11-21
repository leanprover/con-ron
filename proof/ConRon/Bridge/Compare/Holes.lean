/-
# `ConRon.Bridge.Compare.Holes` — an `--olean` challenge's theorem holes

`Arena/Frontend/Compare.lean`'s `holeRecord` against con-leche's (`ConLeche/Driver/Compare.lean`):
a theorem whose file says its value uses `sorryAx` (the read's used constants, `usedOf`, related
by `Bridge/Frontend/Prepare.lean`'s `UsedRel`) and whose name is no built-in axiom's is the axiom
of its statement.  `holeRecordsGo_run`: the twin's records denote con-leche's `holeRecord` of
each denoted record.  Run style, as `Compare/Side.lean`.
-/
module

public import ConRon.Bridge.Compare.Side
public import ConRon.Bridge.Frontend.Prepare
public import ConRon.Arena.Frontend.Compare
public import ConLeche.Driver.Compare
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Frontend.Rel

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge.Frontend

/-- con-leche: ConLeche/Driver/Compare.lean:63-70 holeRecord — **THEOREM 1 for `holeRecord`**:
the twin's record denotes con-leche's `holeRecord` of the denoted one at the read's used
constants, persistently if the record is. -/
theorem holeRecord_run {st0 : EStore} {used : IDeclaration → AM (Array NIdx)}
    {usedC : Declaration → Array ConLeche.Name} (hU : UsedRel st0 used usedC)
    {d : IDeclaration} {dP : Declaration} {s s' : AState} {r : IDeclaration}
    (hx0 : Ext st0 s.store) (hok : StateOK s) (hoff : s.store.scratchOn = false)
    (hp : PinsOK s) (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    (hrun : ConRon.Arena.Frontend.holeRecord used d s = .ok (r, s')) :
    ParseStep s s' ∧
      ConRon.Arena.Frontend.denoteDecl s'.store r = some (ConLeche.Driver.holeRecord usedC dP) ∧
      (PersDecl d → PersDecl r) := by
  cases d with
  | thmDecl cv v =>
    have hd' := hd
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    split at hd
    · next c e hc he =>
      obtain rfl := Option.some.inj hd
      have hn := (denoteCV_inv hc).1
      simp only [ConRon.Arena.Frontend.holeRecord] at hrun
      obtain ⟨b, s₁, h1, k1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hb⟩ := builtinAxiomName_run hok hp hn h1
      rcases AM.ite_ok k1 with ⟨hy, k⟩ | ⟨hn1, k⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
        refine ⟨ParseStep.refl hok, ?_, id⟩
        have hb' : ConLeche.Cached.builtinAxiomName c.name = true := by rw [← hb]; simpa using hy
        simp [ConLeche.Driver.holeRecord, hb', hd']
      · obtain ⟨us, s₂, h2, k2⟩ := AM.bind_ok k
        obtain ⟨hst2, hus⟩ := hU hx0 hok hoff hd' h2
        obtain ⟨sa, s₃, h3, k3⟩ := AM.bind_ok k2
        obtain ⟨rfl, hsa⟩ := pinAt_run (hp.mono hst2.ext hst2.pins) pinNames_eq_sorryAxName h3
        have hcont : us.contains sa = (usedC (.thmDecl c e)).contains ConLeche.sorryAxName := by
          have := denoteNList_contains hst2.ok.wf _ _ hus _ _ hsa
          simpa using this
        have hb' : ConLeche.Cached.builtinAxiomName c.name = false := by
          rw [← hb]; simpa using hn1
        have hc₂ := denoteCV_ext hc hst2.ext
        rcases AM.ite_ok k3 with ⟨hy3, k⟩ | ⟨hn3, k⟩
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
          have h3' : (usedC (.thmDecl c e)).contains ConLeche.sorryAxName = true := by
            rw [← hcont]; simpa using hy3
          refine ⟨hst2, ?_, fun h => h.1⟩
          simp only [ConLeche.Driver.holeRecord, hb', h3', Bool.not_false, Bool.and_self,
            ↓reduceIte, ConRon.Arena.Frontend.denoteDecl, hc₂, Option.map_some]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
          have h3' : (usedC (.thmDecl c e)).contains ConLeche.sorryAxName = false := by
            rw [← hcont]; simpa using hn3
          refine ⟨hst2, ?_, id⟩
          simp only [ConLeche.Driver.holeRecord, hb', h3', Bool.not_false, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte]
          exact ConRon.Bridge.Frontend.denoteDecl_ext hst2.ext hd'
    · exact nomatch hd
  | axiomDecl cv | defnDecl cv v hh | opaqueDecl cv v | indDecl cv v | quotDecl v cv =>
    simp only [ConRon.Arena.Frontend.holeRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨ParseStep.refl hok, ?_, id⟩
    rw [hd]
    cases dP <;> first
      | rfl
      | (exfalso; simp only [ConRon.Arena.Frontend.denoteDecl] at hd
         first
           | (obtain ⟨_, -, h⟩ := Option.map_eq_some_iff.mp hd; exact nomatch h)
           | (split at hd <;> simp_all))

/-- con-leche: ConLeche/Driver/Compare.lean:132-138 chalRecords — **THEOREM 1 for the theorem
holes**: the twin's records, onto `out`, denote con-leche's `holeRecord` of each denoted record,
onto `out`'s denotation; persistent records stay persistent. -/
theorem holeRecordsGo_run {st0 : EStore} {used : IDeclaration → AM (Array NIdx)}
    {usedC : Declaration → Array ConLeche.Name} (hU : UsedRel st0 used usedC) :
    ∀ (ds out r : List IDeclaration) (dsP outP : List Declaration) {s s' : AState},
      Ext st0 s.store → StateOK s → s.store.scratchOn = false → PinsOK s →
      denoteDecls s.store out = some outP → denoteDecls s.store ds = some dsP →
      ConRon.Arena.Frontend.holeRecordsGo used out ds s = .ok (r, s') →
      ParseStep s s' ∧
        denoteDecls s'.store r = some (outP ++ dsP.map (ConLeche.Driver.holeRecord usedC)) ∧
        ((∀ x ∈ out, PersDecl x) → (∀ x ∈ ds, PersDecl x) → ∀ x ∈ r, PersDecl x) := by
  intro ds
  induction ds with
  | nil =>
    intro out r dsP outP s s' _ hok _ _ hout hds hrun
    simp only [denoteDecls, Option.some.injEq] at hds
    subst hds
    simp only [ConRon.Arena.Frontend.holeRecordsGo] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨ParseStep.refl hok, by simpa using hout, fun h _ => h⟩
  | cons d ds ih =>
    intro out r dsP outP s s' hx0 hok hoff hp hout hds hrun
    simp only [denoteDecls] at hds
    split at hds
    · next x xs hx hxs =>
      obtain rfl := Option.some.inj hds
      simp only [ConRon.Arena.Frontend.holeRecordsGo] at hrun
      obtain ⟨d', s₁, h1, k1⟩ := AM.bind_ok hrun
      obtain ⟨hst1, hd', hpd'⟩ := holeRecord_run hU hx0 hok hoff hp hx h1
      have hout' : denoteDecls s₁.store (out ++ [d']) =
          some (outP ++ [ConLeche.Driver.holeRecord usedC x]) :=
        Frontend.denoteDecls_append (denoteDecls_ext hst1.ext _ _ hout)
          (by simp [denoteDecls, hd'])
      obtain ⟨hst2, hr, hpr⟩ := ih (out ++ [d']) r xs _ (hx0.trans hst1.ext) hst1.ok
        (by rw [hst1.scratch]; exact hoff) (hp.mono hst1.ext hst1.pins) hout'
        (denoteDecls_ext hst1.ext _ _ hxs) k1
      refine ⟨hst1.trans hst2, by simpa using hr, fun ho hd x hxr => hpr (fun y hy => ?_)
        (fun y hy => hd y (List.mem_cons_of_mem _ hy)) x hxr⟩
      rcases List.mem_append.mp hy with hy | hy
      · exact ho y hy
      · rw [List.mem_singleton] at hy; subst hy
        exact hpd' (hd d List.mem_cons_self)
    · exact nomatch hds

end ConRon.Bridge
