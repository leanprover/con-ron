/-
# `ConRon.Bridge.Frontend.Olean.Covers` — the reader's records cover the closure

con-leche's `readOleansAt_covers` (`Verify/OleanInput.lean`): every constant of the closure's
views (`closureConstants`) is stored by a record the reader emitted.  Upstream proves it from a
`ModelIO` run of its reader (`readOleansAt_entry`, through `readOleansAt_ok`); the twin's reader
is related to upstream's merge and emission piecewise (`Records.lean`'s `readOleans_run`), not to
a run of `readOleansAt`, so the two halves are restated over those pieces:

* `entry_of_loads`: a constant of a view of a module of the closure has its merged copy
  (`EntryStands`), from the closure's order, its loads (`LoadSpec`) and the merge's
  `mergeAll_ok` — `readOleansAt_entry`'s body;
* `covers_of_merge`: from that and upstream's `MergeFacts`, every record of the closure is
  `CoveredBy` the emitted records — `readOleansAt_covers`'s body.
-/
module

public import ConRon.Bridge.Frontend.Olean.Closure
public import ConLeche.Verify.OleanInput

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche
open ConLeche.Frontend.Olean

/-- con-leche: ConLeche/Verify/OleanInput.lean:72 readOleansAt_entry — **a constant of a view
of a module of the closure has its merged copy**, from the closure's order, the loads of its
modules, and the merge of those loads. -/
theorem entry_of_loads {F : FS} {sp : Roots} (hsp : sp.bare = sp) {rootsC : Array Name}
    {orderC : Array Name} {R' : Roots} {lsC : List Loaded} {mgC : Merged}
    (ho : ModelIO.Gives (closureOrder sp rootsC : ModelIO _) F (.ok (orderC, R')))
    (hnames : lsC.map (·.name) = orderC.toList)
    (hloads : ∀ lC ∈ lsC, ∃ i f, (lC.name, i) ∈ orderC.toList.zipIdx ∧
      ModelIO.Gives (readFiles sp lC.name .private : ModelIO _) F (.ok f) ∧ LoadSpec f i lC)
    (hm : mergeAll lsC.toArray = .ok mgC) :
    ∀ {m : Name} {d : ModDecoded} {c : CEntryF Name Expr},
      InClosure sp F rootsC m → ViewOf sp F m d → c ∈ d.constants →
      ∃ e', mgC.map[c.name]? = some e' ∧ EntryStands e' c := by
  obtain ⟨hk1, -, -, -⟩ := mergeAll_ok hm
  intro m d c hcl hv hc
  obtain ⟨_, ho'⟩ := ho.outcome #[]
  obtain ⟨hco, hcr, -, -⟩ := closureOrder_ok hsp ho'
  have hmo := hcl.mem_order hco hcr
  have : m ∈ lsC.map (·.name) := by
    rw [hnames]
    simpa using hmo
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp this
  obtain ⟨i, f, -, hf, r, a, sk, skels, hreg, hsk, hskels, hlazy⟩ := hloads l hl
  obtain ⟨f', hf', hview⟩ := hv
  obtain rfl := readFiles_unique hf.canGive hf'
  obtain ⟨sk', hsk', hspec⟩ := view_parts hreg hview
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨loc, hloc, hcs⟩ := mapM_mem_inv hspec (by simpa using hc)
  obtain ⟨s, hs1, hs2⟩ := constSpec_parts hcs
  obtain ⟨s', hs'mem, hs'⟩ := mapM_mem hskels hloc
  rw [hs1] at hs'
  cases hs'
  obtain ⟨e, he, hent⟩ := hlazy.of_skel _ hs'mem
  obtain ⟨hn, hlp, hty, hth⟩ := lazyEntry_of_spec hs2 hent
  obtain ⟨c', hc', hst⟩ := hk1 l (by simpa using hl) e (by simpa using he)
  rw [hn] at hc'
  refine ⟨c', hc', ?_⟩
  have hecv : e.toCEntryF.cv = c.cv := by
    simp only [CEntryF.cv, hn, hlp, hty]
  by_cases h2c : c.kind.tag = 2
  · -- a theorem: the loaded entry is a theorem, and so is what stands for it
    cases hck : c.kind with
    | thm v all =>
      obtain ⟨-, g, -, -, hek, -, -⟩ := hth v all hck
      refine .inr ⟨?_, ?_, .inl (by rw [hck]; rfl)⟩
      · rcases hst with he' | ⟨n1, t1, l1, -⟩
        · rw [he']; exact hecv
        · simp only [CEntryF.cv] at hecv ⊢
          rw [n1, t1, l1]; exact hecv
      · rcases hst with he' | ⟨-, -, -, k1⟩
        · rw [he', hek]; rfl
        · rw [hek] at k1
          cases hk' : c'.kind <;> rw [hk'] at k1 <;> first | rfl | exact k1.elim
    | _ => rw [hck] at h2c; simp [CKindF.tag] at h2c
  · have hec : e.toCEntryF = c := lazyEntry_eq_of_spec hs2 hent h2c
    rcases hst with rfl | ⟨n1, t1, l1, k1⟩
    · exact .inl hec
    · have hkc : e.kind = c.kind := by rw [← hec]
      rw [hkc] at k1
      cases hck : c.kind with
      | ax u =>
        rw [hck] at k1
        cases hk' : c'.kind with
        | thm v a =>
          rw [hk'] at k1
          obtain ⟨-, rfl⟩ := k1
          refine .inr ⟨?_, by rw [hk']; rfl, .inr hck⟩
          simp only [CEntryF.cv] at hecv ⊢
          rw [n1, t1, l1]; exact hecv
        | ax u' =>
          rw [hk'] at k1
          obtain rfl : u' = u := k1
          refine .inl ?_
          rw [← hec]
          rcases c' with ⟨⟨cn, cl, ct, ck⟩, cu⟩
          rcases e with ⟨⟨en, el, et, ek⟩, eu⟩
          simp only at n1 t1 l1 hk' hkc hck ⊢
          rw [n1, t1, l1, hk', hkc, hck]
        | _ => rw [hk'] at k1; exact k1.elim
      | thm v a => rw [hck] at h2c; exact absurd rfl h2c
      | _ => rw [hck] at k1; cases hk' : c'.kind <;> rw [hk'] at k1 <;> exact k1.elim

/-- con-leche: ConLeche/Verify/OleanInput.lean:593 readOleansAt_covers — **every record of the
closure is stored by a record the reader emitted** (where that record passes the reserved names'
check), from the merge's facts and its entries. -/
theorem covers_of_merge {F : FS} {sp : Roots} {rootsC : Array Name} {mg : Merged}
    {ds : Array Declaration} (hF : MergeFacts mg ds)
    (hentry : ∀ {m : Name} {d : ModDecoded} {c : CEntryF Name Expr},
      InClosure sp F rootsC m → ViewOf sp F m d → c ∈ d.constants →
      ∃ e', mg.map[c.name]? = some e' ∧ EntryStands e' c)
    {r : ConstantInfo} (hr : closureConstants sp F rootsC r) : CoveredBy ds r := by
  obtain ⟨m, hcl, f, d, c, hf, hd, hc, hrc⟩ := hr
  obtain ⟨e', he, hst⟩ := hentry hcl ⟨f, hf, hd⟩ hc
  by_cases ht : c.kind.tag < 5
  · exact covers_entry hF he hst ht hrc
  · have hec : e'.toCEntryF = c := by
      rcases hst with hec | ⟨-, -, hc2⟩
      · exact hec
      · exfalso; apply ht
        rcases hc2 with hc2 | hc2 <;> rw [hc2] <;> decide
    subst hec
    obtain ⟨d', hd', c', hc', hst'⟩ := covers_block hF he (by omega) hrc
    exact ⟨d', hd', fun _ => ⟨c', hc', hst'⟩⟩

end ConRon.Bridge.Frontend.Olean
