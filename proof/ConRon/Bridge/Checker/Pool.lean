/-
# `ConRon.Bridge.Checker.Pool` — THEOREM 1 at the check phase the driver runs

`Arena.PooledAccepts` is the binary's check phase on the twin side: the stream's index built
from the driver's state, then job lists, one per worker, each increasing, together covering the
records, each accepted from the driver's state's worker.  `Arena.pooledAccepts_bridge`: con-leche's
pure fold `checkDeclsPure` accepts the denoted stream, at the environment the records denote.

The assembly, one theorem per step:

| step | theorem |
|---|---|
| the index denotes con-leche's | `Bridge/Checker/Index.lean`'s `buildIndex_run` (with `constsSpec`, `tablesSpec`) |
| every job passing is the fold | `Bridge/Checker/Pooled.lean`'s `pooled_fold` |
| a record's check is the fold's step | `recordSpec`: `Arena.checkDecl_bridge` and the `And` pin's frame |
| the step pushes what the record says | `Bridge/Checker/Pushes.lean`'s `checkDecl_pushes`, `checkDecl_fresh` |

`Arena.pooledOleanAccepts_bridge` is the same on an `--olean` run (`Arena.PooledOleanAccepts`):
the fold accepts the FILLED stream, every theorem's reference replaced by the value its job
reads (`Bridge/Checker/PooledOleans.lean`'s `pooled_fold_oleans`).
-/
module

public import ConRon.Bridge.Checker.Pooled
public import ConRon.Bridge.Checker.PooledOleans
public import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Fold
public import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Pushes
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Frontend.Rel

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

universe w

/-- con-leche: ConLeche/Verify/Cached/DeclPushes.lean:723 checkDeclStepC_pushes — the pure
kernel's pushes and freshness, as `Pooled.lean` takes them. -/
theorem kernelPushes (pinsP : List NatOpPinSet) : KernelPushes pinsP :=
  fun h => ⟨checkDecl_pushes h, checkDecl_fresh h⟩

/-- con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob — **a record's check at its view
is con-leche's step**: the `And` pin moves the store and nothing the check reads
(`andPinOk_run`), then the per-declaration bridge. -/
theorem recordSpec {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec) : RecordSpec pins pinsP := by
  intro env I k pd d s s' hok hpins hd hrun
  simp only [recordCheck] at hrun
  obtain ⟨b, s₁, ha, k1⟩ := AM.bind_ok hrun
  obtain ⟨hst₁, hx₁, hc₁, hp₁⟩ := andPinOk_run hok.check.state hok.check.pins hd ha
  rcases AM.ite_ok k1 with ⟨-, k2⟩ | ⟨-, k2⟩
  · obtain ⟨fe', s₂, hc, k3⟩ := AM.bind_ok k2
    obtain ⟨-, rfl⟩ := AM.pure_ok k3
    have hok₁ : FoldOK env (I.view k) s₁ := hok.step (hok.check.mono hst₁ hx₁ hc₁ hp₁) hp₁
    have hd₁ := Frontend.denoteDecl_ext hx₁ hd
    have hpins₁ := PinsDenote.mono hx₁ pins pinsP hpins
    obtain ⟨hst₂, hx₂, hp₂, hrun₂⟩ := Arena.checkDecl_bridge hk hind hok₁ hpins₁ hd₁ hc
    exact ⟨hst₂, hx₁.trans hx₂, hp₂.trans hp₁, hrun₂⟩
  · exact absurd k2 (AM.Never.fail _ _ _ _)

/-- con-leche: none — a stream's denotation, record by record. -/
theorem denoteDecls_getElem {st : EStore} :
    ∀ {ds : List IDeclaration} {dsP : List Declaration}, denoteDecls st ds = some dsP →
      dsP.length = ds.length ∧ ∀ (i : Nat) (hi : i < ds.length), ∃ hi' : i < dsP.length,
        Frontend.denoteDecl st ds[i] = some dsP[i]
  | [], dsP, h => by
    simp only [denoteDecls, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | d :: ds, dsP, h => by
    simp only [denoteDecls] at h
    cases h1 : Frontend.denoteDecl st d with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : denoteDecls st ds with
      | none => rw [h1, h2] at h; simp at h
      | some xs =>
        rw [h1, h2] at h
        obtain rfl := Option.some.inj h.symm
        obtain ⟨hl, hi⟩ := denoteDecls_getElem h2
        refine ⟨by simp [hl], fun i hi' => ?_⟩
        cases i with
        | zero => exact ⟨by simp, h1⟩
        | succ j =>
          obtain ⟨hj, hj'⟩ := hi j (by simpa using hi')
          exact ⟨by simpa using hj, hj'⟩

/-- con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool
con-leche: ConLeche/Verify/Cached/StreamIndex.lean:488 checkDecls_of_jobs — **THEOREM 1 at the
check phase the driver runs**: from an accepting `Arena.PooledAccepts`, con-leche's pure fold
`checkDeclsPure` accepts the denoted stream, at the environment its records denote.  The set
theory supplies the well-formedness of each prefix's environment, as in con-leche's own
`declsRun_model`. -/
theorem Arena.pooledAccepts_bridge (V : Type w) [ConLeche.SetTheory V]
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {s s' : AState} {I : IStreamIndex}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hst : DriverOK s) (hoff : s.store.scratchOn = false)
    (hpersPins : PersPins s) (hpp : PersPinSets pins) (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x) (hden : denoteDecls s.store ds.toList = some dsP)
    (hrun : Arena.PooledAccepts .verified pins ds s I s') :
    ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
      = .ok (ConLeche.Cached.streamEnv dsP) := by
  obtain ⟨parts, hidx, hcov, -, hinc, hacc⟩ := hrun
  obtain ⟨hst', hx, hp', -, hI, hpI⟩ := buildIndex_run constsSpec tablesSpec hst hoff hpd hden hidx
  have hx' := PExt.of_ext hx
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
  have hden' : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s'.store ds[i] = some dsP[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨hi', Frontend.denoteDecl_ext hx (by simpa using h)⟩
  exact pooled_fold_records V (recordSpec hk hind) (kernelPushes pinsP) hpp hst'.state
    (hst.pins.pmono hpersPins hx' hp') (hpersPins.mono hp') (PinsDenote.mono hx pins pinsP hpins)
    hpd (by simpa using hlen) hden' hI hpI parts hcov hinc hacc

open ConRon.Arena.Frontend.Olean (OleanPins ModRef) in
/-- con-leche: ConLeche/Driver/CheckMain.lean:152-170 checkOleansG
con-leche: ConLeche/Verify/Cached/StreamIndex.lean:488 checkDecls_of_jobs — **THEOREM 1 at the
check phase of an `--olean` run**: from an accepting `Arena.PooledOleanAccepts` on a snapshot
`F`, con-leche's pure fold accepts the filled stream (`fillStream`: each theorem's reference
replaced by the snapshot's value there), at the environment it denotes.  The reader's module
references and pins are related at an earlier state `s₀` (the read's), which the driver's
persistently extends. -/
theorem Arena.pooledOleanAccepts_bridge (V : Type w) [ConLeche.SetTheory V]
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {s₀ s s' : AState} {I : IStreamIndex}
    {F : FS} {pk : OleanPins} {sp : ConLeche.Frontend.Olean.SearchPath}
    {values : Array ModRef} {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hst : DriverOK s) (hoff : s.store.scratchOn = false)
    (hpersPins : PersPins s) (hpp : PersPinSets pins) (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x) (hden : denoteDecls s.store ds.toList = some dsP)
    (hwf₀ : StoreWF s₀.store) (hoff₀ : s₀.store.scratchOn = false) (hx₀ : PExt s₀.store s.store)
    (hv₀ : Frontend.Olean.ValuesRel sp F s₀.store values valuesP)
    (hnu₀ : Frontend.Olean.NullsRel s₀.store pk)
    (hrun : Arena.PooledOleanAccepts (Frontend.Olean.modelFs F) pk sp values .verified pins ds s
      I s') :
    ∃ Fu, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified Fu) pinsP
      (fillStream sp F valuesP dsP) =
        .ok (ConLeche.Cached.streamEnv (fillStream sp F valuesP dsP)) := by
  obtain ⟨parts, hidx, hcov, -, hinc, hacc⟩ := hrun
  obtain ⟨hst', hx, hp', -, hI, hpI⟩ := buildIndex_run constsSpec tablesSpec hst hoff hpd hden hidx
  have hx' := PExt.of_ext hx
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
  have hden' : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s'.store ds[i] = some dsP[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨hi', Frontend.denoteDecl_ext hx (by simpa using h)⟩
  exact pooled_fold_oleans V (recordSpec hk hind) (kernelPushes pinsP) hpp hst'.state
    (hst.pins.pmono hpersPins hx' hp') (hpersPins.mono hp') (PinsDenote.mono hx pins pinsP hpins)
    hpd (by simpa using hlen) hden' hI hpI hwf₀ hoff₀ (hx₀.trans hx') hv₀ hnu₀ parts hcov hinc
    hacc

end ConRon.Bridge
