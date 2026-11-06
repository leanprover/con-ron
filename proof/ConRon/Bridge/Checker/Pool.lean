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
-/
module

public import ConRon.Bridge.Checker.Pooled
public import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Checker.Pushes
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Install

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
  simp only [recordCheck, Bind.bind, StateT.bind, Except.bind] at hrun
  cases ha : andPinOk pd s with
  | error e => rw [ha] at hrun; exact nomatch hrun
  | ok r =>
    obtain ⟨b, s₁⟩ := r
    rw [ha] at hrun
    obtain ⟨hst₁, hx₁, hc₁, hp₁⟩ := andPinOk_run hok.check.state hok.check.pins hd ha
    cases b with
    | false => simp [fail] at hrun
    | true =>
      simp only [↓reduceIte] at hrun
      cases hc : Arena.checkDecl .verified pins (I.view k) pd s₁ with
      | error e => rw [hc] at hrun; exact nomatch hrun
      | ok q =>
        obtain ⟨fe', s₂⟩ := q
        rw [hc] at hrun
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨-, rfl⟩ := hrun
        have hok₁ : FoldOK env (I.view k) s₁ :=
          hok.step (hok.check.mono hst₁ hx₁ hc₁ hp₁) hp₁
        have hd₁ := denoteDecl_ext hx₁ hd
        have hpins₁ := PinsDenote.mono hx₁ pins pinsP hpins
        obtain ⟨hst₂, hx₂, hp₂, hrun₂⟩ := Arena.checkDecl_bridge hk hind hok₁ hpins₁ hd₁ hc
        exact ⟨hst₂, hx₁.trans hx₂, hp₂.trans hp₁, hrun₂⟩

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
    exact ⟨hi', denoteDecl_ext hx (by simpa using h)⟩
  exact pooled_fold_records V (recordSpec hk hind) (kernelPushes pinsP) hpp hst'.state
    (hst.pins.pmono hpersPins hx' hp') (hpersPins.mono hp') (PinsDenote.mono hx pins pinsP hpins)
    hpd (by simpa using hlen) hden' hI hpI parts hcov hinc hacc

end ConRon.Bridge
