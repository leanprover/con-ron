/-
# `ConRon.Bridge.Checker.Fold` — THEOREM 1, per declaration

DESIGN.md §8.2's per-declaration statement:

    theorem Arena.checkDecl_bridge
        (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
        (hd : Frontend.denoteDecl s.store pd = some d)
        (hrun : Arena.checkDecl .verified pins fe pd s = .ok (fe', s')) :
        DeclOut pinsP env d s s'

`DeclOut`'s last clause is con-leche's `checkDecl` accepting the denoted record at
`env`, the environment the index `fe` answers for (`IFEnvOK`).  It is `cases pd`
over `Bridge/Checker/Arms.lean`'s six arms.  Its consumer is
`Bridge/Checker/Pool.lean`'s `recordSpec`: a record's job at its view of the stream's
index.
-/
module

import ConRon.Bridge.Checker.Arms
public import ConRon.Bridge.Checker.Decl
public import ConRon.Bridge.Checker.Hyp

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## Running an `AM` do-block

Three `rfl` equations; the bind's inversion (`AM.bind_ok`) lives in
`Bridge/Pers.lean`, because `Bridge/Checker/Base.lean` needs it too
and sits below this module.  After them no proof in this module mentions
`StateT`. -/

/-- con-leche: none — `flushCaches` as an equation. -/
theorem flushCaches_run (s : AState) :
    flushCaches s = .ok ((), { s with caches := Caches.empty }) := rfl

/-- con-leche: none — `enterScratch` as an equation. -/
theorem enterScratch_run (s : AState) :
    enterScratch s = .ok ((),
      { store := s.store.enableScratch, memos := Memos.empty,
        caches := s.caches, pins := s.pins }) := rfl

/-- con-leche: none — `dropScratch` as an equation. -/
theorem dropScratch_run (s : AState) :
    dropScratch s = .ok ((),
      { store := s.store.dropScratch, memos := s.memos,
        caches := Caches.empty, pins := s.pins }) := rfl

/-! ## THE PER-DECLARATION BRIDGE -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:43-185 checkDecl
con-leche: ConLeche/Verify/Cached/BridgeC.lean:281 checkDeclStepC_run
**DESIGN §8.2's Theorem 1, per declaration.**  One `cases` over
`Bridge/Checker/Arms.lean`'s six arms; the arms are where the content is.

`Ext` and not `PExt`: `checkDecl` runs inside a job's bracket and drops nothing,
so the total extension holds here; the job's `dropScratch` weakens it one level
up (`Bridge/Checker/Pooled.lean`'s `job_spec`). -/
theorem Arena.checkDecl_bridge
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.checkDecl .verified pins fe pd s = .ok (fe', s')) :
    DeclOut pinsP env d s s' := by
  cases pd with
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact checkDecl_bridge_axiom hk hok hpins hcv hrun
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact checkDecl_bridge_quot hok hcv hrun
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    exact checkDecl_bridge_ind hind hok hb hrun
  | defnDecl v e hint =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact checkDecl_bridge_defn hk hok hpins hcv he hrun
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact checkDecl_bridge_thm hk hok hcv he hrun
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact checkDecl_bridge_opaque hk hok hcv he hrun

end ConRon.Bridge
