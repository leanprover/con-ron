/-
# `ConRon.Bridge.Checker.Fold` — THEOREM 1, per declaration

DESIGN.md §8.2's per-declaration statement:

    theorem Arena.checkDecl_bridge
        (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
        (hd : Frontend.denoteDecl s.store pd = some d)
        (hrun : Arena.checkDecl .verified pins fe pd s = .ok (fe', s')) :
        DeclOut pinsP env d s s'

`DeclOut`'s last clause is con-leche's `checkDecl` accepting the denoted record at
`env`, the environment the index `fe` answers for (`IFEnvOK`).  It is the
declaration's own checks — `Arena.checkDeclKind_bridge`, `cases pd` over
`Bridge/Checker/Arms.lean`'s six arms — then the reserved names' check
(`basisNamesOk_run`).  Its consumer is
`Bridge/Checker/Pool.lean`'s `recordSpec`: a record's job at its view of the stream's
index.
-/
module

import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Frontend.Rel
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

/-! ## THE PER-DECLARATION BRIDGE -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind
**A declaration's own checks.**  One `cases` over `Bridge/Checker/Arms.lean`'s
six arms; the arms are where the content is. -/
theorem Arena.checkDeclKind_bridge
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.checkDeclKind .verified pins fe pd s = .ok (fe', s')) :
    DeclKindOut pinsP env d s s' := by
  cases pd with
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact checkDeclKind_bridge_axiom hk hok hpins hcv hrun
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact checkDeclKind_bridge_quot hok hcv hrun
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    exact checkDeclKind_bridge_ind hind hok hb hrun
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
        exact checkDeclKind_bridge_defn hk hok hpins hcv he hrun
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
        exact checkDeclKind_bridge_thm hk hok hcv he hrun
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
        exact checkDeclKind_bridge_opaque hk hok hcv he hrun

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:166-174 checkDecl
con-leche: ConLeche/Verify/Cached/BridgeC.lean:281 checkDeclStepC_run
**DESIGN §8.2's Theorem 1, per declaration.**  The declaration's own checks
(`Arena.checkDeclKind_bridge`), then, past the flush, the reserved names' check
(`basisNamesOk_run`, at the empty readback memo the flush leaves).

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
  simp only [Arena.checkDecl] at hrun
  obtain ⟨fe₂, s1, h1, h2⟩ := AM.bind_ok hrun
  have o1 := Arena.checkDeclKind_bridge hk hind hok hpins hd h1
  obtain ⟨u, s2, h3, h4⟩ := AM.bind_ok h2
  have e3 : flushCaches s1 = .ok ((), { s1 with caches := Caches.empty }) := rfl
  rw [e3] at h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h3)
  obtain ⟨b, s3, h5, h6⟩ := AM.bind_ok h4
  have hrd : ReadOK { s1 with caches := Caches.empty } :=
    ⟨by intro k x hk; simp [Caches.empty] at hk, by intro k x hk; simp [Caches.empty] at hk,
      by intro k x hk; simp [Caches.empty] at hk⟩
  have hst2 : StateOK { s1 with caches := Caches.empty } := ⟨o1.state.wf⟩
  have hp2 : PinsOK { s1 with caches := Caches.empty } :=
    hok.check.pins.mono o1.ext o1.pins
  obtain ⟨hs3, hb⟩ := basisNamesOk_run hst2 hrd hp2 (Frontend.denoteDecl_ext o1.ext hd) h5
  rcases AM.ite_ok h6 with ⟨hy, k⟩ | ⟨-, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    obtain ⟨env', F, hF⟩ := o1.run
    refine ⟨hs3.ok, o1.ext.trans hs3.ext, by rw [hs3.pins]; exact o1.pins, env', F, ?_⟩
    have hbn : ConLeche.basisNamesOk d = true := by rw [← hb]; exact hy
    simp only [ConLeche.checkDecl, hF, hbn, bind, Except.bind, pure, Except.pure]
    simp
  · exact absurd k (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

end ConRon.Bridge
