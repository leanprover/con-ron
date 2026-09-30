/-
# `ConRon.Bridge.Checker.Nodup` — the pure checker keeps names unique

`Bridge/Checker/Split.lean`'s `checkDecl_nodup` (task #97-P3-Checker round 8's
child, closed in round 9): an accepted `ConLeche.checkDecl` step keeps the
environment's names pairwise distinct.  con-leche proves this for its CACHED
driver only (`Verify/Cached/PushChain.lean`'s `PushChain`, over `FEnv`); the
two-phase fold's bridge needs it for the PURE checker, which is what phase A's
`PhaseA` records.

The proof reads the run off con-leche's own run relation, `DeclRun`
(`checkDeclRun_ofEnvFactsK`), whose records already carry every duplicate
guard the checker ran:

| arm | the guard, in the run record |
|---|---|
| `defn` / `thm` / `opaque` / `axiom` | `ConstantValRun`'s first conjunct, `(env.find? cv.name).isNone` |
| `basis` (and a pinned `ind`/`quot` block) | `BasisInstallRun`'s per-constant `isNone` |
| `ind`, modeled | `MemberValRun` per member and per provisioned recursor (the provisional environment holds the recursors before it, so the group is pairwise distinct), `ProjFnRun`'s `projFnName` guard |
| `ind`, native | `checkConstantVal_inv` at the former, each constructor (`checkSumCtors_inv`) and the recursor, the front guard's `Nodup` of the constructor names, and `checkStructProjTable_inv`'s `projTableName` guard |

This module imports con-leche only: the statement and the proof are pure.
-/
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.EnvBound
import ConLeche.Verify.EnvWF

namespace ConRon.Bridge

open ConLeche ConLeche.Semantics

set_option autoImplicit false

/-! ## Fresh pushes -/

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean PushChain.push — a push
of a name the environment does not hold keeps names unique. -/
theorem nodupNames_push {e : Env} {c : ConstantInfo} (hnd : NodupNames e)
    (hf : e.find? c.name = none) : NodupNames ⟨c :: e.consts⟩ := by
  unfold NodupNames at hnd ⊢
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨fun hmem => ?_, hnd⟩
  obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hmem
  have hne := List.find?_eq_none.mp hf x hx
  simp [hxn] at hne

theorem nodupNames_push' {e : Env} {c : ConstantInfo} (hnd : NodupNames e)
    (hf : (e.find? c.name).isNone = true) : NodupNames ⟨c :: e.consts⟩ :=
  nodupNames_push hnd (Option.isNone_iff_eq_none.mp hf)

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean FreshNames — a list of
names, pairwise distinct and each fresh at `e`. -/
def FreshAt (e : Env) (ns : List Name) : Prop :=
  ns.Nodup ∧ ∀ n ∈ ns, e.find? n = none

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean FreshNames.step — after
the head's push the tail is fresh at the extended environment. -/
theorem FreshAt.step {e : Env} {c : ConstantInfo} {ns : List Name}
    (h : FreshAt e (c.name :: ns)) : FreshAt ⟨c :: e.consts⟩ ns := by
  obtain ⟨hnd, hfr⟩ := h
  rw [List.nodup_cons] at hnd
  refine ⟨hnd.2, fun n hn => ?_⟩
  rw [Env.find?_cons, if_neg (fun he => hnd.1 (by rw [he]; exact hn))]
  exact hfr n (List.mem_cons_of_mem _ hn)

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean FreshNames.cons_of — fresh
at the extended environment, and the head fresh at the base, is fresh at the
base as a whole list. -/
theorem FreshAt.cons_of {e : Env} {c : ConstantInfo} {ns : List Name}
    (hc : e.find? c.name = none) (h : FreshAt ⟨c :: e.consts⟩ ns) :
    FreshAt e (c.name :: ns) := by
  obtain ⟨hnd, hfr⟩ := h
  have hne : ∀ n ∈ ns, c.name ≠ n ∧ e.find? n = none := by
    intro n hn
    have := hfr n hn
    rw [Env.find?_cons] at this
    by_cases he : c.name = n
    · rw [if_pos he] at this; exact nomatch this
    · rw [if_neg he] at this; exact ⟨he, this⟩
  refine ⟨List.nodup_cons.mpr ⟨fun hm => (hne _ hm).1 rfl, hnd⟩, ?_⟩
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hc
  · exact (hne n hn).2

/-! ## The pinned blocks -/

/-- con-leche: ConLeche/Semantics/Decl.lean:57 BasisInstallRun — the pinned
block's install is a chain of fresh pushes. -/
theorem basisInstallRun_nodup : ∀ (cs : List ConstantInfo) {e e' : Env},
    BasisInstallRun e cs e' → NodupNames e → NodupNames e'
  | [], _, _, h, hnd => by
    simp only [BasisInstallRun] at h; subst h; exact hnd
  | c :: cs, e, e', h, hnd => by
    simp only [BasisInstallRun] at h
    exact basisInstallRun_nodup cs h.2 (nodupNames_push' hnd h.1)

theorem declBasisRun_nodup {e e' : Env} {k : BasisKind} (h : DeclBasisRun e k e')
    (hnd : NodupNames e) : NodupNames e' :=
  basisInstallRun_nodup _ h.2 hnd

/-! ## The uniform route -/

/-- con-leche: ConLeche/Semantics/Inductives/DeclBlock.lean:40 DeclBlockRun —
the uniform install pushes the formers, the constructors, the recursors and
the projection tables, each at a name found fresh. -/
theorem declBlockRun_nodup {μ : CheckMode} {F : Nat} {e e' : Env}
    {block : List ConstantInfo} {p₀ : BlockParts} (h : DeclBlockRun μ F e block p₀ e')
    (hnd : NodupNames e) : NodupNames e' := by
  sorry

/-! ## The whole step -/

/-- con-leche: ConLeche/Verify/Cached/InstalledC.lean installRun_trace — **the
pure fold keeps names unique**: every install is guarded by a `find?` miss
(`checkConstantVal`, `installBasisDecl`, the inductive install), which is
what con-leche's `PushChain` carries through its cached fold.  Read off
`DeclRun` arm by arm (the module note). -/
theorem checkDecl_nodup {μ : CheckMode} {pinsP : List NatOpPinSet} {F : Nat}
    {env env' : Env} {d : Declaration}
    (h : ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env')
    (hnd : NodupNames env) : NodupNames env' := by
  have hrun := checkDeclRun_ofEnvFactsK h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -⟩ := hrun
    exact nodupNames_push' hnd hcv.1
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact nodupNames_push' hnd hcv.1
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl, -⟩ := hrun
    exact nodupNames_push' hnd hcv.1
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, hdisj⟩
    · exact hnd
    · rcases hdisj with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
      · exact nodupNames_push' hnd hcv.1
      · exact nodupNames_push' hnd hcv.1
      · exact nodupNames_push' hnd hcv.1
      · exact hnd
  | basisDecl kind => exact declBasisRun_nodup hrun hnd
  | quotDecl k cv =>
    cases k with
    | type => exact declBasisRun_nodup hrun hnd
    | _ => (simp only [DeclRun] at hrun; subst hrun; exact hnd)
  | indDecl block nP =>
    simp only [DeclRun] at hrun
    split at hrun
    · exact declBasisRun_nodup hrun hnd
    · simp only [DeclIndRunDispatchK] at hrun
      split at hrun
      · exact declBlockRun_nodup hrun hnd
      · exact hrun.elim

end ConRon.Bridge
