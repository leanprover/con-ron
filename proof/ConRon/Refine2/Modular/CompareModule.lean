/-
# `ConRon.Refine2.Modular.CompareModule` — `modular/compare_module.rs`: the challenge's closure

Theorem 2 of `chal_walk`: its accept is the twin's `chalWalk`, through `graph_of_refines`.
-/
import ConRon.Refine2.Modular.Graph
import ConRon.Arena.Modular.CompareModule

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.compare_module

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Frontend.Olean

variable {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier} {sp : frontend.olean.files.Roots}

/-- **`chal_walk`'s accept is `chalWalk`**: the challenge's graph through its lookup. -/
theorem chal_walk_refines (hfs : FsRel inst fsv fs) {st : arena.monad.AState} {lst : AState}
    {c : arena.handle.NIdx} :
    AS pers (fun (_ : Unit) (_ : Unit) => True) st lst
      (chal_walk inst fsv pk pers st.store sp c)
      (Modular.chalWalk fs (absPins pk) (absRoots sp) (absNIdx c)) := by
  intro hrel hinv a s' h
  rw [chal_walk] at h
  peel h as n, hn
  cases nidx_dup2_ok hn
  peel h as roots, hr
  have hrv : roots.val = [c] := by
    simpa using ConRon.Refine.vec_push_val hr
  peel h as ⟨r, ar1⟩, hg
  cases r with
  | Err e => simp at h
  | Ok C =>
    have hs : s' = ar1 := by cases Result.ok_injective h; rfl
    subst hs
    obtain ⟨C', lst', hx, -, hrel', hinv'⟩ := graph_of_refines (cmp := none) hfs hrel hinv C _ hg
    refine ⟨(), lst', ?_, trivial, hrel', hinv'⟩
    rw [hrv] at hx
    simp only [List.map_cons, List.map_nil, absCmp, Option.map_none] at hx
    simp [Modular.chalWalk, hx]

end ConRon.Refine2.Modular
