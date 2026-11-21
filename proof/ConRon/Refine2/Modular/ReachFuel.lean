/-
# `ConRon.Refine2.Modular.ReachFuel` — the twin's worklist is monotone in its fuel

**Task #166, Theorem 2.**  A run of the twin's `reachGo` that succeeds with some fuel succeeds,
with the same answer, with more: so the Rust's accept at its own fuel (`u64` lengths plus
`1 <<< 24`) is the twin's at any fuel at least as large.
-/
import ConRon.Arena.Modular.Reach

namespace ConRon.Refine2.Modular

open ConRon.Arena

theorem reachGo_mono (fs : Arena.Frontend.Olean.OleanFs) (pk : Arena.Frontend.Olean.OleanPins)
    (sp : ConLeche.Frontend.Olean.Roots) (env : Modular.ReachEnv) :
    ∀ (n k : Nat) (L : Modular.ReachLog) (c : Modular.ReachCache) (s : AState) r,
      (Modular.reachGo fs pk sp env n L c).run s = .ok r →
      (Modular.reachGo fs pk sp env (n + k) L c).run s = .ok r := by
  intro n
  induction n with
  | zero =>
    intro k L c s r h
    rw [Modular.reachGo.eq_def] at h ⊢
    dsimp only at h ⊢
    cases hs : L.stack with
    | nil =>
      simp only [hs] at h ⊢
      by_cases hp : c.partners.isEmpty = true
      · simp only [hp, ↓reduceIte] at h ⊢; exact h
      · simp only [hp] at h; cases h
    | cons x rest => simp only [hs] at h; cases h
  | succ n ih =>
    intro k L c s r h
    rw [show n + 1 + k = (n + k) + 1 by omega]
    rw [Modular.reachGo.eq_def] at h ⊢
    dsimp only at h ⊢
    cases hs : L.stack with
    | nil =>
      simp only [hs] at h ⊢
      by_cases hp : c.partners.isEmpty = true
      · simp only [hp, ↓reduceIte] at h ⊢; exact h
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [StateT.run_bind] at h ⊢
        cases h1 : (Modular.reachPartners fs pk sp env L c).run s with
        | error e => rw [h1] at h; cases h
        | ok p =>
          rw [h1] at h
          exact ih k _ _ _ r h
    | cons x rest =>
      simp only [hs] at h ⊢
      rw [StateT.run_bind] at h ⊢
      cases h1 : (Modular.reachRead fs pk sp env { L with stack := rest } c x).run s with
      | error e => rw [h1] at h; cases h
      | ok p =>
        rw [h1] at h
        exact ih k _ _ _ r h

end ConRon.Refine2.Modular
