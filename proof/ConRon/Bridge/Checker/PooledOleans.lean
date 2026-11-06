/-
# `ConRon.Bridge.Checker.PooledOleans` — the check phase of an `--olean` run

An `--olean` read leaves a theorem's value in its file: the record holds a reference
(`.thmDecl cv (.bvar code)`), and the theorem's job reads the value into its own scratch tier
(`Arena/OleanJobs.lean`'s `oleanJob`), checks the record with it in place and drops it with the
tier.  `pooled_fold_oleans`: every such job passing is an accept of con-leche's pure fold of the
FILLED stream `dsF`, the records with every reference replaced by the value the job reads.

The index is built from the records with their references (`IndexDenotes … (buildIndex dsP)`);
what a record installs does not read a theorem's value (upstream's `declConstants_fillDecl`), so
that index is the filled stream's (`buildIndex_congr`).  A job is `Pooled.lean`'s step with the
value read in between (`ValueSpec`, the reader's walk); every other record's job is `recordJob`.
-/
module

public import ConRon.Bridge.Checker.Pooled
public import ConRon.Arena.OleanJobs

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena
open ConRon.Arena.Frontend.Olean (OleanFs OleanPins ModRef ValueCache readValue)

universe w

/-! ## The index does not read a value -/

/-- con-leche: ConLeche/Verify/Cached/Fill.lean:27 declConstants_fillDecl — **two streams whose
records install the same have the same index**. -/
theorem buildIndex_congr {dsF dsP : List Declaration}
    (h : dsF.map (fun d => (ConLeche.declConstants d, ConLeche.declTables d)) =
      dsP.map (fun d => (ConLeche.declConstants d, ConLeche.declTables d))) :
    ConLeche.Cached.buildIndex dsF.toArray = ConLeche.Cached.buildIndex dsP.toArray := by
  simp only [ConLeche.Cached.buildIndex, List.foldl_toArray']
  suffices ∀ (a b : List Declaration) (J : ConLeche.Cached.StreamIndex),
      a.map (fun d => (ConLeche.declConstants d, ConLeche.declTables d)) =
        b.map (fun d => (ConLeche.declConstants d, ConLeche.declTables d)) →
      a.foldl ConLeche.Cached.StreamIndex.add J = b.foldl ConLeche.Cached.StreamIndex.add J from
    this dsF dsP {} h
  intro a
  induction a with
  | nil => intro b J h; cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x a ih =>
    intro b J h
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hc, ht⟩, hrest⟩ := h
      simp only [List.foldl_cons]
      have : J.add x = J.add y := by
        simp only [ConLeche.Cached.StreamIndex.add, hc, ht]
      rw [this]
      exact ih b _ hrest

end ConRon.Bridge
