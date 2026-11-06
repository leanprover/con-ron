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
public import ConRon.Bridge.Frontend.Olean.Value
import ConRon.Bridge.Frontend.Rel

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena
open ConRon.Arena.Frontend.Olean (OleanFs OleanPins ModRef ValueCache readValue)

universe w

/-! ## A reference is a `bvar`

`oleanJob` reads a theorem's value as a reference exactly when its handle is a `bvar` (the tag
test, then `viewBVar`); at a denoting handle that is exactly when the value denotes a `bvar`. -/

/-- con-leche: none — a `bvar` view is the `bvar` projection's answer. -/
theorem viewBVar_of_view {st : EStore} {i : EIdx} {k : Nat} (h : st.view i = some (.bvar k)) :
    st.viewBVar i = some k := by
  have htg : i.tag = ETag.bvar := by
    have := EStore.tagOf_of_view h; simpa [ENodeView.tagOf] using this
  rw [EStore.view_eq_tier] at h
  simp only [EStore.viewBVar, EStore.persGetBVar]
  have key : ∀ t : ETables, t.get i = some (.bvar k) → t.getBVar i = some k := by
    intro t ht
    simp only [ETables.get, htg, beq_self_eq_true, ↓reduceIte, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, hk⟩ := ht
    simp only [ENodeView.bvar.injEq] at hk
    simp [ETables.getBVar, hr, hk]
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h ⊢; exact key _ h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h ⊢; exact key _ h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

/-- con-leche: none — **the job's reference test is the denotation's `bvar`**. -/
theorem refTest_iff {st : EStore} (hwf : StoreWF st) {v : EIdx} {x : Expr}
    (hv : denoteE st v = some x) (code : Nat) :
    (if v.tag == ETag.bvar then st.viewBVar v else none) = some code ↔ x = .bvar code := by
  constructor
  · intro h
    split at h
    · rename_i htg
      have hview := view_of_viewBVar (by simpa using htg) h
      exact denote_bvar_inv hwf hview hv
    · cases h
  · intro hx
    subst hx
    have htag : v.tag = ETag.bvar := by
      have h := denote_tag hwf v
      rw [hv] at h
      have := h.some
      simp [exprTag] at this
      exact this.symm
    obtain ⟨w, hw⟩ := denoteE_view hv
    have hwt := EStore.tagOf_of_view hw
    rw [htag] at hwt
    cases w with
    | bvar i =>
      obtain ⟨⟩ := denote_bvar_inv hwf hw hv
      simp only [htag, beq_self_eq_true, ↓reduceIte]
      exact viewBVar_of_view hw
    | _ => simp [ENodeView.tagOf, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
        ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj] at hwt

/-! ## The filled stream -/

/-- con-leche: ConLeche/Verify/Cached/Fill.lean:21 fillDecl — a theorem's value at a
reference, replaced by the value at that reference. -/
@[expose] def fillRef (val : Nat → Expr) : Expr → Expr
  | .bvar code => val code
  | e => e

/-- con-leche: ConLeche/Verify/Frontend/Olean/Files.lean:758 ValueAt — **the value at a
reference** in the snapshot, where there is one (`ValueAt.unique`). -/
noncomputable def valueOf (sp : ConLeche.Frontend.Olean.SearchPath) (F : FS) (valuesP : Array ConLeche.Frontend.Olean.ModRef)
    (code : Nat) : Expr :=
  open Classical in
  if h : ∃ x, ConLeche.Frontend.Olean.ValueAt sp F valuesP code x then Classical.choose h
  else .bvar code

theorem valueOf_eq {sp : ConLeche.Frontend.Olean.SearchPath} {F : FS} {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    {code : Nat} {x : Expr} (h : ConLeche.Frontend.Olean.ValueAt sp F valuesP code x) :
    valueOf sp F valuesP code = x := by
  have hex : ∃ x, ConLeche.Frontend.Olean.ValueAt sp F valuesP code x := ⟨x, h⟩
  unfold valueOf
  rw [dite_eq_left hex]
  exact ConLeche.Frontend.Olean.ValueAt.unique (Classical.choose_spec hex) h

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
