/-
`ConRon.Refine.Frontend.StateDR` — **the parse state and the record readers,
exact against con-leche** (task #87, phase 3).

Phase 1's `Refine/Frontend/Readers.lean` proved `frontend::export_c`'s reading
half *well formed*: every node it stores is one the port's own smart
constructors built.  This file is the tier above it — the same functions
against `ConLeche/Frontend/ExportC.lean:60-352`, value for value and error for
error.

Three things are decided here once and used by every file above.

* **`IdTableRel`** — the port's `scan_types::IdTable<T>` (a dense `Vec` plus a
  sparse `ron::HashMap<u64, T>`) against con-leche's `IdTable α`
  (`ConLeche/Frontend/Scan/Types.lean:330-420`).  con-leche's module note says
  `get?_empty`/`get?_singleton`/`get?_insert` are *"the only facts the semantic
  layer uses about the table"*, so the relation is stated so that `get?` is
  what the five lemmas below speak about.

* **`StateDRel`** — `export_c::StateD`'s **seventeen** fields against
  `ExportC.lean:82-134`'s **eighteen**.  The three `Name`-keyed `ron::HashMap`s
  and the two `u64`-keyed ones go through `Refine/State.lean`'s `StateRel`
  pattern (`HashMap.RelOn` under `Refine/HashMapWF.lean`'s **`Eq2Fwd`**, not
  `Eq2Spec` — at a `Name` key the equality is the port's own `name::beq` and is
  exact only on well-formed names).
  **Documented deviation:** con-leche's eighteenth field `inModelGen` — the
  `CON_LECHE_INMODEL_DUMP` writer's, which `export_c.rs`'s module note says is
  not ported because con-ron has no `Frontend/ExportWrite.lean` — has **no port
  counterpart**, so `StateDRel` leaves it entirely unconstrained.  Nothing
  below the dump reads it: con-leche's own `pushGenD`/`pushDecl`/`applyLine`
  never look at it.
  There is deliberately **no `absStateD`**, for the reason `Refine/State.lean`
  has no `absCState`: a `ron::HashMap` has no functional abstraction to a
  `Std.HashMap` — the map it denotes is only pinned *relative to* the port's own
  table invariant (`HashMap.Inv`), which is a hypothesis and not a computation.

* **The error relation.**  con-leche's `M` is `Except String`
  (`ConLeche/Frontend/Export.lean:117`); the port's `LineErr`
  (`export_c.rs:160-196`, deviation 1) merges `M`'s message with the *right
  summand* of `StateD ⊕ RecordVerdict`.  So a port `Err (LineErr::Msg _)` is a
  con-leche `.error` — messages are never compared (DESIGN.md §3.1) — and a
  port `Err (LineErr::Verdict v)` is a con-leche **success** returning
  `.inr v`.  `LineErrSim`/`LineOut`/`LineOutV` are that, in the shape
  `Refine/Abs.lean` fixed for the checker's `ErrSim`/`OutP`.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.Readers
import ConRon.Refine.Frontend.Abs
import ConRon.Refine.State

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## What this file gives the line layer

The four statements the two agents above this one consume, spelled out so that
they can be read without reading the proofs.

```lean
theorem parse_expr_rec_d_refines {st lst r e}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hr : ExprRecWF r)
    (h : frontend.export_c.parse_expr_rec_d st r = ok e) :
    LineOut absExpr ExprWF e (ConLeche.Frontend.parseExprRecD lst (absExprRec r))

theorem parse_cv_d_refines {st lst cv v}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_cv_d st cv = ok v) :
    LineOut absConstantVal ConstantValWF v
      (ConLeche.Frontend.parseCVD lst (absCVRec cv))

theorem parse_rule_d_refines {st lst ru r}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_rule_d st ru = ok r) :
    LineOut absRecRule RecRuleWF r (ConLeche.Frontend.parseRuleD lst (absRuleRec ru))

structure StateDRel (st : frontend.export_c.StateD)
    (lst : ConLeche.Frontend.StateD) : Prop
```

`ConLeche.Frontend.parseExprRecD` is the one **escape-hatch definition** of
this file: con-leche writes the value half of `parseExprEntryD` inline, the
port factors it into `parse_expr_rec_d`, and `parseExprEntryD_eq` (below) is
the equivalence.  The same for `parseLevelRecD`.

Every `LineOut`-valued lemma is the **full outcome** (DESIGN.md §3's ruling of
2026-09-13): the value is claimed exactly on `.Ok`, and on a mirrored `.Err` —
`LineErr::Msg`, the parse's own `throw` — con-leche throws too.
-/

/-! ## The line layer's outcome -/

/-- con-leche's `RecordVerdict` (`ConLeche/Frontend/Export.lean:71-79`) without
its message: the two kinds a refinement lemma can claim, exactly as
`Refine/Abs.lean`'s `ErrKind` is `CheckError` without its message. -/
inductive VerdictKind where
  | declined
  | invalid
  deriving DecidableEq, Repr

/-- con-leche's verdict, as its kind. -/
def lVerdictKind : ConLeche.Frontend.RecordVerdict → VerdictKind
  | .declined _ => .declined
  | .invalid _ => .invalid

/-- The port's verdict, as its kind.  Both constructors are mirrored — unlike
`CheckError`, `RecordVerdict` has no port-only arm. -/
def absVerdictKind : frontend.export.RecordVerdict → VerdictKind
  | .Declined _ => .declined
  | .Invalid _ => .invalid

/-- **What a port line error claims about con-leche's `M`.**  Two arms, and
the second is a *claim*, not a silence:

* a `Msg` is con-leche's `throw`.  Messages are never compared (DESIGN.md
  §3.1), so what is claimed is that con-leche's outcome *is* an `.error`;
* a `Verdict` is **impossible**.  A function whose con-leche twin is `M γ` has
  nowhere to put the right summand of `StateD ⊕ RecordVerdict`, and the port's
  readers and value builders reach their error channel only through
  `export_c::merr`.  Saying `False` here is therefore a strengthening the
  proofs discharge, and it is what lets the line layer above turn a reader's
  failure into a `LineOutV` without a side lemma (`LineOutV.of_bind`).

This is `Refine/Abs.lean`'s `ErrSim` for the parse — with the difference that
there is no port-only arm to claim nothing about, `ScanErr::IndexOverflow`'s
counterpart living one layer down in `Refine/Frontend/Abs.lean`. -/
def LineErrSim {γ : Type} (e : frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M γ) : Prop :=
  match e with
  | .Msg _ => ∃ s, x = .error s
  | .Verdict _ => False

/-- A mirrored message. -/
theorem LineErrSim.msg {γ : Type} {m : alloc.vec.Vec Std.U32}
    {x : ConLeche.Frontend.M γ} {s : String} (hx : x = .error s) :
    LineErrSim (.Msg m) x := ⟨s, hx⟩

/-- Error propagation through a bind, the move every arm makes. -/
theorem LineErrSim.bind {γ δ : Type} {e : frontend.export_c.LineErr}
    {x : ConLeche.Frontend.M γ} (h : LineErrSim e x)
    (f : γ → ConLeche.Frontend.M δ) : LineErrSim e (x >>= f) := by
  cases e with
  | Msg m => obtain ⟨s, hx⟩ := h; exact ⟨s, by rw [hx]; rfl⟩
  | Verdict v => exact h.elim

/-- `LineErrSim` transported forward: whatever con-leche throws at `x` it
throws at `y`. -/
theorem LineErrSim.trans {γ δ : Type} {e : frontend.export_c.LineErr}
    {x : ConLeche.Frontend.M γ} {y : ConLeche.Frontend.M δ} (h : LineErrSim e x)
    (hxy : ∀ s, x = .error s → ∃ s', y = .error s') : LineErrSim e y := by
  cases e with
  | Msg m => obtain ⟨s, hx⟩ := h; exact hxy s hx
  | Verdict v => exact h.elim

/-- `LineErrSim` transported along an equation on the con-leche side. -/
theorem LineErrSim.of_eq {γ : Type} {e : frontend.export_c.LineErr}
    {x y : ConLeche.Frontend.M γ} (h : LineErrSim e x) (hxy : y = x) :
    LineErrSim e y := by rw [hxy]; exact h

/-- **The full outcome of a port function whose con-leche twin is `M β`**, in
the shape of `Refine/Abs.lean`'s `OutP`: exact on `.Ok`, `LineErrSim` on
`.Err`. -/
def LineOut {α β : Type} (A : α → β) (WF : α → Prop)
    (o : core.result.Result α frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M β) : Prop :=
  match o with
  | .Ok r => x = .ok (A r) ∧ WF r
  | .Err e => LineErrSim e x

theorem LineOut.ok {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {x : ConLeche.Frontend.M β} (hx : x = .ok (A r)) (hwf : WF r) :
    LineOut A WF (.Ok r) x := ⟨hx, hwf⟩

theorem LineOut.err {α β : Type} {A : α → β} {WF : α → Prop}
    {e : frontend.export_c.LineErr} {x : ConLeche.Frontend.M β}
    (h : LineErrSim e x) : LineOut A WF (.Err e) x := h

/-- **The full outcome of a port function whose con-leche twin is
`M (β ⊕ RecordVerdict)`** — the line layer proper (`applyLine`,
`installIndD`).  This is where the port's second `LineErr` arm lands: a
`Verdict` is a con-leche **success** at the right summand, at the same verdict
kind (the message is not compared, as everywhere else). -/
def LineOutV {α β : Type} (A : α → β) (WF : α → Prop)
    (o : core.result.Result α frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M (β ⊕ ConLeche.Frontend.RecordVerdict)) : Prop :=
  match o with
  | .Ok r => x = .ok (.inl (A r)) ∧ WF r
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict v) =>
    ∃ lv, x = .ok (.inr lv) ∧ lVerdictKind lv = absVerdictKind v

theorem LineOutV.ok {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {x : ConLeche.Frontend.M (β ⊕ ConLeche.Frontend.RecordVerdict)}
    (hx : x = .ok (.inl (A r))) (hwf : WF r) : LineOutV A WF (.Ok r) x := ⟨hx, hwf⟩

theorem LineOutV.msg {α β : Type} {A : α → β} {WF : α → Prop}
    {m : alloc.vec.Vec Std.U32} {s : String}
    {x : ConLeche.Frontend.M (β ⊕ ConLeche.Frontend.RecordVerdict)}
    (hx : x = .error s) : LineOutV A WF (.Err (.Msg m)) x := ⟨s, hx⟩

theorem LineOutV.verdict {α β : Type} {A : α → β} {WF : α → Prop}
    {v : frontend.export.RecordVerdict} {lv : ConLeche.Frontend.RecordVerdict}
    {x : ConLeche.Frontend.M (β ⊕ ConLeche.Frontend.RecordVerdict)}
    (hx : x = .ok (.inr lv)) (hk : lVerdictKind lv = absVerdictKind v) :
    LineOutV A WF (.Err (.Verdict v)) x := ⟨lv, hx, hk⟩

/-- **A reader's failure, inside a line function.**  Every line function opens
with readers whose con-leche twin is a plain `M`; this is the one move that
carries their failure into the sum's outcome, and it is where `LineErrSim`'s
`False` arm pays — the reader cannot have returned a verdict. -/
theorem LineOutV.of_bind {α β γ : Type} {A : α → β} {WF : α → Prop}
    {e : frontend.export_c.LineErr} {x : ConLeche.Frontend.M γ}
    {f : γ → ConLeche.Frontend.M (β ⊕ ConLeche.Frontend.RecordVerdict)}
    (h : LineErrSim e x) : LineOutV A WF (.Err e) (x >>= f) := by
  cases e with
  | Msg m => obtain ⟨s, hx⟩ := h; exact ⟨s, by rw [hx]; rfl⟩
  | Verdict v => exact h.elim

/-! ## The `u64`-keyed overflow map

`scan_types::IdTable`'s sparse half is a `ron::HashMap<u64, T>`, whose key
equality is `u64`'s own — so unlike the `Name`-keyed maps it satisfies
`Eq2Spec` outright, and `Eq2Fwd` at any restriction follows. -/

/-- The overflow map's `Hashable` dictionary. -/
abbrev hU64 := U64.Insts.Con_ron_coreRonHashmapHashable
/-- The overflow map's `Eq2` dictionary: `u64`'s `==`. -/
abbrev eU64 := U64.Insts.Con_ron_coreRonHashmapEq2

/-- `u64`'s `eq2` is exact and total. -/
theorem u64Eq2Spec : HashMap.Eq2Spec eU64 := by
  intro a b; rfl

theorem u64Eq2Fwd {P : Std.U64 → Prop} : HashMap.Eq2Fwd eU64 P :=
  HashMap.Eq2Fwd_of_Eq2Spec u64Eq2Spec

/-- The overflow map's key, in `Refine/State.lean`'s `KeyOk` shape: no
restriction at all, because `absU64` is injective on every `u64`. -/
theorem u64Key : State.KeyOk (fun _ : Std.U64 => True) eU64 absU64 :=
  ⟨u64Eq2Fwd, fun _ _ _ _ h => Env.u64_val_inj h⟩

/-- Every key of a `u64`-keyed table satisfies the empty restriction. -/
theorem u64KeysOk {T : Type} (m : ron.hashmap.HashMap Std.U64 T) :
    HashMap.KeysOk (fun _ : Std.U64 => True) m := fun _ _ => trivial

/-! ## The parse's index tables

`scan_types::IdTable<T>` against `ConLeche/Frontend/Scan/Types.lean:341-344`.
The relation is the two halves separately — the dense `Vec` as con-leche's
dense `Array`, the overflow map as con-leche's `Std.HashMap Nat` — plus the
port's own table invariant, which is what makes the overflow probe exact.
`id_table_get_refines` is then `get?`, which con-leche's module note says is
the only thing the semantic layer asks of the table. -/

/-- `scan_types::IdTable T` denotes `ConLeche.Frontend.IdTable α` under `A`. -/
structure IdTableRel {T α : Type} (A : T → α)
    (t : frontend.scan_types.IdTable T)
    (lt : ConLeche.Frontend.IdTable α) : Prop where
  /-- the dense prefix, element for element -/
  dense : t.dense.val.map A = lt.dense.toList
  /-- the overflow map, key for key -/
  sparse : HashMap.RelOn (fun _ : Std.U64 => True) t.sparse lt.sparse absU64 A
  /-- the port's own hash-table invariant (task #16's `Inv`), which a probe of
  the overflow map needs and no abstraction can supply -/
  inv : HashMap.Inv hU64 t.sparse


/-! ### The two halves, read off the relation -/

/-- The dense prefix, at one index. -/
private theorem idt_dense_getElem? {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    (hrel : IdTableRel A t lt) (j : Nat) :
    lt.dense[j]? = (t.dense.val[j]?).map A := by
  rw [← Array.getElem?_toList, ← hrel.dense, List.getElem?_map]

/-- The dense prefix's length. -/
private theorem idt_dense_size {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    (hrel : IdTableRel A t lt) : lt.dense.size = t.dense.val.length := by
  have h := congrArg List.length hrel.dense; simpa using h.symm

/-- con-leche's `get?`, dense half (`Scan/Types.lean:346-348`). -/
private theorem lidt_get?_dense {α : Type} {lt : ConLeche.Frontend.IdTable α} {j : Nat}
    (h : j < lt.dense.size) : lt.get? j = lt.dense[j]? := by
  simp [ConLeche.Frontend.IdTable.get?, h]

/-- con-leche's `get?`, overflow half. -/
private theorem lidt_get?_sparse {α : Type} {lt : ConLeche.Frontend.IdTable α} {j : Nat}
    (h : ¬ j < lt.dense.size) : lt.get? j = lt.sparse[j]? := by
  simp [ConLeche.Frontend.IdTable.get?, h]

/-- The overflow probe, at any key. -/
private theorem idt_sparse_get {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    (hrel : IdTableRel A t lt) {i : Std.U64} {o : Option T}
    (h : ron.hashmap.HashMap.get hU64 eU64 t.sparse i = ok o) :
    o.map A = lt.sparse[i.val]? :=
  HashMap.Rel_get_wf u64Eq2Fwd hrel.inv (u64KeysOk _) hrel.sparse trivial h

/-! ### The five lemmas the semantic layer uses -/

/-- `scan_types::id_table_get` refines `IdTable.get?`
(`ConLeche/Frontend/Scan/Types.lean:346-348`).  The port's extra guard — it
casts the `u64` index to a `usize` and back and takes the overflow map when the
round trip is not the identity — costs nothing: a `u64` that does not fit a
`usize` is above `Usize.max`, hence above any `Vec`'s length, so con-leche's
dense test fails there too. -/
theorem id_table_get_refines {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    {i : Std.U64} {o : Option T} (hrel : IdTableRel A t lt)
    (h : frontend.scan_types.id_table_get t i = ok o) :
    o.map A = lt.get? i.val := by
  rw [frontend.scan_types.id_table_get] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hsize : lt.dense.size = t.dense.val.length := idt_dense_size hrel
  have hlen : (alloc.vec.Vec.len t.dense).val = t.dense.val.length :=
    alloc.vec.Vec.len_val _
  split at h
  · rename_i hc
    -- the round trip is the identity, so the port's index *is* con-leche's
    have hkv : (Std.UScalar.cast .Usize i : Std.Usize).val = i.val := by
      rw [← ExprOps.usize_cast_u64_val (Std.UScalar.cast .Usize i), hc]
    split at h
    · rename_i hlt
      have hltv : i.val < t.dense.val.length := by
        have : (Std.UScalar.cast .Usize i : Std.Usize).val <
            (alloc.vec.Vec.len t.dense).val := by scalar_tac
        omega
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨x, hx, rfl⟩ := h
      have hgx := ExprOps.vec_index_getElem? hx
      rw [hkv] at hgx
      rw [lidt_get?_dense (by omega), idt_dense_getElem? hrel, hgx]
    · rename_i hge
      have hgev : ¬ i.val < t.dense.val.length := by
        intro hc'
        have : ¬ (Std.UScalar.cast .Usize i : Std.Usize).val <
            (alloc.vec.Vec.len t.dense).val := by scalar_tac
        omega
      rw [lidt_get?_sparse (by omega)]
      exact idt_sparse_get hrel h
  · rename_i hc
    -- the cast is not the identity: the index is above `Usize.max`
    have hbig : Std.Usize.max < i.val := by
      by_contra hle
      exact hc (Env.u64_val_inj (by
        rw [ExprOps.usize_cast_u64_val, ExprOps.u64_cast_usize_val (by omega)]))
    have hgev : ¬ i.val < t.dense.val.length := by
      have := t.dense.property; omega
    rw [lidt_get?_sparse (by omega)]
    exact idt_sparse_get hrel h

/-- The write-back of a `Vec::index_mut` is `Vec.set`.  (`Refine/Frontend/Readers.lean`
keeps the same four lines private; `Refine/HashMap.lean`'s `vec_index_mut_eq` says
more but asks for `Inhabited α`, which the port's term types do not have.) -/
private theorem idt_index_mut_back {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {a : α} {f : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (a, f)) :
    f = alloc.vec.Vec.set v i := by
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨y, -, h⟩ := h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- `scan_types::id_table_insert` refines `IdTable.insert`
(`ConLeche/Frontend/Scan/Types.lean:350-357`): the three arms — a push at the
dense frontier, an overwrite below it, an overflow insert above it — are
con-leche's three, at the same index. -/
theorem id_table_insert_refines {T α : Type} {A : T → α}
    {t t' : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    {i : Std.U64} {x : T} (hrel : IdTableRel A t lt)
    (h : frontend.scan_types.id_table_insert t i x = ok t') :
    IdTableRel A t' (lt.insert i.val (A x)) := by
  rw [frontend.scan_types.id_table_insert] at h
  simp only [] at h
  simp only [lift_eq, bind_tc_ok] at h
  have hsize : lt.dense.size = t.dense.val.length := idt_dense_size hrel
  have hnv : (Std.UScalar.cast .U64 (alloc.vec.Vec.len t.dense) : Std.U64).val
      = t.dense.val.length := by
    rw [ExprOps.usize_cast_u64_val]; exact alloc.vec.Vec.len_val _
  split at h
  · -- the dense frontier: a push on both sides
    rename_i hc
    have hiv : i.val = t.dense.val.length := by rw [hc]; exact hnv
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h
    have hins : lt.insert i.val (A x) = { lt with dense := lt.dense.push (A x) } := by
      rw [ConLeche.Frontend.IdTable.insert]
      simp [hiv, hsize]
    rw [hins]
    exact ⟨by rw [vec_push_val hv]; simp [hrel.dense], hrel.sparse, hrel.inv⟩
  · split at h
    · -- below the frontier: an overwrite on both sides
      rename_i hc hlt
      have hltv : i.val < t.dense.val.length := by
        have : i.val < (Std.UScalar.cast .U64 (alloc.vec.Vec.len t.dense) : Std.U64).val := by
          scalar_tac
        omega
      have hne : ¬ i.val = t.dense.val.length := by omega
      have hi2 : (Std.UScalar.cast .Usize i : Std.Usize).val = i.val :=
        ExprOps.u64_cast_usize_val (by have := t.dense.property; omega)
      simp only [bind_eq_ok_iff] at h
      obtain ⟨p, hp, h⟩ := h
      obtain ⟨a, f⟩ := p
      rw [← Result.ok_injective h, idt_index_mut_back hp]
      have hins : lt.insert i.val (A x)
          = { lt with dense := lt.dense.set i.val (A x) (by omega) } := by
        rw [ConLeche.Frontend.IdTable.insert]
        simp [hne, hsize, hltv]
      rw [hins]
      refine ⟨?_, hrel.sparse, hrel.inv⟩
      show (alloc.vec.Vec.set t.dense (Std.UScalar.cast .Usize i) x).val.map A = _
      rw [alloc.vec.Vec.set_val_eq, hi2, Array.toList_set, ← hrel.dense, List.map_set]
    · -- above the frontier: the overflow map
      rename_i hc hge
      have hgev : ¬ i.val < t.dense.val.length := by
        have : ¬ i.val < (Std.UScalar.cast .U64 (alloc.vec.Vec.len t.dense) : Std.U64).val := by
          scalar_tac
        omega
      have hne : ¬ i.val = t.dense.val.length := by
        intro hc'; exact hc (Env.u64_val_inj (by rw [hnv, hc']))
      simp only [bind_eq_ok_iff] at h
      obtain ⟨p, hp, h⟩ := h
      obtain ⟨old, m'⟩ := p
      rw [← Result.ok_injective h]
      have hins : lt.insert i.val (A x)
          = { lt with sparse := lt.sparse.insert i.val (A x) } := by
        rw [ConLeche.Frontend.IdTable.insert]
        simp [hne, hsize, hgev]
      rw [hins]
      obtain ⟨hinv', -, -, hrel'⟩ :=
        State.insert_step (Q := fun _ => True) u64Key hrel.inv (u64KeysOk _)
          (fun _ _ => trivial) hrel.sparse trivial trivial hp
      exact ⟨hrel.dense, hrel', hinv'⟩

/-- `scan_types::id_table_singleton` refines `IdTable.singleton`
(`ConLeche/Frontend/Scan/Types.lean:359-361`): index 0 bound and nothing
else. -/
theorem id_table_singleton_refines {T α : Type} {A : T → α} {x : T}
    {t : frontend.scan_types.IdTable T}
    (h : frontend.scan_types.id_table_singleton x = ok t) :
    IdTableRel A t (ConLeche.Frontend.IdTable.singleton (A x)) := by
  rw [frontend.scan_types.id_table_singleton] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨dense, hd, m, hm, rfl⟩ := h
  refine ⟨?_, ?_, State.new_inv hm⟩
  · rw [vec_push_val hd]; simp [alloc.vec.Vec.new, ConLeche.Frontend.IdTable.singleton]
  · have := State.new_rel (K' := Nat) (V' := α) (absK := absU64) (absV := A)
      (P := fun _ : Std.U64 => True) hm
    simpa [ConLeche.Frontend.IdTable.singleton] using this

/-- `scan_types::id_table_empty` refines `IdTable`'s field defaults
(`ConLeche/Frontend/Scan/Types.lean:341-344`): the empty table. -/
theorem id_table_empty_refines {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T}
    (h : frontend.scan_types.id_table_empty T = ok t) :
    IdTableRel A t ({} : ConLeche.Frontend.IdTable α) := by
  rw [frontend.scan_types.id_table_empty] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨m, hm, rfl⟩ := h
  refine ⟨by simp [alloc.vec.Vec.new], ?_, State.new_inv hm⟩
  have := State.new_rel (K' := Nat) (V' := α) (absK := absU64) (absV := A)
    (P := fun _ : Std.U64 => True) hm
  simpa using this

/-- **`IdTable.bound` through `get?`** (`ConLeche/Frontend/Scan/Types.lean:363-372`
and its `bound_eq`).  `scan_types` has no `bound`, so the port's three freshness
tests read the table instead (`export_c.rs`'s module note); this is that
reading, against con-leche's predicate. -/
theorem id_table_bound_refines {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    {i : Std.U64} {o : Option T} (hrel : IdTableRel A t lt)
    (h : frontend.scan_types.id_table_get t i = ok o) :
    o.isSome = lt.bound i.val := by
  rw [ConLeche.Frontend.IdTable.bound_eq, ← id_table_get_refines hrel h]
  cases o <;> rfl

/-! ## The parse state

`export_c::StateD` (`export_c.rs:214-252`) against
`ConLeche/Frontend/ExportC.lean:82-134`.  Seventeen fields against eighteen:
`inModelGen` is con-leche's debug dump's and **has no port counterpart** (the
module note: `CON_LECHE_INMODEL_DUMP`'s writer, `Frontend/ExportWrite.lean`,
is not ported), so `StateDRel` leaves it unconstrained.  That is a *documented
deviation* and not a hole: con-leche writes `inModelGen` at one place
(`installIndD`'s dump arm) and reads it nowhere on the parse path, so no state
the relation does constrain depends on it.

The three `Vec` fields are element-for-element lists, the five counters and
flags are values, and the six `Name`-keyed `ron::HashMap`s go through
`HashMap.RelOn` — with the table's own `Inv` and the key restriction `NameWF`
carried in the same structure, because `Eq2Fwd` at a `Name` key is
`name::beq`'s exactness and that holds only for well-formed names
(`Refine/HashMapWF.lean`'s note). -/

/-! ### The record abstractions the state's maps need -/

/-- `proj_rec::ProjRecOwner` as con-leche's
(`ConLeche/Frontend/ProjRec.lean:83-104`).

**Duplicated on purpose, for one integration step.**  `Refine/Frontend/
ProjRecR.lean` — the projection rewrite's own file — defines the same map as
`absProjRecOwner`; the two are definitionally equal, and when the two files
meet the coordinator should keep `absProjRecOwner` and make this one
`:= absProjRecOwner`.  It is here because `StateDRel` cannot be stated without
it and `StateDR.lean` must not depend on a file above it. -/
def absProjOwner (o : frontend.proj_rec.ProjRecOwner) :
    ConLeche.Frontend.ProjRecOwner :=
  { T := absName o.t, lps := absNames o.lps, nP := o.n_p.val,
    ctor := absName o.ctor, nF := o.n_f.val, recName := absName o.rec_name,
    recLps := absNames o.rec_lps, recType := absExpr o.rec_type,
    numMotives := o.num_motives.val, numMinors := o.num_minors.val }

/-- `in_model_rec::IndTypeRec` as `InModel.IndTypeRec`
(`ConLeche/Frontend/InModel/Mutual.lean:66-74`). -/
def absMIndTypeRec (t : frontend.in_model_rec.IndTypeRec) :
    ConLeche.Frontend.InModel.IndTypeRec :=
  { cv := absConstantVal t.cv, nP := t.n_p.val, nIdx := t.n_idx.val,
    ctors := absNames t.ctors, isRec := t.is_rec, isReflexive := t.is_reflexive,
    numNested := t.num_nested.val }

/-- `in_model_rec::IndCtorRec` as `InModel.IndCtorRec`
(`ConLeche/Frontend/InModel/Mutual.lean:77-81`). -/
def absMIndCtorRec (c : frontend.in_model_rec.IndCtorRec) :
    ConLeche.Frontend.InModel.IndCtorRec :=
  { cv := absConstantVal c.cv, nP := c.n_p.val, nF := c.n_f.val }

/-- `in_model_rec::IndRecRec` as `InModel.IndRecRec`
(`ConLeche/Frontend/InModel/Mutual.lean:85-93`). -/
def absMIndRecRec (r : frontend.in_model_rec.IndRecRec) :
    ConLeche.Frontend.InModel.IndRecRec :=
  { cv := absConstantVal r.cv, nP := r.n_p.val, nM := r.n_m.val, nm := r.nm.val,
    nI := r.n_i.val, rules := absRecRules r.rules }

/-- `in_model_rec::BlockRec` as `InModel.BlockRec`
(`ConLeche/Frontend/InModel/Mutual.lean:95-99`).  `alloc.sync.Arc T` *is* `T`
in the model (`Refine/Abs.lean`'s note), so the `P<BlockRec>` the state stores
reads exactly as a `BlockRec`. -/
def absBlockRec (b : frontend.in_model_rec.BlockRec) :
    ConLeche.Frontend.InModel.BlockRec :=
  { types := b.types.val.map absMIndTypeRec,
    ctors := b.ctors.val.map absMIndCtorRec,
    recs := b.recs.val.map absMIndRecRec }

/-- `const_types`' value: a constant's level parameters and declared type. -/
def absNamesExpr (p : alloc.vec.Vec name.Name × expr.Expr) :
    List ConLeche.Name × ConLeche.Expr := (absNames p.1, absExpr p.2)

/-- `in_model_declined`'s entry: the block's name and the census's reason
(`Vec<u32>` of code points, DESIGN.md §3.3). -/
def absNameStr (p : name.Name × alloc.vec.Vec Std.U32) :
    ConLeche.Name × String := (absName p.1, absString p.2)

/-! ### The relation -/

/-- **`export_c::StateD` denotes `ConLeche.Frontend.StateD`.**  Seventeen
clauses for the port's seventeen fields, plus, per `Name`-keyed map, the port's
own table invariant and its key restriction; con-leche's eighteenth field
`inModelGen` is unconstrained (see the section note). -/
structure StateDRel (st : frontend.export_c.StateD)
    (lst : ConLeche.Frontend.StateD) : Prop where
  names : IdTableRel absName st.names lst.names
  levels : IdTableRel absLevel st.levels lst.levels
  exprs : IdTableRel absExpr st.exprs lst.exprs
  decls : st.decls.val.map absDeclaration = lst.decls.toList
  projOwners : HashMap.RelOn NameWF st.proj_owners lst.projOwners absName absProjOwner
  projOwnersInv : HashMap.Inv State.hName st.proj_owners
  projOwnersKeys : HashMap.KeysOk NameWF st.proj_owners
  projLevels : HashMap.RelOn NameWF st.proj_levels lst.projLevels absName absLevel
  projLevelsInv : HashMap.Inv State.hName st.proj_levels
  projLevelsKeys : HashMap.KeysOk NameWF st.proj_levels
  projRewrites : st.proj_rewrites.val.map absName = lst.projRewrites.toList
  constTypes : HashMap.RelOn NameWF st.const_types lst.constTypes absName absNamesExpr
  constTypesInv : HashMap.Inv State.hName st.const_types
  constTypesKeys : HashMap.KeysOk NameWF st.const_types
  heights : HashMap.RelOn NameWF st.heights lst.heights absName absU64
  heightsInv : HashMap.Inv State.hName st.heights
  heightsKeys : HashMap.KeysOk NameWF st.heights
  inModel : st.in_model = lst.inModel
  inModelled : st.in_modelled.val.map absName = lst.inModelled.toList
  genRecords : st.gen_records.val = lst.genRecords
  genOwner : HashMap.RelOn NameWF st.gen_owner lst.genOwner absName absName
  genOwnerInv : HashMap.Inv State.hName st.gen_owner
  genOwnerKeys : HashMap.KeysOk NameWF st.gen_owner
  indCount : st.ind_count.val = lst.indCount
  indBlocks : HashMap.RelOn NameWF st.ind_blocks lst.indBlocks absName absBlockRec
  indBlocksInv : HashMap.Inv State.hName st.ind_blocks
  indBlocksKeys : HashMap.KeysOk NameWF st.ind_blocks
  inModelCensus : st.in_model_census = lst.inModelCensus
  inModelDeclined : st.in_model_declined.val.map absNameStr = lst.inModelDeclined.toList

/-! ## The state readers

`export_c::st_name`/`st_level`/`st_expr` against `ExportC.lean:164-177`'s
`StateD.name`/`.level`/`.expr`.  Each is one `id_table_get` and one `*::dup`,
and `dup` is the identity in the model, so what comes out *is* the recorded
entry — `id_table_get_refines` does the whole of the accept direction and the
`none` arm is the mirrored `throw`. -/

/-- `export_c::merr` is the parse's `throw` (`Refine/Frontend/Readers.lean`
keeps the same one-liner private). -/
private theorem merr_eq (T : Type) (msg : alloc.vec.Vec Std.U32) :
    frontend.export_c.merr T msg = ok (.Err (.Msg msg)) := rfl

/-- `export_c::st_name` refines `StateD.name`
(`ConLeche/Frontend/ExportC.lean:164-167`). -/
theorem st_name_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {i : Std.U64} {o : core.result.Result name.Name frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.st_name st i = ok o) :
    LineOut absName NameWF o (lst.name i.val) := by
  rw [frontend.export_c.st_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, ho, h⟩ := h
  have hget := id_table_get_refines hrel.names ho
  have hwf' : ∀ n, o1 = some n → NameWF n :=
    fun n hn => id_table_get_wf hwf.names (hn ▸ ho)
  rw [ConLeche.Frontend.StateD.name, ← hget]
  cases o1 with
  | none =>
    simp only [bind_eq_ok_iff, merr_eq, Result.ok.injEq] at h
    obtain ⟨_, -, _, -, _, -, v, -, rfl⟩ := h
    exact ⟨_, rfl⟩
  | some n =>
    simp only [name_dup_eq, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]
    exact ⟨rfl, hwf' n rfl⟩

/-- `export_c::st_level` refines `StateD.level`
(`ConLeche/Frontend/ExportC.lean:169-172`). -/
theorem st_level_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {i : Std.U64} {o : core.result.Result level.Level frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.st_level st i = ok o) :
    LineOut absLevel LevelWF o (lst.level i.val) := by
  rw [frontend.export_c.st_level] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, ho, h⟩ := h
  have hget := id_table_get_refines hrel.levels ho
  have hwf' : ∀ u, o1 = some u → LevelWF u :=
    fun u hu => id_table_get_wf hwf.levels (hu ▸ ho)
  rw [ConLeche.Frontend.StateD.level, ← hget]
  cases o1 with
  | none =>
    simp only [bind_eq_ok_iff, merr_eq, Result.ok.injEq] at h
    obtain ⟨_, -, _, -, _, -, v, -, rfl⟩ := h
    exact ⟨_, rfl⟩
  | some u =>
    simp only [level_dup_eq, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]
    exact ⟨rfl, hwf' u rfl⟩

/-- `export_c::st_expr` refines `StateD.expr`
(`ConLeche/Frontend/ExportC.lean:174-177`). -/
theorem st_expr_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {i : Std.U64} {o : core.result.Result expr.Expr frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.st_expr st i = ok o) :
    LineOut absExpr ExprWF o (lst.expr i.val) := by
  rw [frontend.export_c.st_expr] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, ho, h⟩ := h
  have hget := id_table_get_refines hrel.exprs ho
  have hwf' : ∀ e, o1 = some e → ExprWF e :=
    fun e he => id_table_get_wf hwf.exprs (he ▸ ho)
  rw [ConLeche.Frontend.StateD.expr, ← hget]
  cases o1 with
  | none =>
    simp only [bind_eq_ok_iff, merr_eq, Result.ok.injEq] at h
    obtain ⟨_, -, _, -, _, -, v, -, rfl⟩ := h
    exact ⟨_, rfl⟩
  | some e =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨c, hc, rfl⟩ := h
    have hce : c = e := Expr.dup_eq hc
    subst hce
    exact ⟨rfl, hwf' _ rfl⟩

/-- `export_c::get_decl_d` refines `getDeclD`
(`ConLeche/Frontend/ExportC.lean:179-189`), which is `StateD.expr`. -/
theorem get_decl_d_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {i : Std.U64} {o : core.result.Result expr.Expr frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.get_decl_d st i = ok o) :
    LineOut absExpr ExprWF o (ConLeche.Frontend.getDeclD lst i.val) := by
  rw [frontend.export_c.get_decl_d] at h
  exact st_expr_refines hrel hwf h

/-! ## The two list readers

`export_c::st_names`/`st_levels` are con-leche's `is.mapM st.name` /
`us.mapM st.level`, which §3.4 forbids as iterator adapters and the port
spells as an index loop with an accumulator.  A `*_loop` is a
`partial_fixpoint` with no induction principle, so each is strong induction on
the `while i < n` measure `n - i`, exactly as phase 1's `st_names_loop_wf`. -/

/-- The `Vec` read at `i`, as the head of the abstracted tail.  (The same four
lines as `Refine/Frontend/ProjRecR.lean`'s `drop_map_index`, which this file
must not depend on.) -/
private theorem vec_drop_map {α β : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (f : α → β)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    (v.val.map f).drop i.val = f x :: (v.val.map f).drop (i.val + 1) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < v.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : v.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  rw [List.drop_eq_getElem_cons (by simpa using hlt)]
  simp [hx]

/-- A push, on the abstracted list. -/
private theorem absNames_push {out out1 : alloc.vec.Vec name.Name} {v : name.Name}
    (h : alloc.vec.Vec.push out v = ok out1) :
    absNames out1 = absNames out ++ [absName v] := by
  rw [absNames, vec_push_val h]; simp [absNames]

private theorem absLevels_push {out out1 : alloc.vec.Vec level.Level} {v : level.Level}
    (h : alloc.vec.Vec.push out v = ok out1) :
    absLevels out1 = absLevels out ++ [absLevel v] := by
  rw [absLevels, vec_push_val h]; simp [absLevels]

/-- A push extends an "every entry satisfies `P`" invariant. -/
private theorem push_wf' {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  rw [vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- The accumulator of `export_c::st_names`' index loop against the tail of
con-leche's `mapM`. -/
private theorem st_names_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (is : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec name.Name) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec name.Name) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → NamesWF out →
      n.val = is.val.length → n.val - i.val = N →
      frontend.export_c.st_names_loop st is out n i = ok o →
      LineOut absNames NamesWF o
        (do let r ← ((absU64s is).drop i.val).mapM lst.name
            pure (absNames out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst is out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.st_names_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hidx, r, hr, h⟩ := h
      have hdrop : (absU64s is).drop i.val
          = absU64 i1 :: (absU64s is).drop (i.val + 1) := vec_drop_map absU64 hidx
      have hst := st_name_refines hrel hwf hr
      cases r with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hih := ih (n.val - i2.val) (by scalar_tac) st lst is out1 n i2 o hrel hwf
          (push_wf' hout hst.2 hpush) hn rfl h
        have heq : (do let r ← ((absU64s is).drop i.val).mapM lst.name
                       pure (absNames out ++ r))
            = (do let r ← ((absU64s is).drop i2.val).mapM lst.name
                  pure (absNames out1 ++ r)) := by
          rw [hdrop, hi2v, List.mapM_cons, hst.1, absNames_push hpush]
          simp
          rfl
        rw [heq]; exact hih
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hst ?_
        intro s hs
        rw [hdrop, List.mapM_cons, hs]
        exact ⟨s, rfl⟩
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absU64s is).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absU64s, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; simp only [List.mapM_nil, pure_bind, List.append_nil]; rfl, hout⟩

/-- `export_c::st_names` refines `is.mapM st.name`, the `mapM` of
`parsePwD`/`parseCVD`/`parseExprEntryD`'s level-parameter and constructor
lists. -/
theorem st_names_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {is : alloc.vec.Vec Std.U64}
    {o : core.result.Result (alloc.vec.Vec name.Name) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.st_names st is = ok o) :
    LineOut absNames NamesWF o ((absU64s is).mapM lst.name) := by
  rw [frontend.export_c.st_names] at h
  have := st_names_loop_refines _ st lst is _ _ 0#usize o hrel hwf
    (by simp [NamesWF, alloc.vec.Vec.with_capacity]) (alloc.vec.Vec.len_val _) rfl h
  simpa [absNames, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using this

/-- The accumulator of `export_c::st_levels`' index loop (see
`st_names_loop_refines`). -/
private theorem st_levels_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (is : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec level.Level) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec level.Level) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → LevelsWF out →
      n.val = is.val.length → n.val - i.val = N →
      frontend.export_c.st_levels_loop st is out n i = ok o →
      LineOut absLevels LevelsWF o
        (do let r ← ((absU64s is).drop i.val).mapM lst.level
            pure (absLevels out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst is out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.st_levels_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hidx, r, hr, h⟩ := h
      have hdrop : (absU64s is).drop i.val
          = absU64 i1 :: (absU64s is).drop (i.val + 1) := vec_drop_map absU64 hidx
      have hst := st_level_refines hrel hwf hr
      cases r with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hih := ih (n.val - i2.val) (by scalar_tac) st lst is out1 n i2 o hrel hwf
          (push_wf' hout hst.2 hpush) hn rfl h
        have heq : (do let r ← ((absU64s is).drop i.val).mapM lst.level
                       pure (absLevels out ++ r))
            = (do let r ← ((absU64s is).drop i2.val).mapM lst.level
                  pure (absLevels out1 ++ r)) := by
          rw [hdrop, hi2v, List.mapM_cons, hst.1, absLevels_push hpush]
          simp
          rfl
        rw [heq]; exact hih
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hst ?_
        intro s hs
        rw [hdrop, List.mapM_cons, hs]
        exact ⟨s, rfl⟩
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absU64s is).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absU64s, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; simp only [List.mapM_nil, pure_bind, List.append_nil]; rfl, hout⟩

/-- `export_c::st_levels` refines `us.mapM st.level`. -/
theorem st_levels_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {is : alloc.vec.Vec Std.U64}
    {o : core.result.Result (alloc.vec.Vec level.Level) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.st_levels st is = ok o) :
    LineOut absLevels LevelsWF o ((absU64s is).mapM lst.level) := by
  rw [frontend.export_c.st_levels] at h
  have := st_levels_loop_refines _ st lst is _ _ 0#usize o hrel hwf
    (by simp [LevelsWF, alloc.vec.Vec.with_capacity]) (alloc.vec.Vec.len_val _) rfl h
  simpa [absLevels, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using this

end ConRon.Refine.Frontend
