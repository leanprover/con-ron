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
import ConRon.Refine.BasisRaw

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## What this file gives the line layer

The four statements the two agents above this one consume, spelled out so that
they can be read without reading the proofs.

```lean
structure StateDRel (st : frontend.export_c.StateD)
    (lst : ConLeche.Frontend.StateD) : Prop

theorem parse_expr_rec_d_refines {st lst r o}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hr : ExprRecWF r)
    (hnat : NatValSpec r)
    (h : frontend.export_c.parse_expr_rec_d st r = ok o) :
    LineOut absExpr ExprWF o (parseExprRecD lst (absExprRec r))

theorem parse_cv_d_refines {st lst cv o}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_cv_d st cv = ok o) :
    LineOut absConstantVal ConstantValWF o
      (ConLeche.Frontend.parseCVD lst (absCVRec cv))

theorem parse_rule_d_refines {st lst ru o}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_rule_d st ru = ok o) :
    LineOut absRecRule RecRuleWF o (ConLeche.Frontend.parseRuleD lst (absRuleRec ru))
```

Two things a caller has to know.

* **`parseExprRecD` / `parseLevelRecD` are this file's two escape-hatch
  definitions** (DESIGN.md's rule for where the port and the Lean do not line
  up one for one): con-leche writes the *value* half of
  `parseExprEntryD`/`parseLevelEntryD` inline, the port factors each into its
  own function, and `parseExprEntryD_eq` / `parseLevelEntryD_eq` are the
  equivalences — each one `simp` per constructor.
* **`NatValSpec r` is an ingredient hypothesis**, vacuous at every
  constructor but `NatVal`, and it is the only thing this file assumes.  See
  its doc comment: it is the port's `nat_decimal::from_decimal` against
  `natOfDigits`, which is a scanner obligation plus a bignum lemma and belongs
  to neither this file nor this tier.

Every `LineOut`-valued lemma is the **full outcome** (DESIGN.md §3's ruling of
2026-09-13): the value is claimed exactly on `.Ok`, and on a mirrored `.Err` —
`LineErr::Msg`, the parse's own `throw` — con-leche throws too.  `LineErr::
Verdict` is claimed **impossible** at an `M`-valued function, which is what
`LineOutV.of_bind` spends one layer up.
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

/-! ## The `pw` datum -/

/-- `export_c::parse_pw_d` refines `parsePwD`
(`ConLeche/Frontend/ExportC.lean:191-194`): the two arms are
`prop_when::never` and `prop_when::if_all_zero`, two of the type's four public
producers. -/
theorem parse_pw_d_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {r : frontend.scan_types.PwRec}
    {o : core.result.Result prop_when.PropWhen frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_pw_d st r = ok o) :
    LineOut absPropWhen PropWhenWF o (ConLeche.Frontend.parsePwD lst (absPwRec r)) := by
  rw [frontend.export_c.parse_pw_d.eq_def] at h
  cases r with
  | Never =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨pw, hpw, rfl⟩ := h
    exact ⟨by rw [show absPwRec .Never = .never from rfl, ConLeche.Frontend.parsePwD,
      PropWhen.never_refines hpw]; rfl, PropWhenWF.never hpw⟩
  | IfAllZero ns =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have hst := st_names_refines hrel hwf hr1
    cases r1 with
    | Ok out =>
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨pw, hpw, rfl⟩ := h
      refine ⟨?_, PropWhenWF.if_all_zero hst.2 hpw⟩
      rw [show absPwRec (.IfAllZero ns) = .ifAllZero (absU64s ns) from rfl,
        ConLeche.Frontend.parsePwD, hst.1, PropWhen.if_all_zero_refines hst.2 hpw]
      rfl
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine LineErrSim.trans hst ?_
      intro s hs
      rw [show absPwRec (.IfAllZero ns) = .ifAllZero (absU64s ns) from rfl,
        ConLeche.Frontend.parsePwD, hs]
      exact ⟨s, rfl⟩

/-! ## The two value builders, and the one escape hatch

con-leche writes the *value* half of `parseLevelEntryD`/`parseExprEntryD`
inline; the port factors each into its own function (`parse_level_rec_d`,
`parse_expr_rec_d`) because §3.4 has no `?` and the entry point must be a
`match` chain.  DESIGN.md's rule for that is an **intermediate Lean definition
matching the port's shape, with an equivalence proof to the piece it came
out of** — `parseLevelRecD`/`parseExprRecD` and `parseLevelEntryD_eq`/
`parseExprEntryD_eq`, both `rfl` per constructor. -/

/-- **Escape hatch 1.**  The value half of `parseLevelEntryD`
(`ConLeche/Frontend/ExportC.lean:239-247`), written out. -/
def parseLevelRecD (st : ConLeche.Frontend.StateD) :
    ConLeche.Frontend.LevelRec → ConLeche.Frontend.M ConLeche.Level
  | .succ u => do pure (ConLeche.Level.succ (← st.level u))
  | .max a b => do pure (ConLeche.Level.max (← st.level a) (← st.level b))
  | .imax a b => do pure (ConLeche.Level.imax (← st.level a) (← st.level b))
  | .param n => do pure (ConLeche.Level.param (← st.name n))

/-- …and it *is* what `parseLevelEntryD` runs. -/
theorem parseLevelEntryD_eq (st : ConLeche.Frontend.StateD) (i : Nat)
    (r : ConLeche.Frontend.LevelRec) :
    ConLeche.Frontend.parseLevelEntryD st i r
      = (do st.freshLevel i
            let l ← parseLevelRecD st r
            pure { st with levels := st.levels.insert i l }) := by
  cases r <;> simp [ConLeche.Frontend.parseLevelEntryD, parseLevelRecD]

/-- **Escape hatch 2.**  The value half of `parseExprEntryD`
(`ConLeche/Frontend/ExportC.lean:249-279`), written out. -/
def parseExprRecD (st : ConLeche.Frontend.StateD) :
    ConLeche.Frontend.ExprRec → ConLeche.Frontend.M ConLeche.Expr
  | .bvar k => pure (ConLeche.Expr.mkBvar k)
  | .sort u => do pure (ConLeche.Expr.mkSort (← st.level u))
  | .const n us => do
    let nm ← st.name n
    let ls ← us.mapM st.level
    pure (ConLeche.Expr.mkConst nm ls)
  | .app f a => do pure (ConLeche.Expr.mkApp (← st.expr f) (← st.expr a))
  | .lam ty bd pw => do
    pure (ConLeche.Expr.mkLam (← st.expr ty) (← st.expr bd) ⟨← ConLeche.Frontend.parsePwD st pw⟩)
  | .forallE ty bd pw => do
    pure (ConLeche.Expr.mkForallE (← st.expr ty) (← st.expr bd)
      ⟨← ConLeche.Frontend.parsePwD st pw⟩)
  | .letE ty vl bd => do
    pure (ConLeche.Expr.mkLetE (← st.expr ty) (← st.expr vl) (← st.expr bd))
  | .proj tn ix s => do pure (ConLeche.Expr.mkProj (← st.name tn) ix (← st.expr s))
  | .natVal n => pure (ConLeche.Expr.mkLit (.natVal n))
  | .strVal s => pure (ConLeche.Expr.mkLit (.strVal s))

/-- …and it *is* what `parseExprEntryD` runs. -/
theorem parseExprEntryD_eq (st : ConLeche.Frontend.StateD) (i : Nat)
    (r : ConLeche.Frontend.ExprRec) :
    ConLeche.Frontend.parseExprEntryD st i r
      = (do st.freshExpr i
            let e ← parseExprRecD st r
            pure { st with exprs := st.exprs.insert i e }) := by
  cases r <;> simp [ConLeche.Frontend.parseExprEntryD, parseExprRecD]

/-- `export_c::parse_level_rec_d` refines the value half of `parseLevelEntryD`
(`ConLeche/Frontend/ExportC.lean:239-247`): four arms, one `Level`
constructor each. -/
theorem parse_level_rec_d_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {r : frontend.scan_types.LevelRec}
    {o : core.result.Result level.Level frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_level_rec_d st r = ok o) :
    LineOut absLevel LevelWF o (parseLevelRecD lst (absLevelRec r)) := by
  rw [frontend.export_c.parse_level_rec_d.eq_def] at h
  cases r with
  | Succ u =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_level_refines hrel hwf hr1
    cases r1 with
    | Ok a =>
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact ⟨by simp only [absLevelRec, parseLevelRecD, h1.1, Level.succ_refines hv]; rfl,
        LevelWF.succ h1.2 hv⟩
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine LineErrSim.trans h1 ?_
      intro s hs
      simp only [absLevelRec, parseLevelRecD, hs]
      exact ⟨s, rfl⟩
  | Max a b =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_level_refines hrel hwf hr1
    cases r1 with
    | Ok x =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_level_refines hrel hwf hr2
      cases r2 with
      | Ok y =>
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨v, hv, rfl⟩ := h
        exact ⟨by simp only [absLevelRec, parseLevelRecD, h1.1, h2.1,
          Level.max_refines hv]; rfl, LevelWF.max h1.2 h2.2 hv⟩
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans h2 ?_
        intro s hs
        simp only [absLevelRec, parseLevelRecD, h1.1, hs]
        exact ⟨s, rfl⟩
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine LineErrSim.trans h1 ?_
      intro s hs
      simp only [absLevelRec, parseLevelRecD, hs]
      exact ⟨s, rfl⟩
  | Imax a b =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_level_refines hrel hwf hr1
    cases r1 with
    | Ok x =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_level_refines hrel hwf hr2
      cases r2 with
      | Ok y =>
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨v, hv, rfl⟩ := h
        exact ⟨by simp only [absLevelRec, parseLevelRecD, h1.1, h2.1,
          Level.imax_refines hv]; rfl, LevelWF.imax h1.2 h2.2 hv⟩
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans h2 ?_
        intro s hs
        simp only [absLevelRec, parseLevelRecD, h1.1, hs]
        exact ⟨s, rfl⟩
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine LineErrSim.trans h1 ?_
      intro s hs
      simp only [absLevelRec, parseLevelRecD, hs]
      exact ⟨s, rfl⟩
  | Param n =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_name_refines hrel hwf hr1
    cases r1 with
    | Ok p =>
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact ⟨by simp only [absLevelRec, parseLevelRecD, h1.1, Level.param_refines hv]; rfl,
        LevelWF.param h1.2 hv⟩
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine LineErrSim.trans h1 ?_
      intro s hs
      simp only [absLevelRec, parseLevelRecD, hs]
      exact ⟨s, rfl⟩

/-! ## The expression builder

`export_c::parse_expr_rec_d` against the value half of `parseExprEntryD`
(`ConLeche/Frontend/ExportC.lean:249-279`): ten arms, one node each. -/

/-- The error arm, said once: whatever con-leche threw at the reader it throws
at the `do` block the reader opens. -/
private theorem errOf {γ δ : Type} {e : frontend.export_c.LineErr}
    {x : ConLeche.Frontend.M γ} (h : LineErrSim e x) {y : ConLeche.Frontend.M δ}
    (hy : ∀ s, x = .error s → y = .error s) : LineErrSim e y :=
  LineErrSim.trans h (fun s hs => ⟨s, hy s hs⟩)

/-- **The one ingredient this file does not prove.**  `scan_types::ExprRec`'s
`NatVal` arm keeps the literal's *decimal digits* where con-leche's keeps the
`Nat` (`Refine/Frontend/Abs.lean`'s deviation 2), so the port reads them with
`nat_decimal::from_decimal` — a bignum routine con-leche has no counterpart
for, since Lean's `Nat` is already arbitrary precision.

`NatValSpec r` is what the arm needs of it, and it decomposes into two facts
neither of which belongs here:

* a **scanner obligation** — the digits are decimal (`from_decimal` returns
  `none` exactly on an empty slice or a byte outside `'0'..'9'`), which is
  phase 3's analogue of phase 1's `ExprRecWF` and is `scan_nat_val`'s to
  discharge;
* an **arithmetic lemma** — `from_decimal`'s nineteen-digit chunk loop over
  `ron::nat` limbs computes `natOfDigits`, i.e. the same fold `readNatAt`
  (`Scan/Fast.lean:499-500`) computes on con-leche's side.

It is vacuous at every other constructor, so a caller that knows its record is
not a `NatVal` discharges it with `by intro _ hc; simp at hc`. -/
def NatValSpec (r : frontend.scan_types.ExprRec) : Prop :=
  ∀ ds, r = .NatVal ds →
    ∀ o, frontend.nat_decimal.from_decimal (alloc.vec.Vec.deref ds) = ok o →
      ∃ n, o = some n ∧ Nat.toNat n = natOfDigits ds

/-- `export_c::parse_expr_rec_d` refines the value half of `parseExprEntryD`
(`ConLeche/Frontend/ExportC.lean:249-279`). -/
theorem parse_expr_rec_d_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {r : frontend.scan_types.ExprRec}
    {o : core.result.Result expr.Expr frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hr : ExprRecWF r)
    (hnat : NatValSpec r)
    (h : frontend.export_c.parse_expr_rec_d st r = ok o) :
    LineOut absExpr ExprWF o (parseExprRecD lst (absExprRec r)) := by
  rw [frontend.export_c.parse_expr_rec_d.eq_def] at h
  cases r with
  | Bvar k =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨e, he, rfl⟩ := h
    refine ⟨?_, ?_⟩
    · simp only [absExprRec, parseExprRecD, Expr.mk_bvar_refines he, absU64]; rfl
    · exact Expr.bvar_wf (by rw [expr.mk_bvar] at he; exact he)
  | «Sort» u =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_level_refines hrel hwf hr1
    cases r1 with
    | Ok l =>
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨e, he, rfl⟩ := h
      exact ⟨by simp only [absExprRec, parseExprRecD, absU64, h1.1, Expr.sort_refines he]; rfl,
        Expr.sort_wf' he h1.2⟩
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h1 (fun s hs => by simp only [absExprRec, parseExprRecD, absU64, hs]; rfl)
  | Const n us =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_name_refines hrel hwf hr1
    cases r1 with
    | Ok nm =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_levels_refines hrel hwf hr2
      cases r2 with
      | Ok ls =>
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨e, he, rfl⟩ := h
        exact ⟨by simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1,
          Expr.mk_const_refines he]; rfl, Expr.mk_const_wf' he h1.2 h2.2⟩
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact errOf h2 (fun s hs => by
          simp only [absExprRec, parseExprRecD, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h1 (fun s hs => by simp only [absExprRec, parseExprRecD, absU64, hs]; rfl)
  | App f a =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_expr_refines hrel hwf hr1
    cases r1 with
    | Ok x =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_expr_refines hrel hwf hr2
      cases r2 with
      | Ok y =>
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨e, he, rfl⟩ := h
        exact ⟨by simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1,
          Expr.app_refines he]; rfl, Expr.app_wf' he h1.2 h2.2⟩
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact errOf h2 (fun s hs => by
          simp only [absExprRec, parseExprRecD, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h1 (fun s hs => by simp only [absExprRec, parseExprRecD, absU64, hs]; rfl)
  | Lam ty bd pw =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_expr_refines hrel hwf hr1
    cases r1 with
    | Ok t =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_expr_refines hrel hwf hr2
      cases r2 with
      | Ok b =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r3, hr3, h⟩ := h
        have h3 := parse_pw_d_refines hrel hwf hr3
        cases r3 with
        | Ok p =>
          simp only [ExprOps.binder_meta_eq, bind_tc_ok, bind_eq_ok_iff, Result.ok.injEq] at h
          obtain ⟨e, he, rfl⟩ := h
          exact ⟨by simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1, h3.1,
            Expr.lam_refines he, absBinderMeta]; rfl,
            Expr.lam_wf' he h1.2 h2.2 h3.2⟩
        | Err e =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact errOf h3 (fun s hs => by
            simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1, hs]; rfl)
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact errOf h2 (fun s hs => by
          simp only [absExprRec, parseExprRecD, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h1 (fun s hs => by simp only [absExprRec, parseExprRecD, absU64, hs]; rfl)
  | ForallE ty bd pw =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_expr_refines hrel hwf hr1
    cases r1 with
    | Ok t =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_expr_refines hrel hwf hr2
      cases r2 with
      | Ok b =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r3, hr3, h⟩ := h
        have h3 := parse_pw_d_refines hrel hwf hr3
        cases r3 with
        | Ok p =>
          simp only [ExprOps.binder_meta_eq, bind_tc_ok, bind_eq_ok_iff, Result.ok.injEq] at h
          obtain ⟨e, he, rfl⟩ := h
          exact ⟨by simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1, h3.1,
            Expr.forall_e_refines he, absBinderMeta]; rfl,
            Expr.forall_e_wf' he h1.2 h2.2 h3.2⟩
        | Err e =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact errOf h3 (fun s hs => by
            simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1, hs]; rfl)
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact errOf h2 (fun s hs => by
          simp only [absExprRec, parseExprRecD, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h1 (fun s hs => by simp only [absExprRec, parseExprRecD, absU64, hs]; rfl)
  | LetE ty vl bd =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_expr_refines hrel hwf hr1
    cases r1 with
    | Ok t =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_expr_refines hrel hwf hr2
      cases r2 with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r3, hr3, h⟩ := h
        have h3 := st_expr_refines hrel hwf hr3
        cases r3 with
        | Ok b =>
          simp only [bind_eq_ok_iff, Result.ok.injEq] at h
          obtain ⟨e, he, rfl⟩ := h
          exact ⟨by simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1, h3.1,
            Expr.let_e_refines he]; rfl, Expr.let_e_wf' he h1.2 h2.2 h3.2⟩
        | Err e =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact errOf h3 (fun s hs => by
            simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1, hs]; rfl)
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact errOf h2 (fun s hs => by
          simp only [absExprRec, parseExprRecD, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h1 (fun s hs => by simp only [absExprRec, parseExprRecD, absU64, hs]; rfl)
  | Proj tn ix s =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_name_refines hrel hwf hr1
    cases r1 with
    | Ok t =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_expr_refines hrel hwf hr2
      cases r2 with
      | Ok x =>
        simp only [bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨e, he, rfl⟩ := h
        exact ⟨by simp only [absExprRec, parseExprRecD, absU64, h1.1, h2.1,
          Expr.proj_refines he]; rfl, Expr.proj_wf' he h1.2 h2.2⟩
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact errOf h2 (fun s' hs => by
          simp only [absExprRec, parseExprRecD, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h1 (fun s' hs => by simp only [absExprRec, parseExprRecD, absU64, hs]; rfl)
  | NatVal ds =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o1, ho1, h⟩ := h
    obtain ⟨n, rfl, hn⟩ := hnat ds rfl o1 ho1
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨l, hl, e, he, rfl⟩ := h
    have hln : l = .NatVal n := by
      rw [show expr.literal_nat n = ok (.NatVal n) from by simp [expr.literal_nat]] at hl
      exact (Result.ok_injective hl).symm
    subst hln
    refine ⟨?_, Expr.lit_wf' he (from_decimal_wf ho1)⟩
    simp only [absExprRec, parseExprRecD, Expr.lit_refines he, absLiteral, hn]
    rfl
  | StrVal s =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, l, hl, e, he, rfl⟩ := h
    have hlv : l = .StrVal v := by
      rw [show expr.literal_str v = ok (.StrVal v) from by simp [expr.literal_str]] at hl
      exact (Result.ok_injective hl).symm
    subst hlv
    have hsv : absString v = absString s := by
      rw [absString, absString, Env.code_points_val hv,
        show (alloc.vec.Vec.deref s).val = s.val from Slice.from_val _ _]
    have hvwf : StrWF v := by
      intro c hc
      rw [Env.code_points_val hv,
        show (alloc.vec.Vec.deref s).val = s.val from Slice.from_val _ _] at hc
      exact (show StrWF s by simpa only [ExprRecWF] using hr) c hc
    exact ⟨by simp only [absExprRec, parseExprRecD, Expr.lit_refines he, absLiteral, hsv]; rfl,
      Expr.lit_wf' he hvwf⟩

/-! ## The two record builders -/

/-- `export_c::parse_cv_d` refines `parseCVD`
(`ConLeche/Frontend/ExportC.lean:283-289`): a declaration's common data —
three readings in the cited order, and no constructor of its own. -/
theorem parse_cv_d_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {cv : frontend.scan_types.CVRec}
    {o : core.result.Result env.ConstantVal frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_cv_d st cv = ok o) :
    LineOut absConstantVal ConstantValWF o (ConLeche.Frontend.parseCVD lst (absCVRec cv)) := by
  rw [frontend.export_c.parse_cv_d.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  have h1 := st_name_refines hrel hwf hr
  cases r with
  | Ok nm =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h2 := get_decl_d_refines hrel hwf hr1
    cases r1 with
    | Ok ty =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h3 := st_names_refines hrel hwf hr2
      cases r2 with
      | Ok lps =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine ⟨?_, ⟨h1.2, h3.2, h2.2⟩⟩
        simp only [ConLeche.Frontend.parseCVD, absCVRec, absU64, h1.1, h2.1, h3.1]
        rfl
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact errOf h3 (fun s hs => by
          simp only [ConLeche.Frontend.parseCVD, absCVRec, absU64, h1.1, h2.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h2 (fun s hs => by
        simp only [ConLeche.Frontend.parseCVD, absCVRec, absU64, h1.1, hs]; rfl)
  | Err e =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact errOf h1 (fun s hs => by
      simp only [ConLeche.Frontend.parseCVD, absCVRec, absU64, hs]; rfl)

/-- `export_c::parse_rule_d` refines `parseRuleD`
(`ConLeche/Frontend/ExportC.lean:346-349`): one recursor rule, at
`env::rec_rule_parsed`'s field defaults. -/
theorem parse_rule_d_refines {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {ru : frontend.scan_types.RuleRec}
    {o : core.result.Result env.RecRule frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_rule_d st ru = ok o) :
    LineOut absRecRule RecRuleWF o (ConLeche.Frontend.parseRuleD lst (absRuleRec ru)) := by
  rw [frontend.export_c.parse_rule_d.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  have h1 := st_name_refines hrel hwf hr
  cases r with
  | Ok c =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h2 := get_decl_d_refines hrel hwf hr1
    cases r1 with
    | Ok rhs =>
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨rr, hrr, rfl⟩ := h
      refine ⟨?_, Env.rec_rule_parsed_wf h1.2 h2.2 hrr⟩
      simp only [ConLeche.Frontend.parseRuleD, absRuleRec, absU64, h1.1, h2.1,
        Env.rec_rule_parsed_refines hrr]
      rfl
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact errOf h2 (fun s hs => by
        simp only [ConLeche.Frontend.parseRuleD, absRuleRec, absU64, h1.1, hs]; rfl)
  | Err e =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact errOf h1 (fun s hs => by
      simp only [ConLeche.Frontend.parseRuleD, absRuleRec, absU64, hs]; rfl)

/-- The accumulator of `export_c::parse_rules_d`' index loop (see
`st_names_loop_refines`). -/
private theorem parse_rules_d_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (rus : alloc.vec.Vec frontend.scan_types.RuleRec) (out : alloc.vec.Vec env.RecRule)
      (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec env.RecRule) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → RecRulesWF out →
      n.val = rus.val.length → n.val - i.val = N →
      frontend.export_c.parse_rules_d_loop st rus out n i = ok o →
      LineOut absRecRules RecRulesWF o
        (do let r ← ((absRuleRecs rus).drop i.val).mapM (ConLeche.Frontend.parseRuleD lst)
            pure (absRecRules out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst rus out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.parse_rules_d_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ru, hidx, r, hr, h⟩ := h
      have hdrop : (absRuleRecs rus).drop i.val
          = absRuleRec ru :: (absRuleRecs rus).drop (i.val + 1) := vec_drop_map absRuleRec hidx
      have hst := parse_rule_d_refines hrel hwf hr
      cases r with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hih := ih (n.val - i2.val) (by scalar_tac) st lst rus out1 n i2 o hrel hwf
          (push_wf' hout hst.2 hpush) hn rfl h
        have heq : (do let r ← ((absRuleRecs rus).drop i.val).mapM
                          (ConLeche.Frontend.parseRuleD lst)
                       pure (absRecRules out ++ r))
            = (do let r ← ((absRuleRecs rus).drop i2.val).mapM
                     (ConLeche.Frontend.parseRuleD lst)
                  pure (absRecRules out1 ++ r)) := by
          rw [hdrop, hi2v, List.mapM_cons, hst.1,
            show absRecRules out1 = absRecRules out ++ [absRecRule v] from by
              rw [absRecRules, vec_push_val hpush]; simp [absRecRules]]
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
      have hnil : (absRuleRecs rus).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absRuleRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; simp only [List.mapM_nil, pure_bind, List.append_nil]; rfl, hout⟩

/-- `export_c::parse_rules_d` refines `r.rules.mapM (parseRuleD st)`
(`ConLeche/Frontend/ExportC.lean:346-349`, as the recursor record's arm of
`applyLine` spells it). -/
theorem parse_rules_d_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {rus : alloc.vec.Vec frontend.scan_types.RuleRec}
    {o : core.result.Result (alloc.vec.Vec env.RecRule) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_rules_d st rus = ok o) :
    LineOut absRecRules RecRulesWF o
      ((absRuleRecs rus).mapM (ConLeche.Frontend.parseRuleD lst)) := by
  rw [frontend.export_c.parse_rules_d] at h
  have := parse_rules_d_loop_refines _ st lst rus _ _ 0#usize o hrel hwf
    (by simp [RecRulesWF, alloc.vec.Vec.with_capacity]) (alloc.vec.Vec.len_val _) rfl h
  simpa [absRecRules, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using this

/-! ## The three freshness tests

`export_c::st_fresh_name`/`st_fresh_level`/`st_fresh_expr` against
`ExportC.lean:211-224`'s `StateD.freshName`/`.freshLevel`/`.freshExpr`.
`scan_types` has no `IdTable.bound`, so the port reads the table instead
(`export_c.rs`'s module note) — `id_table_bound_refines` is the bridge, and it
is con-leche's own `IdTable.bound_eq`.

`export_c::rebound_error` itself carries **no lemma**: it builds the message
con-leche's `reboundError` builds, and messages are never compared
(DESIGN.md §3.1) — the only thing a caller may claim about a `throw` is that
it *is* one. -/

/-- `export_c::st_fresh_name` refines `StateD.freshName`
(`ConLeche/Frontend/ExportC.lean:211-220`). -/
theorem st_fresh_name_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64}
    {o : core.result.Result Unit frontend.export_c.LineErr} (hrel : StateDRel st lst)
    (h : frontend.export_c.st_fresh_name st i = ok o) :
    LineOut (fun _ : Unit => ()) (fun _ => True) o (lst.freshName i.val) := by
  rw [frontend.export_c.st_fresh_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, ho, h⟩ := h
  have hb := id_table_bound_refines hrel.names ho
  simp only [ConLeche.Frontend.StateD.freshName, ← hb]
  cases o1 with
  | none =>
    simp only [Result.ok.injEq] at h
    rw [← h]; exact ⟨by simp; rfl, trivial⟩
  | some x =>
    simp only [bind_eq_ok_iff, merr_eq, Result.ok.injEq] at h
    obtain ⟨_, -, v, -, rfl⟩ := h
    exact ⟨_, by simp only [Option.isSome_some, if_true]; rfl⟩

/-- `export_c::st_fresh_level` refines `StateD.freshLevel`
(`ConLeche/Frontend/ExportC.lean:221-222`). -/
theorem st_fresh_level_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64}
    {o : core.result.Result Unit frontend.export_c.LineErr} (hrel : StateDRel st lst)
    (h : frontend.export_c.st_fresh_level st i = ok o) :
    LineOut (fun _ : Unit => ()) (fun _ => True) o (lst.freshLevel i.val) := by
  rw [frontend.export_c.st_fresh_level] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, ho, h⟩ := h
  have hb := id_table_bound_refines hrel.levels ho
  simp only [ConLeche.Frontend.StateD.freshLevel, ← hb]
  cases o1 with
  | none =>
    simp only [Result.ok.injEq] at h
    rw [← h]; exact ⟨by simp; rfl, trivial⟩
  | some x =>
    simp only [bind_eq_ok_iff, merr_eq, Result.ok.injEq] at h
    obtain ⟨_, -, v, -, rfl⟩ := h
    exact ⟨_, by simp only [Option.isSome_some, if_true]; rfl⟩

/-- `export_c::st_fresh_expr` refines `StateD.freshExpr`
(`ConLeche/Frontend/ExportC.lean:223-224`). -/
theorem st_fresh_expr_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64}
    {o : core.result.Result Unit frontend.export_c.LineErr} (hrel : StateDRel st lst)
    (h : frontend.export_c.st_fresh_expr st i = ok o) :
    LineOut (fun _ : Unit => ()) (fun _ => True) o (lst.freshExpr i.val) := by
  rw [frontend.export_c.st_fresh_expr] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, ho, h⟩ := h
  have hb := id_table_bound_refines hrel.exprs ho
  simp only [ConLeche.Frontend.StateD.freshExpr, ← hb]
  cases o1 with
  | none =>
    simp only [Result.ok.injEq] at h
    rw [← h]; exact ⟨by simp; rfl, trivial⟩
  | some x =>
    simp only [bind_eq_ok_iff, merr_eq, Result.ok.injEq] at h
    obtain ⟨_, -, v, -, rfl⟩ := h
    exact ⟨_, by simp only [Option.isSome_some, if_true]; rfl⟩

/-! ## The three table entries

`export_c::parse_name_entry_d`/`parse_level_entry_d`/`parse_expr_entry_d`
against `ExportC.lean:228-279`.  Each binds one stream index: the value half
above, then `id_table_insert` into the matching table.

The port threads the state by `&mut` and con-leche returns it (`export_c.rs`'s
deviation 1), so the outcome vocabulary here is `StepOut`: on a success the
port's new state denotes the state con-leche returned, on a mirrored failure
con-leche throws — and the port's state on a failure is *not* claimed, because
con-leche has none to compare it with. -/

/-- **The full outcome of a `&mut StateD` step** whose con-leche twin returns
the new state (`Refine/State.lean`'s `Out`, for the parse). -/
def StepOut (o : core.result.Result Unit frontend.export_c.LineErr)
    (st' : frontend.export_c.StateD)
    (x : ConLeche.Frontend.M ConLeche.Frontend.StateD) : Prop :=
  match o with
  | .Ok _ => ∃ lst', x = .ok lst' ∧ StateDRel st' lst' ∧ StateDWF st'
  | .Err e => LineErrSim e x

theorem StepOut.ok {st' : frontend.export_c.StateD} {lst' : ConLeche.Frontend.StateD}
    {x : ConLeche.Frontend.M ConLeche.Frontend.StateD} (hx : x = .ok lst')
    (hrel : StateDRel st' lst') (hwf : StateDWF st') : StepOut (.Ok ()) st' x :=
  ⟨lst', hx, hrel, hwf⟩

theorem StepOut.err {e : frontend.export_c.LineErr} {st' : frontend.export_c.StateD}
    {x : ConLeche.Frontend.M ConLeche.Frontend.StateD} (h : LineErrSim e x) :
    StepOut (.Err e) st' x := h

/-! ### One table replaced

Each of the three writes touches exactly one field, so the other sixteen
clauses of `StateDRel` carry over by the record update. -/

private theorem StateDRel.names_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {it : frontend.scan_types.IdTable name.Name}
    {lit : ConLeche.Frontend.IdTable ConLeche.Name}
    (hrel : StateDRel st lst) (h : IdTableRel absName it lit) :
    StateDRel { st with names := it } { lst with names := lit } :=
  { hrel with names := h }

private theorem StateDRel.levels_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {it : frontend.scan_types.IdTable level.Level}
    {lit : ConLeche.Frontend.IdTable ConLeche.Level}
    (hrel : StateDRel st lst) (h : IdTableRel absLevel it lit) :
    StateDRel { st with levels := it } { lst with levels := lit } :=
  { hrel with levels := h }

private theorem StateDRel.exprs_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {it : frontend.scan_types.IdTable expr.Expr}
    {lit : ConLeche.Frontend.IdTable ConLeche.Expr}
    (hrel : StateDRel st lst) (h : IdTableRel absExpr it lit) :
    StateDRel { st with exprs := it } { lst with exprs := lit } :=
  { hrel with exprs := h }

/-- `export_c::parse_name_entry_d` refines `parseNameEntryD`
(`ConLeche/Frontend/ExportC.lean:228-237`): the parent index is resolved before
the freshness test, as in the cited `do` block, and the value is built directly
by `name::mk_str`/`name::mk_num`. -/
theorem parse_name_entry_d_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64} {r : frontend.scan_types.NameRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hr : NameRecWF r)
    (h : frontend.export_c.parse_name_entry_d st i r = ok (o, st')) :
    StepOut o st' (ConLeche.Frontend.parseNameEntryD lst i.val (absNameRec r)) := by
  have hfull := h
  rw [frontend.export_c.parse_name_entry_d.eq_def] at h
  cases r with
  | Str pre s =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_name_refines hrel hwf hr1
    cases r1 with
    | Ok p =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_fresh_name_refines hrel hr2
      cases r2 with
      | Ok u =>
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨v, hv, v1, hv1, it, hit, rfl, rfl⟩ := h
        have hsv : absString v = absString s := by
          rw [absString, absString, Env.code_points_val hv,
            show (alloc.vec.Vec.deref s).val = s.val from Slice.from_val _ _]
        have hins : IdTableRel absName it
            (lst.names.insert i.val (ConLeche.Name.str (absName p) (absString s))) := by
          have hi := id_table_insert_refines hrel.names hit
          rwa [Name.mk_str_refines hv1, hsv] at hi
        refine StepOut.ok ?_ (StateDRel.names_update hrel hins)
          (parse_name_entry_d_wf hwf hr hfull)
        simp only [ConLeche.Frontend.parseNameEntryD, absNameRec, absU64, h1.1, h2.1]
        rfl
      | Err e =>
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact errOf h2 (fun s' hs => by
          simp only [ConLeche.Frontend.parseNameEntryD, absNameRec, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact errOf h1 (fun s' hs => by
        simp only [ConLeche.Frontend.parseNameEntryD, absNameRec, absU64, hs]; rfl)
  | Num pre k =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have h1 := st_name_refines hrel hwf hr1
    cases r1 with
    | Ok p =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have h2 := st_fresh_name_refines hrel hr2
      cases r2 with
      | Ok u =>
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨v, hv, it, hit, rfl, rfl⟩ := h
        have hins : IdTableRel absName it
            (lst.names.insert i.val (ConLeche.Name.num (absName p) k.val)) := by
          have hi := id_table_insert_refines hrel.names hit
          rwa [Name.mk_num_refines hv] at hi
        refine StepOut.ok ?_ (StateDRel.names_update hrel hins)
          (parse_name_entry_d_wf hwf hr hfull)
        simp only [ConLeche.Frontend.parseNameEntryD, absNameRec, absU64, h1.1, h2.1]
        rfl
      | Err e =>
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact errOf h2 (fun s' hs => by
          simp only [ConLeche.Frontend.parseNameEntryD, absNameRec, absU64, h1.1, hs]; rfl)
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact errOf h1 (fun s' hs => by
        simp only [ConLeche.Frontend.parseNameEntryD, absNameRec, absU64, hs]; rfl)

/-- `export_c::parse_level_entry_d` refines `parseLevelEntryD`
(`ConLeche/Frontend/ExportC.lean:239-247`), through `parseLevelEntryD_eq`. -/
theorem parse_level_entry_d_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64} {r : frontend.scan_types.LevelRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.parse_level_entry_d st i r = ok (o, st')) :
    StepOut o st' (ConLeche.Frontend.parseLevelEntryD lst i.val (absLevelRec r)) := by
  have hfull := h
  rw [frontend.export_c.parse_level_entry_d.eq_def] at h
  rw [parseLevelEntryD_eq]
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r1, hr1, h⟩ := h
  have h1 := st_fresh_level_refines hrel hr1
  cases r1 with
  | Ok u =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r2, hr2, h⟩ := h
    have h2 := parse_level_rec_d_refines hrel hwf hr2
    cases r2 with
    | Ok l =>
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨it, hit, rfl, rfl⟩ := h
      refine StepOut.ok ?_
        (StateDRel.levels_update hrel (id_table_insert_refines hrel.levels hit))
        (parse_level_entry_d_wf hwf hfull)
      simp only [h1.1, h2.1]
      rfl
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact errOf h2 (fun s' hs => by simp only [h1.1, hs]; rfl)
  | Err e =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact errOf h1 (fun s' hs => by simp only [hs]; rfl)

/-- `export_c::parse_expr_entry_d` refines `parseExprEntryD`
(`ConLeche/Frontend/ExportC.lean:249-279`), through `parseExprEntryD_eq`. -/
theorem parse_expr_entry_d_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64} {r : frontend.scan_types.ExprRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hr : ExprRecWF r)
    (hnat : NatValSpec r)
    (h : frontend.export_c.parse_expr_entry_d st i r = ok (o, st')) :
    StepOut o st' (ConLeche.Frontend.parseExprEntryD lst i.val (absExprRec r)) := by
  have hfull := h
  rw [frontend.export_c.parse_expr_entry_d.eq_def] at h
  rw [parseExprEntryD_eq]
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r1, hr1, h⟩ := h
  have h1 := st_fresh_expr_refines hrel hr1
  cases r1 with
  | Ok u =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r2, hr2, h⟩ := h
    have h2 := parse_expr_rec_d_refines hrel hwf hr hnat hr2
    cases r2 with
    | Ok e =>
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨it, hit, rfl, rfl⟩ := h
      refine StepOut.ok ?_
        (StateDRel.exprs_update hrel (id_table_insert_refines hrel.exprs hit))
        (parse_expr_entry_d_wf hwf hr hfull)
      simp only [h1.1, h2.1]
      rfl
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact errOf h2 (fun s' hs => by simp only [h1.1, hs]; rfl)
  | Err e =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact errOf h1 (fun s' hs => by simp only [hs]; rfl)

/-! ## The declaration table

`export_c::note_decl_entries`/`note_one`/`note_block`/`note_entries`/
`note_decl` against `noteDecl` (`ConLeche/Frontend/ExportC.lean:135-153`),
which con-leche writes as one function: a `let cvs := match d with …` and a
`cvs.foldl` over `constTypes` and `heights`.  The port splits it into the list
builder and the index loop (§3.4 has no `foldl` and no closure), so this is
**escape hatches 3 and 4** — `noteDeclEntries` and `noteEntries`, con-leche's
two halves written out, with `noteDecl_eq` the equivalence. -/

/-- One entry of `noteDecl`'s `cvs`: a constant's name, level parameters,
declared type and (for a definition) definitional height. -/
abbrev NoteEntry := ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Option Nat

/-- The port's entry as con-leche's. -/
def absNoteEntry
    (p : name.Name × (alloc.vec.Vec name.Name) × expr.Expr × (Option Std.U64)) :
    NoteEntry :=
  (absName p.1, absNames p.2.1, absExpr p.2.2.1, p.2.2.2.map absU64)

/-- The port's entry `Vec` as con-leche's `cvs`. -/
def absNoteEntries
    (es : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr ×
      (Option Std.U64))) : List NoteEntry :=
  es.val.map absNoteEntry

/-- **Escape hatch 3.**  `noteDecl`'s `cvs`, written out. -/
def noteDeclEntries : ConLeche.Declaration → List NoteEntry
  | .axiomDecl cv => [(cv.name, cv.levelParams, cv.type, none)]
  | .defnDecl cv _ h =>
    [(cv.name, cv.levelParams, cv.type, some (ConLeche.Frontend.InModel.hintHeight h))]
  | .thmDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
  | .opaqueDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
  | .basisDecl k => k.decls.map fun ci =>
    (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
  | .quotDecl _ cv => [(cv.name, cv.levelParams, cv.type, none)]
  | .indDecl block _ => block.map fun ci =>
    (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)

/-- **Escape hatch 4.**  `noteDecl`'s fold, written out — con-leche's own
lines with `cvs` as the parameter. -/
def noteEntries (st : ConLeche.Frontend.StateD) (cvs : List NoteEntry) :
    ConLeche.Frontend.StateD :=
  let ct := st.constTypes
  let hs := st.heights
  let st := { st with constTypes := {}, heights := {} }
  let (ct, hs) := cvs.foldl (fun (ct, hs) (n, lps, ty, h) =>
    (ct.insert n (lps, ty), match h with | some h => hs.insert n h | none => hs)) (ct, hs)
  { st with constTypes := ct, heights := hs }

/-- …and the two halves *are* `noteDecl`. -/
theorem noteDecl_eq (st : ConLeche.Frontend.StateD) (d : ConLeche.Declaration) :
    ConLeche.Frontend.noteDecl st d = noteEntries st (noteDeclEntries d) := by
  cases d <;> rfl

/-- One entry of the fold, peeled. -/
private theorem noteEntries_cons (lst : ConLeche.Frontend.StateD) (e : NoteEntry)
    (rest : List NoteEntry) :
    noteEntries lst (e :: rest) = noteEntries (noteEntries lst [e]) rest := by
  simp [noteEntries]

/-- One entry of the fold, as a record update. -/
private theorem noteEntries_single (lst : ConLeche.Frontend.StateD) (n : ConLeche.Name)
    (lps : List ConLeche.Name) (ty : ConLeche.Expr) (h : Option Nat) :
    noteEntries lst [(n, lps, ty, h)]
      = { lst with constTypes := lst.constTypes.insert n (lps, ty),
                   heights := match h with
                     | some x => lst.heights.insert n x
                     | none => lst.heights } := by
  cases h <;> simp [noteEntries]

/-- The empty fold. -/
private theorem noteEntries_nil (lst : ConLeche.Frontend.StateD) :
    noteEntries lst [] = lst := by simp [noteEntries]

/-! ### The two untracked maps, replaced

`StateDWF` has no clause for `const_types` or `heights` (phase 1's table: they
are the *modeller's*, and `ModellerWF` is unconditional in its argument), so
what a `note_entries` step has to carry is the `StateDRel` clause and the
port's own table invariant. -/

private theorem StateDRel.heights_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {m : ron.hashmap.HashMap name.Name Std.U64}
    {lm : _root_.Std.HashMap ConLeche.Name Nat} (hrel : StateDRel st lst)
    (hr : HashMap.RelOn NameWF m lm absName absU64)
    (hi : HashMap.Inv State.hName m) (hk : HashMap.KeysOk NameWF m) :
    StateDRel { st with heights := m } { lst with heights := lm } :=
  { hrel with heights := hr, heightsInv := hi, heightsKeys := hk }

private theorem StateDRel.constTypes_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {m : ron.hashmap.HashMap name.Name ((alloc.vec.Vec name.Name) × expr.Expr)}
    {lm : _root_.Std.HashMap ConLeche.Name (List ConLeche.Name × ConLeche.Expr)}
    (hrel : StateDRel st lst) (hr : HashMap.RelOn NameWF m lm absName absNamesExpr)
    (hi : HashMap.Inv State.hName m) (hk : HashMap.KeysOk NameWF m) :
    StateDRel { st with const_types := m } { lst with constTypes := lm } :=
  { hrel with constTypes := hr, constTypesInv := hi, constTypesKeys := hk }

/-- `StateDWF` at a state whose two untracked maps moved. -/
private theorem StateDWF.untracked {st st' : frontend.export_c.StateD} (hwf : StateDWF st)
    (h1 : st'.names = st.names) (h2 : st'.levels = st.levels) (h3 : st'.exprs = st.exprs)
    (h4 : st'.decls = st.decls) (h5 : st'.proj_owners = st.proj_owners)
    (h6 : st'.proj_levels = st.proj_levels) : StateDWF st' :=
  ⟨h1 ▸ hwf.names, h2 ▸ hwf.levels, h3 ▸ hwf.exprs, h4 ▸ hwf.decls,
    h5 ▸ hwf.proj_owners, h6 ▸ hwf.proj_levels⟩

/-- What a `Vec` read hands back is one of the `Vec`'s entries. -/
private theorem vec_index_mem' {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    x ∈ v.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? h)

/-- The step of `export_c::note_entries`' index loop against one entry of
`noteDecl`'s `cvs.foldl`. -/
private theorem note_entries_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (es : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr ×
        (Option Std.U64)))
      (n i : Std.Usize) (st' : frontend.export_c.StateD),
      StateDRel st lst → StateDWF st → (∀ p ∈ es.val, NameWF p.1) →
      n.val = es.val.length → n.val - i.val = N →
      frontend.export_c.note_entries_loop st es n i = ok st' →
      StateDRel st' (noteEntries lst ((absNoteEntries es).drop i.val)) ∧ StateDWF st' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst es n i st' hrel hwf hkeys hn hN h
    rw [frontend.export_c.note_entries_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff, Prod.exists] at h
      obtain ⟨n1, v, e, o, hidx, h⟩ := h
      have hdrop : (absNoteEntries es).drop i.val
          = absNoteEntry (n1, v, e, o) :: (absNoteEntries es).drop (i.val + 1) :=
        vec_drop_map absNoteEntry hidx
      have hn1 : NameWF n1 := hkeys _ (vec_index_mem' hidx)
      simp only [rust_invert] at h
      obtain ⟨st1, hst1, v1, hv1, old, hm, hp, i1, hi1, h⟩ := h
      -- the heights half
      have hh : StateDRel st1 { lst with heights := match o.map absU64 with
                 | some x => lst.heights.insert (absName n1) x
                 | none => lst.heights } ∧ StateDWF st1 ∧ st1.const_types = st.const_types := by
        cases o with
        | none =>
          rw [← Result.ok_injective hst1]
          exact ⟨hrel, hwf, rfl⟩
        | some hv =>
          simp only [rust_invert] at hst1
          obtain ⟨a, b, hq, hst1⟩ := hst1
          obtain ⟨hinv', hkeys', -, hrel'⟩ :=
            State.insert_step (Q := fun _ => True) State.nameKey hrel.heightsInv
              hrel.heightsKeys (fun _ _ => trivial) hrel.heights hn1 trivial hq
          rw [← hst1]
          exact ⟨StateDRel.heights_update hrel hrel' hinv' hkeys',
            StateDWF.untracked hwf rfl rfl rfl rfl rfl rfl, rfl⟩
      -- the constTypes half
      have hvv : v1.val = v.val := PropWhen.names_copy_val hv1
      have hval : absNamesExpr (v1, e) = (absNames v, absExpr e) := by
        simp only [absNamesExpr, absNames, hvv]
      obtain ⟨hinv2, hkeys2, -, hrel2⟩ :=
        State.insert_step (Q := fun _ => True) State.nameKey hh.1.constTypesInv
          hh.1.constTypesKeys (fun _ _ => trivial) hh.1.constTypes hn1 trivial hp
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hrel3 : StateDRel { st1 with const_types := hm }
          (noteEntries lst [absNoteEntry (n1, v, e, o)]) := by
        simp only [absNoteEntry, noteEntries_single]
        have hx := StateDRel.constTypes_update hh.1 hrel2 hinv2 hkeys2
        rw [hval] at hx
        exact hx
      have hwf3 : StateDWF { st1 with const_types := hm } :=
        StateDWF.untracked hh.2.1 rfl rfl rfl rfl rfl rfl
      have hih := ih (n.val - i1.val) (by scalar_tac) _ _ es n i1 st' hrel3 hwf3 hkeys hn rfl h
      rw [hi1v] at hih
      rw [hdrop, noteEntries_cons]
      exact hih
    · rename_i hge
      have hnil : (absNoteEntries es).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absNoteEntries, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      rw [hnil, noteEntries_nil, ← Result.ok_injective h]
      exact ⟨hrel, hwf⟩

/-- `export_c::note_entries` refines `noteDecl`'s `cvs.foldl`
(`ConLeche/Frontend/ExportC.lean:135-153`).  Its two writes land in the two
fields `StateDWF` does not track — the *modeller's* tables — so what is claimed
is the `StateDRel` clause and nothing about well-formedness beyond what came
in. -/
theorem note_entries_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {es : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr ×
      (Option Std.U64))}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hkeys : ∀ p ∈ es.val, NameWF p.1)
    (h : frontend.export_c.note_entries st es = ok st') :
    StateDRel st' (noteEntries lst (absNoteEntries es)) ∧ StateDWF st' := by
  rw [frontend.export_c.note_entries] at h
  have := note_entries_loop_refines _ st lst es _ 0#usize st' hrel hwf hkeys
    (alloc.vec.Vec.len_val _) rfl h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using this

/-- The name a `ConstantInfo`'s common data carries is well formed. -/
private theorem to_constant_val_name_wf {c : env.ConstantInfo} {r : env.ConstantVal}
    (hc : ConstantInfoWF c) (h : env.to_constant_val c = ok r) : NameWF r.name := by
  cases c with
  | ProjInfo tbl =>
    rw [env.to_constant_val] at h
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, v, -, l, -, l1, -, e, -, rfl⟩ := h
    exact Env.proj_table_name_wf (show ProjTableWF tbl from hc).1 hn
  | AxiomInfo v => rw [env.to_constant_val] at h
                   rw [Env.constant_val_dup_refines h]; exact (show ConstantValWF v from hc).1
  | DefnInfo v a b => rw [env.to_constant_val] at h
                      rw [Env.constant_val_dup_refines h]
                      exact (show ConstantValWF v ∧ _ from hc).1.1
  | ThmInfo v a => rw [env.to_constant_val] at h
                   rw [Env.constant_val_dup_refines h]
                   exact (show ConstantValWF v ∧ _ from hc).1.1
  | IndInfo v a => rw [env.to_constant_val] at h
                   rw [Env.constant_val_dup_refines h]
                   exact (show ConstantValWF v ∧ _ from hc).1.1
  | CtorInfo v a b => rw [env.to_constant_val] at h
                      rw [Env.constant_val_dup_refines h]
                      exact (show ConstantValWF v from hc).1
  | RecInfo v a b c => rw [env.to_constant_val] at h
                       rw [Env.constant_val_dup_refines h]
                       exact (show ConstantValWF v ∧ _ from hc).1.1

/-- `export_c::note_one` refines `noteDecl`'s `[(cv, h)]`
(`ConLeche/Frontend/ExportC.lean:135-153`). -/
theorem note_one_refines {cv : env.ConstantVal} {hv : Option Std.U64}
    {es : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr ×
      (Option Std.U64))}
    (hcv : ConstantValWF cv) (h : frontend.export_c.note_one cv hv = ok es) :
    absNoteEntries es
        = [((absConstantVal cv).name, (absConstantVal cv).levelParams,
            (absConstantVal cv).type, hv.map absU64)] ∧
      ∀ p ∈ es.val, NameWF p.1 := by
  rw [frontend.export_c.note_one] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv1, e, he, hpush⟩ := h
  have hvv : v.val = cv.level_params.val := PropWhen.names_copy_val hv1
  have hee : e = cv.ty := Expr.dup_eq he
  refine ⟨?_, ?_⟩
  · rw [absNoteEntries, vec_push_val hpush]
    simp [alloc.vec.Vec.new, absNoteEntry, absConstantVal, absNames, hvv, hee]
  · intro p hp
    rw [vec_push_val hpush] at hp
    rcases List.mem_append.mp hp with hp | hp
    · simp [alloc.vec.Vec.new] at hp
    · rw [List.mem_singleton.mp hp]; exact hcv.1

/-- The accumulator of `export_c::note_block`'s index loop against
`noteDecl`'s `block.map`. -/
private theorem note_block_loop_refines (N : Nat) :
    ∀ (bl : alloc.vec.Vec env.ConstantInfo)
      (out r : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr ×
        (Option Std.U64))) (n k : Std.Usize),
      ConstantInfosWF bl → (∀ p ∈ out.val, NameWF p.1) →
      n.val = bl.val.length → n.val - k.val = N →
      frontend.export_c.note_block_loop bl out n k = ok r →
      absNoteEntries r = absNoteEntries out ++
        ((absConstantInfos bl).drop k.val).map (fun ci =>
          (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type,
            (none : Option Nat))) ∧
      (∀ p ∈ r.val, NameWF p.1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bl out r n k hbl hout hn hN h
    rw [frontend.export_c.note_block_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨ci, hidx, cv, hcv, v, hv, e, he, out1, hpush, k1, hk1, h⟩ := h
      have hdrop : (absConstantInfos bl).drop k.val
          = absConstantInfo ci :: (absConstantInfos bl).drop (k.val + 1) :=
        vec_drop_map absConstantInfo hidx
      have hciwf : ConstantInfoWF ci := hbl _ (vec_index_mem' hidx)
      have hnwf : NameWF cv.name := to_constant_val_name_wf hciwf hcv
      have habs : absConstantVal cv = ConLeche.ConstantInfo.toConstantVal (absConstantInfo ci) :=
        Env.to_constant_val_refines hcv
      have hvv : v.val = cv.level_params.val := PropWhen.names_copy_val hv
      have hee : e = cv.ty := Expr.dup_eq he
      have hout1 : ∀ p ∈ out1.val, NameWF p.1 := by
        rw [vec_push_val hpush]
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hout p hp
        · rw [List.mem_singleton.mp hp]; exact hnwf
      have hk1v : k1.val = k.val + 1 := HashMap.uscalar_add_eq hk1
      obtain ⟨hih, hihk⟩ :=
        ih (n.val - k1.val) (by scalar_tac) bl out1 r n k1 hbl hout1 hn rfl h
      refine ⟨?_, hihk⟩
      rw [hih, hk1v, hdrop]
      simp only [List.map_cons]
      rw [absNoteEntries, vec_push_val hpush]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append]
      congr 1
      simp only [absNoteEntry, ← habs, absConstantVal, absNames, hvv, hee]
      rfl
    · rename_i hge
      have hnil : (absConstantInfos bl).drop k.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absConstantInfos, List.length_map]
        have : n.val ≤ k.val := by scalar_tac
        omega
      rw [← Result.ok_injective h, hnil]
      exact ⟨by simp, hout⟩

/-- `export_c::note_block` refines `noteDecl`'s `block.map`. -/
theorem note_block_refines {bl : alloc.vec.Vec env.ConstantInfo}
    {out r : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr ×
      (Option Std.U64))} {k : Std.Usize}
    (hbl : ConstantInfosWF bl) (hout : ∀ p ∈ out.val, NameWF p.1)
    (h : frontend.export_c.note_block bl k out = ok r) :
    absNoteEntries r = absNoteEntries out ++
      ((absConstantInfos bl).drop k.val).map (fun ci =>
        (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type,
          (none : Option Nat))) ∧
    (∀ p ∈ r.val, NameWF p.1) := by
  rw [frontend.export_c.note_block] at h
  exact note_block_loop_refines _ bl out r _ k hbl hout (alloc.vec.Vec.len_val _) rfl h

/-- `export_c::note_decl_entries` refines `noteDecl`'s `cvs`
(`ConLeche/Frontend/ExportC.lean:135-153`, and
`ConLeche/Kernel/Basis.lean:40-47` for the basis arm). -/
theorem note_decl_entries_refines {d : env.Declaration}
    {es : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr ×
      (Option Std.U64))}
    (hd : DeclarationWF d) (h : frontend.export_c.note_decl_entries d = ok es) :
    absNoteEntries es = noteDeclEntries (absDeclaration d) ∧ ∀ p ∈ es.val, NameWF p.1 := by
  rw [frontend.export_c.note_decl_entries.eq_def] at h
  cases d with
  | AxiomDecl cv =>
    obtain ⟨h1, h2⟩ := note_one_refines hd h
    exact ⟨by rw [h1]; rfl, h2⟩
  | DefnDecl cv v hint =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨h1, h2⟩ := note_one_refines hd.1 h
    refine ⟨?_, h2⟩
    rw [h1]
    cases hint <;>
      simp_all [frontend.in_model_rec.hint_height, noteDeclEntries, absDeclaration, absHint,
        ConLeche.Frontend.InModel.hintHeight, absU64, absConstantVal] <;> scalar_tac
  | ThmDecl cv v =>
    obtain ⟨h1, h2⟩ := note_one_refines hd.1 h
    exact ⟨by rw [h1]; rfl, h2⟩
  | OpaqueDecl cv v =>
    obtain ⟨h1, h2⟩ := note_one_refines hd.1 h
    exact ⟨by rw [h1]; rfl, h2⟩
  | QuotDecl k cv =>
    obtain ⟨h1, h2⟩ := note_one_refines hd h
    exact ⟨by rw [h1]; rfl, h2⟩
  | BasisDecl k =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨habs, hwf⟩ := BasisRaw.basis_kind_decls_refines hv
    obtain ⟨h1, h2⟩ := note_block_refines hwf (by simp [alloc.vec.Vec.new]) h
    refine ⟨?_, h2⟩
    rw [h1, habs]
    simp [absNoteEntries, alloc.vec.Vec.new, noteDeclEntries, absDeclaration,
      show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  | IndDecl bl nP =>
    obtain ⟨h1, h2⟩ := note_block_refines hd (by simp [alloc.vec.Vec.new]) h
    refine ⟨?_, h2⟩
    rw [h1]
    simp [absNoteEntries, alloc.vec.Vec.new, noteDeclEntries, absDeclaration,
      absConstantInfos, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- `export_c::note_decl` refines `noteDecl`
(`ConLeche/Frontend/ExportC.lean:135-153`). -/
theorem note_decl_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {d : env.Declaration}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hd : DeclarationWF d)
    (h : frontend.export_c.note_decl st d = ok st') :
    StateDRel st' (ConLeche.Frontend.noteDecl lst (absDeclaration d)) ∧ StateDWF st' := by
  rw [frontend.export_c.note_decl] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨es, hes, h⟩ := h
  obtain ⟨habs, hkeys⟩ := note_decl_entries_refines hd hes
  rw [noteDecl_eq, ← habs]
  exact note_entries_refines hrel hwf hkeys h

/-- `noteDecl` does not touch `decls`, which is why the port may note *before*
it pushes where con-leche pushes before it notes. -/
private theorem noteDecl_decls (lst : ConLeche.Frontend.StateD) (d : ConLeche.Declaration)
    (L : Array ConLeche.Declaration) :
    ConLeche.Frontend.noteDecl { lst with decls := L } d
      = { ConLeche.Frontend.noteDecl lst d with decls := L } := by
  rw [noteDecl_eq, noteDecl_eq]; simp [noteEntries]

/-- `export_c::push_decl` refines `pushDecl`
(`ConLeche/Frontend/ExportC.lean:155-162`): **the one step that extends the
declaration list**, total since con-leche task #293. -/
theorem push_decl_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {d : env.Declaration}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hd : DeclarationWF d)
    (h : frontend.export_c.push_decl st d = ok st') :
    StateDRel st' (ConLeche.Frontend.pushDecl lst (absDeclaration d)) ∧ StateDWF st' := by
  rw [frontend.export_c.push_decl] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨st1, hst1, v, hv, rfl⟩ := h
  obtain ⟨hrel1, hwf1⟩ := note_decl_refines hrel hwf hd hst1
  rw [ConLeche.Frontend.pushDecl, noteDecl_decls]
  refine ⟨{ hrel1 with decls := ?_ }, ?_⟩
  · rw [vec_push_val hv]
    simp [hrel1.decls, noteDecl_eq, noteEntries]
  · exact ⟨hwf1.names, hwf1.levels, hwf1.exprs, push_wf' hwf1.decls hd hv,
      hwf1.proj_owners, hwf1.proj_levels⟩

/-! ## The record copies

`cv_rec_dup`, `ind_ctor_rec_dup`, `proj_rec_owner_dup`, `declaration_dup` and
`constant_infos_dup` have **no con-leche counterpart**: con-leche gets its
copies from Lean's sharing, and the port needs them because Aeneas's `Vec`
model has no way to move an element out of an owned `Vec` (their doc comments
say so).  So the statement is the strongest one available — each copy **is the
identity in the model**, exactly as `nat_op_ground::declaration_dup` was found
to be at task #85 (`Refine/Frontend/Prepare.lean`). -/

/-- The `Vec<u64>` copy behind `cv_rec_dup`. -/
private theorem cv_rec_dup_loop_val (N : Nat) :
    ∀ (v lps r : alloc.vec.Vec Std.U64) (n i : Std.Usize),
      n.val = v.val.length → n.val - i.val = N →
      frontend.export_c.cv_rec_dup_loop v lps n i = ok r →
      r.val = lps.val ++ v.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro v lps r n i hn hN h
    rw [frontend.export_c.cv_rec_dup_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hidx, lps1, hpush, i2, hi2, h⟩ := h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hdrop : v.val.drop i.val = i1 :: v.val.drop (i.val + 1) := by
        have := vec_drop_map (v := v) (i := i) (x := i1) id hidx
        simpa using this
      rw [ih (n.val - i2.val) (by scalar_tac) v lps1 r n i2 hn rfl h,
        vec_push_val hpush, hi2v, hdrop]
      simp
    · rename_i hge
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by scalar_tac)]
      simp

/-- `export_c::cv_rec_dup` is the identity on a `CVRec`. -/
theorem cv_rec_dup_refines {cv r : frontend.scan_types.CVRec}
    (h : frontend.export_c.cv_rec_dup cv = ok r) : r = cv := by
  rw [frontend.export_c.cv_rec_dup] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨lps1, hlps, rfl⟩ := h
  have hv := cv_rec_dup_loop_val _ cv.level_params _ lps1 _ 0#usize
    (alloc.vec.Vec.len_val _) rfl hlps
  have hv' : lps1.val = cv.level_params.val := by
    rw [hv]
    simp [alloc.vec.Vec.with_capacity, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  rw [alloc.vec.Vec.ext lps1 cv.level_params hv']

/-- `export_c::ind_ctor_rec_dup` is the identity on an `IndCtorRec`. -/
theorem ind_ctor_rec_dup_refines {c r : frontend.scan_types.IndCtorRec}
    (h : frontend.export_c.ind_ctor_rec_dup c = ok r) : r = c := by
  rw [frontend.export_c.ind_ctor_rec_dup] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨c1, hc1, rfl⟩ := h
  rw [cv_rec_dup_refines hc1]

/-- `export_c::proj_rec_owner_dup` is the identity on a `ProjRecOwner`. -/
theorem proj_rec_owner_dup_refines {o r : frontend.proj_rec.ProjRecOwner}
    (h : frontend.export_c.proj_rec_owner_dup o = ok r) : r = o := by
  rw [frontend.export_c.proj_rec_owner_dup] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv, v1, hv1, e, he, rfl⟩ := h
  rw [Expr.dup_eq he, alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv),
    alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv1)]

/-- The block copy behind `declaration_dup`'s `.IndDecl` arm. -/
private theorem constant_infos_dup_loop_val (N : Nat) :
    ∀ (bl : alloc.vec.Vec env.ConstantInfo) (out r : alloc.vec.Vec env.ConstantInfo)
      (n i : Std.Usize),
      n.val = bl.val.length → n.val - i.val = N →
      frontend.export_c.constant_infos_dup_loop bl out n i = ok r →
      r.val = out.val ++ bl.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bl out r n i hn hN h
    rw [frontend.export_c.constant_infos_dup_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ci, hidx, c1, hc1, out1, hpush, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hdrop : bl.val.drop i.val = ci :: bl.val.drop (i.val + 1) := by
        have := vec_drop_map (v := bl) (i := i) (x := ci) id hidx
        simpa using this
      rw [ih (n.val - i1.val) (by scalar_tac) bl out1 r n i1 hn rfl h,
        vec_push_val hpush, Env.constant_info_dup_refines hc1, hi1v, hdrop]
      simp
    · rename_i hge
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by scalar_tac)]
      simp

/-- `export_c::constant_infos_dup` is the identity on a block. -/
theorem constant_infos_dup_refines {bl r : alloc.vec.Vec env.ConstantInfo}
    (h : frontend.export_c.constant_infos_dup bl = ok r) : r = bl := by
  rw [frontend.export_c.constant_infos_dup] at h
  have := constant_infos_dup_loop_val _ bl _ r _ 0#usize (alloc.vec.Vec.len_val _) rfl h
  refine alloc.vec.Vec.ext _ _ ?_
  rw [this]
  simp [alloc.vec.Vec.with_capacity, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- `export_c::declaration_dup` is the identity on a parsed record. -/
theorem declaration_dup_refines {d r : env.Declaration}
    (h : frontend.export_c.declaration_dup d = ok r) : r = d := by
  rw [frontend.export_c.declaration_dup.eq_def] at h
  cases d with
  | AxiomDecl cv =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv]
  | DefnDecl cv v hint =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv, v1, hv, h1, hh, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv, Expr.dup_eq hv,
      Env.reducibility_hint_dup_refines hh]
  | ThmDecl cv v =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv, v1, hv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv, Expr.dup_eq hv]
  | OpaqueDecl cv v =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv, v1, hv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv, Expr.dup_eq hv]
  | BasisDecl k =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨k1, hk, rfl⟩ := h
    rw [Env.basis_kind_dup_refines hk]
  | QuotDecl k cv =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨k1, hk, cv1, hcv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv]
    cases k <;> simp only [env.quot_kind_dup, Result.ok.injEq] at hk <;> rw [← hk]
  | IndDecl bl nP =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨bl1, hbl, rfl⟩ := h
    rw [constant_infos_dup_refines hbl]

/-! ## The fresh state and the result -/

/-- `export_c::state_d_init` refines `StateD.init`
(`ConLeche/Frontend/ExportC.lean:755-758`): the two singleton tables hold
`name::anonymous` and `level::zero`, and everything else is empty.  There is no
prelude here any more (con-leche task #293). -/
theorem state_d_init_refines {im ce : Bool} {st : frontend.export_c.StateD}
    (h : frontend.export_c.state_d_init im ce = ok st) :
    StateDRel st (ConLeche.Frontend.StateD.init im ce) := by
  rw [frontend.export_c.state_d_init] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, it, hit, l, hl, it1, hit1, it2, hit2, hm, hhm, hm1, hhm1,
    hm2, hhm2, hm3, hhm3, hm4, hhm4, hm5, hhm5, rfl⟩ := h
  refine ⟨?_, ?_, id_table_empty_refines hit2, by simp [ConLeche.Frontend.StateD.init, alloc.vec.Vec.new], ?_,
    State.new_inv hhm, State.new_keys hhm, ?_, State.new_inv hhm1, State.new_keys hhm1,
    by simp [ConLeche.Frontend.StateD.init, alloc.vec.Vec.new], ?_, State.new_inv hhm2, State.new_keys hhm2,
    ?_, State.new_inv hhm3, State.new_keys hhm3, by simp [ConLeche.Frontend.StateD.init],
    by simp [ConLeche.Frontend.StateD.init, alloc.vec.Vec.new], by simp [ConLeche.Frontend.StateD.init], ?_,
    State.new_inv hhm4, State.new_keys hhm4, by simp [ConLeche.Frontend.StateD.init],
    ?_, State.new_inv hhm5, State.new_keys hhm5, by simp [ConLeche.Frontend.StateD.init],
    by simp [ConLeche.Frontend.StateD.init, alloc.vec.Vec.new]⟩
  · have := id_table_singleton_refines (A := absName) hit
    rwa [Name.anonymous_refines hn] at this
  · have := id_table_singleton_refines (A := absLevel) hit1
    rwa [Level.zero_refines hl] at this
  · exact State.new_rel hhm
  · exact State.new_rel hhm1
  · exact State.new_rel hhm2
  · exact State.new_rel hhm3
  · exact State.new_rel hhm4
  · exact State.new_rel hhm5

/-- `export_c::parse_result_of_state` refines `ParseResultD.ofState`
(`ConLeche/Frontend/ExportC.lean:760-763`), field for field.  con-leche's
seventh field `inModelGen` is the dump's and has no port counterpart (the same
documented deviation as `StateD`'s), so no clause is claimed for it. -/
theorem parse_result_of_state_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {r : frontend.export_c.ParseResultD}
    (hrel : StateDRel st lst) (h : frontend.export_c.parse_result_of_state st = ok r) :
    r.decls.val.map absDeclaration
        = (ConLeche.Frontend.ParseResultD.ofState lst).decls.toList ∧
      r.proj_rewrites.val.map absName
        = (ConLeche.Frontend.ParseResultD.ofState lst).projRewrites.toList ∧
      r.in_modelled.val.map absName
        = (ConLeche.Frontend.ParseResultD.ofState lst).inModelled.toList ∧
      r.gen_records.val = (ConLeche.Frontend.ParseResultD.ofState lst).genRecords ∧
      HashMap.RelOn NameWF r.gen_owner
        (ConLeche.Frontend.ParseResultD.ofState lst).genOwner absName absName ∧
      r.in_model_declined.val.map absNameStr
        = (ConLeche.Frontend.ParseResultD.ofState lst).inModelDeclined.toList := by
  rw [frontend.export_c.parse_result_of_state] at h
  rw [← Result.ok_injective h]
  exact ⟨hrel.decls, hrel.projRewrites, hrel.inModelled, hrel.genRecords, hrel.genOwner,
    hrel.inModelDeclined⟩

/-! ## The modeller's window on the state

`export_c::state_model_ctx` against `ExportC.lean:603-607`'s
`let ctx : InModel.Ctx := ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0,
fun n => st.indBlocks[n]?⟩`.  con-leche's `Ctx` holds three *functions* where
the port holds three borrowed `ron::HashMap`s, so the bridge is stated at the
lookup — and, as everywhere at a `Name` key, only for well-formed names
(`Refine/HashMapWF.lean`'s note). -/

/-- `in_model_rec::ModelCtx` denotes `InModel.Ctx`. -/
structure CtxRel (c : frontend.in_model_rec.ModelCtx)
    (lc : ConLeche.Frontend.InModel.Ctx) : Prop where
  tbl : ∀ n, NameWF n → (HashMap.toFun c.tbl n).map absNamesExpr = lc.tbl (absName n)
  tblInv : HashMap.Inv State.hName c.tbl
  tblKeys : HashMap.KeysOk NameWF c.tbl
  heights : ∀ n, NameWF n →
    ((HashMap.toFun c.heights n).map absU64).getD 0 = lc.heights (absName n)
  heightsInv : HashMap.Inv State.hName c.heights
  heightsKeys : HashMap.KeysOk NameWF c.heights
  blocks : ∀ n, NameWF n → (HashMap.toFun c.blocks n).map absBlockRec = lc.blocks (absName n)
  blocksInv : HashMap.Inv State.hName c.blocks
  blocksKeys : HashMap.KeysOk NameWF c.blocks

/-- `export_c::state_model_ctx` refines the cited `let ctx := ⟨…, …, …⟩`
(`ConLeche/Frontend/ExportC.lean:603-607`). -/
theorem state_model_ctx_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {c : frontend.in_model_rec.ModelCtx}
    (hrel : StateDRel st lst) (h : frontend.export_c.state_model_ctx st = ok c) :
    CtxRel c ⟨fun n => lst.constTypes[n]?, fun n => lst.heights.getD n 0,
      fun n => lst.indBlocks[n]?⟩ := by
  rw [frontend.export_c.state_model_ctx] at h
  rw [← Result.ok_injective h]
  refine ⟨fun n hn => hrel.constTypes n hn, hrel.constTypesInv, hrel.constTypesKeys,
    ?_, hrel.heightsInv, hrel.heightsKeys, fun n hn => hrel.indBlocks n hn,
    hrel.indBlocksInv, hrel.indBlocksKeys⟩
  intro n hn
  rw [hrel.heights n hn]
  show lst.heights[absName n]?.getD 0 = lst.heights.getD (absName n) 0
  rw [_root_.Std.HashMap.getD_eq_getD_getElem?]

/-! ## The syntactic Π-telescope length

`export_c::ind_pi_tele_len` against `indPiTeleLen`
(`ConLeche/Frontend/ExportC.lean:338-344`).  con-leche recurses on the
expression; the port walks it with an owning step function (`ind_pi_body`,
task #13's fix for AENEAS_FINDINGS §2.1's F1), so the proof is structural
induction on the *argument*, which for a `partial_fixpoint` loop is the only
induction there is (`Refine/Abs.lean`'s note). -/

/-- The accumulator of `export_c::ind_pi_tele_len`'s walk. -/
private theorem ind_pi_tele_len_loop_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (k r : Std.U64), frontend.export_c.ind_pi_tele_len_loop k e = ok r →
      r.val = k.val + ConLeche.Frontend.indPiTeleLen (absExpr e) := by
  induction e, he using ExprWF.ind_node with
  | forall_e d ty b m h ihty ihb =>
    intro k r hrun
    rw [frontend.export_c.ind_pi_tele_len_loop.eq_def] at hrun
    simp only [core_k.is_forall, frontend.export_c.ind_pi_body, arc_deref_eq, bind_tc_ok,
      ExprOps.node_kind, if_true, bind_eq_ok_iff] at hrun
    obtain ⟨cur1, hcur, k1, hk1, hrun⟩ := hrun
    have hcb : cur1 = b := Expr.dup_eq hcur
    subst hcb
    have hk1v : k1.val = k.val + 1 := HashMap.uscalar_add_eq hk1
    rw [ihb (ExprWF.forall_e_kids h).2.1 k1 r hrun, hk1v]
    simp only [absExpr_mk, absExprKind, ConLeche.Frontend.indPiTeleLen]
    omega
  | _ =>
    intro k r hrun
    rw [frontend.export_c.ind_pi_tele_len_loop.eq_def] at hrun
    simp only [core_k.is_forall, arc_deref_eq, bind_tc_ok, ExprOps.node_kind,
      Bool.false_eq_true, if_false, Result.ok.injEq] at hrun
    rw [← hrun]
    simp only [absExpr_mk, absExprKind, ConLeche.Frontend.indPiTeleLen]
    omega

/-- `export_c::ind_pi_tele_len` refines `indPiTeleLen`
(`ConLeche/Frontend/ExportC.lean:338-344`). -/
theorem ind_pi_tele_len_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : frontend.export_c.ind_pi_tele_len e = ok r) :
    r.val = ConLeche.Frontend.indPiTeleLen (absExpr e) := by
  rw [frontend.export_c.ind_pi_tele_len] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨cur, hcur, h⟩ := h
  have hce : cur = e := Expr.dup_eq hcur
  subst hce
  rw [ind_pi_tele_len_loop_refines he 0#u64 r h]
  simp

/-! ### The three accessors

`export_c::state_const_type`/`state_height`/`state_ind_block` are the three
readings `ExportC.lean:603-607` writes inline; the port makes them accessors
because the modeller is outside the core and `StateD` is not part of its
interface (`export_c.rs`'s note). -/

/-- `export_c::state_const_type` refines the cited `fun n => st.constTypes[n]?`. -/
theorem state_const_type_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {n : name.Name}
    {o : Option ((alloc.vec.Vec name.Name) × expr.Expr)}
    (hrel : StateDRel st lst) (hn : NameWF n)
    (h : frontend.export_c.state_const_type st n = ok o) :
    o.map absNamesExpr = lst.constTypes[absName n]? := by
  rw [frontend.export_c.state_const_type] at h
  exact HashMap.Rel_get_wf State.nameKey.eq2 hrel.constTypesInv hrel.constTypesKeys
    hrel.constTypes hn h

/-- `export_c::state_height` refines the cited `fun n => st.heights.getD n 0`. -/
theorem state_height_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {n : name.Name} {r : Std.U64}
    (hrel : StateDRel st lst) (hn : NameWF n)
    (h : frontend.export_c.state_height st n = ok r) :
    r.val = lst.heights.getD (absName n) 0 := by
  rw [frontend.export_c.state_height] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  have hget := HashMap.Rel_get_wf State.nameKey.eq2 hrel.heightsInv hrel.heightsKeys
    hrel.heights hn ho
  rw [_root_.Std.HashMap.getD_eq_getD_getElem?, ← hget]
  cases o with
  | none => rw [← Result.ok_injective h]; simp
  | some hv => rw [← Result.ok_injective h]; simp

/-- `export_c::state_ind_block` refines the cited `fun n => st.indBlocks[n]?`. -/
theorem state_ind_block_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {n : name.Name}
    {o : Option frontend.in_model_rec.BlockRec}
    (hrel : StateDRel st lst) (hn : NameWF n)
    (h : frontend.export_c.state_ind_block st n = ok o) :
    o.map absBlockRec = lst.indBlocks[absName n]? := by
  rw [frontend.export_c.state_ind_block] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, ho, h⟩ := h
  have hget := HashMap.Rel_get_wf State.nameKey.eq2 hrel.indBlocksInv hrel.indBlocksKeys
    hrel.indBlocks hn ho
  cases o1 with
  | none => simp only [] at h; rw [← Result.ok_injective h]; simpa using hget
  | some p => simp only [arc_deref_eq, bind_tc_ok, Result.ok.injEq] at h
              rw [← h]; simpa using hget

/-! ### The remaining field updates

`StateDRel`'s other eleven clauses, as one-step lemmas: what a line function
needs to carry the relation across a write it makes.  Each is the record update
plus the one clause that moved (`Refine/State.lean`'s `insert_step` pattern). -/

theorem StateDRel.projOwners_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {m : ron.hashmap.HashMap name.Name frontend.proj_rec.ProjRecOwner}
    {lm : _root_.Std.HashMap ConLeche.Name ConLeche.Frontend.ProjRecOwner}
    (hrel : StateDRel st lst) (hr : HashMap.RelOn NameWF m lm absName absProjOwner)
    (hi : HashMap.Inv State.hName m) (hk : HashMap.KeysOk NameWF m) :
    StateDRel { st with proj_owners := m } { lst with projOwners := lm } :=
  { hrel with projOwners := hr, projOwnersInv := hi, projOwnersKeys := hk }

theorem StateDRel.projLevels_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {m : ron.hashmap.HashMap name.Name level.Level}
    {lm : _root_.Std.HashMap ConLeche.Name ConLeche.Level}
    (hrel : StateDRel st lst) (hr : HashMap.RelOn NameWF m lm absName absLevel)
    (hi : HashMap.Inv State.hName m) (hk : HashMap.KeysOk NameWF m) :
    StateDRel { st with proj_levels := m } { lst with projLevels := lm } :=
  { hrel with projLevels := hr, projLevelsInv := hi, projLevelsKeys := hk }

theorem StateDRel.genOwner_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {m : ron.hashmap.HashMap name.Name name.Name}
    {lm : _root_.Std.HashMap ConLeche.Name ConLeche.Name}
    (hrel : StateDRel st lst) (hr : HashMap.RelOn NameWF m lm absName absName)
    (hi : HashMap.Inv State.hName m) (hk : HashMap.KeysOk NameWF m) :
    StateDRel { st with gen_owner := m } { lst with genOwner := lm } :=
  { hrel with genOwner := hr, genOwnerInv := hi, genOwnerKeys := hk }

theorem StateDRel.indBlocks_update {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {m : ron.hashmap.HashMap name.Name (alloc.sync.Arc frontend.in_model_rec.BlockRec)}
    {lm : _root_.Std.HashMap ConLeche.Name ConLeche.Frontend.InModel.BlockRec}
    (hrel : StateDRel st lst) (hr : HashMap.RelOn NameWF m lm absName absBlockRec)
    (hi : HashMap.Inv State.hName m) (hk : HashMap.KeysOk NameWF m) :
    StateDRel { st with ind_blocks := m } { lst with indBlocks := lm } :=
  { hrel with indBlocks := hr, indBlocksInv := hi, indBlocksKeys := hk }

theorem StateDRel.projRewrites_push {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {v : alloc.vec.Vec name.Name} {n : name.Name}
    (hrel : StateDRel st lst) (h : alloc.vec.Vec.push st.proj_rewrites n = ok v) :
    StateDRel { st with proj_rewrites := v }
      { lst with projRewrites := lst.projRewrites.push (absName n) } :=
  { hrel with projRewrites := by rw [vec_push_val h]; simp [hrel.projRewrites] }

theorem StateDRel.inModelled_push {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {v : alloc.vec.Vec name.Name} {n : name.Name}
    (hrel : StateDRel st lst) (h : alloc.vec.Vec.push st.in_modelled n = ok v) :
    StateDRel { st with in_modelled := v }
      { lst with inModelled := lst.inModelled.push (absName n) } :=
  { hrel with inModelled := by rw [vec_push_val h]; simp [hrel.inModelled] }

theorem StateDRel.inModelDeclined_push {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {v : alloc.vec.Vec (name.Name × (alloc.vec.Vec Std.U32))}
    {p : name.Name × (alloc.vec.Vec Std.U32)}
    (hrel : StateDRel st lst) (h : alloc.vec.Vec.push st.in_model_declined p = ok v) :
    StateDRel { st with in_model_declined := v }
      { lst with inModelDeclined := lst.inModelDeclined.push (absNameStr p) } :=
  { hrel with inModelDeclined := by rw [vec_push_val h]; simp [hrel.inModelDeclined] }

theorem StateDRel.genRecords_step {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {g : Std.U64}
    (hrel : StateDRel st lst) (h : st.gen_records + 1#u64 = ok g) :
    StateDRel { st with gen_records := g } { lst with genRecords := lst.genRecords + 1 } :=
  { hrel with genRecords := by rw [HashMap.uscalar_add_eq h, hrel.genRecords]; rfl }

theorem StateDRel.indCount_step {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {c : Std.U64}
    (hrel : StateDRel st lst) (h : st.ind_count + 1#u64 = ok c) :
    StateDRel { st with ind_count := c } { lst with indCount := lst.indCount + 1 } :=
  { hrel with indCount := by rw [HashMap.uscalar_add_eq h, hrel.indCount]; rfl }

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing here reaches past con-leche's own three axioms.  `parse_expr_rec_d_refines`
carries `NatValSpec` as a *hypothesis*, not as an axiom, so it spends nothing
either. -/

/--
info: 'ConRon.Refine.Frontend.parse_expr_rec_d_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parse_expr_rec_d_refines

/--
info: 'ConRon.Refine.Frontend.push_decl_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms push_decl_refines

/--
info: 'ConRon.Refine.Frontend.state_d_init_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms state_d_init_refines

end ConRon.Refine.Frontend
