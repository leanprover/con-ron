/-
# `ConRon.Refine2.Frontend.ExportC` — the readers and the record builders

**Task #97-P5-Frontend**, the first of `frontend/export_c.rs`'s three files:
the error channel's four constructors, the parse state, the index-table
readers, the value builders, the projection hooks and the modeller's booking
— seventy-nine statements over seventy-six of the module's one hundred and
eighteen `pub fn`s (fifteen of them finding 17's no-claims).
`Refine2/Frontend/ExportCInd.lean` has the inductive record's validation and
install, `Refine2/Frontend/ExportCLine.lean` the line layer and the chunk
drivers.

## The one convention this file fixes for the whole module

**The `StateD` readers are `SimLR`, the writers `SimD`.**  `st_name`,
`st_level`, `st_expr`, `get_decl_d`, `parse_cv_d`, `parse_rule_d` take the
state by shared reference and return a value or a `LineErr`; `note_decl`,
`push_decl`, `parse_*_entry_d` take it by `&mut` and return `()`.  The port's
`&mut StateD` is Aeneas's return value, so the second family's outcome is
`(Result () LineErr) × AState × StateD`, which is `SimD`.

## `sorry` count in this file: 26
-/
import ConRon.Refine2.Frontend.ProjRec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IdTable NameRec LevelRec ExprRec PwRec CVRec HintsRec RuleRec
  IndTypeRec IndCtorRec IndRecRec DeclRec LineRec)

/-! ## The error channel's four constructors

`fail`, `merr`, `declined` and `invalid` are the port's only routes into
`LineErr`.  `fail` carries a whole `CheckError` — `EStore::intern` declines
with `Native` at the `2 ^ 27` cap and that KIND has to reach the exit code
(`export_c.rs`'s deviation 1) — and the other three build one. -/

/-- **`export_c::fail`** — the twin's `fail e`, kind for kind. -/
theorem fail_refines {T : Type} {e o} (h : frontend.export_c.fail T e = ok o) :
    ∃ e', o = .Err (.Err e') ∧ absAErrKind e' = absAErrKind e := by
  rw [frontend.export_c.fail] at h
  simp only [Result.ok.injEq] at h
  exact ⟨e, h.symm, rfl⟩

/-- **`export_c::merr`** — an `internal` message. -/
theorem merr_refines {T : Type} {msg o} (h : frontend.export_c.merr T msg = ok o) :
    ∃ m, o = .Err (.Err (.Internal m)) := by
  rw [frontend.export_c.merr] at h
  obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [kernel.core_types.internal] at hce
  simp only [Result.ok.injEq] at hce h
  exact ⟨msg, by rw [← h, ← hce]⟩

/-- **`export_c::declined`** — a positive DECLINE verdict. -/
theorem declined_refines {T : Type} {what o}
    (h : frontend.export_c.declined T what = ok o) :
    ∃ m, o = .Err (.Verdict (.Declined m)) := by
  rw [frontend.export_c.declined] at h
  simp only [Result.ok.injEq] at h
  exact ⟨what, h.symm⟩

/-- **`export_c::invalid`** — a REJECT verdict. -/
theorem invalid_refines {T : Type} {what o}
    (h : frontend.export_c.invalid T what = ok o) :
    ∃ m, o = .Err (.Verdict (.Invalid m)) := by
  rw [frontend.export_c.invalid] at h
  simp only [Result.ok.injEq] at h
  exact ⟨what, h.symm⟩

/-- **`line_err_to_check` refines `RecordVerdict.toError` composed with the
line number**: the pair the chunk drivers' error channel carries. -/
theorem line_err_to_check_refines {e line_no o}
    (h : frontend.export_c.line_err_to_check e line_no = ok o) :
    absU o.2 = absU line_no ∧
      (∀ ce, e = .Err ce → absAErrKind o.1 = absAErrKind ce) ∧
      (∀ v lv, e = .Verdict v → lVerdictKind lv = absVerdictKind v →
        absAErrKind o.1 = lAErrKind lv.toError) := by
  rw [frontend.export_c.line_err_to_check.eq_def] at h
  cases e with
  | Err ce =>
    cases Result.ok_injective h
    exact ⟨rfl, fun ce' he => (by cases he; rfl), fun v lv he => (by cases he)⟩
  | Verdict v =>
    obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    refine ⟨rfl, fun ce' he => (by cases he), fun v' lv he hk => ?_⟩
    cases he
    exact record_verdict_to_error_refines hk hce

/-! ## `text::cps_beq` — a spelling against a literal

Ported from `RefineOld/Frontend/IndR.lean` (task #87 §8) by task #97-P5-Front
round 2: list equality of the code points, and — on a `StrWF` payload and a
literal of valid code points — equality of the abstracted strings. -/

theorem slice_index_some {α : Type} {s : Slice α} {i : Std.Usize} {x : α}
    (h : Slice.index_usize s i = ok x) : s.val[i.val]? = some x := by
  rw [Slice.index_usize] at h
  have hb : s[i]? = s.val[i.val]? := rfl
  rcases hi : s.val[i.val]? with _ | y
  · rw [hb, hi] at h; simp at h
  · rw [hb, hi] at h
    exact congrArg some (Result.ok_injective h)

theorem cps_beq_loop_val (N : Nat) :
    ∀ (s : alloc.vec.Vec Std.U32) (lit : Slice Std.U32) (n i : Std.Usize) (b : Bool),
      s.val.length - i.val = N → n.val = s.val.length → s.val.length = lit.val.length →
      frontend.text.cps_beq_loop s lit n i = ok b →
      (b = true ↔ s.val.drop i.val = lit.val.drop i.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s lit n i b hN hn hlen h
    rw [frontend.text.cps_beq_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < s.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hcv : s.val[i.val]'(by omega) = c := by
        have hg := vec_index_some hc
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hc2v : lit.val[i.val]'(by omega) = c2 := by
        have hg := slice_index_some hc2
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hds : s.val.drop i.val = c :: s.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (show i.val < s.val.length by omega), hcv]
      have hdl : lit.val.drop i.val = c2 :: lit.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (show i.val < lit.val.length by omega), hc2v]
      rw [hds, hdl]
      split at h
      · rename_i hne
        simp only [Result.ok.injEq] at h
        have hval : ¬ (c.val = c2.val) := by simpa using hne
        have hcc : c ≠ c2 := fun hq => hval (congrArg Std.UScalar.val hq)
        simp [← h, hcc]
      · rename_i hne
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi2
        have hceq : c = c2 := Std.UScalar.val_eq_imp_iff.mpr (by simpa using hne)
        rw [ih (s.val.length - i2.val) (by omega) s lit n i2 b rfl hn hlen h, hi2v]
        simp [hceq]
    · rename_i hge
      have hle : s.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      simp

/-- `text::cps_beq` is list equality of the code points. -/
theorem cps_beq_val {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
    (h : frontend.text.cps_beq s lit = ok b) : (b = true ↔ s.val = lit.val) := by
  rw [frontend.text.cps_beq] at h
  split at h
  · rename_i hne
    have hl : s.val.length ≠ lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    simp only [Result.ok.injEq] at h
    refine ⟨fun hb => absurd (h ▸ hb) (by simp), fun he => ?_⟩
    exact absurd (congrArg List.length he) hl
  · rename_i hne
    have hl : s.val.length = lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    have hh := cps_beq_loop_val _ s lit _ 0#usize b rfl (by simp [alloc.vec.Vec.len]) hl h
    simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- A scanned spelling equals a literal exactly when `cps_beq` says so. -/
theorem cps_beq_str {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
    (hs : ConRon.Refine.StrWF s) (hL : ∀ c ∈ lit.val, Nat.isValidChar c.val)
    (h : frontend.text.cps_beq s lit = ok b) :
    (b = true ↔ ConRon.Refine.absString s = String.ofList (lit.val.map fun c => Char.ofNat c.val)) := by
  rw [cps_beq_val h]
  constructor
  · intro he; simp only [ConRon.Refine.absString, he]
  · intro he
    have hlen : lit.val.length ≤ Std.Usize.max := by scalar_tac
    have ht : ConRon.Refine.StrWF (alloc.vec.Vec.from lit.val hlen) := by
      intro c hc; exact hL c (by simpa using hc)
    have := ConRon.Refine.Name.absString_inj hs ht
      (by rw [he]; simp [ConRon.Refine.absString, alloc.vec.Vec.from_val])
    rw [this, alloc.vec.Vec.from_val]

/-- **The `"safe"` test of `process_line_core_d`'s `defn` arm.** -/
theorem safe_spelling_refines {s : alloc.vec.Vec Std.U32} {b : Bool}
    (hs : ConRon.Refine.StrWF s)
    (h : (do
        let sl ← lift (Std.Array.to_slice frontend.export_c.process_line_core_d.S_SAFE)
        frontend.text.cps_beq s sl) = ok b) :
    (b = true ↔ ConRon.Refine.absString s = "safe") := by
  simp only [lift, bind_tc_ok] at h
  have hv : (Std.Array.to_slice frontend.export_c.process_line_core_d.S_SAFE).val
      = [115#u32, 97#u32, 102#u32, 101#u32] := by
    unfold frontend.export_c.process_line_core_d.S_SAFE; rfl
  rw [cps_beq_str hs (by rw [hv]; decide) h, hv]
  rfl

/-! ## The message builders — fifteen functions with NO refinement claim

Every Rust error sentence is a `Vec<u32>` built from a function-local
`const M: [u32; N]` (DESIGN §3.3), where the twin writes `s!"…"`.  **The
theorem does not read messages** (DESIGN §3.1; task #87 §13's ruling, where
weakening a relation rather than strengthening a hypothesis was the fix), so
these fifteen carry nothing at all, and the two candidate statements both fail
to say anything:

* *"the message is the twin's"* is false and is the ruling's whole point;
* *"the builder succeeds"* is **not provable and not needed** — `text::cat`
  is a `Vec::extend_from_slice` loop, which Aeneas models as failing at
  `Usize.max`, and a failure inside one makes the CALLER's own
  `… = ok o` hypothesis unsatisfiable, so every caller is vacuously fine
  there.

So each of the fifteen is recorded as an explicit no-claim, named so that a
reader looking for `safety_error` finds the reason rather than a gap.  They
are counted as statements in this file's census and they are closed. -/

/-- `export_c::bool_str` builds a message; see the section note. -/
theorem bool_str_no_claim : True := trivial

/-- `export_c::rebound_error` builds a message; see the section note. -/
theorem rebound_error_no_claim : True := trivial

/-- `export_c::no_such_ctor_error` builds a message; see the section note. -/
theorem no_such_ctor_error_no_claim : True := trivial

/-- `export_c::ctor_count_error` builds a message; see the section note. -/
theorem ctor_count_error_no_claim : True := trivial

/-- `export_c::cidx_error` builds a message; see the section note. -/
theorem cidx_error_no_claim : True := trivial

/-- `export_c::induct_error` builds a message; see the section note. -/
theorem induct_error_no_claim : True := trivial

/-- `export_c::fields_error` builds a message; see the section note. -/
theorem fields_error_no_claim : True := trivial

/-- `export_c::rec_params_error` builds a message; see the section note. -/
theorem rec_params_error_no_claim : True := trivial

/-- `export_c::rec_motives_error` builds a message; see the section note. -/
theorem rec_motives_error_no_claim : True := trivial

/-- `export_c::rec_minors_error` builds a message; see the section note. -/
theorem rec_minors_error_no_claim : True := trivial

/-- `export_c::rec_k_error` builds a message; see the section note. -/
theorem rec_k_error_no_claim : True := trivial

/-- `export_c::rec_indices_error` builds a message; see the section note. -/
theorem rec_indices_error_no_claim : True := trivial

/-- `export_c::safety_error` builds a message; see the section note. -/
theorem safety_error_no_claim : True := trivial

/-- `export_c::quot_kind_error` builds a message; see the section note. -/
theorem quot_kind_error_no_claim : True := trivial

/-- `export_c::in_model_decline` builds a message; see the section note. -/
theorem in_model_decline_no_claim : True := trivial

/-! ## Two arithmetic helpers and the scanner's error -/

/-- **`sat_sub`** — saturating subtraction, the twin's `Nat` subtraction. -/
theorem sat_sub_refines {a b v} (h : frontend.export_c.sat_sub a b = ok v) :
    absU v = absU a - absU b := by
  rw [frontend.export_c.sat_sub] at h
  split at h
  · rename_i hge
    have := ConRon.Refine.Nat.usub_val h
    simp only [absU]
    omega
  · rename_i hlt
    simp only [Result.ok.injEq] at h
    subst h
    have hlt' : a.val < b.val := by scalar_tac
    have h0 : (0#u64 : Std.U64).val = 0 := rfl
    simp only [absU, h0]
    omega

/-- **`rel_offset`** — a scan error's offset, relative to the line's start.
The port saturates where the twin's `Nat` subtraction does. -/
theorem rel_offset_refines {off i v}
    (h : frontend.export_c.rel_offset off i = ok v) :
    v.val = off.val - i.val := by
  rw [frontend.export_c.rel_offset] at h
  split at h
  · rename_i hge
    have := ConRon.Refine.Nat.usub_val h
    omega
  · rename_i hlt
    simp only [Result.ok.injEq] at h
    subst h
    have hlt' : off.val < i.val := by scalar_tac
    have h0 : (0#usize : Std.Usize).val = 0 := rfl
    rw [h0]
    omega

/-- **`scan_err_to_check`** — the scanner's tag as a `CheckError`.  Task #87
§4's port bug is the reason this function exists: `ErrTag::IndexOverflow` is
spelled `Native` and every other tag `Internal`, so the port never claims the
twin throws on a stream the twin accepts. -/
theorem scan_err_to_check_refines {e ce}
    (h : frontend.export_c.scan_err_to_check e = ok ce) :
    (absErrTag e.what = none → absAErrKind ce = none) ∧
      (∀ t, absErrTag e.what = some t → absAErrKind ce = some .internal) := by
  rw [frontend.export_c.scan_err_to_check] at h
  rcases e with ⟨off, what⟩
  cases what <;> simp only at h <;>
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h <;>
    simp only [kernel.core_types.internal, kernel.core_types.native, Result.ok.injEq] at h <;>
    subst h <;> simp [absErrTag, absAErrKind]

theorem etables_count_abs {rt lt} (hrel : ETablesRel rt lt) {n : Std.Usize}
    (h : arena.store.ETables.count rt = ok n) : n.val = lt.count := by
  rw [arena.store.ETables.count] at h
  obtain ⟨a0, h0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s1, hs1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s2, hs2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a3, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s3, hs3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a4, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s4, hs4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a5, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s5, hs5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a6, h6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s6, hs6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a7, h7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s7, hs7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a8, h8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s8, hs8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨a9, h9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e0 := tbl_size_abs hrel.bvars h0
  have e1 := tbl_size_abs hrel.fvars h1
  have e2 := tbl_size_abs hrel.sorts h2
  have e3 := tbl_size_abs hrel.consts h3
  have e4 := tbl_size_abs hrel.apps h4
  have e5 := tbl_size_abs hrel.lams h5
  have e6 := tbl_size_abs hrel.foralls h6
  have e7 := tbl_size_abs hrel.lets h7
  have e8 := tbl_size_abs hrel.lits h8
  have e9 := tbl_size_abs hrel.projs h9
  have f1 := ConRon.Refine.Nat.uadd_val hs1
  have f2 := ConRon.Refine.Nat.uadd_val hs2
  have f3 := ConRon.Refine.Nat.uadd_val hs3
  have f4 := ConRon.Refine.Nat.uadd_val hs4
  have f5 := ConRon.Refine.Nat.uadd_val hs5
  have f6 := ConRon.Refine.Nat.uadd_val hs6
  have f7 := ConRon.Refine.Nat.uadd_val hs7
  have f8 := ConRon.Refine.Nat.uadd_val hs8
  have f9 := ConRon.Refine.Nat.uadd_val h
  show n.val = lt.bvars.size + lt.fvars.size + lt.sorts.size + lt.consts.size +
    lt.apps.size + lt.lams.size + lt.foralls.size + lt.lets.size + lt.lits.size +
    lt.projs.size
  omega

theorem estore_node_count_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {n : Std.Usize} (h : arena.store.EStore.node_count rs pers = ok n) :
    n.val = ls.nodeCount := by
  rw [arena.store.EStore.node_count] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ha' : a.val = ls.pers.count := by
    rw [arena.store.EStore.pers_count] at ha
    have hp := hrel.perst
    rw [rPersE] at hp
    split at ha <;> rename_i hs
    · rw [if_pos hs] at hp; exact etables_count_abs hp ha
    · rw [if_neg hs] at hp; exact etables_count_abs hp ha
  have hb' : b.val = ls.scr.count := by
    rw [arena.store.EStore.scr_count] at hb
    exact etables_count_abs hrel.scrt hb
  have h' := ConRon.Refine.Nat.uadd_val h
  show n.val = ls.pers.count + ls.scr.count
  omega

/-! ## The store fuel

The twin's `storeFuel` is the store's node count plus one, which bounds the
length of any path through it because a child is interned before its parent.
The port reads the same counter. -/

theorem store_fuel_refines {pers rst lst v}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.store_fuel pers rst.store = ok v) :
    SimR absU lst v storeFuel := by
  rw [frontend.export_c.store_fuel] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnv := estore_node_count_abs hrel.store hn
  have hcv : c.val = n.val := by
    simp only [lift, Result.ok.injEq] at hc; subst hc; exact usize_cast_u64_val' n
  have hv := ConRon.Refine.Nat.uadd_val h
  show Except.ok _ = _
  simp only [absU]
  rw [show v.val = lst.store.nodeCount + 1 by
    have : v.val = c.val + (1#u64 : Std.U64).val := hv
    rw [this, hcv, hnv]; rfl]

/-! ## The parse state -/

/-- `scan_types::id_table_singleton` refines `IdTable.singleton`
(`ConLeche/Frontend/Scan/Types.lean:361`): index 0 bound and nothing else. -/
theorem id_table_singleton_rel {T α : Type} {A : T → α} {x : T}
    {t : frontend.scan_types.IdTable T}
    (h : frontend.scan_types.id_table_singleton x = ok t) :
    IdTableRel A t (ConLeche.Frontend.IdTable.singleton (A x)) := by
  rw [frontend.scan_types.id_table_singleton] at h
  obtain ⟨dense, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap.new_refines (HashableInst := hU64) hm
  refine ⟨?_, ConRon.Refine.HashMap.RelOn_empty hnone, hinv⟩
  rw [ConRon.Refine.vec_push_val hd]; rfl

/-- `scan_types::id_table_empty` refines `IdTable`'s field defaults
(`ConLeche/Frontend/Scan/Types.lean:342-344`): the empty table. -/
theorem id_table_empty_rel {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T}
    (h : frontend.scan_types.id_table_empty T = ok t) :
    IdTableRel A t ({} : ConLeche.Frontend.IdTable α) := by
  rw [frontend.scan_types.id_table_empty] at h
  obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap.new_refines (HashableInst := hU64) hm
  exact ⟨rfl, ConRon.Refine.HashMap.RelOn_empty hnone, hinv⟩

/-- **`state_d_init` refines `StateD.init`** (`ExportC.lean:709-713`): index 0
of the name table is the format's implicit `Name.anonymous` and index 0 of the
level table its `Level.zero`, and over handles that means the handles those
two nodes intern at — in the PERSISTENT tier, which is the tier the whole
parse appends to.

Both arms (task #97-P5-Front restated it from a success-only statement, which
left `parse_bytes`/`parse_chunks` nothing to say about their `(e, 0)` arm).
The two interns are `Specs.lean`'s `estore_intern_name_abs` /
`estore_intern_level_abs` (no frozen hypothesis since task #97-P5-Unfreeze);
what is left is the nineteen-field `StateDRel` at the fresh record —
`IdTableRel` at a singleton and at `id_table_empty`, `RelOn` at six
`HashMap2::new`s (`Refine/HashMap2.lean`'s `new_refines`), and `StateDInv`. -/
theorem state_d_init_refines {pers rst lst in_model census o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.state_d_init pers rst.store in_model census = ok o) :
    SimRel₀ (fun rsd lsd => StateDRel rsd lsd ∧ StateDInv rsd) pers lst
      (o.1, withStore rst o.2) (StateD.init in_model census) := by
  rw [frontend.export_c.state_d_init] at h
  obtain ⟨⟨r, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hS1 := ConRon.Refine2.intern_n_node_run₀ hrel hinv .Anonymous trivial
    (o := (r, withStore rst ar1))
    (by rw [arena.monad.intern_n_node, h1]; simp only [bind_tc_ok]; rfl)
  simp only [Sim₀, absNNodeView] at hS1
  simp only [SimRel₀, StateD.init, am_run_bind']
  cases r with
  | Err e =>
    have ho := Result.ok_injective h; subst ho
    exact AErrSim.bind (AOut₀.destErr hS1) _
  | Ok n0 =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hS1
    rw [hx1]
    simp only [except_ok_bind]
    obtain ⟨⟨r2, ar2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS2 := ConRon.Refine2.intern_l_node_run₀ hrel1 hinv1 .Zero
      (o := (r2, withStore rst ar2))
      (by rw [arena.monad.intern_l_node]; rw [h2]
          simp only [bind_tc_ok]; rfl)
    simp only [Sim₀, absLNodeView] at hS2
    cases r2 with
    | Err e =>
      have ho := Result.ok_injective h; subst ho
      exact AErrSim.bind (AOut₀.destErr hS2) _
    | Ok l0 =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hS2
      rw [hx2]
      simp only [except_ok_bind]
      obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨it1, hit1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨it2, hit2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hm1, hhm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hm2, hhm2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hm3, hhm3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hm4, hhm4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hm5, hhm5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ho := Result.ok_injective h; subst ho
      obtain ⟨i0, -, n0'⟩ := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm
      obtain ⟨i1, -, n1'⟩ := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm1
      obtain ⟨i2, -, n2'⟩ := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm2
      obtain ⟨i3, -, n3'⟩ := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm3
      obtain ⟨i4, -, n4'⟩ := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm4
      obtain ⟨i5, -, n5'⟩ := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm5
      refine ⟨_, lst2, rfl, ⟨⟨id_table_singleton_rel hit, id_table_singleton_rel hit1,
        id_table_empty_rel hit2, rfl,
        ConRon.Refine.HashMap2.RelOn_empty n0', ConRon.Refine.HashMap2.RelOn_empty n1', rfl,
        ConRon.Refine.HashMap2.RelOn_empty n2', ConRon.Refine.HashMap2.RelOn_empty n3', rfl,
        rfl, rfl, ConRon.Refine.HashMap2.RelOn_empty n4', rfl, rfl,
        ConRon.Refine.HashMap2.RelOn_empty n5', rfl, by simp⟩,
        ⟨i0, i1, i2, i3, i4, i5⟩⟩, hrel2, hinv2⟩

/-- **`state_model_ctx`** — the three tables the modeller reads, borrowed off
the state (`types::ModelCtx`'s deviation).  The twin builds the three closures
inline in `installIndD`; this is `CtxRel` at them. -/
theorem state_model_ctx_refines {rsd lsd rc} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd) (h : frontend.export_c.state_model_ctx rsd = ok rc) :
    CtxRel rc ⟨fun n => lsd.constTypes[n]?, fun n => lsd.heights.getD n 0,
      fun n => lsd.indBlocks[n]?⟩ := by sorry

/-! ## The twin's `noteDecl`, split, and the port's `toConstantVal`

Task #97-P5-Front round 3.  `noteDecl` is `noteEntries ∘ noteDeclEntries`
(`Spec.lean`'s `noteDecl_unfold`), `noteEntries` touches `constTypes` and
`heights` only, and `pushDecl` is therefore `noteDecl` with the record
appended — the port does the two in the other order (`note_decl` first, then
the push, so that a failing record is not pushed), which the twin cannot
observe: `noteDecl` never reads `decls`, and on a failure the twin throws.
`arena::env::i_constant_info_to_constant_val` is `toConstantVal` arm for arm,
including the `.projInfo` arm's three interns in the same order. -/

theorem noteEntries_decls (st : StateD) (X : Array IDeclaration) es :
    noteEntries { st with decls := X } es = { noteEntries st es with decls := X } := rfl

theorem noteEntries_nil (st : StateD) : noteEntries st [] = st := rfl

theorem noteEntries_cons (st : StateD) x xs :
    noteEntries st (x :: xs) = noteEntries (noteEntries st [x]) xs := rfl

theorem noteEntries_single (st : StateD) (n : NIdx) (lps : List NIdx) (ty : EIdx)
    (h : Option Nat) :
    noteEntries st [(n, lps, ty, h)] =
      { st with constTypes := st.constTypes.insert n (lps, ty),
                heights := match h with
                  | some h => st.heights.insert n h
                  | none => st.heights } := by
  cases h <;> rfl

/-- `pushDecl` is `noteDecl` with the record appended to `decls`. -/
theorem pushDecl_run (st : StateD) (d : IDeclaration) (lst : AState) :
    (pushDecl st d).run lst = ((noteDecl st d).run lst).map
      (fun p => ({ p.1 with decls := st.decls.push d }, p.2)) := by
  rw [pushDecl, noteDecl_unfold, noteDecl_unfold, am_run_bind', am_run_bind']
  cases (noteDeclEntries d).run lst <;> rfl

theorem noteDecl_run_decls {st st' : StateD} {d : IDeclaration} {lst lst' : AState}
    (h : (noteDecl st d).run lst = .ok (st', lst')) : st'.decls = st.decls := by
  rw [noteDecl_unfold, am_run_bind'] at h
  revert h
  cases (noteDeclEntries d).run lst with
  | error e => intro h; cases h
  | ok p => intro h; cases h; rfl

theorem AErrSim.of_kind {γ : Type} {e e' : kernel.core_types.CheckError}
    {x : Except Arena.CheckError γ} (h : AErrSim e x)
    (hk : absAErrKind e' = absAErrKind e) : AErrSim e' x := by
  intro k hk'; exact h k (hk ▸ hk')

/-- **`arena::env::i_constant_info_to_constant_val` refines
`IConstantInfo.toConstantVal`** (`Arena/Env.lean:222-229`): six arms are a
copy, the `.projInfo` arm interns `Sort 1` in both, in the same order. -/
theorem i_constant_info_to_constant_val_refines {pers rst lst c o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : arena.env.i_constant_info_to_constant_val pers rst.store c = ok o) :
    Sim₀ absIConstantVal pers lst (o.1, withStore rst o.2)
      (absIConstantInfo c).toConstantVal := by
  have plain : ∀ v iv, arena.env.i_constant_val_dup v = ok iv →
      o = (.Ok iv, rst.store) →
      (absIConstantInfo c).toConstantVal = pure (absIConstantVal v) →
      Sim₀ absIConstantVal pers lst (o.1, withStore rst o.2)
        (absIConstantInfo c).toConstantVal := by
    intro v iv hiv ho hx
    subst ho
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hx, i_constant_val_dup_abs hiv]; rfl
  cases c with
  | AxiomInfo v =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | DefnInfo v _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | ThmInfo v _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | IndInfo v _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | CtorInfo v _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | RecInfo v _ _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | ProjInfo tbl =>
    clear plain
    simp only [arena.env.i_constant_info_to_constant_val] at h
    show AOut₀ _ _ _ _ _
    simp only [absIConstantInfo, IConstantInfo.toConstantVal]
    -- 1. the level `0`
    obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS1 := intern_l_node_run₀ hrel hinv arena.store.LNodeView.Zero
      (o := (r1, withStore rst ar1))
      (by rw [arena.monad.intern_l_node, h1]; simp only [bind_tc_ok]; rfl)
    rw [show Arena.internLNode LNodeView.zero
        = Arena.internLNode (absLNodeView arena.store.LNodeView.Zero) from rfl]
    cases r1 with
    | Err e =>
      have ho := Result.ok_injective h
      subst ho
      exact AOut₀.errBind hS1
    | Ok z =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
    rw [run_bind_ok hx1]
    -- 2. the level `1`
    obtain ⟨⟨r2, ar2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS2 := intern_l_node_run₀ hrel1 hinv1 (arena.store.LNodeView.Succ z)
      (o := (r2, withStore rst ar2))
      (by rw [arena.monad.intern_l_node]; rw [h2]; simp only [bind_tc_ok]; rfl)
    rw [show Arena.internLNode (.succ (absLIdx z))
        = Arena.internLNode (absLNodeView (arena.store.LNodeView.Succ z)) from rfl]
    cases r2 with
    | Err e =>
      have ho := Result.ok_injective h
      subst ho
      exact AOut₀.errBind hS2
    | Ok one =>
    obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
    rw [run_bind_ok hx2]
    -- 3. the expression `Sort 1`
    obtain ⟨⟨r3, ar3⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS3 := intern_e_sort_run₀ hrel2 hinv2 one
      (o := (r3, withStore rst ar3))
      (by rw [arena.monad.intern_e_sort]
          rw [show arena.store.EStore.intern_sort (withStore rst ar2).store pers one
              = arena.store.EStore.intern ar2 pers (arena.store.ENodeView.Sort one) from rfl,
            h3]
          simp only [bind_tc_ok]; rfl)
    rw [show Arena.internE (.sort (absLIdx one)) = Arena.internSortE (absLIdx one) from rfl]
    cases r3 with
    | Err e =>
      have ho := Result.ok_injective h
      subst ho
      exact AOut₀.errBind hS3
    | Ok ty =>
    obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
    rw [run_bind_ok hx3]
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ho := Result.ok_injective h
    subst ho
    refine AOut₀.ok (lst' := lst3) ?_ hrel3 hinv3
    show Except.ok _ = _
    simp only [absIConstantVal, absIProjTable, dupId_nidx _ _ hn, nidx_vec_dup_val hv]

/-! ## Booking a pushed record -/

/-- **`note_one`** — one constant's entry. -/
theorem note_one_refines {cv h' v} (h : frontend.export_c.note_one cv h' = ok v) :
    absNoteEntryL v =
      [(absNIdx cv.name, cv.level_params.val.map absNIdx, absEIdx cv.ty,
        h'.map absU)] := by
  rw [frontend.export_c.note_one] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [absNoteEntryL, ConRon.Refine.vec_push_val h]
  have e0 : (alloc.vec.Vec.with_capacity (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx)
      × arena.handle.EIdx × (Option Std.U64)) 1#usize).val = [] := rfl
  rw [e0, dupId_nidx _ _ hn, dupId_eidx _ _ he]
  simp [absNoteEntry, nidx_vec_dup_val hv1]

/-- The loop of `note_block`, at a cursor. -/
theorem note_block_loop_refines {pers : arena.store.PersTier}
    {bl : alloc.vec.Vec arena.env.IConstantInfo} :
    ∀ (k : Std.Usize) (out : alloc.vec.Vec (arena.handle.NIdx ×
        (alloc.vec.Vec arena.handle.NIdx) × arena.handle.EIdx × (Option Std.U64)))
      {rst lst o}, AStateRel₀ pers rst lst → AStateInv pers rst →
      frontend.export_c.note_block_loop pers rst.store bl out (alloc.vec.Vec.len bl) k
        = ok o →
      SimL absNoteEntryL pers lst (o.1, withStore rst o.2)
        (do
          let es ← (absICILFrom bl k).mapM fun ci => do
            let v ← ci.toConstantVal
            pure (v.name, v.levelParams, v.type, (none : Option Nat))
          pure (absNoteEntryL out ++ es)) := by
  refine cursor_induction (fun k : Std.Usize => k.val) bl.val.length
    (fun k out => ∀ {rst lst o}, AStateRel₀ pers rst lst → AStateInv pers rst →
      frontend.export_c.note_block_loop pers rst.store bl out (alloc.vec.Vec.len bl) k
        = ok o →
      SimL absNoteEntryL pers lst (o.1, withStore rst o.2)
        (do
          let es ← (absICILFrom bl k).mapM fun ci => do
            let v ← ci.toConstantVal
            pure (v.name, v.levelParams, v.type, (none : Option Nat))
          pure (absNoteEntryL out ++ es))) ?_ ?_
  · intro k out hk rst lst o hrel hinv h
    rw [frontend.export_c.note_block_loop.eq_def] at h
    rw [if_neg (show ¬ k < alloc.vec.Vec.len bl by scalar_tac)] at h
    cases Result.ok_injective h
    have hnil : absICILFrom bl k = [] := by
      simp [absICILFrom, List.drop_eq_nil_of_le hk]
    refine LOut.ok (lst' := lst) ?_ hrel hinv
    rw [hnil]; show Except.ok _ = _; simp
  · intro k out hk ih rst lst o hrel hinv h
    rw [frontend.export_c.note_block_loop.eq_def] at h
    rw [if_pos (show k < alloc.vec.Vec.len bl by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hiiv : bl.val[k.val]'hk = ii := by
      have h1 := vec_index_some hii
      rw [List.getElem?_eq_getElem hk] at h1
      exact Option.some_injective _ h1
    have hdrop : absICILFrom bl k =
        absIConstantInfo ii :: (bl.val.drop (k.val + 1)).map absIConstantInfo := by
      simp only [absICILFrom]
      rw [List.drop_eq_getElem_cons hk, hiiv]; rfl
    have hT := i_constant_info_to_constant_val_refines hrel hinv hr
    show LOut _ _ _ _ _
    rw [hdrop]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    cases r with
    | Err e =>
      obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      obtain ⟨e', rfl, hk'⟩ := fail_refines hr1
      show AErrSim e' _
      rw [am_run_bind']
      exact AErrSim.of_kind (AErrSim.bind (Sim₀.apply_err hT) _) hk'
    | Ok cv =>
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hT
      have hk1v : k1.val = k.val + 1 := usize_add_one_inv hk1
      have hR := ih k1 out1 hk1v (rst := withStore rst ar1) (lst := lst1) hrel1 hinv1 h
      rw [run_bind_ok hx1]
      have hout : absNoteEntryL out1 = absNoteEntryL out ++
          [((absIConstantVal cv).name, (absIConstantVal cv).levelParams,
            (absIConstantVal cv).type, (none : Option Nat))] := by
        rw [absNoteEntryL, ConRon.Refine.vec_push_val hout1, dupId_nidx _ _ hn1,
          dupId_eidx _ _ he]
        simp [absNoteEntryL, absNoteEntry, absIConstantVal, nidx_vec_dup_val hv]
      have hrest : absICILFrom bl k1 = (bl.val.drop (k.val + 1)).map absIConstantInfo := by
        simp only [absICILFrom, hk1v]
      rw [hout, hrest] at hR
      simp only [List.append_assoc, List.singleton_append] at hR
      exact hR

/-- **`note_block`** — the `indDecl` arm's `block.mapM`, at a cursor. -/
theorem note_block_refines {pers rst lst bl i out o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.note_block pers rst.store bl i out = ok o) :
    SimL absNoteEntryL pers lst (o.1, withStore rst o.2)
      (do
        let es ← (absICILFrom bl i).mapM fun ci => do
          let v ← ci.toConstantVal
          pure (v.name, v.levelParams, v.type, (none : Option Nat))
        pure (absNoteEntryL out ++ es)) := by
  rw [frontend.export_c.note_block] at h
  exact note_block_loop_refines i out hrel hinv h

/-- **`note_decl_entries`** — the twin's `cvs`: the constants one pushed
declaration declares.  The `.basisDecl` arm fails loudly on both sides (the
twin's own choice: no frontend function produces one). -/
theorem note_decl_entries_refines {pers rst lst d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.note_decl_entries pers rst.store d = ok o) :
    SimL absNoteEntryL pers lst (o.1, withStore rst o.2)
      (noteDeclEntries (absIDeclaration d)) := by
  have one : ∀ cv hh v, frontend.export_c.note_one cv hh = ok v →
      o = (.Ok v, rst.store) →
      noteDeclEntries (absIDeclaration d) =
        pure [((absIConstantVal cv).name, (absIConstantVal cv).levelParams,
          (absIConstantVal cv).type, hh.map absU)] →
      SimL absNoteEntryL pers lst (o.1, withStore rst o.2)
        (noteDeclEntries (absIDeclaration d)) := by
    intro cv hh v hv ho hx
    subst ho
    refine LOut.ok (lst' := lst) ?_ hrel hinv
    rw [hx, note_one_refines hv]; rfl
  cases d with
  | AxiomDecl cv =>
    simp only [frontend.export_c.note_decl_entries] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact one cv none v hv (Result.ok_injective h).symm rfl
  | DefnDecl cv _ hint =>
    simp only [frontend.export_c.note_decl_entries] at h
    obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine one cv (some i) v hv (Result.ok_injective h).symm ?_
    simp only [absIDeclaration, noteDeclEntries, Option.map_some, hint_height_refines hi]
  | ThmDecl cv _ =>
    simp only [frontend.export_c.note_decl_entries] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact one cv none v hv (Result.ok_injective h).symm rfl
  | OpaqueDecl cv _ =>
    simp only [frontend.export_c.note_decl_entries] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact one cv none v hv (Result.ok_injective h).symm rfl
  | QuotDecl _ cv =>
    simp only [frontend.export_c.note_decl_entries] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact one cv none v hv (Result.ok_injective h).symm rfl
  | BasisDecl k =>
    clear one
    simp only [frontend.export_c.note_decl_entries, lift, bind_tc_ok] at h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    obtain ⟨m, rfl⟩ := merr_refines hr
    exact AErrSim.internal rfl
  | IndDecl bl np =>
    clear one
    simp only [frontend.export_c.note_decl_entries] at h
    have hB := note_block_refines hrel hinv h
    have e0 : absNoteEntryL (alloc.vec.Vec.new (arena.handle.NIdx ×
        (alloc.vec.Vec arena.handle.NIdx) × arena.handle.EIdx × (Option Std.U64))) = [] := rfl
    have ed : absICILFrom bl 0#usize = bl.val.map absIConstantInfo := by
      simp [absICILFrom, show ((0#usize : Std.Usize)).val = 0 by rfl]
    rw [e0, ed] at hB
    simp only [List.nil_append, bind_pure] at hB
    exact hB

/-- The loop of `note_entries`, at a cursor. -/
theorem note_entries_loop_refines {es : alloc.vec.Vec (arena.handle.NIdx ×
      (alloc.vec.Vec arena.handle.NIdx) × arena.handle.EIdx × (Option Std.U64))} :
    ∀ (i : Std.Usize) (rsd : frontend.export_c.StateD) {lsd rsd'},
      StateDRel rsd lsd → StateDInv rsd →
      frontend.export_c.note_entries_loop rsd es (alloc.vec.Vec.len es) i = ok rsd' →
      StateDRel rsd' (noteEntries lsd (absNoteEntryLFrom es i)) ∧ StateDInv rsd' := by
  refine cursor_induction (fun i : Std.Usize => i.val) es.val.length
    (fun i rsd => ∀ {lsd rsd'}, StateDRel rsd lsd → StateDInv rsd →
      frontend.export_c.note_entries_loop rsd es (alloc.vec.Vec.len es) i = ok rsd' →
      StateDRel rsd' (noteEntries lsd (absNoteEntryLFrom es i)) ∧ StateDInv rsd') ?_ ?_
  · intro i rsd hn lsd rsd' hd hi h
    rw [frontend.export_c.note_entries_loop.eq_def] at h
    rw [if_neg (show ¬ i < alloc.vec.Vec.len es by scalar_tac)] at h
    cases Result.ok_injective h
    have hnil : absNoteEntryLFrom es i = [] := by
      simp [absNoteEntryLFrom, List.drop_eq_nil_of_le hn]
    rw [hnil, noteEntries_nil]
    exact ⟨hd, hi⟩
  · intro i rsd hlt ih lsd rsd' hd hi h
    rw [frontend.export_c.note_entries_loop.eq_def] at h
    rw [if_pos (show i < alloc.vec.Vec.len es by scalar_tac)] at h
    obtain ⟨⟨n1, v, e, oh⟩, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hxv : es.val[i.val]'hlt = (n1, v, e, oh) := by
      have h1 := vec_index_some hx
      rw [List.getElem?_eq_getElem hlt] at h1
      exact Option.some_injective _ h1
    have hdrop : absNoteEntryLFrom es i =
        (absNIdx n1, v.val.map absNIdx, absEIdx e, oh.map absU) ::
          (es.val.drop (i.val + 1)).map absNoteEntry := by
      simp only [absNoteEntryLFrom]
      rw [List.drop_eq_getElem_cons hlt, hxv]; rfl
    -- the heights write
    obtain ⟨st1, hst1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hH : StateDRel st1 { lsd with heights := match oh.map absU with
        | some hh => lsd.heights.insert (absNIdx n1) hh
        | none => lsd.heights } ∧ StateDInv st1 := by
      cases oh with
      | none =>
        cases Result.ok_injective hst1
        exact ⟨hd, hi⟩
      | some hv =>
        obtain ⟨n2, hn2, hst1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst1
        obtain ⟨⟨old, hm⟩, hhm, hst1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst1
        cases Result.ok_injective hst1
        rw [dupId_nidx _ _ hn2] at hhm
        obtain ⟨hrel', -⟩ := ConRon.Refine.HashMap2.Rel_insert_wf nidx_eq2
          (fun a b _ _ hab => absNIdx_inj hab) hi.heights (anyNKeysOk _) hd.heights
          trivial hhm
        obtain ⟨hinv', -, -, -⟩ := ConRon.Refine.HashMap2.insert_refines_wf nidx_eq2
          hi.heights (anyNKeysOk _) trivial hhm
        exact ⟨{ hd with heights := hrel' }, { hi with heights := hinv' }⟩
    obtain ⟨hd1, hi1⟩ := hH
    -- the constTypes write
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨old, hm⟩, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1v, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ hn2] at hhm
    obtain ⟨hrel', -⟩ := ConRon.Refine.HashMap2.Rel_insert_wf nidx_eq2
      (fun a b _ _ hab => absNIdx_inj hab) hi1.constTypes (anyNKeysOk _) hd1.constTypes
      trivial hhm
    obtain ⟨hinv', -, -, -⟩ := ConRon.Refine.HashMap2.insert_refines_wf nidx_eq2
      hi1.constTypes (anyNKeysOk _) trivial hhm
    have hi1' : i1.val = i.val + 1 := usize_add_one_inv hi1v
    have hct : ConRon.Refine.HashMap2.RelOn anyN hm
        (lsd.constTypes.insert (absNIdx n1) (v.val.map absNIdx, absEIdx e)) absNIdx
        (fun p => (p.1.val.map absNIdx, absEIdx p.2)) := by
      simpa [nidx_vec_dup_val hv1, dupId_eidx _ _ he1] using hrel'
    have hR := ih i1 { st1 with const_types := hm } hi1' (lsd := { lsd with
        constTypes := lsd.constTypes.insert (absNIdx n1) (v.val.map absNIdx, absEIdx e),
        heights := match oh.map absU with
          | some hh => lsd.heights.insert (absNIdx n1) hh
          | none => lsd.heights })
      ({ hd1 with constTypes := hct })
      { hi1 with constTypes := hinv' } h
    rw [hdrop, noteEntries_cons, noteEntries_single]
    have hfrom : absNoteEntryLFrom es i1 = (es.val.drop (i.val + 1)).map absNoteEntry := by
      simp only [absNoteEntryLFrom, hi1']
    rw [← hfrom]
    exact hR

/-- **`note_entries`** — the twin's `cvs.foldl` into `constTypes`/`heights`. -/
theorem note_entries_refines {rsd lsd es rsd'} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd)
    (h : frontend.export_c.note_entries rsd es = ok rsd') :
    StateDRel rsd' (noteEntries lsd (absNoteEntryL es)) ∧ StateDInv rsd' := by
  rw [frontend.export_c.note_entries] at h
  have := note_entries_loop_refines 0#usize rsd hd hi h
  simpa [absNoteEntryLFrom, absNoteEntryL, show ((0#usize : Std.Usize)).val = 0 by rfl]
    using this

/-- **`note_decl` refines `noteDecl`** (`ExportC.lean:138-155`). -/
theorem note_decl_refines {pers rst lst rsd lsd d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.note_decl pers rst.store rsd d = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (noteDecl lsd (absIDeclaration d)) := by
  rw [frontend.export_c.note_decl] at h
  obtain ⟨⟨r, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hE := note_decl_entries_refines hrel hinv h1
  rw [noteDecl_unfold]
  cases r with
  | Ok es =>
    obtain ⟨st1, hst1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    obtain ⟨lst', hx, hrel', hinv'⟩ := hE
    obtain ⟨hd', hi'⟩ := note_entries_refines hd hi hst1
    refine ⟨_, lst', ?_, hd', hi', hrel', hinv'⟩
    rw [am_run_bind', hx]; rfl
  | Err e =>
    cases Result.ok_injective h
    show ALineErrSim e _
    rw [am_run_bind']; exact ALineErrSim.bind hE _

/-- **`push_decl` refines `pushDecl`** (`ExportC.lean:158-159`). -/
theorem push_decl_refines {pers rst lst rsd lsd d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.push_decl pers rst.store rsd d = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (pushDecl lsd (absIDeclaration d)) := by
  rw [frontend.export_c.push_decl] at h
  obtain ⟨⟨r, ar1, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hN := note_decl_refines hrel hinv hd hi h1
  cases r with
  | Ok u =>
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv'⟩ := hN
    refine ⟨{ lsd' with decls := lsd.decls.push (absIDeclaration d) }, lst', ?_, ?_,
      ⟨hi'.1, hi'.2, hi'.3, hi'.4, hi'.5, hi'.6⟩, hrel', hinv'⟩
    · rw [pushDecl_run, hx]; rfl
    · refine { hd' with decls := ?_ }
      show lsd.decls.push (absIDeclaration d) = absIDeclArr v
      rw [← noteDecl_run_decls hx, hd'.decls]
      simp [absIDeclArr, ConRon.Refine.vec_push_val hv]
  | Err e =>
    cases Result.ok_injective h
    show ALineErrSim e _
    have hN' : ALineErrSim e ((noteDecl lsd (absIDeclaration d)).run lst) := hN
    rw [pushDecl_run]
    cases e with
    | Verdict v => exact hN'.elim
    | Err ce =>
      intro k hk
      obtain ⟨le, hle, hk'⟩ := hN' k hk
      exact ⟨le, by rw [hle]; rfl, hk'⟩

/-! ## The index tables -/

/-- A reader's answer, then the rest. -/
theorem SimLR.bind_ok {α β γ δ : Type} {A : α → β} {B : δ → γ} {lst : AState} {o}
    {x : AM γ} {r : δ} {f : γ → AM β}
    (hx : SimLR B lst (.Ok r) x) (h : SimLR A lst o (f (B r))) :
    SimLR A lst o (x >>= f) := by
  simp only [SimLR] at hx
  rcases o with r' | e
  · simp only [SimLR] at h ⊢
    rw [am_run_bind', hx, except_ok_bind]; exact h
  · simp only [SimLR] at h ⊢
    rw [am_run_bind', hx, except_ok_bind]; exact h

/-- A reader's failure, then anything. -/
theorem SimLR.bind_err {α β γ δ : Type} {A : α → β} {B : δ → γ} {lst : AState}
    {e : frontend.export_c.LineErr} {x : AM γ} {f : γ → AM β}
    (hx : SimLR B lst (.Err e) x) : SimLR A lst (.Err e) (x >>= f) := by
  simp only [SimLR] at hx ⊢
  rw [am_run_bind']; exact ALineErrSim.bind hx _

/-- **The `SimLR` cursor loop, once.**  Every `LineErr`-channelled reader loop
of this module (`ind_block_types`, `block_rec_*`, `proj_*_of`, `ty_names_of` …)
has the same shape: at cursor `i` read element `xs[i]`, run one reader step
whose outcome `SimLR`-relates to the twin's per-element action `G`, push its
answer (or stop at its error), and go on at `i + 1`.  `hend`/`hstep` are that
shape, stated against the loop's own unfolding; the conclusion is the twin's
`(xs.drop i).mapM G`, after the accumulator. -/
theorem simLR_cursor {X Y β γ : Type} {absY : Y → β} {absX : X → γ} {lst : AState}
    {xs : alloc.vec.Vec X} {G : γ → AM β}
    {loop : alloc.vec.Vec Y → Std.Usize →
      Result (core.result.Result (alloc.vec.Vec Y) frontend.export_c.LineErr)}
    (hend : ∀ out i o, xs.val.length ≤ i.val → loop out i = ok o → o = .Ok out)
    (hstep : ∀ out i o, (hi : i.val < xs.val.length) → loop out i = ok o →
        ∃ r : core.result.Result Y frontend.export_c.LineErr,
          SimLR absY lst r (G (absX (xs.val[i.val]'hi))) ∧
          ((∃ e, r = .Err e ∧ o = .Err e) ∨
           (∃ y out1 i1, r = .Ok y ∧ out1.val = out.val ++ [y] ∧ i1.val = i.val + 1 ∧
             loop out1 i1 = ok o))) :
    ∀ out i o, loop out i = ok o →
      SimLR (fun v : alloc.vec.Vec Y => v.val.map absY) lst o
        (do let ys ← ((xs.val.drop i.val).map absX).mapM G; pure (out.val.map absY ++ ys)) := by
  suffices H : ∀ (k : Nat) out i o, xs.val.length - i.val = k → loop out i = ok o →
      SimLR (fun v : alloc.vec.Vec Y => v.val.map absY) lst o
        (do let ys ← ((xs.val.drop i.val).map absX).mapM G; pure (out.val.map absY ++ ys)) from
    fun out i o h => H _ out i o rfl h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro out i o hk h
    by_cases hi : i.val < xs.val.length
    · obtain ⟨r, hr, hro⟩ := hstep out i o hi h
      rw [List.drop_eq_getElem_cons hi, List.map_cons]
      rcases hro with ⟨e, rfl, rfl⟩ | ⟨y, out1, i1, rfl, hout1, hi1, h1⟩
      · show ALineErrSim e _
        rw [List.mapM_cons]
        simp only [bind_assoc, am_run_bind']
        exact ALineErrSim.bind hr _
      · have hR := ih (xs.val.length - i1.val) (by omega) out1 i1 o rfl h1
        rw [hi1] at hR
        have hr' : (G (absX (xs.val[i.val]'hi))).run lst = .ok (absY y, lst) := hr
        have hrun : ((do
            let ys ← (absX (xs.val[i.val]'hi) :: (xs.val.drop (i.val + 1)).map absX).mapM G
            pure (out.val.map absY ++ ys)) : AM _).run lst =
            ((do let ys ← ((xs.val.drop (i.val + 1)).map absX).mapM G
                 pure (out1.val.map absY ++ ys)) : AM _).run lst := by
          rw [List.mapM_cons]
          simp only [bind_assoc, am_run_bind', hr', except_ok_bind, pure_bind]
          cases ((xs.val.drop (i.val + 1)).map absX |>.mapM G).run lst with
          | error e => rfl
          | ok p => simp [hout1]
        cases o with
        | Ok w =>
          show _ = _
          exact hrun.trans hR
        | Err e =>
          show ALineErrSim e _
          rw [hrun]; exact hR
    · have := hend out i o (by omega) h
      subst this
      rw [List.drop_eq_nil_of_le (by omega)]
      show Except.ok _ = _
      simp

/-- **`scan_types::id_table_get` refines `IdTable.get?`**
(`ConLeche/Frontend/Scan/Types.lean:346-348`), ported from
`RefineOld/Frontend/StateDR.lean` by task #97-P5-Front round 2.  The port's
extra guard — the `u64` index cast to a `usize` and back, the overflow map
taken when the round trip is not the identity — costs nothing: a `u64` that
does not fit a `usize` is above every `Vec`'s length. -/
theorem id_table_get_refines {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    {i : Std.U64} {o : Option T} (hrel : IdTableRel A t lt)
    (h : frontend.scan_types.id_table_get t i = ok o) :
    o.map A = lt.get? i.val := by
  rw [frontend.scan_types.id_table_get] at h
  simp only [lift, bind_tc_ok] at h
  have hsize : lt.dense.size = t.dense.val.length := by
    have h := congrArg List.length hrel.dense; simpa using h.symm
  have hdense : ∀ j : Nat, lt.dense[j]? = (t.dense.val[j]?).map A := by
    intro j; rw [← Array.getElem?_toList, ← hrel.dense, List.getElem?_map]
  have hsparse : ∀ {o : Option T},
      ron.hashmap.HashMap.get hU64 eU64 t.sparse i = ok o → o.map A = lt.sparse[i.val]? :=
    fun h => ConRon.Refine.HashMap.Rel_get_wf u64Eq2Fwd hrel.inv (u64KeysOk _) hrel.sparse
      trivial h
  split at h
  · rename_i hc
    have hkv : (Std.UScalar.cast .Usize i : Std.Usize).val = i.val := by
      rw [← usize_cast_u64_val' (Std.UScalar.cast .Usize i), hc]
    split at h
    · rename_i hlt
      have hltv : i.val < t.dense.val.length := by rw [← hkv]; scalar_tac
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      have hgx := vec_index_some hx
      rw [hkv] at hgx
      have hlt' : i.val < lt.dense.size := by rw [hsize]; exact hltv
      simp only [ConLeche.Frontend.IdTable.get?, hlt', _root_.dite_true]
      rw [← Array.getElem?_eq_getElem hlt', hdense, hgx]
    · rename_i hge
      have hgev : ¬ i.val < t.dense.val.length := by rw [← hkv]; scalar_tac
      simp only [ConLeche.Frontend.IdTable.get?, hsize, hgev, _root_.dite_false]
      exact hsparse h
  · rename_i hc
    have hbig : Std.Usize.max < i.val := by
      by_contra hle
      exact hc (ConRon.Refine.Env.u64_val_inj (by
        rw [usize_cast_u64_val', ConRon.Refine.Env.u64_cast_usize_val (by omega)]))
    have hgev : ¬ i.val < t.dense.val.length := by
      have := t.dense.property; omega
    simp only [ConLeche.Frontend.IdTable.get?, hsize, hgev, _root_.dite_false]
    exact hsparse h

/-- The three table readers share one shape: a hit is the handle, a miss is
`merr` (an `internal` failure) against the twin's `fail (.internal …)`. -/
theorem st_get_refines {T α : Type} {A : T → α} {lt : ConLeche.Frontend.IdTable α}
    {t : frontend.scan_types.IdTable T} {i : Std.U64} {lst : AState} {g : Option T}
    {x : AM α} (hrel : IdTableRel A t lt)
    (hxs : ∀ n, lt.get? i.val = some n → x.run lst = .ok (n, lst))
    (hxn : lt.get? i.val = none → ∃ le, x.run lst = .error le ∧ lAErrKind le = some .internal)
    {o : core.result.Result T frontend.export_c.LineErr}
    (hg : frontend.scan_types.id_table_get t i = ok g)
    (hn : g = none → ∃ m, o = .Err (.Err (.Internal m)))
    (hs : ∀ n, g = some n → o = .Ok n) :
    SimLR A lst o x := by
  have hG := id_table_get_refines hrel hg
  cases g with
  | none =>
    obtain ⟨m, rfl⟩ := hn rfl
    obtain ⟨le, hle, hk⟩ := hxn (by rw [← hG]; rfl)
    intro k hk'
    simp only [absAErrKind, Option.some.injEq] at hk'
    subst hk'
    exact ⟨le, hle, hk⟩
  | some n =>
    rw [hs n rfl]
    exact hxs _ (by rw [← hG]; rfl)

theorem st_miss {T : Type} {k : Std.Usize} {M : Std.Array Std.U32 k} {i : Std.U64}
    {r : core.result.Result T frontend.export_c.LineErr}
    (h : (do
        let s ← lift (Std.Array.to_slice M)
        let v ← kernel.core_types.code_points s
        let v1 ← frontend.text.u64_str i
        let v2 ← frontend.text.cat v v1
        frontend.export_c.merr T v2) = ok r) :
    ∃ m, r = .Err (.Err (.Internal m)) := by
  simp only [lift, bind_tc_ok] at h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact merr_refines h


/-- **`st_name` refines `StateD.name`** (`ExportC.lean:163-166`). -/
theorem st_name_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_name rsd i = ok o) :
    SimLR absNIdx lst o (lsd.name (absU i)) := by
  rw [frontend.export_c.st_name] at h
  obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine st_get_refines hd.names (fun n hn => by simp only [StateD.name, absU, hn]; rfl)
    (fun hn => ⟨_, by simp only [StateD.name, absU, hn]; rfl, rfl⟩) hg (fun hgn => ?_) (fun n hgs => ?_)
  · subst hgn; exact st_miss h
  · subst hgs
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    rw [dupId_nidx _ _ hn1]

/-- **`st_level` refines `StateD.level`** (`ExportC.lean:170-173`). -/
theorem st_level_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_level rsd i = ok o) :
    SimLR absLIdx lst o (lsd.level (absU i)) := by
  rw [frontend.export_c.st_level] at h
  obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine st_get_refines hd.levels (fun n hn => by simp only [StateD.level, absU, hn]; rfl)
    (fun hn => ⟨_, by simp only [StateD.level, absU, hn]; rfl, rfl⟩) hg (fun hgn => ?_) (fun n hgs => ?_)
  · subst hgn; exact st_miss h
  · subst hgs
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    rw [dupId_lidx _ _ hn1]

/-- **`st_expr` refines `StateD.expr`** (`ExportC.lean:177-180`). -/
theorem st_expr_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_expr rsd i = ok o) :
    SimLR absEIdx lst o (lsd.expr (absU i)) := by
  rw [frontend.export_c.st_expr] at h
  obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine st_get_refines hd.exprs (fun n hn => by simp only [StateD.expr, absU, hn]; rfl)
    (fun hn => ⟨_, by simp only [StateD.expr, absU, hn]; rfl, rfl⟩) hg (fun hgn => ?_) (fun n hgs => ?_)
  · subst hgn; exact st_miss h
  · subst hgs
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    rw [dupId_eidx _ _ hn1]

/-- **`st_names`** — the twin's `ns.mapM st.name`. -/
theorem st_names_refines {rsd lsd lst is o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_names rsd is = ok o) :
    SimLR absNIdxL lst o ((is.val.map absU).mapM lsd.name) := by
  rw [frontend.export_c.st_names] at h
  have key : ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx) o,
      frontend.export_c.st_names_loop rsd is out (alloc.vec.Vec.len is) i = ok o →
      SimLR absNIdxL lst o (do
        let rest ← ((is.val.drop i.val).map absU).mapM lsd.name
        pure (absNIdxL out ++ rest)) := by
    refine cursor_induction (fun i : Std.Usize => i.val) is.val.length
      (fun i (out : alloc.vec.Vec arena.handle.NIdx) => ∀ o,
        frontend.export_c.st_names_loop rsd is out (alloc.vec.Vec.len is) i = ok o →
        SimLR absNIdxL lst o (do
          let rest ← ((is.val.drop i.val).map absU).mapM lsd.name
          pure (absNIdxL out ++ rest))) ?_ ?_
    · intro i out hn o h
      rw [frontend.export_c.st_names_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len is by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hn]
      show Except.ok _ = _
      simp
    · intro i out hi ih o h
      rw [frontend.export_c.st_names_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len is by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hxv : is.val[i.val]'hi = x := by
        have h1 := vec_index_some hx
        rw [List.getElem?_eq_getElem hi] at h1
        exact Option.some_injective _ h1
      have hN := st_name_refines (lst := lst) hd hr
      rw [List.drop_eq_getElem_cons hi, hxv, List.map_cons, List.mapM_cons]
      cases r with
      | Err e =>
        cases Result.ok_injective h
        show ALineErrSim e _
        simp only [bind_assoc, am_run_bind']
        exact ALineErrSim.bind hN _
      | Ok v =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hR := ih i2 out1 hi2v o h
        rw [hi2v] at hR
        simp only [SimLR] at hN
        revert hR
        cases o with
        | Ok w =>
          intro hR
          show _ = _
          simp only [bind_assoc, am_run_bind', hN, except_ok_bind, pure_bind]
          have hR' : ((List.map absU (List.drop (i.val + 1) is.val)).mapM lsd.name >>=
              fun rest => pure (absNIdxL out1 ++ rest) : AM _).run lst = .ok (absNIdxL w, lst) := hR
          rw [am_run_bind'] at hR'
          revert hR'
          cases hm : ((List.map absU (List.drop (i.val + 1) is.val)).mapM lsd.name).run lst with
          | error e => intro hR'; exact absurd hR' (by simp [Bind.bind, Except.bind])
          | ok p =>
            intro hR'
            simp only [except_ok_bind] at hR' ⊢
            rw [← hR']
            simp [absNIdxL, ConRon.Refine.vec_push_val hout1]
        | Err e =>
          intro hR
          simp only [SimLR] at hR ⊢
          refine ALineErrSim.of_eq hR ?_
          simp only [bind_assoc, am_run_bind', hN, except_ok_bind, pure_bind]
          cases hm : ((List.map absU (List.drop (i.val + 1) is.val)).mapM lsd.name).run lst with
          | error e => rfl
          | ok p => simp [absNIdxL, ConRon.Refine.vec_push_val hout1]
  have := key 0#usize _ o h
  have e0 : absNIdxL (alloc.vec.Vec.with_capacity arena.handle.NIdx (alloc.vec.Vec.len is))
      = [] := rfl
  simp only [e0, List.nil_append, show ((0#usize : Std.Usize)).val = 0 by rfl, List.drop_zero,
    bind_pure] at this
  exact this

/-- **`st_levels`** — the twin's `us.mapM st.level`. -/
theorem st_levels_refines {rsd lsd lst is o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_levels rsd is = ok o) :
    SimLR (fun v => v.val.map absLIdx) lst o
      ((is.val.map absU).mapM lsd.level) := by
  rw [frontend.export_c.st_levels] at h
  have key : ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.LIdx) o,
      frontend.export_c.st_levels_loop rsd is out (alloc.vec.Vec.len is) i = ok o →
      SimLR absLIdxL lst o (do
        let rest ← ((is.val.drop i.val).map absU).mapM lsd.level
        pure (absLIdxL out ++ rest)) := by
    refine cursor_induction (fun i : Std.Usize => i.val) is.val.length
      (fun i (out : alloc.vec.Vec arena.handle.LIdx) => ∀ o,
        frontend.export_c.st_levels_loop rsd is out (alloc.vec.Vec.len is) i = ok o →
        SimLR absLIdxL lst o (do
          let rest ← ((is.val.drop i.val).map absU).mapM lsd.level
          pure (absLIdxL out ++ rest))) ?_ ?_
    · intro i out hn o h
      rw [frontend.export_c.st_levels_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len is by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hn]
      show Except.ok _ = _
      simp
    · intro i out hi ih o h
      rw [frontend.export_c.st_levels_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len is by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hxv : is.val[i.val]'hi = x := by
        have h1 := vec_index_some hx
        rw [List.getElem?_eq_getElem hi] at h1
        exact Option.some_injective _ h1
      have hN := st_level_refines (lst := lst) hd hr
      rw [List.drop_eq_getElem_cons hi, hxv, List.map_cons, List.mapM_cons]
      cases r with
      | Err e =>
        cases Result.ok_injective h
        show ALineErrSim e _
        simp only [bind_assoc, am_run_bind']
        exact ALineErrSim.bind hN _
      | Ok v =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hR := ih i2 out1 hi2v o h
        rw [hi2v] at hR
        simp only [SimLR] at hN
        revert hR
        cases o with
        | Ok w =>
          intro hR
          show _ = _
          simp only [bind_assoc, am_run_bind', hN, except_ok_bind, pure_bind]
          have hR' : ((List.map absU (List.drop (i.val + 1) is.val)).mapM lsd.level >>=
              fun rest => pure (absLIdxL out1 ++ rest) : AM _).run lst = .ok (absLIdxL w, lst) := hR
          rw [am_run_bind'] at hR'
          revert hR'
          cases hm : ((List.map absU (List.drop (i.val + 1) is.val)).mapM lsd.level).run lst with
          | error e => intro hR'; exact absurd hR' (by simp [Bind.bind, Except.bind])
          | ok p =>
            intro hR'
            simp only [except_ok_bind] at hR' ⊢
            rw [← hR']
            simp [absLIdxL, ConRon.Refine.vec_push_val hout1]
        | Err e =>
          intro hR
          simp only [SimLR] at hR ⊢
          refine ALineErrSim.of_eq hR ?_
          simp only [bind_assoc, am_run_bind', hN, except_ok_bind, pure_bind]
          cases hm : ((List.map absU (List.drop (i.val + 1) is.val)).mapM lsd.level).run lst with
          | error e => rfl
          | ok p => simp [absLIdxL, ConRon.Refine.vec_push_val hout1]
  have := key 0#usize _ o h
  have e0 : absLIdxL (alloc.vec.Vec.with_capacity arena.handle.LIdx (alloc.vec.Vec.len is))
      = [] := rfl
  simp only [e0, List.nil_append, show ((0#usize : Std.Usize)).val = 0 by rfl, List.drop_zero,
    bind_pure] at this
  exact this



/-- **`get_decl_d` refines `getDeclD`** (`ExportC.lean:185-186`). -/
theorem get_decl_d_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.get_decl_d rsd i = ok o) :
    SimLR absEIdx lst o (getDeclD lsd (absU i)) := by
  rw [frontend.export_c.get_decl_d] at h
  exact st_expr_refines hd h

/-- **`parse_pw_d` refines `parsePwD`** (`ExportC.lean:192-197`): the `pw`
datum over the direct name table.  `PropWhen` holds con-leche `Name`s, so the
resolved handles are read BACK — `arena::env::read_names` against the twin's
`hs.mapM readName`, the same `denoteN` (`Text.lean`'s `env_read_names_abs`).
The second conjunct is the port's own representation fact the binder intern
needs: the datum is a `PropWhenWF` one (the names read back are well formed). -/
theorem parse_pw_d_refines {pers rst lst rsd lsd r o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_pw_d pers rst.store rsd r = ok o) :
    SimLR ConRon.Refine.absPropWhen lst o (parsePwD lsd (absPwRec r)) ∧
      (∀ pw, o = .Ok pw → ConRon.Refine.PropWhenWF pw) := by
  rw [frontend.export_c.parse_pw_d.eq_def] at h
  cases r with
  | Never =>
    simp only at h
    obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    refine ⟨?_, fun p hp => by cases hp; exact ConRon.Refine.PropWhenWF.never hpw⟩
    show Except.ok _ = _
    rw [ConRon.Refine.PropWhen.never_refines hpw]
  | IfAllZero ns =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_names_refines (lst := lst) hd hr1
    have hns : absU64s ns = ns.val.map absU := rfl
    simp only [absPwRec, parsePwD, hns]
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact ⟨SimLR.bind_err h1, fun p hp => by cases hp⟩
    | Ok hs =>
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hR := env_read_names_abs hrel.store hinv.store hr2
      cases hdl : denoteNList lst.store.ns (hs.val.map absNIdx) with
      | none =>
        rw [hdl] at hR
        obtain ⟨e, rfl, hek⟩ := hR
        obtain ⟨e', rfl, hk'⟩ := fail_refines h
        refine ⟨?_, fun p hp => by cases hp⟩
        show AErrSim e' (((do
          let hs ← (ns.val.map absU).mapM lsd.name
          let xs ← hs.mapM readName
          pure (ConLeche.PropWhen.ifAllZero xs)) : AM _).run lst)
        rw [am_run_bind', SimLR.apply h1, except_ok_bind, am_run_bind',
          show absNIdxL hs = hs.val.map absNIdx from rfl, mapM_readName_run, hdl]
        exact AErrSim.mk rfl (by rw [hk', hek]; rfl)
      | some xs =>
        rw [hdl] at hR
        obtain ⟨v, rfl, hv, hw⟩ := hR
        obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases Result.ok_injective h
        refine ⟨?_, fun p hp => by
          cases hp; exact ConRon.Refine.PropWhenWF.if_all_zero hw hpw⟩
        show ((do
          let hs ← (ns.val.map absU).mapM lsd.name
          let xs ← hs.mapM readName
          pure (ConLeche.PropWhen.ifAllZero xs)) : AM _).run lst = _
        rw [am_run_bind', SimLR.apply h1, except_ok_bind, am_run_bind',
          show absNIdxL hs = hs.val.map absNIdx from rfl, mapM_readName_run, hdl]
        show Except.ok _ = _
        rw [ConRon.Refine.PropWhen.if_all_zero_refines hw hpw, ConRon.Refine.absNames, hv]

/-! ## The rebinding test

con-leche measured 17 % of its parse phase on this detail, so the three tests
are their own functions on a borrowed state — and they are the one place the
parse REJECTS a stream for a reason that is not the scanner's. -/

/-! ## Writing an index table

`scan_types::id_table_insert` against `ConLeche/Frontend/Scan/Types.lean`'s
`IdTable.insert`, ported from `RefineOld/Frontend/StateDR.lean` (task #87) at
handles: the three arms — a push at the dense frontier, an overwrite below it,
an overflow insert above it — are con-leche's three, at the same index. -/

theorem idt_index_mut_back {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {a : α} {f : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (a, f)) :
    f = alloc.vec.Vec.set v i := by
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at h
  obtain ⟨y, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- **`scan_types::id_table_insert` refines `IdTable.insert`.** -/
theorem id_table_insert_rel {T α : Type} {A : T → α}
    {t t' : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    {i : Std.U64} {x : T} (hrel : IdTableRel A t lt)
    (h : frontend.scan_types.id_table_insert t i x = ok t') :
    IdTableRel A t' (lt.insert i.val (A x)) := by
  rw [frontend.scan_types.id_table_insert] at h
  simp only [lift, bind_tc_ok] at h
  have hsize : lt.dense.size = t.dense.val.length := by
    have h := congrArg List.length hrel.dense; simpa using h.symm
  have hnv : (Std.UScalar.cast .U64 (alloc.vec.Vec.len t.dense) : Std.U64).val
      = t.dense.val.length := by
    rw [usize_cast_u64_val']; rfl
  split at h
  · -- the dense frontier: a push on both sides
    rename_i hc
    have hiv : i.val = t.dense.val.length := by rw [hc]; exact hnv
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have hins : lt.insert i.val (A x) = { lt with dense := lt.dense.push (A x) } := by
      rw [ConLeche.Frontend.IdTable.insert]
      simp [hiv, hsize]
    rw [hins]
    exact ⟨by rw [ConRon.Refine.vec_push_val hv]; simp [hrel.dense], hrel.sparse, hrel.inv⟩
  · split at h
    · -- below the frontier: an overwrite on both sides
      rename_i hc hlt
      have hltv : i.val < t.dense.val.length := by
        have : i.val < (Std.UScalar.cast .U64 (alloc.vec.Vec.len t.dense) : Std.U64).val := by
          scalar_tac
        omega
      have hne : ¬ i.val = t.dense.val.length := by omega
      have hi2 : (Std.UScalar.cast .Usize i : Std.Usize).val = i.val :=
        ConRon.Refine.Env.u64_cast_usize_val (by have := t.dense.property; omega)
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
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
        intro hc'; exact hc (ConRon.Refine.Env.u64_val_inj (by rw [hnv, hc']))
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨old, m'⟩ := p
      rw [← Result.ok_injective h]
      have hins : lt.insert i.val (A x)
          = { lt with sparse := lt.sparse.insert i.val (A x) } := by
        rw [ConLeche.Frontend.IdTable.insert]
        simp [hne, hsize, hgev]
      rw [hins]
      obtain ⟨hinv', -, -, -⟩ := ConRon.Refine.HashMap.insert_refines_wf u64Eq2Fwd
        hrel.inv (u64KeysOk _) trivial hp
      obtain ⟨hrel', -⟩ := ConRon.Refine.HashMap.Rel_insert_wf u64Eq2Fwd
        (fun a b _ _ hab => ConRon.Refine.Env.u64_val_inj hab) hrel.inv (u64KeysOk _)
        hrel.sparse trivial hp
      exact ⟨hrel.dense, hrel', hinv'⟩

/-- `id_table_get` answers `bound`: con-leche's own `IdTable.bound_eq`. -/
theorem id_table_bound_rel {T α : Type} {A : T → α}
    {t : frontend.scan_types.IdTable T} {lt : ConLeche.Frontend.IdTable α}
    {i : Std.U64} {o : Option T} (hrel : IdTableRel A t lt)
    (h : frontend.scan_types.id_table_get t i = ok o) :
    o.isSome = lt.bound i.val := by
  rw [ConLeche.Frontend.IdTable.bound_eq, ← id_table_get_refines hrel h]
  cases o <;> rfl

/-- **`st_fresh_name` refines `StateD.freshName`** (`ExportC.lean:209-210`):
the port reads the table where the twin asks `bound`, which con-leche's
`IdTable.bound_eq` identifies. -/
theorem st_fresh_name_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_fresh_name rsd i = ok o) :
    SimLR (fun _ => ()) lst o (lsd.freshName (absU i)) := by
  rw [frontend.export_c.st_fresh_name] at h
  obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb := id_table_bound_rel hd.names hg
  cases g with
  | none =>
    cases Result.ok_injective h
    have hf : lsd.names.bound (absU i) = false := by rw [← hb]; rfl
    show (lsd.freshName (absU i)).run lst = _
    simp only [StateD.freshName, hf]; rfl
  | some x =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨m, rfl⟩ := merr_refines h
    have hf : lsd.names.bound (absU i) = true := by rw [← hb]; rfl
    show AErrSim _ _
    exact AErrSim.internal (by simp only [StateD.freshName, hf, if_true]; rfl)

/-- **`st_fresh_level` refines `StateD.freshLevel`**. -/
theorem st_fresh_level_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_fresh_level rsd i = ok o) :
    SimLR (fun _ => ()) lst o (lsd.freshLevel (absU i)) := by
  rw [frontend.export_c.st_fresh_level] at h
  obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb := id_table_bound_rel hd.levels hg
  cases g with
  | none =>
    cases Result.ok_injective h
    have hf : lsd.levels.bound (absU i) = false := by rw [← hb]; rfl
    show (lsd.freshLevel (absU i)).run lst = _
    simp only [StateD.freshLevel, hf]; rfl
  | some x =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨m, rfl⟩ := merr_refines h
    have hf : lsd.levels.bound (absU i) = true := by rw [← hb]; rfl
    show AErrSim _ _
    exact AErrSim.internal (by simp only [StateD.freshLevel, hf, if_true]; rfl)

/-- **`st_fresh_expr` refines `StateD.freshExpr`**. -/
theorem st_fresh_expr_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_fresh_expr rsd i = ok o) :
    SimLR (fun _ => ()) lst o (lsd.freshExpr (absU i)) := by
  rw [frontend.export_c.st_fresh_expr] at h
  obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb := id_table_bound_rel hd.exprs hg
  cases g with
  | none =>
    cases Result.ok_injective h
    have hf : lsd.exprs.bound (absU i) = false := by rw [← hb]; rfl
    show (lsd.freshExpr (absU i)).run lst = _
    simp only [StateD.freshExpr, hf]; rfl
  | some x =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨m, rfl⟩ := merr_refines h
    have hf : lsd.exprs.bound (absU i) = true := by rw [← hb]; rfl
    show AErrSim _ _
    exact AErrSim.internal (by simp only [StateD.freshExpr, hf, if_true]; rfl)

/-! ## The three table-entry writers -/

/-- A `SimD` claim moves along a twin run equation. -/
theorem SimD.of_run_eq {pers : arena.store.PersTier} {lst lst1 : AState}
    {o : core.result.Result Unit frontend.export_c.LineErr ×
      arena.monad.AState × frontend.export_c.StateD}
    {x y : AM Arena.Frontend.StateD}
    (h : SimD pers lst1 o x) (hxy : y.run lst = x.run lst1) : SimD pers lst o y := by
  rcases o with ⟨r, rst', rsd'⟩
  unfold SimD at h ⊢
  rw [hxy]; exact h

/-- The shared tail of the name-table writer: the intern, then the table
write.  Both sides intern blindly — neither checks that the parent handle
resolves (task #97-P5-Front round 3, F11) — so lockstep is all it takes. -/
theorem name_entry_tail {pers rst lst rsd lsd i v o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd) (hvwf : NNodeViewWF v)
    (h : (do
      let (r3, ar1) ← arena.store.EStore.intern_name rst.store pers v
      match r3 with
      | core.result.Result.Ok h =>
        let it ← frontend.scan_types.id_table_insert rsd.names i h
        ok (core.result.Result.Ok (), ar1, { rsd with names := it })
      | core.result.Result.Err e =>
        let r4 ← frontend.export_c.fail Unit e
        ok (r4, ar1, rsd)) = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (do
        let h ← internNNode (absNNodeView v)
        pure { lsd with names := lsd.names.insert (absU i) h }) := by
  obtain ⟨⟨r3, ar1⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hS := intern_n_node_run₀ hrel hinv v hvwf (o := (r3, withStore rst ar1))
    (by rw [arena.monad.intern_n_node, h3]; simp only [bind_tc_ok]; rfl)
  cases r3 with
  | Err e =>
    obtain ⟨r4, hr4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    obtain ⟨e', rfl, hk⟩ := fail_refines hr4
    show AErrSim e' _
    rw [am_run_bind']
    exact AErrSim.of_kind (AErrSim.bind (Sim₀.apply_err hS) _) hk
  | Ok hh =>
    obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS
    refine SimD.mk (lsd' := { lsd with names := lsd.names.insert (absU i) (absNIdx hh) })
      ?_ { hd with names := id_table_insert_rel hd.names hit }
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩ hrel1 hinv1
    rw [am_run_bind', hx1]; rfl

/-- **`parse_name_entry_d` refines `parseNameEntryD`**
(`ExportC.lean:226-236`).  Task #97-P5-Front round 3's F11: false only while
`AStateRel` carried `storeWF` (the parent handle need not resolve, on either
side); lockstep, it is the two reads and the tail. -/
theorem parse_name_entry_d_refines {pers rst lst rsd lsd i r o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd) (hs : NameRecStrWF r)
    (h : frontend.export_c.parse_name_entry_d pers rst.store rsd i r = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (parseNameEntryD lsd (absU i) (absNameRec r)) := by
  rw [frontend.export_c.parse_name_entry_d.eq_def] at h
  cases r with
  | Str pre s =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hN := st_name_refines (lst := lst) hd hr1
    simp only [absNameRec, parseNameEntryD]
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact SimD.err (SimLR.bind_err (A := fun x : Arena.Frontend.StateD => x) hN)
    | Ok p =>
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hF := st_fresh_name_refines (lst := lst) hd hr2
      cases r2 with
      | Err e =>
        cases Result.ok_injective h
        refine SimD.err ?_
        show ALineErrSim e ((do let p ← lsd.name (absU pre); _).run lst)
        rw [am_run_bind', SimLR.apply hN, except_ok_bind, am_run_bind']
        exact ALineErrSim.bind hF _
      | Ok u =>
        obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hsv : ConRon.Refine.absString v = ConRon.Refine.absString s := by
          rw [ConRon.Refine.absString, ConRon.Refine.absString,
            ConRon.Refine.Env.code_points_val hv,
            show (alloc.vec.Vec.deref s).val = s.val from Slice.from_val _ _]
        have hvwf : NNodeViewWF (arena.store.NNodeView.Str p v) := by
          show ConRon.Refine.StrWF v
          have hvv : v.val = s.val := by
            rw [ConRon.Refine.Env.code_points_val hv,
              show (alloc.vec.Vec.deref s).val = s.val from Slice.from_val _ _]
          intro c hc; rw [hvv] at hc; exact hs c hc
        have hT := name_entry_tail hrel hinv hd hi hvwf h
        refine SimD.of_run_eq hT ?_
        rw [am_run_bind', SimLR.apply hN, except_ok_bind, am_run_bind', SimLR.apply hF,
          except_ok_bind]
        simp only [absNNodeView, hsv]
  | Num pre k =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hN := st_name_refines (lst := lst) hd hr1
    simp only [absNameRec, parseNameEntryD]
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact SimD.err (SimLR.bind_err (A := fun x : Arena.Frontend.StateD => x) hN)
    | Ok p =>
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hF := st_fresh_name_refines (lst := lst) hd hr2
      cases r2 with
      | Err e =>
        cases Result.ok_injective h
        refine SimD.err ?_
        show ALineErrSim e ((do let p ← lsd.name (absU pre); _).run lst)
        rw [am_run_bind', SimLR.apply hN, except_ok_bind, am_run_bind']
        exact ALineErrSim.bind hF _
      | Ok u =>
        have hT := name_entry_tail hrel hinv hd hi (v := arena.store.NNodeView.Num p k)
          trivial h
        refine SimD.of_run_eq hT ?_
        rw [am_run_bind', SimLR.apply hN, except_ok_bind, am_run_bind', SimLR.apply hF,
          except_ok_bind]
        rfl

/-- **`parse_level_rec_d`** — the value half of `parseLevelEntryD`, which the
twin writes inline and the port factors out (`Spec.lean`'s `parseLevelRecD`). -/
theorem parse_level_rec_d_refines {rsd lsd lst r o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_level_rec_d rsd r = ok o) :
    SimLR absLNodeView lst o (parseLevelRecD lsd (absLevelRec r)) := by
  rw [frontend.export_c.parse_level_rec_d.eq_def] at h
  cases r with
  | Succ u =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_level_refines (lst := lst) hd hr1
    simp only [absLevelRec, parseLevelRecD]
    cases r1 with
    | Err e => cases Result.ok_injective h; exact SimLR.bind_err h1
    | Ok a => cases Result.ok_injective h; exact SimLR.bind_ok h1 rfl
  | Max a b =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_level_refines (lst := lst) hd hr1
    simp only [absLevelRec, parseLevelRecD]
    cases r1 with
    | Err e => cases Result.ok_injective h; exact SimLR.bind_err h1
    | Ok x =>
      refine SimLR.bind_ok h1 ?_
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_level_refines (lst := lst) hd hr2
      cases r2 with
      | Err e => cases Result.ok_injective h; exact SimLR.bind_err h2
      | Ok y => cases Result.ok_injective h; exact SimLR.bind_ok h2 rfl
  | Imax a b =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_level_refines (lst := lst) hd hr1
    simp only [absLevelRec, parseLevelRecD]
    cases r1 with
    | Err e => cases Result.ok_injective h; exact SimLR.bind_err h1
    | Ok x =>
      refine SimLR.bind_ok h1 ?_
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_level_refines (lst := lst) hd hr2
      cases r2 with
      | Err e => cases Result.ok_injective h; exact SimLR.bind_err h2
      | Ok y => cases Result.ok_injective h; exact SimLR.bind_ok h2 rfl
  | Param n =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_name_refines (lst := lst) hd hr1
    simp only [absLevelRec, parseLevelRecD]
    cases r1 with
    | Err e => cases Result.ok_injective h; exact SimLR.bind_err h1
    | Ok a => cases Result.ok_injective h; exact SimLR.bind_ok h1 rfl

/-- **`parse_level_entry_d` refines `parseLevelEntryD`**
(`ExportC.lean:240-255`), through `Spec.lean`'s `parseLevelEntryD_unfold`.
Round 3's F11: lockstep, the freshness test, the value half, the intern and
the table write, in that order on both sides. -/
theorem parse_level_entry_d_refines {pers rst lst rsd lsd i r o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.parse_level_entry_d pers rst.store rsd i r = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (parseLevelEntryD lsd (absU i) (absLevelRec r)) := by
  rw [parseLevelEntryD_unfold]
  rw [frontend.export_c.parse_level_entry_d] at h
  obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hF := st_fresh_level_refines (lst := lst) hd hr1
  cases r1 with
  | Err e =>
    cases Result.ok_injective h
    refine SimD.err ?_
    rw [am_run_bind']
    exact ALineErrSim.bind hF _
  | Ok u =>
    obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hV := parse_level_rec_d_refines (lst := lst) hd hr2
    cases r2 with
    | Err e =>
      cases Result.ok_injective h
      refine SimD.err ?_
      rw [am_run_bind', SimLR.apply hF, except_ok_bind, am_run_bind']
      exact ALineErrSim.bind hV _
    | Ok v =>
      obtain ⟨⟨r3, ar1⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hS := intern_l_node_run₀ hrel hinv v (o := (r3, withStore rst ar1))
        (by rw [arena.monad.intern_l_node, h3]; simp only [bind_tc_ok]; rfl)
      have hpre : ∀ {β} (k : LIdx → AM β), (do
          lsd.freshLevel (absU i)
          let l ← internLNode (← parseLevelRecD lsd (absLevelRec r))
          k l).run lst = (do let l ← internLNode (absLNodeView v); k l).run lst := by
        intro β k
        rw [am_run_bind', SimLR.apply hF, except_ok_bind, am_run_bind', SimLR.apply hV,
          except_ok_bind]
      cases r3 with
      | Err e =>
        obtain ⟨r4, hr4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases Result.ok_injective h
        obtain ⟨e', rfl, hk⟩ := fail_refines hr4
        show AErrSim e' _
        rw [hpre, am_run_bind']
        exact AErrSim.of_kind (AErrSim.bind (Sim₀.apply_err hS) _) hk
      | Ok hh =>
        obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases Result.ok_injective h
        obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS
        refine SimD.mk (lsd' := { lsd with levels := lsd.levels.insert (absU i) (absLIdx hh) })
          ?_ { hd with levels := id_table_insert_rel hd.levels hit }
          ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩ hrel1 hinv1
        rw [hpre, am_run_bind', hx1]; rfl

/-- A `SimL` claim moves along a twin run equation. -/
theorem SimL.of_run_eq {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst lst1 : AState}
    {o : core.result.Result α frontend.export_c.LineErr × arena.monad.AState}
    {x y : AM β} (h : SimL A pers lst1 o x) (hxy : y.run lst = x.run lst1) :
    SimL A pers lst o y := by
  unfold SimL at h ⊢; rw [hxy]; exact h

/-- The shared tail of the expression-table value half: `EStore::intern` at a
view, lifted to the ambient state, against the twin's `internE`. -/
theorem expr_intern_tail {pers rst lst} {v : arena.store.ENodeView} {o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hlit : ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l)
    (hpw : ∀ ty b m, v = .Lam ty b m ∨ v = .ForallE ty b m →
      ConRon.Refine.PropWhenWF m.pw)
    (h : (do
      let (r1, ar1) ← arena.store.EStore.intern rst.store pers v
      match r1 with
      | core.result.Result.Ok h => ok (core.result.Result.Ok h, ar1)
      | core.result.Result.Err e =>
        let r2 ← frontend.export_c.fail arena.handle.EIdx e
        ok (r2, ar1)) = ok o) :
    SimL absEIdx pers lst (o.1, withStore rst o.2) (internE (absENodeView v)) := by
  obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hS := intern_e_run₀ hrel hinv v hlit hpw (o := (r1, withStore rst ar1))
    (by rw [arena.monad.intern_e, h1]; simp only [bind_tc_ok]; rfl)
  cases r1 with
  | Ok hh =>
    cases Result.ok_injective h
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS
    exact ⟨lst1, hx1, hrel1, hinv1⟩
  | Err e =>
    obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    obtain ⟨e', rfl, hk⟩ := fail_refines hr2
    exact AErrSim.of_kind (Sim₀.apply_err hS) hk

/-- `nat_decimal::from_decimal` returns `ron::nat`'s own normal form, because
its last step is `nat::norm` (ported from `RefineOld/Frontend/Readers.lean`). -/
theorem from_decimal_wf {s : Slice Std.U8} {n : ron.nat.Nat}
    (h : frontend.nat_decimal.from_decimal s = ok (some n)) : ConRon.Refine.Nat.NatWF n := by
  rw [frontend.nat_decimal.from_decimal] at h
  split at h
  · simp only [Result.ok.injEq, reduceCtorEq] at h
  · obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h
    · obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp only [Result.ok.injEq, Option.some.injEq] at h
      subst h
      exact (ConRon.Refine.Nat.norm_refines hm).2
    · simp only [Result.ok.injEq, reduceCtorEq] at h

theorem no_lit_wf {v : arena.store.ENodeView} (hv : ∀ l, v ≠ .Lit l) :
    ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l := fun l hl => absurd hl (hv l)

theorem no_pw_wf {v : arena.store.ENodeView}
    (hv : ∀ ty b m, v ≠ .Lam ty b m ∧ v ≠ .ForallE ty b m) :
    ∀ ty b m, v = .Lam ty b m ∨ v = .ForallE ty b m → ConRon.Refine.PropWhenWF m.pw :=
  fun ty b m hm => by
    rcases hm with hm | hm
    · exact absurd hm (hv ty b m).1
    · exact absurd hm (hv ty b m).2

/-- **`parse_expr_rec_d`** — the value half of `parseExprEntryD` (`Spec.lean`'s
`parseExprRecD`), arm for arm: the table reads, then one intern.  Round 3's
F11: false only while `AStateRel` carried `storeWF` (a child handle out of the
tables need not resolve; neither side checks).  The binder arms rest on
`Specs.lean`'s `intern_e_run₀`, which exists since task #97-T2-LOCKSTEP D6 put
the twin's binder `internE` in the Rust's order.  Its `StrVal` arm interns a
`Lit` node, whose `LiteralWF` is `ExprRecStrWF`; its `NatVal` arm is
`scan_types.rs`'s deviation 2 (`NatValSpec`). -/
theorem parse_expr_rec_d_refines {pers rst lst rsd lsd r o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hs : ExprRecStrWF r) (hnat : NatValSpec r)
    (h : frontend.export_c.parse_expr_rec_d pers rst.store rsd r = ok o) :
    SimL absEIdx pers lst (o.1, withStore rst o.2)
      (parseExprRecD lsd (absExprRec r)) := by
  have hnl : ∀ {v : arena.store.ENodeView}, (∀ l, v ≠ .Lit l) →
      (∀ ty b m, v ≠ .Lam ty b m ∧ v ≠ .ForallE ty b m) → ∀ {o}, (do
      let (r1, ar1) ← arena.store.EStore.intern rst.store pers v
      match r1 with
      | core.result.Result.Ok h => ok (core.result.Result.Ok h, ar1)
      | core.result.Result.Err e =>
        let r2 ← frontend.export_c.fail arena.handle.EIdx e
        ok (r2, ar1)) = ok o →
      SimL absEIdx pers lst (o.1, withStore rst o.2) (internE (absENodeView v)) :=
    fun hv hw _ h => expr_intern_tail hrel hinv (no_lit_wf hv) (no_pw_wf hw) h
  rw [frontend.export_c.parse_expr_rec_d.eq_def] at h
  show LOut _ _ _ _ _
  cases r with
  | Bvar k =>
    simp only at h
    exact hnl (by intro l hl; cases hl) (by intro _ _ _; constructor <;> intro hc <;> cases hc) h
  | «Sort» u =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_level_refines (lst := lst) hd hr1
    simp only [absExprRec, parseExprRecD]
    rw [am_run_bind']
    cases r1 with
    | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h1 _
    | Ok l =>
      rw [SimLR.apply h1, except_ok_bind]
      exact hnl (v := arena.store.ENodeView.Sort l) (by intro l hl; cases hl)
        (by intro _ _ _; constructor <;> intro hc <;> cases hc) h
  | Const n us =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_name_refines (lst := lst) hd hr1
    simp only [absExprRec, parseExprRecD]
    rw [am_run_bind']
    cases r1 with
    | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h1 _
    | Ok nm =>
      rw [SimLR.apply h1, except_ok_bind]
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_levels_refines (lst := lst) hd hr2
      rw [am_run_bind']
      cases r2 with
      | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h2 _
      | Ok ls =>
        rw [show absU64s us = us.val.map absU from rfl, SimLR.apply h2, except_ok_bind]
        obtain ⟨⟨r3, ar1⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hL := intern_ls_node_run₀ hrel hinv ls (o := (r3, withStore rst ar1))
          (by rw [arena.monad.intern_ls_node, h3]; simp only [bind_tc_ok]; rfl)
        rw [am_run_bind']
        cases r3 with
        | Err e =>
          obtain ⟨r4, hr4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases Result.ok_injective h
          obtain ⟨e', rfl, hk⟩ := fail_refines hr4
          exact AErrSim.of_kind (AErrSim.bind (Sim₀.apply_err hL) _) hk
        | Ok lsh =>
          obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hL
          rw [show absLsNodeView ls = ls.val.map absLIdx from rfl] at hx1
          rw [hx1, except_ok_bind]
          exact expr_intern_tail (rst := withStore rst ar1) (v := .Const nm lsh) hrel1 hinv1
            (no_lit_wf (by intro l hl; cases hl))
            (no_pw_wf (by intro _ _ _; constructor <;> intro hc <;> cases hc)) h
  | App f a =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_expr_refines (lst := lst) hd hr1
    simp only [absExprRec, parseExprRecD]
    rw [am_run_bind']
    cases r1 with
    | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h1 _
    | Ok x =>
      rw [SimLR.apply h1, except_ok_bind]
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_expr_refines (lst := lst) hd hr2
      rw [am_run_bind']
      cases r2 with
      | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h2 _
      | Ok y =>
        rw [SimLR.apply h2, except_ok_bind]
        exact hnl (v := .App x y) (by intro l hl; cases hl)
          (by intro _ _ _; constructor <;> intro hc <;> cases hc) h
  | Lam ty bd pw =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_expr_refines (lst := lst) hd hr1
    simp only [absExprRec, parseExprRecD]
    rw [am_run_bind']
    cases r1 with
    | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h1 _
    | Ok x =>
      rw [SimLR.apply h1, except_ok_bind]
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_expr_refines (lst := lst) hd hr2
      rw [am_run_bind']
      cases r2 with
      | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h2 _
      | Ok y =>
        rw [SimLR.apply h2, except_ok_bind]
        obtain ⟨r3, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨h3, hw3⟩ := parse_pw_d_refines (lst := lst) hrel hinv hd hr3
        rw [am_run_bind']
        cases r3 with
        | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h3 _
        | Ok p =>
          rw [SimLR.apply h3, except_ok_bind]
          obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          rw [kernel.expr.binder_meta] at hbm
          cases Result.ok_injective hbm
          exact expr_intern_tail hrel hinv (v := arena.store.ENodeView.Lam x y { pw := p })
            (no_lit_wf (by intro l hl; cases hl))
            (fun _ _ m hm => by
              rcases hm with hm | hm <;> cases hm
              exact hw3 p rfl) h
  | ForallE ty bd pw =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_expr_refines (lst := lst) hd hr1
    simp only [absExprRec, parseExprRecD]
    rw [am_run_bind']
    cases r1 with
    | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h1 _
    | Ok x =>
      rw [SimLR.apply h1, except_ok_bind]
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_expr_refines (lst := lst) hd hr2
      rw [am_run_bind']
      cases r2 with
      | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h2 _
      | Ok y =>
        rw [SimLR.apply h2, except_ok_bind]
        obtain ⟨r3, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨h3, hw3⟩ := parse_pw_d_refines (lst := lst) hrel hinv hd hr3
        rw [am_run_bind']
        cases r3 with
        | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h3 _
        | Ok p =>
          rw [SimLR.apply h3, except_ok_bind]
          obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          rw [kernel.expr.binder_meta] at hbm
          cases Result.ok_injective hbm
          exact expr_intern_tail hrel hinv (v := arena.store.ENodeView.ForallE x y { pw := p })
            (no_lit_wf (by intro l hl; cases hl))
            (fun _ _ m hm => by
              rcases hm with hm | hm <;> cases hm
              exact hw3 p rfl) h
  | LetE ty vl bd =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_expr_refines (lst := lst) hd hr1
    simp only [absExprRec, parseExprRecD]
    rw [am_run_bind']
    cases r1 with
    | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h1 _
    | Ok x =>
      rw [SimLR.apply h1, except_ok_bind]
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_expr_refines (lst := lst) hd hr2
      rw [am_run_bind']
      cases r2 with
      | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h2 _
      | Ok y =>
        rw [SimLR.apply h2, except_ok_bind]
        obtain ⟨r3, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have h3 := st_expr_refines (lst := lst) hd hr3
        rw [am_run_bind']
        cases r3 with
        | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h3 _
        | Ok z =>
          rw [SimLR.apply h3, except_ok_bind]
          exact hnl (v := .LetE x y z) (by intro l hl; cases hl)
            (by intro _ _ _; constructor <;> intro hc <;> cases hc) h
  | Proj tn ix s =>
    simp only at h
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h1 := st_name_refines (lst := lst) hd hr1
    simp only [absExprRec, parseExprRecD]
    rw [am_run_bind']
    cases r1 with
    | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h1 _
    | Ok t =>
      rw [SimLR.apply h1, except_ok_bind]
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := st_expr_refines (lst := lst) hd hr2
      rw [am_run_bind']
      cases r2 with
      | Err e => cases Result.ok_injective h; exact ALineErrSim.bind h2 _
      | Ok x =>
        rw [SimLR.apply h2, except_ok_bind]
        exact hnl (v := .Proj t ix x) (by intro l hl; cases hl)
          (by intro _ _ _; constructor <;> intro hc <;> cases hc) h
  | NatVal ds =>
    simp only at h
    obtain ⟨on, hon, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n, rfl, hnv⟩ := hnat ds rfl on hon
    obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [kernel.expr.literal_nat, ron.ptr.new, alloc.sync.Arc.new, bind_tc_ok] at hl
    cases Result.ok_injective hl
    simp only [absExprRec, parseExprRecD]
    have hT := expr_intern_tail hrel hinv
      (v := arena.store.ENodeView.Lit (kernel.expr.Literal.NatVal n))
      (fun l hl => by cases hl; exact from_decimal_wf hon)
      (no_pw_wf (by intro _ _ _; constructor <;> intro hc <;> cases hc)) h
    simp only [absENodeView, ConRon.Refine.absLiteral, hnv] at hT
    exact hT
  | StrVal s =>
    simp only at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [kernel.expr.literal_str, ron.ptr.new, alloc.sync.Arc.new, bind_tc_ok] at hl
    cases Result.ok_injective hl
    have hvv : v.val = s.val := by
      rw [ConRon.Refine.Env.code_points_val hv,
        show (alloc.vec.Vec.deref s).val = s.val from Slice.from_val _ _]
    have hsv : ConRon.Refine.absString v = ConRon.Refine.absString s := by
      rw [ConRon.Refine.absString, ConRon.Refine.absString, hvv]
    simp only [absExprRec, parseExprRecD]
    have hT := expr_intern_tail hrel hinv
      (v := arena.store.ENodeView.Lit (kernel.expr.Literal.StrVal v))
      (fun l hl => by
        cases hl
        intro c hc; rw [hvv] at hc; exact hs c hc)
      (no_pw_wf (by intro _ _ _; constructor <;> intro hc <;> cases hc)) h
    simp only [absENodeView, ConRon.Refine.absLiteral, hsv] at hT
    exact hT

/-- **`parse_expr_entry_d` refines `parseExprEntryD`**
(`ExportC.lean:259-282`), through `Spec.lean`'s `parseExprEntryD_unfold`.
Round 3's F11: the freshness test, the value half, the table write. -/
theorem parse_expr_entry_d_refines {pers rst lst rsd lsd i r o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd) (hs : ExprRecStrWF r)
    (hnat : NatValSpec r)
    (h : frontend.export_c.parse_expr_entry_d pers rst.store rsd i r = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (parseExprEntryD lsd (absU i) (absExprRec r)) := by
  rw [parseExprEntryD_unfold]
  rw [frontend.export_c.parse_expr_entry_d] at h
  obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hF := st_fresh_expr_refines (lst := lst) hd hr1
  cases r1 with
  | Err e =>
    cases Result.ok_injective h
    refine SimD.err ?_
    rw [am_run_bind']
    exact ALineErrSim.bind hF _
  | Ok u =>
    obtain ⟨⟨r2, ar1⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hV := parse_expr_rec_d_refines hrel hinv hd hs hnat hr2
    cases r2 with
    | Err e =>
      cases Result.ok_injective h
      refine SimD.err ?_
      rw [am_run_bind', SimLR.apply hF, except_ok_bind, am_run_bind']
      exact ALineErrSim.bind hV _
    | Ok hh =>
      obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := LOut.dest hV
      refine SimD.mk (lsd' := { lsd with exprs := lsd.exprs.insert (absU i) (absEIdx hh) })
        ?_ { hd with exprs := id_table_insert_rel hd.exprs hit }
        ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩ hrel1 hinv1
      rw [am_run_bind', SimLR.apply hF, except_ok_bind, am_run_bind', hx1]; rfl

/-- **`parse_cv_d` refines `parseCVD`** (`ExportC.lean:286-290`). -/
theorem parse_cv_d_refines {rsd lsd lst cv o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_cv_d rsd cv = ok o) :
    SimLR absIConstantVal lst o (parseCVD lsd (absCVRec cv)) := by
  rw [frontend.export_c.parse_cv_d] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hN := st_name_refines (lst := lst) hd hr
  simp only [parseCVD, absCVRec]
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact SimLR.bind_err hN
  | Ok nm =>
    refine SimLR.bind_ok hN ?_
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hG := get_decl_d_refines (lst := lst) hd hr1
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact SimLR.bind_err hG
    | Ok ty =>
      refine SimLR.bind_ok hG ?_
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hL := st_names_refines (lst := lst) hd hr2
      cases r2 with
      | Err e =>
        cases Result.ok_injective h
        exact SimLR.bind_err hL
      | Ok lps =>
        cases Result.ok_injective h
        refine SimLR.bind_ok hL ?_
        rfl

/-! ## The projection rewrite's hooks -/

/-- **`proj_level_of`** — the artifact's recorded field sort. -/
theorem proj_level_of_refines {rsd lsd k o} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd) (h : frontend.export_c.proj_level_of rsd k = ok o) :
    o.map absLIdx = lsd.projLevels[absNIdx k]? := by
  rw [frontend.export_c.proj_level_of] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hg := nidx_get hi.projLevels hr
  have hrel := hd.projLevels k trivial
  cases r with
  | none => cases Result.ok_injective h; rw [← hrel, ← hg]
  | some x => cases Result.ok_injective h; rw [← hrel, ← hg]

/-- **`proj_owner_of`** — the recorded owner of a type former. -/
theorem proj_owner_of_refines {rsd lsd t o} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd) (h : frontend.export_c.proj_owner_of rsd t = ok o) :
    o.map absProjRecOwner = lsd.projOwners[absNIdx t]? := by
  rw [frontend.export_c.proj_owner_of] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hg := nidx_get hi.projOwners hr
  have hrel := hd.projOwners t trivial
  cases r with
  | none => cases Result.ok_injective h; rw [← hrel, ← hg]
  | some x => cases Result.ok_injective h; rw [← hrel, ← hg]

/-- **`proj_rewrite_d` refines `projRewriteD`** (`ExportC.lean:302-322`). -/
theorem proj_rewrite_d_refines {pers rst lst rsd lsd cv vl o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.proj_rewrite_d pers rst rsd cv vl = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRewriteD lsd (absIConstantVal cv) (absEIdx vl)) := by
  rw [frontend.export_c.proj_rewrite_d] at h
  obtain ⟨fuel, hfuel, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hF : storeFuel.run lst = .ok (absU fuel, lst) :=
    store_fuel_refines hrel hinv hfuel
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hL := lam_body_refines hrel hinv hr
  show AOut₀ _ _ _ _ _
  rw [projRewriteD, run_bind_ok hF]
  have hnone : ∀ {x : AM (Option EIdx)}, x.run lst = .ok (none, lst) →
      AOut₀ (Option.map absEIdx) pers
        (core.result.Result.Ok (none : Option arena.handle.EIdx)) rst (x.run lst) :=
    fun hx => AOut₀.ok (lst' := lst) hx hrel hinv
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact AOut₀.err (by rw [am_run_bind']; exact AErrSim.bind hL _)
  | Ok v =>
    have hL' : (lamBody (absU fuel) (absEIdx vl)).run lst = .ok (absEIdx v, lst) := hL
    rw [run_bind_ok hL']
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hV := view_run₀ hrel hinv hr1
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact AOut₀.err (by rw [am_run_bind']; exact AErrSim.bind hV _)
    | Ok ev =>
      obtain ⟨lst1, hx1, -, -⟩ := hV
      have := view_run_state hx1
      subst this
      rw [run_bind_ok hx1]
      cases ev with
      | Proj t i sub =>
        simp only [absENodeView]
        obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hV2 := view_run₀ hrel hinv hr2
        cases r2 with
        | Err e =>
          cases Result.ok_injective h
          exact AOut₀.err (by rw [am_run_bind']; exact AErrSim.bind hV2 _)
        | Ok ev1 =>
          obtain ⟨lst2, hx2, -, -⟩ := hV2
          have := view_run_state hx2
          subst this
          rw [run_bind_ok hx2]
          cases ev1 with
          | BVar i1 =>
            simp only [absENodeView]
            simp only at h
            split at h
            · -- the `.bvar 0` arm: the port's `proj_rewrite_at`, inline
              show AOut₀ _ _ _ _ ((match lsd.projOwners[absNIdx t]? with
                | none => pure none
                | some o =>
                  if (absIConstantVal cv).levelParams != o.lps then pure none
                  else do
                    match lsd.projLevels[← projIotaName (absNIdx t) (absU i)]? with
                    | none => pure none
                    | some l => projRecValue (absU fuel) o l (absIConstantVal cv).type (absEIdx vl) (absU i) :
                  AM (Option EIdx)).run lst2)
              rw [frontend.export_c.proj_rewrite_at] at h
              obtain ⟨ow, how, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
              rw [← proj_owner_of_refines hd hi how]
              cases ow with
              | none => cases Result.ok_injective h; exact hnone rfl
              | some o1 =>
                simp only [Option.map_some]
                obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
                have hbv := nidx_vec_beq_refines hb
                have hbv' : b = decide ((absIConstantVal cv).levelParams =
                    (absProjRecOwner o1).lps) := by
                  rw [hbv]
                  simp [absNIdxLFrom, absIConstantVal, absProjRecOwner]
                split at h
                · rename_i hbt
                  have hne : ((absIConstantVal cv).levelParams != (absProjRecOwner o1).lps)
                      = false := by
                    rw [hbv'] at hbt; simpa using hbt
                  rw [if_neg (by rw [hne]; simp)]
                  obtain ⟨⟨r3, ar1⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
                  have hN := proj_iota_name_refines hrel hinv h3
                  cases r3 with
                  | Err e =>
                    cases Result.ok_injective h
                    exact AOut₀.err (by rw [am_run_bind']; exact AErrSim.bind hN _)
                  | Ok k =>
                    obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hN
                    rw [run_bind_ok hx3]
                    obtain ⟨o2, ho2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
                    rw [← proj_level_of_refines hd hi ho2]
                    cases o2 with
                    | none =>
                      cases Result.ok_injective h
                      exact AOut₀.ok (lst' := lst3) rfl hrel3 hinv3
                    | some l =>
                      exact proj_rec_value_refines hrel3 hinv3 h
                · rename_i hbf
                  cases Result.ok_injective h
                  have hne : ((absIConstantVal cv).levelParams != (absProjRecOwner o1).lps)
                      = true := by
                    rw [hbv'] at hbf; simpa using hbf
                  rw [if_pos hne]
                  exact hnone rfl
            · rename_i hz
              cases Result.ok_injective h
              apply hnone
              have hz' : absU i1 ≠ 0 := by
                intro hc; apply hz; apply UScalar.eq_of_val_eq; rw [show (0#64#uscalar : Std.U64).val = 0 from rfl]; simpa [absU] using hc
              rw [show absU i1 = (absU i1 - 1) + 1 by omega]
              rfl
          | _ => cases Result.ok_injective h; exact hnone rfl
      | _ => cases Result.ok_injective h; exact hnone rfl

/-- **`note_proj_iota` refines `noteProjIota`** (`ExportC.lean:325-335`). -/
theorem note_proj_iota_refines {pers rst lst rsd lsd cvp o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.note_proj_iota pers rst rsd cvp = ok o) :
    ∀ _u, o.1 = .Ok _u → ∃ lsd' lst',
      (noteProjIota lsd (absIConstantVal cvp)).run lst = .ok (lsd', lst') ∧
      StateDRel o.2.2 lsd' ∧ StateDInv o.2.2 ∧ AStateRel₀ pers o.2.1 lst' ∧
      AStateInv pers o.2.1 := by sorry

/-! ## The modeller's booking -/

/-- **`push_gen_d` refines `pushGenD`** (`ExportC.lean:339-345`). -/
theorem push_gen_d_refines {pers rst lst rsd lsd d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.push_gen_d pers rst rsd d = ok o) :
    SimD pers lst o (pushGenD lsd (absIDeclaration d)) := by sorry

/-- **`note_gen_names`** — the twin's `ns.foldl` into `genOwner`. -/
theorem note_gen_names_refines {rsd lsd names t0 rsd'} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd)
    (h : frontend.export_c.note_gen_names rsd names t0 = ok rsd') :
    StateDRel rsd'
      { lsd with genRecords := lsd.genRecords + 1,
                 genOwner := (absNIdxL names).foldl
                   (fun m n => m.insert n (absNIdx t0)) lsd.genOwner } ∧
      StateDInv rsd' := by sorry

/-- **`note_gen` refines `noteGen`** (`ExportC.lean:347-353`). -/
theorem note_gen_refines {rsd lsd lst d t0 rsd'} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd) (h : frontend.export_c.note_gen rsd d t0 = ok rsd') :
    ∃ lsd', (noteGen lsd (absIDeclaration d) (absNIdx t0)).run lst = .ok (lsd', lst) ∧
      StateDRel rsd' lsd' ∧ StateDInv rsd' := by sorry

/-- **`push_gen_list` refines `pushGenList`** (`ExportC.lean:425-428`). -/
theorem push_gen_list_refines {pers rst lst rsd lsd gen t0 o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.push_gen_list pers rst rsd gen t0 = ok o) :
    SimD pers lst o (pushGenList lsd (absIDeclL gen) (absNIdx t0)) := by sorry

/-! ## Two spine walks -/

/-- **`ind_pi_tele_len` refines `indPiTeleLen`** (`ExportC.lean:358-364`). -/
theorem ind_pi_tele_len_refines {pers rst lst fuel h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.ind_pi_tele_len pers rst.store fuel h' = ok o) :
    SimLR absU lst o (indPiTeleLen (absU fuel) (absEIdx h')) := by sorry

/-- **`pi_result` refines `piResultD`** — three lines of spine walk, spelled
locally in its one frontend caller (`k_expected_of`).  Its twin is the
frontend's own `piResultD` (full `view` at each step), not `Arena/ExprOps.lean`'s
`piResult` (`viewBindI`, which never decodes a binder's datum): at a `∀` over a
dangling datum the port's `env::view_e` fails where that one walks on — a
twin/Rust divergence, fixed in the twin by task #97-T2-LOCKSTEP lane
Frontend. -/
theorem pi_result_refines {pers rst lst fuel h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.pi_result pers rst.store fuel h' = ok o) :
    SimLR absEIdx lst o (piResultD (absU fuel) (absEIdx h')) := by sorry

/-! ## The recursor rules and the block record -/

/-- **The cursor loop from `0` into a fresh accumulator**: `simLR_cursor` at
the loop's entry, stated as the twin's plain `mapM`. -/
theorem simLR_cursor0 {X Y β γ : Type} {absY : Y → β} {absX : X → γ} {lst : AState}
    {xs : alloc.vec.Vec X} {G : γ → AM β}
    {loop : alloc.vec.Vec Y → Std.Usize →
      Result (core.result.Result (alloc.vec.Vec Y) frontend.export_c.LineErr)}
    (hend : ∀ out i o, xs.val.length ≤ i.val → loop out i = ok o → o = .Ok out)
    (hstep : ∀ out i o, (hi : i.val < xs.val.length) → loop out i = ok o →
        ∃ r : core.result.Result Y frontend.export_c.LineErr,
          SimLR absY lst r (G (absX (xs.val[i.val]'hi))) ∧
          ((∃ e, r = .Err e ∧ o = .Err e) ∨
           (∃ y out1 i1, r = .Ok y ∧ out1.val = out.val ++ [y] ∧ i1.val = i.val + 1 ∧
             loop out1 i1 = ok o)))
    {out : alloc.vec.Vec Y} (hout : out.val = []) {o} (h : loop out 0#usize = ok o) :
    SimLR (fun v : alloc.vec.Vec Y => v.val.map absY) lst o ((xs.val.map absX).mapM G) := by
  have H := simLR_cursor hend hstep out 0#usize o h
  simp only [hout, List.map_nil, List.nil_append, show ((0#usize : Std.Usize)).val = 0 by rfl,
    List.drop_zero, bind_pure] at H
  exact H

/-- One cursor step's bookkeeping: the pushed accumulator and the next index. -/
theorem cursor_push {Y : Type} {out out1 : alloc.vec.Vec Y} {y : Y} {i i1 : Std.Usize}
    (hout1 : alloc.vec.Vec.push out y = ok out1) (hi1 : i + 1#usize = ok i1) :
    out1.val = out.val ++ [y] ∧ i1.val = i.val + 1 :=
  ⟨ConRon.Refine.vec_push_val hout1, by have := ConRon.Refine.Nat.uadd_val hi1; simpa using this⟩

theorem vec_index_eq {X : Type} {xs : alloc.vec.Vec X} {i : Std.Usize} {x : X}
    (hi : i.val < xs.val.length)
    (hx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice X) xs i = ok x) :
    xs.val[i.val]'hi = x := by
  have h1 := vec_index_some hx
  rw [List.getElem?_eq_getElem hi] at h1
  exact Option.some_injective _ h1

/-- **`parse_rule_d` refines `parseRuleD`** (`ExportC.lean:383-385`). -/
theorem parse_rule_d_refines {rsd lsd lst ru o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_rule_d rsd ru = ok o) :
    SimLR absIRecRule lst o (parseRuleD lsd (absRuleRec ru)) := by
  rw [frontend.export_c.parse_rule_d] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := st_name_refines (lst := lst) hd hr
  simp only [parseRuleD, absRuleRec]
  cases r with
  | Err e => cases Result.ok_injective h; exact SimLR.bind_err h1
  | Ok c =>
    refine SimLR.bind_ok h1 ?_
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 := get_decl_d_refines (lst := lst) hd hr1
    cases r1 with
    | Err e => cases Result.ok_injective h; exact SimLR.bind_err h2
    | Ok rhs =>
      refine SimLR.bind_ok h2 ?_
      obtain ⟨ir, hir, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      rw [arena.env.i_rec_rule_parsed] at hir
      cases Result.ok_injective hir
      rfl

/-- **`parse_rules_d`** — the twin's `r.rules.mapM (parseRuleD st)`. -/
theorem parse_rules_d_refines {rsd lsd lst rus o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_rules_d rsd rus = ok o) :
    SimLR absIRecRuleL lst o
      ((absRuleRecs rus).mapM (parseRuleD lsd)) := by
  rw [frontend.export_c.parse_rules_d] at h
  exact simLR_cursor0 (absX := absRuleRec) (xs := rus)
    (loop := fun out i =>
      frontend.export_c.parse_rules_d_loop rsd rus out (alloc.vec.Vec.len rus) i)
    (fun out i o hn h => by
      rw [frontend.export_c.parse_rules_d_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len rus by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.parse_rules_d_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len rus by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨r, by rw [vec_index_eq hi hx]; exact parse_rule_d_refines hd hr, ?_⟩
      cases r with
      | Err e => exact Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩
      | Ok y =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        exact Or.inr ⟨y, out1, i1, rfl, e1, e2, h⟩)
    rfl h

/-- **`block_rec_ctors`** — the block record's constructor half. -/
theorem block_rec_ctors_refines {rsd lsd lst ctors o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_ctors rsd ctors = ok o) :
    SimLR (fun v => v.val.map absMIndCtorRec) lst o
      ((absIndCtorRecs ctors).mapM fun c => do
        pure { cv := ← parseCVD lsd c.cv, nP := c.numParams,
               nF := c.numFields : MIndCtorRec }) := by
  rw [frontend.export_c.block_rec_ctors] at h
  exact simLR_cursor0 (absX := absIndCtorRec) (xs := ctors)
    (loop := fun out i =>
      frontend.export_c.block_rec_ctors_loop rsd ctors out (alloc.vec.Vec.len ctors) i)
    (fun out i o hn h => by
      rw [frontend.export_c.block_rec_ctors_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len ctors by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.block_rec_ctors_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len ctors by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [vec_index_eq hi hx]
      have hC := parse_cv_d_refines (lst := lst) hd hr
      cases r with
      | Err e =>
        refine ⟨.Err e, SimLR.bind_err hC, Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
      | Ok cv =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        refine ⟨.Ok _, ?_, Or.inr ⟨_, out1, i1, rfl, e1, e2, h⟩⟩
        exact SimLR.bind_ok hC rfl)
    rfl h

/-- **`block_rec_types`** — the block record's type half.  The listed
constructors are read before the common data, the port's order (the twin's
too, since task #97-T2-LOCKSTEP lane Frontend). -/
theorem block_rec_types_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_types rsd tys = ok o) :
    SimLR (fun v => v.val.map absMIndTypeRec) lst o
      ((absIndTypeRecs tys).mapM fun t => do
        let ctors ← t.ctors.mapM lsd.name
        pure { cv := ← parseCVD lsd t.cv, nP := t.numParams, nIdx := t.numIndices,
               ctors := ctors, isRec := t.isRec,
               isReflexive := t.isReflexive, numNested := t.numNested :
               MIndTypeRec }) := by
  rw [frontend.export_c.block_rec_types] at h
  exact simLR_cursor0 (absX := absIndTypeRec) (xs := tys)
    (loop := fun out i =>
      frontend.export_c.block_rec_types_loop rsd tys out (alloc.vec.Vec.len tys) i)
    (fun out i o hn h => by
      rw [frontend.export_c.block_rec_types_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len tys by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.block_rec_types_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len tys by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [vec_index_eq hi hx]
      have hN := st_names_refines (lst := lst) hd hr
      cases r with
      | Err e =>
        refine ⟨.Err e, SimLR.bind_err hN, Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
      | Ok v =>
        obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hC := parse_cv_d_refines (lst := lst) hd hr1
        cases r1 with
        | Err e =>
          refine ⟨.Err e, SimLR.bind_ok hN (SimLR.bind_err hC),
            Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
        | Ok cv =>
          obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
          refine ⟨.Ok _, ?_, Or.inr ⟨_, out1, i1, rfl, e1, e2, h⟩⟩
          exact SimLR.bind_ok hN (SimLR.bind_ok hC rfl))
    rfl h

/-- **`block_rec_recs`** — the block record's recursor half. -/
theorem block_rec_recs_refines {rsd lsd lst recs o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_recs rsd recs = ok o) :
    SimLR (fun v => v.val.map absMIndRecRec) lst o
      ((absIndRecRecs recs).mapM fun r => do
        let rules ← r.rules.mapM (parseRuleD lsd)
        pure { cv := ← parseCVD lsd r.cv, nP := r.numParams, nM := r.numMotives,
               nm := r.numMinors, nI := r.numIndices, rules := rules :
               MIndRecRec }) := by
  rw [frontend.export_c.block_rec_recs] at h
  exact simLR_cursor0 (absX := absIndRecRec) (xs := recs)
    (loop := fun out i =>
      frontend.export_c.block_rec_recs_loop rsd recs out (alloc.vec.Vec.len recs) i)
    (fun out i o hn h => by
      rw [frontend.export_c.block_rec_recs_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len recs by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.block_rec_recs_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len recs by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [vec_index_eq hi hx]
      have hN := parse_rules_d_refines (lst := lst) hd hr
      cases r with
      | Err e =>
        refine ⟨.Err e, SimLR.bind_err hN, Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
      | Ok v =>
        obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hC := parse_cv_d_refines (lst := lst) hd hr1
        cases r1 with
        | Err e =>
          refine ⟨.Err e, SimLR.bind_ok hN (SimLR.bind_err hC),
            Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
        | Ok cv =>
          obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
          refine ⟨.Ok _, ?_, Or.inr ⟨_, out1, i1, rfl, e1, e2, h⟩⟩
          exact SimLR.bind_ok hN (SimLR.bind_ok hC rfl))
    rfl h

/-- **`block_rec_of` refines `blockRecOf`** (`ExportC.lean:389-411`). -/
theorem block_rec_of_refines {rsd lsd lst tys cts rcs o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_of rsd tys cts rcs = ok o) :
    SimLR absBlockRec lst o
      (blockRecOf lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
        (absIndRecRecs rcs)) := by
  rw [frontend.export_c.block_rec_of] at h
  rw [blockRecOf]
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := block_rec_types_refines (lst := lst) hd hr
  cases r with
  | Err e => cases Result.ok_injective h; exact SimLR.bind_err h1
  | Ok ts =>
    refine SimLR.bind_ok h1 ?_
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 := block_rec_ctors_refines (lst := lst) hd hr1
    cases r1 with
    | Err e => cases Result.ok_injective h; exact SimLR.bind_err h2
    | Ok cs =>
      refine SimLR.bind_ok h2 ?_
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h3 := block_rec_recs_refines (lst := lst) hd hr2
      cases r2 with
      | Err e => cases Result.ok_injective h; exact SimLR.bind_err h3
      | Ok rs =>
        cases Result.ok_injective h
        exact SimLR.bind_ok h3 rfl

/-- **`cv_rec_dup` is the identity**, the house `foo_dup`. -/
theorem cv_rec_dup_refines {cv cv'} (h : frontend.export_c.cv_rec_dup cv = ok cv') :
    absCVRec cv' = absCVRec cv := by sorry

/-- **`ind_ctor_rec_dup` is the identity.** -/
theorem ind_ctor_rec_dup_refines {c c'}
    (h : frontend.export_c.ind_ctor_rec_dup c = ok c') :
    absIndCtorRec c' = absIndCtorRec c := by sorry

/-- **`m_ind_type_recs_dup` is the identity from the cursor on.** -/
theorem m_ind_type_recs_dup_refines {ts i out v}
    (h : frontend.export_c.m_ind_type_recs_dup ts i out = ok v) :
    v.val.map absMIndTypeRec = out.val.map absMIndTypeRec ++
      (ts.val.drop i.val).map absMIndTypeRec := by
  rw [frontend.export_c.m_ind_type_recs_dup] at h
  refine vec_cursor_copy ts absMIndTypeRec absMIndTypeRec
    (fun k out => frontend.export_c.m_ind_type_recs_dup_loop ts out (alloc.vec.Vec.len ts) k)
    ?_ ?_ i out v h
  · intro k out o hn h
    rw [frontend.export_c.m_ind_type_recs_dup_loop.eq_def] at h
    rw [if_neg (show ¬ k < alloc.vec.Vec.len ts by scalar_tac)] at h
    rw [← Result.ok_injective h]
  · intro k x out o hx h
    have hk : k.val < ts.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [frontend.export_c.m_ind_type_recs_dup_loop.eq_def] at h
    rw [if_pos (show k < alloc.vec.Vec.len ts by scalar_tac)] at h
    obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have htx : t = x := Option.some_injective _ ((vec_index_some ht).symm.trans hx)
    subst htx
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨cs, hcs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, e2⟩ := cursor_push hout1 hk1
    refine ⟨k1, _, out1, e2, e1, ?_, h⟩
    simp only [absMIndTypeRec, i_constant_val_dup_abs hiv, nidx_vec_dup_val hcs]

/-- **`m_ind_ctor_recs_dup` is the identity from the cursor on.** -/
theorem m_ind_ctor_recs_dup_refines {cs i out v}
    (h : frontend.export_c.m_ind_ctor_recs_dup cs i out = ok v) :
    v.val.map absMIndCtorRec = out.val.map absMIndCtorRec ++
      (cs.val.drop i.val).map absMIndCtorRec := by
  rw [frontend.export_c.m_ind_ctor_recs_dup] at h
  refine vec_cursor_copy cs absMIndCtorRec absMIndCtorRec
    (fun k out => frontend.export_c.m_ind_ctor_recs_dup_loop cs out (alloc.vec.Vec.len cs) k)
    ?_ ?_ i out v h
  · intro k out o hn h
    rw [frontend.export_c.m_ind_ctor_recs_dup_loop.eq_def] at h
    rw [if_neg (show ¬ k < alloc.vec.Vec.len cs by scalar_tac)] at h
    rw [← Result.ok_injective h]
  · intro k x out o hx h
    have hk : k.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [frontend.export_c.m_ind_ctor_recs_dup_loop.eq_def] at h
    rw [if_pos (show k < alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have htx : t = x := Option.some_injective _ ((vec_index_some ht).symm.trans hx)
    subst htx
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, e2⟩ := cursor_push hout1 hk1
    refine ⟨k1, _, out1, e2, e1, ?_, h⟩
    simp only [absMIndCtorRec, i_constant_val_dup_abs hiv]

/-- **`m_ind_rec_recs_dup` is the identity from the cursor on.** -/
theorem m_ind_rec_recs_dup_refines {rs i out v}
    (h : frontend.export_c.m_ind_rec_recs_dup rs i out = ok v) :
    v.val.map absMIndRecRec = out.val.map absMIndRecRec ++
      (rs.val.drop i.val).map absMIndRecRec := by
  rw [frontend.export_c.m_ind_rec_recs_dup] at h
  refine vec_cursor_copy rs absMIndRecRec absMIndRecRec
    (fun k out => frontend.export_c.m_ind_rec_recs_dup_loop rs out (alloc.vec.Vec.len rs) k)
    ?_ ?_ i out v h
  · intro k out o hn h
    rw [frontend.export_c.m_ind_rec_recs_dup_loop.eq_def] at h
    rw [if_neg (show ¬ k < alloc.vec.Vec.len rs by scalar_tac)] at h
    rw [← Result.ok_injective h]
  · intro k x out o hx h
    have hk : k.val < rs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [frontend.export_c.m_ind_rec_recs_dup_loop.eq_def] at h
    rw [if_pos (show k < alloc.vec.Vec.len rs by scalar_tac)] at h
    obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have htx : t = x := Option.some_injective _ ((vec_index_some ht).symm.trans hx)
    subst htx
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rl, hrl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, e2⟩ := cursor_push hout1 hk1
    refine ⟨k1, _, out1, e2, e1, ?_, h⟩
    simp only [absMIndRecRec, i_constant_val_dup_abs hiv, i_rec_rules_dup_abs hrl]

/-- **`block_rec_dup` is the identity.** -/
theorem block_rec_dup_refines {b b'}
    (h : frontend.export_c.block_rec_dup b = ok b') :
    absBlockRec b' = absBlockRec b := by
  rw [frontend.export_c.block_rec_dup] at h
  obtain ⟨v1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v3, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v5, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  have e1 := m_ind_type_recs_dup_refines h1
  have e3 := m_ind_ctor_recs_dup_refines h3
  have e5 := m_ind_rec_recs_dup_refines h5
  simp only [show ((0#usize : Std.Usize)).val = 0 by rfl, List.drop_zero,
    show (alloc.vec.Vec.with_capacity frontend.types.MIndTypeRec
      (alloc.vec.Vec.len b.types)).val = [] from rfl,
    show (alloc.vec.Vec.with_capacity frontend.types.MIndCtorRec
      (alloc.vec.Vec.len b.ctors)).val = [] from rfl,
    show (alloc.vec.Vec.with_capacity frontend.types.MIndRecRec
      (alloc.vec.Vec.len b.recs)).val = [] from rfl,
    List.map_nil, List.nil_append] at e1 e3 e5
  simp only [absBlockRec, e1, e3, e5]

/-! ## The projection-owner census's three shape lists -/

/-- **`proj_types_of`** — the twin's `tys.mapM` into the census's type tuples. -/
theorem proj_types_of_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.proj_types_of rsd tys = ok o) :
    SimLR absProjTypeRecL lst o
      ((absIndTypeRecs tys).mapM fun t => do
        let cv ← parseCVD lsd t.cv
        pure (cv.name, cv.levelParams, cv.type, t.numParams, t.numIndices,
          ← t.ctors.mapM lsd.name, t.isRec)) := by sorry

/-- **`proj_ctors_of`** — the census's constructor tuples. -/
theorem proj_ctors_of_refines {rsd lsd lst cts o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.proj_ctors_of rsd cts = ok o) :
    SimLR absProjCtorRecL lst o
      ((absIndCtorRecs cts).mapM fun c => do
        let cv ← parseCVD lsd c.cv
        pure (cv.name, c.numFields, cv.type)) := by sorry

/-- **`proj_recs_of`** — the census's recursor tuples. -/
theorem proj_recs_of_refines {rsd lsd lst rcs o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.proj_recs_of rsd rcs = ok o) :
    SimLR absProjRecRecL lst o
      ((absIndRecRecs rcs).mapM fun r => do
        let cv ← parseCVD lsd r.cv
        pure (cv.name, cv.levelParams, cv.type, r.numMotives, r.numMinors)) := by
  sorry

/-- **`note_proj_owners`** — the twin's `owners.foldl` into `projOwners`.  The
port writes the table unconditionally where the twin's `match` sends `[]` to
`pure st`; a `foldl` over `[]` is the identity, so the two agree (task #87
§13's "two shape differences checked and benign"). -/
theorem note_proj_owners_refines {rsd lsd owners rsd'} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd)
    (h : frontend.export_c.note_proj_owners rsd owners = ok rsd') :
    StateDRel rsd'
      { lsd with projOwners := (absProjRecOwnerL owners).foldl
                   (fun m o => m.insert o.T o) lsd.projOwners } ∧
      StateDInv rsd' := by sorry

/-- **`register_proj_owners` refines `registerProjOwners`**
(`ExportC.lean:401-421`). -/
theorem register_proj_owners_refines {pers rst lst rsd lsd tys cts rcs block o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.register_proj_owners pers rst rsd tys cts rcs block
      = ok o) :
    SimD pers lst o
      (registerProjOwners lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
        (absIndRecRecs rcs) (absICIL block)) := by sorry

/-! ## The parse result -/

/-- **`parse_result_of_state` refines `ParseResultD.ofState`**
(`ExportC.lean:717-719`). -/
theorem parse_result_of_state_refines {rsd lsd p} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_result_of_state rsd = ok p) :
    ParseResultDRel p (ParseResultD.ofState lsd) := by
  rw [frontend.export_c.parse_result_of_state] at h
  cases Result.ok_injective h
  exact ⟨hd.decls, hd.projRewrites, hd.inModelled, hd.genRecords, hd.genOwner,
    hd.inModelGen, hd.inModelDeclined⟩

/-- **`at_line` refines `atLine`** (`ExportC.lean:855-859`): the line number
folded into the message.  The KIND — hence the exit code — is untouched, and
the kind is all the theorem reads. -/
theorem at_line_refines {e n ce} (h : frontend.export_c.at_line e n = ok ce) :
    absAErrKind ce = absAErrKind e := by sorry

/-! ## Line-layer shape lemmas (moved from `Top.lean` by task #97-P5-Front round 3,
so that `ExportCInd.lean`'s `install_ind_d` can compose with them) -/

theorem SimDV.of_run_eq {pers : arena.store.PersTier} {lst lst1 : AState}
    {o : core.result.Result Unit frontend.export_c.LineErr ×
      arena.monad.AState × frontend.export_c.StateD}
    {x y : AM (Arena.Frontend.StateD ⊕ Arena.Frontend.RecordVerdict)}
    (h : SimDV pers lst1 o x) (hxy : y.run lst = x.run lst1) : SimDV pers lst o y := by
  rcases o with ⟨r, rst', rsd'⟩
  unfold SimDV at h ⊢
  rw [hxy]; exact h

/-- **A table-entry writer inside the line layer**: the twin's
`do pure (.inl (← x))` over a `SimD` step. -/
theorem SimD.toSimDV_inl {pers : arena.store.PersTier} {lst : AState}
    {o : core.result.Result Unit frontend.export_c.LineErr ×
      arena.monad.AState × frontend.export_c.StateD}
    {x : AM Arena.Frontend.StateD} (h : SimD pers lst o x) :
    SimDV pers lst o (do pure (Sum.inl (← x))) := by
  rcases o with ⟨r, rst', rsd'⟩
  simp only [SimD] at h
  cases r with
  | Ok u =>
    obtain ⟨lsd', lst', hx, hd, hi, hrel, hinv⟩ := h
    refine SimDV.mk (lsd' := lsd') ?_ hd hi hrel hinv
    simp only [am_run_bind', hx, except_ok_bind]; rfl
  | Err e =>
    exact SimDV.of_bind (f := fun p => (pure (Sum.inl p.1) : AM _).run p.2) h
      (by simp only [am_run_bind'])

/-- A twin prefix that answers `a`, then the rest. -/
theorem SimDV.bind_ok {α : Type} {pers : arena.store.PersTier} {lst lst1 : AState}
    {o : core.result.Result Unit frontend.export_c.LineErr ×
      arena.monad.AState × frontend.export_c.StateD}
    {x : AM α} {f : α → AM (Arena.Frontend.StateD ⊕ Arena.Frontend.RecordVerdict)} {a : α}
    (hx : x.run lst = .ok (a, lst1))
    (h : SimDV pers lst1 o (f a)) : SimDV pers lst o (x >>= f) := by
  have hrun : (x >>= f).run lst = (f a).run lst1 := by
    simp only [am_run_bind', hx, except_ok_bind]
  exact SimDV.of_run_eq h hrun

/-! ## The axiom census

The six closed lemmas of this file, pinned.  (The fifteen `*_no_claim`
statements are `trivial` and carry no axiom at all.) -/

/-- info: 'ConRon.Refine2.Frontend.fail_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fail_refines

/-- info: 'ConRon.Refine2.Frontend.merr_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merr_refines

/-- info: 'ConRon.Refine2.Frontend.declined_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms declined_refines

/-- info: 'ConRon.Refine2.Frontend.invalid_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invalid_refines

/-- info: 'ConRon.Refine2.Frontend.sat_sub_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sat_sub_refines

/-- info: 'ConRon.Refine2.Frontend.rel_offset_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rel_offset_refines

/--
info: 'ConRon.Refine2.Frontend.i_constant_info_to_constant_val_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms i_constant_info_to_constant_val_refines

/-- info: 'ConRon.Refine2.Frontend.note_entries_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms note_entries_refines

/-- info: 'ConRon.Refine2.Frontend.push_decl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms push_decl_refines

end ConRon.Refine2.Frontend
