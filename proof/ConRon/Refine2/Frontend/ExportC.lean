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

## `sorry` count in this file: 57
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

/-! ## The store fuel

The twin's `storeFuel` is the store's node count plus one, which bounds the
length of any path through it because a child is interned before its parent.
The port reads the same counter. -/

theorem store_fuel_refines {pers rst lst v}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.store_fuel pers rst.store = ok v) :
    SimR absU lst v storeFuel := by sorry

/-! ## The parse state -/

/-- **`state_d_init` refines `StateD.init`** (`ExportC.lean:709-713`): index 0
of the name table is the format's implicit `Name.anonymous` and index 0 of the
level table its `Level.zero`, and over handles that means the handles those
two nodes intern at — in the PERSISTENT tier, which is the tier the whole
parse appends to.

Both arms (task #97-P5-Front restated it from a success-only statement, which
left `parse_bytes`/`parse_chunks` nothing to say about their `(e, 0)` arm).
**Open on the `M_FROZEN` ruling**, like `prepare::prelude_key`: at a frozen
tier the port's intern answers `Internal` where the twin appends, so the error
arm holds only once the frozen guard is `Native`; with
`estore_intern_name_abs`/`estore_intern_level_abs`'s `hfrozen` it closes. -/
theorem state_d_init_refines {pers rst lst in_model census o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.state_d_init pers rst.store in_model census = ok o) :
    SimRel (fun rsd lsd => StateDRel rsd lsd ∧ StateDInv rsd) pers lst
      (o.1, withStore rst o.2) (StateD.init in_model census) := by sorry

/-- **`state_model_ctx`** — the three tables the modeller reads, borrowed off
the state (`types::ModelCtx`'s deviation).  The twin builds the three closures
inline in `installIndD`; this is `CtxRel` at them. -/
theorem state_model_ctx_refines {rsd lsd rc} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd) (h : frontend.export_c.state_model_ctx rsd = ok rc) :
    CtxRel rc ⟨fun n => lsd.constTypes[n]?, fun n => lsd.heights.getD n 0,
      fun n => lsd.indBlocks[n]?⟩ := by sorry

/-! ## Booking a pushed record -/

/-- **`note_one`** — one constant's entry. -/
theorem note_one_refines {cv h' v} (h : frontend.export_c.note_one cv h' = ok v) :
    absNoteEntryL v =
      [(absNIdx cv.name, cv.level_params.val.map absNIdx, absEIdx cv.ty,
        h'.map absU)] := by sorry

/-- **`note_block`** — the `indDecl` arm's `block.mapM`, at a cursor. -/
theorem note_block_refines {pers rst lst bl i out o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.note_block pers rst.store bl i out = ok o) :
    SimL absNoteEntryL pers lst (o.1, withStore rst o.2)
      (do
        let es ← (absICILFrom bl i).mapM fun ci => do
          let v ← ci.toConstantVal
          pure (v.name, v.levelParams, v.type, (none : Option Nat))
        pure (absNoteEntryL out ++ es)) := by sorry

/-- **`note_decl_entries`** — the twin's `cvs`: the constants one pushed
declaration declares.  The `.basisDecl` arm fails loudly on both sides (the
twin's own choice: no frontend function produces one). -/
theorem note_decl_entries_refines {pers rst lst d o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.note_decl_entries pers rst.store d = ok o) :
    SimL absNoteEntryL pers lst (o.1, withStore rst o.2)
      (noteDeclEntries (absIDeclaration d)) := by sorry

/-- **`note_entries`** — the twin's `cvs.foldl` into `constTypes`/`heights`. -/
theorem note_entries_refines {rsd lsd es rsd'} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd)
    (h : frontend.export_c.note_entries rsd es = ok rsd') :
    StateDRel rsd' (noteEntries lsd (absNoteEntryL es)) ∧ StateDInv rsd' := by sorry

/-- **`note_decl` refines `noteDecl`** (`ExportC.lean:138-155`). -/
theorem note_decl_refines {pers rst lst rsd lsd d o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.note_decl pers rst.store rsd d = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (noteDecl lsd (absIDeclaration d)) := by sorry

/-- **`push_decl` refines `pushDecl`** (`ExportC.lean:158-159`). -/
theorem push_decl_refines {pers rst lst rsd lsd d o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.push_decl pers rst.store rsd d = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (pushDecl lsd (absIDeclaration d)) := by sorry

/-! ## The index tables -/

/-- **`st_name` refines `StateD.name`** (`ExportC.lean:163-166`). -/
theorem st_name_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_name rsd i = ok o) :
    SimLR absNIdx lst o (lsd.name (absU i)) := by sorry

/-- **`st_level` refines `StateD.level`** (`ExportC.lean:170-173`). -/
theorem st_level_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_level rsd i = ok o) :
    SimLR absLIdx lst o (lsd.level (absU i)) := by sorry

/-- **`st_expr` refines `StateD.expr`** (`ExportC.lean:177-180`). -/
theorem st_expr_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_expr rsd i = ok o) :
    SimLR absEIdx lst o (lsd.expr (absU i)) := by sorry

/-- **`st_names`** — the twin's `ns.mapM st.name`. -/
theorem st_names_refines {rsd lsd lst is o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_names rsd is = ok o) :
    SimLR absNIdxL lst o ((is.val.map absU).mapM lsd.name) := by sorry

/-- **`st_levels`** — the twin's `us.mapM st.level`. -/
theorem st_levels_refines {rsd lsd lst is o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_levels rsd is = ok o) :
    SimLR (fun v => v.val.map absLIdx) lst o
      ((is.val.map absU).mapM lsd.level) := by sorry

/-- **`get_decl_d` refines `getDeclD`** (`ExportC.lean:185-186`). -/
theorem get_decl_d_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.get_decl_d rsd i = ok o) :
    SimLR absEIdx lst o (getDeclD lsd (absU i)) := by sorry

/-- **`parse_pw_d` refines `parsePwD`** (`ExportC.lean:192-197`): the `pw`
datum over the direct name table.  `PropWhen` holds con-leche `Name`s, so the
resolved handles are read BACK — which is `denoteN` itself. -/
theorem parse_pw_d_refines {pers rst lst rsd lsd r o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_pw_d pers rst.store rsd r = ok o) :
    SimLR ConRon.Refine.absPropWhen lst o (parsePwD lsd (absPwRec r)) := by sorry

/-! ## The rebinding test

con-leche measured 17 % of its parse phase on this detail, so the three tests
are their own functions on a borrowed state — and they are the one place the
parse REJECTS a stream for a reason that is not the scanner's. -/

/-- **`st_fresh_name`** — index `i` is not already bound. -/
theorem st_fresh_name_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_fresh_name rsd i = ok o) :
    SimLR (fun _ => ()) lst o
      (if (lsd.names.get? (absU i)).isSome then
        fail (.internal (reboundError "name" (absU i))) else pure ()) := by sorry

/-- **`st_fresh_level`** — index `i` is not already bound. -/
theorem st_fresh_level_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_fresh_level rsd i = ok o) :
    SimLR (fun _ => ()) lst o
      (if (lsd.levels.get? (absU i)).isSome then
        fail (.internal (reboundError "level" (absU i))) else pure ()) := by sorry

/-- **`st_fresh_expr`** — index `i` is not already bound. -/
theorem st_fresh_expr_refines {rsd lsd lst i o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.st_fresh_expr rsd i = ok o) :
    SimLR (fun _ => ()) lst o
      (if (lsd.exprs.get? (absU i)).isSome then
        fail (.internal (reboundError "expr" (absU i))) else pure ()) := by sorry

/-! ## The three table-entry writers -/

/-- **`parse_name_entry_d` refines `parseNameEntryD`**
(`ExportC.lean:226-236`). -/
theorem parse_name_entry_d_refines {pers rst lst rsd lsd i r o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd) (hs : NameRecStrWF r)
    (h : frontend.export_c.parse_name_entry_d pers rst.store rsd i r = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (parseNameEntryD lsd (absU i) (absNameRec r)) := by sorry

/-- **`parse_level_rec_d`** — the value half of `parseLevelEntryD`, which the
twin writes inline and the port factors out (the escape-hatch definition
`RefineOld/Frontend/StateDR.lean` needed for the same shape). -/
theorem parse_level_rec_d_refines {rsd lsd lst r o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_level_rec_d rsd r = ok o) :
    SimLR absLNodeView lst o (parseLevelRecD lsd (absLevelRec r)) := by sorry

/-- **`parse_level_entry_d` refines `parseLevelEntryD`**
(`ExportC.lean:240-255`). -/
theorem parse_level_entry_d_refines {pers rst lst rsd lsd i r o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.parse_level_entry_d pers rst.store rsd i r = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (parseLevelEntryD lsd (absU i) (absLevelRec r)) := by sorry

/-- **`parse_expr_rec_d`** — the value half of `parseExprEntryD`.  Its
`NatVal` arm is `scan_types.rs`'s deviation 2: the port keeps the literal's
decimal digits, so the arm needs `NatValSpec`. -/
theorem parse_expr_rec_d_refines {pers rst lst rsd lsd r o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hnat : NatValSpec r)
    (h : frontend.export_c.parse_expr_rec_d pers rst.store rsd r = ok o) :
    SimL absEIdx pers lst (o.1, withStore rst o.2)
      (parseExprRecD lsd (absExprRec r)) := by sorry

/-- **`parse_expr_entry_d` refines `parseExprEntryD`**
(`ExportC.lean:259-282`). -/
theorem parse_expr_entry_d_refines {pers rst lst rsd lsd i r o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd) (hnat : NatValSpec r)
    (h : frontend.export_c.parse_expr_entry_d pers rst.store rsd i r = ok o) :
    SimD pers lst (o.1, withStore rst o.2.1, o.2.2)
      (parseExprEntryD lsd (absU i) (absExprRec r)) := by sorry

/-- **`parse_cv_d` refines `parseCVD`** (`ExportC.lean:286-290`). -/
theorem parse_cv_d_refines {rsd lsd lst cv o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_cv_d rsd cv = ok o) :
    SimLR absIConstantVal lst o (parseCVD lsd (absCVRec cv)) := by sorry

/-! ## The projection rewrite's hooks -/

/-- **`proj_level_of`** — the artifact's recorded field sort. -/
theorem proj_level_of_refines {rsd lsd k o} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd) (h : frontend.export_c.proj_level_of rsd k = ok o) :
    o.map absLIdx = lsd.projLevels[absNIdx k]? := by sorry

/-- **`proj_owner_of`** — the recorded owner of a type former. -/
theorem proj_owner_of_refines {rsd lsd t o} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd) (h : frontend.export_c.proj_owner_of rsd t = ok o) :
    o.map absProjRecOwner = lsd.projOwners[absNIdx t]? := by sorry

/-- **`proj_rewrite_at`** — the port's split past the two table lookups. -/
theorem proj_rewrite_at_refines {pers rst lst rsd lsd cv vl t i fuel o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.proj_rewrite_at pers rst rsd cv vl t i fuel = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (do
        match lsd.projOwners[absNIdx t]?, lsd.projLevels[absNIdx cv.name]? with
        | some ow, some l =>
          projRecValue (absU fuel) ow l (absEIdx cv.ty) (absEIdx vl) (absU i)
        | _, _ => pure none) := by sorry

/-- **`proj_rewrite_d` refines `projRewriteD`** (`ExportC.lean:302-322`). -/
theorem proj_rewrite_d_refines {pers rst lst rsd lsd cv vl o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.proj_rewrite_d pers rst rsd cv vl = ok o) :
    Sim (Option.map absEIdx) (fun _ => True) pers lst o
      (projRewriteD lsd (absIConstantVal cv) (absEIdx vl)) := by sorry

/-- **`note_proj_iota` refines `noteProjIota`** (`ExportC.lean:325-335`). -/
theorem note_proj_iota_refines {pers rst lst rsd lsd cvp o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.note_proj_iota pers rst rsd cvp = ok o) :
    ∀ _u, o.1 = .Ok _u → ∃ lsd' lst',
      (noteProjIota lsd (absIConstantVal cvp)).run lst = .ok (lsd', lst') ∧
      StateDRel o.2.2 lsd' ∧ StateDInv o.2.2 ∧ AStateRel pers o.2.1 lst' ∧
      AStateInv pers o.2.1 ∧ Ext lst.store lst'.store := by sorry

/-! ## The modeller's booking -/

/-- **`push_gen_d` refines `pushGenD`** (`ExportC.lean:339-345`). -/
theorem push_gen_d_refines {pers rst lst rsd lsd d o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
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
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.push_gen_list pers rst rsd gen t0 = ok o) :
    SimD pers lst o (pushGenList lsd (absIDeclL gen) (absNIdx t0)) := by sorry

/-! ## Two spine walks -/

/-- **`ind_pi_tele_len` refines `indPiTeleLen`** (`ExportC.lean:358-364`). -/
theorem ind_pi_tele_len_refines {pers rst lst fuel h' o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.ind_pi_tele_len pers rst.store fuel h' = ok o) :
    SimLR absU lst o (indPiTeleLen (absU fuel) (absEIdx h')) := by sorry

/-- **`pi_result`** — three lines of spine walk, spelled locally in its one
frontend caller (`k_expected_of`) rather than left as a hole; the twin's is
`Arena/ExprOps.lean`'s `piResult`. -/
theorem pi_result_refines {pers rst lst fuel h' o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.pi_result pers rst.store fuel h' = ok o) :
    SimLR absEIdx lst o (piResult (absU fuel) (absEIdx h')) := by sorry

/-! ## The recursor rules and the block record -/

/-- **`parse_rule_d` refines `parseRuleD`** (`ExportC.lean:368-370`). -/
theorem parse_rule_d_refines {rsd lsd lst ru o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_rule_d rsd ru = ok o) :
    SimLR absIRecRule lst o (parseRuleD lsd (absRuleRec ru)) := by sorry

/-- **`parse_rules_d`** — the twin's `r.rules.mapM (parseRuleD st)`. -/
theorem parse_rules_d_refines {rsd lsd lst rus o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.parse_rules_d rsd rus = ok o) :
    SimLR absIRecRuleL lst o
      ((absRuleRecs rus).mapM (parseRuleD lsd)) := by sorry

/-- **`cv_rec_dup` is the identity**, the house `foo_dup`. -/
theorem cv_rec_dup_refines {cv cv'} (h : frontend.export_c.cv_rec_dup cv = ok cv') :
    absCVRec cv' = absCVRec cv := by sorry

/-- **`ind_ctor_rec_dup` is the identity.** -/
theorem ind_ctor_rec_dup_refines {c c'}
    (h : frontend.export_c.ind_ctor_rec_dup c = ok c') :
    absIndCtorRec c' = absIndCtorRec c := by sorry

/-- **`block_rec_types`** — the block record's type half. -/
theorem block_rec_types_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_types rsd tys = ok o) :
    SimLR (fun v => v.val.map absMIndTypeRec) lst o
      ((absIndTypeRecs tys).mapM fun t => do
        pure { cv := ← parseCVD lsd t.cv, nP := t.numParams, nIdx := t.numIndices,
               ctors := ← t.ctors.mapM lsd.name, isRec := t.isRec,
               isReflexive := t.isReflexive, numNested := t.numNested :
               MIndTypeRec }) := by sorry

/-- **`block_rec_ctors`** — the block record's constructor half. -/
theorem block_rec_ctors_refines {rsd lsd lst ctors o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_ctors rsd ctors = ok o) :
    SimLR (fun v => v.val.map absMIndCtorRec) lst o
      ((absIndCtorRecs ctors).mapM fun c => do
        pure { cv := ← parseCVD lsd c.cv, nP := c.numParams,
               nF := c.numFields : MIndCtorRec }) := by sorry

/-- **`block_rec_recs`** — the block record's recursor half. -/
theorem block_rec_recs_refines {rsd lsd lst recs o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_recs rsd recs = ok o) :
    SimLR (fun v => v.val.map absMIndRecRec) lst o
      ((absIndRecRecs recs).mapM fun r => do
        let rules ← r.rules.mapM (parseRuleD lsd)
        pure { cv := ← parseCVD lsd r.cv, nP := r.numParams, nM := r.numMotives,
               nm := r.numMinors, nI := r.numIndices, rules := rules :
               MIndRecRec }) := by sorry

/-- **`block_rec_of` refines `blockRecOf`** (`ExportC.lean:374-399`). -/
theorem block_rec_of_refines {rsd lsd lst tys cts rcs o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.block_rec_of rsd tys cts rcs = ok o) :
    SimLR absBlockRec lst o
      (blockRecOf lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
        (absIndRecRecs rcs)) := by sorry

/-- **`m_ind_type_recs_dup` is the identity from the cursor on.** -/
theorem m_ind_type_recs_dup_refines {ts i out v}
    (h : frontend.export_c.m_ind_type_recs_dup ts i out = ok v) :
    v.val.map absMIndTypeRec = out.val.map absMIndTypeRec ++
      (ts.val.drop i.val).map absMIndTypeRec := by sorry

/-- **`m_ind_ctor_recs_dup` is the identity from the cursor on.** -/
theorem m_ind_ctor_recs_dup_refines {cs i out v}
    (h : frontend.export_c.m_ind_ctor_recs_dup cs i out = ok v) :
    v.val.map absMIndCtorRec = out.val.map absMIndCtorRec ++
      (cs.val.drop i.val).map absMIndCtorRec := by sorry

/-- **`m_ind_rec_recs_dup` is the identity from the cursor on.** -/
theorem m_ind_rec_recs_dup_refines {rs i out v}
    (h : frontend.export_c.m_ind_rec_recs_dup rs i out = ok v) :
    v.val.map absMIndRecRec = out.val.map absMIndRecRec ++
      (rs.val.drop i.val).map absMIndRecRec := by sorry

/-- **`block_rec_dup` is the identity.** -/
theorem block_rec_dup_refines {b b'}
    (h : frontend.export_c.block_rec_dup b = ok b') :
    absBlockRec b' = absBlockRec b := by sorry

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
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
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

end ConRon.Refine2.Frontend
