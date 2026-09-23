/-
# `ConRon.Refine2.Frontend.ExportCInd` — the inductive record

**Task #97-P5-Frontend**, the second of `frontend/export_c.rs`'s three files:
`validate_ind_d` (the half of an inductive record's processing that reads the
state and changes nothing) and `install_ind_d` (the half that changes it), and
their twenty-five helpers.

## Why this is twenty-seven functions against the twin's two

`validateIndD` is one 100-line `do` block with **two `for`/`mut` loops** and
eleven verdicts; `installIndD` is one 60-line block.  Aeneas copies the code
AFTER a loop into every exit of it, so each loop is its own function whose
tail is one line (`export_c.rs`'s own note, and `con_ron_core`'s arrangement
before it).  Eleven of the twenty-seven are message builders, and their
statements are in `Refine2/Frontend/ExportC.lean`, as explicit no-claims.

**The eleven verdicts are what this tier must not weaken.**  DESIGN §8.3:
*"names are compared for inequality throughout the checker"*, and the parse's
redundant-field checks are the reason a contradicted `numFields` or a
duplicated constructor name is a REJECT and not an accept.  Task #97e part 1
measured them: 23 of the 60 fixtures the arena agreed on at that point were
`validateIndD` rejects.  So `validate_ind_d_refines` is the load-bearing
statement of this file and the helpers exist to feed it.

## What the helper statements are stated against

Eleven of the helpers are PURE or read only the index tables, and their
statement is an equation against the twin's own expression, written inline —
`any_ty_unsafe` is `tys.any (·.isUnsafe)`, `flatten_listed` is
`listed.flatten`, and so on.  The four `check_*` ones and the two `order_*`
ones are the two `for` loops' bodies and have no twin expression of their own;
they are stated against a named reading in the doc comment and **their
transcriptions are what `Refine2/Frontend/Spec.lean` still owes** — the one
group of this tier where the statement is about the port's own arm rather
than about a twin clause.  DESIGN.md's section lists them.

## `sorry` count in this file: 26
-/
import ConRon.Refine2.Frontend.ExportC

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IdTable NameRec LevelRec ExprRec PwRec CVRec HintsRec RuleRec
  IndTypeRec IndCtorRec IndRecRec DeclRec LineRec)

/-! ## The block's own fields -/

/-- **`any_ty_unsafe`** — the twin's `tys.any (·.isUnsafe)`: an `unsafe
inductive` is DECLINED, not an error. -/
theorem any_ty_unsafe_refines {tys v}
    (h : frontend.export_c.any_ty_unsafe tys = ok v) :
    v = (absIndTypeRecs tys).any (·.isUnsafe) := by sorry

/-- **`any_ty_nested`** — the twin's `tys.any (·.numNested != 0)`, the flag
that turns the recursor checks off. -/
theorem any_ty_nested_refines {tys v}
    (h : frontend.export_c.any_ty_nested tys = ok v) :
    v = (absIndTypeRecs tys).any (·.numNested != 0) := by sorry

/-- **`all_num_params`** — the twin's `nPs.all (· == nPd)`: the declared
parameter count is well defined for the block exactly when its type records
agree on it. -/
theorem all_num_params_refines {tys n_pd v}
    (h : frontend.export_c.all_num_params tys n_pd = ok v) :
    v = ((absIndTypeRecs tys).map (·.numParams)).all (· == absU n_pd) := by sorry

/-- **`ty_names_of`** — the twin's `tys.mapM fun t => st.name t.cv.name`. -/
theorem ty_names_of_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ty_names_of rsd tys = ok o) :
    SimLR absNIdxL lst o
      ((absIndTypeRecs tys).mapM fun t => lsd.name t.cv.name) := by sorry

/-- **`ty_types_of`** — the twin's `tys.mapM fun t => getDeclD st t.cv.type`. -/
theorem ty_types_of_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ty_types_of rsd tys = ok o) :
    SimLR absEIdxL lst o
      ((absIndTypeRecs tys).mapM fun t => getDeclD lsd t.cv.type) := by sorry

/-- **`listed_ctors_of`** — the twin's `tys.mapM fun t => t.ctors.mapM
st.name`. -/
theorem listed_ctors_of_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.listed_ctors_of rsd tys = ok o) :
    SimLR (fun v => v.val.map absNIdxL) lst o
      ((absIndTypeRecs tys).mapM fun t => t.ctors.mapM lsd.name) := by sorry

/-- **`ctor_names_of`** — the twin's `cts.mapM fun c => st.name c.cv.name`. -/
theorem ctor_names_of_refines {rsd lsd lst cts o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ctor_names_of rsd cts = ok o) :
    SimLR absNIdxL lst o
      ((absIndCtorRecs cts).mapM fun c => lsd.name c.cv.name) := by sorry

/-- **`flatten_listed`** — the twin's `listed.flatten`. -/
theorem flatten_listed_refines {listed v}
    (h : frontend.export_c.flatten_listed listed = ok v) :
    absNIdxL v = (listed.val.map absNIdxL).flatten := by sorry

/-- **`names_have_dup`** — the twin's `flat.Nodup`, complemented.  The port's
algorithm is a handle-keyed SET PASS and not the quadratic scan, because
Aeneas answers *"Returns inside of nested loops are not supported yet"* to the
obvious spelling (extraction rule 4); the two decide the same predicate, which
is what this says. -/
theorem names_have_dup_refines {flat v}
    (h : frontend.export_c.names_have_dup flat = ok v) :
    v = !(absNIdxL flat).Nodup := by sorry

/-- **`ctor_index_of`** — the twin's `ctorNames.foldl` into `ctorIx`.  Task
#87 §20's port bug — *"`ctor_index_of` was first-wins"* — is a fact about the
`Expr`-tree port that this statement is what would catch again: the twin's
fold is LAST-wins, because `Std.HashMap.insert` overwrites. -/
theorem ctor_index_of_refines {ns m}
    (h : frontend.export_c.ctor_index_of ns = ok m) :
    NameIdxRel m
      ((((absNIdxL ns).foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
        (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0))).1) := by sorry

/-- **`show_name`** — a handle read back for a message.  The port's readback
is `denoteN`'s; messages are never compared, so what is claimed is that it
succeeds wherever the twin's `readName` does. -/
theorem show_name_refines {pers rst lst h' o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.show_name pers rst.store h' = ok o) :
    ∀ m, o = .Ok m → ∃ s lst', (readName (absNIdx h')).run lst = .ok (s, lst') := by
  sorry

/-! ## The first `for` loop: the constructors in the block's own order

`check_one_ctor` is the loop's body — the `cidx`, `induct` and `numFields`
checks at one constructor — and `order_type_ctors` / `order_block_ctors` are
the two nested loops themselves.  These three have no twin expression; see
the module note. -/

/-- **`check_one_ctor`** — the three redundant-field checks at one
constructor: `cidx` names its position, `induct` names its type former, and
`numParams + numFields` is the constructor type's own Π-telescope length. -/
theorem check_one_ctor_refines {pers rst lst rsd lsd fuel n t c j n_pd o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd)
    (h : frontend.export_c.check_one_ctor pers rst.store fuel rsd n t c j n_pd
      = ok o) :
    SimLR (fun _ => ()) lst o
      (do
        let lc := absIndCtorRec c
        match lc.cidx with
        | some ci => if ci != absU j then fail (.internal "cidx") else pure ()
        | none => pure ()
        match lc.induct with
        | some iw => do
          let iwn ← lsd.name iw
          if iwn != absNIdx t then fail (.internal "induct") else pure ()
        | none => pure ()
        let cty ← getDeclD lsd lc.cv.type
        let tele ← indPiTeleLen (absU fuel) cty
        if absU n_pd + lc.numFields != tele then fail (.internal "fields")
        else pure ()) := by sorry

/-- **`order_type_ctors`** — the inner `for n in ns` loop, at one type
former. -/
theorem order_type_ctors_refines
    {pers rst lst rsd lsd fuel t ns cts ctor_ix lm n_pd out o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hx : NameIdxRel ctor_ix lm)
    (h : frontend.export_c.order_type_ctors pers rst.store fuel rsd t ns cts
      ctor_ix n_pd out = ok o) :
    ∀ v, o = .Ok v →
      ∃ pre, absIndCtorRecs v = absIndCtorRecs out ++ pre ∧
        pre.length = (absNIdxL ns).length := by sorry

/-- **`order_block_ctors`** — the outer `for tn in tyNames.zip listed` loop:
the constructors in the block's own order, `types[].ctors` in type order. -/
theorem order_block_ctors_refines
    {pers rst lst rsd lsd fuel ty_names listed cts ctor_ix lm n_pd o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hx : NameIdxRel ctor_ix lm)
    (h : frontend.export_c.order_block_ctors pers rst.store fuel rsd ty_names
      listed cts ctor_ix n_pd = ok o) :
    ∀ v, o = .Ok v →
      (absIndCtorRecs v).length = ((listed.val.map absNIdxL).flatten).length := by
  sorry

/-! ## The K flag and the recursor records -/

/-- **`k_expected_of`** — official's `is_K_target`: a single type former with
a single constructor of zero fields whose result sort is `Prop`. -/
theorem k_expected_of_refines {pers rst lst fuel ty_types listed cts o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.k_expected_of pers rst.store fuel ty_types listed cts
      = ok o) :
    SimLR (Option.map id) lst o
      (match absEIdxL ty_types, listed.val.map absNIdxL, absIndCtorRecs cts with
       | [ty], [[_]], [c] => do
         let r ← piResult (absU fuel) ty
         match ← view r with
         | .sort s =>
           pure (some (c.numFields == 0 &&
             ConLeche.Level.isEquiv (← readLevel s) .zero == some true))
         | _ => pure none
       | _, _, _ => pure (some false)) := by sorry

/-- **`check_rec_indices`** — `numIndices` of `T.rec` is what is left of `T`'s
own telescope once the parameters are peeled. -/
theorem check_rec_indices_refines
    {pers rst lst fuel rn t_pre num_indices ty_names ty_types n_pd o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.check_rec_indices pers rst.store fuel rn t_pre
      num_indices ty_names ty_types n_pd = ok o) :
    SimLR (fun _ => ()) lst o
      ((absNIdxL ty_names).zip (absEIdxL ty_types) |>.forM fun tt => do
        if tt.1 == absNIdx t_pre then
          match ← piSortTeleLen? (absU fuel) tt.2 with
          | some n =>
            if absU n_pd + absU num_indices != n then fail (.internal "indices")
            else pure ()
          | none => pure ()
        else pure ()) := by sorry

/-- **`check_one_rec`** — the four count checks and the K flag at one recursor
record. -/
theorem check_one_rec_refines
    {pers rst lst rsd lsd fuel r ty_names ty_types n_pd n_types n_ctors k_exp o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd)
    (h : frontend.export_c.check_one_rec pers rst.store fuel rsd r ty_names
      ty_types n_pd n_types n_ctors k_exp = ok o) :
    ∀ u, o = .Ok u → True := by sorry

/-- **`check_rec_records`** — the `for r in (if nested then [] else rcs)`
loop. -/
theorem check_rec_records_refines
    {pers rst lst rsd lsd fuel rcs ty_names ty_types n_pd n_types n_ctors k_exp o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd)
    (h : frontend.export_c.check_rec_records pers rst.store fuel rsd rcs ty_names
      ty_types n_pd n_types n_ctors k_exp = ok o) :
    ∀ u, o = .Ok u → True := by sorry

/-- **`validate_ind_d` refines `validateIndD`** (`ExportC.lean:442-539`) — the
load-bearing statement of this file: the eleven verdicts, at the same kind and
in the same order.

A READER on both sides: the port takes the store by shared reference and
returns no state, and every twin call it makes (`st.name`, `getDeclD`,
`storeFuel`, `view`, `viewN`, `readName`, `readLevel`, `indPiTeleLen`,
`piResult`, `piSortTeleLen?`) reads.  So the two answering arms end at the
state they started in — task #97-P5-Front round 2 strengthened them from
`∃ lst'`, which left `process_line_core_d`'s `ind` arm no `AStateRel` for
`install_ind_d` and no `Ext` for its verdict. -/
theorem validate_ind_d_refines {pers rst lst rsd lsd tys cts rcs o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.validate_ind_d pers rst.store rsd tys cts rcs = ok o) :
    (∀ v, o = .Ok v →
      (validateIndD lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
          (absIndRecRecs rcs)).run lst
        = .ok (.inr (absIndCtorRecs v.1, absU v.2), lst)) ∧
    (∀ e, o = .Err e →
      (∀ ce, e = .Err ce → AErrSim ce
        ((validateIndD lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
          (absIndRecRecs rcs)).run lst)) ∧
      (∀ vd, e = .Verdict vd → ∃ lv,
        (validateIndD lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
          (absIndRecRecs rcs)).run lst = .ok (.inl lv, lst) ∧
        lVerdictKind lv = absVerdictKind vd)) := by sorry

/-! ## The block's constants -/

/-- **`ind_block_types`** — the twin's `tys.mapM` into `IConstantInfo.indInfo`. -/
theorem ind_block_types_refines {rsd lsd lst tys out o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_types rsd tys out = ok o) :
    SimLR absICIL lst o
      (do
        let ts ← (absIndTypeRecs tys).mapM fun t => do
          pure (IConstantInfo.indInfo (← parseCVD lsd t.cv) {})
        pure (absICIL out ++ ts)) := by sorry

/-- **`ind_block_ctors`** — the twin's `cts.mapM` into
`IConstantInfo.ctorInfo`. -/
theorem ind_block_ctors_refines {rsd lsd lst cts out o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_ctors rsd cts out = ok o) :
    SimLR absICIL lst o
      (do
        let cs ← (absIndCtorRecs cts).mapM fun c => do
          pure (IConstantInfo.ctorInfo (← parseCVD lsd c.cv) c.numParams c.numFields)
        pure (absICIL out ++ cs)) := by sorry

/-- **`ind_block_recs`** — the twin's `rcs.mapM` into `IConstantInfo.recInfo`. -/
theorem ind_block_recs_refines {rsd lsd lst rcs out o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_recs rsd rcs out = ok o) :
    SimLR absICIL lst o
      (do
        let rs ← (absIndRecRecs rcs).mapM fun r => do
          let rules ← r.rules.mapM (parseRuleD lsd)
          pure (IConstantInfo.recInfo (← parseCVD lsd r.cv)
            (r.numParams + r.numMotives + r.numMinors + r.numIndices)
            (r.numParams + r.numMotives + r.numMinors) rules)
        pure (absICIL out ++ rs)) := by sorry

/-- **`ind_block_of`** — the twin's `types ++ ctors ++ recs`. -/
theorem ind_block_of_refines {rsd lsd lst tys cts rcs o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_of rsd tys cts rcs = ok o) :
    SimLR absICIL lst o
      (do
        let ts ← (absIndTypeRecs tys).mapM fun t => do
          pure (IConstantInfo.indInfo (← parseCVD lsd t.cv) {})
        let cs ← (absIndCtorRecs cts).mapM fun c => do
          pure (IConstantInfo.ctorInfo (← parseCVD lsd c.cv) c.numParams c.numFields)
        let rs ← (absIndRecRecs rcs).mapM fun r => do
          let rules ← r.rules.mapM (parseRuleD lsd)
          pure (IConstantInfo.recInfo (← parseCVD lsd r.cv)
            (r.numParams + r.numMotives + r.numMinors + r.numIndices)
            (r.numParams + r.numMotives + r.numMinors) rules)
        pure (ts ++ cs ++ rs)) := by sorry

/-- **`note_ind_blocks`** — the twin's `b.types.foldl` into `indBlocks`.  The
port copies the block per member type name where con-leche shares one value
(§8.5 has no `ron::ptr`); a block is shape data and the copy is on the parse
path only. -/
theorem note_ind_blocks_refines {rsd lsd b rsd'} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd)
    (h : frontend.export_c.note_ind_blocks rsd b = ok rsd') :
    StateDRel rsd'
      { lsd with indBlocks := (absBlockRec b).types.foldl
                   (fun m t => m.insert t.cv.name (absBlockRec b)) lsd.indBlocks } ∧
      StateDInv rsd' := by sorry

/-! ## The install and the modeller seam -/

/-- **`quot_kind_of`** — the quotient record's `kind` spelling, against the
twin's four-way `match`.  Needs `StrWF`: `absString` sends an invalid code
point to `'\0'`, so without it the port's `text::cps_beq` against `"type"` can
disagree with the twin's `String` match IN THE REJECTING DIRECTION (task #87
§8's `DeclRecStrWF` finding). -/
theorem quot_kind_of_refines {k o} (hs : ConRon.Refine.StrWF k)
    (h : frontend.export_c.quot_kind_of k = ok o) :
    o.map ConRon.Refine.absQuotKind =
      (match ConRon.Refine.absString k with
       | "type" => some ConLeche.QuotKind.type
       | "ctor" => some ConLeche.QuotKind.ctor
       | "lift" => some ConLeche.QuotKind.lift
       | "ind" => some ConLeche.QuotKind.ind
       | _ => none) := by
  rw [frontend.export_c.quot_kind_of] at h
  simp only [lift, bind_tc_ok] at h
  have tst : ∀ {n : Std.Usize} (K : Std.Array Std.U32 n) (L : List Std.U32) (w : String),
      K.to_slice.val = L → (∀ c ∈ L, Nat.isValidChar c.val) →
      String.ofList (L.map fun c => Char.ofNat c.val) = w →
      ∀ b, frontend.text.cps_beq k K.to_slice = ok b →
        (b = true ↔ ConRon.Refine.absString k = w) := by
    intro n K L w hK hL hw b hb
    rw [cps_beq_str hs (by rw [hK]; exact hL) hb, hK, hw]
  have eT := tst frontend.export_c.quot_kind_of.K_TYPE [116#u32, 121#u32, 112#u32, 101#u32]
    "type" (by unfold frontend.export_c.quot_kind_of.K_TYPE; rfl) (by decide) rfl
  have eC := tst frontend.export_c.quot_kind_of.K_CTOR [99#u32, 116#u32, 111#u32, 114#u32]
    "ctor" (by unfold frontend.export_c.quot_kind_of.K_CTOR; rfl) (by decide) rfl
  have eL := tst frontend.export_c.quot_kind_of.K_LIFT [108#u32, 105#u32, 102#u32, 116#u32]
    "lift" (by unfold frontend.export_c.quot_kind_of.K_LIFT; rfl) (by decide) rfl
  have eI := tst frontend.export_c.quot_kind_of.K_IND [105#u32, 110#u32, 100#u32]
    "ind" (by unfold frontend.export_c.quot_kind_of.K_IND; rfl) (by decide) rfl
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hT := eT _ hb
  split at h
  · rename_i hb1
    cases Result.ok_injective h
    rw [hT.mp hb1]; rfl
  · rename_i hb1
    have nT : ConRon.Refine.absString k ≠ "type" := fun e => hb1 (hT.mpr e)
    obtain ⟨b1, hb1', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hC := eC _ hb1'
    split at h
    · rename_i hc
      cases Result.ok_injective h
      rw [hC.mp hc]; rfl
    · rename_i hc
      have nC : ConRon.Refine.absString k ≠ "ctor" := fun e => hc (hC.mpr e)
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hL := eL _ hb2
      split at h
      · rename_i hl
        cases Result.ok_injective h
        rw [hL.mp hl]; rfl
      · rename_i hl
        have nL : ConRon.Refine.absString k ≠ "lift" := fun e => hl (hL.mpr e)
        obtain ⟨b3, hb3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hI := eI _ hb3
        split at h
        · rename_i hi
          cases Result.ok_injective h
          rw [hI.mp hi]; rfl
        · rename_i hi
          have nI : ConRon.Refine.absString k ≠ "ind" := fun e => hi (hI.mpr e)
          cases Result.ok_injective h
          split <;> simp_all

/-- **`install_gen`** — the modeller arm of `installIndD`, split for the
loop-exit reason.  It is where `ModellerRefines` is consumed: the port's
`m.generate` against the twin's `md.generate`, at `state_model_ctx`'s
context. -/
theorem install_gen_refines {G : Type} {inst : frontend.types.Modeller G} {m : G}
    {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd block n_pd t0 b o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.install_gen inst pers m rst rsd block n_pd t0 b = ok o) :
    SimDV pers lst o
      (installGen lmd lsd (absICIL block) (absU n_pd) (absNIdx t0)
        (absBlockRec b)) := by sorry

/-- **`install_ind_d` refines `installIndD`** (`ExportC.lean:549-594`) — every
change to the state a validated inductive record makes. -/
theorem install_ind_d_refines {G : Type} {inst : frontend.types.Modeller G} {m : G}
    {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd tys cts rcs n_pd o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.install_ind_d inst pers m rst rsd tys cts rcs n_pd
      = ok o) :
    SimDV pers lst o
      (installIndD lmd lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
        (absIndRecRecs rcs) (absU n_pd)) := by sorry

end ConRon.Refine2.Frontend
