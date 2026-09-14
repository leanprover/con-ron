/-
`ConRon.Refine.Frontend.IndSpecR` — **the inductive tier's ingredient records,
discharged** (task #87, phase 3).

This file proves nothing new about the port.  It is the *seam*: the three
named `Prop`s the inductive tier is stated modulo — `StateDR.ProjRecSpec`,
`IndInstallR.InstallSpec` and `IndR.IndRSpec` — built from the lemmas of
`Refine/Frontend/ProjRecR.lean`, `Refine/Frontend/IndValidateR.lean` and
`Refine/Frontend/IndInstallR.lean`, and the parse tier's headline restated at
the result.  Each record is one `⟨…⟩`; the whole point is that the elaborator,
not a reader, checks that the shapes line up.

## Why the records exist at all

`Refine/Frontend/StateDR.lean` is the parser's *base* file and
`Refine/Frontend/ProjRecR.lean` sits at the top of the inductive tier (2 179
build jobs).  Importing the second into the first would put the base above the
heaviest tier in the graph for five facts, so the five became `ProjRecSpec`,
a named `Prop` to be discharged where the two tiers finally meet.  That place
is this file.  `InstallSpec` and `IndRSpec` are the same decision one and two
levels up.

## What is proved

* `projRecSpec : ProjRecSpec` — five lemmas of `ProjRecR.lean`, one
  application each (they were stated in `ProjRecSpec`'s binder order on
  purpose).
* `installSpec : InstallSpec` — `StateDR.lean`'s `note_proj_iota_refines` at
  `projRecSpec`, and `ProjRecR.lean`'s `proj_rec_owners_refines` paired with
  phase 1's `proj_rec_owners_wf`.
* `indRSpec … : IndRSpec inst g` — `StateDR.lean`'s `proj_rewrite_d_refines`
  at `projRecSpec`, `IndValidateR.lean`'s `validate_ind_d_refines`, and
  `IndInstallR.lean`'s `indRSpec_installInd` at `installSpec`.  All three
  clauses are *proved*: what is left in front of it is the modeller and
  nothing else.
* `parse_chunks_refines_of_modeller` and its two twins — `ChunksR.lean`'s
  three corollaries with `IndRSpec` discharged, so the parse's residue is
  `Utf8DecodeSpec`, `UnescapeSpec` and the modeller's own two promises.

## The residue that survives

At the modeller, and nowhere else in the inductive tier:
`Refine/Frontend/Base.lean`'s `ModellerWF` and `Refine/Frontend/ChunksR.lean`'s
`ModellerRefines inst g CtxRel` — the two promises about the *unverified*
in-process modeller (DESIGN.md §3's ruling of 2026-09-13), which are function
arguments and disappear the day upstream drops the modeller.

That is the whole list.  `IndRSpec` briefly carried a third,
`ValidateIndRefines`, while `Refine/Frontend/IndValidateR.lean`'s
`validate_ind_d_refines` was being written; the lemma landed and the
hypothesis is gone.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.ProjRecR
import ConRon.Refine.Frontend.IndValidateR
import ConRon.Refine.Frontend.IndInstallR
import ConRon.Refine.Frontend.ChunksR

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## `ProjRecSpec` — the state layer's five borrowed facts

`Refine/Frontend/StateDR.lean:2717-2737`.  Every field is a theorem of
`Refine/Frontend/ProjRecR.lean` stated in exactly this binder order, so the
record is five names. -/

/-- **`StateDR.lean`'s `ProjRecSpec`, discharged** — `frontend::proj_rec`'s
five readers, against `ConLeche/Frontend/ProjRec.lean`. -/
theorem projRecSpec : ProjRecSpec where
  lamBody := lam_body_refines
  isProjIotaName := is_proj_iota_name_refines
  projIotaLevel := proj_iota_level_refines
  projIotaName := proj_iota_name_refines
  projRecValue o l ty val i res ho hl hty hval h :=
    proj_rec_value_refines o l ty val i res ho hl hty hval h

/-! ## `InstallSpec` — the install path's two borrowed lemmas

`Refine/Frontend/IndInstallR.lean:292-316`.  The first is the state layer's
own `note_proj_iota_refines`, which is itself stated modulo `ProjRecSpec` —
so `projRecSpec` above is what unblocks it.  The second is the owner census,
`ProjRecR.lean`'s abstraction lemma paired with phase 1's well-formedness one.

`absProjOwner` (`StateDR.lean`) and `absProjRecOwner` (`ProjRecR.lean`) are
the same structure literal, and likewise `absPTypeRec`/`absProjTypeRec` and
their two neighbours: the duplication is the same import decision, and the two
sides meet here by `rfl`. -/

/-- `Refine/Frontend/StateDR.lean`'s `absProjOwner` **is**
`Refine/Frontend/ProjRecR.lean`'s `absProjRecOwner` — the note on either
definition, checked. -/
theorem absProjOwner_eq : absProjOwner = absProjRecOwner := rfl

/-- **`IndInstallR.lean`'s `InstallSpec`, discharged.** -/
theorem installSpec : InstallSpec where
  noteProjIota hrel hwf hcv h := note_proj_iota_refines projRecSpec hrel hwf hcv h
  projRecOwners hb ht hc hr h :=
    ⟨proj_rec_owners_refines hb ht hc hr h, proj_rec_owners_wf hb ht hc hr h⟩

/-! ## `IndRSpec` — the line layer's three clauses

`Refine/Frontend/IndR.lean:1294-1331`.  The first is the projection rewrite
(the state layer's, at `projRecSpec`), the second the validation, the third
the install — and the third is the one that carries the modeller, so the two
promises about it are this theorem's hypotheses and the parse's whole residue
beyond the string tier. -/

/-- **`IndR.lean`'s `IndRSpec`, discharged** at a modeller that is well formed
(`Refine/Frontend/Base.lean`'s `ModellerWF`) and exact
(`Refine/Frontend/ChunksR.lean`'s `ModellerRefines` at
`Refine/Frontend/StateDR.lean`'s `CtxRel`, the context bridge
`export_c::state_model_ctx` builds). -/
theorem indRSpec {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hmw : ModellerWF inst g) (hmr : ModellerRefines inst g CtxRel) :
    IndRSpec inst g where
  projRewrite hrel hwf hcv hvl h := proj_rewrite_d_refines projRecSpec hrel hwf hcv hvl h
  validateInd hrel hwf h := validate_ind_d_refines hrel hwf h
  installInd hrel hwf h := indRSpec_installInd hmw hmr installSpec hrel hwf h

/-! ## The parse tier, at the discharged record

`Refine/Frontend/ChunksR.lean`'s three corollaries with `IndRSpec` replaced by
what proves it.  What stands in front of the port's streaming parse after
this is `Utf8DecodeSpec`, `UnescapeSpec` and the two modeller promises — and
nothing else. -/

/-- **`export_c::parse_chunks` refines `ConLeche.Frontend.parseChunks`**
(`ConLeche/Frontend/ExportC.lean:882-901`), accept direction, with the
inductive tier discharged. -/
theorem parse_chunks_refines_of_modeller {G : Type}
    {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hu : Utf8DecodeSpec) (hun : UnescapeSpec) (hmw : ModellerWF inst g)
    (hmr : ModellerRefines inst g CtxRel)
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {im ce : Bool}
    {r : frontend.export_c.ParseResultD}
    (h : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Ok r)) :
    ∃ x, ConLeche.Frontend.parseChunks (absChunks chunks) im ce = .ok x ∧
      ParseResultSim r x :=
  parse_chunks_refines_of_specs hu hun (indRSpec hmw hmr) h

/-- **`export_c::parse_chunks`, error direction**, with the inductive tier
discharged. -/
theorem parse_chunks_refines_err_of_modeller {G : Type}
    {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hu : Utf8DecodeSpec) (hun : UnescapeSpec) (hmw : ModellerWF inst g)
    (hmr : ModellerRefines inst g CtxRel)
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {im ce : Bool}
    {p : kernel.core_types.CheckError × Std.U64}
    (h : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Err p)) :
    ParseErrSim p (ConLeche.Frontend.parseChunks (absChunks chunks) im ce) :=
  parse_chunks_refines_err_of_specs hu hun (indRSpec hmw hmr) h

/-- **`prelude::builtin_prelude_e` refines con-leche's prelude parse**, with
the inductive tier discharged. -/
theorem builtin_prelude_e_refines_of_modeller {G : Type}
    {inst : frontend.in_model_rec.Modeller G} {m : G}
    (hu : Utf8DecodeSpec) (hun : UnescapeSpec) (hmw : ModellerWF inst m)
    (hmr : ModellerRefines inst m CtxRel)
    {pre : frontend.prepare.PreludeIx}
    (h : frontend.prelude.builtin_prelude_e inst m = ok (.Ok pre)) :
    ∃ text x, frontend.prelude_text.prelude_text = ok text ∧
      ConLeche.Frontend.parseBytes (absChunk text) true false = .ok x ∧
      pre.decls.val.map absDeclaration = x.decls.toList :=
  builtin_prelude_e_refines_of_specs hu hun (indRSpec hmw hmr) h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Every record and every corollary: Lean's own three axioms and nothing else.
The residues are hypotheses of the statements, not axioms — that is the whole
difference between this file and a `sorry`. -/

/-- info: 'ConRon.Refine.Frontend.projRecSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms projRecSpec

/-- info: 'ConRon.Refine.Frontend.installSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms installSpec

/-- info: 'ConRon.Refine.Frontend.indRSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms indRSpec

/-- info: 'ConRon.Refine.Frontend.parse_chunks_refines_of_modeller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_chunks_refines_of_modeller

/-- info: 'ConRon.Refine.Frontend.parse_chunks_refines_err_of_modeller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_chunks_refines_err_of_modeller

/--
info: 'ConRon.Refine.Frontend.builtin_prelude_e_refines_of_modeller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms builtin_prelude_e_refines_of_modeller

end ConRon.Refine.Frontend
