/-
# `ConRon.Bridge.Frontend.Modeller` — the seam's two promises

DESIGN §8.2 puts the in-process modeller OUTSIDE the verified surface, and
`Arena/Frontend/Types.lean`'s `Modeller` is the one-method seam that says so:

    structure Modeller where
      generate : Ctx → BlockRec → AM (Except String (List IDeclaration))

The original campaign carried exactly two hypotheses about it into
`conron.no_False_declaration` (`proof/ConRon/RefineOld/Main.lean:730-735`):

* `hgen : Frontend.ModellerWF inst g` (`RefineOld/Frontend/Base.lean:154`) —
  *whatever it returns is well formed*;
* `hmr : Frontend.ModellerRefines inst g Frontend.CtxRel`
  (`RefineOld/Frontend/ChunksR.lean:143`) — *when it returns, it returns
  con-leche's own records; when it declines, con-leche declines too*.

This module is those two, transposed from "Rust model vs con-leche" to "twin
vs con-leche".  What changes is only what "well formed" and "is con-leche's"
mean over handles:

| original | here |
|---|---|
| `DeclarationWF d` (the port's own record predicate) | `PersDecl d` **and** the record DENOTES (`Bridge/Checker/Inv.lean`'s `denoteDecls`) |
| `ds.val.map absDeclaration` | `denoteDecls st' hs` |
| `absBlockRec b` | `BlockRecRel st b bP` (`Bridge/Frontend/Rel.lean`) |
| `CtxRel ctx lctx` | `CtxRel st ctx lctx` (the store is a parameter) |

and one thing is ADDED that the original did not need: the seam runs in `AM`,
so it moves the store, and the promise has to say what it does to it —
`StateOK`, `Ext` and the frame (`caches`, `pins`, `scratchOn`).  That is the
shape every `@[spec]` theorem of `Bridge/Specs.lean` has, and it is what lets
a caller compose the seam with the rest of the line's work.

## The one instantiation, and why it is not a hypothesis forever

`Arena/Frontend/InModel.lean`'s `inProcessModeller` **delegates to con-leche's
own generator**: it reads the block back (`denoteBlockRec`), calls
`ConLeche.Frontend.InModel.generate` verbatim, and interns the result
(`internDecls`).  So `ModellerRefines` for it is not a promise about a foreign
program at all — it is the readback/intern exactness of
`Arena/Frontend/Readback.lean`, and `inProcessModeller_refines` below states
it as a theorem rather than an axiom.  `Bridge/Frontend/Capstone.lean` still
takes the two as HYPOTHESES, because the capstone is stated at an arbitrary
`Modeller` (`runPipeline` fixes one, and the assembled letters do not) and
because that is the discipline the original campaign fixed: *a statement about
an unverified argument is a hypothesis of the statement, never an axiom of the
environment*.
-/
import ConRon.Bridge.Frontend.Shared
import ConRon.Arena.Frontend.InModel

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The two promises -/

/-- con-leche: none
`RefineOld/Frontend/Base.lean:154 ModellerWF` — **the seam's first promise**:
every declaration the modeller returns is one the rest of the pipeline can
read — it DENOTES in the store the call leaves behind, and its handles are
PERSISTENT (the parse runs with the scratch tier closed, so a generated record
that were not would vanish at the fold's first `dropScratch`).

This is the clause that discharges the fold theorems' `hpd` for the
generated half of the stream; the parsed half gets it from the parse.

**`StateOK s` and the closed scratch tier are hypotheses of the promise**
(task #97-P3-Frontend round 3's finding 14).  Round 1 wrote the promise
without them, the way the original campaign's `ModellerWF`
(`RefineOld/Frontend/Base.lean:154`) is written — but the original's seam is
PURE and this one runs in `AM`, so its conclusion talks about the store the
call leaves behind.  With no hypothesis about the store it was handed, `StateOK
s'` is simply false: at a `Modeller` that returns `[]` the run leaves the state
alone, so the promise would say `StateOK s` of every state.  Both hypotheses
hold at every call site (`installIndD_run` is the only consumer and it takes
them), and a promise about an UNVERIFIED modeller is a promise about what it
does to a well-formed store — not a promise that it repairs a broken one.

**The `DeclProjNamed` clause is round 5's repair of round 4's finding 16**
(`Bridge/Frontend/Rel.lean`'s module note for the vocabulary).  A record that
merely DENOTES does not have `IDeclaration.names`'s exactness, because
`denoteProjTable` drops the stored `tableName`; the parse's own records get
the clause for free (a parsed `.indDecl` block is built out of `.indInfo`,
`.ctorInfo` and `.recInfo`) and `StateDRel.projNamed` carries it through the
fold, but a record the MODELLER generated enters the stream through
`pushGenList` and nothing upstream constrained it.  So the promise says it, at
one place, instead of eight consumers taking it as a side condition.

**What is asked is the `named` half of `IProjTableOK` and not the whole of
it.**  That is what the name equation needs, and it is what the one concrete
modeller can give: `inProcessModeller` interns the table
(`internProjTable`, `Arena/Frontend/Readback.lean:583-590`), and interning it
interns the reserved name `projTableName sn` itself, so the clause is true of
its answer by construction.  `IProjTableOK`'s two SIZE clauses would not be —
they would have to be imported from con-leche's own `ProjTable`, which nothing
states — and they are not what any consumer here reads.

**The second conjunct is the DECLINE's frame** (task #97-P3-Frontend round 7).
The first says nothing about a run that answers `.error`, and `installIndD`
carries on after one (the census books the decline, or the record is declined
with a verdict) — so without it `installIndD_run`'s `ParseStep` is false at a
modeller that moves the state and then declines.  Both instantiations decline
with a `pure`, so it costs them one line. -/
def ModellerWF (md : Modeller) : Prop :=
  (∀ ctx b s hs s', StateOK s → s.store.scratchOn = false →
    md.generate ctx b s = .ok (.ok hs, s') →
    StateOK s' ∧ Ext s.store s'.store ∧
      (∀ d ∈ hs, PersDecl d) ∧ (∀ d ∈ hs, DeclProjNamed s'.store d) ∧
      (denoteDecls s'.store hs).isSome = true ∧
      s'.memos = s.memos ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      s'.store.scratchOn = s.store.scratchOn) ∧
  (∀ ctx b s m s', StateOK s → s.store.scratchOn = false →
    md.generate ctx b s = .ok (.error m, s') →
    StateOK s' ∧ Ext s.store s'.store ∧
      s'.memos = s.memos ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      s'.store.scratchOn = s.store.scratchOn)

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
`RefineOld/Frontend/ChunksR.lean:143 ModellerRefines` — **the seam's second
promise**: at a context and a block that denote con-leche's, the modeller's
answer is con-leche's answer.  Both signs, as the original: what it RETURNS is
what con-leche's generator returns (up to the denotation), and where it
DECLINES con-leche declines too.

The decline half is what makes the parse's exactness an `iff` at the record
level without a second induction: `installIndD`'s `.declined` verdict is
con-leche's `.declined` verdict, so a stream the twin declines is a stream
con-leche declines, and the capstone's contrapositive ("the twin never
accepts") does not have to reason about coverage at all.

`StateOK s` and the closed scratch tier are hypotheses here for the same
reason as above (finding 14): the answer's DENOTATION is a fact about the
store, and `denoteDecls` at a store that is not well formed relates nothing to
anything.

**The decline half names con-leche's REASON, not just a decline** (task
#97-P3-Frontend round 7).  `installIndD`'s census branch books the reason
(`inModelDeclined.push (T0, why)`), and `StateDRel.inModelDeclined` relates
the two booked strings by EQUALITY — so with only "con-leche declines too"
the census arm of `installIndD_run` is false at a modeller whose reason
differs from con-leche's.  The concrete modeller returns con-leche's own
reason (it calls con-leche's generator), so `inProcessModeller_refines` keeps
the stronger promise at no cost. -/
def ModellerRefines (md : Modeller) : Prop :=
  ∀ ctx ctxP b bP s o s', StateOK s → s.store.scratchOn = false →
    CtxRel s.store ctx ctxP → BlockRecRel s.store b bP →
    md.generate ctx b s = .ok (o, s') →
    (∀ hs, o = .ok hs → ∀ dsP, denoteDecls s'.store hs = some dsP →
        ConLeche.Frontend.InModel.generate ctxP bP = .ok dsP) ∧
      (∀ m, o = .error m → ConLeche.Frontend.InModel.generate ctxP bP = .error m)

/-! ## The instantiation the driver runs

`inProcessModeller` cannot disagree with con-leche — it *calls* con-leche —
so both promises are theorems about the readback and the intern rather than
assumptions about a foreign program.  They are stated here and proved where
`Arena/Frontend/Readback.lean`'s exactness is
(`Bridge/Frontend/Shared.lean`). -/

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate — **the delegating
modeller keeps the first promise.**

`Arena/Frontend/Readback.lean`'s intern exactness (`internDecls_istep`,
`Bridge/Frontend/Shared.lean`) gives the denotation, the persistence AND — since
round 5 — the projection-table naming of the generated records in one; the
frame conjuncts are `internE`'s, which never writes `caches`, `pins` or the
scratch flag.

The naming clause is `internProjTable_istep`'s own new conjunct, carried up
through `internCI_istep`, `internCIList_istep` and `internDecl_istep`: the
twin BUILDS the reserved name (`projTableName sn`) where con-leche recomputes
it, so the two agree by construction and the seam's promise costs this
instantiation nothing. -/
theorem inProcessModeller_wf : ModellerWF inProcessModeller := by
  refine ⟨?_, ?_⟩
  rotate_left
  · intro ctx b s m s' hok hoff hrun
    simp only [inProcessModeller] at hrun
    obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
    obtain ⟨ht, hs₁⟩ := AM.get_ok hget
    rw [ht, hs₁] at hrest
    cases hb : denoteBlockRec s.store b with
    | none =>
      rw [hb] at hrest
      obtain ⟨-, rfl⟩ := AM.pure_ok hrest
      exact ⟨hok, Ext.refl _, rfl, rfl, rfl, rfl⟩
    | some bP =>
    rw [hb] at hrest
    simp only [] at hrest
    cases hg : ConLeche.Frontend.InModel.generate (ctxOf s.store ctx) bP with
    | error why =>
      rw [hg] at hrest
      obtain ⟨-, rfl⟩ := AM.pure_ok hrest
      exact ⟨hok, Ext.refl _, rfl, rfl, rfl, rfl⟩
    | ok ds =>
    rw [hg] at hrest
    simp only [] at hrest
    obtain ⟨p, s₂, hint, hrest2⟩ := AM.bind_ok hrest
    exact absurd (AM.pure_ok hrest2).1 (by simp)
  intro ctx b s hs s' hok hoff hrun
  simp only [inProcessModeller] at hrun
  obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
  obtain ⟨ht, hs₁⟩ := AM.get_ok hget
  rw [ht, hs₁] at hrest
  cases hb : denoteBlockRec s.store b with
  | none => rw [hb] at hrest; exact absurd (AM.pure_ok hrest).1 (by simp)
  | some bP =>
  rw [hb] at hrest
  simp only [] at hrest
  cases hg : ConLeche.Frontend.InModel.generate (ctxOf s.store ctx) bP with
  | error why =>
    rw [hg] at hrest
    exact absurd (AM.pure_ok hrest).1 (by simp)
  | ok ds =>
  rw [hg] at hrest
  simp only [] at hrest
  obtain ⟨p, s₂, hint, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨m2, hsx⟩ := p
  simp only [] at hrest2
  obtain ⟨hstep, hpers, hden, -, hnamed⟩ :=
    internDecls_istep ds hok hoff (EMemoOK.empty s.store) hint
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
  subst hst
  simp only [Except.ok.injEq] at hv
  subst hv
  exact ⟨hstep.ok, hstep.ext, hpers, hnamed, by rw [hden]; rfl, hstep.memos,
    hstep.caches, hstep.pins, by rw [hstep.off, hoff]⟩

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate — **the delegating
modeller keeps the second promise**, and this is the one theorem of the tier
that is about a seam rather than about a function: `inProcessModeller` runs
`ConLeche.Frontend.InModel.generate (ctxOf s.store ctx) bP`, so what has to be
shown is that `ctxOf s.store ctx` IS `ctxP` and `denoteBlockRec s.store b` IS
`bP` — the readback is the denotation, which is
`Bridge/Frontend/Shared.lean`'s `denoteEShared_eq` lifted to the block and the
context.

`ctxOf_eq_of_rel` and `denoteBlockRec_eq_of_rel`
(`Bridge/Frontend/Shared.lean`), then `internDecls_istep` for the returned
records.  The context equality is the only part with content: `ctxOf` probes
the name store (`nameHandle?`) where `CtxRel` quantifies over handles that
denote, and the two agree because `denoteN` is injective (DESIGN §8.3's
exactness obligation, `Arena/Denote.lean`'s `denoteN_inj`) — plus round 2's
finding 12, the three COVER clauses, for the names the store never interned. -/
theorem inProcessModeller_refines : ModellerRefines inProcessModeller := by
  intro ctx ctxP b bP s o s' hok hoff hc hbr hrun
  simp only [inProcessModeller] at hrun
  obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
  obtain ⟨ht, hs₁⟩ := AM.get_ok hget
  rw [ht, hs₁] at hrest
  have hb : denoteBlockRec s.store b = some bP := denoteBlockRec_eq_of_rel hok.wf hbr
  have hctx : ctxOf s.store ctx = ctxP := ctxOf_eq_of_rel hok.wf hc
  rw [hb] at hrest
  simp only [] at hrest
  cases hg : ConLeche.Frontend.InModel.generate (ctxOf s.store ctx) bP with
  | error why =>
    rw [hg] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst; subst hv
    refine ⟨fun hs h => absurd h (by simp), fun m hm => ?_⟩
    injection hm with hm
    subst hm
    rw [← hctx]; exact hg
  | ok ds =>
  rw [hg] at hrest
  simp only [] at hrest
  obtain ⟨p, s₂, hint, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨m2, hsx⟩ := p
  simp only [] at hrest2
  obtain ⟨hstep, hpers, hden, -⟩ :=
    internDecls_istep ds hok hoff (EMemoOK.empty s.store) hint
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
  subst hst; subst hv
  refine ⟨?_, fun m hm => absurd hm (by simp)⟩
  intro hs h dsP hd
  simp only [Except.ok.injEq] at h
  subst h
  rw [hden] at hd
  simp only [Option.some.injEq] at hd
  subst hd
  rw [← hctx]; exact hg

/-- con-leche: none — the modeller that declines everything keeps the second
promise only where con-leche declines too, so it is NOT a `ModellerRefines`
and the fact is worth recording: `declineModeller` is the seam's trivial
instantiation for a run with modelling switched off, and a proof about it
would be a proof about a different pipeline.  What it does keep is the first
promise, vacuously — it never returns records. -/
theorem declineModeller_wf : ModellerWF declineModeller := by
  refine ⟨?_, ?_⟩
  · intro ctx b s hs s' _ _ h
    injection h with h1
    injection h1 with h2 _
    exact nomatch h2
  · intro ctx b s m s' hok _ h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨hok, Ext.refl _, rfl, rfl, rfl, rfl⟩

end ConRon.Bridge.Frontend
