/-
# `ConRon.Bridge.Frontend.Chunks` — **the parser's exactness**

DESIGN §8.2's parser tier, in full:

    denoteDecls (Arena.parse chunks) = parseChunks chunks

Five theorems get there, in the order `Arena/Frontend/ExportC.lean` defines
the functions: `applyFinalLine`, `feedChunk`, `chunkStep`, `chunkFinish`,
`parseChunks` — with `parseBytes` beside them, because the prelude is parsed
by `parseBytes` and not by `parseChunks`.

## What is NOT here, and why that is the point

**The scanner.**  `Arena/Frontend/ExportC.lean` imports
`ConLeche.Frontend.Scan.Fast` and calls `scanLineFwd` — con-leche's own
function on con-leche's own `ByteArray`, returning con-leche's own `LineRec`.
There is no twin, so there is nothing to relate: where the original campaign
needed seven files and 17 479 lines (`RefineOld/Frontend/Scan{WF,Kit,Str,Obj,
Expr,Ind,Line}.lean`, plus `Utf8DecodeSpec` and `UnescapeSpec` as named
obligations), this tier needs **zero**.  That is the single largest saving of
the arena rewrite's proof, and it is a consequence of (B) being Lean: a Lean
twin may CALL con-leche where a Rust port must re-implement.

**The chunks.**  `Arena.Frontend.parseChunks` takes `List ByteArray` and so
does con-leche's, byte for byte — so there is no `absChunks`
(`RefineOld/Frontend/Abs.lean:438`) either, and the capstone's hypothesis is
literally `ConLeche.jsonWithTheoremFalse chunks`.  The second saving, and the
reason the byte-level capstone is a two-step composition rather than a
transport across an abstraction.

**The error channel.**  Both sides carry `Except (CheckError × Nat)` for the
two failures that are VALUES (a scan error, a record verdict), and the twin's
`CheckError` is con-leche's own type — `Arena/Frontend/Types.lean` says the
frontend's `M` collapses into `AM` and nothing else moves.  So there is no
`absErrKind`/`ParseErrSim` (`RefineOld/Frontend/ChunksR.lean:226`) either; the
theorems are one-directional (twin accepts ⇒ con-leche accepts) and a twin
failure claims nothing, which is all the capstone needs.

## The one import the tier's own module note did not foresee

con-leche's `feedChunk` and `applyFinalLine` call **`scanLineSpec`**, the
naive reference, and let `@[csimp]` substitute `scanLineFwd` in compiled code;
the twin calls `scanLineFwd` directly, because *"that is what both binaries
execute"* (`Arena/Frontend/ExportC.lean`).  So the bridge needs the equation
between them — `ConLeche.Frontend.scanLineFwd_eq`
(`Scan/Equiv.lean:932`) — and `Bridge/Frontend/Chunks.lean` imports
`ConLeche.Frontend.Scan.Equiv` for it.

**This does not reopen the scanner tier.**  The 1 800 lines behind that
equation are con-leche's, already proved and already built; what the twin
avoids is re-deriving them, not citing them.  The saving DESIGN §2 records
(seven files, 17 479 lines of `RefineOld/Frontend/Scan*`) is untouched: those
files proved a *re-implementation* right, and there is none here.

## The one escape hatch

con-leche writes `parseChunks`'s fold as a `where go`; the twin writes it as
the top-level `parseChunksGo`, because "the arena's Rust twin is a loop of its
own and a `where` clause has no name to cite"
(`Arena/Frontend/ExportC.lean`).  `parseChunksC` below is con-leche's `go`
respelled at the top level with `parseChunks_eq` as its `rfl` equation —
`RefineOld/Frontend/ChunksR.lean:673`'s `parseBytesFinal`/`parseBytes_eq`
pattern, for the same reason.
-/
import ConRon.Bridge.Frontend.Lines
import ConLeche.Frontend.Scan.Equiv

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The escape hatch -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:895-901 parseChunks.go — the
streaming fold, respelled at the top level so the twin's `parseChunksGo` has
a named original to be stated against. -/
def parseChunksC (st : ConLeche.Frontend.StateD) (carry : ByteArray)
    (lineNo total : Nat) :
    List ByteArray → Except (ConLeche.CheckError × Nat) ConLeche.Frontend.ParseResultD
  | [] => ConLeche.Frontend.chunkFinish st carry lineNo
  | c :: cs =>
    match ConLeche.Frontend.chunkStep st carry lineNo total c with
    | .error e => .error e
    | .ok (st, carry, lineNo, total) => parseChunksC st carry lineNo total cs

/-- con-leche: ConLeche/Frontend/ExportC.lean:895-901 parseChunks.go — the
respelling is the original, step for step.  A list induction whose step is
`rfl` on both sides: `where go` and a top-level `def` with the same clauses
are the same function, and only Lean's equation compiler stands between
them. -/
theorem parseChunksC_eq (st : ConLeche.Frontend.StateD) (carry : ByteArray)
    (lineNo total : Nat) (cs : List ByteArray) :
    ConLeche.Frontend.parseChunks.go st carry lineNo total cs
      = parseChunksC st carry lineNo total cs := by
  induction cs generalizing st carry lineNo total with
  | nil => rfl
  | cons c cs ih =>
    simp only [ConLeche.Frontend.parseChunks.go, parseChunksC]
    split <;> simp_all

/-- con-leche: ConLeche/Frontend/ExportC.lean:891-893 parseChunks — the entry
point at the respelling. -/
theorem parseChunks_eq (chunks : List ByteArray) (im ce : Bool) :
    ConLeche.Frontend.parseChunks chunks im ce
      = parseChunksC (.init im ce) .empty 0 0 chunks :=
  parseChunksC_eq _ _ _ _ _

/-! ## The initial state -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:757 StateD.init — **the two
tables start related**: index 0 of the name table is the handle
`Name.anonymous` interns at and index 0 of the level table the handle
`Level.zero` interns at, which is `IdTableRel.singleton` at
`Bridge/Specs.lean`'s `internNNode_spec` / `internLNode_spec`.

Two intern specs and `IdTableRel.singleton`; every other field is the
structure's default on both sides, so `MapRel` of two empty maps,
`IdTableRel` of two empty tables (`IdTableRel.empty`) and `denoteDeclArray` of
the empty array are `rfl`-level.

**The `PersStateD` half costs one observation**, not an intern lemma
(task #97-P3-Frontend-2 round 2, revising round one's finding 9.1): a scratch
handle reads as ABSENT while the scratch tier is off, so a handle the intern
spec hands back WITH A VIEW is persistent — `Bridge/Frontend/Rel.lean`'s
`PersN_of_view` / `PersL_of_view`, over the `sync` chain that carries
`scratchOn = false` down the nesting. -/
theorem StateD_init_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {im ce : Bool} {sd : StateD}
    (hrun : StateD.init im ce s = .ok (sd, s')) :
    ParseStep s s' ∧ PersStateD sd ∧
      StateDRel s'.store sd (ConLeche.Frontend.StateD.init im ce) := by
  rw [StateD.init] at hrun
  -- the anonymous name
  obtain ⟨n0, s₁, hn, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hwf1, hx1, -, -, hon1, hm1, hc1, hp1, hview1, hden1⟩ :=
    AM.of_run (P := fun t => t = s) rfl hn
      (internNNode_spec s .anonymous hok.wf (by intro c hc; simp [NNodeView.children] at hc))
  -- the zero level
  obtain ⟨l0, s₂, hl, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hwf2, hx2, -, -, hon2, hm2, hc2, hp2, hview2, hden2⟩ :=
    AM.of_run (P := fun t => t = s₁) rfl hl
      (internLNode_spec s₁ .zero hwf1
        ⟨by intro c hc; simp [LNodeView.lchildren] at hc,
         by intro c hc; simp [LNodeView.nchildren] at hc⟩)
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
  subst hv; subst hst
  -- the frame
  have hstep : ParseStep s s' :=
    ParseStep.of_caches ⟨hwf2⟩ (hx1.trans hx2) (by rw [hon2, hon1])
      (by rw [hc2, hc1]) (by rw [hp2, hp1])
  have hoff2 : s'.store.scratchOn = false := by rw [hon2, hon1]; exact hoff
  -- the two handles denote, in the FINAL store
  have hdn1 : denoteN s₁.store.ns n0 = some .anonymous := hden1
  have hdn : denoteN s'.store.ns n0 = some .anonymous := denoteN_ext hdn1 hx2
  have hdl : denoteL s'.store.ls l0 = some .zero := hden2
  -- and they are persistent: a handle with a VIEW on a closed store is
  have hpn : PersN n0 := by
    obtain ⟨v, hv'⟩ := Arena.denoteN_view hdn
    exact PersN_of_view hwf2 hoff2 hv'
  have hpl : PersL l0 := by
    obtain ⟨v, hv'⟩ := Arena.denoteL_view hdl
    exact PersL_of_view hwf2 hoff2 hv'
  refine ⟨hstep, ?_, ?_⟩
  · exact
      { names := by
          intro i h hg
          rw [ConLeche.Frontend.IdTable.get?_singleton] at hg
          split at hg
          · simp only [Option.some.injEq] at hg; exact hg ▸ hpn
          · exact absurd hg (by simp)
        levels := by
          intro i h hg
          rw [ConLeche.Frontend.IdTable.get?_singleton] at hg
          split at hg
          · simp only [Option.some.injEq] at hg; exact hg ▸ hpl
          · exact absurd hg (by simp)
        exprs := by
          intro i h hg
          rw [ConLeche.Frontend.IdTable.get?_empty] at hg
          exact absurd hg (by simp)
        decls := by intro d hd; simp at hd }
  · exact
      { names := IdTableRel.singleton hdn
        levels := IdTableRel.singleton hdl
        exprs := IdTableRel.empty _
        decls := denoteDeclArray_empty _
        projNamed := DeclsProjNamed.empty _
        projOwners := MapRel.empty _ _
        projLevels := MapRel.empty _ _
        projRewrites := rfl
        constTypes := MapRel.empty _ _
        heights := MapRel.empty _ _
        inModel := rfl
        inModelled := rfl
        genRecords := rfl
        genOwner := MapRel.empty _ _
        inModelGen := .nil
        indCount := rfl
        indBlocks := MapRel.empty _ _
        inModelCensus := rfl
        inModelDeclined := .nil }

/-! ## The line feed -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:767-768 applyFinalLine — the
stream's last line, the one no newline ends.  The scanner is con-leche's own
call on both sides, so the only step with content is `applyLine`.

A `cases` on `scanLineFwd`'s answer — the same value on both sides, once
`scanLineFwd_eq` has pointed con-leche's `scanLineSpec` at it — and
`applyLine_run` in the `.ok` arm. -/
theorem applyFinalLine_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {b : ByteArray} {i : USize} {lineNo : Nat}
    (hrun : applyFinalLine md sd b i lineNo s = .ok (.ok sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.applyFinalLine sc b i lineNo = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  rw [applyFinalLine] at hrun
  cases hsc : ConLeche.Frontend.scanLineFwd b i with
  | err e =>
    rw [hsc] at hrun
    exact absurd (AM.pure_ok hrun).1 (by simp)
  | ok r j =>
    rw [hsc] at hrun
    obtain ⟨x, s₁, hline, htail⟩ := AM.bind_ok hrun
    obtain ⟨hstep, hpers, y, hy, hxy⟩ := applyLine_run hmw hmr hok hoff hpins hrb hrel hp hline
    have hcl : ConLeche.Frontend.applyFinalLine sc b i lineNo
        = (match ConLeche.Frontend.applyLine sc r with
           | .error msg => .error (.internal msg, lineNo)
           | .ok (.inr v) => .error (v.toError, lineNo)
           | .ok (.inl st) => .ok st) := by
      rw [ConLeche.Frontend.applyFinalLine, ← ConLeche.Frontend.scanLineFwd_eq,
        hsc]
      rfl
    cases x with
    | inr v =>
      exact absurd (AM.pure_ok htail).1 (by simp)
    | inl st =>
      obtain ⟨hv, hs⟩ := AM.pure_ok htail
      have hst : sd' = st := Except.ok.inj hv
      subst hst
      subst hs
      obtain ⟨sc', hyx, hrel'⟩ := hxy.inl_left rfl
      exact ⟨hstep, hpers sd' rfl, sc', by simp [hcl, hy, hyx], hrel'⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:787-788 feedChunk — **every
complete line of a buffer, applied in order**: the state, the line count and
where the incomplete tail begins.  The three numbers are `Nat`/`USize` on both
sides and must come out EQUAL, not merely related — they are the fold's own
bookkeeping and the next chunk's input.

The loop's strong induction on `b.size - i.toNat` — the twin's own
`termination_by`, taken as a `Nat` bound so that the induction is an ordinary
one — with `applyLine_run` at the step and the two guards (`scanLineFwd`'s
verdict and `newlineFrom`) evaluated once and shared, since both sides call
con-leche's functions on the same bytes.  Task #97-P3-Frontend's sorry list,
item 16 — **the tier's second critical path**, after
`processLineCoreD_run`. -/
theorem feedChunk_run_le {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) :
    ∀ (n : Nat) {s s' : AState}, StateOK s → s.store.scratchOn = false → PinsOK s → ReadCachesOK s →
      ∀ {sd sd' : StateD} {sc : ConLeche.Frontend.StateD},
        StateDRel s.store sd sc → PersStateD sd →
      ∀ {b : ByteArray} {i : USize} {lineNo lineNo' : Nat} {tail : USize},
        b.size - i.toNat ≤ n →
        feedChunk md sd b i lineNo s = .ok (.ok (sd', lineNo', tail), s') →
        ParseStep s s' ∧ PersStateD sd' ∧
          ∃ sc', ConLeche.Frontend.feedChunk sc b i lineNo
              = .ok (sc', lineNo', tail) ∧ StateDRel s'.store sd' sc' := by
  intro n
  induction n with
  | zero =>
    intro s s' hok hoff hpins hrb sd sd' sc hrel hp b i lineNo lineNo' tail hmeas hrun
    rw [feedChunk] at hrun
    have hnot : ¬ (i < b.usize) := fun hlt => by
      have := ConLeche.Frontend.usizeInBounds b i hlt; omega
    rw [dif_neg hnot] at hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrun
    obtain ⟨h1, h2, h3⟩ : sd' = sd ∧ lineNo' = lineNo ∧ tail = i := by
      have := Except.ok.inj hv
      exact ⟨congrArg Prod.fst this, congrArg (Prod.fst ∘ Prod.snd) this,
        congrArg (Prod.snd ∘ Prod.snd) this⟩
    subst h1; subst h2; subst h3; subst hs
    refine ⟨ParseStep.refl hok, hp, sc, ?_, hrel⟩
    rw [ConLeche.Frontend.feedChunk, dif_neg hnot]
  | succ n ih =>
    intro s s' hok hoff hpins hrb sd sd' sc hrel hp b i lineNo lineNo' tail hmeas hrun
    rw [feedChunk] at hrun
    by_cases hlt : i < b.usize
    case neg =>
      rw [dif_neg hlt] at hrun
      obtain ⟨hv, hs⟩ := AM.pure_ok hrun
      obtain ⟨h1, h2, h3⟩ : sd' = sd ∧ lineNo' = lineNo ∧ tail = i := by
        have := Except.ok.inj hv
        exact ⟨congrArg Prod.fst this, congrArg (Prod.fst ∘ Prod.snd) this,
          congrArg (Prod.snd ∘ Prod.snd) this⟩
      subst h1; subst h2; subst h3; subst hs
      refine ⟨ParseStep.refl hok, hp, sc, ?_, hrel⟩
      rw [ConLeche.Frontend.feedChunk, dif_neg hlt]
    case pos =>
    rw [dif_pos hlt] at hrun
    have hbase : ConLeche.Frontend.feedChunk sc b i lineNo
        = (match ConLeche.Frontend.scanLineFwd b i with
           | .err e =>
             if ConLeche.Frontend.newlineFrom b i then
               .error (.internal (ConLeche.Frontend.ScanErr.render
                 ⟨e.offset - i.toNat, e.what⟩), lineNo + 1)
             else .ok (sc, lineNo, i)
           | .ok r j =>
             if j == 0 then .ok (sc, lineNo, i)
             else
               match ConLeche.Frontend.applyLine sc r with
               | .error msg => .error (.internal msg, lineNo + 1)
               | .ok (.inr v) => .error (v.toError, lineNo + 1)
               | .ok (.inl st) =>
                 if _hj : i < j then
                   ConLeche.Frontend.feedChunk st b j (lineNo + 1)
                 else .error (.internal "the line scanner made no progress",
                   lineNo + 1)) := by
      rw [ConLeche.Frontend.feedChunk, dif_pos hlt,
        ← ConLeche.Frontend.scanLineFwd_eq]
      rfl
    cases hsc : ConLeche.Frontend.scanLineFwd b i with
    | err e =>
      simp only [hsc] at hrun hbase
      by_cases hnl : ConLeche.Frontend.newlineFrom b i = true
      · simp only [hnl, if_true] at hrun
        exact absurd (AM.pure_ok hrun).1 (by simp)
      · have hnl' : ConLeche.Frontend.newlineFrom b i = false := by
          simpa using hnl
        simp only [hnl', Bool.false_eq_true, if_false] at hrun hbase
        obtain ⟨hv, hs⟩ := AM.pure_ok hrun
        obtain ⟨h1, h2, h3⟩ : sd' = sd ∧ lineNo' = lineNo ∧ tail = i := by
          have := Except.ok.inj hv
          exact ⟨congrArg Prod.fst this, congrArg (Prod.fst ∘ Prod.snd) this,
            congrArg (Prod.snd ∘ Prod.snd) this⟩
        subst h1; subst h2; subst h3; subst hs
        exact ⟨ParseStep.refl hok, hp, sc, hbase, hrel⟩
    | ok r j =>
      simp only [hsc] at hrun hbase
      by_cases hj : (j == 0) = true
      · simp only [hj, if_true] at hrun hbase
        obtain ⟨hv, hs⟩ := AM.pure_ok hrun
        obtain ⟨h1, h2, h3⟩ : sd' = sd ∧ lineNo' = lineNo ∧ tail = i := by
          have := Except.ok.inj hv
          exact ⟨congrArg Prod.fst this, congrArg (Prod.fst ∘ Prod.snd) this,
            congrArg (Prod.snd ∘ Prod.snd) this⟩
        subst h1; subst h2; subst h3; subst hs
        exact ⟨ParseStep.refl hok, hp, sc, hbase, hrel⟩
      · have hj' : (j == 0) = false := by simpa using hj
        simp only [hj', Bool.false_eq_true, if_false] at hrun hbase
        obtain ⟨x, s₁, hline, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hstep, hpers, y, hy, hxy⟩ :=
          applyLine_run hmw hmr hok hoff hpins hrb hrel hp hline
        cases x with
        | inr v => exact absurd (AM.pure_ok hrest).1 (by simp)
        | inl st =>
          obtain ⟨sc₁, hyx, hrel₁⟩ := hxy.inl_left rfl
          subst hyx
          simp only [hy] at hbase
          simp only [] at hrest
          by_cases hij : i < j
          · rw [dif_pos hij] at hbase
            rw [dif_pos hij] at hrest
            have hmeas' : b.size - j.toNat ≤ n := by
              have h1 := ConLeche.Frontend.usizeInBounds b i hlt
              have h2 := USize.lt_iff_toNat_lt.mp hij
              omega
            obtain ⟨hstep2, hpers2, sc₂, hcl2, hrel₂⟩ :=
              ih hstep.ok (by rw [hstep.scratch, hoff]) (hpins.mono hstep.ext hstep.pins) (hrb.step hstep)
                hrel₁ (hpers st rfl)
                hmeas' hrest
            exact ⟨hstep.trans hstep2, hpers2, sc₂, by rw [hbase, hcl2], hrel₂⟩
          · rw [dif_neg hij] at hrest
            exact absurd (AM.pure_ok hrest).1 (by simp)

/-- con-leche: ConLeche/Frontend/ExportC.lean:787-788 feedChunk — **every
complete line of a buffer, applied in order**: the state, the line count and
where the incomplete tail begins.  The three numbers are `Nat`/`USize` on both
sides and come out EQUAL, not merely related — they are the fold's own
bookkeeping and the next chunk's input. -/
theorem feedChunk_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {b : ByteArray} {i : USize} {lineNo lineNo' : Nat}
    {tail : USize}
    (hrun : feedChunk md sd b i lineNo s = .ok (.ok (sd', lineNo', tail), s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.feedChunk sc b i lineNo
          = .ok (sc', lineNo', tail) ∧ StateDRel s'.store sd' sc' :=
  feedChunk_run_le hmw hmr (b.size - i.toNat) hok hoff hpins hrb hrel hp
    (Nat.le_refl _) hrun

/-! ## The chunk drivers -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:857-858 chunkStep — one chunk:
the carried tail in front, every complete line fed, the new tail cut off.  The
carry, the line count and the running total come out equal, as `feedChunk`'s
do.

The size guard (`total + buf0.size ≥ USize.size`, the same test on both
sides), the `carry ++ buf0` concatenation (the same `ByteArray` on both sides
— the twin does not abstract bytes) and `feedChunk_run`. -/
theorem chunkStep_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {carry carry' : ByteArray} {lineNo total : Nat}
    {buf0 : ByteArray} {lineNo' total' : Nat}
    (hrun : chunkStep md sd carry lineNo total buf0 s
      = .ok (.ok (sd', carry', lineNo', total'), s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.chunkStep sc carry lineNo total buf0
          = .ok (sc', carry', lineNo', total') ∧ StateDRel s'.store sd' sc' := by
  rw [chunkStep] at hrun
  by_cases hsz : total + buf0.size ≥ USize.size
  · rw [if_pos hsz] at hrun
    exact absurd (AM.pure_ok hrun).1 (by simp)
  · rw [if_neg hsz] at hrun
    simp only [pure_bind] at hrun
    obtain ⟨x, s₁, hfeed, hrest⟩ := AM.bind_ok hrun
    cases x with
    | error e =>
      simp only [] at hrest
      exact absurd (AM.pure_ok hrest).1 (by simp)
    | ok p =>
      obtain ⟨sd₁, lineNo₁, tail₁⟩ := p
      simp only [] at hrest
      obtain ⟨hv, hs⟩ := AM.pure_ok hrest
      simp only [Except.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨h1, h2, h3, h4⟩ := hv
      subst h1; subst h2; subst h3; subst h4; subst hs
      obtain ⟨hstep, hpers, sc₁, hcl, hrel'⟩ :=
        feedChunk_run hmw hmr hok hoff hpins hrb hrel hp hfeed
      refine ⟨hstep, hpers, sc₁, ?_, hrel'⟩
      rw [ConLeche.Frontend.chunkStep, if_neg hsz]
      simp only [hcl]

/-- con-leche: ConLeche/Frontend/ExportC.lean:868-869 chunkFinish — the end of
the stream: the carried tail, if any, is its last line.

`applyFinalLine_run` and `ParseResultRel.ofState`. -/
theorem chunkFinish_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {carry : ByteArray} {lineNo : Nat} {r : ParseResultD}
    (hrun : chunkFinish md sd carry lineNo s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, ConLeche.Frontend.chunkFinish sc carry lineNo = .ok rc ∧
        ParseResultRel s'.store r rc := by
  rw [chunkFinish] at hrun
  by_cases hce : carry.isEmpty = true
  · rw [if_pos hce] at hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrun
    simp only [Except.ok.injEq] at hv
    subst hv; subst hs
    exact ⟨ParseStep.refl hok, PersParseResult.ofState hp, _,
      by rw [ConLeche.Frontend.chunkFinish, if_pos hce],
      ParseResultRel.ofState hrel⟩
  · rw [if_neg hce] at hrun
    simp only [pure_bind] at hrun
    obtain ⟨x, s₁, hfin, hrest⟩ := AM.bind_ok hrun
    cases x with
    | error e =>
      simp only [] at hrest
      exact absurd (AM.pure_ok hrest).1 (by simp)
    | ok sd₁ =>
      simp only [] at hrest
      obtain ⟨hv, hs⟩ := AM.pure_ok hrest
      simp only [Except.ok.injEq] at hv
      subst hv; subst hs
      obtain ⟨hstep, hpers, sc₁, hcl, hrel'⟩ :=
        applyFinalLine_run hmw hmr hok hoff hpins hrb hrel hp hfin
      refine ⟨hstep, PersParseResult.ofState hpers, _, ?_,
        ParseResultRel.ofState hrel'⟩
      rw [ConLeche.Frontend.chunkFinish, if_neg hce]
      simp only [hcl]

/-! ## The two entry points -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:831-832 parseBytes — the whole
input fed at once, then the last line.  **This is the prelude's parse**
(`Arena/Frontend/Prelude.lean`'s `builtinPreludeE` is `parseBytes` of
`PreludeText.preludeText`), so it carries its own statement rather than being
a corollary of the chunk fold.

`StateD_init_run`, `feedChunk_run`, `applyFinalLine_run`, composed. -/
theorem parseBytes_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {b : ByteArray} {im ce : Bool}
    {r : ParseResultD} (hrun : parseBytes md b im ce s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, ConLeche.Frontend.parseBytes b im ce = .ok rc ∧
        ParseResultRel s'.store r rc := by
  rw [parseBytes] at hrun
  by_cases hsz : b.size ≥ USize.size
  · rw [if_pos hsz] at hrun
    exact absurd (AM.pure_ok hrun).1 (by simp)
  · rw [if_neg hsz] at hrun
    simp only [pure_bind] at hrun
    obtain ⟨sd0, s0, hinit, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep0, hp0, hrel0⟩ := StateD_init_run hok hoff hinit
    obtain ⟨x, s₁, hfeed, hrest2⟩ := AM.bind_ok hrest
    cases x with
    | error e =>
      simp only [] at hrest2
      exact absurd (AM.pure_ok hrest2).1 (by simp)
    | ok p =>
      obtain ⟨sd₁, lineNo₁, tail₁⟩ := p
      simp only [] at hrest2
      obtain ⟨hstep1, hp1, sc₁, hcl1, hrel1⟩ :=
        feedChunk_run hmw hmr hstep0.ok (by rw [hstep0.scratch, hoff])
          (hpins.mono hstep0.ext hstep0.pins) (hrb.step hstep0) hrel0
          hp0 hfeed
      by_cases htl : tail₁ < b.usize
      · rw [if_pos htl] at hrest2
        obtain ⟨y, s₂, hfin, hrest3⟩ := AM.bind_ok hrest2
        cases y with
        | error e =>
          simp only [] at hrest3
          exact absurd (AM.pure_ok hrest3).1 (by simp)
        | ok sd₂ =>
          simp only [] at hrest3
          obtain ⟨hv, hs⟩ := AM.pure_ok hrest3
          simp only [Except.ok.injEq] at hv
          subst hv; subst hs
          obtain ⟨hstep2, hp2, sc₂, hcl2, hrel2⟩ :=
            applyFinalLine_run hmw hmr hstep1.ok
              (by rw [hstep1.scratch, hstep0.scratch, hoff])
              (hpins.mono (hstep0.trans hstep1).ext (hstep0.trans hstep1).pins) (hrb.step (hstep0.trans hstep1)) hrel1 hp1 hfin
          refine ⟨(hstep0.trans hstep1).trans hstep2,
            PersParseResult.ofState hp2, _, ?_, ParseResultRel.ofState hrel2⟩
          rw [ConLeche.Frontend.parseBytes, if_neg hsz]
          simp only [pure_bind, hcl1, Bind.bind, Except.bind, htl, if_true, hcl2,
            pure, Except.pure]
      · rw [if_neg htl] at hrest2
        obtain ⟨hv, hs⟩ := AM.pure_ok hrest2
        simp only [Except.ok.injEq] at hv
        subst hv; subst hs
        refine ⟨hstep0.trans hstep1, PersParseResult.ofState hp1, _, ?_,
          ParseResultRel.ofState hrel1⟩
        rw [ConLeche.Frontend.parseBytes, if_neg hsz]
        simp only [pure_bind, hcl1, Bind.bind, Except.bind, htl, if_false,
          pure, Except.pure]

/-- con-leche: ConLeche/Frontend/ExportC.lean:895-901 parseChunks.go — the
streaming fold, step by step.

The list induction, with `chunkStep_run` at the step and `chunkFinish_run` at
the end; `ParseStep.trans` carries the frame and each step's own theorem
carries the relation past its appends. -/
theorem parseChunksGo_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {carry : ByteArray} {lineNo total : Nat}
    {chunks : List ByteArray} {r : ParseResultD}
    (hrun : parseChunksGo md sd carry lineNo total chunks s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, parseChunksC sc carry lineNo total chunks = .ok rc ∧
        ParseResultRel s'.store r rc := by
  induction chunks generalizing s sd sc carry lineNo total with
  | nil =>
    rw [parseChunksGo] at hrun
    obtain ⟨hstep, hpers, rc, hcl, hrel'⟩ :=
      chunkFinish_run hmw hmr hok hoff hpins hrb hrel hp hrun
    exact ⟨hstep, hpers, rc, hcl, hrel'⟩
  | cons c cs ih =>
    rw [parseChunksGo] at hrun
    obtain ⟨x, s₁, hstepc, hrest⟩ := AM.bind_ok hrun
    cases x with
    | error e =>
      simp only [] at hrest
      exact absurd (AM.pure_ok hrest).1 (by simp)
    | ok q =>
      obtain ⟨sd₁, carry₁, lineNo₁, total₁⟩ := q
      simp only [] at hrest
      obtain ⟨hstep1, hp1, sc₁, hcl1, hrel1⟩ :=
        chunkStep_run hmw hmr hok hoff hpins hrb hrel hp hstepc
      obtain ⟨hstep2, hp2, rc, hcl2, hrel2⟩ :=
        ih hstep1.ok (by rw [hstep1.scratch, hoff]) (hpins.mono hstep1.ext hstep1.pins) (hrb.step hstep1)
          hrel1 hp1 hrest
      refine ⟨hstep1.trans hstep2, hp2, rc, ?_, hrel2⟩
      rw [parseChunksC]
      simp only [hcl1, hcl2]

/-- con-leche: ConLeche/Frontend/ExportC.lean:891-893 parseChunks —
**DESIGN §8.2'S PARSER STATEMENT**: the twin's streaming parse denotes
con-leche's, record for record.

The fold theorems' two frontend obligations (`hden`, `hpd`) are its two
conclusions: `denoteDecls s'.store r.decls.toList = some rc.decls.toList` is
the `decls` clause of `ParseResultRel` (which is what `denoteDeclArray` is),
and `PersParseResult r` is `∀ x ∈ ds, PersDecl x`.

`StateD_init_run` and `parseChunksGo_run` through `parseChunks_eq`. -/
theorem parseChunks_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {chunks : List ByteArray} {im ce : Bool}
    {r : ParseResultD}
    (hrun : parseChunks md chunks im ce s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, ConLeche.Frontend.parseChunks chunks im ce = .ok rc ∧
        ParseResultRel s'.store r rc := by
  rw [parseChunks] at hrun
  obtain ⟨sd0, s0, hinit, hgo⟩ := AM.bind_ok hrun
  obtain ⟨hstep0, hp0, hrel0⟩ := StateD_init_run hok hoff hinit
  obtain ⟨hstep1, hp1, rc, hcl, hrel1⟩ :=
    parseChunksGo_run hmw hmr hstep0.ok (by rw [hstep0.scratch, hoff])
      (hpins.mono hstep0.ext hstep0.pins) (hrb.step hstep0) hrel0
      hp0 hgo
  exact ⟨hstep0.trans hstep1, hp1, rc, by rw [parseChunks_eq]; exact hcl,
    hrel1⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:891-893 parseChunks — **the
exactness equation, at its letter.**  DESIGN §8.2 writes the parser tier as
`denoteDecls (Arena.parse chunks) = parseChunks chunks`, and this is that
sentence with the `Option` the readback needs and the state the `AM` threads:
*the declarations the twin parsed denote, and what they denote is exactly the
declarations con-leche parsed.*

The record count travels with it — `ParseResultRel.genRecords` is
`r.genRecords = rc.genRecords`, which is what `Arena/Main.lean`'s verdict
number (`r.decls.size - r.genRecords`) is read off — so DESIGN §8.2's "and
the same for the record count / `genRecords`" is this corollary's second
conjunct. -/
theorem parseChunks_exact {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) (hrb : ReadCachesOK s) {chunks : List ByteArray} {im ce : Bool}
    {r : ParseResultD}
    (hrun : parseChunks md chunks im ce s = .ok (.ok r, s')) :
    ∃ rc, ConLeche.Frontend.parseChunks chunks im ce = .ok rc ∧
      denoteDecls s'.store r.decls.toList = some rc.decls.toList ∧
      r.decls.size = rc.decls.size ∧ r.genRecords = rc.genRecords ∧
      (∀ d ∈ r.decls, PersDecl d) := by
  obtain ⟨-, hpers, rc, hrc, hrel⟩ := parseChunks_run hmw hmr hok hoff hpins hrb hrun
  have h := hrel.decls
  simp only [denoteDeclArray, Option.map_eq_some_iff] at h
  obtain ⟨xs, hxs, hEq⟩ := h
  have hdec : denoteDecls s'.store r.decls.toList = some rc.decls.toList := by
    rw [hxs, ← hEq]
  have hlen : r.decls.size = rc.decls.size := by
    have hlen := denoteDecls_length _ _ hxs
    rw [← hEq]
    simpa using hlen
  exact ⟨rc, hrc, hdec, hlen, hrel.genRecords, hpers⟩

end ConRon.Bridge.Frontend
