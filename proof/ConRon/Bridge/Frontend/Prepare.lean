/-
# `ConRon.Bridge.Frontend.Prepare` — the two permuting passes, and the prelude

Between the parse and the fold stand `preparePrelude` and, inside it, the
`Nat`-operation ground hoist.  Both are **total, pure permutations of a record
array** — no record is dropped, rewritten or retagged — which is why
con-leche's own specification of the first is as weak as it is
(`ConLeche/Frontend/Prepare.lean`'s module note):

    ∃ extra, (∀ d ∈ extra, d ∈ prelude) ∧
      (preparePrelude ds).toList.Perm (ds.toList ++ extra)

and why the capstone needs only its corollary
`ConLeche.Frontend.mem_preparePrelude` (`Verify/Frontend/Prepare.lean:174`):
**preparation keeps every record it was given.**

Over handles nothing about that changes, and there is one pleasant surprise:
`declares` and `pick` are PURE on both sides (`Arena/Env.lean`'s
`IProjTable.tableName` note is what buys it — `IDeclaration.names` is a pure
function of handles), so the two `Array` walks are the same walk with
`NIdx` where con-leche has `Name`, and the only monadic step in the whole
module is `preludeKey`'s `.anonymous` fall-through, which has to be interned.

**The hoist is the one place a handle comparison stands for a name
comparison** and therefore the one place `denoteN_inj` (DESIGN §8.3's
soundness obligation) is load-bearing here: `hoistTargets` indexes the stream
by declared name, and a collision between two handles denoting one name would
move a record con-leche does not move.  Injectivity is exactly what rules that
out.

## The prelude, and its gate

`Arena/Frontend/Prelude.lean`'s `builtinPreludeE` is `parseBytes` of
`Arena/Frontend/PreludeText.lean`'s `preludeText`, where con-leche's is
`parseExportD` of `builtinPreludeText` — an `include_str` of
`pins/leanprover-lean4-v4.33.0.prelude.ndjson`.  The two are the same bytes,
and **that is a gate, not a theorem**: `scripts/gen-prelude-lean.sh` generates
`PreludeText.lean` from con-leche's own committed file and
`scripts/gen-prelude-lean.sh --check` is step 11 of `scripts/gates.sh`.
`PreludeText.lean`'s own module note states the wrapping is byte-exact
("the concatenation of the chunks is the ndjson file, byte for byte,
including its final newline").

So `builtinPreludeE_run` below is stated **parametrically in the bytes** —
`preludeText = builtinPreludeText.toUTF8` is its hypothesis, discharged by the
gate — which is the same move `conron.no_False_declaration` makes for the
pins and the prelude (`RefineOld/Main.lean`'s "The prelude never has to be
identified with con-leche's") and which keeps the axiom census at three.
-/
import ConRon.Bridge.Frontend.Chunks
import ConRon.Arena.Frontend.Prelude
import ConLeche.Frontend.Prelude
import ConLeche.Frontend.NatOpGround
import ConLeche.Verify.Frontend.Prepare

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The prelude index -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:87-88 PreludeIx — a prelude
index denotes con-leche's: its records, in order. -/
def PreludeIxRel (st : EStore) (pre : PreludeIx)
    (preC : ConLeche.Frontend.PreludeIx) : Prop :=
  denoteDeclArray st pre.decls = some preC.decls

/-- con-leche: none — a prelude index's records are persistent. -/
def PersPreludeIx (pre : PreludeIx) : Prop := PersDecls pre.decls

/-! ## The prelude's own parse -/

/-- con-leche: ConLeche/Frontend/Prelude.lean:67 builtinPreludeE — **the
built-in prelude parses to con-leche's**, parametrically in the bytes: the
hypothesis is that the committed constant IS con-leche's committed file, which
`scripts/gen-prelude-lean.sh --check` (step 11 of `scripts/gates.sh`) is the
proof of, and which `Arena/Frontend/PreludeText.lean`'s module note states as
its own contract.

`parseExportD` is `parseBytes` of `String.toUTF8`
(`ConLeche/Frontend/ExportC.lean:843-845`), so the two sides run the same
function on the same bytes once the hypothesis is in hand.

`parseBytes_run` under `hbytes`. -/
theorem builtinPreludeE_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md)
    (hbytes : preludeText = ConLeche.Frontend.builtinPreludeText.toUTF8)
    {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    {pre : PreludeIx} (hrun : builtinPreludeE md s = .ok (.ok pre, s')) :
    ParseStep s s' ∧ PersPreludeIx pre ∧
      ∃ preC, ConLeche.Frontend.builtinPreludeE = .ok preC ∧
        PreludeIxRel s'.store pre preC := by
  rw [builtinPreludeE] at hrun
  obtain ⟨x, s₁, hpb, hrest⟩ := AM.bind_ok hrun
  cases x with
  | error e =>
    simp only [] at hrest
    exact absurd (AM.pure_ok hrest).1 (by simp)
  | ok r =>
    simp only [] at hrest
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest
    simp only [Except.ok.injEq] at hv
    subst hv; subst hs
    rw [hbytes] at hpb
    obtain ⟨hstep, hpers, rc, hcl, hrel⟩ := parseBytes_run hmw hmr hok hoff hpb
    refine ⟨hstep, hpers, ⟨rc.decls⟩, ?_, hrel.decls⟩
    rw [ConLeche.Frontend.builtinPreludeE, ConLeche.Frontend.parseExportD, hcl]
    rfl

/-! ## The prelude's front -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:93 preludeKey — the name a
prelude record is looked up by.  The twin is monadic only for the
`.anonymous` fall-through.

**Round 4's finding 16 bites here**: `IDeclaration.names`
(`Arena/Env.lean:262-266`) reads `IConstantInfo.name`, which at a `.projInfo`
is the STORED handle `tbl.tableName` — and `denoteProjTable` does not mention
`tableName`, so `denoteDecl st d = some dP` does NOT give
`denoteNList st.ns d.names = some dP.names`.  Only
`Bridge/StateOK.lean:507-511`'s `IProjTableOK.named` ties the two.  The frame
is already the honest one here (`preludeKey` interns `.anonymous` on the
fall-through), but the ANSWER clause needs that side condition or a
strengthened seam promise; see `Bridge/Frontend/Lines.lean`'s `noteDecl_run`
for the finding in full.

`sorry`: finding 16 first, then `IDeclaration.names`'s exactness at the head
and `internNNode_istep`.  Task #97-P3-Frontend's sorry list, item 20. -/
theorem preludeKey_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {d : IDeclaration} {dP : Declaration}
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP) {n : NIdx}
    (hrun : preludeKey d s = .ok (n, s')) :
    ParseStep s s' ∧ PersN n ∧
      denoteN s'.store.ns n = some (ConLeche.Frontend.preludeKey dP) := by
  sorry

/-- con-leche: ConLeche/Frontend/Prepare.lean:110 declares / :122 pick — the
stream's own copy of a prelude record, pulled out.  PURE on both sides
(`Arena/Frontend/Prepare.lean`'s note), so this is an equation about
`Array.findIdx` at two predicates that agree — which they do because
`d.names.contains n` is a handle test where con-leche's is a name test, and
`denoteN_inj` makes the two the same test on a well-formed store.

**Round 4's finding 16 bites here too**: `declares n d` is
`d.names.contains n`, so this statement reads `IDeclaration.names` at every
record of the stream and needs its exactness — which a `.projInfo` does not
give without `IProjTableOK` (see `preludeKey_run` above).

`sorry`: finding 16, then `denoteN_inj` at the `findIdx` predicate and
`Array.eraseIdxIfInBounds`'s own law.  Task #97-P3-Frontend's sorry list,
item 20. -/
theorem pick_denote {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN st.ns n = some nP)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hds : denoteDeclArray st ds = some dsP) :
    (∀ d, (pick n ds).1 = some d →
      ∃ dP, ConRon.Arena.Frontend.denoteDecl st d = some dP ∧
        (ConLeche.Frontend.pick nP dsP).1 = some dP) ∧
    ((pick n ds).1 = none → (ConLeche.Frontend.pick nP dsP).1 = none) ∧
    denoteDeclArray st (pick n ds).2 = some (ConLeche.Frontend.pick nP dsP).2 := by
  sorry

/-- con-leche: ConLeche/Frontend/Prepare.lean:130-131 frontOf — the prepared
stream's front, prelude record by prelude record.

**The persistence clauses travel with the denotations**, because both passes
of the preparation are PERMUTATIONS: no record is built, so every record out
is a record in, and `Bridge/Checker/Capstone.lean`'s `hpd` at the fold's
argument is the parse's and the prelude's, carried.

`sorry`: a list induction over `preludeKey_run` and `pick_denote`, both of
which wait on round 4's finding 16.  Task #97-P3-Frontend's sorry list,
item 20. -/
theorem frontOf_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {acc : Array IDeclaration}
    {accP : Array Declaration} (hacc : denoteDeclArray s.store acc = some accP)
    (hpacc : PersDecls acc)
    {ps : List IDeclaration} {psP : List Declaration}
    (hps : denoteDecls s.store ps = some psP) (hpps : ∀ d ∈ ps, PersDecl d)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hds : denoteDeclArray s.store ds = some dsP) (hpds : PersDecls ds)
    {front rest : Array IDeclaration}
    (hrun : frontOf acc ps ds s = .ok ((front, rest), s')) :
    ParseStep s s' ∧ PersDecls front ∧ PersDecls rest ∧
      denoteDeclArray s'.store front
          = some (ConLeche.Frontend.frontOf accP psP dsP).1 ∧
        denoteDeclArray s'.store rest
          = some (ConLeche.Frontend.frontOf accP psP dsP).2 := by
  sorry

/-! ## The ground hoist -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:82 Declaration.usedConsts —
the constants a record mentions.  A walk over the record's terms with a `seen`
set, so the GRAY-invariant shape again.

**Round 4's finding 16 bites the FRAME here**: `usedConstsBlock`
(`Arena/Frontend/NatOpGround.lean:85-95`) calls `ci.toConstantVal`, whose
`.projInfo` arm interns `Sort 1`, so `s' = s` is false at a block that holds a
projection table.  `ParseStep s s'` is the honest frame, with the answer read
at `s'.store`; see `Bridge/Frontend/Lines.lean`'s `noteDecl_run`.

`sorry`: finding 16, then the fuel induction with the `seen` set —
`Bridge/ExprOps/Leaves.lean`'s open shape.  Task #97-P3-Frontend's sorry list,
item 21. -/
theorem usedConsts_run {s s' : AState} (hok : StateOK s) {d : IDeclaration}
    {dP : Declaration} (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    {ns : Array NIdx} (hrun : IDeclaration.usedConsts d s = .ok (ns, s')) :
    s' = s ∧ denoteNList s.store.ns ns.toList
      = some (ConLeche.Declaration.usedConsts dP).toList := by
  sorry

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:110 hoistTargets — **the
hoist's index, and where `denoteN_inj` is load-bearing**: the stream is
indexed by declared name, and two handles denoting one name would make the
twin move a record con-leche does not move.

**Round 4's finding 16 bites both halves**: `nameIndex`
(`Arena/Frontend/NatOpGround.lean:133-138`) indexes by `ds[k].names`, and
`usedConsts` moves the store at a projection table.  The frame is `ParseStep`,
and the name exactness wants `IProjTableOK`; see
`Bridge/Frontend/Lines.lean`'s `noteDecl_run`.

`sorry`: finding 16, then `usedConsts_run` and `isNatOpRecord_run` at the
fold, with `denoteN_inj` for the `Std.HashMap NIdx Nat` keyed by handle
against con-leche's `Std.HashMap Nat Nat` keyed by stream position — the two
maps are equal as functions of the position, which is what `applyHoist`
reads.  Task #97-P3-Frontend's sorry list, item 21. -/
theorem hoistTargets_run {s s' : AState} (hok : StateOK s)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hwf : StoreWF s.store) (hds : denoteDeclArray s.store ds = some dsP)
    {target : Std.HashMap Nat Nat} (hrun : hoistTargets ds s = .ok (target, s')) :
    s' = s ∧ target = ConLeche.Frontend.hoistTargets dsP := by
  sorry

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:167 hoistNatOpGround — the
hoist.  Its answer is a PERMUTATION of its argument, so the denotation of the
result is the permutation of the denotation, and the moved-name list denotes.

`sorry`: `hoistTargets_run` (which waits on round 4's finding 16), then
`applyHoist`'s `reorder` as a `List.map` over a permutation of indices — the
same list of indices on both sides.  Task #97-P3-Frontend's sorry list,
item 21. -/
theorem hoistNatOpGround_run {s s' : AState} (hok : StateOK s)
    (hwf : StoreWF s.store) {ds : Array IDeclaration} {dsP : Array Declaration}
    (hds : denoteDeclArray s.store ds = some dsP) (hpds : PersDecls ds)
    {out : Array IDeclaration} {moved : Array NIdx}
    (hrun : hoistNatOpGround ds s = .ok ((out, moved), s')) :
    s' = s ∧ PersDecls out ∧ denoteDeclArray s.store out
        = some (ConLeche.Frontend.hoistNatOpGround dsP).1 ∧
      denoteNList s.store.ns moved.toList
        = some (ConLeche.Frontend.hoistNatOpGround dsP).2.toList := by
  sorry

/-! ## The prepared stream -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:171 preparePrelude — **the
prepared stream denotes con-leche's prepared stream**, which is the second
half of what the capstone's chain needs: the parse's exactness gets the
records, and this carries them across the two permuting passes into the
fold's argument.

`frontOf_run` and `hoistNatOpGround_run` composed. -/
theorem preparePrelude_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {pre : PreludeIx}
    {preC : ConLeche.Frontend.PreludeIx} (hpre : PreludeIxRel s.store pre preC)
    (hprep : PersPreludeIx pre) {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDeclArray s.store ds = some dsP)
    (hpds : PersDecls ds) {out : Array IDeclaration}
    (hrun : preparePrelude pre ds s = .ok (out, s')) :
    ParseStep s s' ∧ PersDecls out ∧
      denoteDeclArray s'.store out
        = some (ConLeche.Frontend.preparePrelude preC dsP) := by
  rw [preparePrelude] at hrun
  obtain ⟨prep, s₁, hprepD, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv, hs⟩ := AM.pure_ok hrest
  subst hv; subst hs
  rw [prepareD] at hprepD
  obtain ⟨fr, s₂, hfront, hrest2⟩ := AM.bind_ok hprepD
  obtain ⟨front, rest⟩ := fr
  simp only [] at hrest2
  obtain ⟨dh, s₃, hhoist, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨decls, hoisted⟩ := dh
  simp only [] at hrest3
  obtain ⟨hv2, hs2⟩ := AM.pure_ok hrest3
  subst hs2
  obtain ⟨hstep1, hpf, hpr, hclf, hclr⟩ :=
    frontOf_run hok hoff (denoteDeclArray_empty s.store) (by intro d hd; simp at hd)
      (denoteDeclArray_iff.mp hpre) (by
        intro d hd
        exact hprep d (by simpa using hd))
      hds hpds hfront
  obtain ⟨hs3, hpo, hclo, -⟩ :=
    hoistNatOpGround_run hstep1.ok hstep1.ok.wf
      (denoteDeclArray_append hclf hclr)
      (by
        intro d hd
        rcases Array.mem_append.mp hd with h | h
        · exact hpf d h
        · exact hpr d h)
      hhoist
  subst hs3
  have hdecls : prep.decls = decls := by rw [hv2]
  refine ⟨hstep1, ?_, ?_⟩
  · rw [hdecls]; exact hpo
  · rw [hdecls, hclo, ConLeche.Frontend.preparePrelude,
      ConLeche.Frontend.prepareD]

/-- con-leche: ConLeche/Verify/Frontend/Prepare.lean:174 mem_preparePrelude —
**the preparation keeps every record**, over handles: the corollary the
capstone consumes, transported through the denotation.

Proved from `preparePrelude_run` and con-leche's own `mem_preparePrelude`, so
the permutation argument is never re-run on this side — which is the point of
stating the pass as a denotation equation rather than as a permutation. -/
theorem mem_preparePrelude_denote {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {pre : PreludeIx}
    {preC : ConLeche.Frontend.PreludeIx} (hpre : PreludeIxRel s.store pre preC)
    (hprep : PersPreludeIx pre) {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDeclArray s.store ds = some dsP)
    (hpds : PersDecls ds) {out : Array IDeclaration}
    (hrun : preparePrelude pre ds s = .ok (out, s'))
    {d : Declaration} (hmem : d ∈ dsP) :
    ∃ outP, denoteDeclArray s'.store out = some outP ∧ d ∈ outP := by
  obtain ⟨-, -, hout⟩ := preparePrelude_run hok hoff hpre hprep hds hpds hrun
  exact ⟨_, hout, ConLeche.Frontend.mem_preparePrelude hmem⟩

end ConRon.Bridge.Frontend
