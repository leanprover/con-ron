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

`sorry`: `parseBytes_run` under `hbytes`.  Task #97-P3-Frontend's sorry list,
item 19. -/
theorem builtinPreludeE_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md)
    (hbytes : preludeText = ConLeche.Frontend.builtinPreludeText.toUTF8)
    {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    {pre : PreludeIx} (hrun : builtinPreludeE md s = .ok (.ok pre, s')) :
    ParseStep s s' ∧ PersPreludeIx pre ∧
      ∃ preC, ConLeche.Frontend.builtinPreludeE = .ok preC ∧
        PreludeIxRel s'.store pre preC := by
  sorry

/-! ## The prelude's front -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:93 preludeKey — the name a
prelude record is looked up by.  The twin is monadic only for the
`.anonymous` fall-through.

`sorry`: `IDeclaration.names`'s exactness at the head, then
`internNNode_spec`.  Task #97-P3-Frontend's sorry list, item 20. -/
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

`sorry`: `denoteN_inj` at the `findIdx` predicate, then
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

`sorry`: a list induction over `preludeKey_run` and `pick_denote`.  Task
#97-P3-Frontend's sorry list, item 20. -/
theorem frontOf_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {acc : Array IDeclaration}
    {accP : Array Declaration} (hacc : denoteDeclArray s.store acc = some accP)
    {ps : List IDeclaration} {psP : List Declaration}
    (hps : denoteDecls s.store ps = some psP)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hds : denoteDeclArray s.store ds = some dsP)
    {front rest : Array IDeclaration}
    (hrun : frontOf acc ps ds s = .ok ((front, rest), s')) :
    ParseStep s s' ∧
      denoteDeclArray s'.store front
          = some (ConLeche.Frontend.frontOf accP psP dsP).1 ∧
        denoteDeclArray s'.store rest
          = some (ConLeche.Frontend.frontOf accP psP dsP).2 := by
  sorry

/-! ## The ground hoist -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:82 Declaration.usedConsts —
the constants a record mentions.  A walk over the record's terms with a `seen`
set, so the GRAY-invariant shape again.

`sorry`: the fuel induction with the `seen` set, `Bridge/ExprOps/Leaves.lean`'s
open shape.  Task #97-P3-Frontend's sorry list, item 21. -/
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

`sorry`: `usedConsts_run` and `isNatOpRecord_run` at the fold, with
`denoteN_inj` for the `Std.HashMap NIdx Nat` keyed by handle against
con-leche's `Std.HashMap Nat Nat` keyed by stream position — the two maps are
equal as functions of the position, which is what `applyHoist` reads.  Task
#97-P3-Frontend's sorry list, item 21. -/
theorem hoistTargets_run {s s' : AState} (hok : StateOK s)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hwf : StoreWF s.store) (hds : denoteDeclArray s.store ds = some dsP)
    {target : Std.HashMap Nat Nat} (hrun : hoistTargets ds s = .ok (target, s')) :
    s' = s ∧ target = ConLeche.Frontend.hoistTargets dsP := by
  sorry

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:167 hoistNatOpGround — the
hoist.  Its answer is a PERMUTATION of its argument, so the denotation of the
result is the permutation of the denotation, and the moved-name list denotes.

`sorry`: `hoistTargets_run`, then `applyHoist`'s `reorder` as a `List.map`
over a permutation of indices — the same list of indices on both sides.  Task
#97-P3-Frontend's sorry list, item 21. -/
theorem hoistNatOpGround_run {s s' : AState} (hok : StateOK s)
    (hwf : StoreWF s.store) {ds : Array IDeclaration} {dsP : Array Declaration}
    (hds : denoteDeclArray s.store ds = some dsP)
    {out : Array IDeclaration} {moved : Array NIdx}
    (hrun : hoistNatOpGround ds s = .ok ((out, moved), s')) :
    s' = s ∧ denoteDeclArray s.store out
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

`sorry`: `frontOf_run` and `hoistNatOpGround_run` composed.  Task
#97-P3-Frontend's sorry list, item 22. -/
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
  sorry

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
