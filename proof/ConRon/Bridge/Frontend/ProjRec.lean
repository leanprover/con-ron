/-
# `ConRon.Bridge.Frontend.ProjRec` — the projection rewrite, and the owner census

`Arena/Frontend/ProjRec.lean` is con-leche's `ConLeche/Frontend/ProjRec.lean`
clause for clause over handles, and its module note lists the three deviations
this tier has to account for.  Each is a theorem here, and none of them is a
*semantic* deviation:

1. **`buildBinders` takes a KIND, not a function.**  con-leche passes
   `mk : Expr → Option Expr`; DESIGN §3.4 forbids a closure, so the twin
   passes `ProjBinderKind` and dispatches on the tag.  The theorem is one
   `cases` on the kind with `mkProjMotive_run` / `mkProjMinor_run` as the two
   arms — con-leche's two lambdas, as two top-level functions.
2. **Three `List.any` / `List.find?` closures are explicit recursions.**
   `occursAnyOf`, `domsMentionAny`, `ctorsMentionBlock`, `findCtorRec`,
   `findRecRec`: each is its `List` combinator's own unfolding, so the theorem
   is a list induction whose step is `rfl` on con-leche's side.
3. **`projRecOwners` evaluates its guards in the cheap order, and the result
   is the same value.**  This is the tier's one *reordering* obligation and it
   is the module note's own argument as a theorem: when the `filterMap` is
   empty the whole function is `[]` whatever the guards say, so computing the
   guards only when it is non-empty is the same function.  It needs nothing
   about the guards themselves — which is why it survives task #97f's dedup
   (the two recognisers are now `Arena/Inductives/`'s twins and their
   exactness is the Inductives tier's, not this one's).

**What the level side costs.**  `projIotaLevel` runs `Level.isEquiv` on a
level tree READ BACK from an `LIdx` (DESIGN §8.3 lesson 4: intern the
representation, not the algorithm), so its theorem is `readLevel`'s exactness
(`Bridge/Specs.lean`) and then con-leche's own function on the same tree —
there is no level algorithm to relate at all.  That is lesson 4's ~1 800
saved proof lines, collected here.
-/
import ConRon.Bridge.Frontend.Shared
import ConRon.Arena.Frontend.ProjRec

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The name and level helpers -/

/-- con-leche: none — `viewN` in run form, off `Bridge/Specs.lean`'s triple. -/
theorem viewN_run {s s' : AState} {h : NIdx} {v : NNodeView}
    (hrun : viewN h s = .ok (v, s')) : s' = s ∧ s.store.ns.view h = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewN_spec s h)

/-- con-leche: none — the name store's own well-formedness, dug out of the
arena's: `StoreWF`'s nesting carries it down three levels. -/
theorem nsWF_of_StateOK {s : AState} (hok : StateOK s) :
    Arena.NStoreWF s.store.ns := by
  obtain ⟨rk, hw⟩ := hok.wf
  obtain ⟨rkl, hl⟩ := hw.lss.ls
  exact hl.ns

/-- con-leche: ConLeche/Frontend/ProjRec.lean:110 projIotaName — the artifact
name `T._model.proj_i.iota`, interned.

Three `internNNode`s, in `Bridge/Frontend/Shared.lean`'s `IStep` shape; the
persistence is the closed scratch tier's (`PersN_of_view`). -/
theorem projIotaName_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {T : NIdx} {TP : ConLeche.Name}
    (hT : denoteN s.store.ns T = some TP) {i : Nat} {n : NIdx}
    (hrun : projIotaName T i s = .ok (n, s')) :
    ParseStep s s' ∧ PersN n ∧
      denoteN s'.store.ns n = some (ConLeche.Frontend.projIotaName TP i) := by
  rw [ConRon.Arena.Frontend.projIotaName] at hrun
  obtain ⟨a, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, -, hda⟩ :=
    internNNode_istep hok hoff
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc; exact nview_isSome_of_denote hT) h1
  have hda' : denoteN s₁.store.ns a = some (TP.str "_model") := by
    rw [hda]
    simp only [denoteNView, denoteN_ext hT hstep1.ext, Option.map_some]
  obtain ⟨b, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hstep2, -, hdb⟩ :=
    internNNode_istep hstep1.ok hstep1.off
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc; exact nview_isSome_of_denote hda') h2
  have hdb' : denoteN s₂.store.ns b
      = some ((TP.str "_model").str s!"proj_{i}") := by
    rw [hdb]
    simp only [denoteNView, denoteN_ext hda' hstep2.ext, Option.map_some]
  obtain ⟨hstep3, hpn, hdn⟩ :=
    internNNode_istep hstep2.ok hstep2.off
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc; exact nview_isSome_of_denote hdb') hrest2
  refine ⟨((hstep1.trans hstep2).trans hstep3).toParse hoff, hpn, ?_⟩
  rw [hdn]
  simp only [denoteNView, denoteN_ext hdb' hstep3.ext, Option.map_some]
  rfl

/-- con-leche: ConLeche/Frontend/ProjRec.lean:116 isProjIotaName — the
recogniser, which reads the name back and runs con-leche's own test.

`sorry`: `readName`'s exactness (`Bridge/Specs.lean`).  Task
#97-P3-Frontend's sorry list, item 10. -/
theorem isProjIotaName_run {s s' : AState} (hok : StateOK s) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN s.store.ns n = some nP) {b : Bool}
    (hrun : isProjIotaName n s = .ok (b, s')) :
    s' = s ∧ b = ConLeche.Frontend.isProjIotaName nP := by
  sorry

/-- con-leche: ConLeche/Frontend/ProjRec.lean:122 projIotaLevel — the field's
sort, off the iota artifact's type.

`sorry`: `stripPisAll_run` and one `viewE`; the level is a handle the walk
returns, so the answer relation is `RelE` at `denoteL`.  Task
#97-P3-Frontend's sorry list, item 10. -/
theorem projIotaLevel_run {s s' : AState} (hok : StateOK s) {fuel : Nat}
    {ty : EIdx} {tyP : Expr} (hty : denoteE s.store ty = some tyP)
    {o : Option LIdx} (hrun : projIotaLevel fuel ty s = .ok (o, s')) :
    s' = s ∧ ∀ l, o = some l → ∃ u, denoteL s.store.ls l = some u ∧
      ConLeche.Frontend.projIotaLevel tyP = some u := by
  sorry

/-! ## The term walks -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:228 occursConstFast — the
memoised occurrence test.  A `Bool` answer names no handle, so task
#97-P3-0 §5's finding 1 applies: this is a `RelV` and the closer takes every
arm.

`sorry`: the fuel induction with the `seen` set's invariant — the same GRAY
shape `Bridge/ExprOps/Leaves.lean`'s `fvarLeavesGo_spec` is open on, and it
is open here for the same reason.  Task #97-P3-Frontend's sorry list,
item 11. -/
theorem occursConstFast_run {s s' : AState} (hok : StateOK s) {fuel : Nat}
    {n : NIdx} {nP : ConLeche.Name} (hn : denoteN s.store.ns n = some nP)
    {h : EIdx} {e : Expr} (he : denoteE s.store h = some e) {b : Bool}
    (hrun : occursConstFast fuel n h s = .ok (b, s')) :
    s' = s ∧ b = ConLeche.Frontend.occursConstFast nP e := by
  sorry

/-- con-leche: ConLeche/Frontend/ProjRec.lean:235 lamBody / :241 stripPisAll —
the two peels.  Read-only walks: no intern, so the state does not move.

`sorry`: two fuel inductions in `Bridge/ExprOps/Spine.lean`'s shape.  Task
#97-P3-Frontend's sorry list, item 11. -/
theorem stripPisAll_run {s s' : AState} (hok : StateOK s) {fuel : Nat}
    {h : EIdx} {e : Expr} (he : denoteE s.store h = some e)
    {bs : List (EIdx × BinderMeta)} {b : EIdx}
    (hrun : stripPisAll fuel h s = .ok ((bs, b), s')) :
    s' = s ∧ ∃ bsP bP, ConLeche.Frontend.stripPisAll e = (bsP, bP) ∧
      ListRel (fun (p : EIdx × BinderMeta) (q : Expr × BinderMeta) =>
        denoteE s.store p.1 = some q.1 ∧ p.2 = q.2) bs bsP ∧
      denoteE s.store b = some bP := by
  sorry

/-- con-leche: ConLeche/Frontend/ProjRec.lean:248 mkLams — the rebuild, which
interns.

`sorry`: `Bridge/StoreBind.lean`'s `internBindIE_spec'` at each binder, right
to left.  Task #97-P3-Frontend's sorry list, item 11. -/
theorem mkLams_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {bs : List (EIdx × BinderMeta)}
    {bsP : List (Expr × BinderMeta)}
    (hbs : ListRel (fun (p : EIdx × BinderMeta) (q : Expr × BinderMeta) =>
      denoteE s.store p.1 = some q.1 ∧ p.2 = q.2) bs bsP)
    {body : EIdx} {bodyP : Expr} (hb : denoteE s.store body = some bodyP)
    {h : EIdx} (hrun : mkLams bs body s = .ok (h, s')) :
    ParseStep s s' ∧ PersE h ∧
      denoteE s'.store h = some (ConLeche.Frontend.mkLams bsP bodyP) := by
  sorry

/-! ## The rewrite -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:283-284 projRecValue — **the
rewrite itself**: a projection function's body as a recursor application.

`sorry`: `stripPisAll_run`, `buildBinders_run`, `instPisOpen_run` and
`mkLams_run` composed; `buildBinders_run` is the `ProjBinderKind` dispatch of
deviation 1.  Task #97-P3-Frontend's sorry list, item 12. -/
theorem projRecValue_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {fuel : Nat} {o : ProjRecOwner}
    {oc : ConLeche.Frontend.ProjRecOwner} (ho : ProjRecOwnerRel s.store o oc)
    {l : LIdx} {u : Level} (hl : denoteL s.store.ls l = some u)
    {ty val : EIdx} {tyP valP : Expr} (hty : denoteE s.store ty = some tyP)
    (hval : denoteE s.store val = some valP) {i : Nat} {res : Option EIdx}
    (hrun : projRecValue fuel o l ty val i s = .ok (res, s')) :
    ParseStep s s' ∧ ∀ h, res = some h → PersE h ∧
      ∃ e, denoteE s'.store h = some e ∧
        ConLeche.Frontend.projRecValue oc u tyP valP i = some e := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:296-297 projRewriteD — the
rewrite AT A RECORD: the state's owner table is consulted, the iota name's
level is read, and the rewrite runs or does not.

`sorry`: `projRecValue_run` plus the `projOwners`/`projLevels` reads through
`Bridge/Frontend/Rel.lean`'s `MapRel`.  Task #97-P3-Frontend's sorry list,
item 12. -/
theorem projRewriteD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {cv : IConstantVal} {c : ConstantVal} (hcv : denoteCV s.store cv = some c)
    {vl : EIdx} {vlP : Expr} (hvl : denoteE s.store vl = some vlP)
    {o : Option EIdx} (hrun : projRewriteD sd cv vl s = .ok (o, s')) :
    ParseStep s s' ∧ ∀ h, o = some h → PersE h ∧
      ∃ e, denoteE s'.store h = some e ∧
        ConLeche.Frontend.projRewriteD sc c vlP = some e := by
  sorry

/-! ## The owner census, and the one reordering -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:344-347 projRecOwners — **the
owner census, AND the module note's deviation 3 as a theorem**: the twin
computes the `filterMap` first and the two guards only when it is non-empty,
which is the same value because both guard branches return `[]` and an empty
`filterMap` makes the whole function `[]` whatever the guards say.

**THE ONE PLACE IN THE PARSE THAT MOVES A PER-DECLARATION CACHE** (task
#97-P3-Frame).  Both guards are recognisers of the Inductives tier, and each
computes its `isProp` field with `Arena/Core.lean`'s `lvlEq?` — a cached
verdict walk that probes `lvlEqC` and on a miss writes `readLC` (twice,
through `readLevelM`) and `lvlEqC`.  Round one's `ParseStep` said
`s'.caches = s.caches`, which is false of this run; `ParseStep`'s cache clause
is now `Bridge/StateOK.lean`'s `CacheFrame` and this statement is true as it
stands.  Nothing here moves up to `CheckOK`, and nothing needs to:

* the FRAME is `Core.lvlEq?_frame` (`Bridge/Core/Walks/Cached.lean`, closed),
  which takes no cache-content hypothesis at all — the tables a call writes
  are a fact about the program text;
* the ANSWER does not depend on the verdict.  `isProp` fills a FIELD of a
  record the recogniser has already decided to return, and this walk reads the
  recognisers through `.isSome` alone, so a wrong `isProp` could not change
  `os`.  (That is also why the two recognisers' own statements stay at `CSpec`
  and this one does not have to follow them up: their `…Rel.isProp` conjunct
  is what needs `LvlEqCacheOK`, and this walk never looks at it.  What it
  needs from that tier is an `isSome`-only lemma at `StateOK`, named in the
  `sorry` below.)

`sorry`: `projRecCandidates_run` (the `filterMap`, a list induction over
`findCtorRec_run` / `findRecRec_run`), then the reordering argument — a
`cases` on the candidate list with the empty arm closing by `rfl` on both
sides — and the two recognisers' `isSome` exactness AT `StateOK`, which
belongs to the Inductives tier (`Arena/Inductives/StructParts.lean`,
`NativeParts.lean`) and is imported here as a hypothesis-free call once that
tier states it.  Task #97-P3-Frontend's sorry list, item 13. -/
theorem projRecOwners_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {fuel : Nat} {block : List IConstantInfo}
    {blockP : List ConstantInfo} (hb : denoteCIList s.store block = some blockP)
    {types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)}
    {typesP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat ×
      List ConLeche.Name × Bool)}
    {ctors : List (NIdx × Nat × EIdx)}
    {ctorsP : List (ConLeche.Name × Nat × Expr)}
    {recs : List (NIdx × List NIdx × EIdx × Nat × Nat)}
    {recsP : List (ConLeche.Name × List ConLeche.Name × Expr × Nat × Nat)}
    (htys : ListRel (fun p q =>
      denoteN s.store.ns p.1 = some q.1 ∧
        denoteNList s.store.ns p.2.1 = some q.2.1 ∧
        denoteE s.store p.2.2.1 = some q.2.2.1 ∧
        p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧
        denoteNList s.store.ns p.2.2.2.2.2.1 = some q.2.2.2.2.2.1 ∧
        p.2.2.2.2.2.2 = q.2.2.2.2.2.2) types typesP)
    (hcts : ListRel (fun p q =>
      denoteN s.store.ns p.1 = some q.1 ∧ p.2.1 = q.2.1 ∧
        denoteE s.store p.2.2 = some q.2.2) ctors ctorsP)
    (hrcs : ListRel (fun p q =>
      denoteN s.store.ns p.1 = some q.1 ∧
        denoteNList s.store.ns p.2.1 = some q.2.1 ∧
        denoteE s.store p.2.2.1 = some q.2.2.1 ∧
        p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2 = q.2.2.2.2) recs recsP)
    {os : List ProjRecOwner}
    (hrun : projRecOwners fuel block types ctors recs s = .ok (os, s')) :
    ParseStep s s' ∧
      ListRel (ProjRecOwnerRel s'.store) os
        (ConLeche.Frontend.projRecOwners blockP typesP ctorsP recsP) := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:379-380 registerProjOwners — the
census, recorded in the parse state's two tables.

`sorry`: `projRecOwners_run` plus `MapRel.insert` at `projOwners`.  Task
#97-P3-Frontend's sorry list, item 13. -/
theorem registerProjOwners_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec}
    {rcs : List ConLeche.Frontend.IndRecRec} {block : List IConstantInfo}
    {blockP : List ConstantInfo} (hb : denoteCIList s.store block = some blockP)
    (hrun : registerProjOwners sd tys cts rcs block s = .ok (sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.registerProjOwners sc tys cts rcs blockP = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  sorry

end ConRon.Bridge.Frontend
