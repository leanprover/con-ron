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
import ConRon.Bridge.Frontend.Scratch
import ConRon.Bridge.ExprOps.Spine
import ConRon.Arena.Frontend.ProjRec

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The name and level helpers -/

/-- con-leche: none — `viewN` in run form, off `Bridge/Specs.lean`'s triple. -/
theorem viewN_run {s s' : AState} {h : NIdx} {v : NNodeView}
    (hrun : viewN h s = .ok (v, s')) : s' = s ∧ s.store.ns.view h = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewN_spec s h)

/-- con-leche: none — `view_run`: the store's own decoding, off
`Bridge/Specs.lean`'s triple.  `Bridge/Inductives/Rel.lean` has the same
four-line bridge; the frontend cone does not import it. -/
theorem view_run {s s' : AState} {h : EIdx} {v : ENodeView}
    (hrun : view h s = .ok (v, s')) : s' = s ∧ s.store.view h = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (view_spec s h)

/-- con-leche: none — `viewLs` in run form, off `Bridge/Specs.lean`'s
triple. -/
theorem viewLs_run {s s' : AState} {h : LsIdx} {v : LsNodeView}
    (hrun : viewLs h s = .ok (v, s')) : s' = s ∧ s.store.lss.view h = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewLs_spec s h)

/-- con-leche: none — `readLevel` in run form: the readback IS `denoteL`
(DESIGN §8.3 lesson 4). -/
theorem readLevel_run {s s' : AState} {h : LIdx} {u : Level}
    (hrun : readLevel h s = .ok (u, s')) :
    s' = s ∧ denoteL s.store.ls h = some u :=
  AM.of_run (P := fun t => t = s) rfl hrun (readLevel_spec s h)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1136-1140 piResult — the run form
of `Bridge/ExprOps/Spine.lean`'s closed `piResult_spec`. -/
theorem piResult_run {fuel : Nat} {s s' : AState} {h r : EIdx} {e : Expr}
    (hok : StateOK s) (hd : denoteE s.store h = some e)
    (hrun : ConRon.Arena.piResult fuel h s = .ok (r, s')) :
    s' = s ∧ denoteE s.store r = some e.piResult := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s) rfl hrun
    (ExprOps.piResult_spec fuel s h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 e hd⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn — the run form of
`Bridge/ExprOps/Spine.lean`'s closed `getAppFn_spec`. -/
theorem getAppFn_run {fuel : Nat} {s s' : AState} {h r : EIdx} {e : Expr}
    (hok : StateOK s) (hd : denoteE s.store h = some e)
    (hrun : ConRon.Arena.getAppFn fuel h s = .ok (r, s')) :
    s' = s ∧ denoteE s.store r = some e.getAppFn := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s) rfl hrun
    (ExprOps.getAppFn_spec fuel s h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 e hd⟩

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

/-- con-leche: none — the name-side counterpart of `Bridge/Rel.lean`'s
denote-inversion layer, at the one constructor this module reads: a handle
whose view is `.str p t` denotes `.str q t` with `p` denoting `q`.  `Arena/
WFProofs.lean` has the two halves (`denoteN_unfold`, `denoteNView_str`); this
is the composition every `viewN` branch of the recogniser wants. -/
theorem denoteN_str_inv {st : NStore} {rk : NIdx → Nat} (hw : Arena.NWFAt st rk)
    {i p : NIdx} {t : String} (hv : st.view i = some (.str p t))
    {x : ConLeche.Name} (hd : denoteN st i = some x) :
    ∃ q, x = .str q t ∧ denoteN st p = some q := by
  rw [denoteN_unfold hw hv, denoteNView, Option.map_eq_some_iff] at hd
  obtain ⟨q, hq, hx⟩ := hd
  exact ⟨q, hx.symm, hq⟩

/-- con-leche: none — the same inversion the other way round: the DENOTED name
is a `.str`, so the handle's view is, whatever the view was known to be.
`Arena/WFProofs.lean`'s `denoteNView_str` under `denoteN_unfold`. -/
theorem view_str_of_denoteN {st : NStore} {rk : NIdx → Nat}
    (hw : Arena.NWFAt st rk) {i : NIdx} {v : NNodeView}
    (hv : st.view i = some v) {q : ConLeche.Name} {t : String}
    (hd : denoteN st i = some (.str q t)) :
    ∃ p, v = .str p t ∧ denoteN st p = some q := by
  rw [denoteN_unfold hw hv] at hd
  exact denoteNView_str hd

/-- con-leche: ConLeche/Frontend/ProjRec.lean:116 isProjIotaName — the
recogniser's `false` half, on con-leche's side alone: a name that is not
`X._model.s.iota` is not recognised.  The twin descends tail component first
and bails at three different places, so the three negative branches all land
here. -/
theorem clIsProjIotaName_false {nP : ConLeche.Name}
    (h : ∀ (q : ConLeche.Name) (t : String),
      nP ≠ ((q.str "_model").str t).str "iota") :
    ConLeche.Frontend.isProjIotaName nP = false := by
  rw [ConLeche.Frontend.isProjIotaName]
  intro q t he
  exact h q t he

/-- con-leche: ConLeche/Frontend/ProjRec.lean:116 isProjIotaName — the
recogniser, which reads the name back and runs con-leche's own test.

Three `viewN`s against con-leche's one nested pattern.  The twin descends
tail-component first (the last component decides, which is the module note's
"cheap pre-filter"), so the theorem is three `denoteN_str_inv`s and then
`cases` on the denoted parent: the shapes con-leche's pattern does **not**
match are exactly the views the twin answers `false` at. -/
theorem isProjIotaName_run {s s' : AState} (hok : StateOK s) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN s.store.ns n = some nP) {b : Bool}
    (hrun : isProjIotaName n s = .ok (b, s')) :
    s' = s ∧ b = ConLeche.Frontend.isProjIotaName nP := by
  obtain ⟨rk, hw⟩ := nsWF_of_StateOK hok
  rw [ConRon.Arena.Frontend.isProjIotaName] at hrun
  obtain ⟨v, s₁, hv1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hview1⟩ := viewN_run hv1
  split at hrest
  · -- the tail component IS `"iota"`
    rename_i p1
    obtain ⟨v2, s₂, hv2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨rfl, hview2⟩ := viewN_run hv2
    obtain ⟨q1, rfl, hq1⟩ := denoteN_str_inv hw hview1 hn
    split at hrest2
    · -- the middle component is a `.str`
      rename_i p2 t2
      obtain ⟨v3, s₃, hv3, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨rfl, hview3⟩ := viewN_run hv3
      obtain ⟨q2, rfl, hq2⟩ := denoteN_str_inv hw hview2 hq1
      split at hrest3
      · -- and the head component IS `"_model"`: both sides answer the prefix test
        rename_i p3
        obtain ⟨q3, rfl, -⟩ := denoteN_str_inv hw hview3 hq2
        obtain ⟨hb, hs⟩ := AM.pure_ok hrest3
        subst hb; subst hs
        exact ⟨rfl, rfl⟩
      · rename_i hne
        obtain ⟨hb, hs⟩ := AM.pure_ok hrest3
        subst hb; subst hs
        refine ⟨rfl, (clIsProjIotaName_false ?_).symm⟩
        rintro q t he
        have hq : q2 = q.str "_model" := by
          injection he with h1 h2
          injection h1 with h3 h4
        subst hq
        obtain ⟨p, rfl, -⟩ := view_str_of_denoteN hw hview3 hq2
        exact hne p rfl
    · rename_i hne
      obtain ⟨hb, hs⟩ := AM.pure_ok hrest2
      subst hb; subst hs
      refine ⟨rfl, (clIsProjIotaName_false ?_).symm⟩
      rintro q t he
      have hq : q1 = (q.str "_model").str t := by
        injection he with h1 h2
      subst hq
      obtain ⟨p, rfl, -⟩ := view_str_of_denoteN hw hview2 hq1
      exact hne p t rfl
  · rename_i hne
    obtain ⟨hb, hs⟩ := AM.pure_ok hrest
    subst hb; subst hs
    refine ⟨rfl, (clIsProjIotaName_false ?_).symm⟩
    rintro q t he
    subst he
    obtain ⟨p, rfl, -⟩ := view_str_of_denoteN hw hview1 hn
    exact hne p rfl

/-- con-leche: none — the length of a level-handle list is the length of its
denotation, which is all `projIotaLevel`'s singleton guard reads of it. -/
theorem denoteLList_length {st : LStore} :
    ∀ {vs : List LIdx} {xs : List Level},
      denoteLList st vs = some xs → vs.length = xs.length := by
  intro vs
  induction vs with
  | nil =>
    intro xs h
    obtain rfl : xs = [] := (Option.some.inj h).symm
    rfl
  | cons a as ih =>
    intro xs h
    rw [denoteLList, opt2_eq_some_iff] at h
    obtain ⟨u, us, -, hus, rfl⟩ := h
    simp only [List.length_cons, ih hus]

/-- con-leche: none — a SINGLETON level-handle list denotes a singleton, which
is what `projIotaLevel`'s universe-argument guard asks. -/
theorem denoteLList_singleton {st : LStore} {l : LIdx} {xs : List Level}
    (h : denoteLList st [l] = some xs) :
    ∃ u, denoteL st l = some u ∧ xs = [u] := by
  rw [denoteLList, denoteLList, opt2_eq_some_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  exact ⟨x, hx, by rw [← hxy, ← Option.some.inj hy]⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel — the
definition as ONE match on the head of the result's application spine, so a
proof that knows that head by an equation can rewrite it in and reduce.  `rfl`;
it exists because `rw` at the recursor's own equations picks the fallback
clause and leaves its side condition. -/
theorem clProjIotaLevel_eq (e : Expr) :
    ConLeche.Frontend.projIotaLevel e =
      match e.piResult.getAppFn with
      | .const n [l] => if n == ConLeche.eqName then some l else none
      | _ => none := rfl

/-- con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel — the
walk's `none` arms, once: the state does not move and both sides answer
`none`. -/
theorem projIotaLevel_none {s s' : AState} (hok : StateOK s) {o : Option LIdx}
    {e : Expr} (hrest : (pure none : AM (Option LIdx)) s = .ok (o, s'))
    (hcl : ConLeche.Frontend.projIotaLevel e = none) :
    ParseStep s s' ∧ (∀ l, o = some l → PersL l) ∧
      OptRel (fun (l : LIdx) (u : Level) => denoteL s'.store.ls l = some u) o
        (ConLeche.Frontend.projIotaLevel e) := by
  obtain ⟨hv, hs⟩ := AM.pure_ok hrest
  subst hv; subst hs
  exact ⟨ParseStep.refl hok, by intro l hl; exact absurd hl (by simp),
    by rw [hcl]; exact OptRel.refl_none⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:122 projIotaLevel — the field's
sort, off the iota artifact's type.

**Round 4's finding 15 — the frame was too strong to be true.**  Round 1 said
`s' = s`, and the walk's last step is `internName ConLeche.eqName`: the twin
SPEAKS the name `Eq` in order to compare the head constant against it, and
speaking a name means interning it (`Arena/Frontend/ProjRec.lean`'s module
note, third bullet).  On a store that does not already hold `Eq` the run
extends the arena, so `s' = s` is not true of it.  The honest frame is
`ParseStep`, which is what the one consumer (`noteProjIota`,
`Arena/Frontend/ExportC.lean:325-334`) can carry: it inserts the answer into
`StateD.projLevels`, whose relation is read at the state the step LEAVES.

The answer is stated as an `OptRel` and **not** as the accept direction alone,
because `projLevels` is a `MapRel` and `MapRel`'s `cover` clause reads the
`none` case: a level con-leche registers and the twin does not would break it.
That is the one place in this module where `denoteN_inj` (DESIGN §8.3's
exactness obligation) is load-bearing — the twin compares HANDLES where
con-leche compares names, and only injectivity rules out a twin miss at a
con-leche hit.

`piResult_run` and `getAppFn_run` are read-only (`Bridge/ExprOps/Spine.lean`),
and the level is a handle the walk was already holding, so no level algorithm
is related at all (DESIGN §8.3 lesson 4). -/
theorem projIotaLevel_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {fuel : Nat}
    {ty : EIdx} {tyP : Expr} (hty : denoteE s.store ty = some tyP)
    {o : Option LIdx} (hrun : projIotaLevel fuel ty s = .ok (o, s')) :
    ParseStep s s' ∧ (∀ l, o = some l → PersL l) ∧
      OptRel (fun (l : LIdx) (u : Level) => denoteL s'.store.ls l = some u) o
        (ConLeche.Frontend.projIotaLevel tyP) := by
  have hwf : StoreWF s.store := hok.wf
  rw [ConRon.Arena.Frontend.projIotaLevel] at hrun
  obtain ⟨r, s₁, hpi, hrest⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hdr⟩ := piResult_run hok hty hpi
  obtain ⟨f, s₂, hgf, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨rfl, hdf⟩ := getAppFn_run hok hdr hgf
  obtain ⟨v, s₃, hv, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨rfl, hview⟩ := view_run hv
  match v, hview with
  | .const n us, hview =>
    obtain ⟨nm, ls, hcl, hdn, hdls⟩ := denote_const_inv hwf hview hdf
    obtain ⟨vs, s₄, hvls, hrest4⟩ := AM.bind_ok hrest3
    obtain ⟨rfl, hviewls⟩ := viewLs_run hvls
    have hdll := hdls
    simp only [denoteLs, hviewls] at hdll
    match vs, hdll with
    | [l], hdll =>
      -- the singleton: the twin compares HANDLES where con-leche compares names
      obtain ⟨u, hdu, rfl⟩ := denoteLList_singleton hdll
      obtain ⟨eqH, s₅, hin, hrest5⟩ := AM.bind_ok hrest4
      obtain ⟨histep, -, hdeq⟩ := internName_istep hok hoff hin
      obtain ⟨hvv, hss⟩ := AM.pure_ok hrest5
      subst hss
      by_cases hn : n = eqH
      · -- the handles agree, so the names do
        subst hn
        have hnm : nm = ConLeche.eqName :=
          Option.some.inj ((denoteN_ext hdn histep.ext).symm.trans hdeq)
        subst hnm
        simp only [beq_self_eq_true, if_true] at hvv
        subst hvv
        refine ⟨histep.toParse hoff, ?_, ?_⟩
        · intro l' hl'
          obtain rfl : l' = l := (Option.some.inj hl').symm
          obtain ⟨w, hw⟩ := Arena.denoteL_view hdu
          exact PersL_of_view hwf hoff hw
        · rw [clProjIotaLevel_eq, hcl]
          simp only [beq_self_eq_true, if_true]
          exact denoteL_ext hdu histep.ext
      · -- the handles differ, so the names do — **`denoteN_inj`**
        have hnm : nm ≠ ConLeche.eqName := by
          intro hcon
          subst hcon
          exact hn (Arena.denoteN_inj (nsWF_of_StateOK histep.ok)
            (denoteN_ext hdn histep.ext) hdeq)
        rw [if_neg (by simpa using hn)] at hvv
        subst hvv
        refine ⟨histep.toParse hoff,
          by intro l' hl'; exact absurd hl' (by simp), ?_⟩
        rw [clProjIotaLevel_eq, hcl]
        simp only [beq_iff_eq, hnm, if_false]
        exact OptRel.refl_none
    | [], hdll =>
      rw [denoteLList] at hdll
      obtain rfl : ls = [] := (Option.some.inj hdll).symm
      exact projIotaLevel_none hok hrest4 (by rw [clProjIotaLevel_eq, hcl])
    | a :: b :: t, hdll =>
      obtain ⟨x, y, z, rfl⟩ : ∃ x y z, ls = x :: y :: z := by
        have hlen := denoteLList_length hdll
        match ls, hlen with
        | x :: y :: z, _ => exact ⟨x, y, z, rfl⟩
      exact projIotaLevel_none hok hrest4 (by rw [clProjIotaLevel_eq, hcl])
  | .bvar i, hview =>
    exact projIotaLevel_none hok hrest3
      (by rw [clProjIotaLevel_eq, denote_bvar_inv hwf hview hdf])
  | .fvar k t, hview =>
    obtain ⟨_, hs, -⟩ := denote_fvar_inv hwf hview hdf
    exact projIotaLevel_none hok hrest3 (by rw [clProjIotaLevel_eq, hs])
  | .sort u, hview =>
    obtain ⟨_, hs, -⟩ := denote_sort_inv hwf hview hdf
    exact projIotaLevel_none hok hrest3 (by rw [clProjIotaLevel_eq, hs])
  | .lit l, hview =>
    exact projIotaLevel_none hok hrest3
      (by rw [clProjIotaLevel_eq, denote_lit_inv hwf hview hdf])
  | .app g a, hview =>
    obtain ⟨_, _, hs, -, -⟩ := denote_app_inv hwf hview hdf
    exact projIotaLevel_none hok hrest3 (by rw [clProjIotaLevel_eq, hs])
  | .lam t bd m, hview =>
    obtain ⟨_, _, hs, -, -⟩ := denote_lam_inv hwf hview hdf
    exact projIotaLevel_none hok hrest3 (by rw [clProjIotaLevel_eq, hs])
  | .forallE t bd m, hview =>
    obtain ⟨_, _, hs, -, -⟩ := denote_forallE_inv hwf hview hdf
    exact projIotaLevel_none hok hrest3 (by rw [clProjIotaLevel_eq, hs])
  | .letE t w bd, hview =>
    obtain ⟨_, _, _, hs, -, -, -⟩ := denote_letE_inv hwf hview hdf
    exact projIotaLevel_none hok hrest3 (by rw [clProjIotaLevel_eq, hs])
  | .proj nn i sub, hview =>
    obtain ⟨_, _, hs, -, -⟩ := denote_proj_inv hwf hview hdf
    exact projIotaLevel_none hok hrest3 (by rw [clProjIotaLevel_eq, hs])

/-! ## The term walks -/


/-! ### Two con-leche-tier facts con-leche does not have

`ConLeche/Verify/` mentions neither `occursConstB` nor `occursConstGo`: the
budgeted and the memoised walks are UNVERIFIED on con-leche's side, and the
pure `occursConst` (`ConLeche/Frontend/ProjRec.lean:129-136`) is their only
specification — con-leche's own note says so (*"`occursConst` has exactly one
caller and no proof depends on it, so the memoised walk is simply what that
caller uses; the pure definition above stays as its specification"*).

The twin's `occursConstFast` is stated against `ConLeche.Frontend.
occursConstFast`, so this tier needs the two, and they belong beside
`occursConst` in con-leche rather than here.  They are stated here in task
#97-P3-Frontend §5's **finding 6** shape — a con-leche-tier lemma stated in
this tier so the gap is a LEMMA and not a hole in a proof — exactly as
`checkDeclsPure_thmDecl_const` is in `Bridge/Frontend/Capstone.lean`. -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:152-178 occursConstB — **the
budgeted descent answers `occursConst` whenever it answers at all.**

`sorry`: a con-leche-tier lemma (finding 6's shape).  A structural induction on
the `Expr` with the budget generalised; the `some false` arms compose and every
`none` arm is vacuous.  It belongs in `ConLeche/Verify/Frontend/ProjRec.lean`
beside `occursConst`, and this tier may not re-derive con-leche's own
functions. -/
theorem clOccursConstB_eq {n : ConLeche.Name} :
    ∀ {fuel : Nat} {e : ConLeche.Expr} {r : Bool},
      (ConLeche.Frontend.occursConstB n fuel e).1 = some r →
      r = ConLeche.Frontend.occursConst n e := by
  sorry

/-- con-leche: ConLeche/Frontend/ProjRec.lean:182-227 occursConstGo — **the
memoised descent answers `occursConst` at a fresh set.**

`sorry`: a con-leche-tier lemma (finding 6's shape).  The induction needs the
set's invariant — *every member is a subterm already shown not to mention `n`*
— which is the GRAY shape, and `∅` is where it starts true.  Same home as
`clOccursConstB_eq`. -/
theorem clOccursConstGo_eq {n : ConLeche.Name} {e : ConLeche.Expr} :
    (ConLeche.Frontend.occursConstGo n ∅ e).1
      = ConLeche.Frontend.occursConst n e := by
  sorry

/-- con-leche: ConLeche/Frontend/ProjRec.lean:228-231 occursConstFast — **what
the twin is stated against is the pure `occursConst`**, which is the only
thing this tier ever has to reason about once the two above are in hand. -/
theorem clOccursConstFast_eq {n : ConLeche.Name} {e : ConLeche.Expr} :
    ConLeche.Frontend.occursConstFast n e = ConLeche.Frontend.occursConst n e := by
  rw [ConLeche.Frontend.occursConstFast]
  cases h : (ConLeche.Frontend.occursConstB n 4096 e).1 with
  | none => exact clOccursConstGo_eq
  | some r => exact clOccursConstB_eq h

/-! ### The occurrence walk's memo, and why it is NOT gray

`occursConstGo`'s `seen` is a **black-only** memo: the twin inserts a node only
once every child has answered `false` (`Arena/Frontend/ProjRec.lean:148-187` —
the `seen.insert h` is in the all-`false` branch and nowhere else), so a key of
the set is a handle whose subtree is ALREADY known not to mention the name.
Nothing is ever marked on the way down.

That is the whole difference from `Bridge/ExprOps/Leaves.lean`'s
`fvarLeavesGo`, which marks a node BEFORE descending and therefore needs the
gray disjunct and `StoreWF`'s rank to say what a gray key is.  Round 5's note
here called this walk the same gray shape; **it is not**, and that is why the
induction below is a plain fuel induction with one invariant, no rank and no
second parameter.  DESIGN #97-P3-Frontend round 6. -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:182-227 occursConstGo — the
memo's invariant: every key denotes a term that does not mention `nP`. -/
def OccSeen (st : EStore) (nP : ConLeche.Name) (seen : Std.HashSet EIdx) : Prop :=
  ∀ k, seen.contains k = true → ∀ e, denoteE st k = some e →
    ConLeche.Frontend.occursConst nP e = false

/-- con-leche: none — the walk starts at the empty set. -/
theorem OccSeen.empty {st : EStore} {nP : ConLeche.Name} :
    OccSeen st nP (∅ : Std.HashSet EIdx) := by
  intro k hk; simp at hk

/-- con-leche: none — a node joins the memo once its children have all said
no, which is the only place the twin inserts. -/
theorem OccSeen.insert {st : EStore} {nP : ConLeche.Name}
    {seen : Std.HashSet EIdx} {h : EIdx} {e : Expr}
    (hs : OccSeen st nP seen) (he : denoteE st h = some e)
    (hb : ConLeche.Frontend.occursConst nP e = false) :
    OccSeen st nP (seen.insert h) := by
  intro k hk e' he'
  rw [Std.HashSet.contains_insert] at hk
  rcases Bool.or_eq_true .. |>.mp hk with hk1 | hk2
  · have hhk : h = k := eq_of_beq hk1
    subst hhk
    obtain rfl : e = e' := Option.some.inj (he.symm.trans he')
    exact hb
  · exact hs k hk2 e' he'

/-- con-leche: none — the six views the walk answers `false` at outright
(`bvar`, `fvar`, `sort`, `lit`), and the memo HIT.  con-leche's `occursConst`
falls through to its catch-all at each of the four. -/
theorem occSeen_stop {s s' : AState} {seen seen' : Std.HashSet EIdx}
    {b : Bool} (hrest : (pure (false, seen) : AM (Bool × Std.HashSet EIdx)) s
      = .ok ((b, seen'), s')) : s' = s ∧ b = false ∧ seen' = seen := by
  obtain ⟨hv, hs⟩ := AM.pure_ok hrest
  injection hv with e1 e2
  exact ⟨hs, e1, e2⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:182-227 occursConstGo — **the
arena side of the memoised occurrence test**: the twin's walk over handles
answers con-leche's pure `occursConst` over the denoted tree, and hands back a
memo that still says only true things.

A fuel induction, ten arms, the inversion layer of `Bridge/Rel.lean` read once
each.  The `const` arm is the only one that compares anything, and it is exact
in BOTH directions: a handle equality gives a name equality because `denoteN`
is a function, and a name equality gives a handle equality because `denoteN` is
INJECTIVE (DESIGN §8.3's soundness obligation).  Read-only: no intern, so the
state does not move. -/
theorem occursConstGo_run {s : AState} (hok : StateOK s) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN s.store.ns n = some nP) :
    ∀ (fuel : Nat) {seen seen' : Std.HashSet EIdx} {h : EIdx} {e : Expr}
      {b : Bool} {s' : AState}, OccSeen s.store nP seen →
      denoteE s.store h = some e →
      occursConstGo n seen fuel h s = .ok ((b, seen'), s') →
      s' = s ∧ b = ConLeche.Frontend.occursConst nP e ∧
        OccSeen s.store nP seen' := by
  have hwf : StoreWF s.store := hok.wf
  intro fuel
  induction fuel with
  | zero =>
    intro seen seen' h e b s' _ _ hrun
    rw [ConRon.Arena.Frontend.occursConstGo] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro seen seen' h e b s' hseen he hrun
    rw [ConRon.Arena.Frontend.occursConstGo] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hview⟩ := view_run hv
    match v, hview with
    | .const m us, hview =>
      obtain ⟨mP, ls, rfl, hm, -⟩ := denote_const_inv hwf hview he
      simp only [] at hrest
      obtain ⟨hvv, hs⟩ := AM.pure_ok hrest
      subst hs
      injection hvv with e1 e2
      subst e1; subst e2
      refine ⟨rfl, ?_, hseen⟩
      rw [ConLeche.Frontend.occursConst]
      by_cases hmn : m = n
      · subst hmn
        rw [hm] at hn
        obtain rfl := Option.some.inj hn
        simp
      · have hne : mP ≠ nP := by
          intro heq
          subst heq
          exact hmn (Arena.denoteN_inj (nsWF_of_StateOK hok) hm hn)
        rw [beq_eq_false_iff_ne.mpr hmn, beq_eq_false_iff_ne.mpr hne]
    | .bvar i, hview =>
      obtain rfl := denote_bvar_inv hwf hview he
      simp only [] at hrest
      obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
      exact ⟨hs, rfl, hseen⟩
    | .fvar k ty, hview =>
      obtain ⟨t, rfl, -⟩ := denote_fvar_inv hwf hview he
      simp only [] at hrest
      obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
      exact ⟨hs, rfl, hseen⟩
    | .sort u, hview =>
      obtain ⟨l, rfl, -⟩ := denote_sort_inv hwf hview he
      simp only [] at hrest
      obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
      exact ⟨hs, rfl, hseen⟩
    | .lit l, hview =>
      obtain rfl := denote_lit_inv hwf hview he
      simp only [] at hrest
      obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
      exact ⟨hs, rfl, hseen⟩
    | .app f a, hview =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hview he
      simp only [] at hrest
      by_cases hc : seen.contains h = true
      · rw [if_pos hc] at hrest
        obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
        exact ⟨hs, (hseen h hc _ he).symm, hseen⟩
      · rw [if_neg hc] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨b1, sn1⟩ := p1
        obtain ⟨rfl, hb1, hs1⟩ := ih hseen hf hg1
        cases b1 with
        | true =>
          simp only [] at hr1
          obtain ⟨hvv, hs⟩ := AM.pure_ok hr1
          subst hs; injection hvv with e1 e2; subst e1; subst e2
          exact ⟨rfl, by rw [ConLeche.Frontend.occursConst, ← hb1]; simp, hs1⟩
        | false =>
          simp only [] at hr1
          obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
          obtain ⟨b2, sn2⟩ := p2
          obtain ⟨rfl, hb2, hs2⟩ := ih hs1 ha hg2
          cases b2 with
          | true =>
            simp only [] at hr2
            obtain ⟨hvv, hs⟩ := AM.pure_ok hr2
            subst hs; injection hvv with e1 e2; subst e1; subst e2
            exact ⟨rfl, by
              rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2]; simp, hs2⟩
          | false =>
            simp only [] at hr2
            obtain ⟨hvv, hs⟩ := AM.pure_ok hr2
            subst hs; injection hvv with e1 e2; subst e1; subst e2
            have hz : ConLeche.Frontend.occursConst nP (Expr.app ef ea) = false := by
              rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2]; simp
            exact ⟨rfl, hz.symm, hs2.insert he hz⟩
    | .lam ty body mt, hview =>
      obtain ⟨et, eb, rfl, hf, ha⟩ := denote_lam_inv hwf hview he
      simp only [] at hrest
      by_cases hc : seen.contains h = true
      · rw [if_pos hc] at hrest
        obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
        exact ⟨hs, (hseen h hc _ he).symm, hseen⟩
      · rw [if_neg hc] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨b1, sn1⟩ := p1
        obtain ⟨rfl, hb1, hs1⟩ := ih hseen hf hg1
        cases b1 with
        | true =>
          simp only [] at hr1
          obtain ⟨hvv, hs⟩ := AM.pure_ok hr1
          subst hs; injection hvv with e1 e2; subst e1; subst e2
          exact ⟨rfl, by rw [ConLeche.Frontend.occursConst, ← hb1]; simp, hs1⟩
        | false =>
          simp only [] at hr1
          obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
          obtain ⟨b2, sn2⟩ := p2
          obtain ⟨rfl, hb2, hs2⟩ := ih hs1 ha hg2
          cases b2 with
          | true =>
            simp only [] at hr2
            obtain ⟨hvv, hs⟩ := AM.pure_ok hr2
            subst hs; injection hvv with e1 e2; subst e1; subst e2
            exact ⟨rfl, by
              rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2]; simp, hs2⟩
          | false =>
            simp only [] at hr2
            obtain ⟨hvv, hs⟩ := AM.pure_ok hr2
            subst hs; injection hvv with e1 e2; subst e1; subst e2
            have hz : ConLeche.Frontend.occursConst nP (Expr.lam et eb mt)
                = false := by
              rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2]; simp
            exact ⟨rfl, hz.symm, hs2.insert he hz⟩
    | .forallE ty body mt, hview =>
      obtain ⟨et, eb, rfl, hf, ha⟩ := denote_forallE_inv hwf hview he
      simp only [] at hrest
      by_cases hc : seen.contains h = true
      · rw [if_pos hc] at hrest
        obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
        exact ⟨hs, (hseen h hc _ he).symm, hseen⟩
      · rw [if_neg hc] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨b1, sn1⟩ := p1
        obtain ⟨rfl, hb1, hs1⟩ := ih hseen hf hg1
        cases b1 with
        | true =>
          simp only [] at hr1
          obtain ⟨hvv, hs⟩ := AM.pure_ok hr1
          subst hs; injection hvv with e1 e2; subst e1; subst e2
          exact ⟨rfl, by rw [ConLeche.Frontend.occursConst, ← hb1]; simp, hs1⟩
        | false =>
          simp only [] at hr1
          obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
          obtain ⟨b2, sn2⟩ := p2
          obtain ⟨rfl, hb2, hs2⟩ := ih hs1 ha hg2
          cases b2 with
          | true =>
            simp only [] at hr2
            obtain ⟨hvv, hs⟩ := AM.pure_ok hr2
            subst hs; injection hvv with e1 e2; subst e1; subst e2
            exact ⟨rfl, by
              rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2]; simp, hs2⟩
          | false =>
            simp only [] at hr2
            obtain ⟨hvv, hs⟩ := AM.pure_ok hr2
            subst hs; injection hvv with e1 e2; subst e1; subst e2
            have hz : ConLeche.Frontend.occursConst nP (Expr.forallE et eb mt)
                = false := by
              rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2]; simp
            exact ⟨rfl, hz.symm, hs2.insert he hz⟩
    | .letE ty w body, hview =>
      obtain ⟨et, ew, eb, rfl, h1d, h2d, h3d⟩ := denote_letE_inv hwf hview he
      simp only [] at hrest
      by_cases hc : seen.contains h = true
      · rw [if_pos hc] at hrest
        obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
        exact ⟨hs, (hseen h hc _ he).symm, hseen⟩
      · rw [if_neg hc] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨b1, sn1⟩ := p1
        obtain ⟨rfl, hb1, hs1⟩ := ih hseen h1d hg1
        cases b1 with
        | true =>
          simp only [] at hr1
          obtain ⟨hvv, hs⟩ := AM.pure_ok hr1
          subst hs; injection hvv with e1 e2; subst e1; subst e2
          exact ⟨rfl, by rw [ConLeche.Frontend.occursConst, ← hb1]; simp, hs1⟩
        | false =>
          simp only [] at hr1
          obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
          obtain ⟨b2, sn2⟩ := p2
          obtain ⟨rfl, hb2, hs2⟩ := ih hs1 h2d hg2
          cases b2 with
          | true =>
            simp only [] at hr2
            obtain ⟨hvv, hs⟩ := AM.pure_ok hr2
            subst hs; injection hvv with e1 e2; subst e1; subst e2
            exact ⟨rfl, by
              rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2]; simp, hs2⟩
          | false =>
            simp only [] at hr2
            obtain ⟨p3, s₄, hg3, hr3⟩ := AM.bind_ok hr2
            obtain ⟨b3, sn3⟩ := p3
            obtain ⟨rfl, hb3, hs3⟩ := ih hs2 h3d hg3
            cases b3 with
            | true =>
              simp only [] at hr3
              obtain ⟨hvv, hs⟩ := AM.pure_ok hr3
              subst hs; injection hvv with e1 e2; subst e1; subst e2
              exact ⟨rfl, by
                rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2, ← hb3]; simp,
                hs3⟩
            | false =>
              simp only [] at hr3
              obtain ⟨hvv, hs⟩ := AM.pure_ok hr3
              subst hs; injection hvv with e1 e2; subst e1; subst e2
              have hz : ConLeche.Frontend.occursConst nP (Expr.letE et ew eb)
                  = false := by
                rw [ConLeche.Frontend.occursConst, ← hb1, ← hb2, ← hb3]; simp
              exact ⟨rfl, hz.symm, hs3.insert he hz⟩
    | .proj nn i sub, hview =>
      obtain ⟨nm, es, rfl, -, hsub⟩ := denote_proj_inv hwf hview he
      simp only [] at hrest
      by_cases hc : seen.contains h = true
      · rw [if_pos hc] at hrest
        obtain ⟨hs, rfl, rfl⟩ := occSeen_stop hrest
        exact ⟨hs, (hseen h hc _ he).symm, hseen⟩
      · rw [if_neg hc] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨b1, sn1⟩ := p1
        obtain ⟨rfl, hb1, hs1⟩ := ih hseen hsub hg1
        cases b1 with
        | true =>
          simp only [] at hr1
          obtain ⟨hvv, hs⟩ := AM.pure_ok hr1
          subst hs; injection hvv with e1 e2; subst e1; subst e2
          exact ⟨rfl, by rw [ConLeche.Frontend.occursConst, ← hb1], hs1⟩
        | false =>
          simp only [] at hr1
          obtain ⟨hvv, hs⟩ := AM.pure_ok hr1
          subst hs; injection hvv with e1 e2; subst e1; subst e2
          have hz : ConLeche.Frontend.occursConst nP (Expr.proj nm i es)
              = false := by
            rw [ConLeche.Frontend.occursConst, ← hb1]
          exact ⟨rfl, hz.symm, hs1.insert he hz⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:228 occursConstFast — the
memoised occurrence test.  A `Bool` answer names no handle, so task
#97-P3-0 §5's finding 1 applies: this is a `RelV` and the closer takes every
arm.

**CLOSED** (round 6).  Round 5's two con-leche-tier lemmas put the con-leche
side at the pure `occursConst` (`clOccursConstFast_eq`), and the arena side is
`occursConstGo_run` above — a plain fuel induction, because the memo is
black-only and there is no gray phase to account for.  What remains under this
theorem is the two con-leche-tier `sorry`s and nothing of this tier's. -/
theorem occursConstFast_run {s s' : AState} (hok : StateOK s) {fuel : Nat}
    {n : NIdx} {nP : ConLeche.Name} (hn : denoteN s.store.ns n = some nP)
    {h : EIdx} {e : Expr} (he : denoteE s.store h = some e) {b : Bool}
    (hrun : occursConstFast fuel n h s = .ok (b, s')) :
    s' = s ∧ b = ConLeche.Frontend.occursConstFast nP e := by
  rw [ConRon.Arena.Frontend.occursConstFast] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨b1, sn1⟩ := p
  obtain ⟨rfl, hb, -⟩ := occursConstGo_run hok hn fuel OccSeen.empty he hgo
  obtain ⟨hvv, hs⟩ := AM.pure_ok hrest
  subst hs
  exact ⟨rfl, by rw [hvv, hb, clOccursConstFast_eq]⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:241 stripPisAll — the walk's
STOP arm, once for the nine non-`forallE` constructors: the twin answers
`([], h)` and con-leche's catch-all answers `([], e)`. -/
theorem stripPisAll_stop {s s' : AState} {h b : EIdx} {e : Expr}
    {bs : List (EIdx × BinderMeta)}
    (hrest : (pure ([], h) : AM (List (EIdx × BinderMeta) × EIdx)) s
      = .ok ((bs, b), s'))
    (he : denoteE s.store h = some e)
    (hcl : ConLeche.Frontend.stripPisAll e = ([], e)) :
    s' = s ∧ ∃ bsP bP, ConLeche.Frontend.stripPisAll e = (bsP, bP) ∧
      ListRel (fun (p : EIdx × BinderMeta) (q : Expr × BinderMeta) =>
        denoteE s.store p.1 = some q.1 ∧ p.2 = q.2) bs bsP ∧
      denoteE s.store b = some bP := by
  obtain ⟨hv, hs⟩ := AM.pure_ok hrest
  subst hs
  obtain ⟨rfl, rfl⟩ : bs = [] ∧ b = h := by
    injection hv with e1 e2
    exact ⟨e1, e2⟩
  exact ⟨rfl, [], e, hcl, ListRel.nil, he⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:235 lamBody / :241 stripPisAll —
the two peels.  Read-only walks: no intern, so the state does not move.

A fuel induction in `Bridge/ExprOps/Spine.lean`'s shape.  The `forallE` arm is
the induction hypothesis at the body; the other nine arms are the ten-lemma
inversion layer of `Bridge/Rel.lean` read once each, and on each of them
con-leche's own `stripPisAll` is its catch-all clause — the two sides stop at
the same node because the view's constructor IS the denoted term's. -/
theorem stripPisAll_run {s : AState} (hok : StateOK s) :
    ∀ (fuel : Nat) {h : EIdx} {e : Expr} (_ : denoteE s.store h = some e)
      {bs : List (EIdx × BinderMeta)} {b : EIdx} {s' : AState}
      (_ : stripPisAll fuel h s = .ok ((bs, b), s')),
      s' = s ∧ ∃ bsP bP, ConLeche.Frontend.stripPisAll e = (bsP, bP) ∧
        ListRel (fun (p : EIdx × BinderMeta) (q : Expr × BinderMeta) =>
          denoteE s.store p.1 = some q.1 ∧ p.2 = q.2) bs bsP ∧
        denoteE s.store b = some bP := by
  have hwf : StoreWF s.store := hok.wf
  intro fuel
  induction fuel with
  | zero =>
    intro h e he bs b s' hrun
    rw [ConRon.Arena.Frontend.stripPisAll] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro h e he bs b s' hrun
    rw [ConRon.Arena.Frontend.stripPisAll] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hview⟩ := view_run hv
    match v, hview with
    | .forallE ty body m, hview =>
      obtain ⟨et, eb, rfl, hty, hb⟩ := denote_forallE_inv hwf hview he
      simp only [] at hrest
      obtain ⟨pr, s₂, hgo, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨tl, tb⟩ := pr
      obtain ⟨rfl, bsP, bP, hcl, hrel, hdb⟩ := ih hb hgo
      obtain ⟨hvv, hss⟩ := AM.pure_ok hrest2
      subst hss
      obtain ⟨rfl, rfl⟩ : bs = (ty, m) :: tl ∧ b = tb := by
        injection hvv with e1 e2
        exact ⟨e1, e2⟩
      exact ⟨rfl, (et, m) :: bsP, bP, by
        rw [ConLeche.Frontend.stripPisAll, hcl], ListRel.cons ⟨hty, rfl⟩ hrel, hdb⟩
    | .bvar i, hview =>
      obtain rfl := denote_bvar_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .fvar k ty, hview =>
      obtain ⟨t, rfl, -⟩ := denote_fvar_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .sort u, hview =>
      obtain ⟨l, rfl, -⟩ := denote_sort_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .const n us, hview =>
      obtain ⟨nm, ls, rfl, -, -⟩ := denote_const_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .lit l, hview =>
      obtain rfl := denote_lit_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .app f a, hview =>
      obtain ⟨ef, ea, rfl, -, -⟩ := denote_app_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .lam ty body m, hview =>
      obtain ⟨et, eb, rfl, -, -⟩ := denote_lam_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .letE ty w body, hview =>
      obtain ⟨et, ew, eb, rfl, -, -, -⟩ := denote_letE_inv hwf hview he
      exact stripPisAll_stop hrest he rfl
    | .proj n i sub, hview =>
      obtain ⟨nm, es, rfl, -, -⟩ := denote_proj_inv hwf hview he
      exact stripPisAll_stop hrest he rfl

/-- con-leche: ConLeche/Frontend/ProjRec.lean:248 mkLams — the rebuild, which
interns.

Structural on the binder list, right to left: con-leche's `foldr` builds the
same `.lam` spine, and each of the twin's `internE`s is one
`Bridge/Frontend/Shared.lean` `IStep` at the state the inner call left. -/
theorem mkLams_run {s : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {body : EIdx} {bodyP : Expr}
    (hb : denoteE s.store body = some bodyP) :
    ∀ {bs : List (EIdx × BinderMeta)} {bsP : List (Expr × BinderMeta)},
      ListRel (fun (p : EIdx × BinderMeta) (q : Expr × BinderMeta) =>
        denoteE s.store p.1 = some q.1 ∧ p.2 = q.2) bs bsP →
      ∀ {h : EIdx} {s' : AState}, mkLams bs body s = .ok (h, s') →
        ParseStep s s' ∧ PersE h ∧
          denoteE s'.store h = some (ConLeche.Frontend.mkLams bsP bodyP) := by
  intro bs bsP hbs
  induction hbs with
  | nil =>
    intro h s' hrun
    rw [ConRon.Arena.Frontend.mkLams] at hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrun
    subst hv; subst hs
    obtain ⟨w, hw⟩ := Arena.denoteE_view hb
    exact ⟨ParseStep.refl hok, PersE_of_view hok.wf hoff hw, hb⟩
  | @cons a q as bsq hab hrest ih =>
    obtain ⟨ty, m⟩ := a
    obtain ⟨et, m'⟩ := q
    obtain ⟨hty, rfl⟩ := hab
    intro h s' hrun
    rw [ConRon.Arena.Frontend.mkLams] at hrun
    obtain ⟨acc, s₁, hgo, hrest2⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, -, hdacc⟩ := ih hgo
    have hoff1 : s₁.store.scratchOn = false := by rw [hstep1.scratch, hoff]
    obtain ⟨histep, hpe, hden⟩ :=
      internE_istep hstep1.ok hoff1
        (viewOK_lam (by rw [denote_ext hty hstep1.ext]; rfl)
          (by rw [hdacc]; rfl)) hrest2
    refine ⟨hstep1.trans (histep.toParse hoff1), hpe, ?_⟩
    rw [hden]
    simp only [denoteEView, opt2_eq_some_iff]
    exact ⟨et, ConLeche.Frontend.mkLams bsq bodyP,
      denote_ext (denote_ext hty hstep1.ext) histep.ext,
      denote_ext hdacc histep.ext, rfl⟩

/-! ## The rewrite -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:233-237 lamBody — the body under
every leading `λ`, a read-only fuel walk. -/
theorem lamBody_run {s : AState} (hok : StateOK s) :
    ∀ (fuel : Nat) {h : EIdx} {e : Expr} (_ : denoteE s.store h = some e)
      {b : EIdx} {s' : AState} (_ : lamBody fuel h s = .ok (b, s')),
      s' = s ∧ denoteE s.store b = some (ConLeche.Frontend.lamBody e) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h e he b s' hrun
    rw [lamBody] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro h e he b s' hrun
    rw [lamBody] at hrun
    -- the twin tests the tag, then reads the binder projection, as the port
    -- does (task #97-T2-LOCKSTEP)
    by_cases ht : (h.tag == ETag.lam) = true
    · rw [if_pos ht] at hrun
      obtain ⟨o, s₁, ho, hrest⟩ := AM.bind_ok hrun
      obtain ⟨hs1, hvb⟩ := AM.of_run (P := fun t => t = s) rfl ho (viewBind_spec s h)
      subst hs1
      cases hoc : o with
      | none =>
        rw [hoc] at hrest
        exact absurd (AM.fail_ok hrest) (by simp)
      | some p =>
        obtain ⟨ty, body, m⟩ := p
        rw [hoc] at hrest hvb
        have hview := view_of_viewBind_tag_lam ht hvb.symm
        obtain ⟨et, eb, rfl, -, hb⟩ := denote_lam_inv hok.wf hview he
        obtain ⟨rfl, hdb⟩ := ih hb hrest
        exact ⟨rfl, hdb⟩
    · rw [if_neg ht] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨rfl, ?_⟩
      obtain ⟨v, hv, hne⟩ := not_lam_of_tag (by rw [he]; rfl) ht
      rw [he]
      cases e with
      | lam x y m =>
        rw [denoteE_view_eq hok.wf hv] at he
        cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
          Option.map_eq_some_iff]
      | _ => rfl

/-- con-leche: none — two handle lists that denote are equal exactly when
their denotations are (`denoteN_inj`). -/
theorem denoteNList_beq {st : NStore} (hw : NStoreWF st) :
    ∀ {a b : List NIdx} {aP bP : List ConLeche.Name},
      denoteNList st a = some aP → denoteNList st b = some bP → (a == b) = (aP == bP) := by
  intro a
  induction a with
  | nil =>
    intro b aP bP ha hb
    simp only [denoteNList, Option.some.injEq] at ha; subst ha
    cases b with
    | nil => simp only [denoteNList, Option.some.injEq] at hb; subst hb; rfl
    | cons y ys =>
      simp only [denoteNList] at hb
      cases h1 : denoteN st y <;> cases h2 : denoteNList st ys <;> rw [h1, h2] at hb <;>
        simp at hb
      subst hb; rfl
  | cons x xs ih =>
    intro b aP bP ha hb
    simp only [denoteNList] at ha
    cases hx : denoteN st x with
    | none => rw [hx] at ha; simp at ha
    | some xP =>
      cases hxs : denoteNList st xs with
      | none => rw [hx, hxs] at ha; simp at ha
      | some xsP =>
        rw [hx, hxs] at ha; obtain rfl := Option.some.inj ha
        cases b with
        | nil => simp only [denoteNList, Option.some.injEq] at hb; subst hb; rfl
        | cons y ys =>
          simp only [denoteNList] at hb
          cases hy : denoteN st y with
          | none => rw [hy] at hb; simp at hb
          | some yP =>
            cases hys : denoteNList st ys with
            | none => rw [hy, hys] at hb; simp at hb
            | some ysP =>
              rw [hy, hys] at hb; obtain rfl := Option.some.inj hb
              simp only [List.cons_beq_cons, ih hxs hys]
              congr 1
              by_cases hxy : x = y
              · subst hxy
                rw [Option.some.inj (hx.symm.trans hy)]; simp
              · have : xP ≠ yP := fun h => hxy (denoteN_inj hw hx (h ▸ hy))
                rw [beq_eq_false_iff_ne.mpr hxy, beq_eq_false_iff_ne.mpr this]

end ConRon.Bridge.Frontend
