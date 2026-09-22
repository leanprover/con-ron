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
    ParseStep s s' ∧ PersPreludeIx pre ∧ DeclsProjNamed s'.store pre.decls ∧
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
    refine ⟨hstep, hpers, hrel.projNamed, ⟨rc.decls⟩, ?_, hrel.decls⟩
    rw [ConLeche.Frontend.builtinPreludeE, ConLeche.Frontend.parseExportD, hcl]
    rfl

/-! ## The prelude's front -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:93 preludeKey — the name a
prelude record is looked up by.  The twin is monadic only for the
`.anonymous` fall-through.

**Round 4's finding 16, repaired (round 5).**  `IDeclaration.names`
(`Arena/Env.lean:262-266`) reads `IConstantInfo.name`, which at a `.projInfo`
is the STORED handle `tbl.tableName` — and `denoteProjTable` does not mention
`tableName`, so `denoteDecl st d = some dP` alone does NOT give
`denoteNList st.ns d.names = some dP.names`.  `DeclProjNamed`
(`Bridge/Frontend/Rel.lean`) is exactly the missing fact and `declNames_denote`
is the equation it buys; the records this is applied to carry it out of the
parse in `ParseResultRel.projNamed`.

`declNames_denote` at the head, and `internNNode_istep` for the `.anonymous`
fall-through — the one monadic step in the whole module. -/
theorem preludeKey_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {d : IDeclaration} {dP : Declaration}
    (hpn : DeclProjNamed s.store d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP) {n : NIdx}
    (hrun : preludeKey d s = .ok (n, s')) :
    ParseStep s s' ∧ PersN n ∧
      denoteN s'.store.ns n = some (ConLeche.Frontend.preludeKey dP) := by
  have hnames := declNames_denote hpn hd
  rw [preludeKey, ConLeche.Frontend.preludeKey] at *
  cases hl : d.names with
  | cons h hs =>
    rw [hl] at hnames
    simp only [ConRon.Arena.Frontend.denoteNList] at hnames
    cases hh : denoteN s.store.ns h with
    | none => rw [hh] at hnames; simp at hnames
    | some x =>
      cases hhs : ConRon.Arena.Frontend.denoteNList s.store.ns hs with
      | none => rw [hh, hhs] at hnames; simp at hnames
      | some xs =>
        rw [hh, hhs] at hnames
        simp only [Option.some.injEq] at hnames
        rw [hl] at hrun
        simp only [List.head?_cons] at hrun
        obtain ⟨hv, hst⟩ := AM.pure_ok hrun
        subst hv; subst hst
        obtain ⟨w, hw⟩ := Arena.denoteN_view hh
        refine ⟨ParseStep.refl hok, PersN_of_view hok.wf hoff hw, ?_⟩
        rw [← hnames]
        simpa using hh
  | nil =>
    rw [hl] at hnames
    simp only [ConRon.Arena.Frontend.denoteNList, Option.some.injEq] at hnames
    rw [hl] at hrun
    simp only [List.head?_nil] at hrun
    obtain ⟨hstep, hpn', hdn⟩ :=
      internNNode_istep hok hoff
        (by intro c hc; simp only [NNodeView.children] at hc; exact absurd hc (by simp))
        hrun
    refine ⟨hstep.toParse hoff, hpn', ?_⟩
    rw [hdn, ← hnames]
    rfl

/-! ### The three list facts `pick` reads

`pick` is an ARRAY function on both sides, but everything it does is a list
operation (`Array.findIdx` is `List.findIdx` of `toList`,
`Array.eraseIdxIfInBounds` is `List.eraseIdx`), and `denoteDeclArray` is
`denoteDecls` of `toList` (`denoteDeclArray_iff`).  So the three facts are
stated on lists and transported once. -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:109-110 declares — **the
name-test is the same test on both sides**, and this is the place
`denoteN_inj` is load-bearing in this module: a handle the list does not hold
must not decode to a name con-leche's list does hold. -/
theorem denoteNList_contains {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN st.ns n = some nP) :
    ∀ (l : List NIdx) (lP : List ConLeche.Name),
      ConRon.Arena.Frontend.denoteNList st.ns l = some lP →
      l.contains n = lP.contains nP := by
  obtain ⟨rk, hrk⟩ := hwf
  intro l
  induction l with
  | nil =>
    intro lP h
    simp only [ConRon.Arena.Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons m ms ih =>
    intro lP h
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    cases hm : denoteN st.ns m with
    | none => rw [hm] at h; simp at h
    | some mP =>
      cases hms : ConRon.Arena.Frontend.denoteNList st.ns ms with
      | none => rw [hm, hms] at h; simp at h
      | some msP =>
        rw [hm, hms] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.contains_cons, ih msP hms]
        by_cases hmn : m = n
        · subst hmn
          rw [hn] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          simp
        · have hne : mP ≠ nP := by
            intro he
            subst he
            exact hmn (Arena.denoteN_inj hrk.nsWF hm hn)
          rw [beq_eq_false_iff_ne.mpr (Ne.symm hmn),
            beq_eq_false_iff_ne.mpr (Ne.symm hne)]

/-- con-leche: ConLeche/Frontend/Prepare.lean:109-110 declares — the test at a
RECORD, over `declNames_denote`. -/
theorem declares_denote {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN st.ns n = some nP) {d : IDeclaration}
    {dP : Declaration} (hpn : DeclProjNamed st d)
    (hd : ConRon.Arena.Frontend.denoteDecl st d = some dP) :
    declares n d = ConLeche.Frontend.declares nP dP := by
  rw [declares, ConLeche.Frontend.declares]
  exact denoteNList_contains hwf hn _ _ (declNames_denote hpn hd)

/-- con-leche: none — a denoting stream is denoting at every index. -/
theorem denoteDecls_getElem? {st : EStore} :
    ∀ (l : List IDeclaration) (lP : List Declaration),
      denoteDecls st l = some lP → ∀ i : Nat,
        OptRel (fun d dP => ConRon.Arena.Frontend.denoteDecl st d = some dP)
          l[i]? lP[i]? := by
  intro l
  induction l with
  | nil =>
    intro lP h i
    simp only [denoteDecls, Option.some.injEq] at h
    subst h
    simp only [List.getElem?_nil]
    exact OptRel.refl_none
  | cons a as ih =>
    intro lP h i
    simp only [denoteDecls] at h
    cases ha : ConRon.Arena.Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero]
          exact ha
        | succ k => simpa using ih xs has k

/-- con-leche: none — a denoting stream stays denoting when one record is
dropped: `Array.eraseIdxIfInBounds` is `List.eraseIdx` on both sides. -/
theorem denoteDecls_eraseIdx {st : EStore} :
    ∀ (l : List IDeclaration) (lP : List Declaration),
      denoteDecls st l = some lP → ∀ i : Nat,
        denoteDecls st (l.eraseIdx i) = some (lP.eraseIdx i) := by
  intro l
  induction l with
  | nil =>
    intro lP h i
    simp only [denoteDecls, Option.some.injEq] at h
    subst h
    simp only [List.eraseIdx_nil, denoteDecls]
  | cons a as ih =>
    intro lP h i
    simp only [denoteDecls] at h
    cases ha : ConRon.Arena.Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        cases i with
        | zero => simpa using has
        | succ k =>
          simp only [List.eraseIdx_cons_succ, denoteDecls, ha, ih xs has k]

/-- con-leche: none — the `findIdx` of two agreeing predicates over two
denoting lists is one index. -/
theorem denoteDecls_findIdx {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN st.ns n = some nP) :
    ∀ (l : List IDeclaration) (lP : List Declaration),
      (∀ d ∈ l, DeclProjNamed st d) → denoteDecls st l = some lP →
      l.findIdx (declares n) = lP.findIdx (ConLeche.Frontend.declares nP) := by
  intro l
  induction l with
  | nil =>
    intro lP _ h
    simp only [denoteDecls, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro lP hpn h
    simp only [denoteDecls] at h
    cases ha : ConRon.Arena.Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [List.findIdx_cons, List.findIdx_cons,
          declares_denote hwf hn (hpn a (by simp)) ha,
          ih xs (fun d hd => hpn d (by simp [hd])) has]

/-- con-leche: ConLeche/Frontend/Prepare.lean:110 declares / :122 pick — the
stream's own copy of a prelude record, pulled out.  PURE on both sides
(`Arena/Frontend/Prepare.lean`'s note), so this is an equation about
`Array.findIdx` at two predicates that agree — which they do because
`d.names.contains n` is a handle test where con-leche's is a name test, and
`denoteN_inj` makes the two the same test on a well-formed store.

`declares n d` is `d.names.contains n`, so this statement reads
`IDeclaration.names` at every record of the stream and needs its exactness —
which round 4's finding 16 said a `.projInfo` does not give.  `DeclsProjNamed`
is the hypothesis that supplies it (round 5).

`denoteDecls_findIdx` for the index, `denoteDecls_getElem?` for the answer and
`denoteDecls_eraseIdx` for the rest — the three list facts above, transported
across `denoteDeclArray_iff`. -/
theorem pick_denote {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN st.ns n = some nP)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hpn : DeclsProjNamed st ds)
    (hds : denoteDeclArray st ds = some dsP) :
    (∀ d, (pick n ds).1 = some d →
      ∃ dP, ConRon.Arena.Frontend.denoteDecl st d = some dP ∧
        (ConLeche.Frontend.pick nP dsP).1 = some dP) ∧
    ((pick n ds).1 = none → (ConLeche.Frontend.pick nP dsP).1 = none) ∧
    denoteDeclArray st (pick n ds).2 = some (ConLeche.Frontend.pick nP dsP).2 := by
  have hl : denoteDecls st ds.toList = some dsP.toList := denoteDeclArray_iff.mp hds
  have hpnl : ∀ d ∈ ds.toList, DeclProjNamed st d := by
    intro d hd; exact hpn d (by simpa using hd)
  have harr : ∀ {α : Type} (a : Array α) (p : α → Bool),
      a.findIdx p = a.toList.findIdx p := by
    intro α a p; rw [← List.findIdx_toArray]
  have hidx : ds.findIdx (declares n) = dsP.findIdx (ConLeche.Frontend.declares nP) := by
    rw [harr, harr]
    exact denoteDecls_findIdx hwf hn _ _ hpnl hl
  have hget := denoteDecls_getElem? ds.toList dsP.toList hl (ds.findIdx (declares n))
  rw [pick, ConLeche.Frontend.pick]
  simp only [← hidx]
  refine ⟨?_, ?_, ?_⟩
  · intro d hdd
    rw [Array.getElem?_toList] at hget
    rw [hdd] at hget
    cases hq : dsP.toList[ds.findIdx (declares n)]? with
    | none => rw [hq] at hget; exact absurd hget (by simp [OptRel])
    | some dP =>
      rw [hq] at hget
      exact ⟨dP, hget, by rw [← Array.getElem?_toList]; exact hq⟩
  · intro hdd
    rw [Array.getElem?_toList] at hget
    rw [hdd] at hget
    cases hq : dsP.toList[ds.findIdx (declares n)]? with
    | none => rw [← Array.getElem?_toList]; exact hq
    | some dP => rw [hq] at hget; exact absurd hget (by simp [OptRel])
  · rw [denoteDeclArray_iff, Array.toList_eraseIdxIfInBounds,
      Array.toList_eraseIdxIfInBounds]
    exact denoteDecls_eraseIdx _ _ hl _

/-- con-leche: none — a record the pick leaves in the rest was in the stream:
`Array.eraseIdxIfInBounds` is `List.eraseIdx`, and a list with one element
dropped is a sublist. -/
theorem mem_eraseIdxIfInBounds {α : Type} {a : Array α} {i : Nat} {x : α}
    (h : x ∈ a.eraseIdxIfInBounds i) : x ∈ a := by
  rw [Array.mem_def] at h ⊢
  rw [Array.toList_eraseIdxIfInBounds] at h
  exact (List.eraseIdx_sublist a.toList i).mem h

theorem mem_of_pick_rest {n : NIdx} {ds : Array IDeclaration} {x : IDeclaration}
    (h : x ∈ (pick n ds).2) : x ∈ ds := mem_eraseIdxIfInBounds h

theorem mem_of_pick {n : NIdx} {ds : Array IDeclaration} {d : IDeclaration}
    (h : (pick n ds).1 = some d) : d ∈ ds := by
  rw [pick] at h
  simp only [] at h
  exact Array.getElem?_eq_some_iff.mp h |>.elim fun hlt hh => by
    subst hh; exact Array.getElem_mem hlt

/-- con-leche: ConLeche/Frontend/Prepare.lean:130-131 frontOf — the prepared
stream's front, prelude record by prelude record.

**The persistence clauses travel with the denotations**, because both passes
of the preparation are PERMUTATIONS: no record is built, so every record out
is a record in, and `Bridge/Checker/Capstone.lean`'s `hpd` at the fold's
argument is the parse's and the prelude's, carried.

`sorry`: a list induction over `preludeKey_run` and `pick_denote`.  Task
#97-P3-Frontend's sorry list, item 20. -/
theorem frontOf_run :
    ∀ (ps : List IDeclaration) {s s' : AState} {acc : Array IDeclaration}
      {accP : Array Declaration} {psP : List Declaration}
      {ds : Array IDeclaration} {dsP : Array Declaration}
      {front rest : Array IDeclaration},
      StateOK s → s.store.scratchOn = false →
      denoteDeclArray s.store acc = some accP → PersDecls acc →
      DeclsProjNamed s.store acc →
      denoteDecls s.store ps = some psP → (∀ d ∈ ps, PersDecl d) →
      (∀ d ∈ ps, DeclProjNamed s.store d) →
      denoteDeclArray s.store ds = some dsP → PersDecls ds →
      DeclsProjNamed s.store ds →
      frontOf acc ps ds s = .ok ((front, rest), s') →
      ParseStep s s' ∧ PersDecls front ∧ PersDecls rest ∧
        DeclsProjNamed s'.store front ∧ DeclsProjNamed s'.store rest ∧
        denoteDeclArray s'.store front
            = some (ConLeche.Frontend.frontOf accP psP dsP).1 ∧
          denoteDeclArray s'.store rest
            = some (ConLeche.Frontend.frontOf accP psP dsP).2 := by
  intro ps
  induction ps with
  | nil =>
    intro s s' acc accP psP ds dsP front rest hok hoff hacc hpacc hnacc hps hpps
      hnps hds hpds hnds hrun
    simp only [denoteDecls, Option.some.injEq] at hps
    subst hps
    rw [frontOf] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hf, hr⟩ := hv
    subst hf; subst hr
    exact ⟨ParseStep.refl hok, hpacc, hpds, hnacc, hnds, hacc, hds⟩
  | cons p ps ih =>
    intro s s' acc accP psP ds dsP front rest hok hoff hacc hpacc hnacc hps hpps
      hnps hds hpds hnds hrun
    simp only [denoteDecls] at hps
    cases hp : ConRon.Arena.Frontend.denoteDecl s.store p with
    | none => rw [hp] at hps; simp at hps
    | some pP =>
      cases hpsr : denoteDecls s.store ps with
      | none => rw [hp, hpsr] at hps; simp at hps
      | some psP' =>
        rw [hp, hpsr] at hps
        simp only [Option.some.injEq] at hps
        subst hps
        rw [frontOf] at hrun
        obtain ⟨k, s₁, hk, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hstep1, hpk, hdk⟩ :=
          preludeKey_run hok hoff (hnps p (by simp)) hp hk
        have hoff1 : s₁.store.scratchOn = false := by
          rw [hstep1.scratch]; exact hoff
        have hds1 : denoteDeclArray s₁.store ds = some dsP :=
          denoteDeclArray_ext hstep1.ext hds
        have hnds1 : DeclsProjNamed s₁.store ds := hnds.mono hstep1.ext
        obtain ⟨hpsome, hpnone, hprest⟩ :=
          pick_denote hstep1.ok.wf hdk hnds1 hds1
        -- the record this step contributes to the front
        have hcontrib : denoteDeclArray s₁.store
              (acc.push ((pick k ds).1.getD p))
            = some ((accP.push
                ((ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey pP) dsP).1.getD
                  pP))) ∧
            PersDecl ((pick k ds).1.getD p) ∧
            DeclProjNamed s₁.store ((pick k ds).1.getD p) := by
          have hone : ∀ (m : IDeclaration) (mP : Declaration),
              ConRon.Arena.Frontend.denoteDecl s₁.store m = some mP →
              PersDecl m → DeclProjNamed s₁.store m →
              denoteDeclArray s₁.store (acc.push m) = some (accP.push mP) ∧
                PersDecl m ∧ DeclProjNamed s₁.store m := by
            intro m mP hm hpm hnm
            refine ⟨?_, hpm, hnm⟩
            have h := denoteDeclArray_append
              (denoteDeclArray_ext hstep1.ext hacc)
              (show denoteDeclArray s₁.store #[m] = some #[mP] by
                rw [denoteDeclArray_iff]
                simp only [denoteDecls, hm])
            simpa only [Array.push_eq_append] using h
          cases hq : (pick k ds).1 with
          | some m =>
            obtain ⟨mP, hmd, hmc⟩ := hpsome m hq
            simp only [hmc, Option.getD_some]
            exact hone m mP hmd (hpds m (mem_of_pick hq)) (hnds1 m (mem_of_pick hq))
          | none =>
            simp only [hpnone hq, Option.getD_none]
            exact hone p pP (denoteDecl_ext hstep1.ext hp)
              (hpps p (by simp)) ((hnps p (by simp)).mono hstep1.ext)
        obtain ⟨hacc1, hpm, hnm⟩ := hcontrib
        obtain ⟨hstep2, hpf, hpr, hnf, hnr, hclf, hclr⟩ :=
          ih hstep1.ok hoff1 hacc1
            (by
              intro x hx
              rcases Array.mem_push.mp hx with h | h
              · exact hpacc x h
              · subst h; exact hpm)
            (by
              intro x hx
              rcases Array.mem_push.mp hx with h | h
              · exact (hnacc x h).mono hstep1.ext
              · subst h; exact hnm)
            (denoteDecls_ext hstep1.ext _ _ hpsr)
            (fun d hd => hpps d (by simp [hd]))
            (fun d hd => (hnps d (by simp [hd])).mono hstep1.ext)
            hprest
            (fun x hx => hpds x (mem_of_pick_rest hx))
            (fun x hx => hnds1 x (mem_of_pick_rest hx))
            hrest
        rw [ConLeche.Frontend.frontOf]
        exact ⟨hstep1.trans hstep2, hpf, hpr, hnf, hnr, hclf, hclr⟩

/-! ## The ground hoist -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:82 Declaration.usedConsts —
the constants a record mentions.  A walk over the record's terms with a `seen`
set, so the GRAY-invariant shape again.

**Round 4's finding 16 bit the FRAME here, and round 5 repaired it**:
`usedConstsBlock` (`Arena/Frontend/NatOpGround.lean:85-95`) calls
`ci.toConstantVal`, whose `.projInfo` arm INTERNS `Sort 1`
(`Arena/Env.lean:224-230`, because con-leche's `ConstantInfo.toConstantVal`
builds the closed dummy type as a VALUE), so `s' = s` is false at a block that
holds a projection table.  `ParseStep s s'` is the honest frame and the answer
is read at `s'.store` — round 4's own finding 15, one module over.

`sorry`: the fuel induction with the `seen` set — `Bridge/ExprOps/Leaves.lean`'s
open shape.  Task #97-P3-Frontend's sorry list, item 21. -/
theorem usedConsts_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {d : IDeclaration}
    {dP : Declaration} (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    {ns : Array NIdx} (hrun : IDeclaration.usedConsts d s = .ok (ns, s')) :
    ParseStep s s' ∧ denoteNList s'.store.ns ns.toList
      = some (ConLeche.Declaration.usedConsts dP).toList := by
  sorry

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:110 hoistTargets — **the
hoist's index, and where `denoteN_inj` is load-bearing**: the stream is
indexed by declared name, and two handles denoting one name would make the
twin move a record con-leche does not move.

**Round 4's finding 16 bit both halves, and round 5 repaired both**:
`nameIndex` (`Arena/Frontend/NatOpGround.lean:133-138`) indexes by
`ds[k].names`, and `usedConsts` moves the store at a projection table.  The
frame is `ParseStep` and the name exactness is `DeclsProjNamed`'s.

`sorry`: `usedConsts_run` and `isNatOpRecord_run` at the
fold, with `denoteN_inj` for the `Std.HashMap NIdx Nat` keyed by handle
against con-leche's `Std.HashMap Nat Nat` keyed by stream position — the two
maps are equal as functions of the position, which is what `applyHoist`
reads.  Task #97-P3-Frontend's sorry list, item 21. -/
theorem hoistTargets_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hwf : StoreWF s.store) (hnds : DeclsProjNamed s.store ds)
    (hds : denoteDeclArray s.store ds = some dsP)
    {target : Std.HashMap Nat Nat} (hrun : hoistTargets ds s = .ok (target, s')) :
    ParseStep s s' ∧ target = ConLeche.Frontend.hoistTargets dsP := by
  sorry

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:167 hoistNatOpGround — the
hoist.  Its answer is a PERMUTATION of its argument, so the denotation of the
result is the permutation of the denotation, and the moved-name list denotes.

**The frame is `ParseStep` for round 4's finding 16's reason** (round 5):
`hoistTargets` reads `usedConsts`, which interns at a projection table.

`sorry`: `hoistTargets_run`, then
`applyHoist`'s `reorder` as a `List.map` over a permutation of indices — the
same list of indices on both sides.  Task #97-P3-Frontend's sorry list,
item 21. -/
theorem hoistNatOpGround_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false)
    (hwf : StoreWF s.store) {ds : Array IDeclaration} {dsP : Array Declaration}
    (hds : denoteDeclArray s.store ds = some dsP) (hpds : PersDecls ds)
    (hnds : DeclsProjNamed s.store ds)
    {out : Array IDeclaration} {moved : Array NIdx}
    (hrun : hoistNatOpGround ds s = .ok ((out, moved), s')) :
    ParseStep s s' ∧ PersDecls out ∧ DeclsProjNamed s'.store out ∧
      denoteDeclArray s'.store out
        = some (ConLeche.Frontend.hoistNatOpGround dsP).1 ∧
      denoteNList s'.store.ns moved.toList
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
    (hprep : PersPreludeIx pre) (hnpre : DeclsProjNamed s.store pre.decls)
    {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDeclArray s.store ds = some dsP)
    (hpds : PersDecls ds) (hnds : DeclsProjNamed s.store ds)
    {out : Array IDeclaration}
    (hrun : preparePrelude pre ds s = .ok (out, s')) :
    ParseStep s s' ∧ PersDecls out ∧ DeclsProjNamed s'.store out ∧
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
  obtain ⟨hstep1, hpf, hpr, hnf, hnr, hclf, hclr⟩ :=
    frontOf_run pre.decls.toList hok hoff (denoteDeclArray_empty s.store)
      (by intro d hd; simp at hd)
      (DeclsProjNamed.empty s.store)
      (denoteDeclArray_iff.mp hpre) (by
        intro d hd
        exact hprep d (by simpa using hd))
      (by
        intro d hd
        exact hnpre d (by simpa using hd))
      hds hpds hnds hfront
  obtain ⟨hstep2, hpo, hno, hclo, -⟩ :=
    hoistNatOpGround_run hstep1.ok (by rw [hstep1.scratch]; exact hoff) hstep1.ok.wf
      (denoteDeclArray_append hclf hclr)
      (by
        intro d hd
        rcases Array.mem_append.mp hd with h | h
        · exact hpf d h
        · exact hpr d h)
      (by
        intro d hd
        rcases Array.mem_append.mp hd with h | h
        · exact hnf d h
        · exact hnr d h)
      hhoist
  have hdecls : prep.decls = decls := by rw [hv2]
  refine ⟨hstep1.trans hstep2, ?_, ?_, ?_⟩
  · rw [hdecls]; exact hpo
  · rw [hdecls]; exact hno
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
    (hprep : PersPreludeIx pre) (hnpre : DeclsProjNamed s.store pre.decls)
    {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDeclArray s.store ds = some dsP)
    (hpds : PersDecls ds) (hnds : DeclsProjNamed s.store ds)
    {out : Array IDeclaration}
    (hrun : preparePrelude pre ds s = .ok (out, s'))
    {d : Declaration} (hmem : d ∈ dsP) :
    ∃ outP, denoteDeclArray s'.store out = some outP ∧ d ∈ outP := by
  obtain ⟨-, -, -, hout⟩ :=
    preparePrelude_run hok hoff hpre hprep hnpre hds hpds hnds hrun
  exact ⟨_, hout, ConLeche.Frontend.mem_preparePrelude hmem⟩

end ConRon.Bridge.Frontend
