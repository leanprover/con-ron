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

/-! ### The used-constant walk's memo, and why THIS one is gray

`usedConstsGo` (`Arena/Frontend/NatOpGround.lean:52-71`) inserts the node into
`seen` BEFORE it matches — so unlike `Bridge/Frontend/ProjRec.lean`'s
`occursConstGo`, whose insert is at the end of the all-`false` branch, this
memo does carry nodes on the descent path.  It costs nothing here all the
same, because the walk's answer does not depend on WHY a key is in the set:
`seen` is only ever consulted as "stop", and the statement below relates the
two sets ELEMENTWISE rather than claiming anything about their members.

**What the two sets are keyed by is the whole content of this section.**
con-leche's memo is a `Std.HashSet Expr` and the twin's a `Std.HashSet EIdx`
(`Arena/Frontend/NatOpGround.lean`'s module note: "the visited set is DESIGN
§8.3's identity hash and a shared subterm costs one probe").  The two walks
therefore stop in the same places exactly when one handle per expression is
reachable — which is DESIGN §8.3's soundness obligation `denoteE_inj`, the
store being hash-consed.  Without it the twin would re-walk a subterm
con-leche skips and push its constants twice, and the array equality below
would be false.  This is the third place in the campaign where `denoteE_inj`
is load-bearing rather than convenient.  DESIGN #97-P3-Frontend round 6. -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:56-58 usedConstsGo — **the
two memos are the same memo**, one keyed by handle and one by the expression
the handle denotes.  Three clauses, because the correspondence has to survive
an arena EXTENSION (`usedConstsBlock` interns at a projection table) and the
`bwd` clause is what makes a NEW handle's absence from `seen` provable. -/
structure UCSeen (st : EStore) (seen : Std.HashSet EIdx)
    (seenP : Std.HashSet ConLeche.Expr) : Prop where
  fwd : ∀ h e, denoteE st h = some e → seen.contains h = true →
    seenP.contains e = true
  bwd : ∀ eP, seenP.contains eP = true →
    ∃ h, seen.contains h = true ∧ denoteE st h = some eP
  dom : ∀ h, seen.contains h = true → (denoteE st h).isSome = true

/-- con-leche: none — both walks start empty. -/
theorem UCSeen.empty {st : EStore} :
    UCSeen st (∅ : Std.HashSet EIdx) (∅ : Std.HashSet ConLeche.Expr) where
  fwd := by intro h e _ hc; simp at hc
  bwd := by intro eP hc; simp at hc
  dom := by intro h hc; simp at hc

/-- con-leche: none — **the stop test agrees**, which is the one thing the
walk reads of the memo.  The `←` direction is `denoteE_inj`. -/
theorem UCSeen.contains {st : EStore} (hwf : StoreWF st)
    {seen : Std.HashSet EIdx} {seenP : Std.HashSet ConLeche.Expr}
    (hs : UCSeen st seen seenP) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) : seen.contains h = seenP.contains e := by
  cases hc : seen.contains h with
  | true => exact (hs.fwd h e he hc).symm
  | false =>
    cases hp : seenP.contains e with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hdk⟩ := hs.bwd e hp
      obtain rfl : k = h := Arena.denoteE_inj hwf hdk he
      rw [hk] at hc; exact absurd hc (by simp)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:59 usedConstsGo — the two
inserts, at a handle and at what it denotes. -/
theorem UCSeen.insert {st : EStore} {seen : Std.HashSet EIdx}
    {seenP : Std.HashSet ConLeche.Expr} (hs : UCSeen st seen seenP)
    {h : EIdx} {e : Expr} (he : denoteE st h = some e) :
    UCSeen st (seen.insert h) (seenP.insert e) where
  fwd := by
    intro k ek hk hc
    rw [Std.HashSet.contains_insert] at hc ⊢
    rcases Bool.or_eq_true .. |>.mp hc with h1 | h2
    · have hhk : h = k := eq_of_beq h1
      subst hhk
      obtain rfl : e = ek := Option.some.inj (he.symm.trans hk)
      simp
    · rw [hs.fwd k ek hk h2]; simp
  bwd := by
    intro eP hc
    rw [Std.HashSet.contains_insert] at hc
    rcases Bool.or_eq_true .. |>.mp hc with h1 | h2
    · obtain rfl : e = eP := eq_of_beq h1
      exact ⟨h, by rw [Std.HashSet.contains_insert]; simp, he⟩
    · obtain ⟨k, hk, hdk⟩ := hs.bwd eP h2
      exact ⟨k, by rw [Std.HashSet.contains_insert, hk]; simp, hdk⟩
  dom := by
    intro k hk
    rw [Std.HashSet.contains_insert] at hk
    rcases Bool.or_eq_true .. |>.mp hk with h1 | h2
    · have hhk : h = k := eq_of_beq h1
      subst hhk; rw [he]; rfl
    · exact hs.dom k h2

/-- con-leche: none — the correspondence survives an arena EXTENSION, which
is what `usedConstsBlock` needs: `toConstantVal` interns `Sort 1` at a
projection table (round 4's finding 16).  A handle the extension ADDED cannot
denote anything the old set already holds, because `denoteE_inj` holds at the
bigger store too — which is the `bwd` clause's whole purpose. -/
theorem UCSeen.mono {st st' : EStore} {seen : Std.HashSet EIdx}
    {seenP : Std.HashSet ConLeche.Expr} (hs : UCSeen st seen seenP)
    (hx : Ext st st') : UCSeen st' seen seenP where
  fwd := by
    intro k ek hk hc
    obtain ⟨e₀, he₀⟩ := Option.isSome_iff_exists.mp (hs.dom k hc)
    have hq : e₀ = ek := Option.some.inj ((denote_ext he₀ hx).symm.trans hk)
    have hr := hs.fwd k e₀ he₀ hc
    rwa [hq] at hr
  bwd := by
    intro eP hc
    obtain ⟨k, hk, hdk⟩ := hs.bwd eP hc
    exact ⟨k, hk, denote_ext hdk hx⟩
  dom := by
    intro h hc
    obtain ⟨e₀, he₀⟩ := Option.isSome_iff_exists.mp (hs.dom h hc)
    rw [denote_ext he₀ hx]; rfl

/-- con-leche: none — the accumulator's own step: a name pushed on both
sides. -/
theorem denoteNList_snoc {st : NStore} :
    ∀ {l : List NIdx} {lP : List ConLeche.Name} {n : NIdx}
      {nP : ConLeche.Name}, denoteNList st l = some lP →
      denoteN st n = some nP → denoteNList st (l ++ [n]) = some (lP ++ [nP]) := by
  intro l
  induction l with
  | nil =>
    intro lP n nP hl hn
    simp only [denoteNList, Option.some.injEq] at hl
    subst hl
    simp only [List.nil_append, denoteNList, hn]
  | cons a as ih =>
    intro lP n nP hl hn
    rw [denoteNList] at hl
    cases ha : denoteN st a with
    | none => rw [ha] at hl; simp at hl
    | some x =>
      cases has : denoteNList st as with
      | none => rw [ha, has] at hl; simp at hl
      | some xs =>
        rw [ha, has] at hl
        simp only [Option.some.injEq] at hl
        subst hl
        simp only [List.cons_append, denoteNList, ha, ih has hn]

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:54-77 usedConstsGo — **the
arena side of the used-constant walk**: the twin's walk over handles visits
the same nodes and pushes the same names, in the same order, as con-leche's
over the denoted tree.  Read-only: it never interns, so the state stands
still. -/
theorem usedConstsGo_run {s : AState} (hok : StateOK s) :
    ∀ (fuel : Nat) {seen seen' : Std.HashSet EIdx} {acc acc' : Array NIdx}
      {seenP : Std.HashSet ConLeche.Expr} {accP : Array ConLeche.Name}
      {h : EIdx} {e : Expr} {s' : AState},
      UCSeen s.store seen seenP →
      denoteNList s.store.ns acc.toList = some accP.toList →
      denoteE s.store h = some e →
      usedConstsGo seen acc fuel h s = .ok ((seen', acc'), s') →
      s' = s ∧
        UCSeen s.store seen' (ConLeche.Frontend.usedConstsGo seenP accP e).1 ∧
        denoteNList s.store.ns acc'.toList
          = some (ConLeche.Frontend.usedConstsGo seenP accP e).2.toList := by
  have hwf : StoreWF s.store := hok.wf
  intro fuel
  induction fuel with
  | zero =>
    intro seen seen' acc acc' seenP accP h e s' _ _ _ hrun
    rw [ConRon.Arena.Frontend.usedConstsGo] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro seen seen' acc acc' seenP accP h e s' hseen hacc he hrun
    rw [ConRon.Arena.Frontend.usedConstsGo] at hrun
    rw [ConLeche.Frontend.usedConstsGo]
    rw [← hseen.contains hwf he]
    by_cases hc : seen.contains h = true
    · rw [if_pos hc] at hrun ⊢
      obtain ⟨hv, hs⟩ := AM.pure_ok hrun
      subst hs
      injection hv with e1 e2
      subst e1; subst e2
      exact ⟨rfl, hseen, hacc⟩
    · rw [if_neg hc] at hrun ⊢
      simp only [] at hrun
      obtain ⟨v, s₁, hv, hrest⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hview⟩ := view_run hv
      have hins := hseen.insert he
      match v, hview with
      | .const m us, hview =>
        obtain ⟨mP, ls, rfl, hm, -⟩ := denote_const_inv hwf hview he
        simp only [] at hrest
        obtain ⟨hv2, hs⟩ := AM.pure_ok hrest
        subst hs
        injection hv2 with e1 e2
        subst e1; subst e2
        refine ⟨rfl, hins, ?_⟩
        simp only [Array.toList_push]
        exact denoteNList_snoc hacc hm
      | .bvar i, hview =>
        obtain rfl := denote_bvar_inv hwf hview he
        simp only [] at hrest
        obtain ⟨hv2, hs⟩ := AM.pure_ok hrest
        subst hs
        injection hv2 with e1 e2
        subst e1; subst e2
        exact ⟨rfl, hins, hacc⟩
      | .sort u, hview =>
        obtain ⟨l, rfl, -⟩ := denote_sort_inv hwf hview he
        simp only [] at hrest
        obtain ⟨hv2, hs⟩ := AM.pure_ok hrest
        subst hs
        injection hv2 with e1 e2
        subst e1; subst e2
        exact ⟨rfl, hins, hacc⟩
      | .lit l, hview =>
        obtain rfl := denote_lit_inv hwf hview he
        simp only [] at hrest
        obtain ⟨hv2, hs⟩ := AM.pure_ok hrest
        subst hs
        injection hv2 with e1 e2
        subst e1; subst e2
        exact ⟨rfl, hins, hacc⟩
      | .fvar k ty, hview =>
        obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
        simp only [] at hrest
        exact ih hins hacc hdt hrest
      | .proj nn i sub, hview =>
        obtain ⟨nm, es, rfl, hnn, hsub⟩ := denote_proj_inv hwf hview he
        simp only [] at hrest
        exact ih hins (by
          simp only [Array.toList_push]
          exact denoteNList_snoc hacc hnn) hsub hrest
      | .app f a, hview =>
        obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hview he
        simp only [] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨sn1, ac1⟩ := p1
        obtain ⟨rfl, hs1, ha1⟩ := ih hins hacc hf hg1
        simp only [] at hr1
        exact ih hs1 ha1 ha hr1
      | .lam ty body mt, hview =>
        obtain ⟨et, eb, rfl, hf, ha⟩ := denote_lam_inv hwf hview he
        simp only [] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨sn1, ac1⟩ := p1
        obtain ⟨rfl, hs1, ha1⟩ := ih hins hacc hf hg1
        simp only [] at hr1
        exact ih hs1 ha1 ha hr1
      | .forallE ty body mt, hview =>
        obtain ⟨et, eb, rfl, hf, ha⟩ := denote_forallE_inv hwf hview he
        simp only [] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨sn1, ac1⟩ := p1
        obtain ⟨rfl, hs1, ha1⟩ := ih hins hacc hf hg1
        simp only [] at hr1
        exact ih hs1 ha1 ha hr1
      | .letE ty w body, hview =>
        obtain ⟨et, ew, eb, rfl, h1d, h2d, h3d⟩ := denote_letE_inv hwf hview he
        simp only [] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨sn1, ac1⟩ := p1
        obtain ⟨rfl, hs1, ha1⟩ := ih hins hacc h1d hg1
        simp only [] at hr1
        obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
        obtain ⟨sn2, ac2⟩ := p2
        obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 h2d hg2
        simp only [] at hr2
        exact ih hs2 ha2 h3d hr2

/-! ### con-leche's two inline folds, named

con-leche writes the block walk as a `List.foldl` over a closure and the rule
walk as another inside it (`ConLeche/Frontend/NatOpGround.lean:87-93`).  DESIGN
§3.4's rule for a fold — "a `List` fold is a named recursion" — is why the twin
has `usedConstsBlock` and `usedConstsRules` as top-level functions; read in the
other direction it is why the theorems below need con-leche's closures to have
names too.  Both equations are `rfl`. -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:92 Declaration.usedConsts —
the inner closure: one recursor rule's right-hand side. -/
def ucRuleStep (p : Std.HashSet ConLeche.Expr × Array ConLeche.Name)
    (r : ConLeche.RecRule) : Std.HashSet ConLeche.Expr × Array ConLeche.Name :=
  ConLeche.Frontend.usedConstsGo p.1 p.2 r.rhs

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:88-93 Declaration.usedConsts
— the outer closure: one block member's type, and its rules if it is a
recursor. -/
def ucBlockStep (p : Std.HashSet ConLeche.Expr × Array ConLeche.Name)
    (ci : ConLeche.ConstantInfo) :
    Std.HashSet ConLeche.Expr × Array ConLeche.Name :=
  let q := ConLeche.Frontend.usedConstsGo p.1 p.2 ci.toConstantVal.type
  match ci with
  | .recInfo _ _ _ rules => rules.foldl ucRuleStep q
  | _ => q

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:87-93 Declaration.usedConsts
— the named fold IS con-leche's inline one. -/
theorem usedConsts_indDecl_eq (block : List ConLeche.ConstantInfo) (nP : Nat) :
    ConLeche.Declaration.usedConsts (.indDecl block nP)
      = (block.foldl ucBlockStep
          (({} : Std.HashSet ConLeche.Expr), (#[] : Array ConLeche.Name))).2 :=
  rfl

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:92 Declaration.usedConsts —
**a recursor's rules**, folded over the block's one visited set.  No intern, so
the state stands still. -/
theorem usedConstsRules_run {s : AState} (hok : StateOK s) :
    ∀ (rs : List IRecRule) {rsP : List ConLeche.RecRule}
      {seen seen' : Std.HashSet EIdx} {acc acc' : Array NIdx}
      {seenP : Std.HashSet ConLeche.Expr} {accP : Array ConLeche.Name}
      {s' : AState},
      ConRon.Arena.Frontend.denoteRules s.store rs = some rsP →
      UCSeen s.store seen seenP →
      denoteNList s.store.ns acc.toList = some accP.toList →
      usedConstsRules seen acc rs s = .ok ((seen', acc'), s') →
      s' = s ∧ UCSeen s.store seen' (rsP.foldl ucRuleStep (seenP, accP)).1 ∧
        denoteNList s.store.ns acc'.toList
          = some (rsP.foldl ucRuleStep (seenP, accP)).2.toList := by
  intro rs
  induction rs with
  | nil =>
    intro rsP seen seen' acc acc' seenP accP s' hd hseen hacc hrun
    simp only [ConRon.Arena.Frontend.denoteRules, Option.some.injEq] at hd
    subst hd
    rw [ConRon.Arena.Frontend.usedConstsRules] at hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrun
    subst hs
    injection hv with e1 e2
    subst e1; subst e2
    exact ⟨rfl, hseen, hacc⟩
  | cons r rs ih =>
    intro rsP seen seen' acc acc' seenP accP s' hd hseen hacc hrun
    rw [ConRon.Arena.Frontend.denoteRules] at hd
    cases h1 : ConRon.Arena.Frontend.denoteRule s.store r with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : ConRon.Arena.Frontend.denoteRules s.store rs with
      | none => rw [h1, h2] at hd; simp at hd
      | some xs =>
        rw [h1, h2] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        have hrhs : denoteE s.store r.rhs = some x.rhs := by
          rw [ConRon.Arena.Frontend.denoteRule] at h1
          cases hc : denoteN s.store.ns r.ctor with
          | none => rw [hc] at h1; simp at h1
          | some c =>
            cases hf : ConRon.Arena.Frontend.denoteFire s.store r.fire with
            | none => rw [hc, hf] at h1; simp at h1
            | some f =>
              cases hr : denoteE s.store r.rhs with
              | none => rw [hc, hf, hr] at h1; simp at h1
              | some rhs =>
                rw [hc, hf, hr] at h1
                simp only [Option.some.injEq] at h1
                subst h1
                rfl
        rw [ConRon.Arena.Frontend.usedConstsRules] at hrun
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrun
        obtain ⟨sn1, ac1⟩ := p1
        obtain ⟨rfl, hs1, ha1⟩ := usedConstsGo_run hok coreWalkFuel hseen hacc hrhs hg1
        simp only [] at hr1
        simp only [List.foldl_cons, ucRuleStep]
        exact ih h2 hs1 ha1 hr1

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo — the denotation
preserves the CONSTRUCTOR: only a recursor denotes a recursor. -/
theorem denoteCI_recInfo {st : EStore} {ci : IConstantInfo}
    {v : ConLeche.ConstantVal} {mI rP : Nat} {rs : List ConLeche.RecRule}
    (hd : ConRon.Arena.Frontend.denoteCI st ci = some (.recInfo v mI rP rs)) :
    ∃ iv imI irP irs, ci = .recInfo iv imI irP irs := by
  cases ci with
  | recInfo w a b c => exact ⟨w, a, b, c, rfl⟩
  | axiomInfo w =>
    rw [ConRon.Arena.Frontend.denoteCI] at hd
    rcases Option.map_eq_some_iff.mp hd with ⟨_, -, hh⟩; exact nomatch hh
  | ctorInfo w a b =>
    rw [ConRon.Arena.Frontend.denoteCI] at hd
    rcases Option.map_eq_some_iff.mp hd with ⟨_, -, hh⟩; exact nomatch hh
  | projInfo t =>
    rw [ConRon.Arena.Frontend.denoteCI] at hd
    rcases Option.map_eq_some_iff.mp hd with ⟨_, -, hh⟩; exact nomatch hh
  | defnInfo w e hint =>
    rw [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · exact nomatch (Option.some.inj hd)
    · exact absurd hd (by simp)
  | thmInfo w e =>
    rw [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · exact nomatch (Option.some.inj hd)
    · exact absurd hd (by simp)
  | indInfo w c =>
    rw [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · exact nomatch (Option.some.inj hd)
    · exact absurd hd (by simp)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:89-93 Declaration.usedConsts
— `ucBlockStep`'s match reads the constructor and nothing else, so at a member
that is not a recursor on the twin's side the fold's rule branch is dead. -/
theorem ucBlockStep_denote {st : EStore} {ci : IConstantInfo}
    {x : ConLeche.ConstantInfo}
    (hd : ConRon.Arena.Frontend.denoteCI st ci = some x)
    (h : ∀ v mI rP rs, ci ≠ .recInfo v mI rP rs)
    (p : Std.HashSet ConLeche.Expr × Array ConLeche.Name) :
    ucBlockStep p x
      = ConLeche.Frontend.usedConstsGo p.1 p.2 x.toConstantVal.type := by
  cases x with
  | recInfo a b c d =>
    obtain ⟨iv, imI, irP, irs, hh⟩ := denoteCI_recInfo hd
    exact absurd hh (h iv imI irP irs)
  | axiomInfo _ => rfl
  | defnInfo _ _ _ => rfl
  | thmInfo _ _ => rfl
  | indInfo _ _ => rfl
  | ctorInfo _ _ _ => rfl
  | projInfo _ => rfl

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:87-93 Declaration.usedConsts
— **an inductive block**, folded over ONE visited set.

The frame is `ParseStep` and not `s' = s`: `toConstantVal`'s `.projInfo` arm
interns `Sort 1` (`Arena/Env.lean:224-230` — round 4's finding 16), so the
store grows at a block that holds a projection table, and `UCSeen.mono`,
`denoteNListE_ext` and `denoteCIList_ext` are what carry the induction's data
across that. -/
theorem usedConstsBlock_run :
    ∀ (cs : List IConstantInfo) {csP : List ConLeche.ConstantInfo}
      {s s' : AState} {seen seen' : Std.HashSet EIdx} {acc acc' : Array NIdx}
      {seenP : Std.HashSet ConLeche.Expr} {accP : Array ConLeche.Name},
      StateOK s → s.store.scratchOn = false →
      ConRon.Arena.Frontend.denoteCIList s.store cs = some csP →
      UCSeen s.store seen seenP →
      denoteNList s.store.ns acc.toList = some accP.toList →
      usedConstsBlock seen acc cs s = .ok ((seen', acc'), s') →
      ParseStep s s' ∧ UCSeen s'.store seen' (csP.foldl ucBlockStep (seenP, accP)).1 ∧
        denoteNList s'.store.ns acc'.toList
          = some (csP.foldl ucBlockStep (seenP, accP)).2.toList := by
  intro cs
  induction cs with
  | nil =>
    intro csP s s' seen seen' acc acc' seenP accP hok hoff hd hseen hacc hrun
    simp only [ConRon.Arena.Frontend.denoteCIList, Option.some.injEq] at hd
    subst hd
    rw [ConRon.Arena.Frontend.usedConstsBlock] at hrun
    obtain ⟨hv, hs⟩ := AM.pure_ok hrun
    subst hs
    injection hv with e1 e2
    subst e1; subst e2
    exact ⟨ParseStep.refl hok, hseen, hacc⟩
  | cons ci cs ih =>
    intro csP s s' seen seen' acc acc' seenP accP hok hoff hd hseen hacc hrun
    rw [ConRon.Arena.Frontend.denoteCIList] at hd
    cases h1 : ConRon.Arena.Frontend.denoteCI s.store ci with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : ConRon.Arena.Frontend.denoteCIList s.store cs with
      | none => rw [h1, h2] at hd; simp at hd
      | some xs =>
        rw [h1, h2] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        rw [ConRon.Arena.Frontend.usedConstsBlock] at hrun
        obtain ⟨cv, s₁, hcv, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hstep1, hty⟩ := toConstantVal_type_run hok hoff h1 hcv
        simp only [] at hrest
        obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok hrest
        obtain ⟨sn1, ac1⟩ := p1
        obtain ⟨rfl, hs1, ha1⟩ :=
          usedConstsGo_run hstep1.ok coreWalkFuel (hseen.mono hstep1.ext)
            (denoteNListE_ext hstep1.ext _ _ hacc) hty hg1
        simp only [] at hr1
        -- the tail of the fold, shared by all seven constructors
        have tail : ∀ {sn2 : Std.HashSet EIdx} {ac2 : Array NIdx} {t : AState},
            UCSeen s₂.store sn2 (ucBlockStep (seenP, accP) x).1 →
            denoteNList s₂.store.ns ac2.toList
              = some (ucBlockStep (seenP, accP) x).2.toList →
            usedConstsBlock sn2 ac2 cs s₂ = .ok ((seen', acc'), t) →
            ParseStep s t ∧
              UCSeen t.store seen' ((x :: xs).foldl ucBlockStep (seenP, accP)).1 ∧
              denoteNList t.store.ns acc'.toList
                = some ((x :: xs).foldl ucBlockStep (seenP, accP)).2.toList := by
          intro sn2 ac2 t hs2 ha2 hr2
          obtain ⟨hstep2, hs3, ha3⟩ :=
            ih hstep1.ok (by rw [hstep1.scratch]; exact hoff)
              (denoteCIList_ext hstep1.ext _ _ h2) hs2 ha2 hr2
          exact ⟨hstep1.trans hstep2,
            by simpa only [List.foldl_cons] using hs3,
            by simpa only [List.foldl_cons] using ha3⟩
        -- the six non-recursor constructors run no rules
        have hnorules : ∀ {t : AState},
            (do let y ← (pure (sn1, ac1) : AM (Std.HashSet EIdx × Array NIdx))
                usedConstsBlock y.1 y.2 cs) s₂ = .ok ((seen', acc'), t) →
            usedConstsBlock sn1 ac1 cs s₂ = .ok ((seen', acc'), t) := by
          intro t hh
          obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hh
          obtain ⟨hv2, hs2⟩ := AM.pure_ok hg2
          subst hs2; subst hv2
          exact hr2
        have hgen : (∀ v mI rP rs, ci ≠ IConstantInfo.recInfo v mI rP rs) →
            usedConstsBlock sn1 ac1 cs s₂ = .ok ((seen', acc'), s') →
            ParseStep s s' ∧
              UCSeen s'.store seen' ((x :: xs).foldl ucBlockStep (seenP, accP)).1 ∧
              denoteNList s'.store.ns acc'.toList
                = some ((x :: xs).foldl ucBlockStep (seenP, accP)).2.toList := by
          intro hne hh
          exact tail (by rw [ucBlockStep_denote h1 hne]; exact hs1)
            (by rw [ucBlockStep_denote h1 hne]; exact ha1) hh
        cases ci with
        | recInfo v mI rP rls =>
          rw [ConRon.Arena.Frontend.denoteCI] at h1
          cases hc : ConRon.Arena.Frontend.denoteCV s.store v with
          | none => rw [hc] at h1; simp at h1
          | some cvP =>
            cases hr : ConRon.Arena.Frontend.denoteRules s.store rls with
            | none => rw [hc, hr] at h1; simp at h1
            | some rlsP =>
              rw [hc, hr] at h1
              simp only [Option.some.injEq] at h1
              subst h1
              obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
              obtain ⟨sn2, ac2⟩ := p2
              obtain ⟨rfl, hq2, hq3⟩ :=
                usedConstsRules_run hstep1.ok rls
                  (denoteRules_ext hstep1.ext _ _ hr) hs1 ha1 hg2
              exact tail (by simpa only [ucBlockStep] using hq2)
                (by simpa only [ucBlockStep] using hq3) hr2
        | axiomInfo v =>
          exact hgen (by intro _ _ _ _ hh; exact nomatch hh) (hnorules hr1)
        | defnInfo v e hint =>
          exact hgen (by intro _ _ _ _ hh; exact nomatch hh) (hnorules hr1)
        | thmInfo v e =>
          exact hgen (by intro _ _ _ _ hh; exact nomatch hh) (hnorules hr1)
        | indInfo v c =>
          exact hgen (by intro _ _ _ _ hh; exact nomatch hh) (hnorules hr1)
        | ctorInfo v a b =>
          exact hgen (by intro _ _ _ _ hh; exact nomatch hh) (hnorules hr1)
        | projInfo t =>
          exact hgen (by intro _ _ _ _ hh; exact nomatch hh) (hnorules hr1)

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

**CLOSED** (round 6).  `usedConstsGo_run` is the walk, `usedConstsRules_run`
and `usedConstsBlock_run` the two folds, and the whole of what makes them line
up is `UCSeen`: con-leche's memo is keyed by `Expr` and the twin's by handle,
and the two stop in the same places because `denoteE` is INJECTIVE.

**No `DeclProjNamed` hypothesis.**  The block arm reads `toConstantVal`, whose
`.projInfo` arm is the one that interns — but only its TYPE, and the dummy
`Sort 1` is the same whatever the table is called.  `toConstantVal_type_run`
(`Bridge/Frontend/Lines.lean`) is that half, stated without the name clause so
that it does not have to be assumed here. -/
theorem usedConsts_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {d : IDeclaration}
    {dP : Declaration} (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP)
    {ns : Array NIdx} (hrun : IDeclaration.usedConsts d s = .ok (ns, s')) :
    ParseStep s s' ∧ denoteNList s'.store.ns ns.toList
      = some (ConLeche.Declaration.usedConsts dP).toList := by
  -- the four record arms that walk a `ConstantVal`'s type
  have hcvty : ∀ (w : IConstantVal) (cw : ConstantVal),
      ConRon.Arena.Frontend.denoteCV s.store w = some cw →
      denoteE s.store w.type = some cw.type := by
    intro w cw hw
    simp only [ConRon.Arena.Frontend.denoteCV] at hw
    cases h1 : denoteN s.store.ns w.name with
    | none => rw [h1] at hw; simp at hw
    | some n =>
      cases h2 : ConRon.Arena.Frontend.denoteNList s.store.ns w.levelParams with
      | none => rw [h1, h2] at hw; simp at hw
      | some lps =>
        cases h3 : denoteE s.store w.type with
        | none => rw [h1, h2, h3] at hw; simp at hw
        | some ty =>
          rw [h1, h2, h3] at hw
          obtain rfl := Option.some.inj hw
          rfl
  have hempty : denoteNList s.store.ns (#[] : Array NIdx).toList
      = some (#[] : Array ConLeche.Name).toList := rfl
  -- a value record: the header's type, then the value, over one visited set
  have hval : ∀ {w : IConstantVal} {cw : ConstantVal} {e : EIdx} {x : Expr},
      ConRon.Arena.Frontend.denoteCV s.store w = some cw →
      denoteE s.store e = some x →
      (do let p ← usedConstsGo ∅ #[] coreWalkFuel w.type
          (do pure (← usedConstsGo p.1 p.2 coreWalkFuel e).2 : AM (Array NIdx)))
        s = .ok (ns, s') →
      ParseStep s s' ∧ denoteNList s'.store.ns ns.toList
        = some (ConLeche.Frontend.usedConstsGo
            (ConLeche.Frontend.usedConstsGo {} #[] cw.type).1
            (ConLeche.Frontend.usedConstsGo {} #[] cw.type).2 x).2.toList := by
    intro w cw e x hw he hh
    obtain ⟨p1, s₁, hg1, hr1⟩ := AM.bind_ok hh
    obtain ⟨sn1, ac1⟩ := p1
    obtain ⟨rfl, hs1, ha1⟩ :=
      usedConstsGo_run hok coreWalkFuel UCSeen.empty hempty (hcvty w cw hw) hg1
    simp only [] at hr1
    obtain ⟨p2, s₂, hg2, hr2⟩ := AM.bind_ok hr1
    obtain ⟨sn2, ac2⟩ := p2
    obtain ⟨rfl, -, ha2⟩ := usedConstsGo_run hok coreWalkFuel hs1 ha1 he hg2
    obtain ⟨hvv, hss⟩ := AM.pure_ok hr2
    subst hss; subst hvv
    exact ⟨ParseStep.refl hok, ha2⟩
  cases d with
  | basisDecl k =>
    rw [ConRon.Arena.Frontend.IDeclaration.usedConsts] at hrun
    obtain ⟨hvv, hss⟩ := AM.pure_ok hrun
    subst hss; subst hvv
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.some.injEq] at hd
    subst hd
    exact ⟨ParseStep.refl hok, rfl⟩
  | quotDecl k w =>
    rw [ConRon.Arena.Frontend.IDeclaration.usedConsts] at hrun
    obtain ⟨hvv, hss⟩ := AM.pure_ok hrun
    subst hss; subst hvv
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cw, -, rfl⟩ := hd
    exact ⟨ParseStep.refl hok, rfl⟩
  | axiomDecl w =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    rw [ConRon.Arena.Frontend.IDeclaration.usedConsts] at hrun
    obtain ⟨p1, s₁, hg1, hr1⟩ := AM.bind_ok hrun
    obtain ⟨sn1, ac1⟩ := p1
    obtain ⟨rfl, -, ha1⟩ :=
      usedConstsGo_run hok coreWalkFuel UCSeen.empty hempty (hcvty w cw hw) hg1
    obtain ⟨hvv, hss⟩ := AM.pure_ok hr1
    subst hss; subst hvv
    exact ⟨ParseStep.refl hok, ha1⟩
  | defnDecl w e hint =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        rw [ConRon.Arena.Frontend.IDeclaration.usedConsts] at hrun
        exact hval hw he hrun
  | thmDecl w e =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        rw [ConRon.Arena.Frontend.IDeclaration.usedConsts] at hrun
        exact hval hw he hrun
  | opaqueDecl w e =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        rw [ConRon.Arena.Frontend.IDeclaration.usedConsts] at hrun
        exact hval hw he hrun
  | indDecl block nP =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨bP, hbP, rfl⟩ := hd
    rw [ConRon.Arena.Frontend.IDeclaration.usedConsts] at hrun
    obtain ⟨p1, s₁, hg1, hr1⟩ := AM.bind_ok hrun
    obtain ⟨sn1, ac1⟩ := p1
    obtain ⟨hstep1, -, ha1⟩ :=
      usedConstsBlock_run block hok hoff hbP UCSeen.empty hempty hg1
    obtain ⟨hvv, hss⟩ := AM.pure_ok hr1
    subst hss; subst hvv
    rw [usedConsts_indDecl_eq]
    exact ⟨hstep1, ha1⟩

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
