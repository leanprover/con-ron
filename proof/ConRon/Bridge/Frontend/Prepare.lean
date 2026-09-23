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
import ConRon.Bridge.Checker.DeclVal
import Init.Internal.Order.While

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
    (hpins : PinsOK s) (hrb : ReadCachesOK s)
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
    obtain ⟨hstep, hpers, rc, hcl, hrel⟩ := parseBytes_run hmw hmr hok hoff hpins hrb hpb
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

/-! ## The target map (task #97-P3-Frontend round 8)

con-leche's `hoistTargets` is an `Id.run do` of two `for` loops (the name
index), a `for i`/`for g` pair, and a worklist `while`.  Every `for` yields on
every turn, so each is a `foldl` (`forIn_id_yield`); the `while` is a
`Lean.Loop.forIn`, unfolded one turn at a time by
`Lean.Loop.forIn_eq_of_monadTail` (`loop_id_unfold`) — con-leche's loop is
never shown to terminate, the twin's accepting run supplies the turns.
`clHoistTargets_eq` is the whole of con-leche's side; the twin's side is four
simulations, bottom up: `hoistClosure_sim` (the worklist, against the
round-8 twin whose fuel counts marked records), `hoistDeps_sim`,
`hoistTargetsGo_sim` and `nameIndex_sim`. -/

/-- con-leche: none — an always-yielding `forIn` in `Id` is a `foldl`. -/
theorem forIn_id_yield {α β : Type} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (F : α → β → β)
    (hf : ∀ a b, f a b = ForInStep.yield (F a b)) :
    forIn l init f = l.foldl (fun b a => F a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, hf]; exact ih _

/-- con-leche: none — con-leche's `while` in `Id`, unfolded once. -/
theorem loop_id_unfold {β : Type} (b : β) (B : Unit → β → Id (ForInStep β)) :
    (forIn Lean.Loop.mk b B : Id β) =
      match B () b with
      | .done v => v
      | .yield v => (forIn Lean.Loop.mk v B : Id β) := by
  show Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  cases B () b <;> rfl

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:110-136 hoistTargets — the
name index, related to con-leche's name-keyed one: a handle looks up what its
name looks up, and the keys of both sides denote. -/
structure IdxRel (st : EStore) (idx : Std.HashMap NIdx Nat)
    (idxP : Std.HashMap ConLeche.Name Nat) : Prop where
  get : ∀ n nP, denoteN st.ns n = some nP → idx[n]? = idxP[nP]?
  keys : ∀ n, idx.contains n = true → ∃ nP, denoteN st.ns n = some nP
  keysP : ∀ nP, idxP.contains nP = true → ∃ n, denoteN st.ns n = some nP

/-- con-leche: none — `IdxRel` survives an arena extension, by `denoteN_inj`
at the bigger store. -/
theorem IdxRel.mono {st st' : EStore} {idx : Std.HashMap NIdx Nat}
    {idxP : Std.HashMap ConLeche.Name Nat} (h : IdxRel st idx idxP)
    (hx : Ext st st') (hw : NStoreWF st'.ns) : IdxRel st' idx idxP where
  get := by
    intro n nP hn
    by_cases hc : idxP.contains nP = true
    · obtain ⟨m, hm⟩ := h.keysP nP hc
      have hm' := hx.lss.ls.ns m nP hm
      obtain rfl := Arena.denoteN_inj hw hn hm'
      exact h.get _ _ hm
    · have hnone : idxP[nP]? = none :=
        Std.HashMap.getElem?_eq_none_of_contains_eq_false (by simpa using hc)
      rw [hnone]
      by_cases hk : idx.contains n = true
      · obtain ⟨mP, hm⟩ := h.keys n hk
        have hm' : denoteN st'.ns n = some mP := hx.lss.ls.ns n mP hm
        rw [hn] at hm'
        obtain rfl := Option.some.inj hm'
        rw [h.get _ _ hm, hnone]
      · exact Std.HashMap.getElem?_eq_none_of_contains_eq_false (by simpa using hk)
  keys := fun n hk => by
    obtain ⟨nP, h1⟩ := h.keys n hk
    exact ⟨nP, hx.lss.ls.ns n nP h1⟩
  keysP := fun nP hk => by
    obtain ⟨n, h1⟩ := h.keysP nP hk
    exact ⟨n, hx.lss.ls.ns n nP h1⟩

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:130-134 hoistTargets — the
worklist's inner `for n in ds[k]!.usedConsts` loop, as a fold. -/
def clPushDeps (idxP : Std.HashMap ConLeche.Name Nat) (i k : Nat)
    (ns : List ConLeche.Name) (st : Array Nat) : Array Nat :=
  ns.foldl (fun st n =>
    match idxP[n]? with
    | some m => if (decide (m > i) && m != k) = true then st.push m else st
    | none => st) st

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:130-134 hoistTargets — the
twin's `pushOne` (a list, top first) is con-leche's push loop (an array, top
last). -/
theorem pushOne_sim {st : EStore} {idx : Std.HashMap NIdx Nat}
    {idxP : Std.HashMap ConLeche.Name Nat} (hr : IdxRel st idx idxP) (i k : Nat) :
    ∀ (ns : List NIdx) (nsP : List ConLeche.Name),
      denoteNList st.ns ns = some nsP → ∀ (arr : Array Nat) (L : List Nat),
      arr.toList.reverse = L →
      (clPushDeps idxP i k nsP arr).toList.reverse = hoistClosure.pushOne idx i k ns L := by
  intro ns
  induction ns with
  | nil =>
    intro nsP h arr L hL
    simp only [denoteNList, Option.some.injEq] at h
    subst h
    simpa [clPushDeps, hoistClosure.pushOne] using hL
  | cons n ns ih =>
    intro nsP h arr L hL
    simp only [denoteNList] at h
    cases hn : denoteN st.ns n with
    | none => rw [hn] at h; simp at h
    | some nP =>
      cases hns : denoteNList st.ns ns with
      | none => rw [hn, hns] at h; simp at h
      | some nsP' =>
        rw [hn, hns] at h
        obtain rfl := Option.some.inj h
        have hg := hr.get n nP hn
        simp only [clPushDeps, List.foldl_cons]
        rw [hoistClosure.pushOne]
        rw [← hg]
        cases hm : idx[n]? with
        | none => exact ih nsP' hns arr L hL
        | some m =>
          simp only []
          refine ih nsP' hns _ _ ?_
          by_cases hc : (decide (m > i) && m != k) = true
          · rw [if_pos hc, if_pos (by simpa using hc)]
            simp [hL]
          · rw [if_neg hc, if_neg (by simpa using hc)]
            exact hL

/-- con-leche: none — an array read as a stack (top last) against a list (top
first): the top, and the pop. -/
theorem arr_rev_cons {arr : Array Nat} {k : Nat} {L : List Nat}
    (h : arr.toList.reverse = k :: L) :
    ∃ hsz : arr.size > 0, arr[arr.size - 1] = k ∧ arr.pop.toList.reverse = L := by
  have ht : arr.toList = L.reverse ++ [k] := by
    rw [← List.reverse_reverse arr.toList, h]; simp
  have hsz : arr.size = L.length + 1 := by
    rw [← Array.length_toList, ht]; simp
  refine ⟨by omega, ?_, ?_⟩
  · rw [← Array.getElem_toList]
    simp only [ht]
    rw [List.getElem_append_right (by simp; omega)]
    simp
  · rw [Array.toList_pop, ht]
    simp

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:122-134 hoistTargets — one
turn of con-leche's worklist `while`, as a value: pop the top, `continue` if
its record already precedes `i`, else mark it and push its dependencies. -/
def clCloseStep (dsP : Array Declaration) (idxP : Std.HashMap ConLeche.Name Nat)
    (i : Nat) (tg : Std.HashMap Nat Nat) (st : Array Nat) :
    ForInStep (Std.HashMap Nat Nat × Array Nat) :=
  if h : st.size > 0 then
    if hoistDone tg st[st.size - 1] i then .yield (tg, st.pop)
    else .yield (tg.insert st[st.size - 1] i,
      clPushDeps idxP i st[st.size - 1] (dsP[st[st.size - 1]]!.usedConsts.toList) st.pop)
  else .done (tg, st)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:122-134 hoistTargets — the
`continue` pops, run in a batch: they are the twin's `hoistDropDone`. -/
theorem loop_drop {dsP : Array Declaration} {idxP : Std.HashMap ConLeche.Name Nat}
    {i : Nat} (B : Unit → Std.HashMap Nat Nat × Array Nat →
      Id (ForInStep (Std.HashMap Nat Nat × Array Nat)))
    (hB : ∀ tg st, B () (tg, st) = clCloseStep dsP idxP i tg st)
    (target : Std.HashMap Nat Nat) :
    ∀ (L : List Nat) (arr : Array Nat), arr.toList.reverse = L →
      ∃ arr' : Array Nat, arr'.toList.reverse = hoistDropDone target i L ∧
        (forIn Lean.Loop.mk (target, arr) B : Id _) =
          forIn Lean.Loop.mk (target, arr') B := by
  intro L
  induction L with
  | nil => intro arr h; exact ⟨arr, by simpa [hoistDropDone] using h, rfl⟩
  | cons k L ih =>
    intro arr h
    obtain ⟨hsz, htop, hpop⟩ := arr_rev_cons h
    by_cases hd : hoistDone target k i = true
    · obtain ⟨arr', h1, h2⟩ := ih arr.pop hpop
      refine ⟨arr', by rw [hoistDropDone, if_pos hd]; exact h1, ?_⟩
      rw [loop_id_unfold, hB]
      simp only [clCloseStep, dif_pos hsz, htop, if_pos hd]
      exact h2
    · refine ⟨arr, by rw [hoistDropDone, if_neg hd]; exact h, rfl⟩

/-- con-leche: none — a denoting stream denotes at an in-bounds index, with
con-leche's `ds[k]!`. -/
theorem declAt_denote {st : EStore} {ds : Array IDeclaration} {dsP : Array Declaration}
    (hds : denoteDeclArray st ds = some dsP) {k : Nat} (hk : k < ds.size) :
    ConRon.Arena.Frontend.denoteDecl st ds[k] = some dsP[k]! := by
  have hL := denoteDeclArray_iff.mp hds
  have h := denoteDecls_getElem? ds.toList dsP.toList hL k
  simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hk] at h
  obtain ⟨dP, h2, h3⟩ := h.some_left rfl
  have hiP : k < dsP.size := by
    rw [Array.getElem?_eq_some_iff] at h2; exact h2.1
  rw [getElem!_pos dsP k hiP, (Array.getElem?_eq_some_iff.mp h2).2]
  exact h3

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:122-134 hoistTargets — **the
worklist**: an accepting run of the twin's fuelled `hoistClosure` answers what
con-leche's `while` answers from the same map and the same stack.  The twin's
batch of `continue` pops is `loop_drop`; a marking pop is one turn on both
sides, with `usedConsts_run` for the pushed references and `pushOne_sim` for
the push loop.  Fuel exhaustion is a `fail`, so an accepting run never meets
it. -/
theorem hoistClosure_sim {ds : Array IDeclaration} {dsP : Array Declaration}
    {idx : Std.HashMap NIdx Nat} {idxP : Std.HashMap ConLeche.Name Nat} {i : Nat}
    (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size)
    (B : Unit → Std.HashMap Nat Nat × Array Nat →
      Id (ForInStep (Std.HashMap Nat Nat × Array Nat)))
    (hB : ∀ tg st, B () (tg, st) = clCloseStep dsP idxP i tg st) :
    ∀ (fuel : Nat) (s : AState) (target : Std.HashMap Nat Nat) (L : List Nat)
      (arr : Array Nat) (t' : Std.HashMap Nat Nat) (s' : AState),
      StateOK s → s.store.scratchOn = false →
      denoteDeclArray s.store ds = some dsP → IdxRel s.store idx idxP →
      (∀ x ∈ L, x < ds.size) → arr.toList.reverse = L →
      hoistClosure ds idx i fuel target L s = .ok (t', s') →
      ParseStep s s' ∧ t' = (forIn Lean.Loop.mk (target, arr) B : Id _).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s target L arr t' s' hok hoff hds hr hL harr hrun
    obtain ⟨arr', harr', hloop⟩ := loop_drop B hB target L arr harr
    rw [hoistClosure] at hrun
    rw [hloop]
    cases hdrop : hoistDropDone target i L with
    | nil =>
      simp only [hdrop] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      rw [hdrop] at harr'
      have : arr' = #[] := by
        apply Array.toList_inj.mp; simpa using harr'
      subst this
      rw [loop_id_unfold, hB]
      exact ⟨ParseStep.refl hok, by simp [clCloseStep]⟩
    | cons k rest =>
      simp only [hdrop] at hrun
      exact (AM.fail_ok hrun).elim
  | succ f ih =>
    intro s target L arr t' s' hok hoff hds hr hL harr hrun
    obtain ⟨arr', harr', hloop⟩ := loop_drop B hB target L arr harr
    rw [hoistClosure] at hrun
    rw [hloop]
    cases hdrop : hoistDropDone target i L with
    | nil =>
      simp only [hdrop] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      rw [hdrop] at harr'
      have : arr' = #[] := by
        apply Array.toList_inj.mp; simpa using harr'
      subst this
      rw [loop_id_unfold, hB]
      exact ⟨ParseStep.refl hok, by simp [clCloseStep]⟩
    | cons k rest =>
      simp only [hdrop] at hrun
      have hmem : ∀ x, x ∈ hoistDropDone target i L → x ∈ L :=
        fun x hx => hoistDropDone_sub target i hx
      have hk : k < ds.size := hL k (hmem k (by rw [hdrop]; exact List.mem_cons_self))
      have hrest : ∀ x ∈ rest, x < ds.size := fun x hx =>
        hL x (hmem x (by rw [hdrop]; exact List.mem_cons_of_mem k hx))
      have hnd := hoistDropDone_head target i hdrop
      rw [hdrop] at harr'
      obtain ⟨hsz, htop, hpop⟩ := arr_rev_cons harr'
      try simp only [] at hrun
      obtain ⟨stack', s₁, hpush, hrun⟩ := AM.bind_ok hrun
      unfold hoistClosure.pushDeps at hpush
      rw [dif_pos hk] at hpush
      obtain ⟨ns, s₂, hus, hpure⟩ := AM.bind_ok hpush
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hpure
      obtain ⟨hstep, hns⟩ := usedConsts_run hok hoff (declAt_denote hds hk) hus
      have hr1 := hr.mono hstep.ext (nsWF_of_StateOK hstep.ok)
      have hpushP := pushOne_sim hr1 i k ns.toList _ hns arr'.pop rest hpop
      have hoff1 : s₁.store.scratchOn = false := by rw [hstep.scratch]; exact hoff
      obtain ⟨hstep2, hres⟩ := ih s₁ (target.insert k i) _ _ t' s' hstep.ok hoff1
        (denoteDeclArray_ext hstep.ext hds) hr1
        (hoistClosure_pushOne_lt hidx k _ rest hrest) hpushP hrun
      refine ⟨hstep.trans hstep2, ?_⟩
      rw [hres, loop_id_unfold (b := (target, arr')), hB]
      simp only [clCloseStep, dif_pos hsz, htop, hnd]
      rfl

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:97-104 isNatOpRecord — the
record test reads two pinned name lists and compares handles; it leaves the
state alone and answers the denoted name exactly when con-leche answers it
(`denoteN_inj`, through `Bridge/Checker/Names.lean`'s `denoteNList_contains`). -/
theorem isNatOpRecord_run {s s' : AState} (hok : StateOK s) (hpins : PinsOK s)
    {d : IDeclaration} {dP : Declaration}
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dP) {r : Option NIdx}
    (hrun : isNatOpRecord d s = .ok (r, s')) :
    s' = s ∧ OptRel (fun (c : NIdx) (cP : ConLeche.Name) => denoteN s.store.ns c = some cP)
      r (ConLeche.Frontend.isNatOpRecord dP) := by
  cases d with
  | defnDecl cv v h =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    cases hw : ConRon.Arena.Frontend.denoteCV s.store cv with
    | none => rw [hw] at hd; simp at hd
    | some cvP =>
      cases he : denoteE s.store v with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        have hn := denoteCV_name hw
        rw [isNatOpRecord] at hrun
        obtain ⟨l1, s₁, h1, hr1⟩ := AM.bind_ok hrun
        obtain ⟨rfl, hl1⟩ := natDivModNames_run hpins h1
        obtain ⟨l2, s₂, h2, hr2⟩ := AM.bind_ok hr1
        obtain ⟨rfl, hl2⟩ := natOpNames_run hpins h2
        have hc1 := Bridge.denoteNList_contains hok.wf _ _ (denoteNL_toList _ _ hl1) _ _ hn
        have hc2 := Bridge.denoteNList_contains hok.wf _ _ (denoteNL_toList _ _ hl2) _ _ hn
        simp only [ConLeche.Frontend.isNatOpRecord]
        by_cases hq : (l1.contains cv.name || l2.contains cv.name) = true
        · rw [if_pos hq] at hr2
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
          rw [hc1, hc2] at hq
          rw [if_pos hq]
          exact ⟨rfl, hn⟩
        · rw [if_neg hq] at hr2
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
          rw [hc1, hc2] at hq
          rw [if_neg hq]
          exact ⟨rfl, trivial⟩
  | axiomDecl cv =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨_, _, rfl⟩ := hd
    simp only [isNatOpRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, trivial⟩
  | thmDecl cv v =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    split at hd
    · obtain rfl := Option.some.inj hd
      simp only [isNatOpRecord] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, trivial⟩
    · simp at hd
  | opaqueDecl cv v =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    split at hd
    · obtain rfl := Option.some.inj hd
      simp only [isNatOpRecord] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, trivial⟩
    · simp at hd
  | basisDecl k =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.some.injEq] at hd
    subst hd
    simp only [isNatOpRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, trivial⟩
  | indDecl block nP =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨_, _, rfl⟩ := hd
    simp only [isNatOpRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, trivial⟩
  | quotDecl k cv =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨_, _, rfl⟩ := hd
    simp only [isNatOpRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, trivial⟩

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:119-134 hoistTargets — one
turn of the `for g in natOpDeps c` loop, as a value: a ground declared after
`i` pulls its closure (con-leche's `while`, whose body is `B i`). -/
def clDepStep (B : Nat → Unit → Std.HashMap Nat Nat × Array Nat →
      Id (ForInStep (Std.HashMap Nat Nat × Array Nat)))
    (idxP : Std.HashMap ConLeche.Name Nat) (i : Nat) (t : Std.HashMap Nat Nat)
    (g : ConLeche.Name) : Std.HashMap Nat Nat :=
  match idxP[g]? with
  | some j => if j > i then (forIn Lean.Loop.mk (t, #[j]) (B i) : Id _).1 else t
  | none => t

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:119-134 hoistTargets — the
twin's `hoistDeps` is con-leche's `for g in natOpDeps c` loop. -/
theorem hoistDeps_sim {ds : Array IDeclaration} {dsP : Array Declaration}
    {idx : Std.HashMap NIdx Nat} {idxP : Std.HashMap ConLeche.Name Nat} {i : Nat}
    (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size)
    (B : Nat → Unit → Std.HashMap Nat Nat × Array Nat →
      Id (ForInStep (Std.HashMap Nat Nat × Array Nat)))
    (hB : ∀ tg st, B i () (tg, st) = clCloseStep dsP idxP i tg st) :
    ∀ (gs : List NIdx) (gsP : List ConLeche.Name) (s : AState)
      (target t' : Std.HashMap Nat Nat) (s' : AState),
      StateOK s → s.store.scratchOn = false →
      denoteDeclArray s.store ds = some dsP → IdxRel s.store idx idxP →
      denoteNL s.store gs gsP →
      hoistTargetsGo.hoistDeps ds idx target i gs s = .ok (t', s') →
      ParseStep s s' ∧ t' = gsP.foldl (clDepStep B idxP i) target := by
  intro gs
  induction gs with
  | nil =>
    intro gsP s target t' s' hok _ _ _ hgs hrun
    cases gsP with
    | cons _ _ => exact hgs.elim
    | nil =>
      rw [hoistTargetsGo.hoistDeps] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨ParseStep.refl hok, rfl⟩
  | cons g gs ih =>
    intro gsP s target t' s' hok hoff hds hr hgs hrun
    cases gsP with
    | nil => exact hgs.elim
    | cons gP gsP =>
      obtain ⟨hg, hgs⟩ := hgs
      have hget := hr.get g gP hg
      rw [hoistTargetsGo.hoistDeps] at hrun
      simp only [List.foldl_cons, clDepStep]
      rw [← hget]
      cases hj : idx[g]? with
      | none =>
        rw [hj] at hrun
        exact ih gsP s target t' s' hok hoff hds hr hgs hrun
      | some j =>
        rw [hj] at hrun
        simp only [] at hrun ⊢
        by_cases hji : j > i
        · rw [if_pos hji] at hrun
          rw [if_pos hji]
          obtain ⟨t1, s₁, h1, hrun⟩ := AM.bind_ok hrun
          obtain ⟨hstep1, rfl⟩ := hoistClosure_sim hidx (B i) hB ds.size s target [j] #[j]
            t1 s₁ hok hoff hds hr (by simpa using hidx g j hj) (by simp) h1
          have hoff1 : s₁.store.scratchOn = false := by rw [hstep1.scratch]; exact hoff
          obtain ⟨hstep2, hres⟩ := ih gsP s₁ _ t' s' hstep1.ok hoff1
            (denoteDeclArray_ext hstep1.ext hds)
            (hr.mono hstep1.ext (nsWF_of_StateOK hstep1.ok))
            (denoteNL_ext hstep1.ext _ _ hgs) hrun
          exact ⟨hstep1.trans hstep2, hres⟩
        · rw [if_neg hji] at hrun
          rw [if_neg hji]
          exact ih gsP s target t' s' hok hoff hds hr hgs hrun

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:117-134 hoistTargets — one
turn of the outer `for i in [0:ds.size]` loop, as a value. -/
def clOuterStep (B : Nat → Unit → Std.HashMap Nat Nat × Array Nat →
      Id (ForInStep (Std.HashMap Nat Nat × Array Nat)))
    (dsP : Array Declaration) (idxP : Std.HashMap ConLeche.Name Nat)
    (t : Std.HashMap Nat Nat) (i : Nat) : Std.HashMap Nat Nat :=
  match ConLeche.Frontend.isNatOpRecord dsP[i]! with
  | some c => (ConLeche.natOpDeps c).foldl (clDepStep B idxP i) t
  | none => t

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:117-134 hoistTargets — the
twin's `hoistTargetsGo` (a tail recursion from `i`) is con-leche's outer loop
over the rest of the index range. -/
theorem hoistTargetsGo_sim {ds : Array IDeclaration} {dsP : Array Declaration}
    {idx : Std.HashMap NIdx Nat} {idxP : Std.HashMap ConLeche.Name Nat}
    (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size)
    (B : Nat → Unit → Std.HashMap Nat Nat × Array Nat →
      Id (ForInStep (Std.HashMap Nat Nat × Array Nat)))
    (hB : ∀ i tg st, B i () (tg, st) = clCloseStep dsP idxP i tg st) :
    ∀ (n i : Nat) (s : AState) (target t' : Std.HashMap Nat Nat) (s' : AState),
      ds.size - i = n →
      StateOK s → s.store.scratchOn = false → PinsOK s →
      denoteDeclArray s.store ds = some dsP → IdxRel s.store idx idxP →
      hoistTargetsGo ds idx target i s = .ok (t', s') →
      ParseStep s s' ∧ t' = (List.range' i n).foldl (clOuterStep B dsP idxP) target := by
  intro n
  induction n with
  | zero =>
    intro i s target t' s' hn hok _ _ _ _ hrun
    rw [hoistTargetsGo, dif_neg (by omega)] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨ParseStep.refl hok, rfl⟩
  | succ n ih =>
    intro i s target t' s' hn hok hoff hpins hds hr hrun
    have hi : i < ds.size := by omega
    rw [hoistTargetsGo, dif_pos hi] at hrun
    obtain ⟨r, s₁, h1, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hopt⟩ := isNatOpRecord_run hok hpins (declAt_denote hds hi) h1
    rw [hs1] at hrun
    simp only [List.range'_succ, List.foldl_cons]
    cases r with
    | none =>
      simp only [] at hrun
      have hcl : ConLeche.Frontend.isNatOpRecord dsP[i]! = none := by
        cases h : ConLeche.Frontend.isNatOpRecord dsP[i]! with
        | none => rfl
        | some _ => rw [h] at hopt; exact hopt.elim
      have := ih (i + 1) s target t' s' (by omega) hok hoff hpins hds hr hrun
      simpa [clOuterStep, hcl] using this
    | some c =>
      simp only [] at hrun
      cases h : ConLeche.Frontend.isNatOpRecord dsP[i]! with
      | none => rw [h] at hopt; exact hopt.elim
      | some cP =>
        rw [h] at hopt
        obtain ⟨gs, s₂, h2, hrun⟩ := AM.bind_ok hrun
        obtain ⟨-, -, -, -, hgs⟩ := natOpDeps_run hok hpins hopt h2
        have hs2 := natOpDeps_state hpins h2
        rw [hs2] at hrun hgs
        obtain ⟨t1, s₃, h3, hrun⟩ := AM.bind_ok hrun
        obtain ⟨hstep1, rfl⟩ := hoistDeps_sim hidx B (hB i) gs _ s target t1 s₃ hok hoff hds hr
          hgs h3
        have hoff1 : s₃.store.scratchOn = false := by rw [hstep1.scratch]; exact hoff
        obtain ⟨hstep2, hres⟩ := ih (i + 1) s₃ _ t' s' (by omega) hstep1.ok hoff1
          (hpins.mono hstep1.ext hstep1.pins) (denoteDeclArray_ext hstep1.ext hds)
          (hr.mono hstep1.ext (nsWF_of_StateOK hstep1.ok)) hrun
        refine ⟨hstep1.trans hstep2, ?_⟩
        rw [hres]
        simp [clOuterStep, h]

/-- con-leche: none — an always-yielding `forIn` in `Id` whose body is a
`bind` into `yield` is a `foldl`. -/
theorem forIn_id_bind_yield {α β : Type} (l : List α) (init : β)
    (g : α → β → Id β) :
    forIn l init (fun a b => (g a b >>= fun s => pure (ForInStep.yield s)) : α → β → Id (ForInStep β))
      = l.foldl (fun b a => g a b) init :=
  forIn_id_yield l init _ _ (fun _ _ => rfl)

/-- con-leche: none — an always-yielding `forIn` in `Id` whose body is an
`if` of two yields is a `foldl`. -/
theorem forIn_id_ite_yield {α β : Type} (l : List α) (init : β)
    (p : α → β → Prop) [∀ a b, Decidable (p a b)] (X Y : α → β → β) :
    forIn l init (fun a b => (if p a b then pure (ForInStep.yield (X a b))
        else pure (ForInStep.yield (Y a b))) : α → β → Id (ForInStep β))
      = l.foldl (fun b a => if p a b then X a b else Y a b) init :=
  forIn_id_yield l init _ _ (fun a b => by by_cases h : p a b <;> simp [h] <;> rfl)

/-- con-leche: none — two `while` bodies that agree pointwise run alike. -/
theorem loop_congr {β : Type} (b : β) (f g : Unit → β → Id (ForInStep β))
    (h : ∀ u x, f u x = g u x) :
    (forIn Lean.Loop.mk b f : Id β) = forIn Lean.Loop.mk b g := by
  have : f = g := funext fun u => funext (h u)
  rw [this]

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:112-116 hoistTargets — the
name index, as con-leche computes it (its two `for` loops, as folds). -/
def clIdx (dsP : Array Declaration) : Std.HashMap ConLeche.Name Nat :=
  List.foldl (fun b a => List.foldl (fun b a_1 => if (!b.contains a_1) = true then
    b.insert a_1 a else b) b dsP[a]!.names) ∅ (List.range' 0 dsP.size)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:122-134 hoistTargets —
con-leche's `while` body, at the index `I`, as the function `clCloseStep`. -/
def clB (dsP : Array Declaration) (I : Std.HashMap ConLeche.Name Nat) (i : Nat) :
    Unit → Std.HashMap Nat Nat × Array Nat →
      Id (ForInStep (Std.HashMap Nat Nat × Array Nat)) :=
  fun _ p => clCloseStep dsP I i p.1 p.2

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:110-136 hoistTargets —
**con-leche's `hoistTargets`, as folds**: the name index is `clIdx`, the outer
loop a fold of `clOuterStep`, and the worklist `while` the `Loop` at the body
`clB` (`clCloseStep`).  Every `for` of the definition yields on every turn,
so each is a `foldl`; the `while` stays a `Loop.forIn`. -/
theorem clHoistTargets_eq (dsP : Array Declaration) :
    ConLeche.Frontend.hoistTargets dsP =
      List.foldl (clOuterStep (clB dsP (clIdx dsP)) dsP (clIdx dsP)) ∅
        (List.range' 0 dsP.size) := by
  symm
  unfold ConLeche.Frontend.hoistTargets
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run_bind, Id.run_pure, forIn_id_ite_yield,
    forIn_id_bind_yield]
  rw [show [:dsP.size].size = dsP.size by simp [Std.Legacy.Range.size]]
  simp only [Id.run]
  refine Eq.trans ?_ (forIn_id_yield _ _ _
    (fun a b => clOuterStep (clB dsP (clIdx dsP)) dsP (clIdx dsP) b a) ?hF).symm
  · rfl
  · intro a b
    unfold clOuterStep
    cases hrec : ConLeche.Frontend.isNatOpRecord dsP[a]! with
    | none => rfl
    | some c =>
      refine congrArg ForInStep.yield (forIn_id_yield _ _ _
        (fun g t => clDepStep (clB dsP (clIdx dsP)) (clIdx dsP) a t g) ?_)
      intro g t
      unfold clDepStep
      split
      · rename_i j heq
        have hj' : (clIdx dsP)[g]? = some j := heq
        rw [hj']
        by_cases hj : j > a
        · simp only [hj, if_true]
          refine congrArg (fun p : Std.HashMap Nat Nat × Array Nat => ForInStep.yield p.1)
            (loop_congr _ _ _ ?_)
          intro u x
          obtain ⟨tg, st⟩ := x
          simp only [clB, clCloseStep, hoistDone]
          by_cases hsz : st.size > 0
          · rw [dif_pos hsz, dif_pos hsz]
            cases hk : tg[st[st.size - 1]]? with
            | some t =>
              by_cases ht : t ≤ a
              · simp only [ht, if_true, decide_true]; rfl
              · simp only [ht, if_false, decide_false]
                refine congrArg (fun s => ForInStep.yield (tg.insert st[st.size - 1] a, s)) ?_
                rw [← Array.forIn_toList]
                refine forIn_id_yield _ _ _ _ ?_
                intro n s'
                split
                · rename_i m heq
                  have hm' : (clIdx dsP)[n]? = some m := heq
                  by_cases hc : (decide (m > a) && m != st[st.size - 1]) = true
                  · simp only [hc, if_true, hm']; rfl
                  · simp only [hc, hm']; rfl
                · rename_i heq
                  have hm' : (clIdx dsP)[n]? = none := by
                    cases h : (clIdx dsP)[n]? with
                    | none => rfl
                    | some j => exact absurd h (heq j)
                  simp only [hm']; rfl
            | none =>
              simp only [Bool.false_eq_true, if_false]
              refine congrArg (fun s => ForInStep.yield (tg.insert st[st.size - 1] a, s)) ?_
              rw [← Array.forIn_toList]
              refine forIn_id_yield _ _ _ _ ?_
              intro n s'
              split
              · rename_i m heq
                have hm' : (clIdx dsP)[n]? = some m := heq
                by_cases hc : (decide (m > a) && m != st[st.size - 1]) = true
                · simp only [hc, if_true, hm']; rfl
                · simp only [hc, hm']; rfl
              · rename_i heq
                have hm' : (clIdx dsP)[n]? = none := by
                  cases h : (clIdx dsP)[n]? with
                  | none => rfl
                  | some j => exact absurd h (heq j)
                simp only [hm']; rfl
          · rw [dif_neg hsz, dif_neg hsz]
            rfl
        · simp only [hj, if_false]
          rfl
      · rename_i heq
        have hj' : (clIdx dsP)[g]? = none := by
          cases h : (clIdx dsP)[g]? with
          | none => rfl
          | some j => exact absurd h (heq j)
        rw [hj']
        rfl

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:112-116 hoistTargets — one
name of the index loop: the first record declaring a name wins, on both
sides, and the relation survives (`denoteN_inj` for a different name). -/
theorem IdxRel.insertOne {st : EStore} {idx : Std.HashMap NIdx Nat}
    {idxP : Std.HashMap ConLeche.Name Nat} (h : IdxRel st idx idxP)
    (hw : NStoreWF st.ns) {n : NIdx} {nP : ConLeche.Name} (hn : denoteN st.ns n = some nP)
    (i : Nat) :
    IdxRel st (if idx.contains n then idx else idx.insert n i)
      (if (!idxP.contains nP) = true then idxP.insert nP i else idxP) := by
  have hc : idx.contains n = idxP.contains nP := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?,
      h.get n nP hn]
  by_cases hk : idx.contains n = true
  · rw [if_pos hk, if_neg (by rw [← hc, hk]; decide)]
    exact h
  · rw [if_neg hk, if_pos (by rw [← hc]; simpa using hk)]
    refine ⟨?_, ?_, ?_⟩
    · intro m mP hm
      rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
      by_cases hmn : n = m
      · subst hmn
        rw [hn] at hm
        obtain rfl := Option.some.inj hm
        simp
      · have hne : nP ≠ mP := fun he => hmn (Arena.denoteN_inj hw hn (he ▸ hm))
        rw [beq_eq_false_iff_ne.mpr hmn, beq_eq_false_iff_ne.mpr hne]
        exact h.get m mP hm
    · intro m hm
      rw [Std.HashMap.contains_insert] at hm
      rcases Bool.or_eq_true_iff.mp hm with he | he
      · have : n = m := by simpa using he
        subst this; exact ⟨nP, hn⟩
      · exact h.keys m he
    · intro mP hm
      rw [Std.HashMap.contains_insert] at hm
      rcases Bool.or_eq_true_iff.mp hm with he | he
      · have : nP = mP := by simpa using he
        subst this; exact ⟨n, hn⟩
      · exact h.keysP mP he

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:112-116 hoistTargets — the
inner `for n in ds[i]!.names` loop. -/
theorem insertNames_sim {st : EStore} (hw : NStoreWF st.ns) (i : Nat) :
    ∀ (ns : List NIdx) (nsP : List ConLeche.Name) (idx : Std.HashMap NIdx Nat)
      (idxP : Std.HashMap ConLeche.Name Nat),
      denoteNList st.ns ns = some nsP → IdxRel st idx idxP →
      IdxRel st (insertNames idx i ns)
        (nsP.foldl (fun b a_1 => if (!b.contains a_1) = true then b.insert a_1 i else b) idxP) := by
  intro ns
  induction ns with
  | nil =>
    intro nsP idx idxP h hr
    simp only [denoteNList, Option.some.injEq] at h
    subst h; exact hr
  | cons n ns ih =>
    intro nsP idx idxP h hr
    simp only [denoteNList] at h
    cases hn : denoteN st.ns n with
    | none => rw [hn] at h; simp at h
    | some nP =>
      cases hns : denoteNList st.ns ns with
      | none => rw [hn, hns] at h; simp at h
      | some nsP' =>
        rw [hn, hns] at h
        obtain rfl := Option.some.inj h
        rw [insertNames, List.foldl_cons]
        exact ih nsP' _ _ hns (hr.insertOne hw hn i)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:112-116 hoistTargets — **the
name index**: the twin's `nameIndex` is con-leche's, name for handle. -/
theorem nameIndex_sim {st : EStore} (hw : NStoreWF st.ns) {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDeclArray st ds = some dsP)
    (hnds : DeclsProjNamed st ds) :
    ∀ (n k : Nat) (idx : Std.HashMap NIdx Nat) (idxP : Std.HashMap ConLeche.Name Nat),
      ds.size - k = n → IdxRel st idx idxP →
      IdxRel st (nameIndex ds idx k)
        ((List.range' k n).foldl (fun b a => List.foldl (fun b a_1 =>
          if (!b.contains a_1) = true then b.insert a_1 a else b) b dsP[a]!.names) idxP) := by
  intro n
  induction n with
  | zero =>
    intro k idx idxP hn hr
    rw [nameIndex, dif_neg (by omega)]
    exact hr
  | succ n ih =>
    intro k idx idxP hn hr
    have hk : k < ds.size := by omega
    rw [nameIndex, dif_pos hk, List.range'_succ, List.foldl_cons]
    refine ih (k + 1) _ _ (by omega) ?_
    exact insertNames_sim hw k _ _ _ _
      (declNames_denote (hnds _ (Array.getElem_mem hk)) (declAt_denote hds hk)) hr

/-- con-leche: none — the twin's name index holds record positions. -/
theorem nameIndex_lt (ds : Array IDeclaration) :
    ∀ (n k : Nat) (idx : Std.HashMap NIdx Nat), ds.size - k = n →
      (∀ (x : NIdx) m, idx[x]? = some m → m < ds.size) →
      ∀ (x : NIdx) m, (nameIndex ds idx k)[x]? = some m → m < ds.size := by
  have hins : ∀ (i : Nat), i < ds.size → ∀ (ns : List NIdx) (idx : Std.HashMap NIdx Nat),
      (∀ (x : NIdx) m, idx[x]? = some m → m < ds.size) →
      ∀ (x : NIdx) m, (insertNames idx i ns)[x]? = some m → m < ds.size := by
    intro i hi ns
    induction ns with
    | nil => intro idx h; simpa [insertNames] using h
    | cons n ns ih =>
      intro idx h
      rw [insertNames]
      refine ih _ ?_
      split
      · exact h
      · intro x m hm
        rw [Std.HashMap.getElem?_insert] at hm
        split at hm
        · obtain rfl := Option.some.inj hm; exact hi
        · exact h x m hm
  intro n
  induction n with
  | zero =>
    intro k idx hn h
    rw [nameIndex, dif_neg (by omega)]
    exact h
  | succ n ih =>
    intro k idx hn h
    have hk : k < ds.size := by omega
    rw [nameIndex, dif_pos hk]
    exact ih (k + 1) _ (by omega) (hins k hk _ _ h)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:110 hoistTargets — **the
hoist's index, and where `denoteN_inj` is load-bearing**: the stream is
indexed by declared name, and two handles denoting one name would make the
twin move a record con-leche does not move.

**Round 4's finding 16 bit both halves, and round 5 repaired both**:
`nameIndex` (`Arena/Frontend/NatOpGround.lean:133-138`) indexes by
`ds[k].names`, and `usedConsts` moves the store at a projection table.  The
frame is `ParseStep` and the name exactness is `DeclsProjNamed`'s.

**CLOSED** (round 8), against the round-8 twin (`hoistClosure`'s fuel counts
marked records, `pushOne` has con-leche's `m != k`).  The target maps are
EQUAL, not merely related: both sides perform the same inserts in the same
order, so the simulations carry the map literally.  `denoteN_inj` is where it
is load-bearing: the name index is keyed by handle on the twin's side and by
name on con-leche's (`IdxRel`), and a handle a later `usedConsts` interned
must not look up a name the index holds under another handle
(`IdxRel.mono`). -/
theorem hoistTargets_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s)
    {ds : Array IDeclaration} {dsP : Array Declaration}
    (hwf : StoreWF s.store) (hnds : DeclsProjNamed s.store ds)
    (hds : denoteDeclArray s.store ds = some dsP)
    {target : Std.HashMap Nat Nat} (hrun : hoistTargets ds s = .ok (target, s')) :
    ParseStep s s' ∧ target = ConLeche.Frontend.hoistTargets dsP := by
  have hnw := nsWF_of_StateOK hok
  have hsz : ds.size = dsP.size := by
    have := denoteDecls_length _ _ (denoteDeclArray_iff.mp hds); simpa using this
  rw [hoistTargets] at hrun
  have hempty : IdxRel s.store (∅ : Std.HashMap NIdx Nat) (∅ : Std.HashMap ConLeche.Name Nat) :=
    ⟨fun _ _ _ => by simp, fun _ h => by simp at h, fun _ h => by simp at h⟩
  have hr0 : IdxRel s.store (nameIndex ds ∅ 0) (clIdx dsP) := by
    have := nameIndex_sim hnw hds hnds ds.size 0 ∅ ∅ (by simp) hempty
    rw [clIdx, ← hsz]; exact this
  have hidx := nameIndex_lt ds ds.size 0 ∅ (by simp) (by simp)
  obtain ⟨hstep, hres⟩ := hoistTargetsGo_sim hidx (clB dsP (clIdx dsP)) (fun _ _ _ => rfl)
    ds.size 0 s ∅ target s' (by simp) hok hoff hpins hds hr0 hrun
  refine ⟨hstep, ?_⟩
  rw [hres, clHoistTargets_eq, hsz]


/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — the
twin's `reorder` fold, as a `filterMap` over the index list. -/
theorem reorder_toList (ds : Array IDeclaration) :
    ∀ (order : List Nat) (acc : Array IDeclaration),
      (order.foldl (fun acc k => acc ++ (ds[k]?.toArray)) acc).toList
        = acc.toList ++ order.filterMap (fun k => ds[k]?) := by
  intro order
  induction order with
  | nil => intro acc; simp
  | cons k ks ih =>
    intro acc
    simp only [List.foldl_cons, ih, Array.toList_append, List.filterMap_cons]
    cases h : ds[k]? <;> simp

/-- con-leche: none — the records at a list of indices denote the denoted
records at the same indices. -/
theorem denoteDecls_filterMap {st : EStore} {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDecls st ds.toList = some dsP.toList) :
    ∀ (order : List Nat),
      denoteDecls st (order.filterMap (fun k => ds[k]?))
        = some (order.filterMap (fun k => dsP[k]?)) := by
  intro order
  induction order with
  | nil => rfl
  | cons k ks ih =>
    have h := denoteDecls_getElem? ds.toList dsP.toList hds k
    simp only [Array.getElem?_toList] at h
    simp only [List.filterMap_cons]
    cases h1 : ds[k]? with
    | none =>
      rw [h1] at h
      rw [h.none_left rfl] ; exact ih
    | some d =>
      obtain ⟨dP, h2, h3⟩ := h.some_left h1
      rw [h2]
      simp only [denoteDecls, h3, ih]

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — the
twin's `movedNames` loop, as con-leche's `filter` then `flatMap`. -/
theorem movedNames_toList (ds : Array IDeclaration) (target : Std.HashMap Nat Nat) :
    ∀ (n k : Nat) (acc : Array NIdx), ds.size - k = n →
      (movedNames ds target acc k).toList
        = acc.toList ++ ((List.range' k (ds.size - k)).filter (fun i => target.contains i)).flatMap
            (fun i => (ds[i]?.map IDeclaration.names).getD []) := by
  intro n
  induction n with
  | zero =>
    intro k acc hn
    rw [movedNames, dif_neg (by omega)]
    simp [hn]
  | succ n ih =>
    intro k acc hn
    have hk : k < ds.size := by omega
    rw [movedNames, dif_pos hk, ih (k + 1) _ (by omega)]
    have hr : ds.size - k = (ds.size - (k + 1)) + 1 := by omega
    rw [hr, List.range'_succ]
    by_cases hc : target.contains k = true
    · rw [if_pos hc]
      simp [hc, Array.getElem?_eq_getElem hk, List.flatMap_cons]
    · rw [if_neg hc]
      simp [hc]

/-- con-leche: none — `denoteNList` through `++`. -/
theorem denoteNList_append' {st : NStore} :
    ∀ {a : List NIdx} {b : List NIdx} {aP bP : List ConLeche.Name},
      denoteNList st a = some aP → denoteNList st b = some bP →
      denoteNList st (a ++ b) = some (aP ++ bP) := by
  intro a
  induction a with
  | nil => intro b aP bP ha hb; simp only [denoteNList, Option.some.injEq] at ha; subst ha; simpa using hb
  | cons x xs ih =>
    intro b aP bP ha hb
    simp only [denoteNList] at ha
    cases hx : denoteN st x with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : denoteNList st xs with
      | none => rw [hx, hxs] at ha; simp at ha
      | some ys =>
        rw [hx, hxs] at ha
        obtain rfl := Option.some.inj ha
        simp only [List.cons_append, denoteNList, hx, ih hxs hb]

/-- con-leche: ConLeche/Kernel/Env.lean:659-670 Declaration.names — the names
of the records at a list of in-range indices denote (`declNames_denote`). -/
theorem denoteNList_flatMap_names {st : EStore} {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDecls st ds.toList = some dsP.toList)
    (hnds : DeclsProjNamed st ds) :
    ∀ (idx : List Nat), (∀ i ∈ idx, i < ds.size) →
      denoteNList st.ns (idx.flatMap (fun i => (ds[i]?.map IDeclaration.names).getD []))
        = some (idx.flatMap (fun i => (dsP[i]!).names)) := by
  intro idx
  induction idx with
  | nil => intro _; rfl
  | cons i is ih =>
    intro hb
    have hi := hb i (by simp)
    have h := denoteDecls_getElem? ds.toList dsP.toList hds i
    simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hi] at h
    obtain ⟨dP, h2, h3⟩ := h.some_left rfl
    have hn := declNames_denote (hnds _ (Array.getElem_mem hi)) h3
    have hiP : i < dsP.size := by
      rw [Array.getElem?_eq_some_iff] at h2; exact h2.1
    have hdP : dsP[i]! = dP := by
      rw [getElem!_pos dsP i hiP]; exact (Array.getElem?_eq_some_iff.mp h2).2
    simp only [List.flatMap_cons, Array.getElem?_eq_getElem hi, Option.map_some,
      Option.getD_some, hdP]
    exact denoteNList_append' hn (ih (fun j hj => hb j (by simp [hj])))

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — **the
reorder, at one and the same target map**: the twin's `reorder` over the sorted
index list is con-leche's `List.map` over the same list (the two comparators
are the same function of the map), and the moved names are the declared names
of the moved records, in index order (`declNames_denote`, so `DeclsProjNamed`).
Pure on both sides.  Round 7's child of `hoistNatOpGround_run`; the two
comparators close by `congr` (they are the same term up to the matcher). -/
theorem applyHoist_run {st : EStore} {ds : Array IDeclaration}
    {dsP : Array Declaration} (hds : denoteDeclArray st ds = some dsP)
    (hpds : PersDecls ds) (hnds : DeclsProjNamed st ds)
    (target : Std.HashMap Nat Nat) :
    PersDecls (applyHoist ds target).1 ∧ DeclsProjNamed st (applyHoist ds target).1 ∧
      denoteDeclArray st (applyHoist ds target).1
        = some (ConLeche.Frontend.applyHoist dsP target).1 ∧
      denoteNList st.ns (applyHoist ds target).2.toList
        = some (ConLeche.Frontend.applyHoist dsP target).2.toList := by
  have hL := denoteDeclArray_iff.mp hds
  have hsz : ds.size = dsP.size := by
    have := denoteDecls_length _ _ hL; simpa using this
  simp only [applyHoist, ConLeche.Frontend.applyHoist]
  generalize hO : ((List.range ds.size).mergeSort fun a b => !hoistLt target b a) = ord
  rw [show (List.range dsP.size).mergeSort _ = ord from ?_]
  rotate_left
  · rw [← hO, ← hsz]
    congr 1
  have hbd : ∀ k ∈ ord, k < ds.size := by
    intro k hk
    rw [← hO] at hk
    have := (List.mergeSort_perm (List.range ds.size) _).mem_iff.mp hk
    simpa using this
  have hre : (reorder ds ord).toList = ord.filterMap (fun k => ds[k]?) := by
    rw [reorder, reorder_toList]; simp
  have hmemR : ∀ x ∈ reorder ds ord, x ∈ ds := by
    intro x hx
    rw [← Array.mem_toList_iff, hre, List.mem_filterMap] at hx
    obtain ⟨k, -, hk⟩ := hx
    exact Array.mem_of_getElem? hk
  refine ⟨fun x hx => hpds x (hmemR x hx), fun x hx => hnds x (hmemR x hx), ?_, ?_⟩
  · rw [denoteDeclArray_iff, hre]
    rw [denoteDecls_filterMap hL ord]
    congr 1
    have key : ∀ l : List Nat, (∀ k ∈ l, k < dsP.size) →
        l.filterMap (fun k => dsP[k]?) = l.map (fun k => dsP[k]!) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons k ks ih =>
        intro hb
        have hk := hb k (by simp)
        simp only [List.filterMap_cons, Array.getElem?_eq_getElem hk, List.map_cons,
          getElem!_pos dsP k hk, ih (fun j hj => hb j (by simp [hj]))]
    exact key ord (fun k hk => hsz ▸ hbd k hk)
  · rw [movedNames_toList ds target _ 0 #[] rfl]
    simp only [List.nil_append, Nat.sub_zero, ← List.range_eq_range']
    simp only [Array.toList_flatMap, Array.toList_filter, Array.toList_range]
    rw [← hsz]
    refine denoteNList_flatMap_names hL hnds _ (fun i hi => ?_)
    simp only [List.mem_filter, List.mem_range] at hi
    exact hi.1

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:167 hoistNatOpGround — the
hoist.  Its answer is a PERMUTATION of its argument, so the denotation of the
result is the permutation of the denotation, and the moved-name list denotes.

**The frame is `ParseStep` for round 4's finding 16's reason** (round 5):
`hoistTargets` reads `usedConsts`, which interns at a projection table.

`hoistTargets_run` (the SAME target map on both sides), then
`applyHoist_run` at it.  Round 7 skeletonised it: what it rests on is those
two, and `PinsOK s` is new — `isNatOpRecord` reads the pinned operation names
(`natDivModNames`/`natOpNames` are pin reads), so without it the twin's
target map is not con-leche's. -/
theorem hoistNatOpGround_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s)
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
  rw [hoistNatOpGround] at hrun
  rw [ConLeche.Frontend.hoistNatOpGround]
  obtain ⟨target, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hstep, rfl⟩ := hoistTargets_run hok hoff hpins hwf hnds hds h1
  have hds1 := denoteDeclArray_ext hstep.ext hds
  have hnds1 := hnds.mono hstep.ext
  by_cases he : (ConLeche.Frontend.hoistTargets dsP).isEmpty = true
  · rw [if_pos he] at hrun
    rw [if_pos he]
    obtain ⟨hv, rfl⟩ := AM.pure_ok hrun
    injection hv with h1 h2
    subst h1; subst h2
    exact ⟨hstep, hpds, hnds1, hds1, rfl⟩
  · rw [if_neg he] at hrun
    rw [if_neg he]
    obtain ⟨hv, rfl⟩ := AM.pure_ok hrun
    obtain ⟨h1, h2, h3, h4⟩ := applyHoist_run hds1 hpds hnds1 (ConLeche.Frontend.hoistTargets dsP)
    rw [← hv] at h1 h2 h3 h4
    exact ⟨hstep, h1, h2, h3, h4⟩

/-! ## The prepared stream -/

/-- con-leche: ConLeche/Frontend/Prepare.lean:171 preparePrelude — **the
prepared stream denotes con-leche's prepared stream**, which is the second
half of what the capstone's chain needs: the parse's exactness gets the
records, and this carries them across the two permuting passes into the
fold's argument.

`frontOf_run` and `hoistNatOpGround_run` composed. -/
theorem preparePrelude_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) {pre : PreludeIx}
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
    hoistNatOpGround_run hstep1.ok (by rw [hstep1.scratch]; exact hoff)
      (hpins.mono hstep1.ext hstep1.pins) hstep1.ok.wf
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
    (hoff : s.store.scratchOn = false) (hpins : PinsOK s) {pre : PreludeIx}
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
    preparePrelude_run hok hoff hpins hpre hprep hnpre hds hpds hnds hrun
  exact ⟨_, hout, ConLeche.Frontend.mem_preparePrelude hmem⟩

end ConRon.Bridge.Frontend
