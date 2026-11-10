/-
# `ConRon.Bridge.Checker.Inv` — the invariant a check runs from, and the declaration layer across a drop

Two things this tier needs that neither `Bridge/StateOK.lean` nor
`Bridge/Rel.lean` has.

**1. The declaration layer transports across a `PExt`**, not only across an
`Ext`.  `Bridge/Rel.lean`'s `denote*_ext` lemmas carry a stored constant past
an *append*; a worker carries the stream's index and records past a *drop*,
which is a weaker extension (`Bridge/Pers.lean`) available only at persistent
handles.  So each gets a `…_pext` twin with a `Pers…` hypothesis.

**2. `FoldOK` — the invariant a declaration's check runs from.**
`Bridge/StateOK.lean`'s `CheckOK` is the CORE tier's invariant (the store, the
fourteen caches, the pins, the index); a declaration's check needs a few
clauses more:

* `EnvWF env` — con-leche's own environment well-formedness, which
  `Verify/Cached/BridgeC.lean`'s `checkDeclStepC_run` takes as `henv` and
  `Bridge/Core`'s `knot_spec` takes for the same reason;
* `IFEnvCoh fe` — the own index is its list's index, con-leche's `fe' = mkFEnv
  fe'.env` for the layer above the frozen one;
* `TblGate fe` — no table without its structure, which is what lets a push of a
  fresh name keep the index spec (`IFEnvOK.pushStored`);
* `PersPins s` — the pin table is persistent.

What a lookup answers is `IFEnvOK`'s, stated by lookups: the frozen layer has
no list to denote.
-/
module

public import ConRon.Bridge.EnvDenote
public import ConRon.Bridge.StateOK
public import ConLeche.Verify.EnvWF
import ConRon.Bridge.EnvDenote

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## Two denotation facts the whole tier uses

Both are facts about the READBACK rather than about `CheckerBase`, so they
live here, where `Bridge/Checker/Canon.lean` — a sibling of `Base.lean`, not a
consumer of it — can see them too. -/

/-- con-leche: none — **a handle comparison is a name comparison**, at two
handles that denote.  The `→` half is `denoteN`'s functionality and the `←`
half is its injectivity (DESIGN §8.3's soundness obligation); every pinned-name
test of the declaration checker cashes this. -/
theorem beq_handle_iff {st : EStore} (hwf : StoreWF st) {n p : NIdx}
    {nm x : ConLeche.Name} (hn : denoteN st.ns n = some nm)
    (hp : denoteN st.ns p = some x) : (n == p) = true ↔ nm = x := by
  obtain ⟨rk, hrk⟩ := hwf
  constructor
  · intro h
    obtain rfl := eq_of_beq h
    rw [hn] at hp
    exact Option.some.inj hp
  · intro h
    subst h
    exact beq_iff_eq.mpr (denoteN_inj hrk.nsWF hn hp)

/-! ## The constant header's denotation, inverted -/

/-- con-leche: none — `Frontend.denoteCV`'s inversion: the three fields denote
the three fields. -/
theorem denoteCV_inv {st : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) :
    denoteN st.ns cv.name = some c.name ∧
      Frontend.denoteNList st.ns cv.levelParams = some c.levelParams ∧
      denoteE st cv.type = some c.type := by
  simp only [Frontend.denoteCV] at h
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at h; exact absurd h (by simp)
  | some n =>
    cases hl : Frontend.denoteNList st.ns cv.levelParams with
    | none => rw [hn, hl] at h; exact absurd h (by simp)
    | some lps =>
      cases ht : denoteE st cv.type with
      | none => rw [hn, hl, ht] at h; exact absurd h (by simp)
      | some ty =>
        rw [hn, hl, ht] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩

/-! ## The four handle kinds across a `PExt` -/

theorem denoteN_pext {st st' : EStore} (hx : PExt st st') {n : NIdx}
    {x : ConLeche.Name} (hp : PersN n) (h : denoteN st.ns n = some x) :
    denoteN st'.ns n = some x := hx.lss.ls.ns n x hp h

theorem denoteL_pext {st st' : EStore} (hx : PExt st st') {l : LIdx} {u : Level}
    (hp : PersL l) (h : denoteL st.ls l = some u) : denoteL st'.ls l = some u :=
  hx.lss.ls.lvl l u hp h

theorem denoteLs_pext {st st' : EStore} (hx : PExt st st') {l : LsIdx}
    {us : List Level} (hp : PersLs l) (h : denoteLs st.lss l = some us) :
    denoteLs st'.lss l = some us := hx.lss.lst l us hp h

theorem denoteE_pext {st st' : EStore} (hx : PExt st st') {i : EIdx} {e : Expr}
    (hp : PersE i) (h : denoteE st i = some e) : denoteE st' i = some e :=
  hx.expr i e hp h

/-! ## The three handle LISTS -/

theorem denoteNList_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name), PersNList ns →
      Frontend.denoteNList st.ns ns = some xs →
        Frontend.denoteNList st'.ns ns = some xs := by
  intro ns
  induction ns with
  | nil => intro xs _ h; exact h
  | cons a as ih =>
    intro xs hp h
    simp only [Frontend.denoteNList] at h ⊢
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteN_pext hx (hp a (by simp)) ha,
          ih ys (fun c hc => hp c (by simp [hc])) has]
        exact h

theorem denoteEList_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (es : List EIdx) (xs : List Expr), PersEList es →
      Frontend.denoteEList st es = some xs →
        Frontend.denoteEList st' es = some xs := by
  intro es
  induction es with
  | nil => intro xs _ h; exact h
  | cons a as ih =>
    intro xs hp h
    simp only [Frontend.denoteEList] at h ⊢
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteE_pext hx (hp a (by simp)) ha,
          ih ys (fun c hc => hp c (by simp [hc])) has]
        exact h

/-! ## The declaration layer -/

theorem denoteCV_pext {st st' : EStore} (hx : PExt st st') {cv : IConstantVal}
    {c : ConstantVal} (hp : PersCV cv) (h : Frontend.denoteCV st cv = some c) :
    Frontend.denoteCV st' cv = some c := by
  simp only [Frontend.denoteCV] at h ⊢
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at h; simp at h
  | some n =>
    cases hlp : Frontend.denoteNList st.ns cv.levelParams with
    | none => rw [hn, hlp] at h; simp at h
    | some lps =>
      cases hty : denoteE st cv.type with
      | none => rw [hn, hlp, hty] at h; simp at h
      | some ty =>
        rw [hn, hlp, hty] at h
        rw [denoteN_pext hx hp.name hn, denoteNList_pext hx _ lps hp.levelParams hlp,
          denoteE_pext hx hp.type hty]
        exact h

theorem denoteFire_pext {st st' : EStore} (hx : PExt st st') {f : IRecRuleFire}
    {r : RecRuleFire} (hp : PersFire f) (h : Frontend.denoteFire st f = some r) :
    Frontend.denoteFire st' f = some r :=
  hx.denoteFire hp r h

theorem denoteRule_pext {st st' : EStore} (hx : PExt st st') {rl : IRecRule}
    {r : RecRule} (hp : PersRule rl) (h : Frontend.denoteRule st rl = some r) :
    Frontend.denoteRule st' rl = some r := by
  simp only [Frontend.denoteRule] at h ⊢
  cases hc : denoteN st.ns rl.ctor with
  | none => rw [hc] at h; simp at h
  | some c =>
    cases hf : Frontend.denoteFire st rl.fire with
    | none => rw [hc, hf] at h; simp at h
    | some f =>
      cases hr : denoteE st rl.rhs with
      | none => rw [hc, hf, hr] at h; simp at h
      | some x =>
        rw [hc, hf, hr] at h
        rw [denoteN_pext hx hp.ctor hc, denoteFire_pext hx hp.fire hf,
          denoteE_pext hx hp.rhs hr]
        exact h

theorem denoteRules_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (rs : List IRecRule) (xs : List RecRule), PersRules rs →
      Frontend.denoteRules st rs = some xs →
        Frontend.denoteRules st' rs = some xs := by
  intro rs
  induction rs with
  | nil => intro xs _ h; exact h
  | cons a as ih =>
    intro xs hp h
    simp only [Frontend.denoteRules] at h ⊢
    cases ha : Frontend.denoteRule st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteRules st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteRule_pext hx (hp a (by simp)) ha,
          ih ys (fun c hc => hp c (by simp [hc])) has]
        exact h

theorem denoteCaps_pext {st st' : EStore} (hx : PExt st st') {c : IIndCaps}
    {x : IndCaps} (hp : PersCaps c) (h : Frontend.denoteCaps st c = some x) :
    Frontend.denoteCaps st' c = some x := by
  simp only [Frontend.denoteCaps] at h ⊢
  · cases ha : Frontend.denoteNList st.ns c.all with
    | none => rw [ha] at h; simp at h
    | some all =>
      cases hk : Frontend.denoteNList st.ns c.ctors with
      | none => rw [ha, hk] at h; simp at h
      | some ks =>
        rw [ha, hk] at h
        rw [denoteNList_pext hx _ _ hp.all ha, denoteNList_pext hx _ _ hp.ctors hk]
        exact h

theorem denoteProjTable_pext {st st' : EStore} (hx : PExt st st')
    {t : IProjTable} {x : ProjTable} (hp : PersProjTable t)
    (h : Frontend.denoteProjTable st t = some x) :
    Frontend.denoteProjTable st' t = some x :=
  hx.denoteProjTable hp x h

theorem denoteCI_pext {st st' : EStore} (hx : PExt st st') {ci : IConstantInfo}
    {c : ConstantInfo} (hp : PersCI ci) (h : Frontend.denoteCI st ci = some c) :
    Frontend.denoteCI st' ci = some c := by
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_pext hx hp hcv, hc⟩
  | ctorInfo v nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_pext hx hp hcv, hc⟩
  | defnInfo v e hint =>
    simp only [Frontend.denoteCI] at h ⊢
    obtain ⟨hpv, hpe⟩ := hp
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        rw [denoteCV_pext hx hpv hcv, denoteE_pext hx hpe he]; exact h
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_pext hx hp hcv, hc⟩
  | indInfo v c' =>
    simp only [Frontend.denoteCI] at h ⊢
    obtain ⟨hpv, hpc⟩ := hp
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hcp : Frontend.denoteCaps st c' with
      | none => rw [hcv, hcp] at h; simp at h
      | some caps =>
        rw [hcv, hcp] at h
        rw [denoteCV_pext hx hpv hcv, denoteCaps_pext hx hpc hcp]; exact h
  | recInfo v mI rP k rs =>
    simp only [Frontend.denoteCI] at h ⊢
    obtain ⟨hpv, hpr⟩ := hp
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hrs : Frontend.denoteRules st rs with
      | none => rw [hcv, hrs] at h; simp at h
      | some rules =>
        rw [hcv, hrs] at h
        rw [denoteCV_pext hx hpv hcv, denoteRules_pext hx _ rules hpr hrs]
        exact h

theorem denoteCIList_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (cs : List IConstantInfo) (xs : List ConstantInfo), PersCIList cs →
      Frontend.denoteCIList st cs = some xs →
        Frontend.denoteCIList st' cs = some xs := by
  intro cs
  induction cs with
  | nil => intro xs _ h; exact h
  | cons a as ih =>
    intro xs hp h
    simp only [Frontend.denoteCIList] at h ⊢
    cases ha : Frontend.denoteCI st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteCIList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteCI_pext hx (hp a (by simp)) ha,
          ih ys (fun c hc => hp c (by simp [hc])) has]
        exact h

/-! ## The pin table survives the drop -/

theorem denoteNL_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name), PersNList hs →
      denoteNL st hs xs → denoteNL st' hs xs := by
  intro hs
  induction hs with
  | nil => intro xs _ h; cases xs <;> exact h
  | cons a as ih =>
    intro xs hp h
    cases xs with
    | nil => exact h
    | cons y ys =>
      obtain ⟨h1, h2⟩ := h
      exact ⟨denoteN_pext hx (hp a (by simp)) h1,
        ih ys (fun c hc => hp c (by simp [hc])) h2⟩

/-- con-leche: none — **`PinsOK` survives `dropScratch`**, given one more
clause: the pin handles are persistent (`PersPins`). -/
theorem PinsOK.pmono {s s' : AState} (h : PinsOK s) (hp : PersPins s)
    (hx : PExt s.store s'.store) (hpe : s'.pins = s.pins) : PinsOK s' where
  ready := by rw [hpe]; exact h.ready
  names := by
    rw [hpe]
    exact denoteNL_pext hx _ pinNames
      (fun n hn => hp.names n (by simpa using hn)) h.names
  reserved := by
    rw [hpe]; exact denoteNL_pext hx _ reservedBasisNameValues hp.reserved h.reserved
  emptyLevels := by rw [hpe]; exact denoteLs_pext hx hp.emptyLevels h.emptyLevels
  zeroLevel := by rw [hpe]; exact denoteL_pext hx hp.zeroLevel h.zeroLevel
  sortOne := by rw [hpe]; exact denoteE_pext hx hp.sortOne h.sortOne
  anon := denoteN_pext hx (by decide) h.anon

theorem PersPins.mono {s s' : AState} (h : PersPins s) (hpe : s'.pins = s.pins) :
    PersPins s' where
  names := by rw [hpe]; exact h.names
  reserved := by rw [hpe]; exact h.reserved
  emptyLevels := by rw [hpe]; exact h.emptyLevels
  zeroLevel := by rw [hpe]; exact h.zeroLevel
  sortOne := by rw [hpe]; exact h.sortOne

/-! ## The declaration STREAM

`denoteDecl` is `Arena/Frontend/Readback.lean`'s; the list lift is not, and
the fold needs it — it is the left-hand side of DESIGN §8.2's parser-tier
statement (`denoteDecls (Arena.parse chunks) = parseChunks chunks`), which the
frontend tier will state against this definition. -/

/-- con-leche: none — the denotation of a declaration STREAM, record by
record.  DESIGN §8.2's `denoteDecls`. -/
@[expose] def denoteDecls (st : EStore) : List IDeclaration → Option (List Declaration)
  | [] => some []
  | d :: ds =>
    match Frontend.denoteDecl st d, denoteDecls st ds with
    | some x, some xs => some (x :: xs)
    | _, _ => none

theorem denoteDecl_pext {st st' : EStore} (hx : PExt st st') {pd : IDeclaration}
    {d : Declaration} (hp : PersDecl pd)
    (h : Frontend.denoteDecl st pd = some d) :
    Frontend.denoteDecl st' pd = some d := by
  cases pd with
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_pext hx hp hcv, hc⟩
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_pext hx hp hcv, hc⟩
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b, hb, hc⟩ := h
    exact ⟨b, denoteCIList_pext hx _ b hp hb, hc⟩
  | defnDecl v e hint =>
    simp only [Frontend.denoteDecl] at h ⊢
    obtain ⟨hpv, hpe⟩ := hp
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        rw [denoteCV_pext hx hpv hcv, denoteE_pext hx hpe he]; exact h
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at h ⊢
    obtain ⟨hpv, hpe⟩ := hp
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        rw [denoteCV_pext hx hpv hcv, denoteE_pext hx hpe he]; exact h
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at h ⊢
    obtain ⟨hpv, hpe⟩ := hp
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        rw [denoteCV_pext hx hpv hcv, denoteE_pext hx hpe he]; exact h

/-- con-leche: none — the stream's denotation survives a drop, record by
record, which is what lets the FOLD state its hypothesis once at the start
instead of once per step. -/
theorem denoteDecls_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (ds : List IDeclaration) (xs : List Declaration),
      (∀ d ∈ ds, PersDecl d) → denoteDecls st ds = some xs →
        denoteDecls st' ds = some xs := by
  intro ds
  induction ds with
  | nil => intro xs _ h; exact h
  | cons a as ih =>
    intro xs hp h
    simp only [denoteDecls] at h ⊢
    cases ha : Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteDecl_pext hx (hp a (by simp)) ha,
          ih ys (fun c hc => hp c (by simp [hc])) has]
        exact h

/-! ## The declaration layer across an APPEND

`Bridge/Rel.lean` stops at `denoteCI_ext`; the fold and the arms need the list
and the environment too.  Named `…_mono` rather than `…_ext` because
`Bridge/Inductives/Rel.lean` has its own `denoteCIList_mono` / `denoteFEnv_mono`
in a namespace that opens this one, and two equally-reachable names of the
same spelling are an ambiguity error rather than a shadowing. -/

/-! ## The index spec across a drop

`IFEnvOK.mono` (`Bridge/StateOK.lean`) carries the index spec across an
APPEND.  The fold needs it across a `dropScratch`, and `PersIFEnv` is exactly
what makes that work: every handle the index mentions — the key and the
constant — is persistent, so both halves of the spec transport by the `…_pext`
lemmas above. -/

/-! ## What a lookup reads

`IFEnv.find?` reads the own index, then the frozen layer (`IFEnv.lookup`; an
empty own index is not hashed into, which answers the same).  So a push answers
at its own name and passes every other name through, whatever the index
held — no coherence with the list is needed for that, unlike con-leche's
`mkFEnv_find?`. -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:98-105 FEnv.lookup — the emptiness test
answers what the hash map answers. -/
theorem IFEnv.find?_eq (fe : IFEnv) (n : NIdx) :
    fe.find? n = match fe.idx[n]? with
      | some ci => some ci
      | none => fe.base.find? n := by
  simp only [IFEnv.find?, IFEnv.lookup]
  split
  · rename_i he
    rw [Std.HashMap.isEmpty_iff_forall_not_mem] at he
    have : fe.idx[n]? = none := Std.HashMap.getElem?_eq_none (he n)
    rw [this]
  · rfl

/-- con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push — **a push answers at
its own name and nowhere else**. -/
theorem IFEnv.find?_push (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) :
    (fe.push ci).find? n = if (ci.name == n) = true then some ci else fe.find? n := by
  rw [IFEnv.find?_eq, IFEnv.find?_eq]
  simp only [IFEnv.push, Std.HashMap.getElem?_insert]
  by_cases hb : (ci.name == n) = true <;> simp [hb]

/-- con-leche: ConLeche/Kernel/FEnv.lean:163-167 FEnv.findTable? — **no table
without its structure**: a raw table hit is at a stored name.  `findTable?`'s
gate is then never what hides a table, so a push of a fresh name opens no stale
table.  The stream's index has it because a record's tables are named after its
own constants (upstream's `declTables_sublist`), and a block installs its tables
after its constants. -/
@[expose] def TblGate (fe : IFEnv) : Prop :=
  ∀ n t, fe.rawTable? n = some t → (fe.find? n).isSome = true

/-- con-leche: none — a push keeps the gate. -/
theorem TblGate.push {fe : IFEnv} (h : TblGate fe) (ci : IConstantInfo) :
    TblGate (fe.push ci) := by
  intro n t ht
  rw [IFEnv.find?_push]
  split
  · rfl
  · exact h n t ht

/-! ## The two invariants, and the rule that separates them

**`StepOK` is the invariant at an index a step has just EXTENDED; `FoldOK` is
the invariant at a fold-step BOUNDARY.**  A statement about "the invariant at
an index this step produced" (`IndSpec.run`, `checkDivModPin_bridge`,
`checkReducePin_bridge`) cannot say `FoldOK`: `FoldOK` carries `PersIFEnv`,
which is FALSE of an index extended inside the scratch bracket — the constant
it holds carries a freshly interned, hence scratch, type.  Persistence is
`promoteNew`'s, one level up.

Splitting the record makes the rule greppable rather than remembered:

> **`FoldOK` may appear in a CONCLUSION only at a fold-step boundary.**
> Anything a `checkDecl`-level theorem says about an index it has just
> produced is `StepOK`.

`FoldOK` as a *hypothesis* is correct and ubiquitous — every theorem of this
tier runs from a boundary — so the rule is about the right-hand side of a `:`
and about `DeclOut`-shaped records, and nothing else.

**Why `StepOK` carries `IFEnvOK` and not `CheckOK`.**  `CheckOK` carries
`CacheOK false env s`, the fourteen caches read AT an environment, and an
install grows the environment: the entries a `whnf`/`infer`/`defeq` cache
holds were computed at `env` and say nothing at `env.push c`.  That is
precisely why `checkDeclStep`'s bracket OPENS with `flushCaches`.  So a value
check that has just installed a constant cannot hand back `CheckOK` at the
extended environment and must not claim to; what it does know is the four
clauses below, and the invariant at the pre-insertion environment — which it
hands back separately, as `CoreStep env fe s s'`.  Putting `CheckOK` in
`StepOK` would be the `PersIFEnv` defect again, one field over. -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK
con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**what a step knows about an index it has just extended**: the index answers
its environment's `find?`, the environment is well formed, the own index is its
list's index, and no table is without its structure.

Nothing here is about the STATE's own invariant (that is `CheckOK`, at the
environment the core ran at). -/
structure StepOK (env : Env) (fe : IFEnv) (s : AState) : Prop where
  ienv : IFEnvOK env fe s
  envWF : EnvWF env
  coh : IFEnvCoh fe
  gate : TblGate fe

/-- con-leche: none — `StepOK` transports across an append: `IFEnvOK.mono`
carries the store clause, the other three mention no store. -/
theorem StepOK.mono {env : Env} {fe : IFEnv} {s s' : AState}
    (h : StepOK env fe s) (hx : Ext s.store s'.store) : StepOK env fe s' where
  ienv := h.ienv.mono hx
  envWF := h.envWF
  coh := h.coh
  gate := h.gate

/-! ## The fold-step invariant -/

/-- con-leche: ConLeche/Verify/Cached/SimC.lean:262 CSOK
con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run
**the invariant a declaration's check runs from**: the Core tier's `CheckOK`,
the environment well formed, the own index its list's index (con-leche's
`fe = mkFEnv fe.env`, for the layer above the frozen one), no table without its
structure, and the pin table persistent. -/
structure FoldOK (env : Env) (fe : IFEnv) (s : AState) :
    Prop where
  check : CheckOK false env fe s
  envWF : EnvWF env
  /-- every table of the own index's list is well shaped -/
  tblShape : ∀ t ∈ fe.env.tables, IProjTableOK t
  persPins : PersPins s
  coh : IFEnvCoh fe
  gate : TblGate fe

/-- con-leche: none — a boundary is a step: the four `StepOK` clauses are
`FoldOK`'s own, `IFEnvOK` read off `CheckOK`.  This is what a theorem whose
hypothesis is `FoldOK` passes to one whose hypothesis is `StepOK`.

(`FoldOK.step` is taken — `Bridge/Checker/Arms.lean` uses it for "carry
`FoldOK` across a step that only appends" — so this one is spelled the way
Lean spells a parent projection.) -/
theorem FoldOK.toStepOK {env : Env} {fe : IFEnv} {s : AState}
    (h : FoldOK env fe s) : StepOK env fe s where
  ienv := h.check.ienv
  envWF := h.envWF
  coh := h.coh
  gate := h.gate

/-- con-leche: none — **`FoldOK` survives a step that only appends and leaves
the environment alone.**  A step of an arm leaves `CheckOK` at the SAME
environment; the other clauses are about the environment index, which did not
move, and the pin handles, which did not either.

It lives here rather than in `Bridge/Checker/Arms.lean` because
`DeclVal.lean`'s `checkThmVal_bridge`, two modules lower, uses it. -/
theorem FoldOK.step {env : Env} {fe : IFEnv} {s s' : AState}
    (h : FoldOK env fe s) (hck : CheckOK false env fe s') (hp : s'.pins = s.pins) :
    FoldOK env fe s' where
  check := hck
  envWF := h.envWF
  tblShape := h.tblShape
  persPins := h.persPins.mono hp
  coh := h.coh
  gate := h.gate

/-! ## The index spec across a PUSH

`StepOK.mono` and `StepOK.pmono` carry the invariant across a change of STORE
at a fixed environment.  The three value checks change the ENVIRONMENT
instead: each ends in `IFEnv.push`, and what it owes its caller is `StepOK` at
the cons.  The two lemmas below are that — the third and fourth members of the
`IFEnv.push` family, beside `Pushed.push` and `IFEnvCoh.push`
(`Bridge/Promote/Exact.lean`).

**One theorem pays for `EnvWF` at every value install.**  `StepOK` carries
`EnvWF env`; con-leche does not prove that `checkDefnVal` preserves it
(`Verify/BridgeWfImp.lean`'s `checkDefnVal_wfimp` is about the fuel family, and
the model tier takes `EnvWF` as a hypothesis rather than re-establishing it),
so the arena tier owes `ConstWF ⟨c :: env.consts, env.tables⟩ c` at every value install.
It is owed once and paid once: `StepOK.push` takes it as a hypothesis and
`Bridge/Checker/DeclVal.lean`'s three `constWF_*` discharge it from the guards
the run has already passed. -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index spec survives a
push.**  `(fe.push ci).find? n` answers at the new name and passes every other
through (`IFEnv.find?_push`), con-leche's side is `Env.find?_cons`, and the two negative cases are `denoteN_inj` — a handle the
pushed key is not cannot denote the pushed constant's name, because the two
handles would then be equal.

A push touches neither the table maps nor the environment's tables, but it
opens both table gates at the new name: `hA`/`hB` are the raw lookups there,
side by side (`IFEnvOK.pushStored` discharges them). -/
theorem IFEnvOK.push {env : Env} {fe : IFEnv} {s : AState}
    {ci : IConstantInfo} {c : ConstantInfo}
    (h : IFEnvOK env fe s) (hst : StateOK s)
    (hci : Frontend.denoteCI s.store ci = some c)
    (hA : ∀ t, fe.rawTable? ci.name = some t → ∃ pt,
      Frontend.denoteProjTable s.store t = some pt ∧
      env.tables.find? (·.structName == c.name) = some pt ∧ IProjTableOK t)
    (hB : ∀ pt, env.tables.find? (·.structName == c.name) = some pt → ∃ t,
      fe.rawTable? ci.name = some t ∧ Frontend.denoteProjTable s.store t = some pt) :
    IFEnvOK ⟨c :: env.consts, env.tables⟩ (fe.push ci) s := by
  obtain ⟨rk, hrk⟩ := hst.wf
  have hnm : denoteN s.store.ns ci.name = some c.name := denoteCI_name hci
  -- the pushed index, as a `List.find?` on a cons
  have keyE : ∀ n : NIdx, (fe.push ci).find? n
      = if (ci.name == n) = true then some ci else fe.find? n := by
    intro n
    exact IFEnv.find?_push fe ci n
  have keyT : (fe.push ci).find? ci.name = some ci := by rw [keyE]; simp
  have keyF : ∀ n : NIdx, (ci.name == n) = false →
      (fe.push ci).find? n = fe.find? n := by
    intro n hb; rw [keyE, hb]; simp
  -- the table lookups: the gate opens at the new name, the raw lookups stay
  have keyTb : ∀ n : NIdx, (fe.push ci).findTable? n
      = if (ci.name == n) = true then fe.rawTable? ci.name else fe.findTable? n := by
    intro n
    cases hb : (ci.name == n) with
    | true =>
      have hn : ci.name = n := by simpa using hb
      subst hn
      simp only [IFEnv.findTable?, keyT, Option.isSome_some, ↓reduceIte]
      rfl
    | false =>
      simp only [IFEnv.findTable?, keyF n hb, Bool.false_eq_true, ↓reduceIte]
      rfl
  have keyEnvT : ∀ nm : ConLeche.Name,
      (⟨c :: env.consts, env.tables⟩ : Env).findTable? nm
        = if c.name = nm then env.tables.find? (·.structName == c.name)
          else env.findTable? nm := by
    intro nm
    unfold Env.findTable?
    rw [Env.find?_cons]
    by_cases hq : c.name = nm
    · subst hq
      simp only [Option.isSome_some, ↓reduceIte]
    · simp only [hq, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `hit`
    intro n ci' hf
    cases hb : (ci.name == n) with
    | true =>
      obtain rfl : ci.name = n := by simpa using hb
      rw [keyT] at hf
      obtain rfl : ci' = ci := (Option.some.inj hf).symm
      exact ⟨_, _, hnm, hci, Env.find?_cons_self _ env⟩
    | false =>
      rw [keyF n hb] at hf
      obtain ⟨nm, c', hd, hc', he⟩ := h.hit n ci' hf
      refine ⟨nm, c', hd, hc', ?_⟩
      rw [Env.find?_cons, ite_eq_right, he]
      intro hq
      obtain rfl := denoteN_inj hrk.nsWF (hq ▸ hnm) hd
      simp at hb
  · -- `cover`
    intro nm c₀ he
    rw [Env.find?_cons] at he
    by_cases hq : c.name = nm
    · rw [ite_eq_left hq] at he
      obtain rfl : c₀ = c := (Option.some.inj he).symm
      exact ⟨ci.name, ci, hq ▸ hnm, keyT, hci⟩
    · rw [ite_eq_right hq] at he
      obtain ⟨n, ci', hd, hf, hc'⟩ := h.cover nm c₀ he
      refine ⟨n, ci', hd, ?_, hc'⟩
      cases hb : (ci.name == n) with
      | true =>
        obtain rfl : ci.name = n := by simpa using hb
        rw [hnm] at hd
        exact absurd (Option.some.inj hd) hq
      | false => rw [keyF n hb]; exact hf
  · -- `tblHit`
    intro n t hf
    rw [keyTb] at hf
    cases hb : (ci.name == n) with
    | true =>
      rw [hb] at hf
      simp only [↓reduceIte] at hf
      obtain rfl : ci.name = n := by simpa using hb
      obtain ⟨pt, hp, he, hk⟩ := hA t hf
      refine ⟨c.name, pt, hnm, hp, ?_, hk⟩
      rw [keyEnvT]; simpa using he
    | false =>
      rw [hb] at hf
      simp only [Bool.false_eq_true, ↓reduceIte] at hf
      obtain ⟨nm, pt, hd, hp, he, hk⟩ := h.tblHit n t hf
      refine ⟨nm, pt, hd, hp, ?_, hk⟩
      rw [keyEnvT, ite_eq_right, he]
      intro hq
      obtain rfl := denoteN_inj hrk.nsWF (hq ▸ hnm) hd
      simp at hb
  · -- `tblCover`
    intro nm pt he
    rw [keyEnvT] at he
    by_cases hq : c.name = nm
    · rw [ite_eq_left hq] at he
      subst hq
      obtain ⟨t, hr, hp⟩ := hB pt he
      exact ⟨ci.name, t, hnm, by rw [keyTb]; simpa using hr, hp⟩
    · rw [ite_eq_right hq] at he
      obtain ⟨n, t, hd, hf, hp⟩ := h.tblCover nm pt he
      refine ⟨n, t, hd, ?_, hp⟩
      rw [keyTb]
      cases hb : (ci.name == n) with
      | true =>
        obtain rfl : ci.name = n := by simpa using hb
        rw [hnm] at hd
        exact absurd (Option.some.inj hd) hq
      | false => simpa using hf

/-- con-leche: none — a denoting table's key denotes its structure's name. -/
theorem denoteProjTable_structName {st : EStore} {t : IProjTable} {pt : ProjTable}
    (h : Frontend.denoteProjTable st t = some pt) :
    denoteN st.ns t.structName = some pt.structName := by
  simp only [Frontend.denoteProjTable] at h
  split at h
  · rename_i sn lps c hsn _ _
    split at h
    · cases h; exact hsn
    · cases h
  · cases h

/-- con-leche: ConLeche/Verify/EnvWF.lean:161-162 TableWF — every stored table
belongs to a stored structure: `TableWF`'s first clause alone, which is what the
push of a fresh constant reads and what the basis install keeps without
`EnvWF`. -/
def TablesStored (env : Env) : Prop :=
  ∀ pt ∈ env.tables, (env.find? pt.structName).isSome = true

/-- con-leche: ConLeche/Verify/EnvWF.lean:161-162 TableWF — off `EnvWF`. -/
theorem TablesStored.of_envWF {env : Env} (h : EnvWF env) : TablesStored env :=
  fun pt hp => (h.tables pt hp).1

/-- con-leche: none — a pushed constant keeps every structure stored. -/
theorem TablesStored.cons {env : Env} {c : ConstantInfo} (h : TablesStored env) :
    TablesStored ⟨c :: env.consts, env.tables⟩ := by
  intro pt hp
  rw [Env.find?_cons]
  split
  · rfl
  · exact h pt hp

/-- con-leche: none — **`IFEnvOK` survives any push** once every con-leche
table belongs to a stored structure (`TablesStored`, `TableWF`'s first
clause).  At a name the index already holds, both gates are open already and
the new name's raw lookups are the old visible ones (`IFEnvOK.tblHit`,
`tblCover`); at a fresh name con-leche has no table (`TablesStored`) and the
arena none either, because no table is without its structure (`TblGate`). -/
theorem IFEnvOK.pushStored {env : Env} {fe : IFEnv} {s : AState}
    {ci : IConstantInfo} {c : ConstantInfo}
    (h : IFEnvOK env fe s) (hst : StateOK s) (hgate : TblGate fe)
    (hstored : TablesStored env)
    (hci : Frontend.denoteCI s.store ci = some c) :
    IFEnvOK ⟨c :: env.consts, env.tables⟩ (fe.push ci) s := by
  obtain ⟨rk, hrk⟩ := hst.wf
  have hnm := denoteCI_name hci
  cases hfi : fe.find? ci.name with
  | none =>
    have hfresh : env.find? c.name = none := IFEnvOK.miss hst h hnm hfi
    have htab : env.tables.find? (·.structName == c.name) = none := by
      cases hf : env.tables.find? (·.structName == c.name) with
      | none => rfl
      | some pt =>
        have hn : pt.structName = c.name := by simpa using List.find?_some hf
        have hg := hstored pt (List.mem_of_find?_eq_some hf)
        rw [hn, hfresh] at hg
        cases hg
    have hraw : fe.rawTable? ci.name = none := by
      cases hf : fe.rawTable? ci.name with
      | none => rfl
      | some t =>
        have := hgate _ t hf
        rw [hfi] at this
        cases this
    refine h.push hst hci (fun t ht => ?_) (fun pt hp => ?_)
    · rw [hraw] at ht; cases ht
    · rw [htab] at hp; cases hp
  | some ci₀ =>
    -- both gates are open at the name already
    obtain ⟨nm, c₀, hd, -, he⟩ := h.hit _ ci₀ hfi
    rw [hnm] at hd
    obtain rfl := Option.some.inj hd
    have gA : fe.findTable? ci.name = fe.rawTable? ci.name := by
      simp only [IFEnv.findTable?, hfi, Option.isSome_some, ↓reduceIte]
    have gB : env.findTable? c.name = env.tables.find? (·.structName == c.name) := by
      simp only [Env.findTable?, he, Option.isSome_some, ↓reduceIte]
    refine h.push hst hci (fun t ht => ?_) (fun pt hp => ?_)
    · rw [← gA] at ht
      obtain ⟨nm', pt, hd', hp, he', hk⟩ := h.tblHit _ t ht
      rw [hnm] at hd'
      obtain rfl := Option.some.inj hd'
      exact ⟨pt, hp, gB ▸ he', hk⟩
    · rw [← gB] at hp
      obtain ⟨n, t, hd', hf, hp'⟩ := h.tblCover _ pt hp
      obtain rfl := denoteN_inj hrk.nsWF hd' hnm
      exact ⟨t, gA ▸ hf, hp'⟩

/-- con-leche: ConLeche/Verify/EnvWF.lean:406 EnvWF.cons — **`StepOK` survives
a push**, which is what each of the three value checks
concludes.  Three of the four clauses are push lemmas (above, and in
`Bridge/Promote/Exact.lean`); the fourth is `EnvWF.cons`, and its `ConstWF`
premise is the one thing con-leche does not prove about the value checks (see
the section note). -/
theorem StepOK.push {env : Env} {fe : IFEnv} {s : AState}
    {ci : IConstantInfo} {c : ConstantInfo}
    (h : StepOK env fe s) (hst : StateOK s)
    (hci : Frontend.denoteCI s.store ci = some c)
    (hs : litShapeOk c = true) (hcw : ConstWF ⟨c :: env.consts, env.tables⟩ c) :
    StepOK ⟨c :: env.consts, env.tables⟩ (fe.push ci) s where
  ienv := h.ienv.pushStored hst h.gate (TablesStored.of_envWF h.envWF) hci
  envWF := EnvWF.cons hs h.envWF hcw
  coh := h.coh.push ci
  gate := h.gate.push ci

end ConRon.Bridge
