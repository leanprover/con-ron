/-
# `ConRon.Bridge.Checker.Inv` — the fold's invariant, and the declaration layer across a drop

Two things this tier needs that neither `Bridge/StateOK.lean` nor
`Bridge/Rel.lean` has.

**1. The declaration layer transports across a `PExt`**, not only across an
`Ext`.  `Bridge/Rel.lean`'s ten `denote*_ext` lemmas carry a stored constant
past an *append*; the fold needs to carry it past a *drop*, which is a weaker
extension (`Bridge/Promote/Pers.lean`) available only at persistent handles.
So each of the ten gets a `…_pext` twin with a `Pers…` hypothesis, and the
pair is what the per-declaration bracket consumes: `Arena/Promote.lean` makes
the environment persistent, `PExt.dropScratch` carries it, and nothing the
fold can see changes.

**2. `FoldOK` — the fold-step invariant.**  `Bridge/StateOK.lean`'s `CheckOK`
is the CORE tier's invariant (the store, the fourteen caches, the pins, the
index); the fold needs three clauses more, and all three are about what
survives the next `dropScratch`:

* `denoteFEnv s.store fe = some env` — the environment index DENOTES, as a
  function.  `IFEnvOK` says what `find?` answers; `denoteFEnv` says what the
  whole environment is, and it is `denoteFEnv` that `ConLeche.checkDecl`'s
  statement names.  con-leche's own join point has exactly this pair
  (`CSOKF s'` and `fe' = mkFEnv fe'.env`, `Verify/Cached/BridgeC.lean:609`);
* `IFEnvCoh fe` — the index is its list's index, con-leche's `fe' = mkFEnv
  fe'.env` letter for letter;
* `PersIFEnv fe` and `PersPins s` — everything the step hands on is in the
  persistent tier.  Without these two the very next `dropScratch` makes the
  environment undecodable, and the fold's second declaration would have
  nothing to say;
* `EnvWF env` — con-leche's own environment well-formedness, which
  `Verify/Cached/BridgeC.lean:609`'s join point takes as `henv` and which
  `Bridge/Core`'s `knot_spec` takes for the same reason.  The Core tier's
  theorem is stated AT a well-formed environment, so the fold has to carry
  one.
-/
import ConRon.Bridge.Promote.Exact
import ConLeche.Verify.EnvWF

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

theorem denoteLList_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (ls : List LIdx) (us : List Level), PersLList ls →
      denoteLList st.ls ls = some us →
        denoteLList st'.ls ls = some us := by
  intro ls
  induction ls with
  | nil => intro us _ h; exact h
  | cons a as ih =>
    intro us hp h
    simp only [denoteLList] at h ⊢
    cases ha : denoteL st.ls a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : denoteLList st.ls as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteL_pext hx (hp a (by simp)) ha,
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

theorem denoteEArray_pext {st st' : EStore} (hx : PExt st st') {hs : Array EIdx}
    {xs : Array Expr} (hp : PersEList hs.toList)
    (h : Frontend.denoteEArray st hs = some xs) :
    Frontend.denoteEArray st' hs = some xs := by
  simp only [Frontend.denoteEArray] at h ⊢
  cases hl : Frontend.denoteEList st hs.toList with
  | none => rw [hl] at h; simp at h
  | some ys => rw [hl] at h; rw [denoteEList_pext hx _ ys hp hl]; exact h

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
    Frontend.denoteFire st' f = some r := by
  cases f with
  | plain => exact h
  | nested lvls pins =>
    simp only [Frontend.denoteFire] at h ⊢
    obtain ⟨hpl, hpe⟩ := hp
    cases hl : denoteLList st.ls lvls with
    | none => rw [hl] at h; simp at h
    | some ls =>
      cases he : Frontend.denoteEList st pins with
      | none => rw [hl, he] at h; simp at h
      | some ps =>
        rw [hl, he] at h
        rw [denoteLList_pext hx _ ls hpl hl, denoteEList_pext hx _ ps hpe he]
        exact h

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
  cases hn : denoteN st.ns c.etaCtor with
  | none => rw [hn] at h; simp at h
  | some ct =>
    rw [hn] at h; rw [denoteN_pext hx hp.etaCtor hn]
    cases ha : Frontend.denoteNList st.ns c.all with
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
    Frontend.denoteProjTable st' t = some x := by
  simp only [Frontend.denoteProjTable] at h ⊢
  cases hsn : denoteN st.ns t.structName with
  | none => rw [hsn] at h; simp at h
  | some sn =>
    cases hlp : Frontend.denoteNList st.ns t.levelParams with
    | none => rw [hsn, hlp] at h; simp at h
    | some lps =>
      cases hc : denoteN st.ns t.ctor with
      | none => rw [hsn, hlp, hc] at h; simp at h
      | some c =>
        rw [hsn, hlp, hc] at h
        rw [denoteN_pext hx hp.structName hsn,
          denoteNList_pext hx _ lps hp.levelParams hlp,
          denoteN_pext hx hp.ctor hc]
        cases hss : denoteL st.ls t.structSort with
        | none => rw [hss] at h; simp at h
        | some ss =>
          cases hb : Frontend.denoteEArray st t.bodies with
          | none => rw [hss, hb] at h; simp at h
          | some bs =>
            cases hg : denoteLList st.ls t.guards with
            | none => rw [hss, hb, hg] at h; simp at h
            | some gs =>
              rw [hss, hb, hg] at h
              rw [denoteL_pext hx hp.structSort hss,
                denoteEArray_pext hx hp.bodies hb,
                denoteLList_pext hx _ gs hp.guards hg]
              exact h

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
  | recInfo v mI rP rs =>
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

/-- con-leche: none — **the environment survives the drop**: the promoted
environment denotes the same `Env` after `dropScratch` as before it.  This is
the payoff of `Arena/Promote.lean` in one line, and the reason the fold has a
`PersIFEnv` clause at all. -/
theorem denoteProjTableList_pext {st st' : EStore} (hx : PExt st st') :
    ∀ (ts : List IProjTable) (xs : List ProjTable), (∀ t ∈ ts, PersProjTable t) →
      Frontend.denoteProjTableList st ts = some xs →
        Frontend.denoteProjTableList st' ts = some xs := by
  intro ts
  induction ts with
  | nil => intro xs _ h; exact h
  | cons a as ih =>
    intro xs hp h
    simp only [Frontend.denoteProjTableList] at h ⊢
    cases ha : Frontend.denoteProjTable st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteProjTableList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteProjTable_pext hx (hp a (by simp)) ha,
          ih ys (fun c hc => hp c (by simp [hc])) has]
        exact h

theorem denoteFEnv_pext {st st' : EStore} (hx : PExt st st') {fe : IFEnv}
    {env : Env} (hp : PersIFEnv fe) (h : denoteFEnv st fe = some env) :
    denoteFEnv st' fe = some env := by
  obtain ⟨h1, h2⟩ := denoteIEnv_some.mp h
  exact denoteIEnv_some.mpr
    ⟨denoteCIList_pext hx _ _ hp.env h1, denoteProjTableList_pext hx _ _ hp.tables h2⟩

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
def denoteDecls (st : EStore) : List IDeclaration → Option (List Declaration)
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
  | basisDecl k => exact h
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

/-- con-leche: none — the environment's denotation survives an append. -/
theorem denoteFEnv_mono {st st' : EStore} (hx : Ext st st') {fe : IFEnv}
    {env : Env} (h : denoteFEnv st fe = some env) :
    denoteFEnv st' fe = some env := by
  obtain ⟨h1, h2⟩ := denoteIEnv_some.mp h
  exact denoteIEnv_some.mpr
    ⟨denoteCIList_mono hx _ _ h1, denoteProjTableList_mono hx _ _ h2⟩

/-! ## The index spec across a drop

`IFEnvOK.mono` (`Bridge/StateOK.lean`) carries the index spec across an
APPEND.  The fold needs it across a `dropScratch`, and `PersIFEnv` is exactly
what makes that work: every handle the index mentions — the key and the
constant — is persistent, so both halves of the spec transport by the `…_pext`
lemmas above. -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index spec survives a
drop.**  Both clauses are a transport, and the persistence they need is
`PersIFEnv`'s row clause read through `PersIFEnv.find`
(`Bridge/Promote/Pers.lean`).

This is what `Bridge/Checker/Fold.lean`'s bracket uses to rebuild `CheckOK`
after the drop, and it is why `IFEnvOK_of_denote` below is NOT on the critical
path: `FoldOK.check.ienv` already carries the spec, so nothing has to
reconstruct it from the denotation. -/
theorem IFEnvOK.pmono {env : Env} {fe : IFEnv} {s s' : AState}
    (h : IFEnvOK env fe s) (hp : PersIFEnv fe) (hx : PExt s.store s'.store) :
    IFEnvOK env fe s' where
  hit := by
    intro n ci hf
    obtain ⟨hpn, hpci⟩ := hp.find hf
    obtain ⟨nm, c, h1, h2, h3⟩ := h.hit n ci hf
    exact ⟨nm, c, denoteN_pext hx hpn h1, denoteCI_pext hx hpci h2, h3⟩
  cover := by
    intro nm c hf
    obtain ⟨n, ci, h1, h2, h3⟩ := h.cover nm c hf
    obtain ⟨hpn, hpci⟩ := hp.find h2
    exact ⟨n, ci, denoteN_pext hx hpn h1, h2, denoteCI_pext hx hpci h3⟩
  tblHit := by
    intro n t hf
    obtain ⟨hpn, hpt⟩ := hp.rawTable (IFEnv.rawTable?_of_findTable? hf)
    obtain ⟨nm, pt, h1, h2, h3, h4⟩ := h.tblHit n t hf
    exact ⟨nm, pt, denoteN_pext hx hpn h1, denoteProjTable_pext hx hpt h2, h3, h4⟩
  tblCover := by
    intro nm pt hf
    obtain ⟨n, t, h1, h2, h3⟩ := h.tblCover nm pt hf
    obtain ⟨hpn, hpt⟩ := hp.rawTable (IFEnv.rawTable?_of_findTable? h2)
    exact ⟨n, t, denoteN_pext hx hpn h1, h2, denoteProjTable_pext hx hpt h3⟩

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
`CacheOK mode env s`, the fourteen caches read AT an environment, and an
install grows the environment: the entries a `whnf`/`infer`/`defeq` cache
holds were computed at `env` and say nothing at `env.push c`.  That is
precisely why `checkDeclStep`'s bracket OPENS with `flushCaches`.  So a value
check that has just installed a constant cannot hand back `CheckOK` at the
extended environment and must not claim to; what it does know is the four
clauses below, and the invariant at the pre-insertion environment — which it
hands back separately, as `CoreStep μ env fe s s'`.  Putting `CheckOK` in
`StepOK` would be the `PersIFEnv` defect again, one field over. -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK
con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**what a step knows about an index it has just extended**: the index answers
its environment's `find?`, the environment is well formed, the index is its
list's index, and it denotes as a function.

Nothing here is about the STATE's own invariant (that is `CheckOK`, at the
environment the core ran at) and nothing here is about persistence (that is
`promoteNew`'s, and it is `FoldOK`'s two remaining clauses). -/
structure StepOK (env : Env) (fe : IFEnv) (s : AState) : Prop where
  ienv : IFEnvOK env fe s
  envWF : EnvWF env
  coh : IFEnvCoh fe
  denote : denoteFEnv s.store fe = some env

/-- con-leche: none — `StepOK` transports across an append: `IFEnvOK.mono`
and `denoteFEnv_mono` carry the two store clauses, the other two mention no
store. -/
theorem StepOK.mono {env : Env} {fe : IFEnv} {s s' : AState}
    (h : StepOK env fe s) (hx : Ext s.store s'.store) : StepOK env fe s' where
  ienv := h.ienv.mono hx
  envWF := h.envWF
  coh := h.coh
  denote := denoteFEnv_mono hx h.denote

/-! ## The fold-step invariant -/

/-- con-leche: ConLeche/Verify/Cached/SimC.lean:262 CSOK
con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run
**the fold-step invariant**: the Core tier's `CheckOK` plus the three clauses
that make a step's output usable by the NEXT step — the environment denotes as
a function, its index is its list's index (con-leche's `fe = mkFEnv fe.env`),
and everything handed on is persistent. -/
structure FoldOK (μ : CheckMode) (env : Env) (fe : IFEnv) (s : AState) :
    Prop where
  check : CheckOK μ env fe s
  envWF : EnvWF env
  /-- every table of the index's list is well shaped (`IFEnvOK_of_denote`'s
  `hproj`, which the bracket's close re-derives the index spec from) -/
  tblShape : ∀ t ∈ fe.env.tables, IProjTableOK t
  persPins : PersPins s
  persEnv : PersIFEnv fe
  coh : IFEnvCoh fe
  denote : denoteFEnv s.store fe = some env

/-- con-leche: none — a boundary is a step: the four `StepOK` clauses are
`FoldOK`'s own, `IFEnvOK` read off `CheckOK`.  This is what a theorem whose
hypothesis is `FoldOK` passes to one whose hypothesis is `StepOK`.

(`FoldOK.step` is taken — `Bridge/Checker/Arms.lean` uses it for "carry
`FoldOK` across a step that only appends" — so this one is spelled the way
Lean spells a parent projection.) -/
theorem FoldOK.toStepOK {μ : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (h : FoldOK μ env fe s) : StepOK env fe s where
  ienv := h.check.ienv
  envWF := h.envWF
  coh := h.coh
  denote := h.denote

/-- con-leche: none — **`FoldOK` survives a step that only appends and leaves
the environment alone.**  A step of an arm leaves `CheckOK` at the SAME
environment and an `Ext`; the other four clauses are about the environment
index and the pin handles, and both transport.

It lives here rather than in `Bridge/Checker/Arms.lean` because
`DeclVal.lean`'s `checkThmVal_bridge`, two modules lower, uses it. -/
theorem FoldOK.step {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (h : FoldOK μ env fe s) (hck : CheckOK μ env fe s')
    (hx : Ext s.store s'.store) (hp : s'.pins = s.pins) :
    FoldOK μ env fe s' where
  check := hck
  envWF := h.envWF
  tblShape := h.tblShape
  persPins := h.persPins.mono hp
  persEnv := h.persEnv
  coh := h.coh
  denote := denoteFEnv_pext (PExt.of_ext hx) h.persEnv h.denote

/-- con-leche: none — **every entry the index answers with is an entry of the
list it was built from**.  `mkIFEnvGo` only ever inserts entries of its own
list, so a hash-map hit is a list member.  This is what makes the
membership-shaped `hproj` of `IFEnvOK_of_denote` strictly stronger than the
`find?`-shaped clause its conclusion has to deliver. -/
theorem mkIFEnvGo_mem : ∀ (cs : List IConstantInfo) (n : NIdx)
    (p : Nat × IConstantInfo), (mkIFEnvGo cs).2[n]? = some p → p.2 ∈ cs := by
  intro cs
  induction cs with
  | nil => intro n p h; simp [mkIFEnvGo] at h
  | cons a as ih =>
    intro n p h
    simp only [mkIFEnvGo] at h
    rw [Std.HashMap.getElem?_insert] at h
    by_cases hn : a.name == n
    · rw [ite_eq_left hn] at h
      obtain rfl := Option.some.inj h
      simp
    · rw [ite_eq_right hn] at h
      exact List.mem_cons_of_mem _ (ih n p h)

/-- con-leche: none — `mkIFEnvGo_mem` at the index of a coherent `IFEnv`. -/
theorem IFEnv.find?_mem {fe : IFEnv} (hcoh : IFEnvCoh fe) {n : NIdx}
    {ci : IConstantInfo} (h : fe.find? n = some ci) : ci ∈ fe.env.consts := by
  simp only [IFEnv.find?, hcoh.idx n] at h
  cases hg : (mkIFEnvGo fe.env.consts).2[n]? with
  | none => rw [hg] at h; simp at h
  | some p =>
    obtain ⟨c0, ci0⟩ := p
    rw [hg] at h
    dsimp only at h
    by_cases hc : c0 < fe.visibleBelow
    · rw [ite_eq_left hc] at h
      obtain rfl : ci0 = ci := Option.some.inj h
      exact mkIFEnvGo_mem _ n (c0, ci0) hg
    · rw [ite_eq_right hc] at h; simp at h

/-! ## The index IS the list

con-leche's `mkFEnv_find?` (`Verify/EnvBound.lean`), at the arena's hash-map
index: `mkIFEnvGo` inserts from the back, so the FRONT entry is inserted last
and wins, which is exactly what `List.find?` does — and every counter it hands
out is below the list's length, so the visibility bound never hides anything.
Three small inductions, and then the whole of `IFEnvOK_of_denote` is a
statement about two LISTS. -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — the counter the index
build ends at is the list's length. -/
theorem mkIFEnvGo_fst : ∀ (cs : List IConstantInfo),
    (mkIFEnvGo cs).1 = cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons a as ih => simp only [mkIFEnvGo, List.length_cons, ih]

/-- con-leche: ConLeche/Verify/EnvBound.lean idxSpec — **the index answers
`List.find?`**: the front entry is inserted last, so the hash map's answer is
the first list entry with that handle. -/
theorem mkIFEnvGo_snd : ∀ (cs : List IConstantInfo) (n : NIdx),
    ((mkIFEnvGo cs).2[n]?).map Prod.snd = cs.find? (fun ci => ci.name == n) := by
  intro cs
  induction cs with
  | nil => intro n; simp [mkIFEnvGo]
  | cons a as ih =>
    intro n
    simp only [mkIFEnvGo, List.find?_cons]
    rw [Std.HashMap.getElem?_insert]
    by_cases hn : a.name == n
    · rw [ite_eq_left hn]; simp [hn]
    · rw [ite_eq_right hn]; simp only [hn]; exact ih n

/-- con-leche: ConLeche/Verify/EnvBound.lean idxBelow — every counter the
index hands out is below the list's length, so `mkIFEnv`'s own visibility
bound hides nothing. -/
theorem mkIFEnvGo_lt : ∀ (cs : List IConstantInfo) (n : NIdx)
    (c : Nat) (ci : IConstantInfo),
    (mkIFEnvGo cs).2[n]? = some (c, ci) → c < cs.length := by
  intro cs
  induction cs with
  | nil => intro n c ci h; simp [mkIFEnvGo] at h
  | cons a as ih =>
    intro n c ci h
    simp only [mkIFEnvGo] at h
    rw [Std.HashMap.getElem?_insert] at h
    by_cases hn : a.name == n
    · rw [ite_eq_left hn] at h
      obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj h
      rw [mkIFEnvGo_fst]
      simp
    · rw [ite_eq_right hn] at h
      exact Nat.lt_succ_of_lt (ih n c ci h)

/-- con-leche: ConLeche/Verify/EnvBound.lean:243 mkFEnv_find? — **the index of
a list IS the list's lookup**. -/
theorem mkIFEnv_find? (e : IEnv) (n : NIdx) : (mkIFEnv e).find? n = e.find? n := by
  show (match (mkIFEnvGo e.consts).2[n]? with
        | some (c, ci) => if c < (mkIFEnvGo e.consts).1 then some ci else none
        | none => none) = e.consts.find? (fun ci => ci.name == n)
  have hm := mkIFEnvGo_snd e.consts n
  cases hg : (mkIFEnvGo e.consts).2[n]? with
  | none => rw [hg] at hm; exact hm
  | some p =>
    obtain ⟨c0, ci0⟩ := p
    rw [hg] at hm
    dsimp only
    rw [ite_eq_left (by rw [mkIFEnvGo_fst]; exact mkIFEnvGo_lt e.consts n c0 ci0 hg)]
    simpa using hm

/-- con-leche: ConLeche/Verify/EnvBound.lean:243 mkFEnv_find? — the same at a
COHERENT index, which is the form every consumer has. -/
theorem IFEnvCoh.find? {fe : IFEnv} (hcoh : IFEnvCoh fe) (n : NIdx) :
    fe.find? n = fe.env.find? n := by
  have h3 : fe.find? n = (mkIFEnv fe.env).find? n := by
    simp only [IFEnv.find?, mkIFEnv, hcoh.idx n, hcoh.1, mkIFEnvGo_fst]
  rw [h3, mkIFEnv_find?]

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
push.**  With `IFEnvCoh` on both sides the index reduces to its list:
`(fe.push ci).find? n` is `List.find?` on a cons, con-leche's side is
`Env.find?_cons`, and the two negative cases are `denoteN_inj` — a handle the
pushed key is not cannot denote the pushed constant's name, because the two
handles would then be equal.

A push touches neither the table map nor the environment's tables, but it
opens both table gates at the new name: `hA`/`hB` are the raw lookups there,
side by side (`IFEnvOK.pushStored` discharges them). -/
theorem IFEnvOK.push {env : Env} {fe : IFEnv} {s : AState}
    {ci : IConstantInfo} {c : ConstantInfo}
    (h : IFEnvOK env fe s) (hst : StateOK s) (hcoh : IFEnvCoh fe)
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
    rw [(hcoh.push ci).find? n, hcoh.find? n]
    show List.find? (fun x => x.name == n) (ci :: fe.env.consts) = _
    cases hb : (ci.name == n) <;> simp [IEnv.find?, hb]
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

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index spec survives a
table install**: the constant index is untouched, and the table map's new row
answers the new table, whose key denotes its structure's name; the two
negative cases are `denoteN_inj`, as at a push. -/
theorem IFEnvOK.pushTable {env : Env} {fe : IFEnv} {s : AState}
    {t : IProjTable} {pt : ProjTable}
    (h : IFEnvOK env fe s) (hst : StateOK s)
    (ht : Frontend.denoteProjTable s.store t = some pt) (hok : IProjTableOK t)
    (hT : (fe.find? t.structName).isSome = true) :
    IFEnvOK ⟨env.consts, pt :: env.tables⟩ (fe.pushTable t) s := by
  obtain ⟨rk, hrk⟩ := hst.wf
  have hnm := denoteProjTable_structName ht
  -- the structure is stored on con-leche's side too
  have hgate : (env.find? pt.structName).isSome = true := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT
    obtain ⟨nm, c, hd, -, he⟩ := h.hit _ ci hci
    rw [hnm] at hd
    obtain rfl := Option.some.inj hd
    rw [he]; rfl
  have keyTb : ∀ n, (fe.pushTable t).findTable? n =
      if (t.structName == n) = true then some t else fe.findTable? n := by
    intro n
    cases hb : (t.structName == n) with
    | true =>
      have hn : t.structName = n := by simpa using hb
      subst hn
      simp only [IFEnv.findTable?, IFEnv.rawTable?, IFEnv.pushTable,
        Std.HashMap.getElem?_insert_self, ↓reduceIte]
      exact ite_eq_left hT
    | false =>
      simp only [IFEnv.findTable?, IFEnv.rawTable?, IFEnv.pushTable,
        Std.HashMap.getElem?_insert, hb, Bool.false_eq_true, ↓reduceIte]
      rfl
  have keyEnvT : ∀ nm, (⟨env.consts, pt :: env.tables⟩ : Env).findTable? nm =
      if (pt.structName == nm) = true then some pt else env.findTable? nm := by
    intro nm
    cases hq : (pt.structName == nm) with
    | true =>
      have hn : pt.structName = nm := by simpa using hq
      subst hn
      simp only [Env.findTable?, List.find?_cons, beq_self_eq_true, ↓reduceIte]
      exact ite_eq_left hgate
    | false =>
      simp only [Env.findTable?, List.find?_cons, hq, Bool.false_eq_true, ↓reduceIte]
      rfl
  refine ⟨h.hit, h.cover, ?_, ?_⟩
  · intro n t' hf
    rw [keyTb] at hf
    cases hb : (t.structName == n) with
    | true =>
      rw [hb] at hf
      simp only [↓reduceIte, Option.some.injEq] at hf
      subst hf
      have hn : t.structName = n := by simpa using hb
      subst hn
      exact ⟨pt.structName, pt, hnm, ht, by rw [keyEnvT]; simp, hok⟩
    | false =>
      rw [hb] at hf
      simp only [Bool.false_eq_true, ↓reduceIte] at hf
      obtain ⟨nm, p, hd, hp, he, hk⟩ := h.tblHit n t' hf
      refine ⟨nm, p, hd, hp, ?_, hk⟩
      cases hq : (pt.structName == nm) with
      | true =>
        have hq' : pt.structName = nm := by simpa using hq
        subst hq'
        obtain rfl := denoteN_inj hrk.nsWF hnm hd
        simp at hb
      | false => rw [keyEnvT, hq]; simpa using he
  · intro nm p he
    rw [keyEnvT] at he
    cases hq : (pt.structName == nm) with
    | true =>
      rw [hq] at he
      simp only [↓reduceIte, Option.some.injEq] at he
      subst he
      have hq' : pt.structName = nm := by simpa using hq
      subst hq'
      exact ⟨t.structName, t, hnm, by rw [keyTb]; simp, ht⟩
    | false =>
      rw [hq] at he
      simp only [Bool.false_eq_true, ↓reduceIte] at he
      obtain ⟨n, t', hd, hf, hp⟩ := h.tblCover nm p he
      refine ⟨n, t', hd, ?_, hp⟩
      cases hb : (t.structName == n) with
      | true =>
        have hb' : t.structName = n := by simpa using hb
        subst hb'
        rw [hnm] at hd
        obtain rfl := Option.some.inj hd
        simp at hq
      | false => rw [keyTb, hb]; simpa using hf

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the two `find?`s agree,
entry by entry**: the arena's list and its denotation answer at handles and
names that denote each other.  One induction, both directions, and
`denoteN_inj` is what makes the negative cases go through — a handle the
arena's `find?` walked past cannot be the handle of the name con-leche's
`find?` stopped at, because the two handles would then denote the same name
and be equal. -/
theorem denoteCIList_find? {st : EStore} (hwf : StoreWF st) :
    ∀ (cs : List IConstantInfo) (zs : List ConstantInfo),
      Frontend.denoteCIList st cs = some zs →
      (∀ n ci, cs.find? (fun d => d.name == n) = some ci →
        ∃ nm c, denoteN st.ns n = some nm ∧ Frontend.denoteCI st ci = some c ∧
          zs.find? (fun d => d.name == nm) = some c) ∧
      (∀ nm c, zs.find? (fun d => d.name == nm) = some c →
        ∃ n ci, denoteN st.ns n = some nm ∧
          cs.find? (fun d => d.name == n) = some ci ∧
          Frontend.denoteCI st ci = some c) := by
  obtain ⟨rk, hrk⟩ := hwf
  intro cs
  induction cs with
  | nil =>
    intro zs hz
    simp only [Frontend.denoteCIList, Option.some.injEq] at hz
    subst hz
    exact ⟨by intro n ci h; simp at h, by intro nm c h; simp at h⟩
  | cons a as ih =>
    intro zs hz
    simp only [Frontend.denoteCIList] at hz
    cases ha : Frontend.denoteCI st a with
    | none => rw [ha] at hz; simp at hz
    | some x =>
      cases has : Frontend.denoteCIList st as with
      | none => rw [ha, has] at hz; simp at hz
      | some xs =>
        rw [ha, has] at hz
        obtain rfl := Option.some.inj hz.symm
        have hnm : denoteN st.ns a.name = some x.name := denoteCI_name ha
        obtain ⟨ihH, ihC⟩ := ih xs has
        constructor
        · intro n ci h
          simp only [List.find?_cons] at h
          cases hb : (a.name == n) with
          | true =>
            rw [hb] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain rfl : a.name = n := by simpa using hb
            exact ⟨x.name, x, hnm, ha, by simp⟩
          | false =>
            rw [hb] at h
            simp only at h
            obtain ⟨nm, c, hn1, hc1, hf1⟩ := ihH n ci h
            refine ⟨nm, c, hn1, hc1, ?_⟩
            have hne : (x.name == nm) = false := by
              cases hx : (x.name == nm) with
              | false => rfl
              | true =>
                obtain rfl : x.name = nm := by simpa using hx
                rw [denoteN_inj hrk.nsWF hnm hn1] at hb
                simp at hb
            simp only [List.find?_cons, hne]
            exact hf1
        · intro nm c h
          simp only [List.find?_cons] at h
          cases hb : (x.name == nm) with
          | true =>
            rw [hb] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain rfl : x.name = nm := by simpa using hb
            exact ⟨a.name, a, hnm, by simp, ha⟩
          | false =>
            rw [hb] at h
            simp only at h
            obtain ⟨n, ci, hn1, hf1, hc1⟩ := ihC nm c h
            refine ⟨n, ci, hn1, ?_, hc1⟩
            have hne : (a.name == n) = false := by
              cases hx : (a.name == n) with
              | false => rfl
              | true =>
                obtain rfl : a.name = n := by simpa using hx
                rw [hn1] at hnm
                obtain rfl : x.name = nm := (Option.some.inj hnm).symm
                simp at hb
            simp only [List.find?_cons, hne]
            exact hf1

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the two raw table lookups
agree, entry by entry**: `denoteCIList_find?` for the table lists, keyed on the
structure name. -/
theorem denoteProjTableList_find? {st : EStore} (hwf : StoreWF st) :
    ∀ (ts : List IProjTable) (zs : List ProjTable),
      Frontend.denoteProjTableList st ts = some zs →
      (∀ n t, ts.find? (fun d => d.structName == n) = some t →
        ∃ nm pt, denoteN st.ns n = some nm ∧ Frontend.denoteProjTable st t = some pt ∧
          zs.find? (fun d => d.structName == nm) = some pt) ∧
      (∀ nm pt, zs.find? (fun d => d.structName == nm) = some pt →
        ∃ n t, denoteN st.ns n = some nm ∧
          ts.find? (fun d => d.structName == n) = some t ∧
          Frontend.denoteProjTable st t = some pt) := by
  obtain ⟨rk, hrk⟩ := hwf
  intro ts
  induction ts with
  | nil =>
    intro zs hz
    simp only [Frontend.denoteProjTableList, Option.some.injEq] at hz
    subst hz
    exact ⟨by intro n t h; simp at h, by intro nm p h; simp at h⟩
  | cons a as ih =>
    intro zs hz
    simp only [Frontend.denoteProjTableList] at hz
    cases ha : Frontend.denoteProjTable st a with
    | none => rw [ha] at hz; simp at hz
    | some x =>
      cases has : Frontend.denoteProjTableList st as with
      | none => rw [ha, has] at hz; simp at hz
      | some xs =>
        rw [ha, has] at hz
        obtain rfl := Option.some.inj hz.symm
        have hnm : denoteN st.ns a.structName = some x.structName :=
          denoteProjTable_structName ha
        obtain ⟨ihH, ihC⟩ := ih xs has
        constructor
        · intro n t h
          simp only [List.find?_cons] at h
          cases hb : (a.structName == n) with
          | true =>
            rw [hb] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain rfl : a.structName = n := by simpa using hb
            exact ⟨x.structName, x, hnm, ha, by simp⟩
          | false =>
            rw [hb] at h
            simp only at h
            obtain ⟨nm, p, hn1, hc1, hf1⟩ := ihH n t h
            refine ⟨nm, p, hn1, hc1, ?_⟩
            have hne : (x.structName == nm) = false := by
              cases hx : (x.structName == nm) with
              | false => rfl
              | true =>
                obtain rfl : x.structName = nm := by simpa using hx
                rw [denoteN_inj hrk.nsWF hnm hn1] at hb
                simp at hb
            simp only [List.find?_cons, hne]
            exact hf1
        · intro nm p h
          simp only [List.find?_cons] at h
          cases hb : (x.structName == nm) with
          | true =>
            rw [hb] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain rfl : x.structName = nm := by simpa using hb
            exact ⟨a.structName, a, hnm, by simp, ha⟩
          | false =>
            rw [hb] at h
            simp only at h
            obtain ⟨n, t, hn1, hf1, hc1⟩ := ihC nm p h
            refine ⟨n, t, hn1, ?_, hc1⟩
            have hne : (a.structName == n) = false := by
              cases hx : (a.structName == n) with
              | false => rfl
              | true =>
                obtain rfl : a.structName = n := by simpa using hx
                rw [hn1] at hnm
                obtain rfl : x.structName = nm := (Option.some.inj hnm).symm
                simp at hb
            simp only [List.find?_cons, hne]
            exact hf1

/-- con-leche: ConLeche/Verify/EnvBound.lean idxSpec — **the table map answers
`List.find?`**: the front table is inserted last. -/
theorem mkIFEnvTblsGo_find? : ∀ (ts : List IProjTable) (n : NIdx),
    (mkIFEnvTblsGo ts)[n]? = ts.find? (fun t => t.structName == n) := by
  intro ts
  induction ts with
  | nil => intro n; simp [mkIFEnvTblsGo]
  | cons a as ih =>
    intro n
    simp only [mkIFEnvTblsGo, List.find?_cons, Std.HashMap.getElem?_insert]
    by_cases hn : a.structName == n
    · simp [hn]
    · simp only [hn]; exact ih n

/-- con-leche: none — the raw table lookup at a COHERENT index is the table
list's lookup. -/
theorem IFEnvCoh.rawTable? {fe : IFEnv} (hcoh : IFEnvCoh fe) (n : NIdx) :
    fe.rawTable? n = fe.env.tables.find? (fun t => t.structName == n) := by
  rw [IFEnv.rawTable?, hcoh.tbls n, mkIFEnvTblsGo_find?]

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index spec from the
denotation**: `IFEnvOK`'s two clauses follow from "the environment denotes"
and "the index is its list's index", because `IEnv.find?` and `Env.find?` are
the same linear search and `denoteN` is injective on a well-formed store.

**It needs one thing the denotation does not carry**: the stored tables'
SHAPE (`IProjTableOK`, their bodies and guards have `numFields` entries),
which `Frontend.denoteProjTable` transports but does not constrain.  A
simulation B ⇒ A takes invariants on the REFINED side only, so it is a
hypothesis about OUR tables (`hproj`), quantified over membership in
`fe.env.tables` (the install is the only place a table is created, so every
table of the list satisfies it), and the conclusion's `tblHit` re-delivers it
at what the table map answers (`IFEnvCoh.rawTable?` makes every answer a
member).

**The proof**, in two halves.  `IFEnvCoh.find?`
(above) retires the index — `mkIFEnvGo` inserts from the back, so the hash
map answers what `List.find?` answers, and every counter it hands out is below
the list's length, so `mkIFEnv`'s own bound hides nothing — after which the
theorem is a statement about two pairs of LISTS and `denoteCIList_find?` /
`denoteProjTableList_find?` are the whole of it: one induction each, both
directions, the key's denotation at each entry and `denoteN_inj` in the
negative cases.  It is the one place `IFEnvCoh` is
consumed rather than propagated, and it is con-leche's `mkFEnv_find?` at a
denoted list. -/
theorem IFEnvOK_of_denote {env : Env} {fe : IFEnv} {s : AState}
    (hwf : StateOK s) (hcoh : IFEnvCoh fe)
    (hproj : ∀ t ∈ fe.env.tables, IProjTableOK t)
    (hd : denoteFEnv s.store fe = some env) : IFEnvOK env fe s := by
  obtain ⟨rk, hrk⟩ := hwf.wf
  obtain ⟨hzs, hts⟩ := denoteIEnv_some.mp hd
  obtain ⟨hH, hC⟩ := denoteCIList_find? hwf.wf fe.env.consts _ hzs
  obtain ⟨tH, tC⟩ := denoteProjTableList_find? hwf.wf fe.env.tables _ hts
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n ci hf
    rw [hcoh.find?] at hf
    exact hH n ci hf
  · intro nm c he
    obtain ⟨n, ci, h1, h2, h3⟩ := hC nm c he
    exact ⟨n, ci, h1, by rw [hcoh.find?]; exact h2, h3⟩
  · intro n t hf
    have hgate := IFEnv.find?_of_findTable? hf
    have hraw := IFEnv.rawTable?_of_findTable? hf
    rw [hcoh.rawTable?] at hraw
    obtain ⟨nm, pt, h1, h2, h3⟩ := tH n t hraw
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hgate
    rw [hcoh.find?] at hci
    obtain ⟨nm', c, h1', -, h3'⟩ := hH n ci hci
    obtain rfl := Option.some.inj (h1'.symm.trans h1)
    refine ⟨nm', pt, h1, h2, ?_, hproj t (List.mem_of_find?_eq_some hraw)⟩
    unfold Env.findTable?
    have : (env.find? nm').isSome = true := by
      show (env.consts.find? (·.name == nm')).isSome = true
      rw [h3']; rfl
    rw [ite_eq_left this]
    exact h3
  · intro nm pt he
    unfold Env.findTable? at he
    split at he
    · rename_i hg
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hg
      obtain ⟨n, t, h1, h2, h3⟩ := tC nm pt he
      obtain ⟨n', ci, h1', h2', -⟩ := hC nm c hc
      obtain rfl := denoteN_inj hrk.nsWF h1 h1'
      refine ⟨n, t, h1, ?_, h3⟩
      unfold IFEnv.findTable?
      have : (fe.find? n).isSome = true := by
        rw [hcoh.find?]; simp only [IEnv.find?, h2', Option.isSome_some]
      rw [ite_eq_left this, hcoh.rawTable?]
      exact h2
    · cases he

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
arena none either, because its tables denote con-leche's. -/
theorem IFEnvOK.pushStored {env : Env} {fe : IFEnv} {s : AState}
    {ci : IConstantInfo} {c : ConstantInfo}
    (h : IFEnvOK env fe s) (hst : StateOK s) (hcoh : IFEnvCoh fe)
    (hden : denoteFEnv s.store fe = some env) (hstored : TablesStored env)
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
      obtain ⟨-, hts⟩ := denoteIEnv_some.mp hden
      obtain ⟨tH, -⟩ := denoteProjTableList_find? hst.wf fe.env.tables _ hts
      cases hf : fe.rawTable? ci.name with
      | none => rfl
      | some t =>
        rw [hcoh.rawTable?] at hf
        obtain ⟨nm, pt, hd, -, he⟩ := tH _ t hf
        rw [hnm] at hd
        obtain rfl := Option.some.inj hd
        rw [htab] at he
        cases he
    refine h.push hst hcoh hci (fun t ht => ?_) (fun pt hp => ?_)
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
    refine h.push hst hcoh hci (fun t ht => ?_) (fun pt hp => ?_)
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
    (hcw : ConstWF ⟨c :: env.consts, env.tables⟩ c) :
    StepOK ⟨c :: env.consts, env.tables⟩ (fe.push ci) s where
  ienv := h.ienv.pushStored hst h.coh h.denote (TablesStored.of_envWF h.envWF) hci
  envWF := EnvWF.cons h.envWF hcw
  coh := h.coh.push ci
  denote := denoteFEnv_push h.denote hci

end ConRon.Bridge
