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
  | inert => exact h
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
  | some ct => rw [hn] at h; rw [denoteN_pext hx hp hn]; exact h

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
  | projInfo t =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨tb, htb, hc⟩ := h
    exact ⟨tb, denoteProjTable_pext hx hp htb, hc⟩
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
  | thmInfo v e =>
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
theorem denoteFEnv_pext {st st' : EStore} (hx : PExt st st') {fe : IFEnv}
    {env : Env} (hp : PersIFEnv fe) (h : denoteFEnv st fe = some env) :
    denoteFEnv st' fe = some env := by
  simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at h ⊢
  obtain ⟨xs, hxs, he⟩ := h
  exact ⟨xs, denoteCIList_pext hx _ xs hp.env hxs, he⟩

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

/-- con-leche: none — **`PinsOK` survives `dropScratch`** — task #97-P3-0 §7's
"`DeclCheck` / `Checker` need `PinsOK` to survive `dropScratch`, which needs
one more clause: the pin handles are persistent".  Here is the clause
(`PersPins`) and here is what it buys. -/
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
  persPins : PersPins s
  persEnv : PersIFEnv fe
  coh : IFEnvCoh fe
  denote : denoteFEnv s.store fe = some env

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index spec from the
denotation**: `IFEnvOK`'s two clauses follow from "the environment denotes"
and "the index is its list's index", because `IEnv.find?` and `Env.find?` are
the same linear search and `denoteN` is injective on a well-formed store.

`sorry`: the `hit`/`cover` pair is an induction on `fe.env.consts` through
`mkIFEnvGo`, with `denoteN_inj` where con-leche uses name equality.  It is the
one place `IFEnvCoh` is consumed rather than propagated, and the argument is
con-leche's `mkFEnv_find?` at a denoted list.  Task #97-P3-Checker's sorry
list, item 6. -/
theorem IFEnvOK_of_denote {μ : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (hwf : StateOK s) (hcoh : IFEnvCoh fe)
    (hd : denoteFEnv s.store fe = some env) : IFEnvOK env fe s := by
  sorry

end ConRon.Bridge
