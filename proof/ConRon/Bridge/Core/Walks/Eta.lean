/-
# `ConRon.Bridge.Core.Walks.Eta` — the structure-η certificate's sub-walks

Task #97-P3-Core round 6.  `structEtaCertWith` (`Walks/Stuck.lean`) reads
four walks that had no Theorem 1 before this round; they are here, each an
equation with con-leche's function of the same name:

| walk | twin | con-leche |
|---|---|---|
| `projFnName_spec` | `Arena/Env.lean:206` | `Kernel/Env.lean:629` |
| `towerSlotsAll_spec` | `Arena/Core.lean:1341` (`towerSlotsAllGo`) | `Kernel/CoreDefs.lean:713` |
| `recSlotsAll_spec` | `Arena/Core.lean:1357` (`recSlotsAllGo`) | `Kernel/CoreDefs.lean:720` |
| `structEtaProjCerts_spec` | `Arena/Core.lean:1313` | `Kernel/Core.lean:359` |
| `etaProjs_spec` | `Arena/Core.lean:1383` (`projNodesGo`, `projAppsGo`) | `Kernel/CoreDefs.lean:730` |

con-leche writes the three slot walks as `(List.range nF).all`/`.map`; the
twin's counted recursions (DESIGN §3.4) are identified with
`(List.range' j n)` at their running index `j`, and `List.range_eq_range'`
closes the gap at `j = 0`.
-/
import ConRon.Bridge.Core.Walks.StrCtor
import ConRon.Bridge.Core.Walks.StrLit

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Small facts about the denotations -/

/-- con-leche: none — a copy of `Bridge/Checker/Canon.lean`'s
`denoteNList_inj` (that module sits above this tier: `Checker/Hyp.lean`
imports `Core/Induction.lean`). -/
theorem denoteNList_injC {st : EStore} (hwf : StoreWF st) :
    ∀ (as bs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns as = some xs →
      Frontend.denoteNList st.ns bs = some xs → as = bs := by
  obtain ⟨rk, hrk⟩ := hwf
  intro as
  induction as with
  | nil =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList, Option.some.injEq] at ha
    subst ha
    cases bs with
    | nil => rfl
    | cons b bt =>
      simp only [Frontend.denoteNList] at hb
      cases hbh : denoteN st.ns b with
      | none => rw [hbh] at hb; simp at hb
      | some y =>
        cases hbt : Frontend.denoteNList st.ns bt with
        | none => rw [hbh, hbt] at hb; simp at hb
        | some ys => rw [hbh, hbt] at hb; simp at hb
  | cons a at_ ih =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList] at ha
    cases hah : denoteN st.ns a with
    | none => rw [hah] at ha; simp at ha
    | some x =>
      cases hat : Frontend.denoteNList st.ns at_ with
      | none => rw [hah, hat] at ha; simp at ha
      | some xt =>
        rw [hah, hat] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        cases bs with
        | nil => simp only [Frontend.denoteNList] at hb; simp at hb
        | cons b bt =>
          simp only [Frontend.denoteNList] at hb
          cases hbh : denoteN st.ns b with
          | none => rw [hbh] at hb; simp at hb
          | some y =>
            cases hbt : Frontend.denoteNList st.ns bt with
            | none => rw [hbh, hbt] at hb; simp at hb
            | some yt =>
              rw [hbh, hbt] at hb
              simp only [Option.some.injEq, List.cons.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              rw [denoteN_inj hrk.nsWF hah hbh, ih bt _ hat hbt]

/-- con-leche: none — two denoting name-handle lists are equal exactly when
their denotations are (the store interns names injectively). -/
theorem denoteNList_eq_iff {st : EStore} (hwf : StoreWF st)
    {as bs : List NIdx} {xs ys : List ConLeche.Name}
    (ha : Frontend.denoteNList st.ns as = some xs)
    (hb : Frontend.denoteNList st.ns bs = some ys) : as = bs ↔ xs = ys := by
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact denoteNList_injC hwf as bs xs ha hb

/-- con-leche: none — a snoc of denoting handles denotes the snoc. -/
theorem denoteEList_snoc {st : EStore} :
    ∀ (l : List EIdx) (es : List Expr) (b : EIdx) (y : Expr),
      Frontend.denoteEList st l = some es → denoteE st b = some y →
      Frontend.denoteEList st (l ++ [b]) = some (es ++ [y])
  | [], es, b, y, h, hb => by
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp [Frontend.denoteEList, hb]
  | a :: as, es, b, y, h, hb => by
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.cons_append, Frontend.denoteEList, ha,
          denoteEList_snoc as xs b y has hb]

/-- con-leche: none — a concatenation of denoting handle lists denotes the
concatenation. -/
theorem denoteEList_appendC {st : EStore} :
    ∀ (l m : List EIdx) (es fs : List Expr),
      Frontend.denoteEList st l = some es → Frontend.denoteEList st m = some fs →
      Frontend.denoteEList st (l ++ m) = some (es ++ fs)
  | [], m, es, fs, h, hm => by
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h; simpa using hm
  | a :: as, m, es, fs, h, hm => by
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.cons_append, Frontend.denoteEList, ha,
          denoteEList_appendC as m xs fs has hm]

/-- con-leche: none — `stripPis`' answer relation decides the same
`isSome`. -/
theorem relBP_isSome {f : Expr → Option (List (Expr × BinderMeta) × Expr)}
    {st : EStore} {c : EIdx} {r : Option (List (EIdx × BinderMeta) × EIdx)}
    {e : Expr} (hr : ExprOps.RelBP f st c st r) (hc : denoteE st c = some e) :
    r.isSome = (f e).isSome := by
  have h := hr e hc
  cases r with
  | none => simp only [ExprOps.denoteBP, Option.some.injEq] at h; rw [← h]; rfl
  | some p =>
    obtain ⟨bs, x⟩ := p
    simp only [ExprOps.denoteBP] at h
    split at h
    · simp only [Option.some.injEq] at h; rw [← h]; rfl
    · simp at h

/-- con-leche: none — a stored recursor denotes a recursor, and nothing else
does. -/
theorem denoteCI_rec_iff {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) :
    (∃ v mI rP rs, ci = .recInfo v mI rP rs) ↔
      ∃ cv mI rP rules, c = .recInfo cv mI rP rules := by
  cases ci <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; simp)
    | (split at h
       · rename_i heq1 heq2; cases h; simp
       · simp at h)

/-- con-leche: none — an indexed recursor is an environment recursor, with
the denoted constant value. -/
theorem optCI_rec_some {st : EStore} {oc' : Option ConstantInfo}
    {v : IConstantVal} {mI rP : Nat} {rs : List IRecRule}
    (hrel : OptCI st (some (.recInfo v mI rP rs)) oc') :
    ∃ cv rules, Frontend.denoteCV st v = some cv ∧
      oc' = some (.recInfo cv mI rP rules) := by
  obtain ⟨c, hci, rfl⟩ := hrel
  simp only [Frontend.denoteCI] at hci
  split at hci
  · rename_i cv rules hcv _
    cases hci
    exact ⟨cv, rules, hcv, rfl⟩
  · simp at hci

/-- con-leche: none — and nothing else the index holds is a recursor. -/
theorem optCI_rec_none {st : EStore} {oc : Option IConstantInfo}
    {oc' : Option ConstantInfo} (hrel : OptCI st oc oc')
    (hnot : ∀ v mI rP rs, oc ≠ some (.recInfo v mI rP rs)) :
    ∀ cv mI rP rules, oc' ≠ some (.recInfo cv mI rP rules) := by
  intro cv mI rP rules h
  subst h
  cases oc with
  | none => simp only [OptCI] at hrel; cases hrel
  | some ci =>
    obtain ⟨c, hci, hc⟩ := hrel
    cases hc
    obtain ⟨v, mI', rP', rs, rfl⟩ :=
      (denoteCI_rec_iff hci).mpr ⟨cv, mI, rP, rules, rfl⟩
    exact hnot v mI' rP' rs rfl

/-! ## 2. `projFnName` -/

/-- con-leche: ConLeche/Kernel/Env.lean:629 projFnName — **THEOREM 1 for
`projFnName`**: the handle the twin interns denotes con-leche's
`(T.str "proj").num i`.  `projTableName_spec`'s proof, verbatim. -/
theorem projFnName_spec (s₀ : AState) (T : NIdx) (i : Nat)
    (Tn : ConLeche.Name) (hwf : StoreWF s₀.store)
    (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projFnName T i
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some (ConLeche.projFnName Tn i)⌝⦄ := by
  mvcgen [ConRon.Arena.projFnName, internNNode_spec]
  all_goals (bridge_peel; subst_vars
             grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children,
               nview_isSome_of_denote, Ext.trans, ConLeche.projFnName])

/-- con-leche: ConLeche/Kernel/Env.lean:629 projFnName — the same at the
checker's invariant. -/
theorem projFnName_ok_spec (s₀ : AState) (T : NIdx) (i : Nat)
    (Tn : ConLeche.Name) (hok : CheckOK mode env fe s₀)
    (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projFnName T i
    ⦃⇓? h s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some (ConLeche.projFnName Tn i)⌝⦄ :=
  triple_mono (projFnName_spec s₀ T i Tn hok.state.wf hT)
    (fun _ _ ⟨hwf', hx', _, hc', hp', hd⟩ =>
      ⟨hok.mono ⟨hwf'⟩ hx' hc' hp', hx', hp', hd⟩)

/-! ## 3. The two slot walks -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — **THEOREM
1 for the counted recursion `towerSlotsAllGo`**, at its running index. -/
theorem towerSlotsAllGo_spec (T : NIdx) (Tn : ConLeche.Name) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.towerSlotsAllGo fe T n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          r = (List.range' j n).all (fun k => (env.findProj? Tn k).isSome)⌝⦄
  | 0, j, s₀, hok, _ => by
    mvcgen [ConRon.Arena.towerSlotsAllGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, by simp⟩
  | n + 1, j, s₀, hok, hT => by
    unfold ConRon.Arena.towerSlotsAllGo
    refine triple_seq (IFEnv.findProj?_spec s₀ T j Tn hok hT) ?_
    rintro o s1 ⟨hok1, hx1, _, _, hp1, hsome, hnone⟩
    have hiff : o.isSome = (env.findProj? Tn j).isSome := by
      cases o with
      | none => rw [hnone rfl]; rfl
      | some e => obtain ⟨p, _, hp⟩ := hsome e rfl; rw [hp]; rfl
    split
    next ho =>
      refine triple_mono (towerSlotsAllGo_spec T Tn n (j + 1) s1 hok1
        (denoteN_ext hT hx1)) ?_
      rintro r s2 ⟨hok2, hx2, hp2, hr⟩
      refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
      rw [hr, List.range'_succ, List.all_cons, ← hiff, ho, Bool.true_and]
    next ho =>
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok1, hx1, hp1, ?_⟩
      have hf : (env.findProj? Tn j).isSome = false := by
        rw [← hiff]; simpa using ho
      rw [List.range'_succ, List.all_cons, hf, Bool.false_and]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — **THEOREM
1 for `towerSlotsAll`**: an equation with con-leche's slot walk. -/
theorem towerSlotsAll_spec (s₀ : AState) (T : NIdx) (Tn : ConLeche.Name)
    (nF : Nat) (hok : CheckOK mode env fe s₀)
    (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.towerSlotsAll fe T nF
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.towerSlotsAll env Tn nF⌝⦄ := by
  unfold ConRon.Arena.towerSlotsAll
  refine triple_mono (towerSlotsAllGo_spec T Tn nF 0 s₀ hok hT) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  rw [h4, ConLeche.towerSlotsAll, List.range_eq_range']

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:720-724 recSlotsAll — the
per-slot test, named so the counted recursion can be stated against it. -/
def recSlotB (env : Env) (Tn : ConLeche.Name) (k : Nat) : Bool :=
  match env.find? (ConLeche.projFnName Tn k) with
  | some (.recInfo _ _ _ _) => true
  | _ => false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:720-724 recSlotsAll — **THEOREM 1
for the counted recursion `recSlotsAllGo`**, at its running index. -/
theorem recSlotsAllGo_spec (T : NIdx) (Tn : ConLeche.Name) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.recSlotsAllGo fe T n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          r = (List.range' j n).all (recSlotB env Tn)⌝⦄
  | 0, j, s₀, hok, _ => by
    mvcgen [ConRon.Arena.recSlotsAllGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, by simp⟩
  | n + 1, j, s₀, hok, hT => by
    unfold ConRon.Arena.recSlotsAllGo
    refine triple_seq (projFnName_ok_spec s₀ T j Tn hok hT) ?_
    rintro h s1 ⟨hok1, hx1, hp1, hh⟩
    have hrel := optCI_find hok1 hh
    split
    next v mI rP rs heq =>
      rw [heq] at hrel
      obtain ⟨cv, rules, _, hfind⟩ := optCI_rec_some hrel
      refine triple_mono (recSlotsAllGo_spec T Tn n (j + 1) s1 hok1
        (denoteN_ext hT hx1)) ?_
      rintro r s2 ⟨hok2, hx2, hp2, hr⟩
      refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
      rw [hr, List.range'_succ, List.all_cons]
      simp [recSlotB, hfind]
    next hnot =>
      have hno := optCI_rec_none hrel (fun v mI rP rs h => hnot v mI rP rs h)
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok1, hx1, hp1, ?_⟩
      have hf : recSlotB env Tn j = false := by
        unfold recSlotB
        split
        · rename_i cv mI rP rules heq; exact absurd heq (hno cv mI rP rules)
        · rfl
      rw [List.range'_succ, List.all_cons, hf, Bool.false_and]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:720-724 recSlotsAll — **THEOREM 1
for `recSlotsAll`**: an equation with con-leche's slot walk. -/
theorem recSlotsAll_spec (s₀ : AState) (T : NIdx) (Tn : ConLeche.Name)
    (nF : Nat) (hok : CheckOK mode env fe s₀)
    (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.recSlotsAll fe T nF
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.recSlotsAll env Tn nF⌝⦄ := by
  unfold ConRon.Arena.recSlotsAll
  refine triple_mono (recSlotsAllGo_spec T Tn nF 0 s₀ hok hT) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  rw [h4, ConLeche.recSlotsAll, List.range_eq_range']
  rfl

/-! ## 4. The per-projection certificates -/

/-- con-leche: ConLeche/Kernel/Core.lean:359-374 structEtaProjCerts — the
recursor-backed slot: con-leche's cons clause after the lookup. -/
theorem structEtaProjCertsFueled_cons_rec {F d : Nat} {Tn : ConLeche.Name}
    {ls : List Level} {xs : List Expr} {y : Expr} {lps : List ConLeche.Name}
    {i : Nat} {rest : List Nat} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule}
    (hf : env.find? (ConLeche.projFnName Tn i) = some (.recInfo cv mI rP rules)) :
    ConLeche.structEtaProjCertsFueled mode env F d Tn ls xs y lps (i :: rest) =
      (if cv.levelParams = lps ∧
          (cv.type.stripPis (xs.length + 1)).isSome = true then do
        if ← ConLeche.iotaCertsFueled mode env F d false
            (cv.type.instantiateLevelParams cv.levelParams ls) (xs ++ [y]) then
          ConLeche.structEtaProjCertsFueled mode env F d Tn ls xs y lps rest
        else pure false
      else pure false) := by
  simp only [ConLeche.structEtaProjCertsFueled, ConLeche.structEtaProjCerts, hf]

/-- con-leche: ConLeche/Kernel/Core.lean:359-374 structEtaProjCerts — the
slot is not a recursor: `false`. -/
theorem structEtaProjCertsFueled_cons_norec {F d : Nat} {Tn : ConLeche.Name}
    {ls : List Level} {xs : List Expr} {y : Expr} {lps : List ConLeche.Name}
    {i : Nat} {rest : List Nat}
    (hf : ∀ cv mI rP rules,
      env.find? (ConLeche.projFnName Tn i) ≠ some (.recInfo cv mI rP rules)) :
    ConLeche.structEtaProjCertsFueled mode env F d Tn ls xs y lps (i :: rest) =
      .ok false := by
  simp only [ConLeche.structEtaProjCertsFueled, ConLeche.structEtaProjCerts]
  first
    | rfl
    | (split
       · rename_i cv mI rP rules heq; exact absurd heq (hf cv mI rP rules)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:359-374 structEtaProjCerts —
**THEOREM 1 for `structEtaProjCerts`**, by induction on the slot list: per
slot `projFnName_ok_spec`, the index (`optCI_rec_some`/`_none`),
`stripPis_spec`, the guard (`denoteNList_eq_iff`), `constTyAt_spec` and
`iotaCerts_spec`.  `EnvWF env` is con-leche's `const_ty_hasFvar`'s
hypothesis: the projection function's stored type, instantiated, is the
telescope `iotaCerts_spec` needs well-scoped. -/
theorem structEtaProjCerts_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (T : NIdx) (us' : LsIdx)
    (targs : List EIdx) (b : EIdx) (lpsT : List NIdx) (Tn : ConLeche.Name)
    (ls : List Level) (xs : List Expr) (y : Expr) (lps : List ConLeche.Name)
    (hwxs : ∀ x ∈ xs, Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ∀ (is : List Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteLs s₀.store.lss us' = some ls →
      Frontend.denoteEList s₀.store targs = some xs →
      denoteE s₀.store b = some y →
      Frontend.denoteNList s₀.store.ns lpsT = some lps →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.structEtaProjCerts (coreKnot mode fe id fuel) fe d T us'
          targs b lpsT is
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimBOp (fun F => ConLeche.structEtaProjCertsFueled mode env F d Tn ls
            xs y lps is) r⌝⦄
  | [], s₀, hok, _, _, _, _, _ => by
    mvcgen [ConRon.Arena.structEtaProjCerts]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, 0, rfl⟩
  | i :: rest, s₀, hok, hT, hus, hxs, hb, hlps => by
    unfold ConRon.Arena.structEtaProjCerts
    refine triple_seq (projFnName_ok_spec s₀ T i Tn hok hT) ?_
    rintro h s1 ⟨hok1, hx1, hp1, hh⟩
    have hrel := optCI_find hok1 hh
    split
    next cvp mI rP rs heq =>
      rw [heq] at hrel
      obtain ⟨cv, rules, hcv, hfind⟩ := optCI_rec_some hrel
      obtain ⟨_, hlpsC, htyC⟩ := denoteCV_inv hcv
      refine triple_seq (ExprOps.stripPis_spec (targs.length + 1) s1 cvp.type
        hok1.state (by rw [htyC]; rfl)) ?_
      rintro peeled s2 ⟨hs2, hpeel⟩
      subst s2
      have hpS := relBP_isSome hpeel htyC
      have hlen : targs.length = xs.length := (denoteEList_len hxs).symm
      have hguard : (cvp.levelParams = lpsT ∧ peeled.isSome = true) ↔
          (cv.levelParams = lps ∧
            (cv.type.stripPis (xs.length + 1)).isSome = true) := by
        rw [denoteNList_eq_iff hok1.state.wf hlpsC
          (denoteNList_ext hx1.lss.ls.ns _ _ hlps), hpS, hlen]
      split
      next hg =>
        have hgP := hguard.mp hg
        have hus1 := denoteLs_ext hus hx1
        refine triple_seq (constTyAt_spec s1 cvp us' _ ls
          (.recInfo cv mI rP rules) hok1
          (by rw [denoteCV_name hcv, ← env_find_name hfind]; rfl) hus1 hfind
          hcv) ?_
        rintro ty s3 ⟨hok3, hx3, hp3, hty⟩
        have hwty : Expr.WScoped d
            (cv.type.instantiateLevelParams cv.levelParams ls) :=
          Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfind ls)
        have hx03 := hx1.trans hx3
        have hargs3 := denoteEList_snoc targs xs b y
          (denoteEList_ext hx03 _ _ hxs) (denote_ext hb hx03)
        have hwargs : ∀ z ∈ xs ++ [y], Expr.WScoped d z := by
          intro z hz
          simp only [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          · exact hwxs z hz
          · exact hwy
        refine triple_seq (iotaCerts_spec hsim d false ty (targs ++ [b]) s3 hok3
          ⟨_, _, hty, hwty, hargs3, hwargs⟩) ?_
        rintro c s4 ⟨hok4, hx4, hp4, hc⟩
        obtain ⟨F1, hF1⟩ := hc _ _ hty hargs3
        have hx04 := hx03.trans hx4
        have hp04 : s4.pins = s₀.pins := hp4.trans (hp3.trans hp1)
        split
        next hct =>
          subst hct
          refine triple_mono (structEtaProjCerts_spec henv hsim d T us' targs b
            lpsT Tn ls xs y lps hwxs hwy rest s4 hok4 (denoteN_ext hT hx04)
            (denoteLs_ext hus hx04) (denoteEList_ext hx04 _ _ hxs)
            (denote_ext hb hx04) (denoteNList_ext hx04.lss.ls.ns _ _ hlps)) ?_
          rintro r s5 ⟨hok5, hx5, hp5, F2, hF2⟩
          refine ⟨hok5, hx04.trans hx5, hp5.trans hp04, max F1 F2, ?_⟩
          have e1 := iotaCertsFueled_mono (Nat.le_max_left F1 F2) hF1
          have e2 := structEtaProjCertsFueled_mono (Nat.le_max_right F1 F2) hF2
          dsimp only
          rw [structEtaProjCertsFueled_cons_rec hfind, if_pos hgP]
          simp only [ConLeche.ConstantInfo.toConstantVal] at e1
          simp only [e1, e2, bind, Except.bind, if_true]
        next hcf =>
          have hcf' : c = false := by simpa using hcf
          subst hcf'
          have hres : ConLeche.structEtaProjCertsFueled mode env F1 d Tn ls xs y
              lps (i :: rest) = .ok false := by
            rw [structEtaProjCertsFueled_cons_rec hfind, if_pos hgP]
            simp only [ConLeche.ConstantInfo.toConstantVal] at hF1
            simp only [hF1, bind, Except.bind, Bool.false_eq_true, if_false]
            rfl
          mvcgen
          bridge_peel; subst_vars
          exact ⟨hok4, hx04, hp04, F1, hres⟩
      next hg =>
        have hres : ConLeche.structEtaProjCertsFueled mode env 0 d Tn ls xs y
            lps (i :: rest) = .ok false := by
          rw [structEtaProjCertsFueled_cons_rec hfind,
            if_neg (fun h => hg (hguard.mpr h))]
          rfl
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok1, hx1, hp1, 0, hres⟩
    next hnot =>
      have hno := optCI_rec_none hrel (fun v mI rP rs h => hnot v mI rP rs h)
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok1, hx1, hp1, 0, structEtaProjCertsFueled_cons_norec hno⟩

/-! ## 5. The fabricated projections -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:730-736 etaProjs — **THEOREM 1
for the `.proj` half**, the counted recursion `projNodesGo`. -/
theorem projNodesGo_spec (T : NIdx) (b : EIdx) (Tn : ConLeche.Name)
    (y : Expr) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteE s₀.store b = some y →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projNodesGo T b n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r =
            some ((List.range' j n).map fun k => Expr.proj Tn k y)⌝⦄
  | 0, j, s₀, hok, _, _ => by
    mvcgen [ConRon.Arena.projNodesGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | n + 1, j, s₀, hok, hT, hb => by
    unfold ConRon.Arena.projNodesGo
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s₀ (.proj T j b) hok (viewOK_proj (nview_isSome_of_denote hT)
        (by rw [hb]; rfl))) ?_
    rintro p s1 ⟨hok1, hx1, hp1, hp⟩
    have hp' : denoteE s1.store p = some (.proj Tn j y) := by
      rw [hp]
      simp only [denoteEView, denoteN_ext hT hx1, denote_ext hb hx1, opt2]
    refine triple_seq (projNodesGo_spec T b Tn y n (j + 1) s1 hok1
      (denoteN_ext hT hx1) (denote_ext hb hx1)) ?_
    rintro rest s2 ⟨hok2, hx2, hp2, hrest⟩
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [List.range'_succ, List.map_cons]
    simp only [Frontend.denoteEList, denote_ext hp' hx2, hrest]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:730-736 etaProjs — **THEOREM 1
for the projection-function half**, the counted recursion `projAppsGo`. -/
theorem projAppsGo_spec (T : NIdx) (us : LsIdx) (targs : List EIdx)
    (b : EIdx) (Tn : ConLeche.Name) (ls : List Level) (xs : List Expr)
    (y : Expr) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteLs s₀.store.lss us = some ls →
      Frontend.denoteEList s₀.store targs = some xs →
      denoteE s₀.store b = some y →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.projAppsGo T us targs b n j
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r =
            some ((List.range' j n).map fun k =>
              Expr.mkAppN (.const (ConLeche.projFnName Tn k) ls) (xs ++ [y]))⌝⦄
  | 0, j, s₀, hok, _, _, _, _ => by
    mvcgen [ConRon.Arena.projAppsGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | n + 1, j, s₀, hok, hT, hus, hxs, hb => by
    unfold ConRon.Arena.projAppsGo
    refine triple_seq (projFnName_ok_spec s₀ T j Tn hok hT) ?_
    rintro h s1 ⟨hok1, hx1, hp1, hh⟩
    have hus1 := denoteLs_ext hus hx1
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s1 (.const h us) hok1 (viewOK_const (nview_isSome_of_denote hh)
        (lsview_isSome_of_denote hus1))) ?_
    rintro f s2 ⟨hok2, hx2, hp2, hf⟩
    have hf' : denoteE s2.store f =
        some (.const (ConLeche.projFnName Tn j) ls) := by
      rw [hf]
      simp only [denoteEView, denoteN_ext hh hx2, denoteLs_ext hus1 hx2, opt2]
    have hx02 := hx1.trans hx2
    have hargs2 := denoteEList_snoc targs xs b y (denoteEList_ext hx02 _ _ hxs)
      (denote_ext hb hx02)
    refine triple_seq (ExprOps.mkAppN_spec (targs ++ [b]) s2 f hok2.state
      (by rw [hf']; rfl) (by rw [hargs2]; rfl)) ?_
    rintro p s3 ⟨hst3, hx3, _, _, hc3, hp3, hrel⟩
    have hok3 : CheckOK mode env fe s3 := hok2.mono hst3 hx3 hc3 hp3
    have hp' := hrel _ _ hf' hargs2
    have hx03 := hx02.trans hx3
    refine triple_seq (projAppsGo_spec T us targs b Tn ls xs y n (j + 1) s3 hok3
      (denoteN_ext hT hx03) (denoteLs_ext hus hx03)
      (denoteEList_ext hx03 _ _ hxs) (denote_ext hb hx03)) ?_
    rintro rest s4 ⟨hok4, hx4, hp4, hrest⟩
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok4, hx03.trans hx4, hp4.trans (hp3.trans (hp2.trans hp1)), ?_⟩
    rw [List.range'_succ, List.map_cons]
    simp only [Frontend.denoteEList, denote_ext hp' hx4, hrest]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:730-736 etaProjs — **THEOREM 1
for `etaProjs`**: the handles the twin fabricates denote con-leche's list. -/
theorem etaProjs_spec (s₀ : AState) (T : NIdx) (us : LsIdx)
    (targs : List EIdx) (b : EIdx) (nF : Nat) (Tn : ConLeche.Name)
    (ls : List Level) (xs : List Expr) (y : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hxs : Frontend.denoteEList s₀.store targs = some xs)
    (hb : denoteE s₀.store b = some y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.etaProjs fe T us targs b nF
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaProjs env Tn ls xs y nF)⌝⦄ := by
  unfold ConRon.Arena.etaProjs
  refine triple_seq (towerSlotsAll_spec s₀ T Tn nF hok hT) ?_
  rintro tw s1 ⟨hok1, hx1, hp1, htw⟩
  split
  next htt =>
    refine triple_mono (projNodesGo_spec T b Tn y nF 0 s1 hok1
      (denoteN_ext hT hx1) (denote_ext hb hx1)) ?_
    rintro r s2 ⟨hok2, hx2, hp2, hr⟩
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    have ht : ConLeche.towerSlotsAll env Tn nF = true := htw ▸ htt
    rw [hr, ConLeche.etaProjs, if_pos ht, List.range_eq_range']
  next htf =>
    refine triple_mono (projAppsGo_spec T us targs b Tn ls xs y nF 0 s1 hok1
      (denoteN_ext hT hx1) (denoteLs_ext hus hx1)
      (denoteEList_ext hx1 _ _ hxs) (denote_ext hb hx1)) ?_
    rintro r s2 ⟨hok2, hx2, hp2, hr⟩
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    have ht : ConLeche.towerSlotsAll env Tn nF = false := by
      rw [← htw]; simpa using htf
    rw [hr, ConLeche.etaProjs, if_neg (by simp [ht]), List.range_eq_range']

/-- con-leche: none — the fabricated projections are well-scoped wherever
the stuck side and the type's arguments are. -/
theorem etaProjs_WScoped {d : Nat} {Tn : ConLeche.Name} {ls : List Level}
    {xs : List Expr} {y : Expr} {nF : Nat}
    (hwxs : ∀ x ∈ xs, Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ∀ p ∈ ConLeche.etaProjs env Tn ls xs y nF, Expr.WScoped d p := by
  intro p hp
  unfold ConLeche.etaProjs at hp
  split at hp
  · simp only [List.mem_map] at hp
    obtain ⟨k, _, rfl⟩ := hp
    simp only [Expr.WScoped]; exact hwy
  · simp only [List.mem_map] at hp
    obtain ⟨k, _, rfl⟩ := hp
    refine Expr.WScoped.mkAppN (by simp [Expr.WScoped]) ?_
    intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hwxs z hz
    · exact hwy

end ConRon.Bridge.Core
