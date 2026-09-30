/-
# `ConRon.Bridge.Inductives.BlockTail` — Theorem 1 for the uniform route's top

`Arena/Inductives/BlockTail.lean` (`BlockPass`, `checkBlockPass`,
`checkBlockRec`, `checkBlockTables`, `checkBlockTail`, `checkBlock`) against
con-leche's `ConLeche/Kernel/Inductives/BlockTail.lean`, assembled step by
step as upstream's cached bridge assembles its own driver
(`ConLeche/Verify/Cached/GenRecC.lean`'s `checkBlockKS_run` /
`checkBlockPassS_run` / `checkBlockTailS_run`, `BlockRunC.lean`'s
`checkBlockTablesS_run`).

The twin's `flushCaches` at the environment transitions are what re-establish
`CheckOK` at the new index (`ReadOK.flush`, `Bridge/Inductives/Rel.lean`):
between two flushes the state is only known to READ the index right
(`ReadOK`), and the stage lemmas that call the knot take `CheckOK` at the index
they run at.
-/
import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.RecCheck
import ConRon.Bridge.Inductives.BlockWF

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

namespace BT

/-! ## The name-nodup guard -/

/-- con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup — the Boolean
test is `List.Nodup` (upstream's `nodup_of_nameNodup` is the one direction). -/
theorem name_nodup_iff : ∀ (ns : List ConLeche.Name), ConLeche.Name.nodup ns = true ↔ ns.Nodup
  | [] => by simp [ConLeche.Name.nodup]
  | n :: ns => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons,
      name_nodup_iff ns]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hm => ?_, h2⟩
      have : ns.contains n = true := List.contains_iff_mem.mpr hm
      rw [this] at h1; exact nomatch h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      cases hc : ns.contains n with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hc) h1

/-! ## The index after a table push -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the read invariant
survives ANY push whose projection-table case is well shaped**:
`Bridge/Checker/Inv.lean`'s `IFEnvOK.push` with its `hnp` (no table)
generalised to "a table only if well shaped", which is what the structure
tables of a mutual block need between two installs.  Belongs beside
`IFEnvOK.push`. -/
theorem _root_.ConRon.Bridge.IFEnvOK.pushT {env : Env} {fe : IFEnv} {s : AState}
    {ci : IConstantInfo} {c : ConstantInfo}
    (h : IFEnvOK env fe s) (hst : StateOK s) (hcoh : IFEnvCoh fe)
    (hproj : ∀ t, ci = .projInfo t → IProjTableOK s.store t)
    (hci : Frontend.denoteCI s.store ci = some c) :
    IFEnvOK ⟨c :: env.consts⟩ (fe.push ci) s := by
  obtain ⟨rk, hrk⟩ := hst.wf
  have hnm : denoteN s.store.ns ci.name = some c.name :=
    denoteCI_name_of (fun t ht => (hproj t ht).toNamed) hci
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
  refine ⟨?_, ?_, ?_⟩
  · intro n ci' hf
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
      rw [Env.find?_cons, if_neg, he]
      intro hq
      obtain rfl := denoteN_inj hrk.nsWF (hq ▸ hnm) hd
      simp at hb
  · intro nm c₀ he
    rw [Env.find?_cons] at he
    by_cases hq : c.name = nm
    · rw [if_pos hq] at he
      obtain rfl : c₀ = c := (Option.some.inj he).symm
      exact ⟨ci.name, ci, hq ▸ hnm, keyT, hci⟩
    · rw [if_neg hq] at he
      obtain ⟨n, ci', hd, hf, hc'⟩ := h.cover nm c₀ he
      refine ⟨n, ci', hd, ?_, hc'⟩
      cases hb : (ci.name == n) with
      | true =>
        obtain rfl : ci.name = n := by simpa using hb
        rw [hnm] at hd
        exact absurd (Option.some.inj hd) hq
      | false => rw [keyF n hb]; exact hf
  · intro n t hf
    cases hb : (ci.name == n) with
    | true =>
      obtain rfl : ci.name = n := by simpa using hb
      rw [keyT] at hf
      exact hproj t (Option.some.inj hf)
    | false =>
      rw [keyF n hb] at hf
      exact h.proj n t hf

/-- con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:52-85
checkStructProjTable — **the install's answer is ONE table pushed**: the
twin's run ends in `pure (fe.push (.projInfo …))`.  What
`checkStructProjTable_runF`'s `InstRel` does not say, and what the next
table's `IFEnvOKS` needs. -/
theorem checkStructProjTable_shape {T C : NIdx} {lps : List NIdx} {nP nF : Nat}
    {resSort : LIdx} {guards : List LIdx} {off : Nat} {cvCa : IConstantVal}
    {fe fe' : IFEnv} {s s' : AState}
    (hrun : Arena.checkStructProjTable T C lps nP nF resSort guards off cvCa fe s
      = .ok (fe', s')) :
    ∃ t, fe' = fe.push (.projInfo t) := by
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkStructProjTable] at hrun
  obtain ⟨o, s₁, -, z1⟩ := bindOk hrun
  obtain ⟨bodies, s₂, -, z2⟩ := bindOk z1
  obtain ⟨sc, s₃, -, z3⟩ := bindOk z2
  obtain ⟨-, z4⟩ := AM.dunless_ok hnever z3
  replace z4 := AM.pure_bind_ok z4
  obtain ⟨b5, s₅, -, z5⟩ := bindOk z4
  obtain ⟨-, z6⟩ := AM.dunless_ok hnever z5
  replace z6 := AM.pure_bind_ok z6
  obtain ⟨tn, s₆, -, z7⟩ := bindOk z6
  obtain ⟨-, z8⟩ := AM.dunless_ok hnever z7
  replace z8 := AM.pure_bind_ok z8
  obtain ⟨rfl, rfl⟩ := pureOk z8
  exact ⟨_, rfl⟩

/-- con-leche: none — `denoteLLists` at a cons, inverted. -/
theorem denoteLLists_cons_inv {st : EStore} {l : List LIdx} {ls : List (List LIdx)}
    {ys : List (List Level)} (h : denoteLLists st (l :: ls) = some ys) :
    ∃ y ys', ys = y :: ys' ∧ denoteLList st.ls l = some y ∧ denoteLLists st ls = some ys' := by
  simp only [denoteLLists] at h
  cases h1 : denoteLList st.ls l with
  | none => rw [h1] at h; exact nomatch h
  | some y =>
  cases h2 : denoteLLists st ls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some ys' =>
  rw [h1, h2] at h
  exact ⟨y, ys', (Option.some.inj h).symm, rfl, rfl⟩

theorem denoteLLists_nil_inv {st : EStore} {ys : List (List Level)}
    (h : denoteLLists st [] = some ys) : ys = [] := by
  simp only [denoteLLists, Option.some.injEq] at h; exact h.symm

theorem mapM_option_nil_inv {α β : Type} {f : α → Option β} {ys : List β}
    (h : ([] : List α).mapM f = some ys) : ys = [] := by
  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; exact h.symm

end BT

open BT

/-! ## The projection tables -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:108-123 checkBlockTables
con-leche: ConLeche/Verify/Cached/BlockRunC.lean:454 checkBlockTablesS_run —
**the projection table at every structure-like member**, the three lists
walked side by side as con-leche walks their zip.  Pure grade at the store
(the tables call no knot), but the index read (`checkStructProjTable`'s name
tests) needs `IFEnvOK` at the index each install starts from: the first from
the caller, every later one by `IFEnvOK.pushT` at the table the previous
install pushed (`checkStructProjTable_shape`), whose shape its own `ProjOut`
supplies. -/
theorem checkBlockTables_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape) :
    ∀ (ms : List Arena.MemberShape) (msP : List ConLeche.MemberShape)
      (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat)))
      (sss : List (List (List LIdx))) (sssP : List (List (List Level)))
      (fe : IFEnv) (env : Env) (s₀ s' : AState) (fe' : IFEnv),
      StateOK s₀ → PinsOK s₀ → IFEnvCoh fe → IFEnvOK env fe s₀ →
      denoteFEnv s₀.store fe = some env → dShape s₀.store p = some pP →
      ms.mapM (dMember s₀.store) = some msP → css.mapM (dCtors s₀.store) = some cssP →
      sss.mapM (denoteLLists s₀.store) = some sssP →
      Arena.checkBlockTables p ms css sss fe s₀ = .ok (fe', s') →
      PStep s₀ s' ∧ InstRel fe (fun e =>
        FOk (ConLeche.checkBlockTables pP (msP.zip (cssP.zip sssP)) env : FueledM Env) e)
        s'.store fe'
  | m :: ms, msP, cs :: css, cssP, ss :: sss, sssP, fe, env, s₀, s', fe',
      hok, hpins, hcoh, hienv, hfe, hsh, hms, hcss, hsss, hrun => by
    obtain ⟨mP, msP', rfl, hm, hms'⟩ := mapM_option_cons_inv hms
    obtain ⟨csP, cssP', rfl, hcs, hcss'⟩ := mapM_option_cons_inv hcss
    obtain ⟨ssP, sssP', rfl, hss, hsss'⟩ := mapM_option_cons_inv hsss
    simp only [List.zip_cons_cons]
    -- the member with no table: the rest, at the same index
    have skip : Arena.checkBlockTables p ms css sss fe s₀ = .ok (fe', s') →
        (∀ {x : FueledM Env}, FOk x env →
          PStep s₀ s' ∧ InstRel fe (fun e =>
            FOk (x >>= fun env' => ConLeche.checkBlockTables pP (msP'.zip (cssP'.zip sssP'))
              env') e) s'.store fe') := by
      intro h x hx
      obtain ⟨hstep, hrel⟩ := checkBlockTables_spec p pP ms msP' css cssP' sss sssP' fe env
        s₀ s' fe' hok hpins hcoh hienv hfe hsh hms' hcss' hsss' h
      exact ⟨hstep, hrel.imp fun e he => FOk.bind hx he⟩
    obtain ⟨hcvT, hnI, hcsm⟩ := RC.dMember_inv hm
    match cs, ss, csP, ssP, hcs, hss with
    | [(cA, nF)], [sorts], csP, ssP, hcs, hss =>
      obtain ⟨cAP', csP', rfl, hcA, hcs'⟩ := mapM_option_cons_inv hcs
      obtain rfl := mapM_option_nil_inv hcs'
      obtain ⟨sortsP, ssP', rfl, hsorts, hss'⟩ := denoteLLists_cons_inv hss
      obtain rfl := denoteLLists_nil_inv hss'
      simp only [dCtor, Option.map_eq_some_iff] at hcA
      obtain ⟨cAP, hcAP, rfl⟩ := hcA
      simp only [Arena.checkBlockTables] at hrun
      by_cases hi : (m.nIdx == 0) = true
      · rw [if_pos hi] at hrun
        obtain ⟨guards, s₁, h1, h2⟩ := bindOk hrun
        obtain ⟨p1, hg⟩ := structProjGuards_spec cA.type cAP.type p.nP nF sorts sortsP s₀ s₁
          guards hok hpins ⟨denoteCV_type hcAP, hsorts⟩ h1
        have hglen : guards.length = nF := by
          rw [denoteLList_length _ _ hg, structProjGuards_length]
        obtain ⟨-, -, hnP, -, hrs, -, -⟩ := RC.dShape_inv hsh
        have x1 := p1.ext
        obtain ⟨fe₂, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨p3, hrel3⟩ := checkStructProjTable_runF fe env m.cvT.name cA.name mP.cvT.name
          cAP.name p.lps pP.lps p.nP nF p.resSort pP.resSort guards
          (ConLeche.structProjGuards cAP.type p.nP nF sortsP) 1 cA cAP hglen hcoh s₁ s₂ fe₂
          p1.ok (hpins.mono x1 p1.pins)
          ⟨denoteN_ext (denoteCV_name hcvT) x1, denoteN_ext (denoteCV_name hcAP) x1,
            denoteNListE_ext x1 _ _ (BlockShape.lps_spec hsh), denoteL_ext hrs x1, hg,
            denoteCV_ext hcAP x1, denoteFEnv_ext x1 hfe, (hienv.mono x1).toS⟩ h3
        have x13 : Ext s₀.store s₂.store := x1.trans p3.ext
        obtain ⟨t, rfl⟩ := checkStructProjTable_shape h3
        obtain ⟨env₁, hden₁, hF₁⟩ := hrel3.denote
        obtain ⟨c, hc, rfl⟩ := denoteFEnv_push_inv (denoteFEnv_ext x13 hfe) hden₁
        have htab : IProjTableOK s₂.store t := by
          have hself : (fe.push (.projInfo t)).find? (IConstantInfo.projInfo t).name
              = some (.projInfo t) := by
            rw [(hcoh.push _).find?]
            simp [IFEnv.push, IEnv.find?]
          rcases hrel3.proj.1 _ t hself with h' | h'
          · exact (hienv.proj _ t h').mono x13
          · exact h'
        have hienv₂ : IFEnvOK ⟨c :: env.consts⟩ (fe.push (.projInfo t)) s₂ :=
          (hienv.mono x13).pushT p3.ok hcoh (fun t' ht' => by cases ht'; exact htab) hc
        obtain ⟨p4, hrel4⟩ := checkBlockTables_spec p pP ms msP' css cssP' sss sssP'
          (fe.push (.projInfo t)) ⟨c :: env.consts⟩ s₂ s' fe' p3.ok
          (hpins.mono x13 (by rw [p3.pins, p1.pins])) hrel3.coh hienv₂ hden₁
          (dShape_ext x13 _ _ hsh) (dMember_ext.list x13 _ _ hms')
          (dCtors_ext.list x13 _ _ hcss') (DExt.list (d := denoteLLists) (fun hx x y h => BI.denoteLLists_ext hx x y h) x13 _ _ hsss') h4
        refine ⟨p1.trans (p3.trans p4), (InstRel.trans p4.ext hrel3 hrel4).imp fun e he => ?_⟩
        rw [ConLeche.checkBlockTables]
        dsimp only
        rw [if_pos (hnI ▸ hi)]
        rw [hnP] at hF₁
        exact FOk.bind hF₁ he
      · rw [if_neg hi] at hrun
        refine skip hrun ?_
        simp only [hnI] at hi
        dsimp only
        rw [if_neg hi]
        exact FOk.pure env
    | [], _, csP, ssP, hcs, hss =>
      obtain rfl := mapM_option_nil_inv hcs
      simp only [Arena.checkBlockTables] at hrun
      exact skip hrun (FOk.pure env)
    | [_], [], csP, ssP, hcs, hss =>
      obtain ⟨_, csP', rfl, -, hcs'⟩ := mapM_option_cons_inv hcs
      obtain rfl := mapM_option_nil_inv hcs'
      obtain rfl := denoteLLists_nil_inv hss
      simp only [Arena.checkBlockTables] at hrun
      exact skip hrun (FOk.pure env)
    | [_], _ :: _ :: _, csP, ssP, hcs, hss =>
      obtain ⟨_, csP', rfl, -, hcs'⟩ := mapM_option_cons_inv hcs
      obtain rfl := mapM_option_nil_inv hcs'
      obtain ⟨_, ssP', rfl, -, hss'⟩ := denoteLLists_cons_inv hss
      obtain ⟨_, ssP'', rfl, -, -⟩ := denoteLLists_cons_inv hss'
      simp only [Arena.checkBlockTables] at hrun
      exact skip hrun (FOk.pure env)
    | _ :: _ :: _, ss, csP, ssP, hcs, hss =>
      obtain ⟨_, csP', rfl, -, hcs'⟩ := mapM_option_cons_inv hcs
      obtain ⟨_, csP'', rfl, -, -⟩ := mapM_option_cons_inv hcs'
      simp only [Arena.checkBlockTables] at hrun
      exact skip hrun (FOk.pure env)
  | [], msP, css, cssP, sss, sssP, fe, env, s₀, s', fe', hok, _, hcoh, _, hfe, _, hms, _, _,
      hrun => by
    obtain rfl := mapM_option_nil_inv hms
    simp only [Arena.checkBlockTables] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, FOk.pure env⟩,
      ProjOut.refl _ _⟩
  | _ :: _, msP, [], cssP, sss, sssP, fe, env, s₀, s', fe', hok, _, hcoh, _, hfe, _, _, hcss,
      _, hrun => by
    obtain rfl := mapM_option_nil_inv hcss
    simp only [Arena.checkBlockTables] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, ?_⟩,
      ProjOut.refl _ _⟩
    simp only [List.zip_nil_left, List.zip_nil_right]
    exact FOk.pure env
  | _ :: _, msP, _ :: _, cssP, [], sssP, fe, env, s₀, s', fe', hok, _, hcoh, _, hfe, _, _, _,
      hsss, hrun => by
    obtain rfl := mapM_option_nil_inv hsss
    simp only [Arena.checkBlockTables] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, ?_⟩,
      ProjOut.refl _ _⟩
    simp only [List.zip_nil_right]
    exact FOk.pure env


end ConRon.Bridge.Inductives
