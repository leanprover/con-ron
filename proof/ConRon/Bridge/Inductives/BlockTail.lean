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
import ConRon.Bridge.Inductives.GenRec
import ConRon.Bridge.Inductives.BlockWF
import ConLeche.Verify.Inductives.PositivityInv

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

/-- con-leche: none — `denoteLLists` at the empty list, inverted. -/
theorem denoteLLists_nil_inv {st : EStore} {ys : List (List Level)}
    (h : denoteLLists st [] = some ys) : ys = [] := by
  simp only [denoteLLists, Option.some.injEq] at h; exact h.symm

/-- con-leche: none — `Option`'s `mapM` at the empty list, inverted. -/
theorem mapM_option_nil_inv {α β : Type} {f : α → Option β} {ys : List β}
    (h : ([] : List α).mapM f = some ys) : ys = [] := by
  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; exact h.symm

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — a pushed index that
denotes had a denoting index under it, and the pushed row denotes. -/
theorem denoteFEnv_push_pre {st : EStore} {fe : IFEnv} {ci : IConstantInfo} {e : Env}
    (h : denoteFEnv st (fe.push ci) = some e) :
    ∃ e₀ c, denoteFEnv st fe = some e₀ ∧ Frontend.denoteCI st ci = some c ∧
      e = ⟨c :: e₀.consts⟩ := by
  simp only [denoteFEnv, denoteIEnv, IFEnv.push, Option.map_eq_some_iff] at h ⊢
  obtain ⟨cs, hcs, rfl⟩ := h
  simp only [Frontend.denoteCIList] at hcs
  cases hc : Frontend.denoteCI st ci with
  | none => rw [hc] at hcs; simp at hcs
  | some c =>
  cases hr : Frontend.denoteCIList st fe.env.consts with
  | none => rw [hc, hr] at hcs; simp at hcs
  | some r =>
  rw [hc, hr] at hcs
  obtain rfl := (Option.some.inj hcs).symm
  exact ⟨⟨r⟩, c, ⟨r, rfl, rfl⟩, rfl, rfl⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the read invariant
survives a run of non-table pushes**: `IFEnvOK.push`, iterated. -/
theorem IFEnvOK_pushAll {s : AState} (hst : StateOK s) :
    ∀ (l : List IConstantInfo) (fe : IFEnv) (env env' : Env),
      IFEnvOK env fe s → IFEnvCoh fe → (∀ ci ∈ l, ∀ t, ci ≠ .projInfo t) →
      denoteFEnv s.store fe = some env →
      denoteFEnv s.store (l.foldl IFEnv.push fe) = some env' →
      IFEnvOK env' (l.foldl IFEnv.push fe) s
  | [], fe, env, env', h, _, _, hd, hd' => by
    simp only [List.foldl_nil] at hd' ⊢
    rw [hd] at hd'
    obtain rfl := Option.some.inj hd'
    exact h
  | ci :: l, fe, env, env', h, hcoh, hnp, hd, hd' => by
    simp only [List.foldl_cons] at hd' ⊢
    have pre : ∀ (l : List IConstantInfo) (fe : IFEnv) (e : Env),
        denoteFEnv s.store (l.foldl IFEnv.push fe) = some e →
        ∃ e₀, denoteFEnv s.store fe = some e₀ := by
      intro l
      induction l with
      | nil => intro fe e h; exact ⟨e, h⟩
      | cons x l ih =>
        intro fe e h
        obtain ⟨e₁, h₁⟩ := ih (fe.push x) e h
        obtain ⟨e₀, _, h₀, -⟩ := denoteFEnv_push_pre h₁
        exact ⟨e₀, h₀⟩
    obtain ⟨e₁, h₁⟩ := pre l (fe.push ci) env' hd'
    obtain ⟨e₀, c, h₀, hc, rfl⟩ := denoteFEnv_push_pre h₁
    rw [hd] at h₀
    obtain rfl := Option.some.inj h₀
    exact IFEnvOK_pushAll hst l (fe.push ci) _ env'
      (h.push hst hcoh (hnp ci (List.mem_cons_self ..)) hc) (hcoh.push ci)
      (fun x hx => hnp x (List.mem_cons_of_mem _ hx)) h₁ hd'

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:93-106 consBlockRecsT —
**the recursors' cons only pushes recursors**: its answer is its argument
with a list of `.recInfo` rows pushed, no projection table among them. -/
theorem consBlockRecsTF_shape (vis₂ : Nat) (p : Arena.BlockShape) :
    ∀ (m : Nat) (out : List (IConstantVal × Arena.TargetMajor × List EIdx)) (fe : IFEnv)
      (s s' : AState) (fe' : IFEnv),
      Arena.consBlockRecsTF vis₂ p m out fe s = .ok (fe', s') →
      ∃ l : List IConstantInfo, (∀ ci ∈ l, ∀ t, ci ≠ .projInfo t) ∧
        fe' = l.foldl IFEnv.push fe
  | _, [], fe, s, s', fe', h => by
    simp only [Arena.consBlockRecsTF] at h
    obtain ⟨rfl, -⟩ := pureOk h
    exact ⟨[], by simp, rfl⟩
  | m, (cv, M, rhss) :: rest, fe, s, s', fe', h => by
    simp only [Arena.consBlockRecsTF] at h
    obtain ⟨rules, s₁, -, h2⟩ := bindOk h
    obtain ⟨l, hl, rfl⟩ := consBlockRecsTF_shape vis₂ p _ rest _ s₁ s' fe' h2
    refine ⟨_ :: l, fun ci hci t => ?_, rfl⟩
    rcases List.mem_cons.1 hci with rfl | hci
    · simp
    · exact hl ci hci t

/-- con-leche: none — **an index with the same list, coherent, is the same
install** (`InstRel` at the identity): the recursor stage hands its index
back after popping its temporary recursors (`IFEnv.popTemp`), with the list it
was handed. -/
theorem InstRel.same {fe fe' : IFEnv} {env : Env} {st : EStore} (hcoh : IFEnvCoh fe)
    (hcoh' : IFEnvCoh fe') (he : fe'.env = fe.env) (hd : denoteFEnv st fe = some env) :
    InstRel fe (fun e => e = env) st fe' := by
  have hf : fe'.find? = fe.find? := by
    funext n; rw [hcoh'.find?, hcoh.find?, he]
  refine ⟨hcoh', ⟨[], by rw [he]; rfl⟩, ?_, ⟨env, ?_, rfl⟩, ?_, ?_⟩
  · rw [hcoh.1, hcoh'.1, he]; exact Nat.le_refl _
  · simp only [denoteFEnv] at hd ⊢; rw [he]; exact hd
  · intro n t h; left; rw [← hf]; exact h
  · intro t h; left; rw [← he]; exact h

/-- con-leche: none — `CheckOK` reads the index only through `find?`. -/
theorem CheckOK.of_find? {μ : CheckMode} {env : Env} {fe fe' : IFEnv} {s : AState}
    (h : CheckOK μ env fe s) (e : fe'.find? = fe.find?) : CheckOK μ env fe' s :=
  ⟨h.state, h.caches, h.pins, RC.IFEnvOK.of_find? h.ienv e⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:266-274 blockNestCtx —
**the walk's canonical parameters are scoped at the parameter count**
(`blockNestCtxS_sim₂`'s `hpar`, read off the pure run): they are the first
former's telescope opened at the parameters (`openPisAtFvars_WScoped`). -/
theorem blockNestCtx_params_scoped {pP : ConLeche.BlockShape} {cvsP : List ConstantVal}
    {find? : ConLeche.Name → Option ConstantInfo} {v : ConLeche.NestCtx × List Expr}
    (hT : ∀ cv ∈ cvsP, Expr.WScoped 0 cv.type)
    (h : FOk (ConLeche.blockNestCtx (m := FueledM) pP cvsP find?) v) :
    ∀ x ∈ v.1.params, Expr.WScoped pP.nP x := by
  obtain ⟨F, hF⟩ := h
  rw [blockNestCtx_datF] at hF
  obtain ⟨ctx, holes⟩ := v
  obtain ⟨cv0, fvs, rest, h0, hop, rfl, -⟩ := ConLeche.blockNestCtx_inv hF
  intro x hx
  have := (ConLeche.openPisAtFvars_WScoped pP.nP cv0.type 0 hop
    (hT cv0 (List.mem_of_mem_head? h0))).1 x hx
  simpa using this

/-- con-leche: none — a walk state's table, denoted. -/
theorem dState_ctorNfs {st : EStore} {ns : Arena.NestState} {nsP : ConLeche.NestState}
    (h : dState st ns = some nsP) :
    ns.ctorNfs.toList.mapM (dCtorNf st) = some nsP.ctorNfs.toList := by
  simp only [dState, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, rfl⟩ := h
  simpa using h3

end BT

open BT

/-! ## The pass's record, denoted -/


/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:25-52 BlockPass —
**the twin's pass record denotes con-leche's**, at the environment `env₁` its
`env1` index denotes (`denoteFEnv`, carried beside it): every handle field
through its own denotation, the field kinds through `kindOf`, the positivity
table (a `List` in the twin, an `Array` upstream) entry by entry. -/
def dPass (st : EStore) (env₁ : Env) (q : Arena.BlockPass) :
    Option (ConLeche.BlockPass Env) := do
  let cvTas ← q.cvTas.mapM (Frontend.denoteCV st)
  let p ← dParts st q.p
  let ctorsAs ← q.ctorsAs.mapM (dCtors st)
  let sortsss ← q.sortsss.mapM (denoteLLists st)
  let nfs ← q.nfs.mapM (Frontend.denoteEList st)
  let params ← Frontend.denoteEList st q.params
  let rd ← dClassRead st q.rd
  let cls ← q.cls.mapM (dMajor st)
  let tbl ← q.tbl.mapM (dCtorNf st)
  pure ⟨env₁, cvTas, p, ctorsAs, sortsss, q.kinds.map (·.map (·.map kindOf)), nfs, params, rd,
    cls, tbl.toArray⟩

/-- con-leche: none — `dPass`, taken apart. -/
theorem dPass_inv {st : EStore} {env₁ : Env} {q : Arena.BlockPass}
    {qP : ConLeche.BlockPass Env} (h : dPass st env₁ q = some qP) :
    qP.env₁ = env₁ ∧ q.cvTas.mapM (Frontend.denoteCV st) = some qP.cvTas ∧
      dParts st q.p = some qP.p ∧ q.ctorsAs.mapM (dCtors st) = some qP.ctorsAs ∧
      q.sortsss.mapM (denoteLLists st) = some qP.sortsss ∧
      qP.kinds = q.kinds.map (·.map (·.map kindOf)) ∧
      q.nfs.mapM (Frontend.denoteEList st) = some qP.nfs ∧
      Frontend.denoteEList st q.params = some qP.params ∧
      dClassRead st q.rd = some qP.rd ∧ q.cls.mapM (dMajor st) = some qP.cls ∧
      q.tbl.mapM (dCtorNf st) = some qP.tbl.toList := by
  simp only [dPass, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, a5, h5, a6, h6, a7, h7, a8, h8, a9, h9, rfl⟩ := h
  exact ⟨rfl, h1, h2, h3, h4, rfl, h5, h6, h7, h8, by simpa using h9⟩

/-- con-leche: none — and built from its parts. -/
theorem dPass_mk {st : EStore} {env₁ : Env} {q : Arena.BlockPass}
    {cvTas : List ConstantVal} {p : ConLeche.BlockParts}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {nfs : List (List Expr)} {params : List Expr} {rd : ConLeche.ClassRead}
    {cls : List ConLeche.TargetMajor} {tbl : List ConLeche.NestCtorNf}
    (h1 : q.cvTas.mapM (Frontend.denoteCV st) = some cvTas) (h2 : dParts st q.p = some p)
    (h3 : q.ctorsAs.mapM (dCtors st) = some ctorsAs)
    (h4 : q.sortsss.mapM (denoteLLists st) = some sortsss)
    (h5 : q.nfs.mapM (Frontend.denoteEList st) = some nfs)
    (h6 : Frontend.denoteEList st q.params = some params) (h7 : dClassRead st q.rd = some rd)
    (h8 : q.cls.mapM (dMajor st) = some cls) (h9 : q.tbl.mapM (dCtorNf st) = some tbl) :
    dPass st env₁ q = some ⟨env₁, cvTas, p, ctorsAs, sortsss,
      q.kinds.map (·.map (·.map kindOf)), nfs, params, rd, cls, tbl.toArray⟩ := by
  simp only [dPass, h1, h2, h3, h4, h5, h6, h7, h8, h9, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

/-- con-leche: none — `dPass` survives the arena's growth. -/
theorem dPass_ext {env₁ : Env} : DExt (fun st q => dPass st env₁ q) := by
  intro st st' hx q qP h
  obtain ⟨he, h1, h2, h3, h4, hk, h5, h6, h7, h8, h9⟩ := dPass_inv h
  obtain ⟨e, cv, p, ca, ss, k, nf, pa, rd, cl, tb⟩ := qP
  simp only at he hk h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst he hk
  have := dPass_mk (env₁ := e) (dExt_denoteCV.list hx _ _ h1) (dParts_ext hx _ _ h2)
    (dCtors_ext.list hx _ _ h3)
    (DExt.list (d := denoteLLists) (fun hx x y h => BI.denoteLLists_ext hx x y h) hx _ _ h4)
    (dExt_denoteEList.list hx _ _ h5) (denoteEList_ext hx _ _ h6) (dClassRead_ext hx _ _ h7)
    (dMajor_ext.list hx _ _ h8) (dCtorNf_ext.list hx _ _ h9)
  show dPass st' e q = _
  rw [this]

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



/-! ## The three stages this module consumes from `GenRec.lean`, named

The pass and the tail are assembled over three stage statements that
`Bridge/Inductives/GenRec.lean` proves (`checkBlockClasses`, `classSeeds`,
`genRecCheck`); they are named here so that the assembly states exactly the
shape it consumes. -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:518-536 checkBlockClasses
— the classes stage's statement, as the pass consumes it
(`checkBlockClassesS_sim`'s hypotheses). -/
def ClassesStageSpec (μ : CheckMode) : Prop :=
  ∀ (fe₁ : IFEnv) (env₁ : Env) (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (params : List EIdx) (paramsP : List Expr) (ctorsAs : List (List (IConstantVal × Nat)))
    (ctorsAsP : List (List (ConstantVal × Nat))),
    EnvWF env₁ → paramsP.length = pP.nP → (∀ x ∈ paramsP, Expr.WScoped pP.nP x) →
    CSpecF μ env₁ fe₁
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st params = some paramsP ∧
        ctorsAs.mapM (dCtors st) = some ctorsAsP ∧ denoteFEnv st fe₁ = some env₁)
      (Arena.checkBlockClasses μ fe₁ p params ctorsAs)
      (fun st r v => dClassRead st r.1 = some v.1 ∧ r.2.mapM (dMajor st) = some v.2 ∧
        ∀ M ∈ v.2, ConLeche.Cached.ClassMajScoped pP.nP M)
      (ConLeche.checkBlockClasses (fueledOpsM μ) (mkFEnv env₁) env₁ pP paramsP ctorsAsP)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:494-499 classSeeds — the
seeds' statement, as the pass consumes it. -/
def SeedsStageSpec : Prop :=
  ∀ (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) (holes : List EIdx)
    (holesP : List Expr) (ms : List Arena.TargetMajor) (msP : List ConLeche.TargetMajor)
    (fnd : ConLeche.Name → Option ConstantInfo),
    PSpecP (fun st => dCtx st fnd ctx = some ctxP ∧ Frontend.denoteEList st holes = some holesP ∧
        ms.mapM (dMajor st) = some msP)
      (Arena.classSeeds ctx holes ms)
      (fun st r => r.mapM (fun k => (dKey st k.1).map (·, k.2))
        = some (ConLeche.classSeeds ctxP holesP msP))

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:76-91 checkBlockRec
con-leche: ConLeche/Verify/Cached/GenRecC.lean:773 genRecCheckS_run — the
recursor stage's statement, as the tail consumes it: the index handed back is
the one handed in (the temporary recursors popped), the checked family
denotes, and its names are fresh in the constructors' environment (what
`consBlockRecsTF_spec` needs). -/
def RecStageSpec (μ : CheckMode) : Prop :=
  ∀ (fe₂ : IFEnv) (env₂ : Env) (p : Arena.BlockParts) (pP : ConLeche.BlockParts)
    (nested : Bool) (params : List EIdx) (paramsP : List Expr) (tbl : List Arena.NestCtorNf)
    (tblP : List ConLeche.NestCtorNf) (rd : Arena.ClassRead) (rdP : ConLeche.ClassRead)
    (ms : List Arena.TargetMajor) (msP : List ConLeche.TargetMajor)
    (cvTas : List IConstantVal) (cvTasP : List ConstantVal) (block : List IConstantInfo)
    (blockP : List ConstantInfo),
    EnvWF env₂ → IFEnvCoh fe₂ → (∀ cv ∈ cvTasP, Expr.WScoped 0 cv.type) →
    (∀ M ∈ msP, ConLeche.Cached.ClassMajScoped pP.nP M) →
    CSpecF μ env₂ fe₂
      (fun st => denoteFEnv st fe₂ = some env₂ ∧ dParts st p = some pP ∧
        Frontend.denoteEList st params = some paramsP ∧ tbl.mapM (dCtorNf st) = some tblP ∧
        dClassRead st rd = some rdP ∧ ms.mapM (dMajor st) = some msP ∧
        cvTas.mapM (Frontend.denoteCV st) = some cvTasP ∧
        Frontend.denoteCIList st block = some blockP)
      (Arena.checkBlockRec μ fe₂ p nested params tbl rd ms block cvTas)
      (fun st r out => IFEnvCoh r.1 ∧ r.1.env = fe₂.env ∧ r.2.mapM (dRecOut st) = some out ∧
        ∀ t ∈ out, env₂.find? t.1.name = none)
      (ConLeche.checkBlockRec (fueledOpsM μ) env₂ pP nested paramsP tblP rdP msP blockP cvTasP)

/-! ## The install after the pass -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:125-138 checkBlockTail
con-leche: ConLeche/Verify/Cached/GenRecC.lean:868 checkBlockTailS_run —
**the install after the pass**, from the formers' index `q.env1` (whose
caches are sound: the pass's last stages ran there): the index binders'
sorts, the constructors consed, the flush entering them (`ReadOK.flush`), the
recursor stage (`hGR`: the stage lemma at this call), the recursors consed
at the constructors' view, the tables.  The answer is an install over
`q.env1` whose denotation con-leche's `checkBlockTail` produces. -/
theorem checkBlockTail_of {μ : CheckMode} (hk : CoreSpec μ Arena.checkFuel)
    {env₁ : Env} {q : Arena.BlockPass} {qP : ConLeche.BlockPass Env}
    {block : List IConstantInfo} {blockP : List ConstantInfo} {s s' : AState} {fe' : IFEnv}
    (hGR : RecStageSpec μ)
    (henv₁ : EnvWF env₁) (hck : CheckOK μ env₁ q.env1 s) (hcoh : IFEnvCoh q.env1)
    (hden : denoteFEnv s.store q.env1 = some env₁) (hq : dPass s.store env₁ q = some qP)
    (hb : Frontend.denoteCIList s.store block = some blockP)
    (hT : ∀ cv ∈ qP.cvTas, Expr.WScoped 0 cv.type)
    (henv₂ : EnvWF (ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)
    (hrun : Arena.checkBlockTail μ block q s = .ok (fe', s')) :
    InstStep s s' ∧
      InstRel q.env1 (fun e => FOk (ConLeche.checkBlockTail (fueledOpsM μ) blockP qP) e)
        s'.store fe' := by
  obtain ⟨he, hcv, hp, hca, hss, hkd, hnf, hpa, hrd, hcl, htb⟩ := dPass_inv hq
  obtain ⟨shP, hsh, hpP⟩ : ∃ shP, dShape s.store q.p.shape = some shP ∧ qP.p = ⟨shP⟩ := by
    simp only [dParts, Option.map_eq_some_iff] at hp
    obtain ⟨shP, h1, h2⟩ := hp
    exact ⟨shP, h1, h2.symm⟩
  obtain ⟨hms, -, hnP, -, -, -, -⟩ := RC.dShape_inv hsh
  simp only [Arena.checkBlockTail] at hrun
  -- the index binders' sorts
  obtain ⟨isorts, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨c1, isP, -, hisF⟩ := checkBlockIdxSorts_specF q.env1 hk henv₁ q.p.shape shP
    q.p.shape.members shP.members q.cvTas qP.cvTas hT s s₁ isorts hck ⟨hsh, hms, hcv, hden⟩ h1
  have x1 := c1.ext
  -- the constructors consed
  obtain ⟨hcons, hconsOK⟩ := consBlockCtors_spec s₁.store q.p.shape.nP q.ctorsAs qP.ctorsAs
    q.env1 env₁ (dCtors_ext.list x1 _ _ hca) (denoteFEnv_ext x1 hden) hcoh
  rw [hnP, ← show qP.p.nP = shP.nP by rw [hpP]] at hcons hconsOK
  rw [← show qP.p.nP = shP.nP by rw [hpP]] at hnP
  generalize hfe₂ : Arena.consBlockCtors q.p.shape.nP q.ctorsAs q.env1 = fe₂ at h2
  rw [hnP] at hfe₂
  subst hfe₂
  generalize hE₂ : ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁ = env₂ at henv₂ hcons hconsOK
  have hden₂ : denoteFEnv s₁.store (Arena.consBlockCtors qP.p.nP q.ctorsAs q.env1) = some env₂ := by
    obtain ⟨e, h, rfl⟩ := hcons.denote; exact h
  -- the flush entering them
  obtain ⟨u, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush (μ := μ)
    (⟨c1.ok.state, c1.ok.pins, hconsOK c1.ok.state.wf (c1.ok.ienv.toS) s₁ rfl⟩ :
      ReadOK env₂ (Arena.consBlockCtors qP.p.nP q.ctorsAs q.env1) s₁) h3
  have x2 : Ext s.store s₂.store := by rw [hs2]; exact x1
  -- the recursor stage
  obtain ⟨⟨fe₂b, out⟩, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨-, hcv', hp', hca', hss', -, hnf', hpa', hrd', hcl', htb'⟩ :=
    dPass_inv (dPass_ext x2 _ _ hq)
  obtain ⟨c3, outP, ⟨hcoh₂b, hfe₂b, hout, hfresh⟩, hGRF⟩ := hGR _ env₂ q.p qP.p _ q.params
    qP.params q.tbl qP.tbl.toList q.rd qP.rd q.cls qP.cls q.cvTas qP.cvTas block blockP henv₂
    hcons.coh hT hMs s₂ s₃ (fe₂b, out) c2
    ⟨by rw [hs2]; exact hden₂, hp', hpa', htb', hrd', hcl', hcv', denoteCIList_ext x2 _ _ hb⟩ h5
  rw [blockNestedBit_eq hsh, ← hkd, ← show qP.p.toBlockShape = shP by rw [hpP]] at hGRF
  have x3 := c3.ext
  dsimp only at h6
  -- the recursors consed at the constructors' view
  obtain ⟨fe₃, s₄, h7, h8⟩ := bindOk h6
  have hvis : fe₂b.visibleBelow = (Arena.consBlockCtors qP.p.nP q.ctorsAs q.env1).visibleBelow := by
    rw [hcoh₂b.1, hcons.coh.1, hfe₂b]
  have hfind₂b : fe₂b.find? = (Arena.consBlockCtors qP.p.nP q.ctorsAs q.env1).find? := by
    funext n; rw [hcoh₂b.find?, hcons.coh.find?, hfe₂b]
  have hden₂b : denoteFEnv s₃.store fe₂b = some env₂ := by
    have h' := denoteFEnv_ext (show Ext s₁.store s₃.store by rw [← hs2]; exact x3) hden₂
    simp only [denoteFEnv] at h' ⊢; rw [hfe₂b]; exact h'
  have x03 : Ext s.store s₃.store := x2.trans x3
  have hview : (fe₂b.restrictTo (Arena.consBlockCtors qP.p.nP q.ctorsAs q.env1).visibleBelow).find?
      = (Arena.consBlockCtors qP.p.nP q.ctorsAs q.env1).find? := by
    rw [← hvis]; exact hfind₂b
  obtain ⟨c4, hrel4⟩ := consBlockRecsTF_spec (μ := μ)
    (Arena.consBlockCtors qP.p.nP q.ctorsAs q.env1).visibleBelow q.p.shape shP out outP 0
    fe₂b env₂ s₃ s₄ fe₃ c3.ok (RC.IFEnvOK.of_find? c3.ok.ienv hview) (Nat.le_of_eq hvis.symm)
    hcoh₂b hden₂b (dShape_ext x03 _ _ hsh) hout hfresh h7
  have x4 := c4.ext
  obtain ⟨env₃, hden₃, rfl⟩ := hrel4.denote
  obtain ⟨l, hl, hfe₃⟩ := consBlockRecsTF_shape _ _ _ _ _ _ _ _ h7
  have hienv₃ : IFEnvOK (consBlockRecsT env₂.find? (·.constsResolve env₂) shP 0 outP env₂)
      fe₃ s₄ := by
    subst hfe₃
    exact IFEnvOK_pushAll c4.ok.state l fe₂b env₂ _
      (RC.IFEnvOK.of_find? c4.ok.ienv hfind₂b) hcoh₂b hl (denoteFEnv_ext x4 hden₂b) hden₃
  have x04 : Ext s.store s₄.store := x03.trans x4
  -- the projection tables
  obtain ⟨p5, hrel5⟩ := checkBlockTables_spec q.p.shape shP q.p.shape.members shP.members
    q.ctorsAs qP.ctorsAs q.sortsss qP.sortsss fe₃ _ s₄ s' fe' c4.ok.state c4.ok.pins hrel4.coh
    hienv₃ hden₃ (dShape_ext x04 _ _ hsh) (dMember_ext.list x04 _ _ hms)
    (dCtors_ext.list x04 _ _ hca)
    (DExt.list (d := denoteLLists) (fun hx x y h => BI.denoteLLists_ext hx x y h) x04 _ _ hss)
    h8
  have x5 := p5.ext
  -- the chain
  have r12 := InstRel.same (st := s₃.store) hcons.coh hcoh₂b hfe₂b
    (denoteFEnv_ext (show Ext s₁.store s₃.store by rw [← hs2]; exact x3) hden₂)
  have r0 := InstRel.trans (show Ext s₁.store s₃.store by rw [← hs2]; exact x3) hcons r12
  have r03 := InstRel.trans x4 r0 hrel4
  have r05 := InstRel.trans x5 r03 hrel5
  refine ⟨(c1.toInst.trans i2).trans (c3.toInst.trans (c4.toInst.trans p5.toInst)), ?_⟩
  refine r05.imp fun e he' => ?_
  obtain ⟨env₁', cvTasP, pP', ctorsAsP, sortsssP, kindsP, nfsP, paramsP, rdP, clsP, tblP⟩ := qP
  simp only at he hpP hisF hGRF hE₂ hfresh he' hkd
  subst he hpP
  subst hE₂
  unfold ConLeche.checkBlockTail
  exact FOk.bind hisF (FOk.bind hGRF he')


/-! ## The pass -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:54-74 checkBlockPass
con-leche: ConLeche/Verify/Cached/GenRecC.lean:931 checkBlockPassS_run —
**one pass over the formers, the constructors and the classes**: the formers
(at the entry index, `CheckOK` there), the flush entering the index that
holds them all, then every other stage at that index.  The answer denotes the
pass con-leche's `checkBlockPass` produces, with the facts the tail needs:
the caches sound at the formers' index, both environments well formed, the
formers' types closed, the classes scoped. -/
theorem checkBlockPass_of {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel)
    (hCL : ClassesStageSpec μ) (hCS : SeedsStageSpec)
    {env : Env} {fe : IFEnv} {p₀ : Arena.BlockParts} {p₀P : ConLeche.BlockParts}
    {isRec : Bool} {s s' : AState} {q : Arena.BlockPass}
    (henv : EnvWF env) (hck : CheckOK μ env fe s) (hcoh : IFEnvCoh fe)
    (hden : denoteFEnv s.store fe = some env) (hp : dParts s.store p₀ = some p₀P)
    (hrun : Arena.checkBlockPass μ fe p₀ isRec s = .ok (q, s')) :
    ∃ env₁ qP, InstStep s s' ∧ CheckOK μ env₁ q.env1 s' ∧
      InstRel fe (fun e => e = env₁) s'.store q.env1 ∧ EnvWF env₁ ∧
      dPass s'.store env₁ q = some qP ∧ (∀ cv ∈ qP.cvTas, Expr.WScoped 0 cv.type) ∧
      EnvWF (ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁) ∧
      (∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M) ∧
      FOk (ConLeche.checkBlockPass (fueledOpsM μ) env p₀P isRec) qP := by
  simp only [Arena.checkBlockPass] at hrun
  -- the formers
  obtain ⟨⟨fe₁, cvTas, p₁⟩, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨c1, ⟨env₁, cvTasP, p₁P⟩, ⟨hrel1, hOKS1, hcvs, hsh1, hT⟩, hF1⟩ :=
    checkBlockInds_spec fe hμ hk henv hcoh p₀ p₀P isRec s s₁ _ hck ⟨hp, hden⟩ h1
  dsimp only at h2 hrel1 hOKS1 hcvs hsh1 hT hF1
  have henv₁ : EnvWF env₁ := by
    obtain ⟨F, hF⟩ := hF1
    rw [checkBlockInds_datF] at hF
    exact (direct_block_inds_wf henv hF).1
  have hden₁ : denoteFEnv s₁.store fe₁ = some env₁ := by
    obtain ⟨e, h, rfl⟩ := hrel1.denote; exact h
  -- the flush entering the formers' index
  obtain ⟨u, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush (μ := μ)
    (⟨c1.ok.state, c1.ok.pins, hOKS1 s₁ rfl⟩ : ReadOK env₁ fe₁ s₁) h3
  simp only [Arena.BlockParts.complete] at h4
  have x2 : Ext s₁.store s₂.store := by rw [hs2]; exact Ext.refl _
  obtain ⟨hms1, -⟩ := RC.dShape_inv hsh1
  -- the constructors
  obtain ⟨⟨ctorsAs, sortsss⟩, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨c3, ⟨ctorsAsP, sortsssP⟩, ⟨hca, hss⟩, hF3⟩ :=
    checkBlockCtors_specF fe₁ fe₁ hμ hk henv₁ p₁ p₁P env₁ p₁.members p₁P.members cvTas cvTasP
      hT s₂ s₃ _ c2
      ⟨dShape_ext x2 _ _ hsh1, dMember_ext.list x2 _ _ hms1, dExt_denoteCV.list x2 _ _ hcvs,
        denoteFEnv_ext x2 hden₁, denoteFEnv_ext x2 hden₁, c2.ienv.toS⟩ h5
  dsimp only at h6 hca hss hF3
  have x3 := c3.ext
  -- the walk's context
  obtain ⟨⟨ctx, holes⟩, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨c4, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, hlen, hnh, hnP⟩, hF4⟩ :=
    blockNestCtx_spec (μ := μ) fe₁ henv₁ p₁ p₁P cvTas cvTasP hT s₃ s₄ _ c3.ok
      ⟨dShape_ext (x2.trans x3) _ _ hsh1, dExt_denoteCV.list (x2.trans x3) _ _ hcvs⟩ h7
  dsimp only at h8 hctx hholes hctxOk hhw hpar hlen hnh hnP hF4
  have hparN := blockNestCtx_params_scoped hT hF4
  dsimp only at hparN
  have x4 := c4.ext
  have x14 : Ext s₁.store s₄.store := x2.trans (x3.trans x4)
  obtain ⟨namesP, lpsP, paramsP, sortP, hctxEq, -, -, hparams, -, -⟩ := dCtx_inv hctx
  -- the classes
  obtain ⟨⟨rd, ms⟩, s₅, h9, h10⟩ := bindOk h8
  obtain ⟨c5, ⟨rdP, msP⟩, ⟨hrd, hmsP, hMsc⟩, hF5⟩ :=
    hCL fe₁ env₁ p₁ p₁P ctx.params ctxP.params ctorsAs ctorsAsP henv₁ (by rw [hlen, hnP])
      (by rw [← hnP]; exact fun x hx => by rw [hnP]; exact hparN x hx) s₄ s₅ _ c4.ok
      ⟨dShape_ext x14 _ _ hsh1, by rw [hctxEq]; exact hparams,
        dCtors_ext.list x4 _ _ hca, denoteFEnv_ext x14 hden₁⟩ h9
  dsimp only at h10 hrd hmsP hMsc hF5
  have x5 := c5.ext
  have x15 : Ext s₁.store s₅.store := x14.trans x5
  -- the positivity function, on the stored constructors (the root frame)
  obtain ⟨⟨kinds, nfs, pos⟩, s₆, h11, h12⟩ := bindOk h10
  obtain ⟨c6, ⟨kindsP, nfsP, posP⟩, ⟨hkinds, hnfs, hpos⟩, hF6⟩ :=
    checkBlockPositivity_spec fe₁ hk henv₁ ⟨p₁⟩ ⟨p₁P⟩ cvTas cvTasP ctorsAs ctorsAsP hT
      (checkBlockCtors_types hF3) s₅ s₆ _ c5.ok
      ⟨by simp only [dParts, dShape_ext x15 _ _ hsh1, Option.map_some],
        dExt_denoteCV.list x15 _ _ hcvs, dCtors_ext.list (x4.trans x5) _ _ hca,
        denoteFEnv_ext x15 hden₁⟩ h11
  dsimp only at h12 hkinds hnfs hpos hF6
  subst hkinds
  have x6 := c6.ext
  -- the seeds: every outside class
  obtain ⟨seeds, s₇, h13, h14⟩ := bindOk h12
  obtain ⟨p7, hseeds⟩ := hCS ctx ctxP holes holesP ms msP env₁.find? s₆ s₇ seeds c6.ok.state c6.ok.pins
    ⟨dCtx_ext _ (x5.trans x6) _ _ hctx, denoteEList_ext (x5.trans x6) _ _ hholes,
      dMajor_ext.list x6 _ _ hmsP⟩ h13
  have c7 := p7.toCore c6.ok
  -- every outside class, walked from the root frame's state
  obtain ⟨ns, s₈, h15, h16⟩ := bindOk h14
  obtain ⟨c8, nsP, hns, hF8⟩ := nestSeeds_spec (μ := μ) (env := env₁) (fe := fe₁) hk henv₁
    hctxOk seeds (ConLeche.classSeeds ctxP holesP msP) pos posP
    (fun k hk x hx => by
      obtain ⟨M, hM, hMn, rfl⟩ := ConLeche.Cached.mem_classSeeds hk
      exact (ConLeche.nestSeedOf_ds hnh hlen (fun y hy => ConLeche.Expr.fvarB_le (by
        rw [hnP]; exact (hMsc M hM).2.1 hMn y hy)) x hx).2 (fun y hy => (hhw y hy).1) hpar)
    s₇ s₈ ns c7.ok
    ⟨dCtx_ext _ (x5.trans (x6.trans c7.ext)) _ _ hctx, hseeds, dState_ext c7.ext _ _ hpos⟩
    h15
  obtain ⟨rfl, rfl⟩ := pureOk h16
  have x8 := c8.ext
  have x7 := c7.ext
  have x58 : Ext s₅.store s'.store := x6.trans (x7.trans x8)
  have x18 : Ext s₁.store s'.store := x15.trans x58
  -- the pure side
  have hFP : FOk (ConLeche.checkBlockPass (fueledOpsM μ) env p₀P isRec)
      ⟨env₁, cvTasP, ⟨p₁P⟩, ctorsAsP, sortsssP, kinds.map (·.map (·.map kindOf)), nfsP,
        ctxP.params, rdP, msP, nsP.ctorNfs⟩ := by
    unfold ConLeche.checkBlockPass
    exact FOk.bind hF1 (FOk.bind hF3 (FOk.bind hF4 (FOk.bind hF5 (FOk.bind hF6
      (FOk.bind hF8 (FOk.pure _))))))
  have hwf₂ : EnvWF (ConLeche.consBlockCtors p₁P.nP ctorsAsP env₁) := by
    obtain ⟨F, hF⟩ := hFP
    rw [checkBlockPass_datF] at hF
    exact (checkBlockPass_envWF henv hF).2
  refine ⟨env₁, _, (c1.toInst.trans i2).trans (c3.toInst.trans (c4.toInst.trans
      (c5.toInst.trans (c6.toInst.trans (c7.toInst.trans c8.toInst))))), c8.ok,
    hrel1.ext x18, henv₁, ?_, hT, hwf₂, hMsc, hFP⟩
  exact dPass_mk (dExt_denoteCV.list x18 _ _ hcvs)
    (by simp only [dParts, dShape_ext x18 _ _ hsh1, Option.map_some])
    (dCtors_ext.list (x4.trans (x5.trans x58)) _ _ hca)
    (DExt.list (d := denoteLLists) (fun hx x y h => BI.denoteLLists_ext hx x y h)
      (x4.trans (x5.trans x58)) _ _ hss)
    (dExt_denoteEList.list (x7.trans x8) _ _ hnfs)
    (denoteEList_ext (x5.trans x58) _ _ (by rw [hctxEq]; exact hparams))
    (dClassRead_ext x58 _ _ hrd) (dMajor_ext.list x58 _ _ hmsP) (dState_ctorNfs hns)


/-! ## The uniform route's entry -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:140-148 checkBlock
con-leche: ConLeche/Verify/Cached/GenRecC.lean:1047 checkBlockKS_run —
**Theorem 1 at the uniform route**, over the three `GenRec.lean` stages
(named above): the distinct names (`nameNodup_spec`, `name_nodup_iff`), the
flush, the pass at official's `is_rec` (`blockRawRec_spec`), the install after
it.  `IndOut`'s `envWF` clause is `checkBlock_envWF` at the pure run, its
`proj` the chained `ProjOut`s. -/
theorem checkBlock_bridge_of {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (hCL : ClassesStageSpec μ) (hCS : SeedsStageSpec)
    (hGR : RecStageSpec μ)
    {env : Env} {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {p₀ : Arena.BlockParts} {p₀P : ConLeche.BlockParts}
    (hok : CheckOK μ env fe s) (henv : EnvWF env) (hcoh : IFEnvCoh fe)
    (hden : denoteFEnv s.store fe = some env) (hb : Frontend.denoteCIList s.store block = some b)
    (hp : dParts s.store p₀ = some p₀P)
    (hrun : Arena.checkBlock μ fe block p₀ s = .ok (fe', s')) :
    IndOut fe fe' s s' (fun env' => FOk (ConLeche.checkBlock (fueledOpsM μ) env b p₀P) env') := by
  obtain ⟨shP, hsh, rfl⟩ : ∃ shP, dShape s.store p₀.shape = some shP ∧ p₀P = ⟨shP⟩ := by
    simp only [dParts, Option.map_eq_some_iff] at hp
    obtain ⟨shP, h1, h2⟩ := hp
    exact ⟨shP, h1, h2.symm⟩
  simp only [Arena.checkBlock] at hrun
  -- the distinct names
  have hnC := nameNodup_spec hok.state.wf _ _ (BI.dCtors_names (BlockShape.allCtors_spec hsh))
  have hnM := nameNodup_spec hok.state.wf _ _ (BlockShape.memberNames_spec hsh)
  by_cases hc : (!nameNodup (p₀.shape.allCtors.map (·.1.name)) ||
      !nameNodup p₀.shape.memberNames) = true
  · rw [if_pos hc] at hrun; exact absurd hrun (fun h => failOk h)
  rw [if_neg hc] at hrun
  have hnd : (shP.allCtors.map (·.1.name)).Nodup ∧ shP.memberNames.Nodup := by
    rw [hnC, hnM] at hc
    refine ⟨(name_nodup_iff _).1 ?_, (name_nodup_iff _).1 ?_⟩ <;> revert hc <;>
      cases ConLeche.Name.nodup (shP.allCtors.map (·.1.name)) <;>
      cases ConLeche.Name.nodup shP.memberNames <;> simp
  -- the flush
  obtain ⟨u, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨c1, i1, hs1⟩ := ReadOK.flush (μ := μ) hok.toR h1
  have x1 : Ext s.store s₁.store := by rw [hs1]; exact Ext.refl _
  -- official's `is_rec`
  obtain ⟨raw, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨p2, hraw⟩ := blockRawRec_spec p₀ ⟨shP⟩ s₁ s₂ raw c1.state
    (by simp only [dParts, dShape_ext x1 _ _ hsh, Option.map_some]) h3
  simp only [RV] at hraw
  subst hraw
  have c2 := p2.toCore c1
  have x12 := x1.trans p2.ext
  -- the pass
  obtain ⟨q, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨env₁, qP, i3, c3, hrel3, henv₁, hq, hT, henv₂, hMs, hFP⟩ :=
    checkBlockPass_of (p₀P := ⟨shP⟩) hμ hk hCL hCS henv c2.ok hcoh (denoteFEnv_ext x12 hden)
      (by simp only [dParts, dShape_ext x12 _ _ hsh, Option.map_some]) h5
  have x3 := i3.ext
  obtain ⟨e₁, hden₁, rfl⟩ := hrel3.denote
  -- the install after it
  obtain ⟨i4, hrel4⟩ := checkBlockTail_of hk hGR henv₁ c3 hrel3.coh hden₁ hq
    (denoteCIList_ext (x12.trans x3) _ _ hb) hT henv₂ hMs h6
  have hrel := InstRel.trans i4.ext hrel3 hrel4
  have hFB : ∀ e, FOk (ConLeche.checkBlockTail (fueledOpsM μ) b qP) e →
      FOk (ConLeche.checkBlock (fueledOpsM μ) env b ⟨shP⟩) e := by
    intro e he
    unfold ConLeche.checkBlock
    dsimp only
    rw [if_pos hnd]
    exact FOk.bind hFP he
  have hi := (i1.trans (p2.toInst.trans (i3.trans i4)))
  obtain ⟨env', hden', hF'⟩ := hrel.denote
  exact
    { state := hi.state
      ext := hi.ext
      pins := hi.pins
      coh := hrel.coh
      pushed := hrel.pushed
      visible := hrel.visible
      denote := ⟨env', hden', hFB env' hF'⟩
      proj := hrel.proj
      envWF := fun env'' h'' => by
        rw [hden'] at h''
        obtain rfl := Option.some.inj h''
        obtain ⟨F, hF⟩ := hFB env' hF'
        rw [checkBlock_datF] at hF
        exact checkBlock_envWF henv hF }


/-! ## The three stages, discharged -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:518-536 checkBlockClasses —
`GenRec.lean`'s `checkBlockClasses_spec`, at the shape the pass consumes. -/
theorem classesStage {μ : CheckMode} (hk : CoreSpec μ Arena.checkFuel) :
    ClassesStageSpec μ := by
  intro fe₁ env₁ p pP params paramsP ctorsAs ctorsAsP henv₁ hpl hp s₀ s' r hok hpre hrun
  obtain ⟨h1, h2, h3, -⟩ := hpre
  exact checkBlockClasses_spec fe₁ hk henv₁ p pP params paramsP ctorsAs ctorsAsP hpl hp
    s₀ s' r hok ⟨h1, h2, h3⟩ hrun

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:494-499 classSeeds —
`GenRec.lean`'s `classSeeds_spec`. -/
theorem seedsStage : SeedsStageSpec :=
  fun ctx ctxP holes holesP ms msP fnd => classSeeds_spec fnd ctx ctxP holes holesP ms msP

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:76-91 checkBlockRec —
`GenRec.lean`'s `genRecCheck_spec`, at the shape the tail consumes: the
returned index is coherent with the list it was handed (`GR.FEq`). -/
theorem recStage {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) : RecStageSpec μ := by
  intro fe₂ env₂ p pP nested params paramsP tbl tblP rd rdP ms msP cvTas cvTasP block blockP
    henv₂ hcoh hT hMs s₀ s' r hok hpre hrun
  obtain ⟨-, hp, hpa, htb, hrd, hms, hcv, hb⟩ := hpre
  obtain ⟨shP, hsh, rfl⟩ : ∃ shP, dShape s₀.store p.shape = some shP ∧ pP = ⟨shP⟩ := by
    simp only [dParts, Option.map_eq_some_iff] at hp
    obtain ⟨shP, h1, h2⟩ := hp
    exact ⟨shP, h1, h2.symm⟩
  obtain ⟨c, out, ⟨hout, hfresh, hfeq⟩, hF⟩ := genRecCheck_spec fe₂ hμ hk henv₂ hcoh p.shape shP
    nested params paramsP tbl tblP rd rdP ms msP cvTas cvTasP block blockP hMs hT s₀ s' r hok
    ⟨hsh, hpa, htb, hrd, hms, hcv, hb⟩ hrun
  refine ⟨c, out, ⟨⟨by rw [hfeq.2.1, hcoh.1, hfeq.1], fun n => by
    rw [hfeq.2.2 n, hcoh.2 n, hfeq.1]⟩, hfeq.1, hout, hfresh⟩, hF⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:140-148 checkBlock
con-leche: ConLeche/Verify/Cached/GenRecC.lean:1047 checkBlockKS_run —
**THEOREM 1 AT THE UNIFORM ROUTE**: an accepting run of `Arena.checkBlock`
from a checking state at a well-formed environment's coherent index refines
con-leche's `checkBlock` at the fueled operations, with the install's nine
clauses (`IndOut`). -/
theorem checkBlock_bridge {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel)
    {env : Env} {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {p₀ : Arena.BlockParts} {p₀P : ConLeche.BlockParts}
    (hok : CheckOK μ env fe s) (henv : EnvWF env) (hcoh : IFEnvCoh fe)
    (hden : denoteFEnv s.store fe = some env) (hb : Frontend.denoteCIList s.store block = some b)
    (hp : dParts s.store p₀ = some p₀P)
    (hrun : Arena.checkBlock μ fe block p₀ s = .ok (fe', s')) :
    IndOut fe fe' s s' (fun env' => FOk (ConLeche.checkBlock (fueledOpsM μ) env b p₀P) env') :=
  checkBlock_bridge_of hμ hk (classesStage hk) seedsStage (recStage hμ hk) hok henv hcoh
    hden hb hp hrun

end ConRon.Bridge.Inductives
