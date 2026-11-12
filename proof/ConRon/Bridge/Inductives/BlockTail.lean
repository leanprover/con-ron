/-
# `ConRon.Bridge.Inductives.BlockTail` — Theorem 1 for the uniform route's top

`Arena/Inductives/BlockTail.lean` (`BlockPass`, `checkBlockPass`,
`checkBlockRec`, `consBlockRecsTemp`, `checkBlockTables`, `checkBlockTail`,
`reduceMember(s)`, `checkBlock`) against con-leche's
`ConLeche/Kernel/Inductives/BlockTail.lean`, assembled step by step as
upstream's cached bridge assembles its own driver
(`ConLeche/Verify/Cached/GenRecC.lean`'s `checkBlockKS_run` /
`checkBlockPassS_run` / `checkBlockTailS_run`).

Every environment the twin builds is related to con-leche's by its lookups
(`EnvRel`, `IFEnvOK`, `Bridge/Inductives/Rel.lean`), never by a denotation of
the whole index.  The twin's `flushCaches` at the environment transitions are
what re-establish `CheckOK` at the new index (`ReadOK.flush`): between two
flushes the state is only known to READ the index right (`ReadOK`), and the
stage lemmas that call the knot take `CheckOK` at the index they run at.

The environments' well-formedness, which the knot calls need, is con-leche's
own: `direct_block_inds_wf` (the formers), `direct_block_ctors_wf` (the
constructors), `genRecCheck_recsWF` (the generated family).

The block's install (`blockRecs`, `blockTables`, the final `pushDelta`) is the
job's own index, dropped with it: the route owes `IndOut` (the state's frame
and the pure run) and nothing about that index.
-/
module

import ConRon.Bridge.Inductives.BlockInstall
public import ConRon.Bridge.Inductives.RecCheck
public import ConRon.Bridge.Inductives.GenRec
import ConRon.Bridge.Inductives.StreamRecs
import ConRon.Bridge.Inductives.Install
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Denote.IndFrame
public import ConRon.Bridge.Inductives.ClassRead
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Inductives.StructInstall
import ConRon.Bridge.Inductives.StructParts
public import ConLeche.Verify.Cached.GenRecC
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Core.Walks.Guards
import ConRon.Bridge.EnvDenote

public section

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

/-! ## The generated family, pushed in place and popped -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:80-91 consBlockRecsT —
**the temporary pushes answer as con-leche's cons**: a denoting record list
pushed head first is the environment with the records consed in reverse
(`IFEnvOK.pushStored`, iterated). -/
theorem consBlockRecsTemp_ok {s : AState} (hst : StateOK s) :
    ∀ (L : List IConstantInfo) (LP : List ConstantInfo) (fe : IFEnv) (env : Env)
      (prevs : List (NIdx × Option IConstantInfo)),
      Frontend.denoteCIList s.store L = some LP → IFEnvOK env fe s → TblGate fe →
      TablesStored env →
      IFEnvOK ⟨LP.reverse ++ env.consts, env.tables⟩
        (Arena.consBlockRecsTemp L fe prevs).1 s
  | [], LP, fe, env, prevs, hL, hie, _, _ => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at hL
    subst hL
    exact hie
  | ci :: L, LP, fe, env, prevs, hL, hie, hg, hts => by
    simp only [Frontend.denoteCIList] at hL
    cases hc : Frontend.denoteCI s.store ci with
    | none => rw [hc] at hL; simp at hL
    | some c =>
    cases hr : Frontend.denoteCIList s.store L with
    | none => rw [hc, hr] at hL; simp at hL
    | some LP' =>
    rw [hc, hr] at hL
    obtain rfl := (Option.some.inj hL).symm
    simp only [Arena.consBlockRecsTemp]
    have h := consBlockRecsTemp_ok hst L LP' (fe.push ci) ⟨c :: env.consts, env.tables⟩
      (prevs ++ [(ci.name, fe.idx[ci.name]?)]) hr
      (hie.pushStored hst hg hts hc) (hg.push ci) hts.cons
    simpa [List.reverse_cons, List.append_assoc] using h

/-- con-leche: none — **the pops restore the index the pushes started from**:
the recorded rows, popped in reverse (`foldr`), give back an index answering
exactly as the input (`GR.popTemp_push`). -/
theorem consBlockRecsTemp_pop :
    ∀ (L : List IConstantInfo) (fe : IFEnv) (prevs : List (NIdx × Option IConstantInfo)),
      ∃ news, (Arena.consBlockRecsTemp L fe prevs).2 = prevs ++ news ∧
        GR.FEq (news.foldr (fun (x : NIdx × Option IConstantInfo) acc =>
          acc.popTemp x.1 x.2) (Arena.consBlockRecsTemp L fe prevs).1) fe
  | [], fe, prevs => ⟨[], by simp [Arena.consBlockRecsTemp], GR.FEq.refl _⟩
  | ci :: L, fe, prevs => by
    simp only [Arena.consBlockRecsTemp]
    obtain ⟨news, hn, hf⟩ := consBlockRecsTemp_pop L (fe.push ci)
      (prevs ++ [(ci.name, fe.idx[ci.name]?)])
    refine ⟨(ci.name, fe.idx[ci.name]?) :: news, by rw [hn]; simp, ?_⟩
    simp only [List.foldr_cons]
    exact (hf.popTemp _ _).trans (GR.popTemp_push fe ci)

/-- con-leche: none — `GR.FEq` carries `EnvRel` (lookups and gate). -/
theorem EnvRel.feq {env : Env} {a b : IFEnv} {st : EStore} (h : GR.FEq a b)
    (hb : EnvRel env b st) : EnvRel env a st :=
  ⟨fun s hs => h.ifenv (hb.ienv s hs), h.gate hb.gate, hb.stored⟩

/-! ## The pass's helpers -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:263-270 blockNestCtx —
**the walk's canonical parameters are scoped at the parameter count**
(`blockNestCtxS_sim₂`'s `hpar`, read off the pure run): they are the first
former's telescope opened at the parameters (`openPisAtFvars_WScoped`). -/
theorem blockNestCtx_params_scoped {pP : ConLeche.BlockShape}
    {find? : ConLeche.Name → Option ConstantInfo} {v : ConLeche.NestCtx × List Expr}
    (hT : ∀ cv ∈ pP.formers, Expr.WScoped 0 cv.type)
    (h : FOk (ConLeche.blockNestCtx (m := FueledM) pP find?) v) :
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

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:272-274 nestOutKinds —
the root frame's field kinds, denoted. -/
theorem nestOutKinds_denote {st : EStore} :
    ∀ {outs : List (List (List Arena.NestFieldKind × EIdx))}
      {outsP : List (List (List ConLeche.NestFieldKind × Expr))},
      dOutss st outs = some outsP →
      (Arena.nestOutKinds outs).map (·.map (·.map kindOf)) = ConLeche.nestOutKinds outsP
  | [], _, h => by
    simp only [dOutss, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | os :: oss, _, h => by
    simp only [dOutss] at h
    obtain ⟨osP, ossP, rfl, hos, hoss⟩ := mapM_option_cons_inv h
    have ih := nestOutKinds_denote (st := st) (outs := oss) hoss
    simp only [Arena.nestOutKinds, ConLeche.nestOutKinds, List.map_cons, List.map_map] at ih ⊢
    refine List.cons_eq_cons.mpr ⟨?_, ih⟩
    clear ih hoss h
    induction os generalizing osP with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hos
      subst hos; rfl
    | cons o os ih =>
      obtain ⟨oP, osP', rfl, ho, hos'⟩ := mapM_option_cons_inv hos
      simp only [dOut, Option.map_eq_some_iff] at ho
      obtain ⟨e, -, rfl⟩ := ho
      simp only [List.map_cons, Function.comp_apply, ih osP' hos']

/-- con-leche: none — a block with its members replaced, denoted. -/
theorem dShape_members {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    {ms : List Arena.MemberShape} {msP : List ConLeche.MemberShape}
    (hp : dShape st p = some pP) (hms : ms.mapM (dMember st) = some msP) :
    dShape st { p with members := ms } = some { pP with members := msP } := by
  obtain ⟨-, hrecs, hnP, hel, hrs, hl, hip⟩ := dShape_inv hp
  obtain ⟨m, r, n, e, s, l, i⟩ := pP
  simp only at hrecs hnP hel hrs hl hip
  simp only [dShape, hms, hrecs, hel, hrs, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, hnP, hl, hip]

end BT

open BT

/-! ## The pass's record, denoted -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:24-42 BlockPass —
**the twin's pass record denotes con-leche's**, at the environment `env₁` its
`env1` index answers for (carried beside it): every handle field through its
own denotation, the field kinds through `kindOf`, the positivity table (a
`List` in the twin, an `Array` upstream) entry by entry. -/
def dPass (st : EStore) (env₁ : Env) (q : Arena.BlockPass) :
    Option (ConLeche.BlockPass Env) := do
  let p ← dShape st q.p
  let params ← Frontend.denoteEList st q.params
  let rd ← dClassRead st q.rd
  let cls ← q.cls.mapM (dMajor st)
  let tbl ← q.tbl.mapM (dCtorNf st)
  pure ⟨env₁, p, q.kinds.map (·.map (·.map kindOf)), params, rd, cls, tbl.toArray⟩

/-- con-leche: none — `dPass`, taken apart. -/
theorem dPass_inv {st : EStore} {env₁ : Env} {q : Arena.BlockPass}
    {qP : ConLeche.BlockPass Env} (h : dPass st env₁ q = some qP) :
    qP.env₁ = env₁ ∧ dShape st q.p = some qP.p ∧
      qP.kinds = q.kinds.map (·.map (·.map kindOf)) ∧
      Frontend.denoteEList st q.params = some qP.params ∧
      dClassRead st q.rd = some qP.rd ∧ q.cls.mapM (dMajor st) = some qP.cls ∧
      q.tbl.mapM (dCtorNf st) = some qP.tbl.toList := by
  simp only [dPass, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, a5, h5, rfl⟩ := h
  exact ⟨rfl, h1, rfl, h2, h3, h4, by simpa using h5⟩

/-- con-leche: none — and built from its parts. -/
theorem dPass_mk {st : EStore} {env₁ : Env} {q : Arena.BlockPass}
    {p : ConLeche.BlockShape} {params : List Expr} {rd : ConLeche.ClassRead}
    {cls : List ConLeche.TargetMajor} {tbl : List ConLeche.NestCtorNf}
    (h1 : dShape st q.p = some p) (h2 : Frontend.denoteEList st q.params = some params)
    (h3 : dClassRead st q.rd = some rd) (h4 : q.cls.mapM (dMajor st) = some cls)
    (h5 : q.tbl.mapM (dCtorNf st) = some tbl) :
    dPass st env₁ q = some ⟨env₁, p, q.kinds.map (·.map (·.map kindOf)), params, rd, cls,
      tbl.toArray⟩ := by
  simp only [dPass, h1, h2, h3, h4, h5, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-! ## The projection tables -/

/-- con-leche: none — `dPass` survives an extension. -/
theorem dPass_ext {st st' : EStore} {env₁ : Env} {q : Arena.BlockPass}
    {qP : ConLeche.BlockPass Env} (hx : Ext st st') (h : dPass st env₁ q = some qP) :
    dPass st' env₁ q = some qP := by
  obtain ⟨he, hsh, hkd, hpa, hrd, hcl, htb⟩ := dPass_inv h
  rw [dPass_mk (dShape_ext hx _ _ hsh) (denoteEList_ext hx _ _ hpa) (dClassRead_ext hx _ _ hrd)
    (dMajor_ext.list hx _ _ hcl) (dCtorNf_ext.list hx _ _ htb)]
  obtain ⟨e, p, k, pa, rd, cl, tb⟩ := qP
  simp only at he hkd ⊢
  subst he hkd
  simp

/-- con-leche: none — a table list's denotation survives an extension. -/
theorem denoteProjTableList_ext {st st' : EStore} (hx : Ext st st') :
    ∀ {Q : List IProjTable} {QP : List ProjTable},
      Frontend.denoteProjTableList st Q = some QP →
      Frontend.denoteProjTableList st' Q = some QP
  | [], _, h => h
  | t :: ts, QP, h => by
    simp only [Frontend.denoteProjTableList] at h ⊢
    split at h
    · rename_i x xs hx1 hx2
      rw [denoteProjTable_ext hx1 hx, denoteProjTableList_ext hx hx2]
      exact h
    · exact nomatch h

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:94-98 checkBlockTables
con-leche: ConLeche/Cached/IndTail.lean:204-209 checkBlockTablesC —
**the checks of the block's projection tables**, table by table
(`checkStructProjTable_runF`), all at one index. -/
theorem checkBlockTables_spec (fe : IFEnv) (env : Env) :
    ∀ (Q : List IProjTable) (QP : List ProjTable) (s₀ s' : AState) (r : Unit),
      StateOK s₀ → PinsOK s₀ → IFEnvOKS env fe s₀.store →
      Frontend.denoteProjTableList s₀.store Q = some QP →
      Arena.checkBlockTables fe Q s₀ = .ok (r, s') →
      PStep s₀ s' ∧ FOk (ConLeche.checkBlockTables (m := FueledM) env QP) ()
  | [], QP, s₀, s', r, hok, _, _, hQ, hrun => by
    simp only [Frontend.denoteProjTableList, Option.some.injEq] at hQ
    subst hQ
    simp only [Arena.checkBlockTables] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, by simp only [ConLeche.checkBlockTables]; exact FOk.pure ()⟩
  | t :: ts, QP, s₀, s', r, hok, hpins, hie, hQ, hrun => by
    simp only [Frontend.denoteProjTableList] at hQ
    split at hQ
    · rename_i tP tsP ht hts
      obtain rfl := (Option.some.inj hQ).symm
      simp only [Arena.checkBlockTables] at hrun
      simp only [ConLeche.checkBlockTables]
      obtain ⟨u, s₁, k1, z1⟩ := AM.bind_ok hrun
      obtain ⟨p1, hF1⟩ := checkStructProjTable_runF fe env t tP s₀ s₁ u hok hpins
        ⟨ht, hie⟩ k1
      obtain ⟨p2, hF2⟩ := checkBlockTables_spec fe env ts tsP _ s' r p1.ok
        (hpins.mono p1.ext p1.pins) (hie.mono p1.ext) (denoteProjTableList_ext p1.ext hts) z1
      exact ⟨p1.trans p2, FOk.seq hF1 hF2⟩
    · exact nomatch hQ

/-! ## The checks after the pass -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:103-115 checkBlockTail
con-leche: ConLeche/Verify/Cached/GenRecC.lean:1339 checkBlockTailS_run —
**the checks after the pass**, from the formers' index `q.env1` (whose caches
are sound: the pass's last stages ran there): the index binders' sorts, the
constructors consed (`consBlockCtors_spec`), the flush entering them, the
generated recursors (`genRecCheck_spec`, the index handed back answering as the
constructors'), the K flags, the generated family pushed in place
(`consBlockRecsTemp_ok`, con-leche's `consBlockRecsT`), a flush, the stream's
recursors against it (`streamRecsCheck_spec`), the pops
(`consBlockRecsTemp_pop`), a flush, and the projection tables' checks. -/
theorem checkBlockTail_of (hk : CoreSpec Arena.checkFuel)
    {env₁ : Env} {q : Arena.BlockPass} {qP : ConLeche.BlockPass Env}
    {block : List IConstantInfo} {blockP : List ConstantInfo} {s s' : AState} {fe' : IFEnv}
    {Q : List IProjTable} {QP : List ProjTable}
    (henv₁ : EnvWF env₁) (hck : CheckOK false env₁ q.env1 s)
    (hrel : EnvRel env₁ q.env1 s.store) (hq : dPass s.store env₁ q = some qP)
    (hb : Frontend.denoteCIList s.store block = some blockP)
    (hT : ∀ cv ∈ qP.p.formers, Expr.WScoped 0 cv.type)
    (henv₂ : EnvWF (ConLeche.consBlockCtors qP.p.nP qP.p.ctorGroups env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)
    (hpl : qP.params.length = qP.p.nP)
    (hQ : Frontend.denoteProjTableList s.store Q = some QP)
    (hrun : Arena.checkBlockTail .verified block q Q s = .ok (fe', s')) :
    InstStep s s' ∧ FOk (ConLeche.checkBlockTail (fueledOpsM .verified) blockP qP QP) () := by
  obtain ⟨he, hsh, hkd, hpa, hrd, hcl, htb⟩ := dPass_inv hq
  obtain ⟨env₁', pP, kindsP, paramsP, rdP, clsP, tblP⟩ := qP
  simp only at he hsh hkd hpa hrd hcl htb hT henv₂ hMs hpl
  subst env₁' hkd
  obtain ⟨hms, hrecs, hnP, -, -, -, -⟩ := dShape_inv hsh
  have hzT : ∀ ms ∈ pP.members, Expr.WScoped 0 ms.cvT.type :=
    fun ms hms => hT ms.cvT (List.mem_map_of_mem hms)
  simp only [Arena.checkBlockTail] at hrun
  -- the index binders' sorts
  obtain ⟨u1, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, _, -, hisF⟩ := checkBlockIdxSorts_specF q.env1 hk henv₁ q.p pP
    q.p.members pP.members hzT s s₁ u1 hck ⟨hsh, hms⟩ h1
  have x1 := c1.ext
  -- the constructors consed
  have hcss : q.p.ctorGroups.mapM (dGroup s₁.store) = some pP.ctorGroups :=
    ctorGroups_denote (dShape_ext x1 _ _ hsh)
  obtain ⟨env₂, hrel₂, he₂⟩ := (consBlockCtors_spec c1.ok.state.wf q.p.nP q.p.ctorGroups
    pP.ctorGroups q.env1 env₁ hcss (hrel.mono x1)).denote
  rw [hnP] at hrel₂ h2 he₂
  rw [← he₂] at henv₂
  generalize hfe₂ : Arena.consBlockCtors pP.nP q.p.ctorGroups q.env1 = fe₂ at h2 hrel₂
  -- the flush entering them
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush
    (⟨c1.ok.state, c1.ok.pins, hrel₂.ifenv⟩ : ReadOK _ fe₂ s₁) h3
  have x2 : Ext s.store s₂.store := by rw [hs2]; exact x1
  -- the recursor stage
  obtain ⟨⟨fe₂b, out⟩, s₃, h5, h6⟩ := AM.bind_ok h4
  simp only [Arena.checkBlockRec] at h5
  obtain ⟨c3, outP, ⟨hout, hfresh, hfeq⟩, hGRF⟩ := genRecCheck_spec fe₂ hk henv₂ hrel₂.gate
    q.p pP _ q.params paramsP q.tbl tblP.toList q.rd rdP q.cls clsP block blockP hMs hT s₂ s₃
    (fe₂b, out) c2
    ⟨dShape_ext x2 _ _ hsh, denoteEList_ext x2 _ _ hpa, dCtorNf_ext.list x2 _ _ htb,
      dClassRead_ext x2 _ _ hrd, dMajor_ext.list x2 _ _ hcl, denoteCIList_mono x2 _ _ hb⟩ h5
  rw [blockNestedBit_eq (dShape_ext x2 _ _ hsh)] at hGRF
  have x3 := c3.ext
  have x03 : Ext s.store s₃.store := x2.trans x3
  dsimp only at h6
  -- the K flags
  obtain ⟨uK, sK, hK1, hK2⟩ := AM.bind_ok h6
  obtain ⟨hsK, hKF⟩ := streamKCheck_run q.p.recs pP.recs out outP s₃ sK uK
    (dShape_ext x03 _ _ hsh) (dRec_ext.list x03 _ _ hrecs) hout hK1
  subst sK
  -- the generated family's records
  obtain ⟨infos, s₄, h7, h8⟩ := AM.bind_ok hK2
  obtain ⟨p4, hinfos⟩ := blockRecInfosTF_run q.p pP out outP 0 s₃ s₄ infos c3.ok.state
    (dShape_ext x03 _ _ hsh) hout h7
  have x4 := p4.ext
  have x04 : Ext s.store s₄.store := x03.trans x4
  -- pushed in place
  have henvG : EnvWF (ConLeche.consBlockRecsT pP 0 outP env₂) := by
    obtain ⟨FR, hFR⟩ := hGRF
    rw [genRecCheck_datF] at hFR
    exact ConLeche.Cached.genRecCheck_recsWF (mode := .verified) henv₂ hFR hpl
      (fun M hM => (hMs M hM).2.1)
  have hrel₂b : EnvRel env₂ fe₂b s₄.store :=
    EnvRel.feq hfeq (hrel₂.mono (show Ext s₁.store s₄.store by rw [← hs2]; exact x3.trans x4))
  have hienvG : IFEnvOK (ConLeche.consBlockRecsT pP 0 outP env₂)
      (Arena.consBlockRecsTemp infos fe₂b []).1 s₄ := by
    rw [consBlockRecsT_eq]
    exact consBlockRecsTemp_ok p4.ok infos _ fe₂b env₂ [] hinfos hrel₂b.ifenv hrel₂b.gate
      hrel₂b.stored
  obtain ⟨news, hn, hpop⟩ := consBlockRecsTemp_pop infos fe₂b []
  rw [List.nil_append] at hn
  -- the flush entering it
  obtain ⟨u5, s₅, h9, h10⟩ := AM.bind_ok h8
  obtain ⟨c5, i5, hs5⟩ := ReadOK.flush
    (⟨p4.ok, c3.ok.pins.mono x4 p4.pins, hienvG⟩ : ReadOK _ _ s₄) h9
  have x05 : Ext s.store s₅.store := by rw [hs5]; exact x04
  -- the stream's recursors against it
  obtain ⟨u6, s₆, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨c6, _, -, hFS⟩ := streamRecsCheck_spec _ hk henvG q.p.recs pP.recs out outP s₅ s₆ u6 c5
    ⟨dRec_ext.list x05 _ _ hrecs, dRecOut_ext.list (by rw [hs5]; exact x4) _ _ hout⟩ h11
  have x06 : Ext s.store s₆.store := x05.trans c6.ext
  -- the pops, and the flush leaving them
  rw [hn] at h12
  generalize hfe₃ : news.foldr (fun (x : NIdx × Option IConstantInfo) acc =>
    acc.popTemp x.1 x.2) (Arena.consBlockRecsTemp infos fe₂b []).1 = fe₃ at hpop
  have hfe₃' : List.foldr (fun x acc => match x with
      | (n, prev) => IFEnv.popTemp acc n prev) (Arena.consBlockRecsTemp infos fe₂b []).1 news
      = fe₃ := hfe₃
  rw [hfe₃'] at h12
  have hrel₃ : EnvRel env₂ fe₃ s₆.store :=
    EnvRel.feq hpop (hrel₂b.mono (by rw [← hs5]; exact c6.ext))
  obtain ⟨u7, s₇, h13, h14⟩ := AM.bind_ok h12
  obtain ⟨c7, i7, hs7⟩ := ReadOK.flush
    (⟨c6.ok.state, c6.ok.pins, hrel₃.ifenv⟩ : ReadOK env₂ fe₃ s₆) h13
  have x07 : Ext s.store s₇.store := by rw [hs7]; exact x06
  -- the projection tables
  obtain ⟨u8, s₈, h15, h16⟩ := AM.bind_ok h14
  obtain ⟨p8, hFT⟩ := checkBlockTables_spec fe₃ env₂ Q QP s₇ s₈ u8
    c7.state c7.pins (hrel₃.ienv.mono (by rw [hs7]; exact Ext.refl _))
    (denoteProjTableList_ext x07 hQ) h15
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h16
  refine ⟨((c1.toInst.trans i2).trans (c3.toInst.trans (p4.toInst.trans (i5.trans
    (c6.toInst.trans (i7.trans p8.toInst)))))), ?_⟩
  unfold ConLeche.checkBlockTail
  subst he₂
  exact FOk.bind hisF (FOk.bind hGRF (FOk.seq hKF (FOk.seq hFS hFT)))

/-! ## The pass -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:44-62 checkBlockPass
con-leche: ConLeche/Verify/Cached/GenRecC.lean:1446 checkBlockPassS_run —
**one pass over the formers, the constructors and the classes**: the formers
(at the entry index, `CheckOK` there), the flush entering the index that
holds them all, then every other stage at that index.  The answer denotes the
pass con-leche's `checkBlockPass` produces, with the facts the tail needs:
the caches sound at the formers' index, both environments well formed, the
formers' types closed, the classes scoped. -/
theorem checkBlockPass_of (hk : CoreSpec Arena.checkFuel)
    {env : Env} {fe : IFEnv} {p₀ : Arena.BlockShape} {p₀P : ConLeche.BlockShape}
    {isRec : Bool} {s s' : AState} {q : Arena.BlockPass}
    (henv : EnvWF env) (hck : CheckOK false env fe s) (hrel : EnvRel env fe s.store)
    (hp : dShape s.store p₀ = some p₀P)
    (hdecl : ∀ ms ∈ p₀P.members, MemberDeclaredWF env ms)
    (hrun : Arena.checkBlockPass .verified fe p₀ isRec s = .ok (q, s')) :
    ∃ env₁ qP, InstStep s s' ∧ CheckOK false env₁ q.env1 s' ∧
      EnvRel env₁ q.env1 s'.store ∧ EnvWF env₁ ∧
      dPass s'.store env₁ q = some qP ∧ (∀ cv ∈ qP.p.formers, Expr.WScoped 0 cv.type) ∧
      EnvWF (ConLeche.consBlockCtors qP.p.nP qP.p.ctorGroups env₁) ∧
      (∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M) ∧
      qP.params.length = qP.p.nP ∧
      FOk (ConLeche.checkBlockPass (fueledOpsM .verified) env p₀P isRec) qP := by
  simp only [Arena.checkBlockPass] at hrun
  -- the formers
  obtain ⟨⟨fe₁, p₁⟩, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, ⟨env₁, p₁P⟩, ⟨hrel1, hsh1⟩, hF1⟩ :=
    checkBlockInds_spec fe hk henv p₀ p₀P isRec s s₁ _ hck ⟨hp, hrel⟩ h1
  dsimp only at h2 hrel1 hsh1 hF1
  obtain ⟨F1, hF1'⟩ := id hF1
  rw [checkBlockInds_datF] at hF1'
  obtain ⟨henv₁, hTf⟩ := direct_block_inds_wf henv hdecl hF1'
  have hfor : p₁P.formers = p₀P.formers := by
    show p₁P.members.map _ = p₀P.members.map _
    rw [checkBlockInds_members hF1']
  have hT : ∀ cv ∈ p₁P.formers, Expr.WScoped 0 cv.type := fun cv hcv =>
    Expr.WScoped.of_not_hasFvar (hTf cv (hfor ▸ hcv))
  have hzT : ∀ ms ∈ p₁P.members, Expr.WScoped 0 ms.cvT.type :=
    fun ms hms => hT ms.cvT (List.mem_map_of_mem hms)
  -- the flush entering the formers' index
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush
    (⟨c1.ok.state, c1.ok.pins, hrel1.ifenv⟩ : ReadOK env₁ fe₁ s₁) h3
  have x2 : Ext s₁.store s₂.store := by rw [hs2]; exact Ext.refl _
  obtain ⟨hms1, -⟩ := dShape_inv hsh1
  -- the constructors
  obtain ⟨u3, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨c3, _, -, hF3⟩ :=
    checkBlockCtors_specF fe₁ fe₁ hk henv₁ p₁ p₁P env₁ p₁.members p₁P.members hzT s₂ s₃ u3 c2
      ⟨dShape_ext x2 _ _ hsh1, dMember_ext.list x2 _ _ hms1, c2.ienv.toS⟩ h5
  have x3 := c3.ext
  -- the walk's context
  obtain ⟨⟨ctx, holes⟩, s₄, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨c4, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, hlen, hnh, hnP⟩, hF4⟩ :=
    blockNestCtx_spec fe₁ henv₁ p₁ p₁P hT s₃ s₄ _ c3.ok (dShape_ext (x2.trans x3) _ _ hsh1) h7
  dsimp only at h8 hctx hholes hctxOk hhw hpar hlen hnh hnP hF4
  have hparN := blockNestCtx_params_scoped hT hF4
  dsimp only at hparN
  have x4 := c4.ext
  have x14 : Ext s₁.store s₄.store := x2.trans (x3.trans x4)
  obtain ⟨namesP, lpsP, paramsP, sortP, _, hctxEq, -, -, hparams, -, -, _⟩ := dCtx_inv hctx
  -- the classes
  obtain ⟨⟨rd, ms⟩, s₅, h9, h10⟩ := AM.bind_ok h8
  obtain ⟨c5, ⟨rdP, msP⟩, ⟨hrd, hmsP, hMsc⟩, hF5⟩ :=
    checkBlockClasses_spec fe₁ hk henv₁ p₁ p₁P ctx.params ctxP.params (by rw [hlen, hnP])
      hparN s₄ s₅ _ c4.ok
      ⟨dShape_ext x14 _ _ hsh1, by rw [hctxEq]; exact hparams⟩ h9
  dsimp only at h10 hrd hmsP hMsc hF5
  have x5 := c5.ext
  have x15 : Ext s₁.store s₅.store := x14.trans x5
  -- the positivity function, on the stored constructors (the root frame)
  obtain ⟨⟨outs, pos⟩, s₆, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨c6, ⟨outsP, posP⟩, ⟨houts, hpos⟩, hF6⟩ :=
    checkBlockPositivity_spec fe₁ hk henv₁ p₁ p₁P hT (checkBlockCtors_types hF3) s₅ s₆ _ c5.ok
      (dShape_ext x15 _ _ hsh1) h11
  dsimp only at h12 houts hpos hF6
  have x6 := c6.ext
  -- the seeds: every outside class
  obtain ⟨seeds, s₇, h13, h14⟩ := AM.bind_ok h12
  obtain ⟨p7, hseeds⟩ := classSeeds_spec env₁.find? ctx ctxP holes holesP ms msP s₆ s₇ seeds
    c6.ok.state c6.ok.pins
    ⟨dCtx_ext _ (x5.trans x6) _ _ hctx, denoteEList_ext (x5.trans x6) _ _ hholes,
      dMajor_ext.list x6 _ _ hmsP⟩ h13
  have c7 := p7.toCore c6.ok
  -- every outside class, walked from the root frame's state
  obtain ⟨ns, s₈, h15, h16⟩ := AM.bind_ok h14
  obtain ⟨c8, nsP, hns, hF8⟩ := nestSeeds_spec (env := env₁) (fe := fe₁) hk henv₁
    hctxOk seeds (ConLeche.classSeeds ctxP holesP msP) pos posP
    (fun k hk x hx => by
      obtain ⟨M, hM, hMn, rfl⟩ := ConLeche.Cached.mem_classSeeds hk
      exact (ConLeche.nestSeedOf_ds hnh hlen (fun y hy => ConLeche.Expr.fvarB_le (by
        rw [hnP]; exact (((hMsc M hM).2.1 hMn).2 y hy).2)) x hx).2 (fun y hy => (hhw y hy).1) hpar)
    s₇ s₈ ns c7.ok
    ⟨dCtx_ext _ (x5.trans (x6.trans c7.ext)) _ _ hctx, hseeds, dState_ext c7.ext _ _ hpos⟩
    h15
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h16
  have x8 := c8.ext
  have x7 := c7.ext
  have x58 : Ext s₅.store s'.store := x6.trans (x7.trans x8)
  have x18 : Ext s₁.store s'.store := x15.trans x58
  -- the pure side
  have hFP : FOk (ConLeche.checkBlockPass (fueledOpsM .verified) env p₀P isRec)
      ⟨env₁, p₁P, ConLeche.nestOutKinds outsP, ctxP.params, rdP, msP, nsP.ctorNfs⟩ := by
    unfold ConLeche.checkBlockPass
    exact FOk.bind hF1 (FOk.seq hF3 (FOk.bind hF4 (FOk.bind hF5 (FOk.bind hF6
      (FOk.bind hF8 (FOk.pure _))))))
  obtain ⟨F3, hF3'⟩ := id hF3
  rw [checkBlockCtors_datF] at hF3'
  obtain ⟨_, hF3r⟩ := ConLeche.checkBlockCtors_inv hF3'
  refine ⟨env₁, _, (c1.toInst.trans i2).trans (c3.toInst.trans (c4.toInst.trans
      (c5.toInst.trans (c6.toInst.trans (c7.toInst.trans c8.toInst))))), c8.ok,
    hrel1.mono (x2.trans (x3.trans (x4.trans (x5.trans x58)))), henv₁, ?_, hT,
    direct_block_ctors_wf henv₁ hF3r, hMsc, by rw [hlen, hnP], hFP⟩
  have hkinds := nestOutKinds_denote houts
  rw [← hkinds]
  exact dPass_mk (dShape_ext x18 _ _ hsh1)
    (denoteEList_ext (x5.trans x58) _ _ (by rw [hctxEq]; exact hparams))
    (dClassRead_ext x58 _ _ hrd) (dMajor_ext.list x58 _ _ hmsP) (dState_ctorNfs hns)

/-! ## The members at their telescopes -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:117-125 declinedAtDefinition —
the families declined at a definition, read off the pins. -/
theorem declinedAtDefinition_run {s s' : AState} {r : List NIdx} (hp : PinsOK s)
    (hrun : Arena.declinedAtDefinition s = .ok (r, s')) :
    s' = s ∧ Frontend.denoteNList s.store.ns r = some ConLeche.declinedAtDefinition := by
  simp only [Arena.declinedAtDefinition, Arena.pinStringOfList, Arena.pinListNil,
    Arena.pinListCons, Arena.pinCharOfNat, Arena.pinBool] at hrun
  obtain ⟨a, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, ha⟩ := pinAt_run hp (by rfl) k1
  obtain ⟨b, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨rfl, hb⟩ := pinAt_run hp (by rfl) k2
  obtain ⟨c, s3, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨rfl, hc⟩ := pinAt_run hp (by rfl) k3
  obtain ⟨d, s4, k4, z4⟩ := AM.bind_ok z3
  obtain ⟨rfl, hd⟩ := pinAt_run hp (by rfl) k4
  obtain ⟨e, s5, k5, z5⟩ := AM.bind_ok z4
  obtain ⟨rfl, he⟩ := pinAt_run hp (by rfl) k5
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z5
  refine ⟨rfl, ?_⟩
  simp only [Frontend.denoteNList, ha, hb, hc, hd, he, ConLeche.declinedAtDefinition,
    ConLeche.boolName]

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:127-139 reduceMember
con-leche: ConLeche/Cached/CheckerC.lean:165-176 reduceMemberS —
**a member's former at its telescope**: at a definition-headed former, the
decline at a literal's name, the declared type checked
(`checkConstantVal_bridge`), reduced (`reducedFormer_specF`) and compared
(`defeq_crun`). -/
theorem reduceMember_spec {env : Env} (fe : IFEnv) (hk : CoreSpec Arena.checkFuel)
    (henv : EnvWF env) (nP : Nat) (m : Arena.MemberShape) (mP : ConLeche.MemberShape) :
    CSpecF env fe (fun st => dMember st m = some mP)
      (Arena.reduceMember .verified fe m nP) (fun st r v => dMember st r = some v)
      (ConLeche.reduceMember (fueledOpsM .verified) env mP nP) := by
  intro s₀ s' r hok hm hrun
  obtain ⟨hcvT, hnI, hcs, hdecl⟩ := dMember_inv hm
  simp only [Arena.reduceMember] at hrun
  obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, rfl⟩ := formerDefHeaded_run hok hcvT k1
  unfold ConLeche.reduceMember
  cases hdh : ConLeche.formerDefHeaded mP.cvT with
  | false =>
    rw [hdh] at z1
    simp only [Bool.false_eq_true, ↓reduceIte] at z1 ⊢
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    exact ⟨CoreStep.refl hok, mP, hm, FOk.pure _⟩
  | true =>
    rw [hdh] at z1
    simp only [↓reduceIte] at z1 ⊢
    obtain ⟨ds, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨rfl, hds⟩ := declinedAtDefinition_run hok.pins k2
    have hcont : ds.contains m.cvT.name =
        ConLeche.declinedAtDefinition.contains mP.cvT.name :=
      contains_handle_eq hok.state.wf (denoteCV_name hcvT) hds
    rw [hcont] at z2
    cases hdc : ConLeche.declinedAtDefinition.contains mP.cvT.name with
    | true =>
      rw [hdc] at z2
      simp only [↓reduceIte] at z2
      exact absurd z2 (fun hc => AM.fail_ok hc)
    | false =>
    rw [hdc] at z2
    simp only [Bool.false_eq_true, ↓reduceIte] at z2 ⊢
    obtain ⟨u3, s₃, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨c3, F3, hF3⟩ := checkConstantVal_bridge hk hok henv hcvT k3
    have hws : Expr.WScoped 0 mP.cvT.type :=
      Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF3).1
    obtain ⟨cvR, s₄, k4, z4⟩ := AM.bind_ok z3
    rw [hnI] at k4
    obtain ⟨c4, cvRP, hcvR, hF4⟩ := reducedFormer_specF hk henv m.cvT mP.cvT _ hws s₃ s₄ cvR
      c3.ok (denoteCV_ext hcvT c3.ext) k4
    have hwR : Expr.WScoped 0 cvRP.type := by
      exact Expr.WScoped.of_not_hasFvar (ConLeche.Cached.Runs.reducedFormer_hasFvar henv
        (ConLeche.checkConstantVal_typeWF hF3).1 hF4)
    obtain ⟨d5, s₅, k5, z5⟩ := AM.bind_ok z4
    obtain ⟨c5, hF5⟩ := defeq_crun (hk.knot env fe henv) c4.ok
      (denoteCV_type (denoteCV_ext hcvT (c3.ext.trans c4.ext))) (denoteCV_type hcvR) hws hwR k5
    obtain ⟨hd5, z6⟩ := AM.dunless_ok AM.Never.fail_any z5
    replace z6 := AM.pure_bind_ok z6
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z6
    have x := (c3.ext.trans c4.ext).trans c5.ext
    refine ⟨(c3.trans c4).trans c5, { mP with cvT := cvRP }, ?_, ?_⟩
    · simp only [dMember, denoteCV_ext hcvR c5.ext, hnI, dCtors_ext x _ _ hcs,
        denoteCV_ext hdecl x, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · refine FOk.seq ⟨F3, ?_⟩ (FOk.bind hF4 (FOk.bind hF5 ?_))
      · rw [checkConstantVal_datF]; exact hF3
      · rw [ite_eq_left hd5]
        exact FOk.seq (FOk.pure ()) (FOk.pure _)

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:141-148 reduceMembers
con-leche: ConLeche/Cached/CheckerC.lean:178-185 reduceMembersS —
the members, each at its telescope, a flush before each. -/
theorem reduceMembers_spec {env : Env} (fe : IFEnv) (hk : CoreSpec Arena.checkFuel)
    (henv : EnvWF env) (nP : Nat) :
    ∀ (ms : List Arena.MemberShape) (msP : List ConLeche.MemberShape),
    CSpecF env fe (fun st => ms.mapM (dMember st) = some msP)
      (Arena.reduceMembers .verified fe nP ms) (fun st r v => r.mapM (dMember st) = some v)
      (ConLeche.reduceMembers (fueledOpsM .verified) env nP msP)
  | [], msP, s₀, s', r, hok, hms, hrun => by
    obtain rfl := mapM_option_nil_inv hms
    simp only [Arena.reduceMembers] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, [], rfl, by simp only [ConLeche.reduceMembers]; exact FOk.pure _⟩
  | m :: ms, msP, s₀, s', r, hok, hms, hrun => by
    obtain ⟨mP, msP', rfl, hm, hms'⟩ := mapM_option_cons_inv hms
    simp only [Arena.reduceMembers] at hrun
    obtain ⟨u, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, i1, hs1⟩ := ReadOK.flush hok.toR k1
    have c1' : CoreStep env fe s₀ s₁ := ⟨c1, by rw [hs1]; exact Ext.refl _, i1.pins⟩
    obtain ⟨m', s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨c2, mP', hm', hF2⟩ := reduceMember_spec fe hk henv nP m mP s₁ s₂ m' c1
      (by rw [hs1]; exact hm) k2
    obtain ⟨rest, s₃, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨c3, restP, hrest, hF3⟩ := reduceMembers_spec fe hk henv nP ms msP' s₂ s₃ rest c2.ok
      (dMember_ext.list (by rw [← hs1] at *; exact c2.ext) _ _ hms') k3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
    refine ⟨(c1'.trans c2).trans c3, mP' :: restP, ?_, ?_⟩
    · simp only [List.mapM_cons, dMember_ext c3.ext _ _ hm', hrest, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
    · simp only [ConLeche.reduceMembers]
      exact FOk.bind hF2 (FOk.bind hF3 (FOk.pure _))

/-! ## The uniform route's entry -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:150-163 checkBlock
con-leche: ConLeche/Verify/Cached/GenRecC.lean:1618 checkBlockKS_run —
**THEOREM 1 AT THE UNIFORM ROUTE**: an accepting run of `Arena.checkBlock` from
a checking state at a well-formed environment's index refines con-leche's
`checkBlock` at the fueled operations: the distinct names (`nameNodup_spec`,
`name_nodup_iff`), the `Bool` constructors' names (the pins), the members at
their telescopes (`reduceMembers_spec`; the recogniser's members stand at
their declared formers, so each is a `MemberAt`, `reduceMembers_inv`), the
flush, the pass at official's `is_rec` (`blockIsRec_spec`), the checks after
it, and the block's install read off the block (`blockRecs_run`,
`blockTables_run`), which the route owes nothing about. -/
theorem checkBlock_bridge (hk : CoreSpec Arena.checkFuel)
    {env : Env} {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {p₀ : Arena.BlockShape} {p₀P : ConLeche.BlockShape}
    (hok : CheckOK false env fe s) (henv : EnvWF env) (hrel : EnvRel env fe s.store)
    (hb : Frontend.denoteCIList s.store block = some b) (hp : dShape s.store p₀ = some p₀P)
    (hd : ∀ ms ∈ p₀P.members, ms.declared = ms.cvT)
    (hrun : Arena.checkBlock .verified fe block p₀ s = .ok (fe', s')) :
    IndOut s s' (∃ env', FOk (ConLeche.checkBlock (fueledOpsM .verified) env b p₀P) env') := by
  simp only [Arena.checkBlock] at hrun
  -- the distinct names
  have hnC := nameNodup_spec hok.state.wf _ _ (dCtors_names (BlockShape.allCtors_spec hp))
  have hnM := nameNodup_spec hok.state.wf _ _ (BlockShape.memberNames_spec hp)
  by_cases hc : (!nameNodup (p₀.allCtors.map (·.1.name)) ||
      !nameNodup p₀.memberNames) = true
  · rw [ite_eq_left hc] at hrun; exact absurd hrun (fun h => AM.fail_ok h)
  rw [ite_eq_right hc] at hrun
  have hnd : (p₀P.allCtors.map (·.1.name)).Nodup ∧ p₀P.memberNames.Nodup := by
    rw [hnC, hnM] at hc
    refine ⟨(name_nodup_iff _).1 ?_, (name_nodup_iff _).1 ?_⟩ <;> revert hc <;>
      cases ConLeche.Name.nodup (p₀P.allCtors.map (·.1.name)) <;>
      cases ConLeche.Name.nodup p₀P.memberNames <;> simp
  -- the `Bool` constructors' names
  obtain ⟨bt, s₀₁, kb1, zb1⟩ := AM.bind_ok hrun
  obtain ⟨hs01, hbt⟩ := pinAt_run hok.pins (by rfl) kb1
  subst s₀₁
  obtain ⟨bf, s₀₂, kb2, zb2⟩ := AM.bind_ok zb1
  obtain ⟨hs02, hbf⟩ := pinAt_run hok.pins (by rfl) kb2
  subst s₀₂
  have hct := contains_handle_eq hok.state.wf hbt (BlockShape.memberNames_spec hp)
  have hcf := contains_handle_eq hok.state.wf hbf (BlockShape.memberNames_spec hp)
  by_cases hbc : (p₀.memberNames.contains bt || p₀.memberNames.contains bf) = true
  · rw [ite_eq_left hbc] at zb2; exact absurd zb2 (fun h => AM.fail_ok h)
  rw [ite_eq_right hbc] at zb2
  have hbool : ConLeche.boolTrueName ∉ p₀P.memberNames ∧
      ConLeche.boolFalseName ∉ p₀P.memberNames := by
    rw [hct, hcf] at hbc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hbc
    simp only [ConLeche.boolTrueName, ConLeche.boolFalseName, ConLeche.boolName]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hm := List.contains_iff_mem.mpr h
      rw [hbc.1] at hm; exact nomatch hm
    · have hm := List.contains_iff_mem.mpr h
      rw [hbc.2] at hm; exact nomatch hm
  -- the members at their telescopes
  obtain ⟨hms₀, -⟩ := dShape_inv hp
  obtain ⟨ms, s₁, h1, h2⟩ := AM.bind_ok zb2
  obtain ⟨c1, msP, hms, hF1⟩ := reduceMembers_spec fe hk henv p₀.nP p₀.members p₀P.members
    s s₁ ms hok hms₀ h1
  have hnP₀ := (dShape_inv hp).2.2.1
  rw [hnP₀] at hF1
  obtain ⟨F1, hF1'⟩ := id hF1
  rw [reduceMembers_datF] at hF1'
  obtain ⟨hAt, -⟩ := ConLeche.reduceMembers_inv hd hF1'
  -- the flush
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush c1.ok.toR h3
  have x12 : Ext s.store s₂.store := by rw [hs2]; exact c1.ext
  -- official's `is_rec`
  obtain ⟨isRec, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨p3, hisRec⟩ := blockIsRec_spec p₀ p₀P s₂ s₃ isRec c2.state (dShape_ext x12 _ _ hp) h5
  simp only [RV] at hisRec
  subst hisRec
  have c3 := p3.toCore c2
  have x13 := x12.trans p3.ext
  -- the pass
  obtain ⟨q, s₄, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨env₁, qP, i4, c4, hrel4, henv₁, hq, hT, henv₂, hMs, hpl, hFP⟩ :=
    checkBlockPass_of (p₀P := { p₀P with members := msP }) hk henv c3.ok
      (hrel.mono x13) (dShape_members (dShape_ext x13 _ _ hp)
        (dMember_ext.list (show Ext s₁.store s₃.store by rw [← hs2]; exact p3.ext) _ _ hms))
      (fun m hm => (hAt m hm).declaredWF) h7
  have x4 := i4.ext
  -- the projection tables, read off the block once
  obtain ⟨oQ, s₄₁, h81, h82⟩ := AM.bind_ok h8
  obtain ⟨p41, -, hQ⟩ := blockTables_run p₀.members p₀P.members i4.state
    (dShape_ext (x13.trans x4) _ _ hp) (dMember_ext.list (x13.trans x4) _ _ hms₀) h81
  obtain ⟨Q, s₄₂, h83, h84⟩ := AM.bind_ok h82
  obtain ⟨rfl, rfl⟩ := unwrapOr_ok h83
  obtain ⟨QP, hQP, hQd, -⟩ := hQ
  have c41 := p41.toCore c4
  have x41 := x4.trans p41.ext
  -- the checks after it
  obtain ⟨fe₂, s₅, h9, h10⟩ := AM.bind_ok h84
  obtain ⟨i5, hFT⟩ := checkBlockTail_of hk henv₁ c41.ok (hrel4.mono p41.ext)
    (dPass_ext p41.ext hq) (denoteCIList_mono (x13.trans x41) _ _ hb) hT henv₂ hMs hpl hQd h9
  have x5 := i5.ext
  -- the block's install, read off the block
  have x05 : Ext s.store s₅.store := (x13.trans x41).trans x5
  have hpins5 : s₅.pins = s.pins := by
    rw [i5.pins, p41.pins, i4.pins, p3.pins, i2.pins, c1.pins]
  obtain ⟨recs, s₆, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨p6, -, -⟩ := blockRecs_run p₀.recs p₀P.recs i5.state
    (hok.pins.mono x05 hpins5) (dShape_ext x05 _ _ hp)
    (dRec_ext.list x05 _ _ (dShape_inv hp).2.1) h11
  obtain ⟨-, rfl⟩ := AM.pure_ok h12
  have hi := ((c1.toInst.trans i2).trans (p3.toInst.trans (i4.trans p41.toInst))).trans
    (i5.trans p6.toInst)
  refine ⟨hi.state, hi.ext, hi.pins,
    ⟨env.pushDelta (ConLeche.blockConstants p₀P) QP, ?_⟩⟩
  unfold ConLeche.checkBlock
  rw [ite_eq_left hnd, ite_eq_left hbool, hQP]
  dsimp only
  exact FOk.bind hF1 (FOk.bind hFP (FOk.bind FOk.unwrapOr (FOk.seq hFT (FOk.pure _))))

end ConRon.Bridge.Inductives
