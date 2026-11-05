/-
# `ConRon.Refine2.Inductives.BlockTail` — Theorem 2 for `arena::inductives::block_tail`

**Task #105** (DESIGN.md §8.2).  `crates/con-ron-core/src/arena/inductives/block_tail.rs`
against `proof/ConRon/Arena/Inductives/BlockTail.lean`: the uniform route's
entry `check_block` — the distinct names, the pass (`check_block_pass`, with
`check_block_pass_classes` its inline tail), and the install after it
(`check_block_tail`: index sorts, constructors consed, the generated recursor
stage, the stored recursors against the generated ones and consed at their majors
(`check_block_tail_stored`, `StoredRecs.lean`), the projection tables).

`BlockPass` carries the pass's environment, so it RELATES
(`BlockPassRel`: `IFEnvRelI` on `env1`, the abstraction on every other
field) rather than abstracts.

`check_block_ls` is the tier's export to the checker (`Refine2/Checker/Top.lean`'s
`check_ind_decl_refines`), stated in `Inductives/Top.lean`'s shape.
-/
import ConRon.Refine2.Inductives.BlockInstall
import ConRon.Refine2.Inductives.GenRecCheck
import ConRon.Refine2.Inductives.StoredRecs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

open Lockstep

/-- The pass's record: the environment related, every other field abstracted. -/
structure BlockPassRel (r : arena.inductives.block_tail.BlockPass) (q : BlockPass) : Prop where
  env1 : IFEnvRelI r.env1 q.env1
  cvTas : q.cvTas = absICVL r.cv_tas
  p : q.p = absBlockParts r.p
  ctorsAs : q.ctorsAs = absCtorsLL r.ctors_as
  sortsss : q.sortsss = absLIdxLLL r.sortsss
  kinds : q.kinds = absKindsLLL r.kinds
  nfs : q.nfs = absEIdxLL r.nfs
  params : q.params = absEIdxL r.params
  rd : q.rd = absClassRead r.rd
  cls : q.cls = absTargetMajorL r.cls
  tbl : q.tbl = r.tbl.val.map absNestCtorNf

/-- `check_block_inds` with the pair of abstractions as ONE equation, so the
twin's `let (fe₁, cvTas, p₁) ← …` destructures a known term. -/
@[lockstep high] theorem check_block_inds_pair_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (p : arena.inductives.block_parts.BlockParts) (is_rec : Bool) :
    LS pers (fun a b => IFEnvRelI a.1 b.1 ∧ b.2 = (absICVL a.2.1, absBlockShape a.2.2))
      (arena.inductives.block_install.check_block_inds pers st mode rf p is_rec) lst
      (checkBlockInds (ConRon.Refine.absMode mode) lf (absBlockParts p) is_rec) :=
  Lockstep.PPR.LS.weaken (check_block_inds_ls hrel hinv mode hfe p is_rec)
    (fun _ _ h => ⟨h.1, Prod.ext h.2.1 h.2.2⟩)

attribute [local lockstep_inline] arena.inductives.block_tail.check_block_pass_classes

/-- `check_block_pass` ⊑ `checkBlockPass` (`check_block_pass_classes` inline). -/
@[lockstep] theorem check_block_pass_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p0 : arena.inductives.block_parts.BlockParts} {is_rec : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers BlockPassRel
      (arena.inductives.block_tail.check_block_pass pers st mode rf p0 is_rec) lst
      (checkBlockPass (ConRon.Refine.absMode mode) lf (absBlockParts p0) is_rec) := by
  rw [arena.inductives.block_tail.check_block_pass, checkBlockPass]
  lockstep
  exact LS.pure ⟨by assumption, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by simp [absNestState]⟩ ‹_› ‹_›

/-- `check_block_rec` ⊑ `checkBlockRec`: the generated recursor stage. -/
@[lockstep] theorem check_block_rec_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p : arena.inductives.block_parts.BlockParts} {nested : Bool}
    {params : alloc.vec.Vec arena.handle.EIdx}
    {tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf}
    {rd : arena.inductives.class_read.ClassRead}
    {ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {cv_tas : alloc.vec.Vec arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => IFEnvRelI a.1 b.1 ∧ b.2 = absRuleOutL a.2)
      (arena.inductives.block_tail.check_block_rec pers st mode rf p nested params tbl rd ms
        block cv_tas) lst
      (checkBlockRec (ConRon.Refine.absMode mode) lf (absBlockParts p) nested (absEIdxL params)
        (tbl.val.map absNestCtorNf) (absClassRead rd) (absTargetMajorL ms)
        (block.val.map absIConstantInfo) (absICVL cv_tas)) := by
  rw [arena.inductives.block_tail.check_block_rec, checkBlockRec]
  exact gen_rec_check_ls hrel hinv hfe _ _ _ _ _ _ _ _

/-- `checkBlockTables` at a structure-like member (one constructor, one
sort list). -/
theorem checkBlockTables_one (p : BlockShape) (m : MemberShape) (ms : List MemberShape)
    (cA : IConstantVal) (nF : Nat) (css : List (List (IConstantVal × Nat)))
    (sorts : List LIdx) (sss : List (List (List LIdx))) (fe : IFEnv) :
    checkBlockTables p (m :: ms) ([(cA, nF)] :: css) ([sorts] :: sss) fe =
      (if m.nIdx == 0 then do
        let guards ← structProjGuards cA.type p.nP nF sorts
        let fe₂ ← checkStructProjTable m.cvT.name cA.name p.lps p.nP nF p.resSort
          guards cA fe
        checkBlockTables p ms css sss fe₂
      else checkBlockTables p ms css sss fe) := by
  rw [checkBlockTables]

/-- `checkBlockTables` at any other member: skipped. -/
theorem checkBlockTables_other (p : BlockShape) (m : MemberShape) (ms : List MemberShape)
    (cs : List (IConstantVal × Nat)) (css : List (List (IConstantVal × Nat)))
    (ss : List (List LIdx)) (sss : List (List (List LIdx))) (fe : IFEnv)
    (h : ¬ (cs.length = 1 ∧ ss.length = 1)) :
    checkBlockTables p (m :: ms) (cs :: css) (ss :: sss) fe = checkBlockTables p ms css sss fe := by
  match cs, ss, h with
  | [], _, _ => (rw [checkBlockTables]; simp)
  | _ :: _ :: _, _, _ => (rw [checkBlockTables]; simp)
  | [_], [], _ => (rw [checkBlockTables]; simp)
  | [_], _ :: _ :: _, _ => (rw [checkBlockTables]; simp)
  | [_], [_], h => exact absurd ⟨rfl, rfl⟩ h

/-- `check_block_tables` ⊑ `checkBlockTables`, from the cursor on: the three
lists walked side by side. -/
@[lockstep] theorem check_block_tables_ls {pers st lst} {rf lf}
    {p : arena.inductives.block_parts.BlockShape}
    {ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))}
    {sortsss : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx))}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block_tables pers st p ctors_as sortsss i rf) lst
      (checkBlockTables (absBlockShape p) ((p.members.val.drop i.val).map absMemberShape)
        ((ctors_as.val.drop i.val).map absCtorsL) ((sortsss.val.drop i.val).map absLIdxLL)
        lf) := by
  suffices H : ∀ (n : Nat) (i : Std.Usize) st lst rf lf, p.members.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st → IFEnvRelI rf lf →
      LS pers IFEnvRelI
        (arena.inductives.block_tail.check_block_tables pers st p ctors_as sortsss i rf) lst
        (checkBlockTables (absBlockShape p) ((p.members.val.drop i.val).map absMemberShape)
          ((ctors_as.val.drop i.val).map absCtorsL) ((sortsss.val.drop i.val).map absLIdxLL)
          lf) from H _ i st lst rf lf rfl hrel hinv hfe
  intro n
  induction n with
  | zero =>
    intro i st lst rf lf hn hrel hinv hfe
    rw [arena.inductives.block_tail.check_block_tables.eq_def,
      ite_eq_left (by simp only [alloc.vec.Vec.len]; scalar_tac),
      List.drop_eq_nil_of_le (by omega : p.members.val.length ≤ i.val)]
    simp only [List.map_nil, checkBlockTables]
    lockstep
  | succ n ih =>
    intro i st lst rf lf hn hrel hinv hfe
    have hm : i.val < p.members.val.length := by omega
    rw [arena.inductives.block_tail.check_block_tables.eq_def,
      ite_eq_right (by simp only [alloc.vec.Vec.len]; scalar_tac),
      List.drop_eq_getElem_cons hm]
    by_cases hc : i.val < ctors_as.val.length
    · rw [ite_eq_right (by simp only [alloc.vec.Vec.len]; scalar_tac), List.drop_eq_getElem_cons hc]
      by_cases hs : i.val < sortsss.val.length
      · rw [ite_eq_right (by simp only [alloc.vec.Vec.len]; scalar_tac), List.drop_eq_getElem_cons hs]
        simp only [List.map_cons]
        by_cases h1 : (ctors_as.val[i.val]).val.length = 1 ∧ (sortsss.val[i.val]).val.length = 1
        · obtain ⟨h1c, h1s⟩ := h1
          obtain ⟨⟨cA, nF⟩, hcA⟩ := List.length_eq_one_iff.mp h1c
          obtain ⟨sorts, hso⟩ := List.length_eq_one_iff.mp h1s
          simp only [absCtorsL, absLIdxLL, hcA, hso, List.map_cons, List.map_nil,
            checkBlockTables_one]
          lockstep
          all_goals
            simp only [hcA, hso, List.getElem_cons_zero, Lockstep.usize_zero_val'] at *
            simp only [absMemberShape, absIConstantVal] at *
            lockstep
        · rw [checkBlockTables_other _ _ _ _ _ _ _ _
            (by simpa [absCtorsL, absLIdxLL] using h1)]
          lockstep
      · rw [ite_eq_left (by simp only [alloc.vec.Vec.len]; scalar_tac),
          List.drop_eq_nil_of_le (by omega : sortsss.val.length ≤ i.val)]
        simp only [List.map_cons, List.map_nil, checkBlockTables]
        lockstep
    · rw [ite_eq_left (by simp only [alloc.vec.Vec.len]; scalar_tac),
        List.drop_eq_nil_of_le (by omega : ctors_as.val.length ≤ i.val)]
      simp only [List.map_cons, List.map_nil, checkBlockTables]
      lockstep

/-! ## The generated install, pushed and popped: `cons_block_recs_temp`,
`check_block_tail_stored` -/

/-- `ifenv_push_temp` at a recursor: related to the twin's push, the equation kept for
the pops. -/
theorem ifenv_push_temp_rec_ls {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (ci : arena.env.IConstantInfo) (hwf : IConstantInfoWF ci) :
    LSP (arena.env.ifenv_push_temp rf ci)
      (fun r => IFEnvRelI r.2 (lf.push (absIConstantInfo ci)) ∧
        arena.env.ifenv_push_temp rf ci = ok r) := by
  rintro ⟨prev, rf1⟩ h
  obtain ⟨hpush, -⟩ := gr_ifenv_push_temp_spec hfe.inv h
  obtain ⟨hrel1, hinv1⟩ := ifenv_push_refines hfe.rel hfe.inv hwf hpush
  exact ⟨⟨hrel1, hinv1⟩, h⟩

/-- What the pushes hand on: the index related, the displaced rows counted, the port's pops
undoing them, and the twin's pops restoring what the pushes started from. -/
structure TempRel (rf : arena.env.IFEnv) (lf : IFEnv)
    (prevs : alloc.vec.Vec (arena.handle.NIdx × Option (Std.U64 × Std.U64)))
    (prevsL : List (NIdx × Option (Nat × IConstantInfo))) (q : Nat)
    (a : arena.env.IFEnv × alloc.vec.Vec (arena.handle.NIdx × Option (Std.U64 × Std.U64)))
    (b : IFEnv × List (NIdx × Option (Nat × IConstantInfo))) : Prop where
  rel : IFEnvRelI a.1 b.1
  count : ∃ Q, a.2.val = prevs.val ++ Q ∧ Q.length = q
  pops : ∀ rfX, RFEq rfX a.1 → IdxInv rfX → ∀ (j : Std.Usize) out,
    j.val = prevs.val.length + q →
    arena.inductives.gen_rec.class_fe_r_pop rfX a.2 j = ok out →
    ∃ rfY, RFEq rfY rf ∧ IdxInv rfY ∧ ∀ (j' : Std.Usize), j'.val = prevs.val.length →
      arena.inductives.gen_rec.class_fe_r_pop rfY a.2 j' = ok out
  twin : ∃ news, b.2 = prevsL ++ news ∧
    TFEq (news.foldr (fun (x : NIdx × Option (Nat × IConstantInfo)) acc =>
      acc.popTemp x.1 x.2) b.1) lf

attribute [local lockstep] ifenv_push_temp_rec_ls
attribute [local lockstep high] Lockstep.PC2.i_constant_val_dup_ls

theorem cons_block_recs_temp_aux {pers} (vis2 : Std.U64)
    (p : arena.inductives.block_parts.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) (q : Nat) :
    ∀ (m : Std.U64) st lst (rf : arena.env.IFEnv) (lf : IFEnv)
      (prevs : alloc.vec.Vec (arena.handle.NIdx × Option (Std.U64 × Std.U64)))
      (prevsL : List (NIdx × Option (Nat × IConstantInfo))),
      out.val.length - m.val = q → IFEnvRelI rf lf →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (TempRel rf lf prevs prevsL q)
        (arena.inductives.block_tail.cons_block_recs_temp pers vis2 st p m out rf prevs) lst
        (consBlockRecsTemp (absU vis2) (absBlockShape p) (absU m)
          ((out.val.drop m.val).map absRecOut) lf prevsL) := by
  induction q with
  | zero =>
    intro m st lst rf lf prevs prevsL hn hfe hrel hinv
    rw [arena.inductives.block_tail.cons_block_recs_temp.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil, consBlockRecsTemp]
    lockstep
    refine LS.pure ⟨hfe, ⟨[], by simp, rfl⟩, ?_, ⟨[], by simp, TFEq.refl _⟩⟩ hrel hinv
    intro rfX hX hXi j o hj hpop
    refine ⟨rfX, hX, hXi, fun j' hj' => ?_⟩
    rw [gr_usize_ext (show j'.val = j.val by simp at hj; omega)]
    exact hpop
  | succ q ih =>
    intro m st lst rf lf prevs prevsL hn hfe hrel hinv
    rw [arena.inductives.block_tail.cons_block_recs_temp.eq_def,
      List.drop_eq_getElem_cons (show m.val < out.val.length by omega), List.map_cons,
      consBlockRecsTemp]
    lockstep
    rename_i _ _ i6 h6 _ mi _ rp _ _ _ _ _ _ _ rules prev rf1 hpush prevs1 hprevs1
    obtain ⟨hR1, hpq⟩ := hpush
    have e6 : i6.val = m.val := by
      rcases h6 with h | h
      · exact h
      · exfalso; scalar_tac
    have ha : a.val = m.val + 1 := by scalar_tac
    have hrec : absIConstantInfo (arena.env.IConstantInfo.RecInfo out.val[i6.val].1 mi rp rules) =
        .recInfo (absRecOut out.val[m.val]).1 (absU mi) (absU rp) (absIRecRuleL rules) := by
      simp only [absIConstantInfo, e6, absRecOut]
      rfl
    rw [hrec] at hR1
    have h := ih a st1 lst1 rf1 _ prevs1
      (prevsL ++ [((absRecOut out.val[m.val]).1.name, lf.idx[(absRecOut out.val[m.val]).1.name]?)])
      (by omega) hR1 hrel hinv
    refine LS.tail h (by simp only [ha, absU]) ?_
    rintro ⟨rfK, prevsK⟩ ⟨feK, psK⟩ ⟨hR, ⟨Q, hQ, hQl⟩, hpops, ⟨news, hnews, hT⟩⟩
    obtain ⟨-, n', hn', -⟩ := gr_ifenv_push_temp_spec hfe.inv hpq
    have hnn : n' = out.val[i6.val].1.name := by
      simp only [arena.env.i_constant_info_name] at hn'
      exact dupId_nidx _ _ hn'
    subst hnn
    simp only at hQ hpops hnews hT
    refine ⟨hR, ⟨(out.val[i6.val].1.name, prev) :: Q, by rw [hQ, hprevs1]; simp, by simp [hQl]⟩, ?_,
      ⟨((absRecOut out.val[m.val]).1.name, lf.idx[(absRecOut out.val[m.val]).1.name]?) :: news,
        by rw [hnews]; simp, ?_⟩⟩
    · rw [← hQl]
      exact gr_pop_step hfe.inv hpq hn' hprevs1 hQ
        (fun rfX hX hXi j o hj hpop => hpops rfX hX hXi j o (by rw [hj, hQl]) hpop)
    · simp only [List.foldr_cons]
      exact (hT.popTemp _ _).trans (TFEq.popTemp_push lf _)

@[lockstep] theorem cons_block_recs_temp_ls {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (vis2 : Std.U64) (p : arena.inductives.block_parts.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (fun a b => IFEnvRelI a.1 b.1 ∧
        ∀ (j : Std.Usize) o, j.val = a.2.val.length →
          arena.inductives.gen_rec.class_fe_r_pop a.1 a.2 j = ok o →
          IFEnvRelI o (b.2.foldr grPop b.1))
      (arena.inductives.block_tail.cons_block_recs_temp pers vis2 st p 0#u64 out rf
        (alloc.vec.Vec.new _)) lst
      (consBlockRecsTemp (absU vis2) (absBlockShape p) 0 (out.val.map absRecOut) lf []) := by
  have h := cons_block_recs_temp_aux vis2 p out _ 0#u64 st lst rf lf (alloc.vec.Vec.new _) [] rfl
    hfe hrel hinv
  refine LS.tail h (by simp [absU]) ?_
  rintro ⟨rfK, prevsK⟩ ⟨feK, prevsLK⟩ ⟨hR, ⟨Q, hQ, hQl⟩, hpops, ⟨news, hn, hT⟩⟩
  refine ⟨hR, fun j o hj hpop => ?_⟩
  obtain ⟨rfY, hY, hYi, hpopY⟩ := hpops rfK (RFEq.refl _) hR.inv.1 j o
    (by simp only at hj hQ; rw [hj, hQ]; simp [alloc.vec.Vec.new, hQl]) hpop
  have hout := hpopY 0#usize (by simp [alloc.vec.Vec.new])
  rw [arena.inductives.gen_rec.class_fe_r_pop.eq_def, ite_eq_left rfl, Result.ok.injEq] at hout
  subst hout
  refine IFEnvRelI.transfer hfe hY hYi ?_
  simp only at hn hT ⊢
  rw [hn, List.nil_append]
  exact hT

attribute [local lockstep_simp] grPop

/-- `check_block_tail_stored` ⊑ `checkBlockTailStored`: the generated install pushed, a flush,
the comparison, the pops, a flush, and the stored recursors consed. -/
@[lockstep] theorem check_block_tail_stored_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (vis2 : Std.U64) (p : arena.inductives.block_parts.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block_tail_stored pers vis2 st mode p out rf) lst
      (checkBlockTailStored (ConRon.Refine.absMode mode) (absU vis2) (absBlockShape p)
        (out.val.map absRecOut) lf) := by
  rw [arena.inductives.block_tail.check_block_tail_stored, checkBlockTailStored]
  lockstep
  refine LS.tail (cons_block_recs_t_ls hrel hinv (hR _ _ (by simp [alloc.vec.Vec.len]) hf) vis2 p
    0#u64 a) ?_ (fun _ _ h => h)
  have hP' : storedOut (absBlockShape p).recs (List.map absRecOut out.val) = a.val.map absRecOut :=
    hP
  rw [hP']
  simp only [show (0#u64 : Std.U64).val = 0 from rfl, List.drop_zero, absU]
  rfl

/-- `check_block_tail` ⊑ `checkBlockTail`, at a related pass. -/
@[lockstep] theorem check_block_tail_ls {pers st lst} {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {r : arena.inductives.block_tail.BlockPass} {q : BlockPass}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : BlockPassRel r q) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block_tail pers st mode block r) lst
      (checkBlockTail (ConRon.Refine.absMode mode) (absICIL block) q) := by
  obtain ⟨henv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hq
  cases q
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 henv
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rw [arena.inductives.block_tail.check_block_tail, checkBlockTail]
  lockstep
  simp only [absCtorsLL, absBlockParts_shape, Lockstep.usize_zero_val', List.drop_zero] at *
  obtain ⟨⟨_, _, hvb, _, _⟩, _⟩ := ‹IFEnvRelI _ (consBlockCtors _ _ _)›
  have hout : ∀ v, absRuleOutL v = v.val.map absRecOut := fun _ => rfl
  simp only [absBlockShape] at hvb ⊢
  rw [hvb, hout]
  lockstep

/-- **`block_tail::check_block` ⊑ `checkBlock`** — the uniform install. -/
@[lockstep] theorem check_block_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {p0 : arena.inductives.block_parts.BlockParts}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block pers st mode rf block p0) lst
      (checkBlock (ConRon.Refine.absMode mode) lf (absICIL block) (absBlockParts p0)) := by
  rw [arena.inductives.block_tail.check_block, checkBlock]
  lockstep
  all_goals
    simp only [TwinEq, absBlockParts_shape, absNIdxL] at *
    try simp only [← ‹(absBlockShape p0.shape).allCtors = _›] at *
    try simp only [← ‹(absBlockShape p0.shape).memberNames = _›] at *
    lockstep

end ConRon.Refine2
