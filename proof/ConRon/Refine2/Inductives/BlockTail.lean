/-
# `ConRon.Refine2.Inductives.BlockTail` — Theorem 2 for `arena::inductives::block_tail`

**Task #105** (DESIGN.md §8.2, Theorem 2); restated by task #143.
`crates/con-ron-core/src/arena/inductives/block_tail.rs` against
`proof/ConRon/Arena/Inductives/BlockTail.lean`: the uniform route's entry
`check_block` — the distinct names, each member's former reduced to its telescope
(`reduce_member(s)`), the pass (`check_block_pass`, with
`check_block_pass_classes` its inline tail), the checks after it
(`check_block_tail`: index sorts, constructors consed, the generated recursor
stage, the stream's K flags and recursors against the generated ones at the
generated family pushed and popped, `check_block_tail_stream`, the tables'
checks), and the block's install pushed onto the constructors' environment
(`Checker/Install.lean`'s `block_recs`, `block_tables`).

`BlockPass` carries the pass's environment, so it RELATES (`BlockPassRel`:
`IFEnvRelI` on `env1`, the abstraction on every other field) rather than
abstracts.  `check_block_ls` is the tier's export to the checker
(`Refine2/Checker/Top.lean`), stated in `Inductives/Top.lean`'s shape.
-/
import ConRon.Refine2.Inductives.BlockInstall
import ConRon.Refine2.Inductives.GenRecCheck
import ConRon.Refine2.Inductives.StreamRecs
import ConRon.Refine2.Checker.Install

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

open Lockstep

/-- The field kinds of the root frame's outputs, as the twin's lists. -/
def absKindsLLL (v : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec
    arena.inductives.positivity.NestFieldKind))) : List (List (List NestFieldKind)) :=
  v.val.map fun ks => ks.val.map fun k => k.val.map absNestFieldKind

/-- The pass's record: the environment related, every other field abstracted. -/
structure BlockPassRel (pers : arena.store.PersTier) (r : arena.inductives.block_tail.BlockPass)
    (q : BlockPass) : Prop where
  env1 : IFEnvRelI pers r.env1 q.env1
  p : q.p = absBlockShape r.p
  kinds : q.kinds = absKindsLLL r.kinds
  params : q.params = absEIdxL r.params
  rd : q.rd = absClassRead r.rd
  cls : q.cls = absTargetMajorL r.cls
  tbl : q.tbl = r.tbl.val.map absNestCtorNf

attribute [local lockstep_inline] arena.inductives.block_tail.check_block_pass_classes

/-- `check_block_pass` ⊑ `checkBlockPass` (`check_block_pass_classes` inline). -/
@[lockstep] theorem check_block_pass_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p0 : arena.inductives.block_shape.BlockShape} {is_rec : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (BlockPassRel pers)
      (arena.inductives.block_tail.check_block_pass pers st mode rf p0 is_rec) lst
      (checkBlockPass (ConRon.Refine.absMode mode) lf (absBlockShape p0) is_rec) := by
  rw [arena.inductives.block_tail.check_block_pass, checkBlockPass]
  lockstep
  refine LS.pure ⟨‹_›, rfl, rfl, rfl, rfl, rfl, ?_⟩ ‹_› ‹_›
  simp [absNestState]

/-- `check_block_rec` ⊑ `checkBlockRec`: the generated recursor stage. -/
@[lockstep] theorem check_block_rec_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p : arena.inductives.block_shape.BlockShape} {nested : Bool}
    {params : alloc.vec.Vec arena.handle.EIdx}
    {tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf}
    {rd : arena.inductives.class_read.ClassRead}
    {ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => IFEnvRelI pers a.1 b.1 ∧ b.2 = absRuleOutL a.2)
      (arena.inductives.block_tail.check_block_rec pers st mode rf p nested params tbl rd ms
        block) lst
      (checkBlockRec (ConRon.Refine.absMode mode) lf (absBlockShape p) nested (absEIdxL params)
        (tbl.val.map absNestCtorNf) (absClassRead rd) (absTargetMajorL ms)
        (block.val.map absIConstantInfo)) := by
  rw [arena.inductives.block_tail.check_block_rec, checkBlockRec]
  exact gen_rec_check_ls hrel hinv hfe _ _ _ _ _ _ _

/-! ## The generated family pushed temporarily: `cons_block_recs_temp`

Each side is shown to pop back to a layer that answers like the one it started
from (`GenRecCheck.lean`'s `RFEq`/`TFEq`, as for `class_fe_r_push`). -/

/-- The name `i_constant_info_name` reads is the abstraction's. -/
theorem bt_name_abs {c : arena.env.IConstantInfo} {n : arena.handle.NIdx}
    (h : arena.env.i_constant_info_name c = ok n) : absNIdx n = (absIConstantInfo c).name := by
  cases c <;> simp only [arena.env.i_constant_info_name,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2, Result.ok.injEq] at h <;>
    subst h <;> rfl

/-- The twin's pops restore the layer the pushes started from. -/
theorem bt_consBlockRecsTemp_pop :
    ∀ (l : List IConstantInfo) (fe : IFEnv) (prevs : List (NIdx × Option IConstantInfo)),
      ∃ news, (consBlockRecsTemp l fe prevs).2 = prevs ++ news ∧
        TFEq (news.foldr grPop (consBlockRecsTemp l fe prevs).1) fe
  | [], fe, prevs => ⟨[], by simp [consBlockRecsTemp], TFEq.refl _⟩
  | ci :: rest, fe, prevs => by
    simp only [consBlockRecsTemp]
    obtain ⟨news, hn, hf⟩ := bt_consBlockRecsTemp_pop rest (fe.push ci)
      (prevs ++ [(ci.name, fe.idx[ci.name]?)])
    refine ⟨(ci.name, fe.idx[ci.name]?) :: news, by rw [hn]; simp, ?_⟩
    simp only [List.foldr_cons]
    exact (hf.popTemp _ _).trans (TFEq.popTemp_push fe ci)

theorem bt_recs_temp_aux {pers : arena.store.PersTier}
    (infos : alloc.vec.Vec arena.env.IConstantInfo) :
    ∀ (q : Nat) (m : Std.Usize) (rf : arena.env.IFEnv) (lf : IFEnv)
      (prevs : alloc.vec.Vec (arena.handle.NIdx × Option Std.U64))
      (prevsL : List (NIdx × Option IConstantInfo)) rfK prevsK,
      infos.val.length - m.val = q →
      IFEnvRelI pers rf lf →
      arena.inductives.block_tail.cons_block_recs_temp infos m rf prevs = ok (rfK, prevsK) →
      IFEnvRelI pers rfK
          (consBlockRecsTemp ((infos.val.drop m.val).map absIConstantInfo) lf prevsL).1 ∧
      (∃ Q, prevsK.val = prevs.val ++ Q ∧ Q.length = q) ∧
      (∀ rfX, RFEq rfX rfK → IdxInv rfX → ∀ (j : Std.Usize) out,
        j.val = prevs.val.length + q →
        arena.inductives.gen_rec.class_fe_r_pop rfX prevsK j = ok out →
        ∃ rfY, RFEq rfY rf ∧ IdxInv rfY ∧ ∀ (j' : Std.Usize), j'.val = prevs.val.length →
          arena.inductives.gen_rec.class_fe_r_pop rfY prevsK j' = ok out) := by
  intro q
  induction q with
  | zero =>
    intro m rf lf prevs prevsL rfK prevsK hq hfe h
    rw [arena.inductives.block_tail.cons_block_recs_temp.eq_def,
      ite_eq_left (show m ≥ alloc.vec.Vec.len infos by scalar_tac)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h).symm
    refine ⟨?_, ⟨[], by simp, rfl⟩, ?_⟩
    · rw [List.drop_eq_nil_of_le (by omega), List.map_nil]; simpa [consBlockRecsTemp] using hfe
    · intro rfX hX hXi j out hj hpop
      refine ⟨rfX, hX, hXi, fun j' hj' => ?_⟩
      rw [gr_usize_ext (show j'.val = j.val by omega)]; exact hpop
  | succ q ih =>
    intro m rf lf prevs prevsL rfK prevsK hq hfe h
    have hm : m.val < infos.val.length := by omega
    rw [arena.inductives.block_tail.cons_block_recs_temp.eq_def,
      ite_eq_right (show ¬ m ≥ alloc.vec.Vec.len infos by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hiix := vec_index_some hii
    rw [List.getElem?_eq_getElem hm, Option.some.injEq] at hiix
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ii1, hii1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨pq, hpq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨prev, rf1⟩ := pq
    simp only [Aeneas.Std.uncurry_apply_pair] at h
    obtain ⟨prevs1, hprevs1, hA⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨m1, hm1', hB⟩ := ConRon.Refine.bind_eq_ok_iff.mp hA
    have hm1v : m1.val = m.val + 1 := absSz_add_one hm1'
    have hdup := i_constant_info_dup_abs hii1
    obtain ⟨hpush, n', hn', -, -, -, -, -, -, -⟩ := gr_ifenv_push_temp_spec hfe.inv hpq
    have hnn : n' = n := by
      apply absNIdx_inj
      rw [bt_name_abs hn', bt_name_abs hn, hdup]
    subst hnn
    obtain ⟨hrel1, hinv1⟩ := ifenv_push_refines hfe.rel hfe.inv hpush
    obtain ⟨ih1, ⟨Q, hQ, hQl⟩, ih3⟩ := ih m1 rf1 _ prevs1
      (prevsL ++ [((absIConstantInfo ii).name, lf.idx[(absIConstantInfo ii).name]?)]) rfK prevsK
      (by omega) ⟨hrel1, hinv1⟩ hB
    have hprevs1v := ConRon.Refine.vec_push_val hprevs1
    refine ⟨?_, ⟨(n', prev) :: Q, by rw [hQ, hprevs1v]; simp, by simp [hQl]⟩, ?_⟩
    · rw [List.drop_eq_getElem_cons hm, List.map_cons, consBlockRecsTemp, hiix]
      rw [hm1v, hdup] at ih1
      exact ih1
    · rw [← hQl]
      exact gr_pop_step hfe.inv hpq hn' hprevs1v hQ
        (fun rfX hX hXi j out hj hpop => ih3 rfX hX hXi j out (by rw [hj, hQl]) hpop)

/-- **The generated family pushed, and popped again**: the pushed layer is the
twin's `consBlockRecsTemp`, and whatever the pops return is related to the
twin's `foldr popTemp`. -/
@[lockstep] theorem cons_block_recs_temp_spec {pers : arena.store.PersTier}
    (infos : alloc.vec.Vec arena.env.IConstantInfo)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) :
    LSP (arena.inductives.block_tail.cons_block_recs_temp infos 0#usize rf (alloc.vec.Vec.new _))
      (fun r => IFEnvRelI pers r.1 (consBlockRecsTemp (absICIL infos) lf []).1 ∧
        ∀ (j : Std.Usize) out, j.val = r.2.val.length →
          arena.inductives.gen_rec.class_fe_r_pop r.1 r.2 j = ok out →
          IFEnvRelI pers out ((consBlockRecsTemp (absICIL infos) lf []).2.foldr (fun x acc => acc.popTemp x.1 x.2)
            (consBlockRecsTemp (absICIL infos) lf []).1)) := by
  intro r hr
  obtain ⟨rfK, prevsK⟩ := r
  obtain ⟨h1, ⟨Q, hQ, hQl⟩, h3⟩ := bt_recs_temp_aux infos _ 0#usize rf lf
    (alloc.vec.Vec.new _) [] rfK prevsK rfl hfe hr
  simp only [Lockstep.usize_zero_val', List.drop_zero] at h1
  refine ⟨h1, fun j out hj hpop => ?_⟩
  obtain ⟨rfY, hY, hYi, hpopY⟩ := h3 rfK (RFEq.refl _) h1.inv.1 j out
    (by rw [hj, hQ]; simp [alloc.vec.Vec.new, hQl]) hpop
  have hout := hpopY 0#usize (by simp [alloc.vec.Vec.new])
  rw [arena.inductives.gen_rec.class_fe_r_pop.eq_def, ite_eq_left rfl, Result.ok.injEq] at hout
  subst hout
  obtain ⟨news, hn, hT⟩ := bt_consBlockRecsTemp_pop (absICIL infos) lf []
  refine IFEnvRelI.transfer hfe hY hYi ?_
  rw [hn, List.nil_append]
  exact hT

/-- `block_rec_infos_tf` from the first recursor into an empty accumulator: the
records as the twin's list (the tail's call). -/
theorem block_rec_infos_tf_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (fun a b => b = absICIL a)
      (arena.inductives.rec_check.block_rec_infos_tf pers st p 0#u64 out (alloc.vec.Vec.new _)) lst
      (blockRecInfosTF (absBlockShape p) 0 (out.val.map absRecOut)) := by
  have h := block_rec_infos_tf_ls hrel hinv p 0#u64 out (alloc.vec.Vec.new _)
  refine LS.tail h (by simp [absU]) (fun a b h1 => ?_)
  simpa [absICIL, alloc.vec.Vec.new] using h1.symm

attribute [local lockstep high] block_rec_infos_tf_ls0

/-- `check_block_tables` ⊑ `checkBlockTables` from the member cursor on: the
table's checks at every structure-like member. -/
@[lockstep] theorem check_block_tables_ls {pers st lst} {rf lf}
    {p : arena.inductives.block_shape.BlockShape}
    {ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape} {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_tail.check_block_tables pers st p rf ms i) lst
      (checkBlockTables (absBlockShape p) lf ((ms.val.drop i.val).map absMemberShape)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.block_tail.check_block_tables pers st p rf ms i) lst
        (checkBlockTables (absBlockShape p) lf ((ms.val.drop i.val).map absMemberShape)))
    ?_ ?_ i () st lst hrel hinv
  · intro i _ hn st lst hrel hinv
    rw [arena.inductives.block_tail.check_block_tables, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, checkBlockTables]
    lockstep
  · intro i _ hlt ih st lst hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ st lst, AStateRel₀ pers st lst →
        AStateInv pers st → LS pers (fun _ _ => True)
          (arena.inductives.block_tail.check_block_tables pers st p rf ms j) lst
          (checkBlockTables (absBlockShape p) lf ((ms.val.drop j.val).map absMemberShape)) :=
      fun j hj => ih j () hj
    clear ih
    rw [arena.inductives.block_tail.check_block_tables, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, checkBlockTables]
    lockstep

/-- `check_block_tables` from member `0` (the tail's call). -/
@[lockstep] theorem check_block_tables_ls0 {pers st lst} {rf lf}
    {p : arena.inductives.block_shape.BlockShape}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True)
      (arena.inductives.block_tail.check_block_tables pers st p rf p.members 0#usize) lst
      (checkBlockTables (absBlockShape p) lf (absBlockShape p).members) := by
  have h := check_block_tables_ls (p := p) (ms := p.members) (i := 0#usize) hrel hinv hfe
  simpa [absBlockShape] using h

/-- `check_block_tail_stream` ⊑ the stream's records against the generated
family: the K flags, the generated records pushed TEMPORARILY, the comparison,
the pops.  Its answer is the twin's popped environment. -/
@[lockstep] theorem check_block_tail_stream_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (IFEnvRelI pers)
      (arena.inductives.block_tail.check_block_tail_stream pers st mode p out rf) lst
      (do
        streamKCheck (absBlockShape p) (absBlockShape p).recs (out.val.map absRecOut)
        let infos ← blockRecInfosTF (absBlockShape p) 0 (out.val.map absRecOut)
        let (feG, prevs) := consBlockRecsTemp infos lf []
        flushCaches
        streamRecsCheck (ConRon.Refine.absMode mode) feG (absBlockShape p).recs
          (out.val.map absRecOut)
        let fe₃ := prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feG
        flushCaches
        checkBlockTables (absBlockShape p) fe₃ (absBlockShape p).members
        pure fe₃) := by
  rw [arena.inductives.block_tail.check_block_tail_stream]
  lockstep
  all_goals
    obtain ⟨hR, hpop⟩ := ‹IFEnvRelI _ _ _ ∧ ∀ _ _, _›
    have hpe := ‹arena.inductives.gen_rec.class_fe_r_pop _ _ _ = ok _›
    have hfe3 := hpop _ _ (by simp [alloc.vec.Vec.len]) hpe
    lockstep

/-- `check_block_tail` ⊑ `checkBlockTail`, at a related pass. -/
@[lockstep] theorem check_block_tail_ls {pers st lst} {mode : kernel.env.CheckMode}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {r : arena.inductives.block_tail.BlockPass} {q : BlockPass}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : BlockPassRel pers r q) :
    LS pers (IFEnvRelI pers)
      (arena.inductives.block_tail.check_block_tail pers st mode block r) lst
      (checkBlockTail (ConRon.Refine.absMode mode) (absICIL block) q) := by
  obtain ⟨env1, qp, kinds, params, rd, cls, tbl⟩ := q
  obtain ⟨hfe, hp, hk, hpa, hrd, hcl, htb⟩ := hq
  simp only at hfe hp hk hpa hrd hcl htb
  subst hp hk hpa hrd hcl htb
  rw [arena.inductives.block_tail.check_block_tail, checkBlockTail]
  lockstep

/-! ## The block's check -/

/-- `declined_at_definition` ⊑ `declinedAtDefinition`. -/
@[lockstep] theorem declined_at_definition_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxL a)
      (arena.inductives.block_tail.declined_at_definition st) st lst declinedAtDefinition := by
  apply LSR.of_LS
  rw [arena.inductives.block_tail.declined_at_definition, declinedAtDefinition]
  lockstep

attribute [local lockstep_simp] absMemberShape_cvT
@[local lockstep_simp] theorem bt_absMemberShape_nIdx (m : arena.inductives.block_shape.MemberShape) :
    (absMemberShape m).nIdx = absU m.n_idx := rfl
@[local lockstep_simp] theorem bt_absMemberShape_ctors (m : arena.inductives.block_shape.MemberShape) :
    (absMemberShape m).ctors = absCtorsL m.ctors := rfl
@[local lockstep_simp] theorem bt_absMemberShape_declared
    (m : arena.inductives.block_shape.MemberShape) :
    (absMemberShape m).declared = absIConstantVal m.declared := rfl

/-- `block_recs` from the first record into an empty accumulator. -/
theorem bt_block_recs_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (p : arena.inductives.block_shape.BlockShape)
    (rs : alloc.vec.Vec arena.inductives.block_shape.RecShape) :
    LS pers (fun a b => b = absICIL a)
      (arena.install.block_recs pers st p rs 0#usize (alloc.vec.Vec.new _)) lst
      (blockRecs (absBlockShape p) (rs.val.map absRecShape)) := by
  have h := block_recs_ls hrel hinv p rs 0#usize (alloc.vec.Vec.new _)
  refine LS.tail h (by simp) (fun a b h1 => ?_)
  simpa [absICIL, alloc.vec.Vec.new] using h1.symm

/-- `block_tables` from the first member into an empty accumulator. -/
theorem bt_block_tables_ls0 {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) :
    LS pers (fun a b => b = a.val.map absIProjTable)
      (arena.install.block_tables pers st p ms 0#usize (alloc.vec.Vec.new _)) lst
      (blockTables (absBlockShape p) (ms.val.map absMemberShape)) := by
  have h := block_tables_ls hrel hinv p ms 0#usize (alloc.vec.Vec.new _)
  refine LS.tail h (by simp) (fun a b h1 => ?_)
  simpa [alloc.vec.Vec.new] using h1.symm

/-- `push_delta`: the block's install pushed. -/
theorem bt_push_delta_spec {pers : arena.store.PersTier} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (l : alloc.vec.Vec arena.env.IConstantInfo)
    (q : alloc.vec.Vec arena.env.IProjTable) :
    LSP (arena.install.push_delta rf l q)
      (fun o => IFEnvRelI pers o (lf.pushDelta (absICIL l) (q.val.map absIProjTable))) :=
  fun _ h => push_delta_refines hfe h

attribute [local lockstep high] bt_block_recs_ls0 bt_block_tables_ls0
attribute [local lockstep] bt_push_delta_spec

attribute [local lockstep_inline] arena.inductives.block_tail.reduce_member_checked
  arena.inductives.block_tail.check_block_reduced

/-- `reduce_member` ⊑ `reduceMember`: a member's former at its telescope. -/
@[lockstep] theorem reduce_member_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (ms : arena.inductives.block_shape.MemberShape) (n_p : Std.U64) :
    LS pers (fun a b => b = absMemberShape a)
      (arena.inductives.block_tail.reduce_member pers st mode rf ms n_p) lst
      (reduceMember (ConRon.Refine.absMode mode) lf (absMemberShape ms) (absU n_p)) := by
  rw [arena.inductives.block_tail.reduce_member, reduceMember]
  lockstep
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    first
    | exact (member_shape_dup_abs ‹_›).symm
    | simp_all [absMemberShape]

/-- `reduce_members` ⊑ `reduceMembers` from the cursor on, behind the
accumulator. -/
@[lockstep] theorem reduce_members_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (n_p : Std.U64) (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) (i : Std.Usize)
    (out : alloc.vec.Vec arena.inductives.block_shape.MemberShape) :
    LS pers (fun a b => a.val.map absMemberShape = out.val.map absMemberShape ++ b)
      (arena.inductives.block_tail.reduce_members pers st mode rf n_p ms i out) lst
      (reduceMembers (ConRon.Refine.absMode mode) lf (absU n_p)
        ((ms.val.drop i.val).map absMemberShape)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ st lst (out : alloc.vec.Vec arena.inductives.block_shape.MemberShape),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absMemberShape = out.val.map absMemberShape ++ b)
        (arena.inductives.block_tail.reduce_members pers st mode rf n_p ms i out) lst
        (reduceMembers (ConRon.Refine.absMode mode) lf (absU n_p)
          ((ms.val.drop i.val).map absMemberShape))) ?_ ?_ i () st lst out hrel hinv
  · intro i _ hn st lst out hrel hinv
    rw [arena.inductives.block_tail.reduce_members, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, reduceMembers]
    lockstep
  · intro i _ hlt ih st lst out hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ st lst
        (out : alloc.vec.Vec arena.inductives.block_shape.MemberShape),
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => a.val.map absMemberShape = out.val.map absMemberShape ++ b)
          (arena.inductives.block_tail.reduce_members pers st mode rf n_p ms j out) lst
          (reduceMembers (ConRon.Refine.absMode mode) lf (absU n_p)
            ((ms.val.drop (i.val + 1)).map absMemberShape)) := by
      intro j hj; simpa only [hj] using ih j () hj
    clear ih
    rw [arena.inductives.block_tail.reduce_members, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, reduceMembers]
    lockstep
    rename_i out1 hout1
    refine ls_map_twin (ih' _ (by scalar_tac) _ _ _ ‹_› ‹_›) ?_
    intro r b hr
    rw [hr, hout1]
    simp_all

/-- **`block_tail::check_block` ⊑ `checkBlock`** — a block checked, and its
install pushed onto the constructors' environment. -/
@[lockstep] theorem check_block_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {p0 : arena.inductives.block_shape.BlockShape}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (IFEnvRelI pers)
      (arena.inductives.block_tail.check_block pers st mode rf block p0) lst
      (checkBlock (ConRon.Refine.absMode mode) lf (absICIL block) (absBlockShape p0)) := by
  rw [arena.inductives.block_tail.check_block, checkBlock]
  lockstep
  simp only [TwinEq] at hP
  rw [← hP, absBlockShape_recs, absBlockShape_members]
  lockstep

end ConRon.Refine2
