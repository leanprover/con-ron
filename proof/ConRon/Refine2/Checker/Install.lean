/-
# `ConRon.Refine2.Checker.Install` — Theorem 2 for `arena::install`

**Task #143.**  `crates/con-ron-core/src/arena/install.rs` against
`proof/ConRon/Arena/Install.lean`: what a declaration installs, read off the
record with no inference and no reduction — its constants (`decl_constants`)
and its projection tables (`decl_tables`), and the push of both onto an
environment (`push_delta`).  `stream_index::build_index` reads every record
through the two `decl_*` functions; a block's check pushes its constants onto
the constructors' environment through `push_delta`.

The Rust builds its lists by a cursor pushing onto an accumulator, where the
twin maps; each cursor lemma reads `<abs> o = <abs> out ++ <the twin from the
cursor on>`, the shape of `Refine2/Inductives/StructParts.lean`'s cursors.
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Refine2.Tactic.Lockstep
import ConRon.Refine2.Inductives.Abs
import ConRon.Refine2.Inductives.BlockInstall
import ConRon.Refine2.Inductives.BlockShape
import ConRon.Refine2.Checker.Basis
import ConRon.Arena.Install

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The copies -/

/-- `stream_index::i_proj_table_dup` is the identity on the abstraction. -/
theorem i_proj_table_dup_abs {t o : arena.env.IProjTable}
    (h : arena.stream_index.i_proj_table_dup t = ok o) : absIProjTable o = absIProjTable t := by
  rw [arena.stream_index.i_proj_table_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIProjTable, dupId_nidx _ _ hn, dupId_nidx _ _ hc, nidx_vec_dup_val hv,
    eidx_vec_dup_val hb]

/-! ## The pushes -/

/-- `push_delta_consts` ⊑ `IFEnv.pushAll` from the cursor on: each record
pushed, in order. -/
theorem push_delta_consts_refines {pers : arena.store.PersTier}
    {l : alloc.vec.Vec arena.env.IConstantInfo} :
    ∀ (i : Std.Usize) (rf : arena.env.IFEnv) (lf : IFEnv) (o : arena.env.IFEnv),
      IFEnvRelI pers rf lf → arena.install.push_delta_consts rf l i = ok o →
      IFEnvRelI pers o (IFEnv.pushAll ((l.val.drop i.val).map absIConstantInfo) lf) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) l.val.length
    (fun i (_ : Unit) => ∀ (rf : arena.env.IFEnv) (lf : IFEnv) (o : arena.env.IFEnv),
      IFEnvRelI pers rf lf → arena.install.push_delta_consts rf l i = ok o →
      IFEnvRelI pers o (IFEnv.pushAll ((l.val.drop i.val).map absIConstantInfo) lf))
    ?_ ?_ i ()
  · intro i _ hn rf lf o hfe h
    rw [arena.install.push_delta_consts.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len l by scalar_tac)] at h
    obtain rfl := Result.ok_injective h
    rw [List.drop_eq_nil_of_le hn]
    exact hfe
  · intro i _ hlt ih rf lf o hfe h
    rw [arena.install.push_delta_consts.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len l by scalar_tac)] at h
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ci, hci, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨fe1, hfe1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx : l.val[i.val]? = some ii := vec_index_some hii
    have hxv : l.val[i.val] = ii := (List.getElem?_eq_some_iff.mp hx).2
    obtain ⟨hrel1, hinv1⟩ := ifenv_push_refines hfe.rel hfe.inv hfe1
    have h3 : i3.val = i.val + 1 := absSz_add_one hi3
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, hxv, IFEnv.pushAll]
    have := ih i3 () h3 fe1 _ o ⟨by rwa [i_constant_info_dup_abs hci] at hrel1, hinv1⟩ h
    rwa [h3] at this

/-- `push_delta_tables` ⊑ `IFEnv.pushTables` from the cursor on. -/
theorem push_delta_tables_refines {pers : arena.store.PersTier}
    {q : alloc.vec.Vec arena.env.IProjTable} :
    ∀ (i : Std.Usize) (rf : arena.env.IFEnv) (lf : IFEnv) (o : arena.env.IFEnv),
      IFEnvRelI pers rf lf → arena.install.push_delta_tables rf q i = ok o →
      IFEnvRelI pers o (IFEnv.pushTables ((q.val.drop i.val).map absIProjTable) lf) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) q.val.length
    (fun i (_ : Unit) => ∀ (rf : arena.env.IFEnv) (lf : IFEnv) (o : arena.env.IFEnv),
      IFEnvRelI pers rf lf → arena.install.push_delta_tables rf q i = ok o →
      IFEnvRelI pers o (IFEnv.pushTables ((q.val.drop i.val).map absIProjTable) lf))
    ?_ ?_ i ()
  · intro i _ hn rf lf o hfe h
    rw [arena.install.push_delta_tables.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len q by scalar_tac)] at h
    obtain rfl := Result.ok_injective h
    rw [List.drop_eq_nil_of_le hn]
    exact hfe
  · intro i _ hlt ih rf lf o hfe h
    rw [arena.install.push_delta_tables.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len q by scalar_tac)] at h
    obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨fe1, hfe1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx : q.val[i.val]? = some it := vec_index_some hit
    have hxv : q.val[i.val] = it := (List.getElem?_eq_some_iff.mp hx).2
    obtain ⟨hrel1, hinv1⟩ := ifenv_push_table_refines hfe.rel hfe.inv hfe1
    have h3 : i3.val = i.val + 1 := absSz_add_one hi3
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, hxv, IFEnv.pushTables]
    have := ih i3 () h3 fe1 _ o ⟨by rwa [i_proj_table_dup_abs ht] at hrel1, hinv1⟩ h
    rwa [h3] at this

/-- **`push_delta` ⊑ `IFEnv.pushDelta`**: a declaration's constants, then its
tables, pushed in order, the related and well-formed environment after. -/
theorem push_delta_refines {pers : arena.store.PersTier} {rf o : arena.env.IFEnv} {lf : IFEnv}
    {l : alloc.vec.Vec arena.env.IConstantInfo} {q : alloc.vec.Vec arena.env.IProjTable}
    (hfe : IFEnvRelI pers rf lf) (h : arena.install.push_delta rf l q = ok o) :
    IFEnvRelI pers o (lf.pushDelta (l.val.map absIConstantInfo) (q.val.map absIProjTable)) := by
  rw [arena.install.push_delta] at h
  obtain ⟨fe1, hfe1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := push_delta_consts_refines 0#usize rf lf fe1 hfe hfe1
  have h2 := push_delta_tables_refines 0#usize fe1 _ o h1 h
  simpa [IFEnv.pushDelta] using h2

/-! ## The pure list builders -/

/-- `block_ctors` ⊑ `blockCtors` from the cursor on. -/
theorem block_ctors_abs {n_p : Std.U64} {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IConstantInfo),
      arena.install.block_ctors n_p cs i out = ok o →
      o.val.map absIConstantInfo = out.val.map absIConstantInfo ++
        (cs.val.drop i.val).map fun c =>
          IConstantInfo.ctorInfo (absIConstantVal c.1) (absU n_p) (absU c.2) := by
  refine vec_cursor_copy cs absIConstantInfo _ (arena.install.block_ctors n_p cs) ?_ ?_
  · intro i out o hn h
    rw [arena.install.block_ctors.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.install.block_ctors.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, nf⟩ := p
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hex : (iv, nf) = x := by
      have h1 := vec_index_some hp; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hex
    exact ⟨i3, _, out1, absSz_add_one hi3, ConRon.Refine.vec_push_val hout1,
      by simp [absIConstantInfo, i_constant_val_dup_abs hiv1], h⟩

/-- `rules_with_fire` ⊑ `rc.rules.map ({ · with fire := f })` from the cursor on. -/
theorem rules_with_fire_abs {rules : alloc.vec.Vec arena.env.IRecRule}
    {f : arena.env.IRecRuleFire} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IRecRule),
      arena.install.rules_with_fire rules f i out = ok o →
      o.val.map absIRecRule = out.val.map absIRecRule ++
        (rules.val.drop i.val).map fun r => { absIRecRule r with fire := absIRecRuleFire f } := by
  refine vec_cursor_copy rules absIRecRule _ (arena.install.rules_with_fire rules f) ?_ ?_
  · intro i out o hn h
    rw [arena.install.rules_with_fire.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len rules by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.install.rules_with_fire.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rules by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨ir, hir, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨irf, hirf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hex : ir = x := by
      have h1 := vec_index_some hir; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hex
    exact ⟨i3, _, out1, absSz_add_one hi3, ConRon.Refine.vec_push_val hout1,
      by simp [absIRecRule, dupId_nidx _ _ hn, dupId_eidx _ _ he,
        i_rec_rule_fire_dup_abs hirf], h⟩

/-- `block_formers` ⊑ `blockFormers` from the member cursor on, behind the accumulator:
each member as declared, with the capabilities its block gives it at its index. -/
theorem block_formers_abs (p : arena.inductives.block_shape.BlockShape) (is_rec : Bool) :
    ∀ (N : Nat) (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IConstantInfo),
      p.members.val.length - i.val = N →
      arena.install.block_formers p is_rec i out = ok o →
      o.val.map absIConstantInfo = out.val.map absIConstantInfo ++
        ((p.members.val.zipIdx).drop i.val).map fun q =>
          IConstantInfo.indInfo (absIConstantVal q.1.declared)
            (blockCapsAt (absBlockShape p) q.2 is_rec) := by
  intro N
  induction N with
  | zero =>
    intro i out o hN h
    rw [arena.install.block_formers.eq_def, ite_eq_left (by scalar_tac), Result.ok.injEq] at h
    rw [h, List.drop_eq_nil_of_le (by simp; scalar_tac)]
    simp
  | succ N ih =>
    intro i out o hN h
    have hlt : i.val < p.members.val.length := by omega
    rw [arena.install.block_formers.eq_def, ite_eq_right (by scalar_tac)] at h
    obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ic, hic, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hmv : p.members.val[i.val]? = some m := vec_index_some hm
    have hi2v : i2.val = i.val := by
      simp only [lift, Result.ok.injEq] at hi2; subst hi2; rw [usize_cast_u64_val']
    have hi3v : i3.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
    have hcaps : blockCapsAt (absBlockShape p) i.val is_rec = absIIndCaps ic := by
      have : Lockstep.TwinEq _ _ := block_caps_at_twin p i2 is_rec ic hic
      have hu : absU i2 = i.val := hi2v
      unfold Lockstep.TwinEq at this
      rw [hu] at this
      exact this
    rw [ih i3 out1 o (by omega) h, ConRon.Refine.vec_push_val hout1, hi3v]
    have hz : (p.members.val.zipIdx).drop i.val =
        (m, i.val) :: (p.members.val.zipIdx).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      congr 1
      rw [List.getElem_zipIdx]
      rw [List.getElem?_eq_getElem hlt] at hmv
      simp [Option.some_inj.mp hmv]
    rw [hz]
    simp [absIConstantInfo, i_constant_val_dup_abs hiv, hcaps]

/-- `block_formers` from member `0`, as the twin's `blockFormers`. -/
theorem block_formers_eq {p : arena.inductives.block_shape.BlockShape} {is_rec : Bool}
    {o : alloc.vec.Vec arena.env.IConstantInfo}
    (h : arena.install.block_formers p is_rec 0#usize (alloc.vec.Vec.new _) = ok o) :
    o.val.map absIConstantInfo = blockFormers (absBlockShape p) is_rec := by
  rw [block_formers_abs p is_rec _ 0#usize _ o rfl h]
  simp only [alloc.vec.Vec.new, show ((0#usize : Std.Usize)).val = 0 from rfl,
    List.drop_zero, blockFormers, absBlockShape_members, List.map_map]
  rw [List.zipIdx_map]
  simp [Function.comp_def, absMemberShape]

/-! ## The dropped variables -/

open Lockstep in
theorem expr_drop_vars_aux {pers} (N : Nat) :
    ∀ (n : Std.U64) (e : arena.handle.EIdx) st lst,
      n.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (arena.install.expr_drop_vars pers st n e) lst
        (exprDropVars (absU n) (absEIdx e)) := by
  induction N with
  | zero =>
    intro n e st lst hn hrel hinv
    have h0 : n = 0#u64 := by scalar_tac
    subst h0
    rw [arena.install.expr_drop_vars.eq_def, ite_eq_left rfl,
      show absU (0#u64 : Std.U64) = 0 from rfl, exprDropVars]
    lockstep
  | succ N ih =>
    intro n e st lst hn hrel hinv
    rw [arena.install.expr_drop_vars.eq_def, ite_eq_right (by scalar_tac),
      show absU n = N + 1 by simp [absU, hn], exprDropVars]
    lockstep

open Lockstep in
@[lockstep] theorem expr_drop_vars_ls {pers st lst} {n : Std.U64} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.install.expr_drop_vars pers st n e) lst
      (exprDropVars (absU n) (absEIdx e)) :=
  expr_drop_vars_aux _ n e st lst rfl hrel hinv

open Lockstep in
theorem drop_vars_all_aux {pers} (n : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) (N : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      xs.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absEIdx = out.val.map absEIdx ++ b)
        (arena.install.drop_vars_all pers st n xs i out) lst
        (((xs.val.drop i.val).map absEIdx).mapM (exprDropVars (absU n))) := by
  induction N with
  | zero =>
    intro i out st lst hN hrel hinv
    rw [arena.install.drop_vars_all.eq_def, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, List.mapM_nil]
    lockstep
  | succ N ih =>
    intro i out st lst hN hrel hinv
    have hlt : i.val < xs.val.length := by omega
    rw [arena.install.drop_vars_all.eq_def, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, List.mapM_cons]
    lockstep
    rename_i _ x out1 hout1
    have h := ih a out1 st1 lst1 (by have := hP; scalar_tac) hrel hinv
    rw [hP, show ((1#usize : Std.Usize)).val = 1 from rfl] at h
    refine LS.tail_bind_pure h ?_
    intro r b hb
    rw [hb, hout1]
    simp

open Lockstep in
@[lockstep] theorem drop_vars_all_ls {pers st lst} {n : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a.val.map absEIdx)
      (arena.install.drop_vars_all pers st n xs 0#usize (alloc.vec.Vec.new _)) lst
      ((xs.val.map absEIdx).mapM (exprDropVars (absU n))) := by
  refine LS.tail (drop_vars_all_aux n xs _ 0#usize _ st lst rfl hrel hinv) (by simp) ?_
  intro a b h
  simpa [alloc.vec.Vec.new] using h.symm

/-! ## How a recursor's rules fire -/

/-- `recFire`'s major-domain arm, the Rust's `rec_fire_dom`: at a constant head,
`.nested` at its levels and its leading arguments, the index variables dropped. -/
def recFireDomSpec (rc : RecShape) (dom : EIdx) : AM IRecRuleFire := do
  let hd ← getAppFn coreWalkFuel dom
  if hd.tag == ETag.const then
    match ← viewConst hd with
    | none => failDanglingE
    | some (_, us) => do
      let lvls ← viewLs us
      let args ← getAppArgs coreWalkFuel dom
      let nI := rc.mI - rc.rP
      let ps ← (args.take (args.length - nI)).mapM (exprDropVars nI)
      pure (.nested lvls ps)
  else pure .plain

theorem recFire_split (p : BlockShape) (rc : RecShape) :
    recFire p rc = (do
      if rc.tgt < p.k then pure .plain
      else
        match ← stripPis rc.mI rc.cvR.type with
        | none => pure .plain
        | some q =>
          if q.2.tag == ETag.forallE then
            match ← viewBind q.2 with
            | none => failDanglingE
            | some (dom, _) => recFireDomSpec rc dom
          else pure .plain) := rfl

open Lockstep in
@[lockstep] theorem rec_fire_dom_ls {pers st lst} {rc : arena.inductives.block_shape.RecShape}
    {dom : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIRecRuleFire a) (arena.install.rec_fire_dom pers st rc dom) lst
      (recFireDomSpec (absRecShape rc) (absEIdx dom)) := by
  rw [arena.install.rec_fire_dom, recFireDomSpec]
  lockstep
  -- the leading arguments: the port's `take_eidx_n` at the saturated count
  rename_i lvls _ _ args nI hnI len hlen k hk
  have hl := absEIdxL_of_takeEidx hP
  have e1 : (absRecShape rc).mI - (absRecShape rc).rP = absU nI := by
    simp only [absRecShape, absU]; omega
  have hlenv : len.val = args.val.length := by rw [hlen]; simp [alloc.vec.Vec.len]
  have e2 : List.take ((List.map absEIdx args.val).length - absU nI) (List.map absEIdx args.val)
      = a.val.map absEIdx := by
    have hl' : a.val.map absEIdx = (args.val.map absEIdx).take k.val := by
      simpa [absEIdxL] using hl
    rw [hl', List.length_map]
    congr 1
    simp only [absU]; omega
  rw [e1, e2]
  lockstep

open Lockstep in
@[lockstep] theorem rec_fire_ls {pers st lst} {p : arena.inductives.block_shape.BlockShape}
    {rc : arena.inductives.block_shape.RecShape}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIRecRuleFire a) (arena.install.rec_fire pers st p rc) lst
      (recFire (absBlockShape p) (absRecShape rc)) := by
  rw [arena.install.rec_fire, recFire_split]
  lockstep

/-! ## A block's constants and tables -/

/-- `block_recs` ⊑ `blockRecs` from the recursor cursor on, behind the
accumulator: each record with its rules' firing mode. -/
theorem block_recs_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (p : arena.inductives.block_shape.BlockShape)
    (rs : alloc.vec.Vec arena.inductives.block_shape.RecShape) (i : Std.Usize)
    (out : alloc.vec.Vec arena.env.IConstantInfo) :
    Lockstep.LS pers (fun a b => a.val.map absIConstantInfo = out.val.map absIConstantInfo ++ b)
      (arena.install.block_recs pers st p rs i out) lst
      (blockRecs (absBlockShape p) ((rs.val.drop i.val).map absRecShape)) := by
  suffices h : ∀ N (i : Std.Usize) out st lst, rs.val.length - i.val = N →
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => a.val.map absIConstantInfo = out.val.map absIConstantInfo ++ b)
        (arena.install.block_recs pers st p rs i out) lst
        (blockRecs (absBlockShape p) ((rs.val.drop i.val).map absRecShape)) from
    h _ i out st lst rfl hrel hinv
  intro N
  induction N with
  | zero =>
    intro i out st lst hN hrel hinv
    rw [arena.install.block_recs.eq_def, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, blockRecs]
    lockstep
  | succ N ih =>
    intro i out st lst hN hrel hinv
    have hlt : i.val < rs.val.length := by omega
    rw [arena.install.block_recs.eq_def, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, blockRecs]
    lockstep
    rename_i _ f cv' hcv rules' out1 hout1
    have h := ih a out1 st1 lst1 (by have := hP; scalar_tac) hrel hinv
    rw [hP, show ((1#usize : Std.Usize)).val = 1 from rfl] at h
    refine Lockstep.LS.tail_bind_pure h ?_
    intro r b hb
    have hw := rules_with_fire_abs 0#usize _ rules' hf
    rw [hb, hout1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    congr 2
    simp only [absIConstantInfo, absRecShape, hcv]
    congr 1
    simp only [alloc.vec.Vec.new, List.map_map] at hw ⊢
    rw [hw]
    rfl

/-- `block_shape::member_struct_ctor` ⊑ `MemberShape.structCtor?`. -/
theorem member_struct_ctor_abs {ms : arena.inductives.block_shape.MemberShape} {o}
    (h : arena.inductives.block_shape.member_struct_ctor ms = ok o) :
    (absMemberShape ms).structCtor? = o.map fun c => (absIConstantVal c.1, absU c.2) := by
  rw [arena.inductives.block_shape.member_struct_ctor] at h
  simp only [absMemberShape, MemberShape.structCtor?, absCtorsL]
  by_cases h1 : alloc.vec.Vec.len ms.ctors = 1#usize
  · rw [ite_eq_left h1] at h
    have hl : ms.ctors.val.length = 1 := by
      have := congrArg Aeneas.Std.UScalar.val h1; simpa [alloc.vec.Vec.len] using this
    obtain ⟨c, hc⟩ : ∃ c, ms.ctors.val = [c] := List.length_eq_one_iff.mp hl
    rw [hc]
    simp only [List.map_cons, List.map_nil]
    by_cases h2 : ms.n_idx = 0#u64
    · rw [ite_eq_left h2] at h
      obtain ⟨⟨iv, i1⟩, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain rfl := (Result.ok_injective h).symm
      have hpv := vec_index_some hp
      rw [hc] at hpv
      simp only [show ((0#usize : Std.Usize)).val = 0 from rfl, List.getElem?_cons_zero,
        Option.some.injEq] at hpv
      subst hpv
      have h0 : absU ms.n_idx = 0 := by rw [h2]; rfl
      simp [h0, i_constant_val_dup_abs hiv1]
    · rw [ite_eq_right h2] at h
      obtain rfl := (Result.ok_injective h).symm
      have h0 : absU ms.n_idx ≠ 0 := by
        intro h0; apply h2; simp only [absU] at h0; scalar_tac
      simp [h0]
  · rw [ite_eq_right h1] at h
    obtain rfl := (Result.ok_injective h).symm
    have hl : ms.ctors.val.length ≠ 1 := by
      intro hl; apply h1; scalar_tac
    match hc : ms.ctors.val with
    | [] => simp
    | [_] => simp [hc] at hl
    | _ :: _ :: _ => simp

open Lockstep in
@[lockstep] theorem member_struct_ctor_twin (ms : arena.inductives.block_shape.MemberShape) :
    LSP (arena.inductives.block_shape.member_struct_ctor ms)
      (fun o => TwinEq (absMemberShape ms).structCtor?
        (o.map fun c => (absIConstantVal c.1, absU c.2))) :=
  fun _ h => member_struct_ctor_abs h

/-- `block_tables` ⊑ `blockTables` from the member cursor on, behind the
accumulator: one table per structure-like member, `none` where one's
constructor is too short. -/
theorem block_tables_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (p : arena.inductives.block_shape.BlockShape)
    (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape) (i : Std.Usize)
    (out : alloc.vec.Vec arena.env.IProjTable) :
    Lockstep.LS pers (fun a b => a.map (fun v => v.val.map absIProjTable) =
        b.map (out.val.map absIProjTable ++ ·))
      (arena.install.block_tables pers st p ms i out) lst
      (blockTables (absBlockShape p) ((ms.val.drop i.val).map absMemberShape)) := by
  suffices h : ∀ N (i : Std.Usize) out st lst, ms.val.length - i.val = N →
      AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers (fun a b => a.map (fun v => v.val.map absIProjTable) =
          b.map (out.val.map absIProjTable ++ ·))
        (arena.install.block_tables pers st p ms i out) lst
        (blockTables (absBlockShape p) ((ms.val.drop i.val).map absMemberShape)) from
    h _ i out st lst rfl hrel hinv
  intro N
  induction N with
  | zero =>
    intro i out st lst hN hrel hinv
    rw [arena.install.block_tables.eq_def, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, blockTables]
    lockstep
  | succ N ih =>
    intro i out st lst hN hrel hinv
    have hlt : i.val < ms.val.length := by omega
    rw [arena.install.block_tables.eq_def, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, blockTables]
    lockstep
    rename_i _ c1 c2 hsc bodies lps hlps out1 hout1
    have h := ih a out1 st1 lst1 (by have := hP; scalar_tac) hrel hinv
    rw [hP, show ((1#usize : Std.Usize)).val = 1 from rfl] at h
    refine Lockstep.LS.tail_bind_pure h ?_
    intro r b hb
    rw [hout1] at hb
    cases r <;> cases b <;>
      simp_all [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    rfl

open Lockstep in
/-- `block_tables` from member `0` and an empty accumulator: `blockTables` of the
block's members. -/
@[lockstep] theorem block_tables_ls0 {pers st lst} {p : arena.inductives.block_shape.BlockShape}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a.map (fun v => v.val.map absIProjTable))
      (arena.install.block_tables pers st p p.members 0#usize (alloc.vec.Vec.new _)) lst
      (blockTables (absBlockShape p) (absBlockShape p).members) := by
  refine LS.tail (block_tables_ls hrel hinv p p.members 0#usize _) (by
    simp [absBlockShape_members]) ?_
  intro a b h
  cases a <;> cases b <;> simp_all [alloc.vec.Vec.new]

open Lockstep in
@[lockstep] theorem block_formers_twin0 (p : arena.inductives.block_shape.BlockShape) (is_rec : Bool) :
    LSP (arena.install.block_formers p is_rec 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (blockFormers (absBlockShape p) is_rec) (o.val.map absIConstantInfo)) :=
  fun _ h => (block_formers_eq h).symm

open Lockstep in
/-- `block_constants` ⊑ `blockConstants`: the formers, the constructors, the recursors. -/
@[lockstep] theorem block_constants_ls {pers st lst} {p : arena.inductives.block_shape.BlockShape}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a.val.map absIConstantInfo)
      (arena.install.block_constants pers st p) lst (blockConstants (absBlockShape p)) := by
  rw [arena.install.block_constants, blockConstants]
  lockstep
  rename_i _ formers _ all
  have hall := hP
  have hc := block_ctors_abs 0#usize formers a hf
  have hb := block_recs_ls hrel hinv p p.recs 0#usize a
  simp only [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hb
  refine LS.tail_bind_pure hb ?_
  intro r rs hr
  rw [hr, hc]
  unfold TwinEq at hall
  simp only [List.drop_zero, show ((0#usize : Std.Usize)).val = 0 from rfl, blockCtors]
  rw [hall]
  simp only [absCtorsL, List.map_map, List.append_assoc]
  rfl

/-! ## What a declaration installs -/

open Lockstep in
/-- `decl_constants_axiom` ⊑ `declConstantsAxiom`: `Quot.sound`'s pin at the record's
names, `sorryAx` nothing, any other axiom itself. -/
@[lockstep] theorem decl_constants_axiom_ls {pers st lst} {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a.val.map absIConstantInfo)
      (arena.install.decl_constants_axiom pers st cv) lst
      (declConstantsAxiom (absIConstantVal cv)) := by
  rw [arena.install.decl_constants_axiom, declConstantsAxiom]
  lockstep

open Lockstep in
/-- `decl_constants` ⊑ `declConstants`, in the lockstep shape. -/
theorem decl_constants_ls {pers st lst} {pd : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a.val.map absIConstantInfo)
      (arena.install.decl_constants pers st pd) lst (declConstants (absIDeclaration pd)) := by
  cases pd <;> simp only [arena.install.decl_constants, absIDeclaration, declConstants] <;>
    lockstep

open Lockstep in
/-- `decl_tables` ⊑ `declTables`, in the lockstep shape. -/
theorem decl_tables_ls {pers st lst} {pd : arena.env.IDeclaration}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a.val.map absIProjTable)
      (arena.install.decl_tables pers st pd) lst (declTables (absIDeclaration pd)) := by
  cases pd <;> simp only [arena.install.decl_tables, absIDeclaration, declTables] <;>
    lockstep

/-- **`decl_constants` ⊑ `declConstants`**: the constants a declaration installs,
in push order, read off the record (`stream_index::build_index`'s step). -/
theorem decl_constants_refines {pers st lst} {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.install.decl_constants pers st pd = ok o) :
    SimRel₀ (fun cs L => L = cs.val.map absIConstantInfo) pers lst o
      (declConstants (absIDeclaration pd)) :=
  Lockstep.LS.toSimRel₀ (decl_constants_ls hrel hinv) hrun

/-- **`decl_tables` ⊑ `declTables`**: the projection tables a declaration
installs. -/
theorem decl_tables_refines {pers st lst} {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.install.decl_tables pers st pd = ok o) :
    SimRel₀ (fun ts Q => Q = ts.val.map absIProjTable) pers lst o
      (declTables (absIDeclaration pd)) :=
  Lockstep.LS.toSimRel₀ (decl_tables_ls hrel hinv) hrun

end ConRon.Refine2
