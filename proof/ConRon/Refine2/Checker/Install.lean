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
import ConRon.Refine2.Inductives.Abs
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

/-! ## What a declaration installs -/

/-- **`decl_constants` ⊑ `declConstants`**: the constants a declaration installs,
in push order, read off the record (`stream_index::build_index`'s step). -/
theorem decl_constants_refines {pers st lst} {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.install.decl_constants pers st pd = ok o) :
    SimRel₀ (fun cs L => L = cs.val.map absIConstantInfo) pers lst o
      (declConstants (absIDeclaration pd)) := by
  sorry -- T143-STUB

/-- **`decl_tables` ⊑ `declTables`**: the projection tables a declaration
installs. -/
theorem decl_tables_refines {pers st lst} {pd : arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.install.decl_tables pers st pd = ok o) :
    SimRel₀ (fun ts Q => Q = ts.val.map absIProjTable) pers lst o
      (declTables (absIDeclaration pd)) := by
  sorry -- T143-STUB

end ConRon.Refine2
