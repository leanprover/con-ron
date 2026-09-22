import ConRon.RefineOld.Frontend.Readers
import ConRon.RefineOld.Frontend.ProjRec

/-! # The inductive record's install (task #85, phase 1)

`export_c::install_ind_d` and everything under it: the block's
`ConstantInfo`s, the projection-owner table, the in-process modeller's
generated records, and the pushes into the parse state.  Every change to
`StateD` that a validated `#IND` line makes is here, and the capstone
`install_ind_d_wf` says the state that comes out is what `StateDWF` claims.

The shape is always the same.  A Rust `fn f(st: &mut StateD, …) -> Result<(),
LineErr>` extracts to a pair-returning function, so a lemma reads

    (h : frontend.export_c.f st … = ok (.Ok (), st')) : StateDWF st'

and a `fn f(st: &mut StateD, …)` with no `Result` drops the `core::result`
wrapper.  The three block loops and the three projection-record loops are
`while i < n` accumulators: `partial_fixpoint` definitions with no induction
principle, so each is proved by strong induction on the measure `n - i`,
exactly as `Refine/Frontend/Readers.lean`'s `st_names_loop_wf` is.

One mechanical note for the next reader.  A `&mut` call whose result is a
*pair* — `let (_, hm) = map.insert(…)`, `let (r1, st1) = register_proj_owners(…)`
— extracts to a bind whose continuation is a `Function.uncurry`, and neither
`simp only [bind_eq_ok_iff]` nor `dsimp` nor `split` sees through it.  The
lemma that peels it is `uncurry_apply_pair`, and it only fires once the pair
itself has been destructured, so the step is always the three lines
`obtain … p …; obtain ⟨_, hm⟩ := p; simp only [uncurry_apply_pair, …] at h`.

## What carries no clause, and why

**`validate_ind_d` and its ~20 helpers.**  `check_one_ctor`,
`order_block_ctors`, `check_rec_records`, `k_expected_of`, `ctor_index_of` and
the error renderers all work on `scan_types::IndTypeRec`/`IndCtorRec`/
`IndRecRec`, and those records hold a `CVRec` of `u64` *indices* into the
parse's three tables plus machine words and bools (`Generated/Types.lean`
lines 899-969) — never a `Name`, `Level` or `Expr`.  Validation therefore
cannot produce an ill-formed term and cannot consume a well-formed one; it has
nothing to say to `StateDWF` and is skipped entirely.  The terms first appear
at `parse_cv_d`/`st_names`/`parse_rules_d`, which is where the block loops
below pick them up.

**`block_rec_of` and `note_ind_blocks`.**  The `in_model_rec::BlockRec` those
two build and file under `st.ind_blocks` is handed to the **modeller** and to
nothing else, and `Base.lean`'s `ModellerWF` is unconditional in its argument:
whatever `generate` returns is well formed, no matter which `ModelCtx` it was
shown.  That is the payoff of task #84's seam — `StateDWF` needs no clause for
`ind_blocks`, none for the block records, and none for the `const_types`/
`heights` that `state_model_ctx` reads alongside them, so `block_rec_of`'s
three loops get no lemma at all and `note_ind_blocks` gets a trivial one.  The
day upstream drops the modeller, `ModellerWF` and this paragraph go with it.

`gen_records` and `gen_owner` are the same story from the other side:
`note_gen_names` writes only those two, `StateDWF` has no clause for either,
and the lemma is six `hst.<field>`s.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Plumbing

`Refine/Frontend/Readers.lean` keeps its copies of the first two `private`;
they are one line each and restated here rather than widening that file's
interface. -/

/-- What a `Vec` read hands back is one of the `Vec`'s entries. -/
private theorem vec_mem {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    x ∈ v.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? h)

/-- A push extends a "every entry satisfies `P`" invariant by the pushed element. -/
private theorem push_mem {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  rw [vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- `name::dup` is the identity. -/
private theorem name_dup_refines {n r : name.Name} (h : name.dup n = ok r) : r = n := by
  rw [name_dup_eq] at h
  simp only [Result.ok.injEq] at h
  exact h.symm

/-- `Vec::deref` is the identity on the underlying list. -/
private theorem deref_val {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).val = v.val := Slice.from_val _ _

/-- A state update that touches none of the six tracked fields keeps the
invariant.  Every equation is `rfl` at a record update of an untracked field,
so the use sites read `stateDWF_same hst rfl rfl rfl rfl rfl rfl`. -/
private theorem stateDWF_same {st st' : frontend.export_c.StateD} (hst : StateDWF st)
    (hn : st'.names = st.names) (hl : st'.levels = st.levels)
    (he : st'.exprs = st.exprs) (hd : st'.decls = st.decls)
    (ho : st'.proj_owners = st.proj_owners) (hp : st'.proj_levels = st.proj_levels) :
    StateDWF st' :=
  ⟨hn ▸ hst.names, hl ▸ hst.levels, he ▸ hst.exprs, hd ▸ hst.decls,
   ho ▸ hst.proj_owners, hp ▸ hst.proj_levels⟩

/-! ## The block's constants

`installIndD`'s `types ++ ctors ++ recs`, as three accumulating loops and a
joiner.  Each loop reads a `ConstantVal` through `parse_cv_d` and pushes one
`ConstantInfo`, so the invariant is `ConstantInfosWF` on the accumulator. -/

/-- `export_c::ind_block_types` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`, the cited `tys.mapM`), as its loop. -/
private theorem ind_block_types_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (b : alloc.vec.Vec env.ConstantInfo),
      StateDWF st → ConstantInfosWF out → n.val - i.val = N →
      frontend.export_c.ind_block_types_loop st tys out n i = ok (.Ok b) →
      ConstantInfosWF b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st tys out n i b hst hout hN h
    rw [frontend.export_c.ind_block_types_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, -, r, hr, h⟩ := h
      cases r with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨ic, hic, out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        refine ih (n.val - i1.val) (by scalar_tac) st tys out1 n i1 b hst ?_ rfl h
        refine push_mem hout ?_ hpush
        exact ⟨parse_cv_d_wf hst hr, Env.ind_caps_default_wf hic⟩
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::ind_block_types` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`): the `IndInfo`s the block's type formers contribute. -/
theorem ind_block_types_wf {st : frontend.export_c.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {out b : alloc.vec.Vec env.ConstantInfo} (hst : StateDWF st) (hout : ConstantInfosWF out)
    (h : frontend.export_c.ind_block_types st tys out = ok (.Ok b)) : ConstantInfosWF b := by
  rw [frontend.export_c.ind_block_types] at h
  exact ind_block_types_loop_wf _ st tys out _ _ b hst hout rfl h

/-- `export_c::ind_block_ctors` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`, the cited `cts.mapM`), as its loop. -/
private theorem ind_block_ctors_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (cts : alloc.vec.Vec frontend.scan_types.IndCtorRec)
      (out : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (b : alloc.vec.Vec env.ConstantInfo),
      StateDWF st → ConstantInfosWF out → n.val - i.val = N →
      frontend.export_c.ind_block_ctors_loop st cts out n i = ok (.Ok b) →
      ConstantInfosWF b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st cts out n i b hst hout hN h
    rw [frontend.export_c.ind_block_ctors_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, -, r, hr, h⟩ := h
      cases r with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        refine ih (n.val - i1.val) (by scalar_tac) st cts out1 n i1 b hst ?_ rfl h
        refine push_mem hout ?_ hpush
        exact parse_cv_d_wf hst hr
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::ind_block_ctors` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`): the `CtorInfo`s the block's constructors contribute. -/
theorem ind_block_ctors_wf {st : frontend.export_c.StateD}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {out b : alloc.vec.Vec env.ConstantInfo} (hst : StateDWF st) (hout : ConstantInfosWF out)
    (h : frontend.export_c.ind_block_ctors st cts out = ok (.Ok b)) : ConstantInfosWF b := by
  rw [frontend.export_c.ind_block_ctors] at h
  exact ind_block_ctors_loop_wf _ st cts out _ _ b hst hout rfl h

/-- `export_c::ind_block_recs` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`, the cited `rcs.mapM`), as its loop.  The one arm that also
reads recursor rules, through `parse_rules_d`. -/
private theorem ind_block_recs_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (rcs : alloc.vec.Vec frontend.scan_types.IndRecRec)
      (out : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (b : alloc.vec.Vec env.ConstantInfo),
      StateDWF st → ConstantInfosWF out → n.val - i.val = N →
      frontend.export_c.ind_block_recs_loop st rcs out n i = ok (.Ok b) →
      ConstantInfosWF b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st rcs out n i b hst hout hN h
    rw [frontend.export_c.ind_block_recs_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, -, r1, hr1, h⟩ := h
      cases r1 with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok rs =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r2, hr2, h⟩ := h
        cases r2 with
        | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
        | Ok cv =>
          simp only [bind_eq_ok_iff] at h
          obtain ⟨i1, -, i2, -, i3, -, i4, -, out1, hpush, i5, hi5, h⟩ := h
          have hi5v : i5.val = i.val + 1 := HashMap.uscalar_add_eq hi5
          refine ih (n.val - i5.val) (by scalar_tac) st rcs out1 n i5 b hst ?_ rfl h
          refine push_mem hout ?_ hpush
          exact ⟨parse_cv_d_wf hst hr2, parse_rules_d_wf hst hr1⟩
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::ind_block_recs` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`): the `RecInfo`s the block's recursors contribute. -/
theorem ind_block_recs_wf {st : frontend.export_c.StateD}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {out b : alloc.vec.Vec env.ConstantInfo} (hst : StateDWF st) (hout : ConstantInfosWF out)
    (h : frontend.export_c.ind_block_recs st rcs out = ok (.Ok b)) : ConstantInfosWF b := by
  rw [frontend.export_c.ind_block_recs] at h
  exact ind_block_recs_loop_wf _ st rcs out _ _ b hst hout rfl h

/-- `export_c::ind_block_of` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`, the cited `types ++ ctors ++ recs`): the block a validated
`#IND` line installs.  By `DeclarationWF`'s `.IndDecl` clause this conclusion
*is* `DeclarationWF (.IndDecl b n_pd)`. -/
theorem ind_block_of_wf {st : frontend.export_c.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec} {b : alloc.vec.Vec env.ConstantInfo}
    (hst : StateDWF st) (h : frontend.export_c.ind_block_of st tys cts rcs = ok (.Ok b)) :
    ConstantInfosWF b := by
  rw [frontend.export_c.ind_block_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
  | Ok b1 =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    cases r1 with
    | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
    | Ok b2 =>
      exact ind_block_recs_wf hst (ind_block_ctors_wf hst (ind_block_types_wf hst
        (by intro c hc; simp [alloc.vec.Vec.new] at hc) hr) hr1) h

/-! ## The projection-owner table

`registerProjOwners`: the export's own shape data, read back out of the parse
tables into `proj_rec`'s three record types, handed to
`proj_rec::proj_rec_owners`, and filed under every owner's type name. -/

/-- `export_c::proj_type_recs_of` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`, the cited `types` component), as its loop. -/
private theorem proj_type_recs_of_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out : alloc.vec.Vec frontend.proj_rec.ProjTypeRec) (n i : Std.Usize)
      (ts : alloc.vec.Vec frontend.proj_rec.ProjTypeRec),
      StateDWF st → (∀ t ∈ out.val, ProjTypeRecWF t) → n.val - i.val = N →
      frontend.export_c.proj_type_recs_of_loop st tys out n i = ok (.Ok ts) →
      ∀ t ∈ ts.val, ProjTypeRecWF t := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st tys out n i ts hst hout hN h
    rw [frontend.export_c.proj_type_recs_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨t, -, r, hr, h⟩ := h
      cases r with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        cases r1 with
        | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
        | Ok cs =>
          simp only [bind_eq_ok_iff] at h
          obtain ⟨n1, hn1, v2, hv2, e, he, out1, hpush, i1, hi1, h⟩ := h
          have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
          obtain ⟨hcvn, hcvl, hcvt⟩ := parse_cv_d_wf hst hr
          refine ih (n.val - i1.val) (by scalar_tac) st tys out1 n i1 ts hst ?_ rfl h
          refine push_mem hout ⟨?_, ?_, ?_, st_names_wf hst hr1⟩ hpush
          · rw [name_dup_refines hn1]; exact hcvn
          · rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv2)]; exact hcvl
          · rw [Expr.dup_eq he]; exact hcvt
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::proj_type_recs_of` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`). -/
theorem proj_type_recs_of_wf {st : frontend.export_c.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {ts : alloc.vec.Vec frontend.proj_rec.ProjTypeRec} (hst : StateDWF st)
    (h : frontend.export_c.proj_type_recs_of st tys = ok (.Ok ts)) :
    ∀ t ∈ ts.val, ProjTypeRecWF t := by
  rw [frontend.export_c.proj_type_recs_of] at h
  exact proj_type_recs_of_loop_wf _ st tys _ _ _ ts hst
    (by intro t ht; simp [alloc.vec.Vec.with_capacity] at ht) rfl h

/-- `export_c::proj_ctor_recs_of` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`, the cited `ctors` component), as its loop. -/
private theorem proj_ctor_recs_of_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (cts : alloc.vec.Vec frontend.scan_types.IndCtorRec)
      (out : alloc.vec.Vec frontend.proj_rec.ProjCtorRec) (n i : Std.Usize)
      (cs : alloc.vec.Vec frontend.proj_rec.ProjCtorRec),
      StateDWF st → (∀ c ∈ out.val, ProjCtorRecWF c) → n.val - i.val = N →
      frontend.export_c.proj_ctor_recs_of_loop st cts out n i = ok (.Ok cs) →
      ∀ c ∈ cs.val, ProjCtorRecWF c := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st cts out n i cs hst hout hN h
    rw [frontend.export_c.proj_ctor_recs_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, -, r, hr, h⟩ := h
      cases r with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, e, he, out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨hcvn, -, hcvt⟩ := parse_cv_d_wf hst hr
        refine ih (n.val - i1.val) (by scalar_tac) st cts out1 n i1 cs hst ?_ rfl h
        refine push_mem hout ⟨?_, ?_⟩ hpush
        · rw [name_dup_refines hn1]; exact hcvn
        · rw [Expr.dup_eq he]; exact hcvt
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::proj_ctor_recs_of` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`). -/
theorem proj_ctor_recs_of_wf {st : frontend.export_c.StateD}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {cs : alloc.vec.Vec frontend.proj_rec.ProjCtorRec} (hst : StateDWF st)
    (h : frontend.export_c.proj_ctor_recs_of st cts = ok (.Ok cs)) :
    ∀ c ∈ cs.val, ProjCtorRecWF c := by
  rw [frontend.export_c.proj_ctor_recs_of] at h
  exact proj_ctor_recs_of_loop_wf _ st cts _ _ _ cs hst
    (by intro c hc; simp [alloc.vec.Vec.with_capacity] at hc) rfl h

/-- `export_c::proj_rec_recs_of` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`, the cited `recs` component), as its loop. -/
private theorem proj_rec_recs_of_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (rcs : alloc.vec.Vec frontend.scan_types.IndRecRec)
      (out : alloc.vec.Vec frontend.proj_rec.ProjRecRec) (n i : Std.Usize)
      (rs : alloc.vec.Vec frontend.proj_rec.ProjRecRec),
      StateDWF st → (∀ r ∈ out.val, ProjRecRecWF r) → n.val - i.val = N →
      frontend.export_c.proj_rec_recs_of_loop st rcs out n i = ok (.Ok rs) →
      ∀ r ∈ rs.val, ProjRecRecWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st rcs out n i rs hst hout hN h
    rw [frontend.export_c.proj_rec_recs_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, -, r1, hr1, h⟩ := h
      cases r1 with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, v, hv, e, he, out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨hcvn, hcvl, hcvt⟩ := parse_cv_d_wf hst hr1
        refine ih (n.val - i1.val) (by scalar_tac) st rcs out1 n i1 rs hst ?_ rfl h
        refine push_mem hout ⟨?_, ?_, ?_⟩ hpush
        · rw [name_dup_refines hn1]; exact hcvn
        · rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv)]; exact hcvl
        · rw [Expr.dup_eq he]; exact hcvt
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::proj_rec_recs_of` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`). -/
theorem proj_rec_recs_of_wf {st : frontend.export_c.StateD}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {rs : alloc.vec.Vec frontend.proj_rec.ProjRecRec} (hst : StateDWF st)
    (h : frontend.export_c.proj_rec_recs_of st rcs = ok (.Ok rs)) :
    ∀ r ∈ rs.val, ProjRecRecWF r := by
  rw [frontend.export_c.proj_rec_recs_of] at h
  exact proj_rec_recs_of_loop_wf _ st rcs _ _ _ rs hst
    (by intro r hr; simp [alloc.vec.Vec.with_capacity] at hr) rfl h

/-- `export_c::proj_rec_owner_dup` (no con-leche line: the record copy the Lean
model needs because `insert_proj_owners` walks a borrowed `Vec`).  Every field
is copied by the kernel's own `_dup`, each of which is the identity. -/
private theorem proj_rec_owner_dup_wf {o o' : frontend.proj_rec.ProjRecOwner}
    (ho : ProjRecOwnerWF o) (h : frontend.export_c.proj_rec_owner_dup o = ok o') :
    ProjRecOwnerWF o' := by
  rw [frontend.export_c.proj_rec_owner_dup] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨v, hv, v1, hv1, e, he, rfl⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ho
  refine ⟨h1, ?_, h3, h4, ?_, ?_⟩
  · rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv)]; exact h2
  · rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv1)]; exact h5
  · rw [Expr.dup_eq he]; exact h6

/-- `export_c::insert_proj_owners` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`, the cited `owners.foldl` into `projOwners`), as its
loop.  The only field it writes is `proj_owners`. -/
private theorem insert_proj_owners_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD)
      (owners : alloc.vec.Vec frontend.proj_rec.ProjRecOwner) (n i : Std.Usize)
      (st' : frontend.export_c.StateD),
      StateDWF st → (∀ o ∈ owners.val, ProjRecOwnerWF o) → n.val - i.val = N →
      frontend.export_c.insert_proj_owners_loop st owners n i = ok st' → StateDWF st' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st owners n i st' hst ho hN h
    rw [frontend.export_c.insert_proj_owners_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨pro, hpro, n1, hn1, pro1, hpro1, p, hins, h⟩ := h
      obtain ⟨old, hm⟩ := p
      -- a pair bind leaves a `Function.uncurry`, which `uncurry_apply_pair` peels
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      refine ih (n.val - i1.val) (by scalar_tac) _ owners n i1 st' ?_ ho rfl h
      exact ⟨hst.names, hst.levels, hst.exprs, hst.decls,
        map_insert_wf hst.proj_owners
          (proj_rec_owner_dup_wf (ho _ (vec_mem hpro)) hpro1) hins,
        hst.proj_levels⟩
    · exact Result.ok_injective h ▸ hst

/-- `export_c::insert_proj_owners` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`). -/
theorem insert_proj_owners_wf {st st' : frontend.export_c.StateD}
    {owners : alloc.vec.Vec frontend.proj_rec.ProjRecOwner} (hst : StateDWF st)
    (ho : ∀ o ∈ owners.val, ProjRecOwnerWF o)
    (h : frontend.export_c.insert_proj_owners st owners = ok st') : StateDWF st' := by
  rw [frontend.export_c.insert_proj_owners] at h
  exact insert_proj_owners_loop_wf _ st owners _ _ st' hst ho rfl h

/-- `export_c::register_proj_owners` (`ConLeche/Frontend/ExportC.lean:377-396`
`registerProjOwners`): the whole owner table, from the block's constants and
the parse's three record lists. -/
theorem register_proj_owners_wf {st st' : frontend.export_c.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {block : alloc.vec.Vec env.ConstantInfo} (hst : StateDWF st) (hb : ConstantInfosWF block)
    (h : frontend.export_c.register_proj_owners st tys cts rcs block = ok (.Ok (), st')) :
    StateDWF st' := by
  rw [frontend.export_c.register_proj_owners] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
  | Ok ts =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    cases r1 with
    | Err e => simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
    | Ok cs =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      cases r2 with
      | Err e => simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
      | Ok rs =>
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨owners, howners, st1, hst1, -, rfl⟩ := h
        refine insert_proj_owners_wf hst ?_ hst1
        refine proj_rec_owners_wf hb ?_ ?_ ?_ howners
        · intro t ht; rw [deref_val] at ht; exact proj_type_recs_of_wf hst hr t ht
        · intro c hc; rw [deref_val] at hc; exact proj_ctor_recs_of_wf hst hr1 c hc
        · intro r hr'; rw [deref_val] at hr'; exact proj_rec_recs_of_wf hst hr2 r hr'

/-! ## The in-process modeller's generated records -/

/-- `export_c::note_proj_iota` (`ConLeche/Frontend/ExportC.lean:304-317`
`noteProjIota`).  The **only** write to `proj_levels` in the whole parse: an
artifact `T._model.proj_i.iota`'s `Eq` level, read out of the theorem's own
type by `proj_rec::proj_iota_level`. -/
theorem note_proj_iota_wf {st st' : frontend.export_c.StateD} {cvp : env.ConstantVal}
    (hst : StateDWF st) (hcv : ConstantValWF cvp)
    (h : frontend.export_c.note_proj_iota st cvp = ok st') : StateDWF st' := by
  rw [frontend.export_c.note_proj_iota] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, -, h⟩ := h
  split at h
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    cases o with
    | none => exact Result.ok_injective h ▸ hst
    | some l =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n, hn, p, hins, h⟩ := h
      obtain ⟨old, hm⟩ := p
      simp only [uncurry_apply_pair] at h
      rw [← Result.ok_injective h]
      exact ⟨hst.names, hst.levels, hst.exprs, hst.decls, hst.proj_owners,
        map_insert_wf hst.proj_levels (proj_iota_level_wf hcv.2.2 ho) hins⟩
  · exact Result.ok_injective h ▸ hst

/-- `export_c::push_gen_d` (`ConLeche/Frontend/ExportC.lean:319-326`
`pushGenD`): one record the modeller generated, pushed, with the
projection-iota registration on the `ThmDecl` arm. -/
theorem push_gen_d_wf {st st' : frontend.export_c.StateD} {d : env.Declaration}
    (hst : StateDWF st) (hd : DeclarationWF d)
    (h : frontend.export_c.push_gen_d st d = ok st') : StateDWF st' := by
  rw [frontend.export_c.push_gen_d.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨st1, hst1, h⟩ := h
  refine push_decl_wf ?_ hd h
  cases d with
  | ThmDecl cv v =>
    simp only [bind_eq_ok_iff] at hst1
    obtain ⟨cv2, hcv2, hst1⟩ := hst1
    rw [Env.constant_val_dup_refines hcv2] at hst1
    exact note_proj_iota_wf hst hd.1 hst1
  | AxiomDecl cv => exact Result.ok_injective hst1 ▸ hst
  | DefnDecl cv v hint => exact Result.ok_injective hst1 ▸ hst
  | OpaqueDecl cv v => exact Result.ok_injective hst1 ▸ hst
  | BasisDecl k => exact Result.ok_injective hst1 ▸ hst
  | IndDecl bl n => exact Result.ok_injective hst1 ▸ hst
  | QuotDecl k cv => exact Result.ok_injective hst1 ▸ hst

/-- `export_c::note_gen_names` (`ConLeche/Frontend/ExportC.lean:328-336`
`noteGen`): booking a generated record under the block that models it.  It
bumps `gen_records` and inserts into `gen_owner`; both are untracked (the
module note), so the six clauses pass through unchanged. -/
theorem note_gen_names_wf {st st' : frontend.export_c.StateD}
    {names : alloc.vec.Vec name.Name} {t0 : name.Name} (hst : StateDWF st)
    (h : frontend.export_c.note_gen_names st names t0 = ok st') : StateDWF st' := by
  rw [frontend.export_c.note_gen_names] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨i, -, hm, -, rfl⟩ := h
  exact stateDWF_same hst rfl rfl rfl rfl rfl rfl

/-- `export_c::note_gen` (`ConLeche/Frontend/ExportC.lean:328-336` `noteGen`):
`note_gen_names` at the record's own names.  Nothing it reads or writes is
tracked. -/
theorem note_gen_wf {st st' : frontend.export_c.StateD} {d : env.Declaration}
    {t0 : name.Name} (hst : StateDWF st)
    (h : frontend.export_c.note_gen st d t0 = ok st') : StateDWF st' := by
  rw [frontend.export_c.note_gen] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, -, h⟩ := h
  exact note_gen_names_wf hst h

/-- `export_c::constant_infos_dup` (no con-leche line), as its loop: the block
copy `declaration_dup`'s `.IndDecl` arm needs.  `env::constant_info_dup` is
the identity (`Refine/Env.lean`), so the invariant just transfers. -/
private theorem constant_infos_dup_loop_wf (N : Nat) :
    ∀ (bl out : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (v : alloc.vec.Vec env.ConstantInfo),
      ConstantInfosWF bl → ConstantInfosWF out → n.val - i.val = N →
      frontend.export_c.constant_infos_dup_loop bl out n i = ok v → ConstantInfosWF v := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bl out n i v hbl hout hN h
    rw [frontend.export_c.constant_infos_dup_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ci, hci, ci1, hci1, out1, hpush, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      refine ih (n.val - i1.val) (by scalar_tac) bl out1 n i1 v hbl ?_ rfl h
      refine push_mem hout ?_ hpush
      rw [Env.constant_info_dup_refines hci1]
      exact hbl _ (vec_mem hci)
    · exact Result.ok_injective h ▸ hout

/-- `export_c::declaration_dup` (no con-leche line: the record copy
`push_gen_list` needs because it walks a borrowed list).  Every field is
copied by the kernel's own `_dup`, each of which is the identity. -/
private theorem declaration_dup_wf {d d' : env.Declaration} (hd : DeclarationWF d)
    (h : frontend.export_c.declaration_dup d = ok d') : DeclarationWF d' := by
  rw [frontend.export_c.declaration_dup.eq_def] at h
  cases d with
  | AxiomDecl cv =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv1, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv1]; exact hd
  | DefnDecl cv v hint =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv1, e, he, rh, -, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv1, Expr.dup_eq he]; exact hd
  | ThmDecl cv v =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv1, e, he, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv1, Expr.dup_eq he]; exact hd
  | OpaqueDecl cv v =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv1, hcv1, e, he, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv1, Expr.dup_eq he]; exact hd
  | BasisDecl k =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨bk, -, rfl⟩ := h
    trivial
  | IndDecl bl n =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h
    rw [frontend.export_c.constant_infos_dup] at hv
    exact constant_infos_dup_loop_wf _ bl _ _ _ v hd
      (by intro c hc; simp [alloc.vec.Vec.with_capacity] at hc) rfl hv
  | QuotDecl k cv =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨qk, -, cv1, hcv1, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv1]; exact hd

/-- `export_c::push_gen_list` (`ConLeche/Frontend/ExportC.lean:398-404`
`pushGenList`), as its loop. -/
private theorem push_gen_list_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (gen : alloc.vec.Vec env.Declaration)
      (t0 : name.Name) (n i : Std.Usize) (st' : frontend.export_c.StateD),
      StateDWF st → (∀ d ∈ gen.val, DeclarationWF d) → n.val - i.val = N →
      frontend.export_c.push_gen_list_loop st gen t0 n i = ok st' → StateDWF st' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st gen t0 n i st' hst hgen hN h
    rw [frontend.export_c.push_gen_list_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨d, hd, names, -, d1, hd1, st1, hst1, st2, hst2, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      refine ih (n.val - i1.val) (by scalar_tac) st2 gen t0 n i1 st' ?_ hgen rfl h
      exact note_gen_names_wf
        (push_gen_d_wf hst (declaration_dup_wf (hgen _ (vec_mem hd)) hd1) hst1) hst2
    · exact Result.ok_injective h ▸ hst

/-- `export_c::push_gen_list` (`ConLeche/Frontend/ExportC.lean:398-404`
`pushGenList`): the whole family the modeller generated for one block, each
record pushed and booked as a declaration of the fold. -/
theorem push_gen_list_wf {st st' : frontend.export_c.StateD}
    {gen : alloc.vec.Vec env.Declaration} {t0 : name.Name} (hst : StateDWF st)
    (hgen : ∀ d ∈ gen.val, DeclarationWF d)
    (h : frontend.export_c.push_gen_list st gen t0 = ok st') : StateDWF st' := by
  rw [frontend.export_c.push_gen_list] at h
  exact push_gen_list_loop_wf _ st gen t0 _ _ st' hst hgen rfl h

/-- `export_c::note_ind_blocks` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`, the cited `b.types.foldl`), as its loop.  It writes
`ind_blocks`, which only the modeller reads and `StateDWF` does not track (the
module note). -/
private theorem note_ind_blocks_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD)
      (b : alloc.sync.Arc frontend.in_model_rec.BlockRec) (n i : Std.Usize)
      (st' : frontend.export_c.StateD),
      StateDWF st → n.val - i.val = N →
      frontend.export_c.note_ind_blocks_loop st b n i = ok st' → StateDWF st' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st b n i st' hst hN h
    rw [frontend.export_c.note_ind_blocks_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨br, -, itr, -, n1, -, a, -, p, -, h⟩ := h
      obtain ⟨old, hm⟩ := p
      -- a pair bind leaves a `Function.uncurry`, which `uncurry_apply_pair` peels
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      refine ih (n.val - i1.val) (by scalar_tac) _ b n i1 st' ?_ rfl h
      exact stateDWF_same hst rfl rfl rfl rfl rfl rfl
    · exact Result.ok_injective h ▸ hst

/-- `export_c::note_ind_blocks` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`). -/
theorem note_ind_blocks_wf {st st' : frontend.export_c.StateD}
    {b : alloc.sync.Arc frontend.in_model_rec.BlockRec} (hst : StateDWF st)
    (h : frontend.export_c.note_ind_blocks st b = ok st') : StateDWF st' := by
  rw [frontend.export_c.note_ind_blocks] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨br, -, h⟩ := h
  exact note_ind_blocks_loop_wf _ st b _ _ st' hst rfl h

/-! ## The two entry points -/

/-- `export_c::install_gen` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`, **the in-process modeller**).  This is the one place
`ModellerWF` is consumed: `hgen` turns the modeller's `generate` into
`∀ d ∈ gen.val, DeclarationWF d`, and `push_gen_list_wf` carries it into the
state.  The census arm pushes the block bare, which needs exactly `hb`; the
non-census decline arm returns `.Err` and so cannot reach the conclusion. -/
theorem install_gen_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {block : alloc.vec.Vec env.ConstantInfo}
    {n_pd : Std.U64} {t0 : name.Name} {b : alloc.sync.Arc frontend.in_model_rec.BlockRec}
    (hgen : ModellerWF inst g) (hst : StateDWF st) (hb : ConstantInfosWF block)
    (h : frontend.export_c.install_gen inst g st block n_pd t0 b = ok (.Ok (), st')) :
    StateDWF st' := by
  rw [frontend.export_c.install_gen] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ctx, -, br, -, gen, hg, h⟩ := h
  cases gen with
  | Ok gen2 =>
    simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨st1, hst1, n, -, v, -, st2, hst2, -, rfl⟩ := h
    have h1 : StateDWF st1 := push_gen_list_wf hst (hgen _ _ _ hg) hst1
    refine push_decl_wf ?_ ?_ hst2
    · exact stateDWF_same h1 rfl rfl rfl rfl rfl rfl
    · exact hb
  | Err why =>
    -- `simp only []` just iota-reduces the `match` `cases` left behind
    simp only [] at h
    split at h
    · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨n, -, v, -, st1, hst1, -, rfl⟩ := h
      refine push_decl_wf ?_ ?_ hst1
      · exact stateDWF_same hst rfl rfl rfl rfl rfl rfl
      · exact hb
    · -- the decline is an `.Err`: the hypothesis cannot hold
      simp only [frontend.export_c.declined, bind_tc_ok, bind_eq_ok_iff, ok.injEq,
        Prod.mk.injEq, reduceCtorEq, false_and, and_false, exists_const] at h

/-- `export_c::install_ind_d` (`ConLeche/Frontend/ExportC.lean:560-623`
`installIndD`): **an inductive record, installed**.  The block's constants,
the projection-owner table, the block record for the modeller, then the
modelled or the bare push.  Every state change a validated `#IND` line makes
is here; `validate_ind_d`, which runs before it and produces only indices and
bools, contributes nothing (the module note). -/
theorem install_ind_d_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec} {n_pd : Std.U64}
    (hgen : ModellerWF inst g) (hst : StateDWF st)
    (h : frontend.export_c.install_ind_d inst g st tys cts rcs n_pd = ok (.Ok (), st')) :
    StateDWF st' := by
  rw [frontend.export_c.install_ind_d] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
  | Ok v =>
    have hb : ConstantInfosWF v := ind_block_of_wf hst hr
    simp only [bind_eq_ok_iff] at h
    obtain ⟨p, hp, h⟩ := h
    obtain ⟨r1, st1⟩ := p
    simp only [uncurry_apply_pair] at h
    cases r1 with
    | Err e => simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
    | Ok u =>
      have hst1 : StateDWF st1 := by
        cases u; exact register_proj_owners_wf hst hb hp
      simp only [bind_eq_ok_iff] at h
      obtain ⟨t0, -, r2, hr2, h⟩ := h
      cases r2 with
      | Err e => simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
      | Ok v1 =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨b, -, st2, hst2, h⟩ := h
        have hst2' : StateDWF st2 := note_ind_blocks_wf hst1 hst2
        split at h
        · simp only [bind_eq_ok_iff] at h
          obtain ⟨br, -, b1, -, h⟩ := h
          split at h
          · exact install_gen_wf hgen hst2' hb h
          · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨st3, hst3, -, rfl⟩ := h
            refine push_decl_wf hst2' ?_ hst3
            exact hb
        · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨st3, hst3, -, rfl⟩ := h
          refine push_decl_wf hst2' ?_ hst3
          exact hb

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/-- info: 'ConRon.Refine.Frontend.install_ind_d_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms install_ind_d_wf

end ConRon.Refine.Frontend
