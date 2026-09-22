/-
`ConRon.Refine.Frontend.Prepare` — the **tail of the parse pipeline**
(task #85, phase 1).

After `export_c::parse_chunks` has produced a `Vec<Declaration>`, two passes
run below the verified fold: `prepare::prepare_prelude` puts the built-in
prelude's records in front of the stream
(`crates/con-ron-core/src/frontend/prepare.rs`) and
`nat_op_ground::hoist_nat_op_ground` moves each pinned `Nat` operation's
stream-certified ground ahead of it
(`crates/con-ron-core/src/frontend/nat_op_ground.rs`).

**Neither pass builds a term.**  Both only *permute and copy*: every record
either of them stores is `nat_op_ground::declaration_dup` of a record it was
given, and `declaration_dup` is the identity in the model — a `Name`/`Expr`
copy is an `Arc::clone` and a `Vec` copy is the `Vec` (DESIGN.md §3.2, and
`Refine/Env.lean`'s `*_dup` family, which this file reuses wholesale).  So the
whole content of the file is

    ∀ d ∈ ds.val, DeclarationWF d  →  ∀ d ∈ out.val, DeclarationWF d

carried through six loops, and `declaration_dup_refines` — the copy *is* the
record — is what makes each of the six one line of real work.

**The index computations carry no clause, because they produce indices and
names, not terms.**  `hoist_name_index`, `hoist_targets*`, `hoist_close*`,
`hoist_push_dep*`, `hoist_moved_idxs`, `hoist_order*`, `target_done`,
`target_is`, `idx_get`, `used_consts_go*`, `decl_used_consts`,
`block_used_consts`, `is_nat_op_record`, `stack_push_*` and
`hoist_moved_names` on the hoist side, and `front_of*`, `pick_idx*`,
`no_picks*`, `prelude_key` and `declares` on the prelude side, compute the
*plan* — a permutation, a mask, and the driver's receipt of names the stream
already carries.  `hoist_nat_op_ground`'s second component is such a receipt:
only its first component reaches the fold, which is why the capstone below
says nothing about `r.2`.

**The built-in prelude is not named here.**  `frontend.prelude.builtin_prelude_e`
parses an embedded string constant with `export_c::parse_bytes`, which
`AENEAS_FINDINGS.md` §3.8 measured as out of reach in the kernel at that size;
the tier is therefore stated *parametrically* in the prelude's records
(`PreludeIxWF`), and `parse_bytes` belongs to `Refine/Frontend/Readers.lean`.

## `sorry` count in this file: 0
-/
import ConRon.RefineOld.Frontend.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Plumbing

The three facts every loop below needs: a push extends a "every entry is well
formed" invariant, a `Vec` read hands back one of the `Vec`'s entries, and a
`Vec` built by `with_capacity` is empty. -/

/-- A push extends a "every entry satisfies `P`" invariant by the pushed
element. -/
private theorem push_wf {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  rw [vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- What a `Vec` read hands back is one of the `Vec`'s entries.  Unlike
`Refine/PinsWF.lean`'s copy this one needs no range hypothesis: the read's own
success supplies it. -/
private theorem vec_index_mem {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    x ∈ v.val := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    rw [← Result.ok_injective h]
    exact List.mem_of_getElem? hi

/-- A `Vec::with_capacity` holds nothing. -/
private theorem with_capacity_wf {α : Type} {P : α → Prop} {n : Std.Usize} :
    ∀ y ∈ (alloc.vec.Vec.with_capacity α n).val, P y := by
  intro y hy
  simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at hy

/-! ## The copy

`nat_op_ground::declaration_dup` copies a parsed record field by field through
`kernel::env`'s own `*_dup`s, each of which `Refine/Env.lean` has already
proved the identity.  So the copy is the record, and well-formedness comes
along for free. -/

/-- `env::quot_kind_dup` is the identity on a five-constructor enum.  It is the
one `*_dup` of `kernel::env` that `Refine/Env.lean` never needed. -/
theorem quot_kind_dup_val (k : env.QuotKind) : env.quot_kind_dup k = ok k := by
  cases k <;> simp [env.quot_kind_dup]

/-- `nat_op_ground::block_copy` appends the rest of the block's members to its
accumulator: the index recursion behind `declaration_dup`'s `IndDecl` arm
(`Refine/Env.lean`'s `constant_infos_copy_from_val`, at `constant_info_dup`). -/
theorem block_copy_val (block : alloc.vec.Vec env.ConstantInfo) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec env.ConstantInfo),
      block.length - i.val ≤ k →
      frontend.nat_op_ground.block_copy block i out = ok v →
      v.val = out.val ++ block.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [frontend.nat_op_ground.block_copy.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
  | succ k ih =>
    intro i out v hk h
    rw [frontend.nat_op_ground.block_copy.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ block.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
      have hlt : i.val < block.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := block.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨c1, hc1, out1, hout1, h⟩ := h
      rw [Env.constant_info_dup_refines hc1] at hout1
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1, hwv,
        List.drop_eq_getElem_cons hlt]
      simp

/-- `nat_op_ground::block_copy` at `declaration_dup`'s own call: the
identity. -/
theorem block_copy_refines {block v : alloc.vec.Vec env.ConstantInfo}
    (h : frontend.nat_op_ground.block_copy block 0#usize
          (alloc.vec.Vec.new env.ConstantInfo) = ok v) : v = block :=
  alloc.vec.Vec.ext _ _ (by
    simpa using block_copy_val block block.length 0#usize _ v (by scalar_tac) h)

/-- **`nat_op_ground::declaration_dup` is the identity** on a parsed record:
every field goes through a `kernel::env` `*_dup` that `Refine/Env.lean` has
already read as one. -/
theorem declaration_dup_refines {d d' : env.Declaration}
    (h : frontend.nat_op_ground.declaration_dup d = ok d') : d' = d := by
  cases d with
  | AxiomDecl cv =>
    simp only [frontend.nat_op_ground.declaration_dup, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨cv1, hcv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv]
  | DefnDecl cv v hint =>
    simp only [frontend.nat_op_ground.declaration_dup, bind_eq_ok_iff,
      Env.expr_dup_val, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨cv1, hcv, h1, hh, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv, Env.reducibility_hint_dup_refines hh]
  | ThmDecl cv v =>
    simp only [frontend.nat_op_ground.declaration_dup, bind_eq_ok_iff,
      Env.expr_dup_val, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨cv1, hcv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv]
  | OpaqueDecl cv v =>
    simp only [frontend.nat_op_ground.declaration_dup, bind_eq_ok_iff,
      Env.expr_dup_val, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨cv1, hcv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv]
  | BasisDecl k =>
    simp only [frontend.nat_op_ground.declaration_dup, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨k1, hk, rfl⟩ := h
    rw [Env.basis_kind_dup_refines hk]
  | IndDecl block n =>
    simp only [frontend.nat_op_ground.declaration_dup, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨b1, hb, rfl⟩ := h
    rw [block_copy_refines hb]
  | QuotDecl k cv =>
    simp only [frontend.nat_op_ground.declaration_dup, bind_eq_ok_iff,
      quot_kind_dup_val, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨cv1, hcv, rfl⟩ := h
    rw [Env.constant_val_dup_refines hcv]

/-- **`nat_op_ground::declaration_dup` preserves well-formedness** — trivially,
being the identity.  This is the one fact the two passes below need of it. -/
theorem declaration_dup_wf {d d' : env.Declaration} (hd : DeclarationWF d)
    (h : frontend.nat_op_ground.declaration_dup d = ok d') : DeclarationWF d' := by
  rw [declaration_dup_refines h]; exact hd

/-! ## The hoist

`nat_op_ground::hoist_nat_op_ground` computes a permutation of the stream's
positions and applies it.  Only the application touches records, and it does so
in one loop: `hoist_reorder` pushes `declaration_dup (ds[order[i]])`.  The
permutation itself (`hoist_targets` and everything under it, `hoist_moved_idxs`,
`hoist_order`) and the receipt (`hoist_moved_names`) produce `u64`s and `Name`s
that were already in `ds`, so neither carries a clause — the module note above
lists them. -/

/-- `nat_op_ground::hoist_reorder`'s loop: everything it pushes is
`declaration_dup` of an entry of `ds`, hence — `declaration_dup` being the
identity — an entry of `ds`.  `partial_fixpoint` gives no recursor, so the
recursion is carried by the `while`'s own decreasing measure `n - i`. -/
private theorem hoist_reorder_loop_wf {ds : alloc.vec.Vec env.Declaration}
    {order : alloc.vec.Vec Std.U64} (hds : ∀ d ∈ ds.val, DeclarationWF d) :
    ∀ k : Nat, ∀ (n i : Std.Usize) (out v : alloc.vec.Vec env.Declaration),
      n.val - i.val ≤ k → (∀ d ∈ out.val, DeclarationWF d) →
      frontend.nat_op_ground.hoist_reorder_loop ds order n out i = ok v →
      ∀ d ∈ v.val, DeclarationWF d := by
  intro k
  induction k with
  | zero =>
    intro n i out v hk hout h
    rw [frontend.nat_op_ground.hoist_reorder_loop.eq_def] at h
    rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
    rw [← h]; exact hout
  | succ k ih =>
    intro n i out v hk hout h
    rw [frontend.nat_op_ground.hoist_reorder_loop.eq_def] at h
    by_cases hi : i.val < n.val
    · rw [if_pos (show i < n by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, -, i2, -, d, hd, d1, hd1, out1, hout1, i3, hi3, h⟩ := h
      have hi3v : i3.val = i.val + 1 := by have := Nat.uadd_val hi3; simpa using this
      refine ih n i3 out1 v (by omega) ?_ h
      exact push_wf hout (declaration_dup_wf (hds _ (vec_index_mem hd)) hd1) hout1
    · rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
      rw [← h]; exact hout

/-- **`nat_op_ground::hoist_reorder` preserves well-formedness.**  The order
vector is arbitrary: an out-of-range entry makes the `Vec` read fail, so the
port produces nothing to be well formed. -/
theorem hoist_reorder_wf {ds ds' : alloc.vec.Vec env.Declaration}
    {order : alloc.vec.Vec Std.U64} (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.nat_op_ground.hoist_reorder ds order = ok ds') :
    ∀ d ∈ ds'.val, DeclarationWF d := by
  rw [frontend.nat_op_ground.hoist_reorder] at h
  exact hoist_reorder_loop_wf hds order.length _ 0#usize _ ds'
    (by scalar_tac) with_capacity_wf h

/-- `ConLeche/Frontend/NatOpGround.lean:138-162` — **`nat_op_ground::apply_hoist`
preserves well-formedness** of the records.  Its second component is the
driver's receipt (`hoist_moved_names`), a list of names already in `ds`; the
fold never sees it. -/
theorem apply_hoist_wf {ds : alloc.vec.Vec env.Declaration}
    {target : ron.hashmap.HashMap Std.U64 Std.U64}
    {r : (alloc.vec.Vec env.Declaration) × (alloc.vec.Vec name.Name)}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.nat_op_ground.apply_hoist ds target = ok r) :
    ∀ d ∈ r.1.val, DeclarationWF d := by
  rw [frontend.nat_op_ground.apply_hoist] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨moved, -, order, -, out, hout, names, -, hr⟩ := h
  subst hr
  exact hoist_reorder_wf hds hout

/-- `ConLeche/Frontend/NatOpGround.lean:164-169` — **the hoist preserves
well-formedness.**  Either the target map is empty and the vector comes back
untouched, or `apply_hoist` rebuilds it out of copies of its own records. -/
theorem hoist_nat_op_ground_wf {ds : alloc.vec.Vec env.Declaration}
    {r : (alloc.vec.Vec env.Declaration) × (alloc.vec.Vec name.Name)}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.nat_op_ground.hoist_nat_op_ground ds = ok r) :
    ∀ d ∈ r.1.val, DeclarationWF d := by
  rw [frontend.nat_op_ground.hoist_nat_op_ground] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨target, -, i, -, h⟩ := h
  split at h
  · have hr := Result.ok_injective h; subst hr; exact hds
  · exact apply_hoist_wf hds h

/-! ## The prelude front

`prepare::prepare_prelude` computes a *plan* — for each prelude record, the
index in the stream of the stream's own copy of it, or `ds.len()`, plus the
mask of the records so spoken for (`front_of`, `pick_idx`, `no_picks`,
`prelude_key`, `declares`) — and then materialises the prepared list in one
pass.  Only the second half touches records, and again at one
`nat_op_ground::declaration_dup` per record, so the plan carries no clause. -/

/-- `ConLeche/Frontend/Prepare.lean:83-88` — `prepare::PreludeIx`: the built-in
prelude's records, all well formed.  A one-field record, so a one-clause
predicate. -/
def PreludeIxWF (pre : frontend.prepare.PreludeIx) : Prop :=
  ∀ d ∈ pre.decls.val, DeclarationWF d

/-- `ConLeche/Frontend/Prepare.lean:126-135` — `prepare::prepared_front`'s
loop: each slot is `declaration_dup` of an entry of `ds` (where the plan found
the stream's own copy) or of `ps` (where it did not). -/
private theorem prepared_front_loop_wf {ps ds : alloc.vec.Vec env.Declaration}
    {picks : alloc.vec.Vec Std.Usize}
    (hps : ∀ d ∈ ps.val, DeclarationWF d) (hds : ∀ d ∈ ds.val, DeclarationWF d) :
    ∀ k : Nat, ∀ (n np j : Std.Usize) (out v : alloc.vec.Vec env.Declaration),
      np.val - j.val ≤ k → (∀ d ∈ out.val, DeclarationWF d) →
      frontend.prepare.prepared_front_loop ps ds picks out n np j = ok v →
      ∀ d ∈ v.val, DeclarationWF d := by
  intro k
  induction k with
  | zero =>
    intro n np j out v hk hout h
    rw [frontend.prepare.prepared_front_loop.eq_def] at h
    rw [if_neg (show ¬ j < np by scalar_tac), Result.ok.injEq] at h
    rw [← h]; exact hout
  | succ k ih =>
    intro n np j out v hk hout h
    rw [frontend.prepare.prepared_front_loop.eq_def] at h
    by_cases hj : j.val < np.val
    · rw [if_pos (show j < np by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨kk, -, out1, hout1, j1, hj1, h⟩ := h
      have hj1v : j1.val = j.val + 1 := by have := Nat.uadd_val hj1; simpa using this
      refine ih n np j1 out1 v (by omega) ?_ h
      split at hout1
      · simp only [bind_eq_ok_iff] at hout1
        obtain ⟨d, hd, d1, hd1, hpush⟩ := hout1
        exact push_wf hout (declaration_dup_wf (hds _ (vec_index_mem hd)) hd1) hpush
      · simp only [bind_eq_ok_iff] at hout1
        obtain ⟨d, hd, d1, hd1, hpush⟩ := hout1
        exact push_wf hout (declaration_dup_wf (hps _ (vec_index_mem hd)) hd1) hpush
    · rw [if_neg (show ¬ j < np by scalar_tac), Result.ok.injEq] at h
      rw [← h]; exact hout

/-- `ConLeche/Frontend/Prepare.lean:126-135` — **`prepare::prepared_front`
preserves well-formedness**: the front of the prepared list. -/
theorem prepared_front_wf {ps ds out v : alloc.vec.Vec env.Declaration}
    {picks : alloc.vec.Vec Std.Usize}
    (hps : ∀ d ∈ ps.val, DeclarationWF d) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (hout : ∀ d ∈ out.val, DeclarationWF d)
    (h : frontend.prepare.prepared_front out ps ds picks = ok v) :
    ∀ d ∈ v.val, DeclarationWF d := by
  rw [frontend.prepare.prepared_front] at h
  exact prepared_front_loop_wf hps hds ps.length _ _ 0#usize _ v
    (by scalar_tac) hout h

/-- `ConLeche/Frontend/Prepare.lean:159-163` — `prepare::prepared_rest`'s loop:
the stream's records the mask does not carry, each `declaration_dup` of an
entry of `ds`. -/
private theorem prepared_rest_loop_wf {ds : alloc.vec.Vec env.Declaration}
    {picked : alloc.vec.Vec Bool} (hds : ∀ d ∈ ds.val, DeclarationWF d) :
    ∀ k : Nat, ∀ (n i : Std.Usize) (out v : alloc.vec.Vec env.Declaration),
      n.val - i.val ≤ k → (∀ d ∈ out.val, DeclarationWF d) →
      frontend.prepare.prepared_rest_loop ds picked out n i = ok v →
      ∀ d ∈ v.val, DeclarationWF d := by
  intro k
  induction k with
  | zero =>
    intro n i out v hk hout h
    rw [frontend.prepare.prepared_rest_loop.eq_def] at h
    rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
    rw [← h]; exact hout
  | succ k ih =>
    intro n i out v hk hout h
    rw [frontend.prepare.prepared_rest_loop.eq_def] at h
    by_cases hi : i.val < n.val
    · rw [if_pos (show i < n by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, -, out1, hout1, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
      refine ih n i1 out1 v (by omega) ?_ h
      split at hout1
      · rw [← Result.ok_injective hout1]; exact hout
      · simp only [bind_eq_ok_iff] at hout1
        obtain ⟨d, hd, d1, hd1, hpush⟩ := hout1
        exact push_wf hout (declaration_dup_wf (hds _ (vec_index_mem hd)) hd1) hpush
    · rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
      rw [← h]; exact hout

/-- `ConLeche/Frontend/Prepare.lean:159-163` — **`prepare::prepared_rest`
preserves well-formedness**: the prepared list's second half. -/
theorem prepared_rest_wf {ds out v : alloc.vec.Vec env.Declaration}
    {picked : alloc.vec.Vec Bool} (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (hout : ∀ d ∈ out.val, DeclarationWF d)
    (h : frontend.prepare.prepared_rest out ds picked = ok v) :
    ∀ d ∈ v.val, DeclarationWF d := by
  rw [frontend.prepare.prepared_rest] at h
  exact prepared_rest_loop_wf hds ds.length _ 0#usize _ v (by scalar_tac) hout h

/-- `ConLeche/Frontend/Prepare.lean:126-135` — **`prepare::prepared_stream`
preserves well-formedness**: the front, then the rest, from a
`with_capacity` accumulator that holds nothing. -/
theorem prepared_stream_wf {ps ds v : alloc.vec.Vec env.Declaration}
    {picks : alloc.vec.Vec Std.Usize} {picked : alloc.vec.Vec Bool}
    (hps : ∀ d ∈ ps.val, DeclarationWF d) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.prepare.prepared_stream ps ds picks picked = ok v) :
    ∀ d ∈ v.val, DeclarationWF d := by
  rw [frontend.prepare.prepared_stream] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨cap, -, front, hfront, h⟩ := h
  exact prepared_rest_wf hds (prepared_front_wf hps hds with_capacity_wf hfront) h

/-- `ConLeche/Frontend/Prepare.lean:159-163` — **`prepare::prepare_d` preserves
well-formedness** of the prepared records.  Its other two fields are the
driver's receipts: a count, and the names of the records the hoist moved. -/
theorem prepare_d_wf {pre : frontend.prepare.PreludeIx}
    {ds : alloc.vec.Vec env.Declaration} {p : frontend.prepare.Prepared}
    (hpre : PreludeIxWF pre) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.prepare.prepare_d pre ds = ok p) :
    ∀ d ∈ p.decls.val, DeclarationWF d := by
  rw [frontend.prepare.prepare_d] at h
  -- the two tuple-returning calls are `let (a, b) ← …`; splitting that `match`
  -- leaves the next bind with `ITree.bind` at its head, which `simp only
  -- [bind_eq_ok_iff]` no longer matches syntactically — so the binds are
  -- inverted by *application*, which unifies up to the monad instance
  obtain ⟨⟨picks, picked⟩, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨all, hall, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨out, names⟩, hhoist, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨syn, -, h⟩ := bind_eq_ok_iff.mp h
  have hp := Result.ok_injective h
  subst hp
  exact hoist_nat_op_ground_wf (prepared_stream_wf hpre hds hall) hhoist

/-- `ConLeche/Frontend/Prepare.lean:165-172` — **`prepare::prepare_prelude`
preserves well-formedness.**  This is the tail of task #85's chain: the parse
hands the fold the prepared list, and every record in it is one the parse's own
smart constructors built. -/
theorem prepare_prelude_wf {pre : frontend.prepare.PreludeIx}
    {ds out : alloc.vec.Vec env.Declaration}
    (hpre : PreludeIxWF pre) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.prepare.prepare_prelude pre ds = ok out) :
    ∀ d ∈ out.val, DeclarationWF d := by
  rw [frontend.prepare.prepare_prelude] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨p, hp, hout⟩ := h
  rw [← hout]
  exact prepare_d_wf hpre hds hp

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Both capstones are plain forward arguments over the generated model and reach
past nothing but Lean's own three axioms. -/

/-- info: 'ConRon.Refine.Frontend.prepare_prelude_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prepare_prelude_wf

/-- info: 'ConRon.Refine.Frontend.hoist_nat_op_ground_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoist_nat_op_ground_wf

end ConRon.Refine.Frontend
