/-
`ConRon.Refine.Frontend.IndInstallR` — **the inductive record's install, exact
against con-leche** (task #87, phase 3).

Phase 1's `Refine/Frontend/Ind.lean` proved `export_c::install_ind_d` and
everything under it *well formed*.  This file is the tier above: the same
functions against `ConLeche/Frontend/ExportC.lean:319-404` and `:564-628`,
state for state and verdict for verdict.

`install_ind_d` is **the first function in the parse that can genuinely
construct a `RecordVerdict`** — every reader below it has `LineErrSim`'s
`Verdict` arm as `False` — so this is where `StepOutV`'s third arm starts
carrying content: the in-process modeller's decline, outside the census mode,
is con-leche's `.inr (.declined …)`.  As everywhere, the *message* is not
compared (DESIGN.md §3.1), only the verdict's kind.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.StateDR
import ConRon.Refine.Frontend.Ind
import ConRon.Refine.Frontend.PrepareR
import ConLeche.Frontend.InModel

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Plumbing

`Refine/Frontend/StateDR.lean` and `Refine/Frontend/Ind.lean` keep the same
three one-liners `private`; they are restated here rather than widening either
file's interface. -/

/-- What a `Vec` read hands back is one of the `Vec`'s entries. -/
private theorem iid_vec_mem {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    x ∈ v.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? h)

/-- The `Vec` read at `i`, as the head of the abstracted tail. -/
private theorem iid_drop_map {α β : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (f : α → β)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    (v.val.map f).drop i.val = f x :: (v.val.map f).drop (i.val + 1) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < v.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : v.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  rw [List.drop_eq_getElem_cons (by simpa using hlt)]
  simp [hx]

/-- A push extends a "every entry satisfies `P`" invariant by the pushed
element. -/
private theorem iid_push_wf {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  rw [vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- A state update that touches none of the six tracked fields keeps phase 1's
invariant. -/
private theorem iid_wf_same {st st' : frontend.export_c.StateD} (hst : StateDWF st)
    (hn : st'.names = st.names) (hl : st'.levels = st.levels)
    (he : st'.exprs = st.exprs) (hd : st'.decls = st.decls)
    (ho : st'.proj_owners = st.proj_owners) (hp : st'.proj_levels = st.proj_levels) :
    StateDWF st' :=
  ⟨hn ▸ hst.names, hl ▸ hst.levels, he ▸ hst.exprs, hd ▸ hst.decls,
   ho ▸ hst.proj_owners, hp ▸ hst.proj_levels⟩

/-- `name::dup` is the identity. -/
private theorem iid_name_dup {n r : name.Name} (h : name.dup n = ok r) : r = n := by
  rw [name_dup_eq] at h; exact (Result.ok_injective h).symm

/-- `Vec::deref` is the identity on the underlying list. -/
private theorem iid_deref_val {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).val = v.val := Slice.from_val _ _

/-! ## The names a generated record books

`export_c::note_gen_names`/`note_gen` against `noteGen`
(`ConLeche/Frontend/ExportC.lean:332-341`).  con-leche writes the fold inline
over `d.names`; the port takes the name list as an argument because
`push_gen_d` consumes the `Declaration` (`export_c.rs`'s doc comment says so),
so **`noteGenNames` is this file's escape hatch 1** — con-leche's body at the
names already in hand — and `noteGen_eq` is the equivalence, one `rfl`. -/

/-- **Escape hatch 1.**  `noteGen`'s body, at the record's names as an
argument (`ConLeche/Frontend/ExportC.lean:332-341`). -/
def noteGenNames (st : ConLeche.Frontend.StateD) (ns : List ConLeche.Name)
    (T0 : ConLeche.Name) : ConLeche.Frontend.StateD :=
  { st with genRecords := st.genRecords + 1,
            genOwner := ns.foldl (fun m n => m.insert n T0) st.genOwner }

/-- …and the hatch *is* `noteGen`. -/
theorem noteGen_eq (st : ConLeche.Frontend.StateD) (d : ConLeche.Declaration)
    (T0 : ConLeche.Name) :
    ConLeche.Frontend.noteGen st d T0 = noteGenNames st d.names T0 := rfl

/-- The accumulator of `export_c::note_gen_names`' index loop against
`noteGen`'s `d.names.foldl` (`ConLeche/Frontend/ExportC.lean:332-341`). -/
private theorem note_gen_names_loop_refines (N : Nat) :
    ∀ (m : ron.hashmap.HashMap name.Name name.Name)
      (lm : _root_.Std.HashMap ConLeche.Name ConLeche.Name)
      (names : alloc.vec.Vec name.Name) (t0 : name.Name) (n i : Std.Usize)
      (m' : ron.hashmap.HashMap name.Name name.Name),
      HashMap.RelOn NameWF m lm absName absName → HashMap.Inv State.hName m →
      HashMap.KeysOk NameWF m → NamesWF names → NameWF t0 →
      n.val = names.val.length → n.val - i.val = N →
      frontend.export_c.note_gen_names_loop m names t0 n i = ok m' →
      HashMap.RelOn NameWF m'
          (((absNames names).drop i.val).foldl
            (fun q x => q.insert x (absName t0)) lm) absName absName
        ∧ HashMap.Inv State.hName m' ∧ HashMap.KeysOk NameWF m' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m lm names t0 n i m' hrel hinv hkeys hnames ht0 hn hN h
    rw [frontend.export_c.note_gen_names_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n1, hidx, n2, hn2, n3, hn3, p, hins, h⟩ := h
      obtain ⟨old, hm⟩ := p
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hdrop : (absNames names).drop i.val
          = absName n1 :: (absNames names).drop (i.val + 1) := iid_drop_map absName hidx
      have hn1 : NameWF n1 := hnames _ (iid_vec_mem hidx)
      rw [iid_name_dup hn2] at hins
      rw [iid_name_dup hn3] at hins
      obtain ⟨hinv2, hkeys2, -, hrel2⟩ :=
        State.insert_step (Q := fun _ => True) State.nameKey hinv hkeys
          (fun _ _ => trivial) hrel hn1 trivial hins
      have hih := ih (n.val - i1.val) (by scalar_tac) hm _ names t0 n i1 m'
        hrel2 hinv2 hkeys2 hnames ht0 hn rfl h
      rw [hi1v] at hih
      rw [hdrop, List.foldl_cons]
      exact hih
    · rename_i hge
      have hnil : (absNames names).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absNames, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      rw [hnil, List.foldl_nil, ← Result.ok_injective h]
      exact ⟨hrel, hinv, hkeys⟩

/-- `export_c::note_gen_names` refines `noteGenNames`
(`ConLeche/Frontend/ExportC.lean:332-341`).  It writes `gen_records` and
`gen_owner`, neither of which `StateDWF` tracks (`Refine/Frontend/Ind.lean`'s
module note), so the well-formedness half passes straight through. -/
theorem note_gen_names_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {names : alloc.vec.Vec name.Name} {t0 : name.Name}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hnames : NamesWF names)
    (ht0 : NameWF t0)
    (h : frontend.export_c.note_gen_names st names t0 = ok st') :
    StateDRel st' (noteGenNames lst (absNames names) (absName t0)) ∧ StateDWF st' := by
  rw [frontend.export_c.note_gen_names] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨g, hg, hm, hloop, rfl⟩ := h
  obtain ⟨hrel2, hinv2, hkeys2⟩ :=
    note_gen_names_loop_refines _ st.gen_owner lst.genOwner names t0 _ 0#usize hm
      hrel.genOwner hrel.genOwnerInv hrel.genOwnerKeys hnames ht0
      (alloc.vec.Vec.len_val _) rfl hloop
  rw [show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero] at hrel2
  refine ⟨?_, iid_wf_same hwf rfl rfl rfl rfl rfl rfl⟩
  have hstep := StateDRel.genRecords_step (StateDRel.genOwner_update hrel hrel2 hinv2 hkeys2) hg
  exact hstep

/-- `export_c::note_gen` refines `noteGen`
(`ConLeche/Frontend/ExportC.lean:332-341`). -/
theorem note_gen_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {d : env.Declaration} {t0 : name.Name}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hd : DeclarationWF d)
    (ht0 : NameWF t0) (h : frontend.export_c.note_gen st d t0 = ok st') :
    StateDRel st' (ConLeche.Frontend.noteGen lst (absDeclaration d) (absName t0))
      ∧ StateDWF st' := by
  rw [frontend.export_c.note_gen] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ns, hns, h⟩ := h
  obtain ⟨habs, hwfn⟩ := declaration_names_refines hd hns
  rw [noteGen_eq, ← habs]
  exact note_gen_names_refines hrel hwf hwfn ht0 h

/-! ## The projection census records, as con-leche's tuples

`ConLeche/Frontend/ProjRec.lean:332-370`'s `projRecOwners` takes its three
lists as tuples; the port's three named structs abstract onto exactly those.

**Duplicated on purpose, for one integration step**, exactly as
`Refine/Frontend/StateDR.lean`'s `absProjOwner` is: `Refine/Frontend/ProjRecR.lean`
defines the same three maps as `absProjTypeRec`/`absProjCtorRec`/`absProjRecRec`,
the pairs are definitionally equal, and when the files meet the coordinator
keeps ProjRecR's and makes these `:= absProjTypeRec` and so on.  They are here
because `InstallSpec`'s third field cannot be stated without them and this
file must not depend on one above it. -/

/-- `proj_rec::ProjTypeRec` as Lean's `(name, levelParams, type, numParams,
numIndices, ctors, isRec)`. -/
def absPTypeRec (t : frontend.proj_rec.ProjTypeRec) :
    ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool :=
  (absName t.name, absNames t.lps, absExpr t.ty, t.n_p.val, t.n_i.val,
    absNames t.ctors, t.is_rec)

/-- `proj_rec::ProjCtorRec` as Lean's `(name, numFields, type)`. -/
def absPCtorRec (c : frontend.proj_rec.ProjCtorRec) :
    ConLeche.Name × Nat × ConLeche.Expr :=
  (absName c.name, c.n_f.val, absExpr c.ty)

/-- `proj_rec::ProjRecRec` as Lean's `(name, levelParams, type, numMotives,
numMinors)`. -/
def absPRecRec (r : frontend.proj_rec.ProjRecRec) :
    ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat :=
  (absName r.name, absNames r.lps, absExpr r.ty, r.n_m.val, r.nm.val)

/-! ## The named ingredients

Three lemmas this file stands on that belong to files beside it (the
`Refine/IndSpec.lean` pattern, DESIGN.md §3.5): one from the state layer
below, one from the block-record file beside it, one from the projection
rewrite's own.  Each is stated here exactly as its owner states it, and when
the files meet the coordinator replaces the bundle with the three theorems.

The **modeller** is separate, and is not an ingredient that will ever be
discharged: it is the residue (`Refine/Frontend/Base.lean`'s `ModellerWF`,
whose exactness twin it is). -/

/-- **The residue, exactly** — the exactness twin of `Frontend.ModellerWF`: at
related contexts and the same block, `in_model_rec::Modeller::generate` returns
what `ConLeche.Frontend.InModel.generate` (`ConLeche/Frontend/InModel.lean:39-45`)
returns, and declines where it declines.  The decline's *text* is not compared
(DESIGN.md §3.1).

This is `Refine/Frontend/ChunksR.lean`'s `ModellerRefines inst g CtxRel`
written out: that file sits above this one, so the definition is repeated here
rather than imported, and the coordinator unifies the two. -/
def IndModellerRefines {G : Type} (inst : frontend.in_model_rec.Modeller G) (g : G) :
    Prop :=
  ∀ ctx lctx b o, CtxRel ctx lctx → inst.generate g ctx b = ok o →
    (∀ ds, o = .Ok ds →
      ConLeche.Frontend.InModel.generate lctx (absBlockRec b)
        = .ok (ds.val.map absDeclaration)) ∧
    (∀ m, o = .Err m →
      ∃ s, ConLeche.Frontend.InModel.generate lctx (absBlockRec b) = .error s)

/-- The three lemmas of the neighbouring files that this one consumes. -/
structure InstallSpec : Prop where
  /-- `export_c::note_proj_iota` refines `noteProjIota`
  (`ConLeche/Frontend/ExportC.lean:304-317`) — `Refine/Frontend/StateDR.lean`'s,
  the state layer's last reader. -/
  noteProjIota : ∀ {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {cvp : env.ConstantVal},
    StateDRel st lst → StateDWF st → ConstantValWF cvp →
    frontend.export_c.note_proj_iota st cvp = ok st' →
    StateDRel st' (ConLeche.Frontend.noteProjIota lst (absConstantVal cvp))
      ∧ StateDWF st'
  /-- `export_c::block_rec_of` refines `blockRecOf`
  (`ConLeche/Frontend/ExportC.lean:353-375`) — `Refine/Frontend/IndR.lean`'s. -/
  blockRecOf : ∀ {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {o : core.result.Result frontend.in_model_rec.BlockRec frontend.export_c.LineErr},
    StateDRel st lst → StateDWF st →
    frontend.export_c.block_rec_of st tys cts rcs = ok o →
    LineOut absBlockRec (fun _ => True) o
      (ConLeche.Frontend.blockRecOf lst (absIndTypeRecs tys) (absIndCtorRecs cts)
        (absIndRecRecs rcs))
  /-- `proj_rec::proj_rec_owners` refines `projRecOwners`
  (`ConLeche/Frontend/ProjRec.lean:332-370`) — `Refine/Frontend/ProjRecR.lean`'s. -/
  projRecOwners : ∀ {block : alloc.vec.Vec env.ConstantInfo}
    {types : Slice frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec}
    {recs : Slice frontend.proj_rec.ProjRecRec}
    {os : alloc.vec.Vec frontend.proj_rec.ProjRecOwner},
    ConstantInfosWF block → (∀ t ∈ types.val, ProjTypeRecWF t) →
    (∀ c ∈ ctors.val, ProjCtorRecWF c) → (∀ r ∈ recs.val, ProjRecRecWF r) →
    frontend.proj_rec.proj_rec_owners block types ctors recs = ok os →
    os.val.map absProjOwner
        = ConLeche.Frontend.projRecOwners (absConstantInfos block)
            (types.val.map absPTypeRec) (ctors.val.map absPCtorRec)
            (recs.val.map absPRecRec)
      ∧ ∀ o ∈ os.val, ProjRecOwnerWF o

/-! ## One generated record, pushed

`export_c::push_gen_d` against `pushGenD`
(`ConLeche/Frontend/ExportC.lean:323-331`): `push_decl`, plus the
projection-iota registration on the `ThmDecl` arm. -/

/-- `export_c::push_gen_d` refines `pushGenD`
(`ConLeche/Frontend/ExportC.lean:323-331`). -/
theorem push_gen_d_refines (hsp : InstallSpec) {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {d : env.Declaration}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hd : DeclarationWF d)
    (h : frontend.export_c.push_gen_d st d = ok st') :
    StateDRel st' (ConLeche.Frontend.pushGenD lst (absDeclaration d)) ∧ StateDWF st' := by
  rw [frontend.export_c.push_gen_d.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨st1, hst1, h⟩ := h
  cases d with
  | ThmDecl cv v =>
    simp only [bind_eq_ok_iff] at hst1
    obtain ⟨cv2, hcv2, hst1⟩ := hst1
    rw [Env.constant_val_dup_refines hcv2] at hst1
    obtain ⟨hrel1, hwf1⟩ := hsp.noteProjIota hrel hwf hd.1 hst1
    simp only [absDeclaration, ConLeche.Frontend.pushGenD]
    exact push_decl_refines hrel1 hwf1 hd h
  | AxiomDecl cv =>
    rw [← Result.ok_injective hst1] at h
    simp only [absDeclaration, ConLeche.Frontend.pushGenD]
    exact push_decl_refines hrel hwf hd h
  | DefnDecl cv v hint =>
    rw [← Result.ok_injective hst1] at h
    simp only [absDeclaration, ConLeche.Frontend.pushGenD]
    exact push_decl_refines hrel hwf hd h
  | OpaqueDecl cv v =>
    rw [← Result.ok_injective hst1] at h
    simp only [absDeclaration, ConLeche.Frontend.pushGenD]
    exact push_decl_refines hrel hwf hd h
  | BasisDecl k =>
    rw [← Result.ok_injective hst1] at h
    simp only [absDeclaration, ConLeche.Frontend.pushGenD]
    exact push_decl_refines hrel hwf hd h
  | IndDecl bl n =>
    rw [← Result.ok_injective hst1] at h
    simp only [absDeclaration, ConLeche.Frontend.pushGenD]
    exact push_decl_refines hrel hwf hd h
  | QuotDecl k cv =>
    rw [← Result.ok_injective hst1] at h
    simp only [absDeclaration, ConLeche.Frontend.pushGenD]
    exact push_decl_refines hrel hwf hd h

/-! ## The generated family, pushed

`export_c::push_gen_list` against `pushGenList`
(`ConLeche/Frontend/ExportC.lean:402-411`).  con-leche recurses on the list;
the port walks it by index and copies each record in (`export_c.rs`: the
subset has no way to move an element out of an owned `Vec`), so the loop is
strong induction on `n - i` against the list's `drop`. -/

/-- The accumulator of `export_c::push_gen_list`'s index loop. -/
private theorem push_gen_list_loop_refines (hsp : InstallSpec) (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (gen : alloc.vec.Vec env.Declaration) (t0 : name.Name) (n i : Std.Usize)
      (st' : frontend.export_c.StateD),
      StateDRel st lst → StateDWF st → (∀ d ∈ gen.val, DeclarationWF d) → NameWF t0 →
      n.val = gen.val.length → n.val - i.val = N →
      frontend.export_c.push_gen_list_loop st gen t0 n i = ok st' →
      StateDRel st'
          (ConLeche.Frontend.pushGenList lst ((absDecls gen).drop i.val) (absName t0))
        ∧ StateDWF st' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst gen t0 n i st' hrel hwf hgen ht0 hn hN h
    rw [frontend.export_c.push_gen_list_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨d, hidx, ns, hns, d1, hd1, st1, hst1, st2, hst2, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hdd : DeclarationWF d := hgen _ (iid_vec_mem hidx)
      have hdrop : (absDecls gen).drop i.val
          = absDeclaration d :: (absDecls gen).drop (i.val + 1) :=
        iid_drop_map absDeclaration hidx
      rw [export_c_declaration_dup_refines hd1] at hst1
      obtain ⟨hrel1, hwf1⟩ := push_gen_d_refines hsp hrel hwf hdd hst1
      obtain ⟨habs, hwfn⟩ := declaration_names_refines hdd hns
      obtain ⟨hrel2, hwf2⟩ := note_gen_names_refines hrel1 hwf1 hwfn ht0 hst2
      rw [habs] at hrel2
      have hih := ih (n.val - i1.val) (by scalar_tac) st2 _ gen t0 n i1 st'
        hrel2 hwf2 hgen ht0 hn rfl h
      rw [hi1v] at hih
      rw [hdrop, ConLeche.Frontend.pushGenList, noteGen_eq]
      exact hih
    · rename_i hge
      have hnil : (absDecls gen).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absDecls, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      rw [hnil, ConLeche.Frontend.pushGenList, ← Result.ok_injective h]
      exact ⟨hrel, hwf⟩

/-- `export_c::push_gen_list` refines `pushGenList`
(`ConLeche/Frontend/ExportC.lean:402-411`). -/
theorem push_gen_list_refines (hsp : InstallSpec) {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {gen : alloc.vec.Vec env.Declaration}
    {t0 : name.Name} (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hgen : ∀ d ∈ gen.val, DeclarationWF d) (ht0 : NameWF t0)
    (h : frontend.export_c.push_gen_list st gen t0 = ok st') :
    StateDRel st' (ConLeche.Frontend.pushGenList lst (absDecls gen) (absName t0))
      ∧ StateDWF st' := by
  rw [frontend.export_c.push_gen_list] at h
  have := push_gen_list_loop_refines hsp _ st lst gen t0 _ 0#usize st' hrel hwf hgen ht0
    (alloc.vec.Vec.len_val _) rfl h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using this

end ConRon.Refine.Frontend
