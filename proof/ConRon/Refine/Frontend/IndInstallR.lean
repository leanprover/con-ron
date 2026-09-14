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
import ConRon.Refine.Frontend.IndR
import ConRon.Refine.Frontend.PrepareR
import ConRon.Refine.Env
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


/-! ## Does the block want a model?

`in_model_rec::wants` against `InModel.wants`
(`ConLeche/Frontend/InModel.lean:35-37`): the one test `install_ind_d` makes
before it calls the modeller. -/

/-- A `Vec` read at `i` is in range. -/
private theorem iid_index_lt {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length := by
  have hg := ExprOps.vec_index_getElem? h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at hg
  simp at hg

/-- The index recursion behind `in_model_rec::wants`. -/
private theorem wants_loop_refines (N : Nat) :
    ∀ (v : alloc.vec.Vec frontend.in_model_rec.IndTypeRec) (n i : Std.Usize) (b : Bool),
      v.val.length - i.val = N → n.val = v.val.length →
      frontend.in_model_rec.wants_loop v n i = ok b →
      b = ((v.val.map absMIndTypeRec).drop i.val).any (·.numNested > 0) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro v n i b hN hn h
    rw [frontend.in_model_rec.wants_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, h⟩ := h
      have hltv : i.val < v.val.length := iid_index_lt hidx
      have hdrop : (v.val.map absMIndTypeRec).drop i.val
          = absMIndTypeRec itr :: (v.val.map absMIndTypeRec).drop (i.val + 1) :=
        iid_drop_map absMIndTypeRec hidx
      rw [hdrop]
      split at h
      · rename_i hu
        simp only [Result.ok.injEq] at h
        have hne : 0 < itr.num_nested.val := by simpa using hu
        simp [← h, absMIndTypeRec, hne]
      · rename_i hu
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have heq : itr.num_nested.val = 0 := by
          have : ¬ (0 < itr.num_nested.val) := by simpa using hu
          omega
        rw [ih (v.val.length - i2.val) (by omega) v n i2 b rfl hn h, hi2v]
        simp [absMIndTypeRec, heq]
    · rename_i hge
      have hle : v.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `in_model_rec::wants` refines `InModel.wants`
(`ConLeche/Frontend/InModel.lean:35-37`). -/
theorem wants_refines {b : frontend.in_model_rec.BlockRec} {r : Bool}
    (h : frontend.in_model_rec.wants b = ok r) :
    r = ConLeche.Frontend.InModel.wants (absBlockRec b) := by
  rw [frontend.in_model_rec.wants] at h
  rw [ConLeche.Frontend.InModel.wants]
  simp only [absBlockRec]
  split at h
  · rename_i hgt
    have : 1 < b.types.val.length := by
      have := alloc.vec.Vec.len_val b.types; scalar_tac
    rw [← Result.ok_injective h]
    simp [this]
  · rename_i hgt
    have hle : ¬ (1 < b.types.val.length) := by
      have := alloc.vec.Vec.len_val b.types
      intro hc; exact hgt (by scalar_tac)
    rw [wants_loop_refines _ b.types _ 0#usize r rfl (alloc.vec.Vec.len_val _) h]
    simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac, hle]



/-! ## The projection census's three record lists

`export_c::proj_type_recs_of` / `proj_ctor_recs_of` / `proj_rec_recs_of`
against the three `mapM`s of `registerProjOwners`
(`ConLeche/Frontend/ExportC.lean:379-401`).  Each is an accumulating
`while i < n` loop, so each is strong induction on `n - i` against the list's
`drop`, in the shape `Refine/Frontend/IndR.lean` fixed for `blockRecOf`'s
three. -/

/-- A `Vec<proj_rec::ProjTypeRec>` as con-leche's list of tuples. -/
def absPTypeRecs (v : alloc.vec.Vec frontend.proj_rec.ProjTypeRec) :
    List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool) :=
  v.val.map absPTypeRec

/-- A `Vec<proj_rec::ProjCtorRec>` as con-leche's list of tuples. -/
def absPCtorRecs (v : alloc.vec.Vec frontend.proj_rec.ProjCtorRec) :
    List (ConLeche.Name × Nat × ConLeche.Expr) :=
  v.val.map absPCtorRec

/-- A `Vec<proj_rec::ProjRecRec>` as con-leche's list of tuples. -/
def absPRecRecs (v : alloc.vec.Vec frontend.proj_rec.ProjRecRec) :
    List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat) :=
  v.val.map absPRecRec

/-- `LineOut` transported along an equation on the con-leche side
(`Refine/Frontend/IndR.lean` keeps the same one-liner `private`). -/
private theorem iid_lineOut_of_eq {α β : Type} {A : α → β} {WF : α → Prop}
    {o : core.result.Result α frontend.export_c.LineErr}
    {x y : ConLeche.Frontend.M β} (h : LineOut A WF o x) (hxy : y = x) :
    LineOut A WF o y := by rw [hxy]; exact h

/-- A `LineOut`'s success half, spelled `pure` so that `pure_bind` fires. -/
private theorem iid_lineOut_ok_pure {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {x : ConLeche.Frontend.M β} (h : LineOut A WF (.Ok r) x) : x = pure (A r) := h.1

/-- The accumulator of `export_c::proj_type_recs_of`' index loop. -/
private theorem proj_type_recs_of_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out : alloc.vec.Vec frontend.proj_rec.ProjTypeRec) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec frontend.proj_rec.ProjTypeRec)
        frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → (∀ t ∈ out.val, ProjTypeRecWF t) →
      n.val = tys.val.length → n.val - i.val = N →
      frontend.export_c.proj_type_recs_of_loop st tys out n i = ok o →
      LineOut absPTypeRecs (fun v => ∀ t ∈ v.val, ProjTypeRecWF t) o
        (do let r ← ((absIndTypeRecs tys).drop i.val).mapM
              (fun t : ConLeche.Frontend.IndTypeRec => do
                 let cv ← ConLeche.Frontend.parseCVD lst t.cv
                 pure (cv.name, cv.levelParams, cv.type, t.numParams, t.numIndices,
                   ← t.ctors.mapM lst.name, t.isRec))
            pure (absPTypeRecs out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst tys out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.proj_type_recs_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨t, hidx, r, hr, h⟩ := h
      have hdrop : (absIndTypeRecs tys).drop i.val
          = absIndTypeRec t :: (absIndTypeRecs tys).drop (i.val + 1) :=
        iid_drop_map absIndTypeRec hidx
      have hcv := parse_cv_d_refines hrel hwf hr
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hcv ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndTypeRec]
        rw [hs]
        exact ⟨s, rfl⟩
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        have hns := st_names_refines hrel hwf hr1
        cases r1 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          refine LineErrSim.trans hns ?_
          intro s hs
          rw [hdrop, List.mapM_cons]
          simp only [absIndTypeRec]
          rw [iid_lineOut_ok_pure hcv, hs]
          exact ⟨s, rfl⟩
        | Ok cs =>
          simp only [bind_eq_ok_iff] at h
          obtain ⟨n1, hn1, v2, hv2, e, he, out1, hpush, i1, hi1, h⟩ := h
          have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
          obtain ⟨hcvn, hcvl, hcvt⟩ := parse_cv_d_wf hwf hr
          have hout1 : ∀ t ∈ out1.val, ProjTypeRecWF t := by
            refine iid_push_wf hout ⟨?_, ?_, ?_, st_names_wf hwf hr1⟩ hpush
            · rw [iid_name_dup hn1]; exact hcvn
            · rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv2)]; exact hcvl
            · rw [Expr.dup_eq he]; exact hcvt
          have hih := ih (n.val - i1.val) (by scalar_tac) st lst tys out1 n i1 o
            hrel hwf hout1 hn rfl h
          refine iid_lineOut_of_eq hih ?_
          have habs : absPTypeRecs out1
              = absPTypeRecs out ++ [absPTypeRec ⟨n1, v2, e, t.num_params, t.num_indices,
                  cs, t.is_rec⟩] := by
            rw [absPTypeRecs, vec_push_val hpush]; simp [absPTypeRecs]
          rw [hdrop, hi1v, List.mapM_cons, habs]
          simp only [absIndTypeRec]
          rw [iid_lineOut_ok_pure hcv, iid_lineOut_ok_pure hns]
          simp only [pure_bind, absPTypeRec, iid_name_dup hn1, Expr.dup_eq he,
            alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv2)]
          simp [absConstantVal, absU64]
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndTypeRecs tys).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndTypeRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::proj_type_recs_of` refines the `tys.mapM` of
`registerProjOwners` (`ConLeche/Frontend/ExportC.lean:379-401`). -/
theorem proj_type_recs_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {o : core.result.Result (alloc.vec.Vec frontend.proj_rec.ProjTypeRec)
      frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.proj_type_recs_of st tys = ok o) :
    LineOut absPTypeRecs (fun v => ∀ t ∈ v.val, ProjTypeRecWF t) o
      ((absIndTypeRecs tys).mapM
        (fun t : ConLeche.Frontend.IndTypeRec => do
           let cv ← ConLeche.Frontend.parseCVD lst t.cv
           pure (cv.name, cv.levelParams, cv.type, t.numParams, t.numIndices,
             ← t.ctors.mapM lst.name, t.isRec))) := by
  rw [frontend.export_c.proj_type_recs_of] at h
  have hh := proj_type_recs_of_loop_refines _ st lst tys _ _ 0#usize o hrel hwf
    (by intro t ht; simp [alloc.vec.Vec.with_capacity] at ht)
    (alloc.vec.Vec.len_val _) rfl h
  simpa [absPTypeRecs, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh



/-- The accumulator of `export_c::proj_ctor_recs_of`' index loop. -/
private theorem proj_ctor_recs_of_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (cts : alloc.vec.Vec frontend.scan_types.IndCtorRec)
      (out : alloc.vec.Vec frontend.proj_rec.ProjCtorRec) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec frontend.proj_rec.ProjCtorRec)
        frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → (∀ c ∈ out.val, ProjCtorRecWF c) →
      n.val = cts.val.length → n.val - i.val = N →
      frontend.export_c.proj_ctor_recs_of_loop st cts out n i = ok o →
      LineOut absPCtorRecs (fun v => ∀ c ∈ v.val, ProjCtorRecWF c) o
        (do let r ← ((absIndCtorRecs cts).drop i.val).mapM
              (fun c : ConLeche.Frontend.IndCtorRec => do
                 let cv ← ConLeche.Frontend.parseCVD lst c.cv
                 pure (cv.name, c.numFields, cv.type))
            pure (absPCtorRecs out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst cts out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.proj_ctor_recs_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hidx, r, hr, h⟩ := h
      have hdrop : (absIndCtorRecs cts).drop i.val
          = absIndCtorRec c :: (absIndCtorRecs cts).drop (i.val + 1) :=
        iid_drop_map absIndCtorRec hidx
      have hcv := parse_cv_d_refines hrel hwf hr
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hcv ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndCtorRec]
        rw [hs]
        exact ⟨s, rfl⟩
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, e, he, out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨hcvn, -, hcvt⟩ := parse_cv_d_wf hwf hr
        have hout1 : ∀ x ∈ out1.val, ProjCtorRecWF x := by
          refine iid_push_wf hout ⟨?_, ?_⟩ hpush
          · rw [iid_name_dup hn1]; exact hcvn
          · rw [Expr.dup_eq he]; exact hcvt
        have hih := ih (n.val - i1.val) (by scalar_tac) st lst cts out1 n i1 o
          hrel hwf hout1 hn rfl h
        refine iid_lineOut_of_eq hih ?_
        have habs : absPCtorRecs out1
            = absPCtorRecs out ++ [absPCtorRec ⟨n1, c.num_fields, e⟩] := by
          rw [absPCtorRecs, vec_push_val hpush]; simp [absPCtorRecs]
        rw [hdrop, hi1v, List.mapM_cons, habs]
        simp only [absIndCtorRec]
        rw [iid_lineOut_ok_pure hcv]
        simp only [pure_bind, absPCtorRec, iid_name_dup hn1, Expr.dup_eq he]
        simp [absConstantVal, absU64]
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndCtorRecs cts).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndCtorRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::proj_ctor_recs_of` refines the `cts.mapM` of
`registerProjOwners` (`ConLeche/Frontend/ExportC.lean:379-401`). -/
theorem proj_ctor_recs_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {o : core.result.Result (alloc.vec.Vec frontend.proj_rec.ProjCtorRec)
      frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.proj_ctor_recs_of st cts = ok o) :
    LineOut absPCtorRecs (fun v => ∀ c ∈ v.val, ProjCtorRecWF c) o
      ((absIndCtorRecs cts).mapM
        (fun c : ConLeche.Frontend.IndCtorRec => do
           let cv ← ConLeche.Frontend.parseCVD lst c.cv
           pure (cv.name, c.numFields, cv.type))) := by
  rw [frontend.export_c.proj_ctor_recs_of] at h
  have hh := proj_ctor_recs_of_loop_refines _ st lst cts _ _ 0#usize o hrel hwf
    (by intro c hc; simp [alloc.vec.Vec.with_capacity] at hc)
    (alloc.vec.Vec.len_val _) rfl h
  simpa [absPCtorRecs, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- The accumulator of `export_c::proj_rec_recs_of`' index loop. -/
private theorem proj_rec_recs_of_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (rcs : alloc.vec.Vec frontend.scan_types.IndRecRec)
      (out : alloc.vec.Vec frontend.proj_rec.ProjRecRec) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec frontend.proj_rec.ProjRecRec)
        frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → (∀ r ∈ out.val, ProjRecRecWF r) →
      n.val = rcs.val.length → n.val - i.val = N →
      frontend.export_c.proj_rec_recs_of_loop st rcs out n i = ok o →
      LineOut absPRecRecs (fun v => ∀ r ∈ v.val, ProjRecRecWF r) o
        (do let r ← ((absIndRecRecs rcs).drop i.val).mapM
              (fun r : ConLeche.Frontend.IndRecRec => do
                 let cv ← ConLeche.Frontend.parseCVD lst r.cv
                 pure (cv.name, cv.levelParams, cv.type, r.numMotives, r.numMinors))
            pure (absPRecRecs out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst rcs out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.proj_rec_recs_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨rc, hidx, r1, hr1, h⟩ := h
      have hdrop : (absIndRecRecs rcs).drop i.val
          = absIndRecRec rc :: (absIndRecRecs rcs).drop (i.val + 1) :=
        iid_drop_map absIndRecRec hidx
      have hcv := parse_cv_d_refines hrel hwf hr1
      cases r1 with
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hcv ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndRecRec]
        rw [hs]
        exact ⟨s, rfl⟩
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, v, hv, e, he, out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨hcvn, hcvl, hcvt⟩ := parse_cv_d_wf hwf hr1
        have hout1 : ∀ x ∈ out1.val, ProjRecRecWF x := by
          refine iid_push_wf hout ⟨?_, ?_, ?_⟩ hpush
          · rw [iid_name_dup hn1]; exact hcvn
          · rw [alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv)]; exact hcvl
          · rw [Expr.dup_eq he]; exact hcvt
        have hih := ih (n.val - i1.val) (by scalar_tac) st lst rcs out1 n i1 o
          hrel hwf hout1 hn rfl h
        refine iid_lineOut_of_eq hih ?_
        have habs : absPRecRecs out1
            = absPRecRecs out ++ [absPRecRec ⟨n1, v, e, rc.num_motives, rc.num_minors⟩] := by
          rw [absPRecRecs, vec_push_val hpush]; simp [absPRecRecs]
        rw [hdrop, hi1v, List.mapM_cons, habs]
        simp only [absIndRecRec]
        rw [iid_lineOut_ok_pure hcv]
        simp only [pure_bind, absPRecRec, iid_name_dup hn1, Expr.dup_eq he,
          alloc.vec.Vec.ext _ _ (PropWhen.names_copy_val hv)]
        simp [absConstantVal, absU64]
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndRecRecs rcs).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndRecRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::proj_rec_recs_of` refines the `rcs.mapM` of
`registerProjOwners` (`ConLeche/Frontend/ExportC.lean:379-401`). -/
theorem proj_rec_recs_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {o : core.result.Result (alloc.vec.Vec frontend.proj_rec.ProjRecRec)
      frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.proj_rec_recs_of st rcs = ok o) :
    LineOut absPRecRecs (fun v => ∀ r ∈ v.val, ProjRecRecWF r) o
      ((absIndRecRecs rcs).mapM
        (fun r : ConLeche.Frontend.IndRecRec => do
           let cv ← ConLeche.Frontend.parseCVD lst r.cv
           pure (cv.name, cv.levelParams, cv.type, r.numMotives, r.numMinors))) := by
  rw [frontend.export_c.proj_rec_recs_of] at h
  have hh := proj_rec_recs_of_loop_refines _ st lst rcs _ _ 0#usize o hrel hwf
    (by intro r hr; simp [alloc.vec.Vec.with_capacity] at hr)
    (alloc.vec.Vec.len_val _) rfl h
  simpa [absPRecRecs, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh



/-! ## The owner table, written

`export_c::insert_proj_owners` against the cited
`owners.foldl (fun m o => m.insert o.T o)` and `export_c::register_proj_owners`
against the whole of `registerProjOwners`
(`ConLeche/Frontend/ExportC.lean:379-401`).

The port writes the table unconditionally where con-leche's `match` sends the
empty list to `pure st`; the two agree because a `foldl` over `[]` is the
identity, and the `split` at the bottom of `register_proj_owners_refines` is
that observation. -/

/-- The accumulator of `export_c::insert_proj_owners`' index loop.  Only
`proj_owners` moves, so phase 1's `insert_proj_owners_wf` carries the
well-formedness half and this lemma is the relation alone. -/
private theorem insert_proj_owners_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (owners : alloc.vec.Vec frontend.proj_rec.ProjRecOwner) (n i : Std.Usize)
      (st' : frontend.export_c.StateD),
      StateDRel st lst → (∀ o ∈ owners.val, ProjRecOwnerWF o) →
      n.val = owners.val.length → n.val - i.val = N →
      frontend.export_c.insert_proj_owners_loop st owners n i = ok st' →
      StateDRel st'
        { lst with
          projOwners := ((owners.val.map absProjOwner).drop i.val).foldl
            (fun m o => m.insert o.T o) lst.projOwners } := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst owners n i st' hrel ho hn hN h
    rw [frontend.export_c.insert_proj_owners_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨pro, hidx, n1, hn1, pro1, hpro1, p, hins, h⟩ := h
      obtain ⟨old, hm⟩ := p
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hdrop : (owners.val.map absProjOwner).drop i.val
          = absProjOwner pro :: (owners.val.map absProjOwner).drop (i.val + 1) :=
        iid_drop_map absProjOwner hidx
      have hpw : ProjRecOwnerWF pro := ho _ (iid_vec_mem hidx)
      rw [iid_name_dup hn1, proj_rec_owner_dup_refines hpro1] at hins
      obtain ⟨hinv2, hkeys2, -, hrel2⟩ :=
        State.insert_step (Q := fun _ => True) State.nameKey hrel.projOwnersInv
          hrel.projOwnersKeys (fun _ _ => trivial) hrel.projOwners hpw.1 trivial hins
      have hstep := StateDRel.projOwners_update hrel hrel2 hinv2 hkeys2
      have hih := ih (n.val - i1.val) (by scalar_tac) _ _ owners n i1 st' hstep ho hn rfl h
      rw [hi1v] at hih
      rw [hdrop, List.foldl_cons]
      exact hih
    · rename_i hge
      have hnil : (owners.val.map absProjOwner).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      rw [hnil, List.foldl_nil, ← Result.ok_injective h]
      exact hrel

/-- `export_c::insert_proj_owners` refines the cited `owners.foldl`
(`ConLeche/Frontend/ExportC.lean:379-401`). -/
theorem insert_proj_owners_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {owners : alloc.vec.Vec frontend.proj_rec.ProjRecOwner}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (ho : ∀ o ∈ owners.val, ProjRecOwnerWF o)
    (h : frontend.export_c.insert_proj_owners st owners = ok st') :
    StateDRel st'
        { lst with
          projOwners := (owners.val.map absProjOwner).foldl
            (fun m o => m.insert o.T o) lst.projOwners }
      ∧ StateDWF st' := by
  refine ⟨?_, insert_proj_owners_wf hwf ho h⟩
  rw [frontend.export_c.insert_proj_owners] at h
  have hh := insert_proj_owners_loop_refines _ st lst owners _ 0#usize st' hrel ho
    (alloc.vec.Vec.len_val _) rfl h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- `export_c::register_proj_owners` refines `registerProjOwners`
(`ConLeche/Frontend/ExportC.lean:379-401`): the export's own shape data, read
back out of the parse tables, handed to `proj_rec::proj_rec_owners` and filed
under every owner's type name. -/
theorem register_proj_owners_refines (hsp : InstallSpec)
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {block : alloc.vec.Vec env.ConstantInfo}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hb : ConstantInfosWF block)
    (h : frontend.export_c.register_proj_owners st tys cts rcs block = ok (o, st')) :
    StepOut o st'
      (ConLeche.Frontend.registerProjOwners lst (absIndTypeRecs tys) (absIndCtorRecs cts)
        (absIndRecRecs rcs) (absConstantInfos block)) := by
  rw [frontend.export_c.register_proj_owners] at h
  rw [ConLeche.Frontend.registerProjOwners]
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  have hts := proj_type_recs_of_refines hrel hwf hr
  cases r with
  | Err e =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact LineErrSim.bind hts _
  | Ok ts =>
    rw [iid_lineOut_ok_pure hts]
    simp only [pure_bind]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have hcs := proj_ctor_recs_of_refines hrel hwf hr1
    cases r1 with
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact LineErrSim.bind hcs _
    | Ok cs =>
      rw [iid_lineOut_ok_pure hcs]
      simp only [pure_bind]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      have hrs := proj_rec_recs_of_refines hrel hwf hr2
      cases r2 with
      | Err e =>
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact LineErrSim.bind hrs _
      | Ok rs =>
        rw [iid_lineOut_ok_pure hrs]
        simp only [pure_bind]
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨owners, howners, st1, hst1, hu, hsteq⟩ := h
        obtain ⟨habs, hwfo⟩ :=
          hsp.projRecOwners hb
            (by intro t ht; rw [iid_deref_val] at ht; exact hts.2 t ht)
            (by intro c hc; rw [iid_deref_val] at hc; exact hcs.2 c hc)
            (by intro r hr'; rw [iid_deref_val] at hr'; exact hrs.2 r hr') howners
        obtain ⟨hrel1, hwf1⟩ := insert_proj_owners_refines hrel hwf hwfo hst1
        rw [iid_deref_val, iid_deref_val, iid_deref_val] at habs
        rw [← hu, ← hsteq]
        simp only [absPTypeRecs, absPCtorRecs, absPRecRecs]
        rw [← habs]
        split
        · rename_i hnil
          refine StepOut.ok rfl ?_ hwf1
          rw [hnil, List.foldl_nil] at hrel1
          exact hrel1
        · exact StepOut.ok rfl hrel1 hwf1


/-! ## The block's constants

`export_c::ind_block_types` / `ind_block_ctors` / `ind_block_recs` and their
joiner `ind_block_of` against `installIndD`'s `types ++ ctors ++ recs`
(`ConLeche/Frontend/ExportC.lean:564-628`).  The port accumulates the three
`mapM`s into ONE `Vec`, so each loop's statement is the abstracted accumulator
followed by the abstracted tail. -/

/-- The accumulator of `export_c::ind_block_types`' index loop. -/
private theorem ind_block_types_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec env.ConstantInfo) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → ConstantInfosWF out →
      n.val = tys.val.length → n.val - i.val = N →
      frontend.export_c.ind_block_types_loop st tys out n i = ok o →
      LineOut absConstantInfos ConstantInfosWF o
        (do let r ← ((absIndTypeRecs tys).drop i.val).mapM
              (fun t : ConLeche.Frontend.IndTypeRec => do
                 pure (ConLeche.ConstantInfo.indInfo (← ConLeche.Frontend.parseCVD lst t.cv) {}))
            pure (absConstantInfos out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst tys out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.ind_block_types_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨t, hidx, r, hr, h⟩ := h
      have hdrop : (absIndTypeRecs tys).drop i.val
          = absIndTypeRec t :: (absIndTypeRecs tys).drop (i.val + 1) :=
        iid_drop_map absIndTypeRec hidx
      have hcv := parse_cv_d_refines hrel hwf hr
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hcv ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndTypeRec]
        rw [hs]
        exact ⟨s, rfl⟩
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨ic, hic, out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hout1 : ConstantInfosWF out1 := by
          refine iid_push_wf hout ?_ hpush
          exact ⟨parse_cv_d_wf hwf hr, Env.ind_caps_default_wf hic⟩
        have hih := ih (n.val - i1.val) (by scalar_tac) st lst tys out1 n i1 o
          hrel hwf hout1 hn rfl h
        rw [hi1v] at hih
        refine iid_lineOut_of_eq hih ?_
        have habs : absConstantInfos out1
            = absConstantInfos out ++ [absConstantInfo (.IndInfo cv ic)] := by
          rw [absConstantInfos, vec_push_val hpush]; simp [absConstantInfos]
        rw [hdrop, List.mapM_cons, habs]
        simp only [absIndTypeRec]
        rw [iid_lineOut_ok_pure hcv]
        simp only [pure_bind, absConstantInfo, Env.ind_caps_default_refines hic]
        simp
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndTypeRecs tys).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndTypeRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::ind_block_types` refines the `tys.mapM` of `installIndD`
(`ConLeche/Frontend/ExportC.lean:564-628`). -/
theorem ind_block_types_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {out : alloc.vec.Vec env.ConstantInfo}
    {o : core.result.Result (alloc.vec.Vec env.ConstantInfo) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hout : ConstantInfosWF out)
    (h : frontend.export_c.ind_block_types st tys out = ok o) :
    LineOut absConstantInfos ConstantInfosWF o
      (do let r ← (absIndTypeRecs tys).mapM
            (fun t : ConLeche.Frontend.IndTypeRec => do
               pure (ConLeche.ConstantInfo.indInfo (← ConLeche.Frontend.parseCVD lst t.cv) {}))
          pure (absConstantInfos out ++ r)) := by
  rw [frontend.export_c.ind_block_types] at h
  have hh := ind_block_types_loop_refines _ st lst tys out _ 0#usize o hrel hwf hout
    (alloc.vec.Vec.len_val _) rfl h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- The accumulator of `export_c::ind_block_ctors`' index loop. -/
private theorem ind_block_ctors_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (cts : alloc.vec.Vec frontend.scan_types.IndCtorRec)
      (out : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec env.ConstantInfo) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → ConstantInfosWF out →
      n.val = cts.val.length → n.val - i.val = N →
      frontend.export_c.ind_block_ctors_loop st cts out n i = ok o →
      LineOut absConstantInfos ConstantInfosWF o
        (do let r ← ((absIndCtorRecs cts).drop i.val).mapM
              (fun c : ConLeche.Frontend.IndCtorRec => do
                 pure (ConLeche.ConstantInfo.ctorInfo (← ConLeche.Frontend.parseCVD lst c.cv)
                   c.numParams c.numFields))
            pure (absConstantInfos out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst cts out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.ind_block_ctors_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hidx, r, hr, h⟩ := h
      have hdrop : (absIndCtorRecs cts).drop i.val
          = absIndCtorRec c :: (absIndCtorRecs cts).drop (i.val + 1) :=
        iid_drop_map absIndCtorRec hidx
      have hcv := parse_cv_d_refines hrel hwf hr
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hcv ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndCtorRec]
        rw [hs]
        exact ⟨s, rfl⟩
      | Ok cv =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hout1 : ConstantInfosWF out1 := by
          refine iid_push_wf hout ?_ hpush
          exact parse_cv_d_wf hwf hr
        have hih := ih (n.val - i1.val) (by scalar_tac) st lst cts out1 n i1 o
          hrel hwf hout1 hn rfl h
        rw [hi1v] at hih
        refine iid_lineOut_of_eq hih ?_
        have habs : absConstantInfos out1
            = absConstantInfos out
              ++ [absConstantInfo (.CtorInfo cv c.num_params c.num_fields)] := by
          rw [absConstantInfos, vec_push_val hpush]; simp [absConstantInfos]
        rw [hdrop, List.mapM_cons, habs]
        simp only [absIndCtorRec]
        rw [iid_lineOut_ok_pure hcv]
        simp only [pure_bind, absConstantInfo, absU64]
        simp
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndCtorRecs cts).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndCtorRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::ind_block_ctors` refines the `cts.mapM` of `installIndD`
(`ConLeche/Frontend/ExportC.lean:564-628`). -/
theorem ind_block_ctors_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {out : alloc.vec.Vec env.ConstantInfo}
    {o : core.result.Result (alloc.vec.Vec env.ConstantInfo) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hout : ConstantInfosWF out)
    (h : frontend.export_c.ind_block_ctors st cts out = ok o) :
    LineOut absConstantInfos ConstantInfosWF o
      (do let r ← (absIndCtorRecs cts).mapM
            (fun c : ConLeche.Frontend.IndCtorRec => do
               pure (ConLeche.ConstantInfo.ctorInfo (← ConLeche.Frontend.parseCVD lst c.cv)
                 c.numParams c.numFields))
          pure (absConstantInfos out ++ r)) := by
  rw [frontend.export_c.ind_block_ctors] at h
  have hh := ind_block_ctors_loop_refines _ st lst cts out _ 0#usize o hrel hwf hout
    (alloc.vec.Vec.len_val _) rfl h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- The accumulator of `export_c::ind_block_recs`' index loop.  The one arm
that also reads recursor rules, through `parse_rules_d`, and the one that
computes the two derived counts. -/
private theorem ind_block_recs_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (rcs : alloc.vec.Vec frontend.scan_types.IndRecRec)
      (out : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec env.ConstantInfo) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → ConstantInfosWF out →
      n.val = rcs.val.length → n.val - i.val = N →
      frontend.export_c.ind_block_recs_loop st rcs out n i = ok o →
      LineOut absConstantInfos ConstantInfosWF o
        (do let r ← ((absIndRecRecs rcs).drop i.val).mapM
              (fun r : ConLeche.Frontend.IndRecRec => do
                 let rules ← r.rules.mapM (ConLeche.Frontend.parseRuleD lst)
                 pure (ConLeche.ConstantInfo.recInfo (← ConLeche.Frontend.parseCVD lst r.cv)
                   (r.numParams + r.numMotives + r.numMinors + r.numIndices)
                   (r.numParams + r.numMotives + r.numMinors) rules))
            pure (absConstantInfos out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst rcs out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.ind_block_recs_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨rc, hidx, r1, hr1, h⟩ := h
      have hdrop : (absIndRecRecs rcs).drop i.val
          = absIndRecRec rc :: (absIndRecRecs rcs).drop (i.val + 1) :=
        iid_drop_map absIndRecRec hidx
      have hru := parse_rules_d_refines hrel hwf hr1
      cases r1 with
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hru ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndRecRec]
        rw [hs]
        exact ⟨s, rfl⟩
      | Ok rs =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r2, hr2, h⟩ := h
        have hcv := parse_cv_d_refines hrel hwf hr2
        cases r2 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          refine LineErrSim.trans hcv ?_
          intro s hs
          rw [hdrop, List.mapM_cons]
          simp only [absIndRecRec]
          rw [iid_lineOut_ok_pure hru, hs]
          exact ⟨s, rfl⟩
        | Ok cv =>
          simp only [bind_eq_ok_iff] at h
          obtain ⟨i1, hia, i2, hib, i3, hic, i4, hid, out1, hpush, i5, hi5, h⟩ := h
          have hi5v : i5.val = i.val + 1 := HashMap.uscalar_add_eq hi5
          have hav : i1.val = rc.num_params.val + rc.num_motives.val :=
            HashMap.uscalar_add_eq hia
          have hbv : i2.val = i1.val + rc.num_minors.val := HashMap.uscalar_add_eq hib
          have hcvv : i3.val = i2.val + rc.num_indices.val := HashMap.uscalar_add_eq hic
          have hdv : i4.val = i1.val + rc.num_minors.val := HashMap.uscalar_add_eq hid
          have hout1 : ConstantInfosWF out1 := by
            refine iid_push_wf hout ?_ hpush
            exact ⟨parse_cv_d_wf hwf hr2, parse_rules_d_wf hwf hr1⟩
          have hih := ih (n.val - i5.val) (by scalar_tac) st lst rcs out1 n i5 o
            hrel hwf hout1 hn rfl h
          rw [hi5v] at hih
          refine iid_lineOut_of_eq hih ?_
          have habs : absConstantInfos out1
              = absConstantInfos out ++ [absConstantInfo (.RecInfo cv i3 i4 rs)] := by
            rw [absConstantInfos, vec_push_val hpush]; simp [absConstantInfos]
          rw [hdrop, List.mapM_cons, habs]
          simp only [absIndRecRec]
          rw [iid_lineOut_ok_pure hru, iid_lineOut_ok_pure hcv]
          simp only [pure_bind, absConstantInfo, absRecRules, absU64, hcvv, hbv, hdv, hav]
          simp [Nat.add_assoc]
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndRecRecs rcs).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndRecRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::ind_block_recs` refines the `rcs.mapM` of `installIndD`
(`ConLeche/Frontend/ExportC.lean:564-628`). -/
theorem ind_block_recs_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {out : alloc.vec.Vec env.ConstantInfo}
    {o : core.result.Result (alloc.vec.Vec env.ConstantInfo) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hout : ConstantInfosWF out)
    (h : frontend.export_c.ind_block_recs st rcs out = ok o) :
    LineOut absConstantInfos ConstantInfosWF o
      (do let r ← (absIndRecRecs rcs).mapM
            (fun r : ConLeche.Frontend.IndRecRec => do
               let rules ← r.rules.mapM (ConLeche.Frontend.parseRuleD lst)
               pure (ConLeche.ConstantInfo.recInfo (← ConLeche.Frontend.parseCVD lst r.cv)
                 (r.numParams + r.numMotives + r.numMinors + r.numIndices)
                 (r.numParams + r.numMotives + r.numMinors) rules))
          pure (absConstantInfos out ++ r)) := by
  rw [frontend.export_c.ind_block_recs] at h
  have hh := ind_block_recs_loop_refines _ st lst rcs out _ 0#usize o hrel hwf hout
    (alloc.vec.Vec.len_val _) rfl h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh


/-! ### The joiner

`export_c::ind_block_of` against `installIndD`'s `types ++ ctors ++ recs`.
Two one-line inversions of a `bind` whose continuation is `pure` carry the
accumulator from each loop's statement into the next one's. -/

/-- A failing `bind` whose continuation is `pure` is a failing `bind` under any
continuation: the continuation cannot be what threw. -/
private theorem iid_errSim_bind_pure {α β γ : Type}
    {e : frontend.export_c.LineErr} {x : ConLeche.Frontend.M α} {g : α → β}
    (h : LineErrSim e (do let a ← x; pure (g a)))
    (f : α → ConLeche.Frontend.M γ) : LineErrSim e (do let a ← x; f a) := by
  refine LineErrSim.trans h ?_
  intro s hs
  cases hx : x with
  | error s' => exact ⟨s', rfl⟩
  | ok v => rw [hx] at hs; simp at hs

/-- …and a succeeding one names the value the accumulator was extended by. -/
private theorem iid_bind_pure_ok {α β : Type} {x : ConLeche.Frontend.M α} {g : α → β}
    {b : β} (h : (do let a ← x; pure (g a)) = .ok b) : ∃ a, x = pure a ∧ g a = b := by
  cases hx : x with
  | error s => rw [hx] at h; simp at h
  | ok v => exact ⟨v, rfl, by rw [hx] at h; simpa using h⟩

/-- `export_c::ind_block_of` refines `installIndD`'s `types ++ ctors ++ recs`
(`ConLeche/Frontend/ExportC.lean:564-628`). -/
theorem ind_block_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {o : core.result.Result (alloc.vec.Vec env.ConstantInfo) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.ind_block_of st tys cts rcs = ok o) :
    LineOut absConstantInfos ConstantInfosWF o
      (do let types ← (absIndTypeRecs tys).mapM
            (fun t : ConLeche.Frontend.IndTypeRec => do
               pure (ConLeche.ConstantInfo.indInfo (← ConLeche.Frontend.parseCVD lst t.cv) {}))
          let ctors ← (absIndCtorRecs cts).mapM
            (fun c : ConLeche.Frontend.IndCtorRec => do
               pure (ConLeche.ConstantInfo.ctorInfo (← ConLeche.Frontend.parseCVD lst c.cv)
                 c.numParams c.numFields))
          let recs ← (absIndRecRecs rcs).mapM
            (fun r : ConLeche.Frontend.IndRecRec => do
               let rules ← r.rules.mapM (ConLeche.Frontend.parseRuleD lst)
               pure (ConLeche.ConstantInfo.recInfo (← ConLeche.Frontend.parseCVD lst r.cv)
                 (r.numParams + r.numMotives + r.numMinors + r.numIndices)
                 (r.numParams + r.numMotives + r.numMinors) rules))
          pure (types ++ ctors ++ recs)) := by
  have hempty : ConstantInfosWF (alloc.vec.Vec.new env.ConstantInfo) := by
    intro c hc; simp [alloc.vec.Vec.new] at hc
  rw [frontend.export_c.ind_block_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  have hnew : (alloc.vec.Vec.new env.ConstantInfo).val = [] := rfl
  have hts := ind_block_types_refines hrel hwf hempty hr
  simp only [absConstantInfos, hnew, List.map_nil, List.nil_append, bind_pure] at hts
  cases r with
  | Err e =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact LineErrSim.bind hts _
  | Ok ts =>
    rw [iid_lineOut_ok_pure hts]
    simp only [pure_bind]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    have hcs := ind_block_ctors_refines hrel hwf hts.2 hr1
    cases r1 with
    | Err e =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact iid_errSim_bind_pure hcs _
    | Ok cs =>
      obtain ⟨lctors, hlctors, hlc⟩ := iid_bind_pure_ok (iid_lineOut_ok_pure hcs)
      rw [hlctors]
      simp only [pure_bind]
      rw [hlc]
      exact ind_block_recs_refines hrel hwf hcs.2 h

/-! ## The block record, filed under every member name

`export_c::note_ind_blocks` against the cited
`b.types.foldl (fun m t => m.insert t.cv.name b)`
(`ConLeche/Frontend/ExportC.lean:564-628`).

Phase 1 gives the block record **no** well-formedness clause — `ModellerWF` is
unconditional in its argument, so `StateDWF` tracks neither `ind_blocks` nor
the records it holds (`Refine/Frontend/Ind.lean`'s module note).  Exactness
needs one fact all the same: `StateDRel`'s `ind_blocks` clause is a
`HashMap.RelOn NameWF`, and an insert into it must know its *key* is a
well-formed name.  `block_rec_types_names_wf` below is that fact and nothing
more — the type formers' names come out of `parse_cv_d`. -/

/-- The type formers of a block record carry well-formed names. -/
def BlockRecTypeNamesWF (b : frontend.in_model_rec.BlockRec) : Prop :=
  ∀ t ∈ b.types.val, NameWF t.cv.name

/-- The accumulator of `export_c::block_rec_types`' index loop, for names. -/
private theorem block_rec_types_names_wf_loop (N : Nat) :
    ∀ (st : frontend.export_c.StateD)
      (types : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out ts : alloc.vec.Vec frontend.in_model_rec.IndTypeRec) (n i : Std.Usize),
      StateDWF st → (∀ t ∈ out.val, NameWF t.cv.name) → n.val - i.val = N →
      frontend.export_c.block_rec_types_loop st types out n i = ok (.Ok ts) →
      ∀ t ∈ ts.val, NameWF t.cv.name := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st types out ts n i hwf hout hN h
    rw [frontend.export_c.block_rec_types_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨t, -, r, hr, h⟩ := h
      cases r with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        cases r1 with
        | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
        | Ok cv =>
          simp only [bind_eq_ok_iff] at h
          obtain ⟨out1, hpush, i1, hi1, h⟩ := h
          have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
          refine ih (n.val - i1.val) (by scalar_tac) st types out1 ts n i1 hwf ?_ rfl h
          refine iid_push_wf hout ?_ hpush
          exact (parse_cv_d_wf hwf hr1).1
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::block_rec_of` files type formers whose names are well formed. -/
theorem block_rec_of_type_names_wf {st : frontend.export_c.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {b : frontend.in_model_rec.BlockRec} (hwf : StateDWF st)
    (h : frontend.export_c.block_rec_of st tys cts rcs = ok (.Ok b)) :
    BlockRecTypeNamesWF b := by
  rw [frontend.export_c.block_rec_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
  | Ok ts =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    cases r1 with
    | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
    | Ok cs =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r2, hr2, h⟩ := h
      cases r2 with
      | Err e => simp only [Result.ok.injEq, reduceCtorEq] at h
      | Ok rs =>
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
        rw [← h]
        rw [frontend.export_c.block_rec_types] at hr
        exact block_rec_types_names_wf_loop _ st tys _ ts _ 0#usize hwf
          (by intro t ht; simp [alloc.vec.Vec.with_capacity] at ht) rfl hr

/-- The accumulator of `export_c::note_ind_blocks`' index loop. -/
private theorem note_ind_blocks_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (b : alloc.sync.Arc frontend.in_model_rec.BlockRec) (n i : Std.Usize)
      (st' : frontend.export_c.StateD),
      StateDRel st lst → BlockRecTypeNamesWF b →
      n.val = b.types.val.length → n.val - i.val = N →
      frontend.export_c.note_ind_blocks_loop st b n i = ok st' →
      StateDRel st'
        { lst with
          indBlocks := (((absBlockRec b).types).drop i.val).foldl
            (fun m t => m.insert t.cv.name (absBlockRec b)) lst.indBlocks } := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst b n i st' hrel hb hn hN h
    rw [frontend.export_c.note_ind_blocks_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, n1, hn1, a, ha, p, hins, h⟩ := h
      obtain ⟨old, hm⟩ := p
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hdrop : ((absBlockRec b).types).drop i.val
          = absMIndTypeRec itr :: ((absBlockRec b).types).drop (i.val + 1) := by
        simpa only [absBlockRec] using iid_drop_map absMIndTypeRec hidx
      have hnwf : NameWF itr.cv.name := hb _ (iid_vec_mem hidx)
      rw [iid_name_dup hn1] at hins
      rw [show a = b from Result.ok_injective (ha.symm.trans (ptr_clone_eq b))] at hins
      obtain ⟨hinv2, hkeys2, -, hrel2⟩ :=
        State.insert_step (Q := fun _ => True) State.nameKey hrel.indBlocksInv
          hrel.indBlocksKeys (fun _ _ => trivial) hrel.indBlocks hnwf trivial hins
      have hstep := StateDRel.indBlocks_update hrel hrel2 hinv2 hkeys2
      have hih := ih (n.val - i1.val) (by scalar_tac) _ _ b n i1 st' hstep hb hn rfl h
      rw [hi1v] at hih
      rw [hdrop, List.foldl_cons]
      exact hih
    · rename_i hge
      have hnil : ((absBlockRec b).types).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absBlockRec, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      rw [hnil, List.foldl_nil, ← Result.ok_injective h]
      exact hrel

/-- `export_c::note_ind_blocks` refines the cited `b.types.foldl`
(`ConLeche/Frontend/ExportC.lean:564-628`): the block record is filed under
every member type name, shared through `ron::ptr`. -/
theorem note_ind_blocks_refines {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {b : alloc.sync.Arc frontend.in_model_rec.BlockRec}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (hb : BlockRecTypeNamesWF b)
    (h : frontend.export_c.note_ind_blocks st b = ok st') :
    StateDRel st'
        { lst with
          indBlocks := ((absBlockRec b).types).foldl
            (fun m t => m.insert t.cv.name (absBlockRec b)) lst.indBlocks }
      ∧ StateDWF st' := by
  refine ⟨?_, note_ind_blocks_wf hwf h⟩
  rw [frontend.export_c.note_ind_blocks] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  have hh := note_ind_blocks_loop_refines _ st lst b _ 0#usize st' hrel hb
    (alloc.vec.Vec.len_val _) rfl h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

end ConRon.Refine.Frontend
