/-
# `ConRon.Refine2.Checker.StreamIndex` — the stream index, related

`arena::stream_index` against `Arena/StreamIndex.lean` (con-leche's
`Cached/StreamIndex.lean`): the index the driver builds once from the records and
freezes into the `PersTier`, its insertion steps, and the view of a record's position.

**The representation** (`arena::stream_index`'s note): the Rust stores every record's
constants in counter order, so a constant's slot is its counter, and its name map holds
the counter of the name's first entry; the twin's base maps a name to `(counter,
constant)`.  `StreamIndexRel` is entry for entry over `ixRow`/`ixTbl`
(`Refine2/AbsState.lean`), and carries the two facts that make an insertion move no
old entry: the constant list is exactly `next` long, and every stored counter and slot
is in range.
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Arena.StreamIndex

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap2 (Inv)

/-! ## The relation -/

/-- **The index's constants**: its name map against the twin's, the list as long as the
counter, the map well formed and every counter it stores in range. -/
structure IxConsts (ix : arena.stream_index.IStreamIndex)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) : Prop where
  rows : ∀ n, ixRow ix n = idx[absNIdx n]?
  len : ix.consts.val.length = ix.next.val
  inv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable ix.idx
  range : ∀ n c, ConRon.Refine.HashMap2.toFun ix.idx n = some c → c.val < ix.consts.val.length

/-- **The index's tables**: its table map against the twin's, well formed, every slot
in range. -/
structure IxTables (ix : arena.stream_index.IStreamIndex)
    (tbls : Std.HashMap NIdx (Nat × IProjTable)) : Prop where
  rows : ∀ n, ixTbl ix n = tbls[absNIdx n]?
  inv : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable ix.tbls
  range : ∀ n p, ConRon.Refine.HashMap2.toFun ix.tbls n = some p →
    p.2.val < ix.tables.val.length

/-- **`arena::stream_index::IStreamIndex` against the twin's `IStreamIndex`.** -/
structure StreamIndexRel (ix : arena.stream_index.IStreamIndex) (I : IStreamIndex) : Prop where
  consts : IxConsts ix I.base.idx
  tables : IxTables ix I.base.tbls
  firsts : I.firsts.toList = ix.firsts.val.map absU
  next : I.next = absU ix.next

theorem StreamIndexRel.baseRel {ix : arena.stream_index.IStreamIndex} {I : IStreamIndex}
    (h : StreamIndexRel ix I) (b : IFBase) (hi : b.idx = I.base.idx)
    (ht : b.tbls = I.base.tbls) : BaseRel ix b :=
  ⟨fun n => by rw [hi]; exact h.consts.rows n, fun n => by rw [ht]; exact h.tables.rows n⟩

/-- A tier holding a related index is a well-formed base. -/
theorem StreamIndexRel.baseOK {pers : arena.store.PersTier} {I : IStreamIndex}
    (h : StreamIndexRel pers.env I) : BaseOK pers :=
  ⟨h.consts.inv, h.tables.inv, h.consts.range, h.tables.range⟩

/-! ## The copies -/

/-- **`stream_index::i_proj_table_dup` is the identity on the abstraction.** -/
theorem i_proj_table_dup_abs {t o : arena.env.IProjTable}
    (h : arena.stream_index.i_proj_table_dup t = ok o) : absIProjTable o = absIProjTable t := by
  rw [arena.stream_index.i_proj_table_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIProjTable, dupId_nidx _ _ hn, dupId_nidx _ _ hn1, nidx_vec_dup_val hv,
    eidx_vec_dup_val hv1]

/-! ## The empty index -/

/-- **`stream_index_empty()` ⊑ `{}`**. -/
theorem ixEmpty_rel : StreamIndexRel ixEmpty ({} : IStreamIndex) := by
  have hn := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64) (m' := ixEmpty.idx) rfl
  have ht := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64 × Std.U64) (m' := ixEmpty.tbls) rfl
  refine ⟨⟨fun n => ?_, by simp [ixEmpty], hn.1, fun n c hc => ?_⟩,
    ⟨fun n => ?_, ht.1, fun n p hp => ?_⟩, by simp [ixEmpty], by simp [ixEmpty, absU]⟩
  · simp [ixRow, hn.2.2 n]
  · rw [hn.2.2 n] at hc; cases hc
  · simp [ixTbl, ht.2.2 n]
  · rw [ht.2.2 n] at hp; cases hp

/-! ## The insertions -/

/-- A cast of a `Vec`'s length up to a `u64` is its value. -/
private theorem len_cast_val {α : Type} {v : alloc.vec.Vec α} {s : Std.U64}
    (hs : lift (UScalar.cast .U64 (alloc.vec.Vec.len v)) = (ok s : Result Std.U64)) :
    s.val = v.val.length := by
  simp only [lift, Result.ok.injEq] at hs
  subst hs
  rw [usize_cast_u64_val']
  simp [alloc.vec.Vec.len]

/-- **`insert_consts` ⊑ `insertConsts`**: the record's constants from cursor `i` on, a
name's first entry winning, each pushed at the next counter.  The tables and the record
positions are untouched. -/
theorem insert_consts_rel (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    ∀ (m : Nat) (ix : arena.stream_index.IStreamIndex) (i : Std.Usize)
      (idx : Std.HashMap NIdx (Nat × IConstantInfo)) {ix'},
      cs.val.length - i.val = m → IxConsts ix idx →
      arena.stream_index.insert_consts ix cs i = ok ix' →
      IxConsts ix' (insertConsts idx (absU ix.next) ((cs.val.drop i.val).map absIConstantInfo)).1 ∧
        absU ix'.next =
          (insertConsts idx (absU ix.next) ((cs.val.drop i.val).map absIConstantInfo)).2 ∧
        ix'.tables = ix.tables ∧ ix'.tbls = ix.tbls ∧ ix'.firsts = ix.firsts := by
  intro m
  induction m with
  | zero =>
    intro ix i idx ix' hm hC h
    rw [arena.stream_index.insert_consts.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    exact ⟨hC, rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    intro ix i idx ix' hm hC h
    rw [arena.stream_index.insert_consts.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    have hlt : i.val < cs.val.length := by omega
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hiiv : cs.val[i.val]? = some ii := vec_index_some hii
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hname : absNIdx n = (absIConstantInfo ii).name := i_constant_info_name_abs hn
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := ConRon.Refine.HashMap2.contains_key_refines_wf nidx_eq2 hC.inv
      ConRon.Refine.HashMap2.KeysOk_true trivial hb
    obtain ⟨hm1, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ii1, hii1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hvv : v.val = ix.consts.val ++ [ii1] := ConRon.Refine.vec_push_val hv
    have hii1 := i_constant_info_dup_abs hii1
    have hi2v : i2.val = ix.next.val + 1 := by simpa using ConRon.Refine.Nat.uadd_val hi2
    have hi3v : i3.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, insertConsts]
    have hget : cs.val[i.val] = ii := by
      have := hiiv; rw [List.getElem?_eq_getElem hlt] at this; exact Option.some_inj.mp this
    rw [hget]
    -- the step's index, one entry inserted if new
    have hC' : IxConsts { ix with consts := v, idx := hm1, next := i2 }
        (idx.insertIfNew (absIConstantInfo ii).name (absU ix.next, absIConstantInfo ii)) := by
      have hmem : (ConRon.Refine.HashMap2.toFun ix.idx n).isSome =
          ((absIConstantInfo ii).name ∈ idx) := by
        rw [← hname, Std.HashMap.mem_iff_isSome_getElem?, ← hC.rows n, ixRow]
        cases hp : ConRon.Refine.HashMap2.toFun ix.idx n with
        | none => rfl
        | some c =>
          have hc := hC.range n c hp
          simp [List.getElem?_eq_getElem hc]
      cases b with
      | true =>
        obtain rfl := (Result.ok_injective hhm).symm
        have hin : (absIConstantInfo ii).name ∈ idx := by
          have := hmem; rw [← hbv] at this; simpa using this.symm
        refine ⟨fun k => ?_, ?_, hC.inv, fun k c hc => ?_⟩
        · rw [Std.HashMap.getElem?_insertIfNew]
          rw [ite_eq_right (by simp [hin])]
          rw [← hC.rows k, ixRow, ixRow]
          cases hp : ConRon.Refine.HashMap2.toFun ix.idx k with
          | none => rfl
          | some c =>
            simp only [Option.bind_some, hvv]
            rw [List.getElem?_append_left (hC.range k c hp)]
        · simp only [hvv, List.length_append, List.length_singleton, hi2v, hC.len]
        · simp only [hvv, List.length_append, List.length_singleton]
          have := hC.range k c hc; omega
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hhm
        obtain ⟨⟨old, hm2⟩, hins, hhm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hhm
        obtain rfl := (Result.ok_injective hhm).symm
        obtain ⟨hinv', -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True)
          nidx_eq2 hC.inv ConRon.Refine.HashMap2.KeysOk_true trivial hins
        have hnin : (absIConstantInfo ii).name ∉ idx := by
          intro hc; rw [← hmem, ← hbv] at hc; simp at hc
        refine ⟨fun k => ?_, ?_, hinv', fun k c hc => ?_⟩
        · rw [Std.HashMap.getElem?_insertIfNew, ixRow, hupd, Function.update_apply]
          by_cases hk : k = n
          · subst hk
            rw [ite_eq_left rfl, ite_eq_left (by simp [hname, hnin])]
            simp only [Option.bind_some, hvv]
            rw [List.getElem?_append_right (by rw [hC.len]), hC.len, Nat.sub_self]
            simp [hii1]
          · rw [ite_eq_right hk, ite_eq_right (by
              simp only [beq_iff_eq, not_and]
              intro he; exact absurd (absNIdx_inj (hname.trans he)).symm hk)]
            rw [← hC.rows k, ixRow]
            cases hp : ConRon.Refine.HashMap2.toFun ix.idx k with
            | none => rfl
            | some c =>
              simp only [Option.bind_some, hvv]
              rw [List.getElem?_append_left (hC.range k c hp)]
        · simp only [hvv, List.length_append, List.length_singleton, hi2v, hC.len]
        · rw [hupd, Function.update_apply] at hc
          simp only [hvv, List.length_append, List.length_singleton]
          by_cases hk : k = n
          · subst hk
            rw [ite_eq_left rfl] at hc
            obtain rfl := (Option.some_injective _ hc).symm
            rw [hC.len]; omega
          · rw [ite_eq_right hk] at hc
            have := hC.range k c hc; omega
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      ih { ix with consts := v, idx := hm1, next := i2 } i3 _ (by omega) hC' h
    have hnext : absU i2 = absU ix.next + 1 := by simp [absU, hi2v]
    rw [hi3v] at h1 h2
    simp only [hnext] at h1 h2
    exact ⟨h1, h2, h3, h4, h5⟩

/-- **`insert_tables` ⊑ `insertTables`**: the record's tables at record position `r`, a
name's first entry winning.  The constants, the counter and the record positions are
untouched. -/
theorem insert_tables_rel (r : Std.U64) (ts : alloc.vec.Vec arena.env.IProjTable) :
    ∀ (m : Nat) (ix : arena.stream_index.IStreamIndex) (i : Std.Usize)
      (tbls : Std.HashMap NIdx (Nat × IProjTable)) {ix'},
      ts.val.length - i.val = m → IxTables ix tbls →
      arena.stream_index.insert_tables ix r ts i = ok ix' →
      IxTables ix' (insertTables tbls (absU r) ((ts.val.drop i.val).map absIProjTable)) ∧
        ix'.consts = ix.consts ∧ ix'.idx = ix.idx ∧ ix'.next = ix.next ∧
        ix'.firsts = ix.firsts := by
  intro m
  induction m with
  | zero =>
    intro ix i tbls ix' hm hT h
    rw [arena.stream_index.insert_tables.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ts by scalar_tac)] at h
    obtain rfl := (Result.ok_injective h).symm
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    exact ⟨hT, rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    intro ix i tbls ix' hm hT h
    rw [arena.stream_index.insert_tables.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ts by scalar_tac)] at h
    have hlt : i.val < ts.val.length := by omega
    obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hitv : ts.val[i.val]? = some it := vec_index_some hit
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl := dupId_nidx _ _ hn
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := ConRon.Refine.HashMap2.contains_key_refines_wf nidx_eq2 hT.inv
      ConRon.Refine.HashMap2.KeysOk_true trivial hb
    obtain ⟨⟨v, hm1⟩, hvm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, insertTables]
    have hget : ts.val[i.val] = it := by
      have := hitv; rw [List.getElem?_eq_getElem hlt] at this; exact Option.some_inj.mp this
    rw [hget]
    have hkey : (absIProjTable it).structName = absNIdx it.struct_name := rfl
    have hmem : (ConRon.Refine.HashMap2.toFun ix.tbls it.struct_name).isSome =
        ((absIProjTable it).structName ∈ tbls) := by
      rw [hkey, Std.HashMap.mem_iff_isSome_getElem?, ← hT.rows, ixTbl]
      cases hp : ConRon.Refine.HashMap2.toFun ix.tbls it.struct_name with
      | none => rfl
      | some p =>
        have hc := hT.range _ p hp
        simp [List.getElem?_eq_getElem hc]
    have hT' : IxTables { ix with tables := v, tbls := hm1 }
        (tbls.insertIfNew (absIProjTable it).structName (absU r, absIProjTable it)) := by
      cases b with
      | true =>
        simp only [↓reduceIte] at hvm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hvm).symm
        have hin : (absIProjTable it).structName ∈ tbls := by
          have := hmem; rw [← hbv] at this; simpa using this.symm
        refine ⟨fun k => ?_, hT.inv, hT.range⟩
        rw [Std.HashMap.getElem?_insertIfNew, ite_eq_right (by simp [hin])]
        exact hT.rows k
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hvm
        obtain ⟨s, hs, hvm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hvm
        have hsv := len_cast_val hs
        obtain ⟨⟨old, hm2⟩, hins, hvm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hvm
        obtain ⟨it1, hit1, hvm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hvm
        obtain ⟨v1, hv1, hvm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hvm
        have hvv : v1.val = ix.tables.val ++ [it1] := ConRon.Refine.vec_push_val hv1
        obtain ⟨hv1e, hm1e⟩ := Prod.mk.inj (Result.ok_injective hvm)
        subst hv1e hm1e
        have hit1 := i_proj_table_dup_abs hit1
        obtain ⟨hinv', -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True)
          nidx_eq2 hT.inv ConRon.Refine.HashMap2.KeysOk_true trivial hins
        have hnin : (absIProjTable it).structName ∉ tbls := by
          intro hc; rw [← hmem, ← hbv] at hc; simp at hc
        refine ⟨fun k => ?_, hinv', fun k p hp => ?_⟩
        · rw [Std.HashMap.getElem?_insertIfNew, ixTbl, hupd, Function.update_apply]
          by_cases hk : k = it.struct_name
          · subst hk
            rw [ite_eq_left rfl, ite_eq_left (by simp only [hkey, beq_self_eq_true, true_and]; exact hnin)]
            simp only [Option.bind_some, hvv]
            rw [List.getElem?_append_right (by rw [hsv]), hsv, Nat.sub_self]
            simp [hit1]
          · rw [ite_eq_right hk, ite_eq_right (by
              simp only [hkey, beq_iff_eq, not_and]
              intro he; exact absurd (absNIdx_inj he).symm hk)]
            rw [← hT.rows k, ixTbl]
            cases hp : ConRon.Refine.HashMap2.toFun ix.tbls k with
            | none => rfl
            | some p =>
              simp only [Option.bind_some, hvv]
              rw [List.getElem?_append_left (hT.range k p hp)]
        · rw [hupd, Function.update_apply] at hp
          show p.2.val < v1.val.length
          simp only [hvv, List.length_append, List.length_singleton]
          by_cases hk : k = it.struct_name
          · subst hk
            rw [ite_eq_left rfl] at hp
            obtain rfl := (Option.some_injective _ hp).symm
            simp only; omega
          · rw [ite_eq_right hk] at hp
            have := hT.range k p hp; omega
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih { ix with tables := v, tbls := hm1 } i2 _ (by omega) hT' h
    rw [hi2v] at h1
    exact ⟨h1, h2, h3, h4, h5⟩

/-! ## The view of a position -/

/-- **`stream_index_view` ⊑ `IStreamIndex.view`**: an empty layer over the frozen index,
visible below the record's first counter (the counter past the records for a position
past them) and its position. -/
theorem stream_index_view_rel {pers : arena.store.PersTier} {I : IStreamIndex}
    {k : Std.U64} {w : arena.env.IFEnv}
    (hI : StreamIndexRel pers.env I) (hk : k.val ≤ Std.Usize.max)
    (h : arena.stream_index.stream_index_view pers k = ok w) :
    IFEnvRelI pers w (I.view (absU k)) := by
  rw [arena.stream_index.stream_index_view] at h
  obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hiv : i.val = k.val := by
    rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hk]
    exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi).symm
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hcv : absU c = I.firsts.getD (absU k) I.next := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hI.firsts, hI.next]
    by_cases hlt : i < alloc.vec.Vec.len pers.env.firsts
    · rw [ite_eq_left hlt] at hc
      obtain ⟨i2, hi2, hc⟩ := ConRon.Refine.bind_eq_ok_iff.mp hc
      have hi2v : i2.val = k.val := by
        rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hk]
        exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi2).symm
      have := vec_index_some hc
      rw [hi2v] at this
      simp [absU, List.getElem?_map, this]
    · rw [ite_eq_right hlt] at hc
      obtain rfl := (Result.ok_injective hc).symm
      have hge : pers.env.firsts.val.length ≤ k.val := by
        have h1 := (Std.UScalar.lt_equiv i _).not.mp hlt
        have h2 : (alloc.vec.Vec.len pers.env.firsts).val = pers.env.firsts.val.length :=
          alloc.vec.Vec.len_val _
        omega
      simp [absU, List.getElem?_map, List.getElem?_eq_none hge]
  rw [arena.env.ifenv_layer] at h
  simp only [arena.env.i_env_empty, ron.hashmap2.HashMap2.new, bind_ok] at h
  obtain rfl := (Result.ok_injective h).symm
  have hn := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64) (m' := layer00.idx) rfl
  refine ⟨⟨⟨fun n => ?_, fun n => ?_, hI.baseRel _ rfl rfl, ?_, rfl, hI.baseOK⟩, ?_⟩,
    hn.1, fun n p hp => ?_, hn.1, fun n s hs => ?_⟩
  · show (ConRon.Refine.HashMap2.toFun layer00.idx n).bind _ = _
    simp [hn.2.2 n, IStreamIndex.view]
  · show (ConRon.Refine.HashMap2.toFun layer00.tbls n).bind _ = _
    rw [show layer00.tbls = layer00.idx from rfl]
    simp [hn.2.2 n, IStreamIndex.view]
  · simp only [IStreamIndex.view]; exact hcv.symm
  · simp [IStreamIndex.view, absIEnv]
  · have hp' : ConRon.Refine.HashMap2.toFun layer00.idx n = some p := hp
    rw [hn.2.2 n] at hp'; cases hp'
  · have hs' : ConRon.Refine.HashMap2.toFun layer00.idx n = some s := hs
    rw [hn.2.2 n] at hs'; cases hs'

end ConRon.Refine2
