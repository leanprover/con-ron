/-
# `ConRon.Bridge.Modular.Infos` — the copies' statements, Theorem 1 (task #166)

`readInfosOf_run`: one module's copies read, its statements and kinds upstream's, read back.
`readInfos_run`: every module's, **upstream's reads succeeding on the snapshot** and every
requested copy's entry related (`InfosRel`).  The twin groups the copies by module in buckets,
upstream by a hash map sorted by key: both groups of a module are the copies of that module in
order (`byModule_mem`, `bm_byModule_mem`), so each group upstream reads is one the twin read.  What
an entry is does not depend on the group: it is the specification's statement at the copy's
location (upstream's `readInfos_ok`), so twin's and upstream's maps agree at every requested copy
whichever group was read last.  Run style, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.Clash
public import ConLeche.Verify.Driver.Clashes
public import ConLeche.Verify.Driver.ReachFrom
public import ConRon.Bridge.Modular.Graph

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left Copy Roots OLeanLevel ModFiles)

/-- con-leche: none — the loads' order and flags read back: what reading the copies needs. -/
structure LoadsOF (st : EStore) (ld : ConRon.Arena.Frontend.Olean.HeaderLoads)
    (ldC : ConLeche.Frontend.Olean.HeaderLoads) : Prop where
  order : ListRel (NR st) ld.order.toList ldC.order.toList
  flags : ld.flags = ldC.flags

theorem LoadsOF.ext {st st' : EStore} (hx : Ext st st') {ld : ConRon.Arena.Frontend.Olean.HeaderLoads}
    {ldC : ConLeche.Frontend.Olean.HeaderLoads} (h : LoadsOF st ld ldC) : LoadsOF st' ld ldC :=
  ⟨NR_list_ext hx h.order, h.flags⟩

theorem loadsOF_of {st : EStore} {ld : ConRon.Arena.Frontend.Olean.HeaderLoads}
    {ldC : ConLeche.Frontend.Olean.HeaderLoads} (h : LoadsRel st ld ldC) : LoadsOF st ld ldC :=
  ⟨h.order, h.flags⟩

/-- The loads' name at a position, read back. -/
theorem nameAt_den {pk : OleanPins} {st : EStore} (hnu : NullsRel st pk)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (h : LoadsOF st ld ldC) (i : Nat) :
    denoteN st.ns (ld.nameAt pk i) = some (ldC.nameAt i) := by
  unfold ConRon.Arena.Frontend.Olean.HeaderLoads.nameAt ConLeche.Frontend.Olean.HeaderLoads.nameAt
  rw [← Array.getElem?_toList, ← Array.getElem?_toList]
  rcases optRel_cases (listRel_getElem? h.order i) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
  · rw [h1, h2]; exact hnu.anon
  · rw [h1, h2]; exact h3

/-- A copy's location, read alike. -/
theorem at_loc {st : EStore} {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (h : IndexRel st ix ixC) (c : Copy) :
    (ix.at c).map (·.loc) = (ixC.at c).map (·.loc) := by
  unfold ConRon.Arena.Frontend.Olean.NameIndex.at ConLeche.Frontend.Olean.NameIndex.at
  rw [← Array.getElem?_toList, ← Array.getElem?_toList]
  rcases optRel_cases (listRel_getElem? h.parts c.mod) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]
    simp only [Option.bind_some]
    rw [← Array.getElem?_toList, ← Array.getElem?_toList]
    rcases optRel_cases (listRel_getElem? h3.consts c.pos) with ⟨g1, g2⟩ | ⟨q, qC, g1, g2, g3⟩
    · rw [g1, g2]; rfl
    · rw [g1, g2]; simp [g3.loc]

theorem listRel_zip_info {st : EStore} :
    ∀ {cs : List Copy} {ss : List ConRon.Arena.Frontend.Olean.StmtRec} {ssC : List ConstantVal}
      {ks : List (CKindF NIdx Unit)} {ksC : List (CKindF ConLeche.Name Unit)},
      ss.mapM (denoteStmt st) = some ssC → ks.mapM (denoteKindN st) = some ksC →
      ListRel (CopyInfoRel st) (cs.zip (ss.zip ks)) (cs.zip (ssC.zip ksC))
  | [], _, _, _, _, _, _ => by simp; exact .nil
  | _ :: _, [], ssC, _, _, h1, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h1; subst h1; simp; exact .nil
  | _ :: _, _ :: _, _, [], ksC, _, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h2; subst h2; simp; exact .nil
  | c :: cs, s :: ss, ssC, k :: ks, ksC, h1, h2 => by
    simp only [List.mapM_cons] at h1 h2
    obtain ⟨z, hz, h1⟩ := bind_some_left h1
    obtain ⟨zs, hzs, h1⟩ := bind_some_left h1
    obtain ⟨j, hj, h2⟩ := bind_some_left h2
    obtain ⟨js, hjs, h2⟩ := bind_some_left h2
    simp only [pure, Option.some.injEq] at h1 h2
    subst h1 h2
    exact .cons ⟨rfl, hz, hj⟩ (listRel_zip_info hzs hjs)

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → ys.length = l.length
  | [], ys, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; rfl
  | a :: l, ys, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨y, -, h⟩ := bind_some_left h
    obtain ⟨zs, hzs, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    simp [mapM_length hzs]

theorem denoteStmt_ext {st st' : EStore} (hx : Ext st st') {c : ConRon.Arena.Frontend.Olean.StmtRec}
    {z : ConstantVal} (h : denoteStmt st c = some z) : denoteStmt st' c = some z := by
  obtain ⟨h1, h2, h3⟩ := denoteStmt_parts h
  simp [denoteStmt, denoteN_ext h1 hx, mapM_denoteN_ext hx h2, denote_ext h3 hx]

theorem CopyInfoRel.ext {st st' : EStore} (hx : Ext st st')
    {x : Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit}
    {y : Copy × ConstantVal × CKindF ConLeche.Name Unit} (h : CopyInfoRel st x y) :
    CopyInfoRel st' x y :=
  ⟨h.1, denoteStmt_ext hx h.2.1, denoteKindN_ext hx h.2.2⟩

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:76-91 readInfosOf — **one module's copies,
their statements and kinds read together, are upstream's**, on the snapshot, read back. -/
theorem readInfosOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    {i : Nat} {cs : Array Copy}
    {arr : Array (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)} {s s' : AState}
    (hctx : Ctx pk s) (hld : LoadsOF s.store ld ldC) (hix : IndexRel s.store ix ixC)
    (h : ConRon.Arena.Frontend.Olean.readInfosOf (modelFs F) pk sp ld ix i cs s = .ok (arr, s')) :
    ParseStep s s' ∧ ∃ arrC, ModelIO.Gives (ConLeche.Frontend.Olean.readInfosOf
        (.ofPath sp) ldC ixC (i, cs) : ModelIO _) F (.ok arrC) ∧
      ListRel (CopyInfoRel s'.store) arr.toList arrC.toList := by
  unfold ConRon.Arena.Frontend.Olean.readInfosOf at h
  obtain ⟨mn, s₁, h1, hA⟩ := AM.bind_ok h
  obtain ⟨rfl, hd⟩ := readName_run h1
  have hmn : mn = ldC.nameAt i := Option.some.inj (hd.symm.trans (nameAt_den hctx.nulls hld i))
  subst hmn
  have hlev : ld.levelAt i = ((ldC.flags[i]?).getD default).level := by
    unfold ConRon.Arena.Frontend.Olean.HeaderLoads.levelAt; rw [hld.flags]
  have hlocs : (cs.toList.filterMap fun c => (ix.at c).map (·.loc)) =
      cs.toList.filterMap fun c => (ixC.at c).map (·.loc) := by
    congr 1; funext c; exact at_loc hix c
  obtain ⟨fv, s₂, h2, hB⟩ := AM.bind_ok hA
  cases hf : ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp (ldC.nameAt i) (ld.levelAt i) with
  | error e => rw [hf] at h2; exact (AM.fail_ok h2).elim
  | ok f =>
  rw [hf] at h2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  obtain ⟨o1, s₃, h3, hC⟩ := AM.bind_ok hB
  cases o1 with
  | none => exact (AM.fail_ok hC).elim
  | some ss =>
  obtain ⟨o2, s₄, h4, hD⟩ := AM.bind_ok hC
  cases o2 with
  | none => exact (AM.fail_ok hD).elim
  | some ks =>
  obtain ⟨hst3, ssC, hss, hds⟩ := readStmts_run hctx h3
  obtain ⟨hst4, ksC, hks, hdk⟩ := readKinds_run (hctx.step hst3) h4
  dsimp only at hD
  by_cases hlen : (ss.length == cs.size && ks.length == cs.size) = true
  · rw [ite_eq_left hlen] at hD
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hD
    refine ⟨hst3.trans hst4, cs.zip (ssC.zip ksC).toArray, ?_, ?_⟩
    · unfold ConLeche.Frontend.Olean.readInfosOf
      dsimp only
      refine (readFiles_sim (roots_ok_of_bare hsp) rfl (hlev ▸ hf)).bind ?_
      dsimp only
      rw [hlev, hlocs] at hss hks
      rw [hss, hks]
      have hl1 := mapM_length hds
      have hl2 := mapM_length hdk
      simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      have : (ssC.length == cs.size && ksC.length == cs.size) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨hl1.trans hlen.1, hl2.trans hlen.2⟩
      simp only [this, ↓reduceIte]
      exact ModelIO.gives_pure _ _
    · rw [Array.toList_zip, Array.toList_zip]
      have := listRel_zip_info (cs := cs.toList) (list_mono (fun _ _ hy => denoteStmt_ext hst4.ext hy) _ hds) hdk
      simpa using this
  · rw [ite_eq_right hlen] at hD
    exact (AM.fail_ok hD).elim

/-! ## The groups -/

/-- The twin's buckets: each the module's copies, in order. -/
theorem buckets_fold (top : Nat) :
    ∀ (l : List Copy) (b : Array (Array Copy)) (hs : b.size = top), (∀ c ∈ l, c.mod < top) →
      ∀ (L : List Copy), (∀ k (hk : k < top), (b[k]'(by omega)).toList = L.filter (·.mod == k)) →
      (l.foldl (fun (b : Array (Array Copy)) c => b.modify c.mod (·.push c)) b).size = top ∧
      ∀ k, k < top → ((l.foldl (fun (b : Array (Array Copy)) c => b.modify c.mod (·.push c)) b)[k]?)
        = some ((L ++ l).filter (·.mod == k)).toArray
  | [], b, hs, _, L, hb => by
    refine ⟨hs, fun k hk => ?_⟩
    simp only [List.foldl_nil, List.append_nil]
    rw [Array.getElem?_eq_getElem (by omega)]
    congr 1
    apply Array.ext'
    rw [hb k hk]
  | c :: l, b, hs, hl, L, hb => by
    rw [List.foldl_cons]
    have := buckets_fold top l (b.modify c.mod (·.push c)) (by simp [hs])
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (L ++ [c]) (fun k hk => by
        rw [Array.getElem_modify]
        split
        · rename_i he
          subst he
          simp [hb _ hk]
        · rename_i he
          have : (c.mod == k) = false := by simpa using he
          simp [hb k hk, this])
    simpa using this

theorem byModule_top (cs : List Copy) :
    ∀ (t : Nat), ∀ c ∈ cs, c.mod < cs.foldl (fun t c => max t (c.mod + 1)) t := by
  induction cs with
  | nil => intro t c hc; cases hc
  | cons a l ih =>
    intro t c hc
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · have : ∀ (l : List Copy) (t : Nat), t ≤ l.foldl (fun t c => max t (c.mod + 1)) t := by
        intro l; induction l with
        | nil => intro t; exact Nat.le_refl t
        | cons x l ih' => intro t; rw [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih' _)
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) (this l _)
    · exact ih _ c hc

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:93-97 byModule — **the twin's groups**: a
module's copies, in order, when it has some. -/
theorem byModule_mem {cs : Array Copy} {i : Nat} {g : Array Copy}
    (h : (i, g) ∈ ConRon.Arena.Frontend.Olean.byModule cs) :
    g.toList = cs.toList.filter (·.mod == i) ∧ g.size > 0 := by
  unfold ConRon.Arena.Frontend.Olean.byModule at h
  dsimp only at h
  rw [← Array.foldl_toList, ← Array.foldl_toList] at h
  generalize ht : cs.toList.foldl (fun t c => max t (c.mod + 1)) 0 = top at h
  have htop := byModule_top cs.toList 0
  rw [ht] at htop
  obtain ⟨hsz, hget⟩ := buckets_fold top cs.toList (Array.replicate top #[]) (by simp) htop []
    (fun k hk => by simp)
  simp only [Array.mem_map, Array.mem_filter, Prod.exists, Prod.mk.injEq] at h
  obtain ⟨a, k, ⟨hm, hpos⟩, rfl, rfl⟩ := h
  rw [Array.mem_zipIdx_iff_getElem?] at hm
  dsimp only at hm
  have hk : k < top := by
    have := (Array.getElem?_eq_some_iff.mp hm).1
    rw [hsz] at this; exact this
  rw [hget k hk] at hm
  simp only [List.nil_append, Option.some.injEq] at hm
  subst hm
  exact ⟨by simp, by simpa using hpos⟩

/-- Upstream's groups: a module's copies, in order, when it has some. -/
theorem bmStep_get :
    ∀ (l : List Copy) (m : Std.HashMap Nat (Array Copy)) (i : Nat),
      (l.foldl ConLeche.Driver.bmStep m)[i]? =
        match m[i]? with
        | none => if l.filter (·.mod == i) = [] then none else some (l.filter (·.mod == i)).toArray
        | some a => some (a ++ (l.filter (·.mod == i)).toArray)
  | [], m, i => by cases h : m[i]? <;> simp [h]
  | c :: l, m, i => by
    rw [List.foldl_cons, bmStep_get l _ i]
    simp only [ConLeche.Driver.bmStep, Std.HashMap.getElem?_alter]
    by_cases he : c.mod = i
    · subst he
      simp only [BEq.rfl, ↓reduceIte, List.filter_cons]
      cases hm : m[c.mod]? <;> simp
    · have : (c.mod == i) = false := by simpa using he
      simp only [this, Bool.false_eq_true, ↓reduceIte, List.filter_cons]

theorem bm_byModule_mem {cs : Array Copy} {i : Nat} {g : Array Copy}
    (h : (i, g) ∈ ConLeche.Frontend.Olean.byModule cs) :
    g.toList = cs.toList.filter (·.mod == i) ∧ g.size > 0 := by
  rw [ConLeche.Driver.byModule_eq, ConLeche.Driver.qsort_mem,
    Std.HashMap.mem_toArray_iff_getElem?_eq_some] at h
  rw [← Array.foldl_toList, bmStep_get] at h
  simp only [Std.HashMap.getElem?_empty] at h
  split at h
  · cases h
  · rename_i hne
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨by simp, ?_⟩
    simp only [List.size_toArray]
    exact List.length_pos_iff.mpr hne

/-- Every group upstream reads, the twin read. -/
theorem byModule_sub {cs : Array Copy} {x : Nat × Array Copy}
    (h : x ∈ ConLeche.Frontend.Olean.byModule cs) : x ∈ ConRon.Arena.Frontend.Olean.byModule cs := by
  obtain ⟨i, g⟩ := x
  obtain ⟨h1, h2⟩ := bm_byModule_mem h
  unfold ConRon.Arena.Frontend.Olean.byModule
  dsimp only
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize ht : cs.toList.foldl (fun t c => max t (c.mod + 1)) 0 = top
  have htop := byModule_top cs.toList 0
  rw [ht] at htop
  obtain ⟨hsz, hget⟩ := buckets_fold top cs.toList (Array.replicate top #[]) (by simp) htop []
    (fun k hk => by simp)
  have hi : i < top := by
    have : 0 < (cs.toList.filter (·.mod == i)).length := by rw [← h1]; simpa using h2
    obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos this
    simp only [List.mem_filter, beq_iff_eq] at hc
    exact hc.2 ▸ htop c hc.1
  simp only [Array.mem_map, Array.mem_filter, Prod.exists, Prod.mk.injEq]
  refine ⟨g, i, ⟨?_, by simpa using h2⟩, rfl, rfl⟩
  rw [Array.mem_zipIdx_iff_getElem?]
  dsimp only
  rw [hget i hi]
  congr 1
  apply Array.ext'
  simp [h1]

/-! ## Every module's copies -/

/-- con-leche: none — **the statements read for some copies, read back**: an entry only at a
requested copy, and at every requested copy an entry on both sides, the twin's read back as
upstream's. -/
structure InfosRel (st : EStore) (cs : Array Copy)
    (infos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit))
    (infosC : Std.HashMap Copy (ConstantVal × CKindF ConLeche.Name Unit)) : Prop where
  dom : ∀ c v, infos[c]? = some v → c ∈ cs.toList
  rel : ∀ c ∈ cs.toList, ∃ v w, infos[c]? = some v ∧ infosC[c]? = some w ∧
    denoteStmt st v.1 = some w.1 ∧ denoteKindN st v.2 = some w.2

/-- The infos' insert, over any values. -/
theorem insFold {V : Type} :
    ∀ (L : List (Copy × V)) (m : Std.HashMap Copy V),
      (∀ c v, (L.foldl (fun m (x : Copy × V) => m.insert x.1 x.2) m)[c]? = some v →
        (c, v) ∈ L ∨ m[c]? = some v) ∧
      (∀ c, (∃ v, (c, v) ∈ L) ∨ (m[c]?).isSome = true →
        ((L.foldl (fun m (x : Copy × V) => m.insert x.1 x.2) m)[c]?).isSome = true)
  | [], m => by simp
  | (c₀, v₀) :: L, m => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := insFold L (m.insert c₀ v₀)
    refine ⟨fun c v h => ?_, fun c h => h2 c ?_⟩
    · rcases h1 c v h with hh | hh
      · exact .inl (List.mem_cons_of_mem _ hh)
      · rw [Std.HashMap.getElem?_insert] at hh
        split at hh
        · rename_i he
          obtain rfl := eq_of_beq he
          cases hh
          exact .inl List.mem_cons_self
        · exact .inr hh
    · rcases h with ⟨v, hv⟩ | hh
      · rcases List.mem_cons.mp hv with he | hv
        · cases he; exact .inr (by simp)
        · exact .inl ⟨v, hv⟩
      · refine .inr ?_
        rw [Std.HashMap.getElem?_insert]
        split
        · rfl
        · exact hh

theorem mapExcept_gives {α β ε : Type} {F : FS} {f : α → ModelIO (Except ε β)} :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, (f x).Gives F (Except.ok y)) →
      ∃ ys, (ConLeche.mapExcept f l : ModelIO (Except ε (List β))).Gives F (Except.ok ys)
  | [], _ => ⟨[], ModelIO.gives_pure _ _⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := mapExcept_gives l (fun z hz => h z (List.mem_cons_of_mem _ hz))
    refine ⟨y :: ys, ?_⟩
    unfold ConLeche.mapExcept
    refine hy.bind ?_
    dsimp only
    refine hys.bind ?_
    exact ModelIO.gives_pure _ _

theorem infosFold {V : Type} :
    ∀ (rs : List (Array (Copy × V))) (m : Std.HashMap Copy V),
      (∀ c v, (rs.foldl (fun m r => r.foldl (fun m (x : Copy × V) => m.insert x.1 x.2) m) m)[c]? = some v →
        (∃ r ∈ rs, (c, v) ∈ r.toList) ∨ m[c]? = some v) ∧
      (∀ c, (∃ r ∈ rs, ∃ v, (c, v) ∈ r.toList) ∨ (m[c]?).isSome = true →
        ((rs.foldl (fun m r => r.foldl (fun m (x : Copy × V) => m.insert x.1 x.2) m) m)[c]?).isSome = true)
  | [], m => by simp
  | r :: rs, m => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := infosFold rs (r.foldl (fun m (x : Copy × V) => m.insert x.1 x.2) m)
    obtain ⟨g1, g2⟩ := insFold r.toList m
    rw [Array.foldl_toList] at g1 g2
    refine ⟨fun c v h => ?_, fun c h => h2 c ?_⟩
    · rcases h1 c v h with ⟨r', hr', h⟩ | h
      · exact .inl ⟨r', List.mem_cons_of_mem _ hr', h⟩
      · rcases g1 c v h with h | h
        · exact .inl ⟨r, List.mem_cons_self, h⟩
        · exact .inr h
    · rcases h with ⟨r', hr', v, h⟩ | h
      · rcases List.mem_cons.1 hr' with rfl | hr'
        · exact .inr (g2 c (.inl ⟨v, h⟩))
        · exact .inl ⟨r', hr', v, h⟩
      · exact .inr (g2 c (.inr h))

/-- The twin's group reads, each one upstream's. -/
theorem groups_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex} :
    ∀ (l : List (Nat × Array Copy))
      {rs : List (Array (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit))}
      {s s' : AState}, Ctx pk s → LoadsOF s.store ld ldC → IndexRel s.store ix ixC →
      l.mapM (m := AM) (fun (x : Nat × Array Copy) => match x with
        | (i, cs) => ConRon.Arena.Frontend.Olean.readInfosOf (modelFs F) pk sp ld ix i cs) s
        = .ok (rs, s') →
      ParseStep s s' ∧ rs.length = l.length ∧ ∀ (j : Nat) (x : Nat × Array Copy)
        (arr : Array (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)),
        l[j]? = some x → rs[j]? = some arr →
        ∃ arrC, ModelIO.Gives (ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC x :
          ModelIO _) F (.ok arrC) ∧ ListRel (CopyInfoRel s'.store) arr.toList arrC.toList
  | [], rs, s, s', hctx, _, _, h => by
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, rfl, fun j x arr hx => by simp at hx⟩
  | (i, cs) :: l, rs, s, s', hctx, hld, hix, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨arr, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨rs', s₂, h2, h⟩ := AM.bind_ok h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    obtain ⟨hst1, arrC, hg, hr⟩ := readInfosOf_run hsp hctx hld hix h1
    obtain ⟨hst2, hlen, hall⟩ := groups_run hsp l (hctx.step hst1) (hld.ext hst1.ext)
      (hix.ext' hst1.ext) h2
    refine ⟨hst1.trans hst2, by simp [hlen], fun j x a hx ha => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx ha
      subst hx ha
      exact ⟨arrC, hg, listRel_ext (fun _ _ hq => hq.ext hst2.ext) hr⟩
    | succ j => exact hall j x a (by simpa using hx) (by simpa using ha)

theorem stmtSkel_det {r : ConLeche.Frontend.Olean.Region} {loc : Nat} {cv cv' : ConstantVal}
    {k k' : CKindF ConLeche.Name Unit} (h : ConLeche.Driver.StmtSkel r loc cv k)
    (h' : ConLeche.Driver.StmtSkel r loc cv' k') : cv = cv' ∧ k = k' := by
  obtain ⟨s, hs, h1, h2, h3, h4⟩ := h
  obtain ⟨s', hs', h1', h2', h3', h4'⟩ := h'
  rw [hs] at hs'; cases hs'
  rcases cv with ⟨a, b, c⟩
  rcases cv' with ⟨a', b', c'⟩
  simp only at h1 h2 h3 h1' h2' h3'
  rw [h1] at h1'; rw [h2] at h2'; rw [h3] at h3'; rw [h4] at h4'
  cases h1'; cases h2'; cases h3'; cases h4'
  exact ⟨rfl, rfl⟩

/-- An entry of a group the twin read: the group's, upstream's group read related. -/
theorem entry_group {F : FS} {sp : Roots} {st : EStore} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ixC : ConLeche.Frontend.Olean.NameIndex} {l : List (Nat × Array Copy)}
    {rs : List (Array (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit))}
    (hlen : rs.length = l.length)
    (hall : ∀ (j : Nat) (x : Nat × Array Copy)
      (arr : Array (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)),
      l[j]? = some x → rs[j]? = some arr →
      ∃ arrC, ModelIO.Gives (ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC x :
        ModelIO _) F (.ok arrC) ∧ ListRel (CopyInfoRel st) arr.toList arrC.toList)
    {r : Array (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)} (hr : r ∈ rs)
    {c : Copy} {v : ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit}
    (hm : (c, v) ∈ r.toList) :
    ∃ x arrC, (x ∈ l ∧ ModelIO.Gives (ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC x :
        ModelIO _) F (.ok arrC)) ∧ ListRel (CopyInfoRel st) r.toList arrC.toList ∧ c ∈ x.2.toList := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hj' : j < l.length := by rw [← hlen]; exact hj
  obtain ⟨arrC, hg, hrel⟩ := hall j l[j] rs[j] (List.getElem?_eq_getElem hj')
    (List.getElem?_eq_getElem hj)
  obtain ⟨y, hy, hyr⟩ := listRel_memL hrel hm
  obtain ⟨ok1, -⟩ := ConLeche.Driver.readInfosOf_ok (i := l[j].1) (cs := l[j].2)
    (show ModelIO.CanGive (ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC (l[j].1, l[j].2))
      F (.ok arrC) from hg.canGive)
  have hy' : (c, y.2.1, y.2.2) ∈ arrC.toList := by rw [show c = y.1 from hyr.1]; exact hy
  exact ⟨l[j], arrC, ⟨List.getElem_mem hj', hg⟩, hrel, (ok1 c _ _ hy').1⟩

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:99-106 readInfos — **the statements and kinds
of some copies, module by module: upstream's reads succeed on the snapshot, and agree with the
twin's at every requested copy** (`InfosRel`). -/
theorem readInfos_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    {cs : Array Copy}
    {infos : Std.HashMap Copy (ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)}
    {s s' : AState} (hctx : Ctx pk s) (hld : LoadsOF s.store ld ldC) (hix : IndexRel s.store ix ixC)
    (h : ConRon.Arena.Frontend.Olean.readInfos (modelFs F) pk sp ld ix cs s = .ok (infos, s')) :
    ParseStep s s' ∧ ∃ infosC, ModelIO.Gives (ConLeche.Frontend.Olean.readInfos (.ofPath sp) ldC ixC
        1 cs : ModelIO _) F (.ok infosC) ∧ InfosRel s'.store cs infos infosC := by
  unfold ConRon.Arena.Frontend.Olean.readInfos at h
  obtain ⟨rs, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hinf, hs⟩ := AM.pure_ok h2
  subst hs
  have hinf' : infos = rs.foldl (fun m r => r.foldl (fun m
      (x : Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit) => m.insert x.1 x.2) m) {} := by
    rw [hinf]
  subst hinf'
  obtain ⟨hst, hlen, hall⟩ := groups_run hsp _ hctx hld hix h1
  -- each upstream group is a twin group
  have hgr : ∀ x ∈ (ConLeche.Frontend.Olean.byModule cs).toList, ∃ arr arrC,
      arr ∈ rs ∧ ModelIO.Gives (ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC x :
        ModelIO _) F (.ok arrC) ∧ ListRel (CopyInfoRel s'.store) arr.toList arrC.toList := by
    intro x hx
    have hx' := byModule_sub (Array.mem_toList_iff.mp hx)
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem (Array.mem_toList_iff.mpr hx')
    have hj' : j < rs.length := by rw [hlen]; exact hj
    obtain ⟨arrC, hg, hr⟩ := hall j x rs[j] (by rw [List.getElem?_eq_getElem hj, hjx])
      (List.getElem?_eq_getElem hj')
    exact ⟨rs[j], arrC, List.getElem_mem hj', hg, hr⟩
  obtain ⟨rsC, hrsC⟩ := mapExcept_gives (f := ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC)
    _ (fun x hx => let ⟨_, arrC, _, hg, _⟩ := hgr x hx; ⟨arrC, hg⟩)
  let infosC : Std.HashMap Copy (ConstantVal × CKindF ConLeche.Name Unit) :=
    rsC.foldl (fun m r => r.foldl (fun m (x : Copy × ConstantVal × CKindF ConLeche.Name Unit) =>
      match x with | (c, s, k) => m.insert c (s, k)) m) {}
  have hgives : ModelIO.Gives (ConLeche.Frontend.Olean.readInfos (.ofPath sp) ldC ixC 1 cs :
      ModelIO _) F (.ok infosC) := by
    unfold ConLeche.Frontend.Olean.readInfos
    refine (show (CheckerIO.parMapExcept 1 (ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC)
      (ConLeche.Frontend.Olean.byModule cs).toList : ModelIO _).Gives F (.ok rsC) from hrsC).bind ?_
    exact ModelIO.gives_pure _ _
  obtain ⟨u1, u2⟩ := ConLeche.Driver.readInfos_ok hgives.canGive
  refine ⟨hst, infosC, hgives, ⟨fun c v hv => ?_, fun c hc => ?_⟩⟩
  · -- an entry of the twin's map: an entry of a group read, a requested copy
    rcases (infosFold rs {}).1 c v hv with ⟨r, hr, hm⟩ | hm
    · obtain ⟨x, arrC, ⟨hxl, -⟩, -, hc⟩ := entry_group hlen hall hr hm
      have := (byModule_mem (Array.mem_toList_iff.mp hxl)).1
      rw [this] at hc
      exact (List.mem_filter.mp hc).1
    · simp at hm
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (u2 c hc)
    obtain ⟨q, f, r, a, hq, hf, hreg, hsk⟩ := u1 c w hw
    -- the twin's map has an entry: the twin read the copy's group
    obtain ⟨g, hgm, hcg⟩ := (ConLeche.Driver.byModule_spec cs).2 c hc
    obtain ⟨arr, arrC, harr, hgv, hrel⟩ := hgr _ (Array.mem_toList_iff.mpr hgm)
    obtain ⟨-, ok2⟩ := ConLeche.Driver.readInfosOf_ok hgv.canGive
    obtain ⟨cv, k, hck⟩ := ok2 c hcg
    obtain ⟨x, hx, hxr⟩ := listRel_memR hrel hck
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((infosFold rs {}).2 c
      (.inl ⟨arr, harr, x.2, by rw [show c = x.1 from hxr.1.symm]; exact hx⟩))
    refine ⟨v, w, hv, hw, ?_⟩
    rcases (infosFold rs {}).1 c v hv with ⟨r', hr', hm⟩ | hm
    · obtain ⟨⟨i', g'⟩, arrC', ⟨hxl', hg'⟩, hrel', hc'⟩ := entry_group hlen hall hr' hm
      obtain ⟨y, hy, hyr⟩ := listRel_memL hrel' hm
      obtain ⟨ok1, -⟩ := ConLeche.Driver.readInfosOf_ok (i := i') (cs := g')
        (show ModelIO.CanGive (ConLeche.Frontend.Olean.readInfosOf (.ofPath sp) ldC ixC (i', g')) F
          (.ok arrC') from hg'.canGive)
      have hy' : (c, y.2.1, y.2.2) ∈ arrC'.toList := by rw [show c = y.1 from hyr.1]; exact hy
      obtain ⟨-, q', f', r'', a', hq', hf', hreg', hsk'⟩ := ok1 c y.2.1 y.2.2 hy'
      have hmod : c.mod = i' := by
        have := (byModule_mem (Array.mem_toList_iff.mp hxl')).1
        rw [this] at hc'
        simpa using (List.mem_filter.mp hc').2
      subst hmod
      rw [hq] at hq'; cases hq'
      obtain rfl := ConLeche.Driver.readFiles_unique_at hf hf'
      rw [hreg] at hreg'; cases hreg'
      obtain ⟨e1, e2⟩ := stmtSkel_det hsk hsk'
      exact ⟨e1 ▸ hyr.2.1, e2 ▸ hyr.2.2⟩
    · simp at hm

end ConRon.Bridge.Modular
