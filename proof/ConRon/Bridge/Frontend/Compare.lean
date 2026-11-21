/-
# `ConRon.Bridge.Frontend.Compare` — Theorem 1 for a compared run's pure parts (task #165)

The twin's `recKey` is upstream's `Driver.recKey` at the record's denotation (`recKey_denote`);
the twin's homes of a closure (`homesOf`, over handles) denote upstream's `homesOf` of the loaded
modules (`homesOf_den`); and where the twin finds no foreign `--constant` name (`foreignOf` is
`none`), upstream's `foreignConstant` finds none either (`foreignOf_none`), which is what
`compareG_accept` reads (`foreignConstant_none`).
-/
module

public import ConRon.Arena.Frontend.Compare
public import ConRon.Arena.Frontend.Olean.Records
public import ConRon.Bridge.Frontend.Olean.Closure
public import ConRon.Bridge.Frontend.Olean.Merge
public import ConLeche.Driver.Compare

public section

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The name a record is found under -/

theorem denoteCV_name {st : EStore} {cv : IConstantVal} {x : ConstantVal}
    (h : ConRon.Arena.Frontend.denoteCV st cv = some x) : denoteN st.ns cv.name = some x.name := by
  unfold ConRon.Arena.Frontend.denoteCV at h
  split at h
  · rename_i n lps ty hn _ _
    cases h
    exact hn
  · cases h

theorem denoteCI_name {st : EStore} {c : IConstantInfo} {x : ConstantInfo}
    (h : ConRon.Arena.Frontend.denoteCI st c = some x) :
    denoteN st.ns c.name = some x.toConstantVal.name := by
  cases c <;> simp only [ConRon.Arena.Frontend.denoteCI] at h <;>
    first
    | (obtain ⟨cv, hcv, rfl⟩ := Option.map_eq_some_iff.mp h
       exact denoteCV_name hcv)
    | (split at h
       · rename_i cv _ hcv _
         cases h
         exact denoteCV_name hcv
       · cases h)

/-- con-leche: ConLeche/Driver/Compare.lean:48-52 recKey — **the twin's `recKey` is upstream's**
at the record's denotation (`none`: upstream's `.anonymous`, a block with no type). -/
theorem recKey_denote {st : EStore} {d : IDeclaration} {dP : Declaration}
    (h : ConRon.Arena.Frontend.denoteDecl st d = some dP) :
    match ConRon.Arena.Frontend.recKey d with
    | some n => denoteN st.ns n = some (ConLeche.Driver.recKey dP)
    | none => ConLeche.Driver.recKey dP = .anonymous := by
  cases d with
  | axiomDecl cv | quotDecl _ cv =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact denoteCV_name hx
  | defnDecl cv _ _ | thmDecl cv _ | opaqueDecl cv _ =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at h
    split at h
    · rename_i x _ hx _
      cases h
      exact denoteCV_name hx
    · cases h
  | indDecl b nP =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at h
    obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
    cases b with
    | nil =>
      simp only [ConRon.Arena.Frontend.denoteCIList] at hxs
      cases hxs
      rfl
    | cons c cs =>
      simp only [ConRon.Arena.Frontend.denoteCIList] at hxs
      split at hxs
      · rename_i x xs' hx _
        cases hxs
        exact denoteCI_name hx
      · cases hxs

/-! ## The homes -/

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:76-81 homesOf — **the twin's homes denote
upstream's**: a name with a home is a handle with a home, both ways, the homes denoting alike. -/
@[expose] def HomesDen (ns : NStore) (h : Std.HashMap NIdx NIdx)
    (hC : Std.HashMap ConLeche.Name ConLeche.Name) : Prop :=
  (∀ n m, h[n]? = some m → ∃ nC mC, denoteN ns n = some nC ∧ denoteN ns m = some mC ∧
      hC[nC]? = some mC) ∧
    (∀ nC mC, hC[nC]? = some mC → ∃ n m, denoteN ns n = some nC ∧ h[n]? = some m ∧
      denoteN ns m = some mC)

theorem HomesDen.empty (ns : NStore) : HomesDen ns {} {} :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem HomesDen.ext {st st' : EStore} {h : Std.HashMap NIdx NIdx}
    {hC : Std.HashMap ConLeche.Name ConLeche.Name} (hd : HomesDen st.ns h hC) (hx : Ext st st') :
    HomesDen st'.ns h hC :=
  ⟨fun n m hn => let ⟨nC, mC, h1, h2, h3⟩ := hd.1 n m hn
      ⟨nC, mC, denoteN_ext h1 hx, denoteN_ext h2 hx, h3⟩,
   fun nC mC hn => let ⟨n, m, h1, h2, h3⟩ := hd.2 nC mC hn
      ⟨n, m, denoteN_ext h1 hx, h2, denoteN_ext h3 hx⟩⟩

theorem HomesDen.contains {ns : NStore} (hwf : NStoreWF ns) {h : Std.HashMap NIdx NIdx}
    {hC : Std.HashMap ConLeche.Name ConLeche.Name} (hd : HomesDen ns h hC) {n : NIdx}
    {nC : ConLeche.Name} (hn : denoteN ns n = some nC) : h.contains n = hC.contains nC := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?]
  cases hx : h[n]? with
  | some m =>
    obtain ⟨nC', mC, hn', -, hc⟩ := hd.1 n m hx
    rw [hn] at hn'
    cases hn'
    rw [hc]; rfl
  | none =>
    cases hy : hC[nC]? with
    | none => rfl
    | some mC =>
      obtain ⟨n', m, hn', hx', -⟩ := hd.2 nC mC hy
      rw [denoteN_inj hwf hn' hn, hx] at hx'
      cases hx'

theorem HomesDen.insert {ns : NStore} (hwf : NStoreWF ns) {h : Std.HashMap NIdx NIdx}
    {hC : Std.HashMap ConLeche.Name ConLeche.Name} (hd : HomesDen ns h hC) {n m : NIdx}
    {nC mC : ConLeche.Name} (hn : denoteN ns n = some nC) (hm : denoteN ns m = some mC) :
    HomesDen ns (h.insert n m) (hC.insert nC mC) := by
  refine ⟨fun k v hk => ?_, fun kC vC hk => ?_⟩
  · rw [Std.HashMap.getElem?_insert] at hk
    by_cases e : (n == k) = true
    · rw [ite_eq_left e] at hk
      cases hk
      obtain rfl := beq_iff_eq.mp e
      exact ⟨nC, mC, hn, hm, by simp⟩
    · rw [ite_eq_right e] at hk
      obtain ⟨kC, vC, hk1, hk2, hk3⟩ := hd.1 k v hk
      refine ⟨kC, vC, hk1, hk2, ?_⟩
      rw [Std.HashMap.getElem?_insert, ite_eq_right]
      · exact hk3
      · intro e'
        apply e
        rw [beq_iff_eq.mp e'] at hn
        exact beq_iff_eq.mpr (denoteN_inj hwf hn hk1)
  · rw [Std.HashMap.getElem?_insert] at hk
    by_cases e : (nC == kC) = true
    · rw [ite_eq_left e] at hk
      cases hk
      obtain rfl := beq_iff_eq.mp e
      exact ⟨n, m, hn, by simp, hm⟩
    · rw [ite_eq_right e] at hk
      obtain ⟨k, v, hk1, hk2, hk3⟩ := hd.2 kC vC hk
      refine ⟨k, v, hk1, ?_, hk3⟩
      rw [Std.HashMap.getElem?_insert, ite_eq_right]
      · exact hk2
      · intro e'
        apply e
        rw [← beq_iff_eq.mp e', hn] at hk1
        exact beq_iff_eq.mpr (Option.some.inj hk1)

theorem denoteCEntry_name {st : EStore} {c : ConRon.Arena.Frontend.Olean.CEntry}
    {z : ConLeche.Frontend.Olean.CEntry} (h : Olean.denoteCEntry st c = some z) :
    denoteN st.ns c.c.name = some z.name :=
  (Olean.denoteCEntry_parts h).1

/-- One module's constants, folded into the homes. -/
theorem homes_inner_den {st : EStore} (hwf : NStoreWF st.ns) {m : NIdx} {mC : ConLeche.Name}
    (hm : denoteN st.ns m = some mC) :
    ∀ (cs : List ConRon.Arena.Frontend.Olean.CEntry) {csC : List ConLeche.Frontend.Olean.CEntry}
      {h : Std.HashMap NIdx NIdx} {hC : Std.HashMap ConLeche.Name ConLeche.Name},
      cs.mapM (Olean.denoteCEntry st) = some csC → HomesDen st.ns h hC →
      HomesDen st.ns (cs.foldl (fun h c => if h.contains c.c.name then h else h.insert c.c.name m) h)
        (csC.foldl (fun h c => if h.contains c.name then h else h.insert c.name mC) hC)
  | [], csC, h, hC, hcs, hd => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at hcs
    subst hcs
    exact hd
  | c :: cs, csC, h, hC, hcs, hd => by
    simp only [List.mapM_cons] at hcs
    cases hz : Olean.denoteCEntry st c with
    | none => simp [hz, bind, Option.bind] at hcs
    | some z =>
      cases hzs : cs.mapM (Olean.denoteCEntry st) with
      | none => simp [hz, hzs, bind, Option.bind] at hcs
      | some zs =>
        simp only [hz, hzs, bind, Option.bind, pure, Option.some.injEq] at hcs
        subst hcs
        have hn := denoteCEntry_name hz
        simp only [List.foldl_cons]
        refine homes_inner_den hwf hm cs hzs ?_
        rw [hd.contains hwf hn]
        split
        · exact hd
        · exact hd.insert hwf hn hm

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:76-81 homesOf — **the twin's homes of loaded
modules denote upstream's homes of their denotations.** -/
theorem homesOf_den {st : EStore} (hwf : NStoreWF st.ns) :
    ∀ {ls : List ConRon.Arena.Frontend.Olean.Loaded} {lsC : List ConLeche.Frontend.Olean.Loaded},
      ListRel (Olean.LoadedRel st) ls lsC →
      ∀ {h : Std.HashMap NIdx NIdx} {hC : Std.HashMap ConLeche.Name ConLeche.Name},
        HomesDen st.ns h hC →
        HomesDen st.ns (ls.foldl (fun h l => l.constants.foldl (fun h c =>
            if h.contains c.c.name then h else h.insert c.c.name l.name) h) h)
          (lsC.foldl (fun h l => l.constants.foldl (fun h c =>
            if h.contains c.name then h else h.insert c.name l.name) h) hC)
  | _, _, .nil, _, _, hd => hd
  | _, _, .cons hl hrest, _, _, hd => by
    simp only [List.foldl_cons]
    refine homesOf_den hwf hrest ?_
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    exact homes_inner_den hwf hl.name _ hl.constants hd

/-- **The twin's `homesOf` denotes upstream's**, on related loads. -/
theorem homesOf_denote {st : EStore} (hwf : NStoreWF st.ns)
    {ls : Array ConRon.Arena.Frontend.Olean.Loaded} {lsC : List ConLeche.Frontend.Olean.Loaded}
    (hls : ListRel (Olean.LoadedRel st) ls.toList lsC) :
    HomesDen st.ns (ConRon.Arena.Frontend.Olean.homesOf ls)
      (ConLeche.Frontend.Olean.homesOf lsC.toArray) := by
  unfold ConRon.Arena.Frontend.Olean.homesOf ConLeche.Frontend.Olean.homesOf
  rw [← Array.foldl_toList, ← Array.foldl_toList, List.toList_toArray]
  exact homesOf_den hwf hls (HomesDen.empty _)

/-! ## A `--constant` name of another module -/

/-- con-leche: ConLeche/Verify/Driver/CompareRun.lean:74 foreignConstant_none — **where the twin
finds no foreign `--constant` name, upstream finds none**: the request's names and challenge
denoting the twin's handles, and the homes the twin's. -/
theorem foreignOf_none {ns : NStore} {cs : Option (Array NIdx)} {ch : NIdx}
    {homes : Std.HashMap NIdx NIdx} {homesC : Std.HashMap ConLeche.Name ConLeche.Name}
    {r : ConLeche.Driver.CmpReq}
    (hcs : r.constants = cs.map fun a => (a.toList.filterMap (denoteN ns)).toArray)
    (hch : denoteN ns ch = some r.challenge) (hd : HomesDen ns homes homesC)
    (h : ConRon.Arena.Frontend.foreignOf cs ch homes = none) :
    ConLeche.Driver.foreignConstant r homesC = none := by
  unfold ConLeche.Driver.foreignConstant
  rw [hcs]
  cases cs with
  | none => rfl
  | some a =>
    simp only [ConRon.Arena.Frontend.foreignOf, Option.bind_some] at h
    have hall := Array.find?_eq_none.mp h
    have hnone : ((a.toList.filterMap (denoteN ns)).toArray.find?
        (homesC[·]? != some r.challenge)) = none := by
      apply Array.find?_eq_none.mpr
      intro xC hx
      simp only [List.mem_toArray, List.mem_filterMap] at hx
      obtain ⟨n, hn, hnx⟩ := hx
      have hf := hall n (by simpa using hn)
      simp only [ConRon.Arena.Frontend.foreignAt, bne_iff_ne, ne_eq, Decidable.not_not] at hf
      obtain ⟨nC, mC, h1, h2, h3⟩ := hd.1 n ch hf
      rw [h1] at hnx
      cases hnx
      rw [hch] at h2
      cases h2
      simp [h3]
    simp [Option.map_some, bind, Option.bind, hnone]

end ConRon.Bridge.Frontend
