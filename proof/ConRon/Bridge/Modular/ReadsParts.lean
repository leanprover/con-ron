/-
# `ConRon.Bridge.Modular.ReadsParts` — a part's names, statements and kinds, Theorem 1 (task #166)

The reads the worker makes of a loaded part before its own records, each the twin's accept read
back as upstream's: the name positions (`namePositionsAt_run`, `readNamePositions_run`,
`readPartNames_run` at `ModelIO`), the statements of some constants (`stmtsAt_run`, over the
passes' memo, upstream's `stmtsAt_eq`), their kinds with the expressions left out
(`kindNamesAt_run`, over the sparse read).  Run style (simulations), not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.Rel
public import ConRon.Bridge.Frontend.Olean.Sparse
public import ConRon.Bridge.Frontend.Olean.Parse
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Sparse

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins)
open ConLeche.Frontend.Olean (Region CEntryF CKindF ImportF ImportRec Roots OLeanLevel ModFiles
  constSkel moduleSkel nameP exprP distinctGo)

/-! ## The name positions -/

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:71-74 namePosition -/
theorem namePosition_run {pk : OleanPins} {r : Region} {c : Nat}
    {q : ConRon.Arena.Frontend.Olean.NamePosition} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.namePosition pk r c s = .ok (some q, s')) :
    ParseStep s s' ∧ ∃ qC, ConLeche.Frontend.Olean.namePosition r c = some qC ∧
      NPRel s'.store q qC := by
  unfold ConRon.Arena.Frontend.Olean.namePosition at h
  unfold ConLeche.Frontend.Olean.namePosition
  cases hsk : constSkel r c with
  | none => simp only [hsk] at h; exact (none_not_some h).elim
  | some sk =>
    simp only [hsk] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none => exact (none_not_some h2).elim
    | some n =>
      obtain ⟨hv, rfl⟩ := AM.pure_ok h2
      cases hv
      obtain ⟨hst, z, hz, hd⟩ := nameP_run hctx.ok hctx.nulls h1
      exact ⟨hst, ⟨c, z, sk.kind.tag, sk.kind.skipped⟩, by simp [bind, Option.bind, hz],
        ⟨rfl, hd, rfl, rfl⟩⟩

theorem NPRel.ext {st st' : EStore} (hx : Ext st st') {q : ConRon.Arena.Frontend.Olean.NamePosition}
    {qC : ConLeche.Frontend.Olean.NamePosition} (h : NPRel st q qC) : NPRel st' q qC :=
  ⟨h.loc, denoteN_ext h.name hx, h.tag, h.skipped⟩

theorem listRel_ext {α β : Type} {R R' : α → β → Prop} (hr : ∀ a b, R a b → R' a b) :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → ListRel R' l l'
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hr _ _ h) (listRel_ext hr t)

theorem listRel_append {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {m : List α} {m' : List β}, ListRel R l l' → ListRel R m m' →
      ListRel R (l ++ m) (l' ++ m')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a t, h => .cons a (listRel_append t h)

theorem NPsRel.ext {st st' : EStore} (hx : Ext st st') {p : ConRon.Arena.Frontend.Olean.NamePositions}
    {pC : ConLeche.Frontend.Olean.NamePositions} (h : NPsRel st p pC) : NPsRel st' p pC :=
  ⟨h.isModule, h.imports.ext hx, listRel_ext (fun _ _ hq => hq.ext hx) h.consts⟩

/-- A list of positions related one by one: the name lists denote one another. -/
theorem names_mapM {st : EStore} :
    ∀ {l : List ConRon.Arena.Frontend.Olean.NamePosition} {lC : List ConLeche.Frontend.Olean.NamePosition},
      ListRel (NPRel st) l lC → (l.map (·.name)).mapM (denoteN st.ns) = some (lC.map (·.name))
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    simp only [List.map_cons, List.mapM_cons, h.name, names_mapM t]; rfl

/-- Handle lists that denote name lists: one is without duplicates iff the other is. -/
theorem nodup_iff_of_mapM {st : EStore} (hw : NStoreWF st.ns) :
    ∀ {l : List NIdx} {zs : List ConLeche.Name}, l.mapM (denoteN st.ns) = some zs →
      (l.Nodup ↔ zs.Nodup)
  | [], zs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; simp
  | x :: l, zs, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    obtain ⟨ys, hys, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    have ih := nodup_iff_of_mapM hw hys
    simp only [List.nodup_cons, ih]
    constructor
    · rintro ⟨hm, hn⟩
      refine ⟨fun hy' => hm ?_, hn⟩
      obtain ⟨x', hx', hd⟩ := mem_of_mapM hys hy'
      rw [denoteN_inj hw hy hd]; exact hx'
    · rintro ⟨hm, hn⟩
      refine ⟨fun hx => hm ?_, hn⟩
      obtain ⟨y', hy', hd⟩ := mem_of_mapM' hys hx
      rw [hy] at hd
      cases hd
      exact hy'
where
  mem_of_mapM {l : List NIdx} {ys : List ConLeche.Name} (h : l.mapM (denoteN st.ns) = some ys)
      {y : ConLeche.Name} (hy : y ∈ ys) : ∃ x ∈ l, denoteN st.ns x = some y := by
    induction l generalizing ys with
    | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; cases hy
    | cons a l ih =>
      simp only [List.mapM_cons] at h
      obtain ⟨b, hb, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
      obtain ⟨bs, hbs, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
      simp only [pure, Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, List.mem_cons_self, hb⟩
      · obtain ⟨x, hx, hd⟩ := ih hbs hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hd⟩
  mem_of_mapM' {l : List NIdx} {ys : List ConLeche.Name} (h : l.mapM (denoteN st.ns) = some ys)
      {x : NIdx} (hx : x ∈ l) : ∃ y ∈ ys, denoteN st.ns x = some y := by
    induction l generalizing ys with
    | nil => cases hx
    | cons a l ih =>
      simp only [List.mapM_cons] at h
      obtain ⟨b, hb, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
      obtain ⟨bs, hbs, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
      simp only [pure, Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, List.mem_cons_self, hb⟩
      · obtain ⟨y, hy, hd⟩ := ih hbs hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hd⟩

/-- con-leche: none — a name position read back, as a function. -/
@[expose] def denoteNP (st : EStore) (q : ConRon.Arena.Frontend.Olean.NamePosition) :
    Option ConLeche.Frontend.Olean.NamePosition :=
  (denoteN st.ns q.name).map fun n => ⟨q.loc, n, q.tag, q.skipped⟩

theorem npRel_of_denoteNP {st : EStore} {q : ConRon.Arena.Frontend.Olean.NamePosition}
    {qC : ConLeche.Frontend.Olean.NamePosition} (h : denoteNP st q = some qC) : NPRel st q qC := by
  unfold denoteNP at h
  cases hn : denoteN st.ns q.name with
  | none => rw [hn] at h; cases h
  | some n =>
    rw [hn] at h
    cases h
    exact ⟨rfl, hn, rfl, rfl⟩

theorem listRel_of_mapM' {α β : Type} {f : α → Option β} {R : α → β → Prop}
    (hR : ∀ a b, f a = some b → R a b) :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → ListRel R l ys :=
  fun h => listRel_ext hR (listRel_of_mapM h)

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:76-84 namePositionsAt — **the twin's name
positions are upstream's**, read back. -/
theorem namePositionsAt_run {pk : OleanPins} {r : Region} {root : UInt64}
    {p : ConRon.Arena.Frontend.Olean.NamePositions} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.namePositionsAt pk r root s = .ok (some p, s')) :
    ParseStep s s' ∧ ∃ pC, ConLeche.Frontend.Olean.namePositionsAt r root = some pC ∧
      NPsRel s'.store p pC := by
  unfold ConRon.Arena.Frontend.Olean.namePositionsAt at h
  unfold ConLeche.Frontend.Olean.namePositionsAt
  cases hsk : moduleSkel r root with
  | none => simp only [hsk] at h; exact (none_not_some h).elim
  | some sk =>
  simp only [hsk] at h
  obtain ⟨imps, s₁, h1, h⟩ := OT.bind_ok h
  obtain ⟨cs, s₂, h2, h⟩ := OT.bind_ok h
  obtain ⟨hst1, zs, hzs, hds⟩ := optT_list_run (pk := pk) (den := denoteImport)
    (g := ImportF.mapM (nameP r)) (fun hx hy => denoteImport_ext hx hy)
    (fun i s s' y hctx hrun => by
      obtain ⟨q, s₂, h3, h4⟩ := OT.bind_ok hrun
      obtain ⟨hv', hs'⟩ := AM.pure_ok h4
      cases hv'
      subst hs'
      obtain ⟨hst, z, hz, hd⟩ := nameP_run hctx.ok hctx.nulls h3
      refine ⟨hst, { i with module := z }, ?_, ?_⟩
      · simp only [ImportF.mapM, hz]; rfl
      · simp only [denoteImport, ImportF.mapM, hd]; rfl) sk.imports hctx h1
  have hctx₁ := hctx.step hst1
  obtain ⟨hst2, qs, hqs, hdq⟩ := optT_list_run (pk := pk) (den := denoteNP)
    (g := ConLeche.Frontend.Olean.namePosition r)
    (fun {st st' y z} hx hy => by
      unfold denoteNP at hy ⊢
      cases hn : denoteN st.ns y.name with
      | none => rw [hn] at hy; cases hy
      | some n => rw [hn] at hy; rw [denoteN_ext hn hx]; exact hy)
    (fun c s s' y hctx hrun => by
      obtain ⟨hst, qC, hq, hrel⟩ := namePosition_run hctx hrun
      refine ⟨hst, qC, hq, ?_⟩
      simp only [denoteNP, hrel.name, Option.map_some]
      rw [hrel.loc, hrel.tag, hrel.skipped])
    sk.consts hctx₁ h2
  have hrelq : ListRel (NPRel s₂.store) cs qs := listRel_of_mapM' (fun _ _ => npRel_of_denoteNP) hdq
  have hw := nsWF_of_StateOK hst2.ok
  split at h
  · rename_i hdist
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    refine ⟨hst1.trans hst2, ⟨⟨sk.isModule, zs.toArray⟩, qs.toArray⟩, ?_, ?_⟩
    · have hnd : (cs.map (·.name)).Nodup :=
        ((ConLeche.Frontend.Olean.distinctGo_iff _ _).mp hdist).1
      have hnd' : (qs.map (·.name)).Nodup := (nodup_iff_of_mapM hw (names_mapM hrelq)).mp hnd
      have hdC : distinctGo (qs.map (·.name)) (Std.HashSet.emptyWithCapacity qs.length) = true :=
        (ConLeche.Frontend.Olean.distinctGo_iff _ _).mpr ⟨hnd', fun _ _ => by simp⟩
      simp [hzs, hqs, hdC]
    · exact ⟨rfl, by simpa [ImpsD] using
        (mapM_denoteImport_ext' hst2.ext hds), by simpa using hrelq⟩
  · exact (none_not_some (show (pure none : AM (Option ConRon.Arena.Frontend.Olean.NamePositions)) s₂ =
      .ok (some p, s') from h)).elim

/-! ## The statements -/

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:348-351 stmtsFast — the statements off the
memo, read back, the memo's answers upstream's at every root. -/
theorem stmtsOf_memo {pk : OleanPins} {r : Region} {st : EStore}
    {memo : ConRon.Arena.Frontend.Olean.DS} :
    ∀ (sks : List (CEntryF UInt64 UInt64)) {ys : List ConRon.Arena.Frontend.Olean.StmtRec},
      (∀ s ∈ sks, ∀ v ∈ s.name :: s.levelParams, ∀ y, memo.nameOf pk r v = some y →
        ∃ z, nameP r v = some z ∧ denoteN st.ns y = some z) →
      (∀ s ∈ sks, ∀ y, memo.exprOf r s.type = some y →
        ∃ z, exprP r s.type = some z ∧ denoteE st y = some z) →
      (sks.mapM fun s => do
        pure (⟨← memo.nameOf pk r s.name, ← s.levelParams.mapM (memo.nameOf pk r),
          ← memo.exprOf r s.type⟩ : ConRon.Arena.Frontend.Olean.StmtRec)) = some ys →
      ∃ zs, sks.mapM (ConLeche.Frontend.Olean.stmtP r) = some zs ∧
        ys.mapM (denoteStmt st) = some zs := by
  intro sks ys hN hE h
  refine list_sim sks h fun sk hsk y hy => ?_
  obtain ⟨n, hn, hy⟩ := ConLeche.Frontend.Olean.bind_some_left hy
  obtain ⟨ls, hls, hy⟩ := ConLeche.Frontend.Olean.bind_some_left hy
  obtain ⟨e, he, hy⟩ := ConLeche.Frontend.Olean.bind_some_left hy
  simp only [pure, Option.some.injEq] at hy
  subst hy
  obtain ⟨zn, h1, h1'⟩ := hN sk hsk sk.name List.mem_cons_self n hn
  obtain ⟨zl, h2, h2'⟩ := list_sim sk.levelParams hls
    (fun v hv => hN sk hsk v (List.mem_cons_of_mem _ hv))
  obtain ⟨ze, h3, h3'⟩ := hE sk hsk e he
  refine ⟨⟨zn, zl, ze⟩, ?_, ?_⟩
  · simp [ConLeche.Frontend.Olean.stmtP, h1, h2, h3, bind, Option.bind, pure]
  · simp [denoteStmt, h1', h2', h3', bind, Option.bind, pure]

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:90-92 stmtsAt — **the statements of some
constants, read together, are upstream's**, read back. -/
theorem stmtsAt_run {pk : OleanPins} {r : Region} {cs : List Nat}
    {ys : List ConRon.Arena.Frontend.Olean.StmtRec} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.stmtsAt pk r cs s = .ok (some ys, s')) :
    ParseStep s s' ∧ ∃ zs, ConLeche.Frontend.Olean.stmtsAt r cs = some zs ∧
      ys.mapM (denoteStmt s'.store) = some zs := by
  unfold ConRon.Arena.Frontend.Olean.stmtsAt at h
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
  cases o with
  | none => exact (none_not_some h2).elim
  | some sks =>
  obtain ⟨rfl, hsks⟩ := constsSkel_run cs h1
  unfold ConRon.Arena.Frontend.Olean.stmtsFast at h2
  obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
  unfold ConRon.Arena.Frontend.Olean.runPasses at h3
  obtain ⟨o', s₃, h5, h6⟩ := AM.bind_ok h3
  rcases o' with _ | ⟨nm, ms, memo⟩
  · obtain ⟨hv, rfl⟩ := AM.pure_ok h6
    cases hv
    exact (none_not_some h4).elim
  obtain ⟨hv, rfl⟩ := AM.pure_ok h6
  cases hv
  obtain ⟨hv, rfl⟩ := AM.pure_ok h4
  obtain ⟨hst, hN, hE, -⟩ := runMarked_run hctx h5
  obtain ⟨zs, hzs, hds⟩ := stmtsOf_memo sks
    (fun sk hsk v hv y hy => hN v (List.mem_flatMap.mpr ⟨sk, hsk, hv⟩) y hy)
    (fun sk hsk y hy => hE sk.type (List.mem_map_of_mem hsk) y hy) hv.symm
  refine ⟨hst, zs, ?_, hds⟩
  simp only [ConLeche.Frontend.Olean.stmtsAt, hsks]
  show ConLeche.Frontend.Olean.stmtsFast r sks = some zs
  rw [ConLeche.Frontend.Olean.stmtsFast_eq]
  exact hzs

/-! ## The kinds -/

theorem recur_mapM {m : Type → Type} [Monad m] {N E N' E' : Type} (fn : N → m N') (fe : E → m E')
    (all : List N) (np ni nmo nmi : Nat) (rules : List (N × Nat × E)) (kk iu : Bool) :
    (CKindF.recur all np ni nmo nmi rules kk iu).mapM fn fe = (do
      let all ← all.mapM fn
      let rules ← rules.mapM (fun x => do
        let c ← fn x.1
        let e ← fe x.2.2
        pure (c, x.2.1, e))
      pure (CKindF.recur all np ni nmo nmi rules kk iu)) := rfl

theorem mapM_denoteN_ext {st st' : EStore} (hx : Ext st st') {l : List NIdx}
    {zs : List ConLeche.Name} (h : l.mapM (denoteN st.ns) = some zs) :
    l.mapM (denoteN st'.ns) = some zs :=
  list_mono (fun _ _ hy => denoteN_ext hy hx) l h

theorem OT.pure_ok {α : Type} {a b : α} {s s' : AState}
    (h : (pure a : OptionT AM α) s = .ok (some b, s')) : b = a ∧ s' = s := by
  have h' : (pure (some a) : AM (Option α)) s = .ok (some b, s') := h
  obtain ⟨hv, hs⟩ := AM.pure_ok h'
  cases hv
  exact ⟨rfl, hs⟩

/-- A name list read in `OptionT AM`, each name upstream's, read back. -/
theorem names_run {pk : OleanPins} {fn : UInt64 → AM (Option NIdx)} {gn : UInt64 → Option ConLeche.Name}
    (hstep : ∀ a s s' y, Ctx pk s → fn a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (l : List UInt64) {ys : List NIdx} {s s' : AState} (hctx : Ctx pk s)
    (h : l.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) s = .ok (some ys, s')) :
    ParseStep s s' ∧ ∃ zs, l.mapM gn = some zs ∧ ys.mapM (denoteN s'.store.ns) = some zs :=
  optT_list_run (pk := pk) (den := fun st => denoteN st.ns) (g := gn)
    (fun hx hy => denoteN_ext hy hx) (fun a s s' y hctx h => hstep a s s' y hctx h) l hctx h

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:275-296 CKindF.mapM — **a kind's names read
one by one, its expressions left out**, upstream's, read back. -/
theorem kindNames_run {pk : OleanPins} {fn : UInt64 → AM (Option NIdx)}
    {gn : UInt64 → Option ConLeche.Name}
    (hstep : ∀ a s s' y, Ctx pk s → fn a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (k : CKindF UInt64 UInt64) {kr : CKindF NIdx Unit} {s s' : AState} (hctx : Ctx pk s)
    (h : (k.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) (fun _ => pure ())) s
      = .ok (some kr, s')) :
    ParseStep s s' ∧ ∃ kC, k.mapM gn (fun _ => some ()) = some kC ∧
      denoteKindN s'.store kr = some kC := by
  cases k with
  | ax u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | quot u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | defn v hh sf =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h1
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | opaq v u =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h1
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | thm v all =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h1
    obtain ⟨ns, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst, zs, hz, hd⟩ := names_run hstep all hctx h3
    refine ⟨hst, .thm () zs, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [denoteKindN, CKindF.mapM, hd, bind, Option.bind, pure]
  | induct np ni all cs nn ir iu irf =>
    simp only [CKindF.mapM] at h
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨bs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := names_run hstep all hctx h1
    obtain ⟨hst2, ws, hw, hdw⟩ := names_run hstep cs (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .induct np ni zs ws nn ir iu irf, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hw, bind, Option.bind, pure]
    · have hd' := mapM_denoteN_ext hst2.ext hd
      simp [denoteKindN, CKindF.mapM, hd', hdw, bind, Option.bind, pure]
  | ctor ind ci np nf iu =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := hstep ind s _ a hctx h1
    refine ⟨hst, .ctor z ci np nf iu, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [denoteKindN, CKindF.mapM, hd, bind, Option.bind, pure]
  | recur all np ni nmo nmi rules kk iu =>
    rw [recur_mapM] at h ⊢
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := names_run hstep all hctx h1
    obtain ⟨hst2, ws, hw, hdw⟩ := optT_list_run (pk := pk)
      (den := fun st (x : NIdx × Nat × Unit) => do
        let c ← denoteN st.ns x.1
        let e ← (fun _ => some ()) x.2.2
        pure (c, x.2.1, e))
      (g := fun (x : UInt64 × Nat × UInt64) => do
        let c ← gn x.1
        let e ← (fun _ => some ()) x.2.2
        pure (c, x.2.1, e))
      (fun {st st' y z} hx hy => by
        cases hn : denoteN st.ns y.1 with
        | none => simp [hn] at hy
        | some n => simp only [hn] at hy; simp only [denoteN_ext hn hx]; exact hy)
      (fun x s s' y hctx hrun => by
        obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok hrun
        obtain ⟨b, s₂, h3, h4⟩ := OT.bind_ok h2
        obtain ⟨rfl, rfl⟩ := OT.pure_ok h3
        obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
        obtain ⟨hst, z, hz, hd⟩ := hstep x.1 s _ a hctx h1
        exact ⟨hst, (z, x.2.1, ()), by simp [hz], by simp [hd]⟩) rules (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .recur zs np ni nmo nmi ws kk iu, ?_, ?_⟩
    · rw [hz, hw]; rfl
    · have hd' := mapM_denoteN_ext hst2.ext hd
      rw [denoteKindN, recur_mapM, hd', hdw]; rfl

theorem denoteKindN_ext {st st' : EStore} (hx : Ext st st') {k : CKindF NIdx Unit}
    {kC : CKindF ConLeche.Name Unit} (h : denoteKindN st k = some kC) : denoteKindN st' k = some kC := by
  have hl : ∀ (l : List NIdx) {ys : List ConLeche.Name}, l.mapM (denoteN st.ns) = some ys →
      l.mapM (denoteN st'.ns) = some ys := fun l _ h => mapM_denoteN_ext hx h
  unfold denoteKindN at h ⊢
  cases k with
  | ax u => exact h
  | quot u => exact h
  | defn v hh sf => exact h
  | opaq v u => exact h
  | thm v all =>
    simp only [CKindF.mapM, bind, Option.bind] at h ⊢
    cases ha : all.mapM (denoteN st.ns) with
    | none => rw [ha] at h; cases h
    | some as => rw [ha] at h; rw [hl all ha]; exact h
  | induct np ni all cs nn ir iu irf =>
    simp only [CKindF.mapM, bind, Option.bind] at h ⊢
    cases ha : all.mapM (denoteN st.ns) with
    | none => rw [ha] at h; cases h
    | some as =>
      rw [ha] at h; rw [hl all ha]
      cases hc : cs.mapM (denoteN st.ns) with
      | none => rw [hc] at h; cases h
      | some bs => rw [hc] at h; rw [hl cs hc]; exact h
  | ctor ind ci np nf iu =>
    simp only [CKindF.mapM, bind, Option.bind] at h ⊢
    cases hi : denoteN st.ns ind with
    | none => rw [hi] at h; cases h
    | some n => rw [hi] at h; rw [denoteN_ext hi hx]; exact h
  | recur all np ni nmo nmi rules kk iu =>
    rw [recur_mapM] at h ⊢
    obtain ⟨as, ha, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    obtain ⟨ws, hws, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    rw [hl all ha, list_mono (fun x y hy => by
      cases hn : denoteN st.ns x.1 with
      | none => simp [hn] at hy
      | some n => simp only [hn] at hy; simp only [denoteN_ext hn hx]; exact hy) rules hws]
    exact h

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:137-142 kindNamesAt — **a constant's kind, its
expressions left out, is upstream's**, read back. -/
theorem kindNamesAt_run {pk : OleanPins} {r : Region} {c : Nat} {kr : CKindF NIdx Unit}
    {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.kindNamesAt pk r c s = .ok (some kr, s')) :
    ParseStep s s' ∧ ∃ kC, ConLeche.Frontend.Olean.kindNamesAt r c = some kC ∧
      denoteKindN s'.store kr = some kC := by
  unfold ConRon.Arena.Frontend.Olean.kindNamesAt at h
  unfold ConLeche.Frontend.Olean.kindNamesAt
  cases hsk : constSkel r c with
  | none => simp only [hsk] at h; exact (none_not_some h).elim
  | some sk =>
  simp only [hsk] at h
  obtain ⟨u, s₁, h1, h2⟩ := AM.bind_ok h
  have := skelFits_run h1
  subst this
  unfold ConRon.Arena.Frontend.Olean.kindNames at h2
  obtain ⟨hst, kC, hk, hd⟩ := kindNames_run
    (fun a s s' y hctx hrun => sparseNameP_run hctx.ok hctx.nulls hrun) sk.kind hctx h2
  refine ⟨hst, kC, ?_, hd⟩
  simp only [bind, Option.bind]
  rw [show (ConLeche.Frontend.Olean.sparseNameP r) = nameP r from
    funext (ConLeche.Frontend.Olean.sparseNameP_eq r)]
  exact hk

/-! ## A view's reads -/

/-- con-leche: ConLeche/Frontend/Olean/View.lean:148-150 readNamePositions -/
theorem readNamePositions_run {pk : OleanPins} {f : ModFiles} {level : OLeanLevel}
    {p : ConRon.Arena.Frontend.Olean.NamePositions} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.readNamePositions pk f level s = .ok (some p, s')) :
    ParseStep s s' ∧ ∃ pC, ConLeche.Frontend.Olean.readNamePositions f level = some pC ∧
      NPsRel s'.store p pC := by
  unfold ConRon.Arena.Frontend.Olean.readNamePositions at h
  unfold ConLeche.Frontend.Olean.readNamePositions
  cases hv : f.viewRegion level with
  | none => simp only [hv] at h; exact (none_not_some h).elim
  | some ra =>
    obtain ⟨r, a⟩ := ra
    simp only [hv] at h
    obtain ⟨hst, pC, hp, hrel⟩ := namePositionsAt_run hctx h
    exact ⟨hst, pC, by simp [hp, bind, Option.bind], hrel⟩

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:346-350 namesOf -/
theorem namesOf_run {pk : OleanPins} {m : ConLeche.Name} {f : ModFiles} {level : OLeanLevel}
    {p : ConRon.Arena.Frontend.Olean.NamePositions} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.namesOf pk m f level s = .ok (p, s')) :
    ParseStep s s' ∧ ∃ pC, ConLeche.Frontend.Olean.namesOf m f level = .ok pC ∧
      NPsRel s'.store p pC := by
  unfold ConRon.Arena.Frontend.Olean.namesOf at h
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
  cases o with
  | none =>
    obtain ⟨e, s₂, -, h3⟩ := AM.bind_ok h2
    exact (AM.fail_ok h3).elim
  | some ps =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    obtain ⟨hst, pC, hp, hrel⟩ := readNamePositions_run hctx h1
    exact ⟨hst, pC, by simp [ConLeche.Frontend.Olean.namesOf, hp], hrel⟩

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:359-364 readPartNames — **a part's name
positions, read on the snapshot through any lookup with the twin's directories**, read back. -/
theorem readPartNames_run {pk : OleanPins} {F : FS} {sp R : Roots} (hR : R.Ok F)
    (hb : R.bare = sp.bare) {m : NIdx} {mC : ConLeche.Name} {level : OLeanLevel}
    {p : ConRon.Arena.Frontend.Olean.NamePositions} {s s' : AState} (hctx : Ctx pk s)
    (hm : denoteN s.store.ns m = some mC)
    (h : ConRon.Arena.Frontend.Olean.readPartNames (modelFs F) pk sp m level s = .ok (p, s')) :
    ParseStep s s' ∧ ∃ pC, ModelIO.Gives (ConLeche.Frontend.Olean.readPartNames R (mC, level) :
        ModelIO _) F (.ok pC) ∧ NPsRel s'.store p pC := by
  unfold ConRon.Arena.Frontend.Olean.readPartNames at h
  obtain ⟨mn, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, hd⟩ := readName_run h1
  obtain rfl : mn = mC := Option.some.inj (hd.symm.trans hm)
  cases hloc : ConRon.Arena.Frontend.Olean.findModule (modelFs F) sp mn with
  | error e => simp only [hloc] at h2; exact (AM.fail_ok h2).elim
  | ok loc =>
  simp only [hloc] at h2
  unfold ConRon.Arena.Frontend.Olean.readPartNamesAt at h2
  obtain ⟨fv, s₂, h3, h4⟩ := AM.bind_ok h2
  cases hf : ConRon.Arena.Frontend.Olean.readFilesAt (modelFs F) loc mn level with
  | error e =>
    rw [hf] at h3
    exact (AM.fail_ok h3).elim
  | ok f =>
    rw [hf] at h3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    obtain ⟨hst, pC, hp, hrel⟩ := namesOf_run hctx h4
    refine ⟨hst, pC, ?_, hrel⟩
    unfold ConLeche.Frontend.Olean.readPartNames ConLeche.Frontend.Olean.readPartNamesAt
    refine (findModule_simR hR hb hloc).bind ((readFilesAt_sim hf).bind ?_)
    simp only [hp]
    exact ModelIO.gives_pure _ _

/-- con-leche: ConLeche/Frontend/Olean/View.lean:157-160 readStmts -/
theorem readStmts_run {pk : OleanPins} {f : ModFiles} {level : OLeanLevel} {cs : List Nat}
    {ys : List ConRon.Arena.Frontend.Olean.StmtRec} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.readStmts pk f level cs s = .ok (some ys, s')) :
    ParseStep s s' ∧ ∃ zs, ConLeche.Frontend.Olean.readStmts f level cs = some zs ∧
      ys.mapM (denoteStmt s'.store) = some zs := by
  unfold ConRon.Arena.Frontend.Olean.readStmts at h
  unfold ConLeche.Frontend.Olean.readStmts
  cases hv : f.viewRegion level with
  | none => simp only [hv] at h; exact (none_not_some h).elim
  | some ra =>
    obtain ⟨r, a⟩ := ra
    simp only [hv] at h
    obtain ⟨hst, zs, hz, hd⟩ := stmtsAt_run hctx h
    exact ⟨hst, zs, by simp [hz, bind, Option.bind], hd⟩

/-- con-leche: ConLeche/Frontend/Olean/View.lean:169-174 readKinds -/
theorem readKinds_run {pk : OleanPins} {f : ModFiles} {level : OLeanLevel} {cs : List Nat}
    {ks : List (CKindF NIdx Unit)} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.readKinds pk f level cs s = .ok (some ks, s')) :
    ParseStep s s' ∧ ∃ zs, ConLeche.Frontend.Olean.readKinds f level cs = some zs ∧
      ks.mapM (denoteKindN s'.store) = some zs := by
  unfold ConRon.Arena.Frontend.Olean.readKinds at h
  unfold ConLeche.Frontend.Olean.readKinds
  cases hv : f.viewRegion level with
  | none => simp only [hv] at h; exact (none_not_some h).elim
  | some ra =>
    obtain ⟨r, a⟩ := ra
    simp only [hv] at h
    obtain ⟨hst, zs, hz, hd⟩ := optT_list_run (pk := pk) (den := denoteKindN)
      (g := ConLeche.Frontend.Olean.kindNamesAt r)
      (fun {st st' y z} hx hy => denoteKindN_ext hx hy)
      (fun c s s' y hctx hrun => kindNamesAt_run hctx hrun) cs hctx h
    exact ⟨hst, zs, by simp [hz, bind, Option.bind], hd⟩

end ConRon.Bridge.Modular
