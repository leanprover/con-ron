/-
# `ConRon.Bridge.Frontend.Olean.Levels` — the header fixpoint, Theorem 1 (task #166)

**An accepting twin run of `headerFixpoint` is upstream's run on the snapshot, denoted**
(`levelsGo_run`; `Bridge/Modular/Reads.lean`'s `headerFixpoint_gives` is the whole fixpoint): the
worklist `levelsGo` is upstream's step for step, over handles.  The
state relation (`StRel`) is upstream's state read back: the flags and the imports by module
(`HMRel`, a map over handles against one over names), the open set (`SetRel`), the order
(`ListRel`); each header read is `moduleImports_run`'s upstream read at the search path itself
(`roots_ok_of_bare`).  The result is related by `LoadsRel`, under which the public-import
closures are equal (`pubClosures_eq`).

This is a simulation in `closureGo_run`'s run style (`Bridge/Frontend/Olean/Closure.lean`), not a
`sym … vcgen … finish` walk proof over `bridge_grind`.
-/
module

public import ConRon.Arena.Frontend.Olean.Levels
public import ConRon.Bridge.Frontend.Olean.Closure
public import ConLeche.Verify.Driver.Loads
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins LvWork LvState levelsGo levelsJoin headerFixpoint
  HeaderLoads)
open ConLeche.Frontend.Olean (ImportF ImportRec Roots LoadFlags)

/-! ## Relations -/

/-- con-leche: none — a handle import list read back as upstream's. -/
@[expose] def ImpsD (st : EStore) (is : Array (ImportF NIdx)) (isC : Array ImportRec) : Prop :=
  is.toList.mapM (denoteImport st) = some isC.toList

theorem mapM_denoteImport_ext' {st st' : EStore} (hx : Ext st st') :
    ∀ {l : List (ImportF NIdx)} {zs : List ImportRec},
      l.mapM (denoteImport st) = some zs → l.mapM (denoteImport st') = some zs
  | [], zs, h => h
  | i :: l, zs, h => by
    simp only [List.mapM_cons] at h ⊢
    obtain ⟨z, hz, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    obtain ⟨zs', hzs, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    rw [denoteImport_ext hx hz, mapM_denoteImport_ext' hx hzs]
    exact h

theorem ImpsD.ext {st st' : EStore} (hx : Ext st st') {is : Array (ImportF NIdx)}
    {isC : Array ImportRec} (h : ImpsD st is isC) : ImpsD st' is isC :=
  mapM_denoteImport_ext' hx h

/-- An import read back: its module denoted, its flags kept. -/
theorem denoteImport_eq {st : EStore} {i : ImportF NIdx} {z : ImportRec}
    (h : denoteImport st i = some z) :
    ∃ y, denoteN st.ns i.module = some y ∧ z = { i with module := y } := by
  unfold denoteImport ImportF.mapM at h
  obtain ⟨y, hy, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  simp only [pure, Option.some.injEq] at h
  exact ⟨y, hy, h.symm⟩

/-- con-leche: none — **a map over handles against one over names**: each entry's key denotes
one of the other's, the values related. -/
structure HMRel {α β : Type} (R : α → β → Prop) (st : EStore) (M : Std.HashMap NIdx α)
    (MC : Std.HashMap ConLeche.Name β) : Prop where
  fwd : ∀ h a, M[h]? = some a → ∃ n b, denoteN st.ns h = some n ∧ MC[n]? = some b ∧ R a b
  bwd : ∀ n b, MC[n]? = some b → ∃ h a, denoteN st.ns h = some n ∧ M[h]? = some a ∧ R a b

theorem HMRel.empty {α β : Type} (R : α → β → Prop) (st : EStore) :
    HMRel R st ({} : Std.HashMap NIdx α) ({} : Std.HashMap ConLeche.Name β) :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem HMRel.ext {α β : Type} {R R' : α → β → Prop} {st st' : EStore} {M : Std.HashMap NIdx α}
    {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) (hx : Ext st st')
    (hr : ∀ a b, R a b → R' a b) : HMRel R' st' M MC :=
  ⟨fun x a hm => by
      obtain ⟨n, b, h1, h2, h3⟩ := h.fwd x a hm
      exact ⟨n, b, denoteN_ext h1 hx, h2, hr _ _ h3⟩,
   fun n b hm => by
      obtain ⟨x, a, h1, h2, h3⟩ := h.bwd n b hm
      exact ⟨x, a, denoteN_ext h1 hx, h2, hr _ _ h3⟩⟩

/-- A lookup answers alike. -/
theorem HMRel.get {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap NIdx α} {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) {x : NIdx}
    {n : ConLeche.Name} (hd : denoteN st.ns x = some n) : Option.Rel R M[x]? MC[n]? := by
  generalize hm : M[x]? = o
  cases o with
  | some a =>
    obtain ⟨n', b, h1, h2, h3⟩ := h.fwd x a hm
    have : n' = n := Option.some.inj (h1.symm.trans hd)
    subst this
    rw [h2]
    exact .some h3
  | none =>
    cases hc : MC[n]? with
    | none => exact .none
    | some b =>
      obtain ⟨y, a, h1, h2, _⟩ := h.bwd n b hc
      have : y = x := denoteN_inj hw h1 hd
      subst this
      rw [hm] at h2
      cases h2

theorem optRel_cases {α β : Type} {R : α → β → Prop} {o1 : Option α} {o2 : Option β}
    (h : Option.Rel R o1 o2) : (o1 = none ∧ o2 = none) ∨ ∃ a b, o1 = some a ∧ o2 = some b ∧ R a b := by
  cases h with
  | none => exact .inl ⟨rfl, rfl⟩
  | some h => exact .inr ⟨_, _, rfl, rfl, h⟩

theorem HMRel.get_eq {α : Type} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap NIdx α} {MC : Std.HashMap ConLeche.Name α} (h : HMRel Eq st M MC) {x : NIdx}
    {n : ConLeche.Name} (hd : denoteN st.ns x = some n) : M[x]? = MC[n]? := by
  rcases optRel_cases (h.get hw hd) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2, h3]

theorem HMRel.insert {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap NIdx α} {MC : Std.HashMap ConLeche.Name β} (h : HMRel R st M MC) {m : NIdx}
    {mC : ConLeche.Name} (hd : denoteN st.ns m = some mC) {a : α} {b : β} (hr : R a b) :
    HMRel R st (M.insert m a) (MC.insert mC b) := by
  constructor
  · intro x a' hx
    rw [Std.HashMap.getElem?_insert] at hx
    by_cases he : m = x
    · subst he
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      exact ⟨mC, b, hd, by simp, hr⟩
    · simp only [beq_iff_eq, he, ↓reduceIte] at hx
      obtain ⟨n, b', h1, h2, h3⟩ := h.fwd x a' hx
      have hn : ¬ mC = n := fun hn => he (denoteN_inj hw hd (hn ▸ h1))
      exact ⟨n, b', h1, by simp [Std.HashMap.getElem?_insert, hn, h2], h3⟩
  · intro n b' hn
    rw [Std.HashMap.getElem?_insert] at hn
    by_cases he : mC = n
    · subst he
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact ⟨m, a, hd, by simp, hr⟩
    · simp only [beq_iff_eq, he, ↓reduceIte] at hn
      obtain ⟨x, a', h1, h2, h3⟩ := h.bwd n b' hn
      have hx : ¬ m = x := fun hx => he (Option.some.inj (hd.symm.trans (hx ▸ h1)))
      exact ⟨x, a', h1, by simp [Std.HashMap.getElem?_insert, hx, h2], h3⟩

theorem SetRel.erase {st : EStore} (hw : NStoreWF st.ns) {t : Std.HashSet NIdx}
    {tC : Std.HashSet ConLeche.Name} (h : SetRel st t tC) {x : NIdx} {n : ConLeche.Name}
    (hd : denoteN st.ns x = some n) : SetRel st (t.erase x) (tC.erase n) := by
  constructor
  · intro y hy
    rw [Std.HashSet.mem_erase] at hy
    obtain ⟨hne, hy⟩ := hy
    obtain ⟨k, a, b⟩ := h.fwd y hy
    have hk : ¬ n = k := fun hk => by
      subst hk
      have : y = x := denoteN_inj hw a hd
      subst this
      simp at hne
    exact ⟨k, a, by simp [Std.HashSet.mem_erase, hk, b]⟩
  · intro k hk
    rw [Std.HashSet.mem_erase] at hk
    obtain ⟨hne, hk⟩ := hk
    obtain ⟨y, a, b⟩ := h.bwd k hk
    have hy : ¬ x = y := fun hy => by
      subst hy
      have : n = k := Option.some.inj (hd.symm.trans b)
      subst this
      simp at hne
    exact ⟨y, by simp [Std.HashSet.mem_erase, hy, a], b⟩

/-- con-leche: none — a work item against upstream's. -/
@[expose] def WorkR (st : EStore) : LvWork → ConLeche.Frontend.Olean.LvWork → Prop
  | .imp pf i, .imp pf' iC => pf = pf' ∧ denoteImport st i = some iC
  | .done m fl, .done mC fl' => denoteN st.ns m = some mC ∧ fl = fl'
  | _, _ => False

theorem WorkR.done_rel {st : EStore} {m : NIdx} {mC : ConLeche.Name}
    (h : denoteN st.ns m = some mC) (fl : LoadFlags) : WorkR st (.done m fl) (.done mC fl) :=
  ⟨h, rfl⟩

theorem WorkR_list_ext {st st' : EStore} (hx : Ext st st') {l : List LvWork}
    {ys : List ConLeche.Frontend.Olean.LvWork} (h : ListRel (WorkR st) l ys) :
    ListRel (WorkR st') l ys :=
  ListRel.mono' (fun a b hab => by
    cases a <;> cases b <;> simp only [WorkR] at hab ⊢
    · exact ⟨hab.1, denoteImport_ext hx hab.2⟩
    · exact ⟨denoteN_ext hab.1 hx, hab.2⟩) h

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:65-67 LvWork.ofImports — related. -/
theorem ofImports_rel {st : EStore} (fl : LoadFlags) {is : Array (ImportF NIdx)}
    {isC : Array ImportRec} (h : ImpsD st is isC) :
    ListRel (WorkR st) (LvWork.ofImports fl is) (ConLeche.Frontend.Olean.LvWork.ofImports fl isC) :=
  ListRel.map_left (ListRel.map_right
    (ListRel.mono' (fun _ _ hab => ⟨rfl, hab⟩) (listRel_of_mapM h)))

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:54-63 LvState — **the fixpoint's state read
back**. -/
structure StRel (st : EStore) (x : LvState) (xC : ConLeche.Frontend.Olean.LvState) : Prop where
  flags : HMRel Eq st x.flags xC.flags
  open_ : SetRel st x.open_ xC.open_
  order : ListRel (NR st) x.order.toList xC.order.toList
  imports : HMRel (ImpsD st) st x.imports xC.imports

theorem StRel.ext {st st' : EStore} (hx : Ext st st') {x : LvState}
    {xC : ConLeche.Frontend.Olean.LvState} (h : StRel st x xC) : StRel st' x xC :=
  ⟨h.flags.ext hx (fun _ _ => id), h.open_.ext hx, NR_list_ext hx h.order,
   h.imports.ext hx (fun _ _ => ImpsD.ext hx)⟩

/-! ## The worklist -/

/-- con-leche: ConLeche/Verify/Driver/Loads.lean:597 levelsGo_inv — **the twin's worklist is
upstream's**, step for step, each header read upstream's on the snapshot. -/
theorem levelsGo_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp) (gPriv : Bool) :
    ∀ (fuel : Nat) (ws : List LvWork) (x : LvState) (wsC : List ConLeche.Frontend.Olean.LvWork)
      (xC : ConLeche.Frontend.Olean.LvState) {s s' : AState} {xF : LvState}, Ctx pk s →
      ListRel (WorkR s.store) ws wsC → StRel s.store x xC →
      levelsGo (modelFs F) pk sp gPriv fuel ws x s = .ok (xF, s') →
      ParseStep s s' ∧ ∃ xFC, ModelIO.Gives
        (ConLeche.Frontend.Olean.levelsGo (ConLeche.Frontend.Olean.moduleImports sp) gPriv fuel wsC xC :
          ModelIO _) F (.ok xFC) ∧ StRel s'.store xF xFC := by
  intro fuel
  induction fuel with
  | zero =>
    intro ws x wsC xC s s' xF hctx hws hx h
    cases hws with
    | nil =>
      rw [levelsGo] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv hs
      exact ⟨ParseStep.refl hctx.ok, xC, by
        rw [ConLeche.Frontend.Olean.levelsGo]; exact ModelIO.gives_pure _ _, hx⟩
    | cons _ _ =>
      rw [levelsGo] at h
      cases h
  | succ fuel ih =>
    intro ws x wsC xC s s' xF hctx hws hx h
    have hw := nsWF_of_StateOK hctx.ok
    cases hws with
    | nil =>
      rw [levelsGo] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv hs
      exact ⟨ParseStep.refl hctx.ok, xC, by
        rw [ConLeche.Frontend.Olean.levelsGo]; exact ModelIO.gives_pure _ _, hx⟩
    | @cons a b ws' bs hab hrest =>
      cases a with
      | done m fl =>
        cases b with
        | imp _ _ => exact absurd hab (by simp [WorkR])
        | done mC fl' =>
          obtain ⟨hm, rfl⟩ := hab
          rw [levelsGo] at h
          rw [ConLeche.Frontend.Olean.levelsGo]
          exact ih ws' ⟨x.flags.insert m fl, x.open_.erase m, x.order.push m, x.imports⟩ bs
            ⟨xC.flags.insert mC fl, xC.open_.erase mC, xC.order.push mC, xC.imports⟩ hctx hrest
            ⟨hx.flags.insert hw hm rfl, hx.open_.erase hw hm, array_rel_push hx.order hm,
             hx.imports⟩ h
      | imp pf i =>
        cases b with
        | done _ _ => exact absurd hab (by simp [WorkR])
        | imp pf' iC =>
          obtain ⟨rfl, hi⟩ := hab
          obtain ⟨y, hy, rfl⟩ := denoteImport_eq hi
          rw [levelsGo] at h
          rw [ConLeche.Frontend.Olean.levelsGo]
          by_cases hc : (!(i.isExported || pf.importAll)) = true
          · simp only [hc, ↓reduceIte] at h ⊢
            exact ih _ _ _ _ hctx hrest hx h
          · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
            have hfl := hx.flags.get_eq hw hy
            cases hold : xC.flags[y]? with
            | some old =>
              have hcon : x.flags.contains i.module = true := by
                rw [Std.HashMap.contains_eq_isSome_getElem?, hfl, hold]; rfl
              simp only [hcon, ↓reduceIte] at h
              unfold levelsJoin at h
              rw [hfl, hold] at h
              dsimp only at h ⊢
              split at h
              · rename_i hf
                simp only [hf, ↓reduceIte]
                exact ih _ _ _ _ hctx hrest hx h
              · rename_i hf
                simp only [hf, Bool.false_eq_true, ↓reduceIte]
                have hfx := fun (fl' : LoadFlags) => hx.flags.insert hw hy (a := fl') (b := fl') rfl
                rcases optRel_cases (hx.imports.get hw hy) with ⟨hn1, hn2⟩ | ⟨is, isC, hn1, hn2, hd⟩
                · rw [hn1] at h
                  rw [hn2]
                  simp only [Option.getD_none, ConLeche.Frontend.Olean.LvWork.ofImports,
                    List.map_nil, List.nil_append] at h ⊢
                  exact ih _ _ _ _ hctx hrest (by exact ⟨hfx _, hx.open_, hx.order, hx.imports⟩) h
                · rw [hn1] at h
                  rw [hn2]
                  simp only [Option.getD_some] at h ⊢
                  exact ih _ _ _ _ hctx (ListRel.append (ofImports_rel _ hd) hrest)
                    (by exact ⟨hfx _, hx.open_, hx.order, hx.imports⟩) h
            | none =>
              have hcon : x.flags.contains i.module = false := by
                rw [Std.HashMap.contains_eq_isSome_getElem?, hfl, hold]; rfl
              simp only [hcon, Bool.false_eq_true, ↓reduceIte] at h
              dsimp only
              rw [← hx.open_.contains hw hy]
              split at h
              · rename_i ho
                simp only [ho, ↓reduceIte]
                exfalso
                obtain ⟨_, _, _, h2⟩ := AM.bind_ok h
                cases h2
              · rename_i ho
                simp only [ho, Bool.false_eq_true, ↓reduceIte]
                obtain ⟨is, s₁, h1, h2⟩ := AM.bind_ok h
                obtain ⟨hst1, zs, hz, hd⟩ :=
                  moduleImports_run (roots_ok_of_bare hsp) rfl hy hctx h1
                have hctx1 := hctx.step hst1
                have hw1 := nsWF_of_StateOK hctx1.ok
                have hy1 := denoteN_ext hy hst1.ext
                have hx1 := hx.ext hst1.ext
                obtain ⟨hst2, xFC, hC, hR⟩ := ih _ _ _
                  ({ xC with open_ := xC.open_.insert y, imports := xC.imports.insert y zs })
                  hctx1 (by exact (ListRel.append (ofImports_rel _ hd)
                    (.cons (WorkR.done_rel hy1 _) (WorkR_list_ext hst1.ext hrest))))
                  (by exact ⟨hx1.flags, hx1.open_.insert hy1, hx1.order, hx1.imports.insert hw1 hy1 hd⟩) h2
                refine ⟨hst1.trans hst2, xFC, ?_, hR⟩
                exact hz.bind hC

/-! ## The loads -/

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:113-122 HeaderLoads — **the loads read back**:
the order denoted, the flags equal, each module's imports denoted, the index answering alike. -/
structure LoadsRel (st : EStore) (ld : HeaderLoads) (ldC : ConLeche.Frontend.Olean.HeaderLoads) :
    Prop where
  order : ListRel (NR st) ld.order.toList ldC.order.toList
  flags : ld.flags = ldC.flags
  imports : ListRel (ImpsD st) ld.imports.toList ldC.imports.toList
  index : ∀ h n, denoteN st.ns h = some n → ld.index[h]? = ldC.index[n]?

theorem listRel_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {lC : List β}, ListRel R l lC → l.map f = lC.map g
  | _, _, .nil => rfl
  | _, _, .cons a b => by
    simp only [List.map_cons, hfg _ _ a, listRel_map_eq hfg b]

theorem listRel_foldl_eq {α β γ : Type} {R : α → β → Prop} {f : γ → α → γ} {g : γ → β → γ}
    (hfg : ∀ c a b, R a b → f c a = g c b) :
    ∀ {l : List α} {lC : List β}, ListRel R l lC → ∀ c, l.foldl f c = lC.foldl g c
  | _, _, .nil, _ => rfl
  | _, _, .cons a b, c => by
    simp only [List.foldl_cons, hfg _ _ _ a]
    exact listRel_foldl_eq hfg b _

theorem listRel_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {lC : List β}, ListRel R l lC → ∀ (k : Nat), Option.Rel R l[k]? lC[k]?
  | _, _, .nil, _ => .none
  | _, _, .cons a _, 0 => .some a
  | _, _, .cons _ b, k + 1 => by
    simp only [List.getElem?_cons_succ]
    exact listRel_getElem? b k

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint — the index fold, related. -/
theorem indexFold_rel {st : EStore} (hw : NStoreWF st.ns) :
    ∀ {l : List NIdx} {lC : List ConLeche.Name}, ListRel (NR st) l lC →
      ∀ (M : Std.HashMap NIdx Nat) (MC : Std.HashMap ConLeche.Name Nat) (k : Nat),
      (∀ h n, denoteN st.ns h = some n → M[h]? = MC[n]?) →
      ∀ h n, denoteN st.ns h = some n →
        (l.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
          (M, k)).1[h]? =
        (lC.foldl (fun (acc : Std.HashMap ConLeche.Name Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
          (MC, k)).1[n]?
  | _, _, .nil, _, _, _, hM, h, n, hd => hM h n hd
  | _, _, @ListRel.cons _ _ _ a b _ _ hab hr, M, MC, k, hM, h, n, hd => by
    simp only [List.foldl_cons]
    refine indexFold_rel hw hr _ _ _ (fun h' n' hd' => ?_) h n hd
    simp only [Std.HashMap.getElem?_insert]
    by_cases he : a = h'
    · subst he
      have : b = n' := Option.some.inj (hab.symm.trans hd')
      subst this
      simp
    · have hn : ¬ b = n' := fun hn => he (denoteN_inj hw hab (hn ▸ hd'))
      simp only [beq_iff_eq, he, hn, ↓reduceIte]
      exact hM h' n' hd'

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint — the flags of the
loads, as a map over the order. -/
theorem ofStateGo_flags (fm : Std.HashMap NIdx LoadFlags) :
    ∀ (ms : List NIdx) (i : Nat) (im : Std.HashMap NIdx (Array (ImportF NIdx)))
      (fl : Array LoadFlags) (is : Array (Array (ImportF NIdx))) (ix : Std.HashMap NIdx Nat),
      (HeaderLoads.ofStateGo fm ms i im fl is ix).1.toList =
        fl.toList ++ ms.map fun m => (fm[m]?).getD default
  | [], _, _, _, _, _ => by simp [HeaderLoads.ofStateGo]
  | m :: ms, i, im, fl, is, ix => by
    rw [HeaderLoads.ofStateGo, ofStateGo_flags fm ms]
    simp

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint — the imports of the
loads, as a map over an order without duplicates: each module's are moved out as it is placed. -/
theorem ofStateGo_imports (fm : Std.HashMap NIdx LoadFlags) :
    ∀ (ms : List NIdx), ms.Nodup → ∀ (i : Nat) (im : Std.HashMap NIdx (Array (ImportF NIdx)))
      (fl : Array LoadFlags) (is : Array (Array (ImportF NIdx))) (ix : Std.HashMap NIdx Nat),
      (HeaderLoads.ofStateGo fm ms i im fl is ix).2.1.toList =
        is.toList ++ ms.map fun m => (im[m]?).getD #[]
  | [], _, _, _, _, _, _ => by simp [HeaderLoads.ofStateGo]
  | m :: ms, hnd, i, im, fl, is, ix => by
    rw [List.nodup_cons] at hnd
    rw [HeaderLoads.ofStateGo, ofStateGo_imports fm ms hnd.2]
    simp only [Array.toList_push, List.append_assoc, List.map_cons, List.singleton_append]
    congr 2
    refine List.map_congr_left (fun m' hm' => ?_)
    have : ¬ m = m' := fun he => hnd.1 (he ▸ hm')
    simp [Std.HashMap.getElem?_erase, this]

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint — the index of the
loads, upstream's fold. -/
theorem ofStateGo_index (fm : Std.HashMap NIdx LoadFlags) :
    ∀ (ms : List NIdx) (i : Nat) (im : Std.HashMap NIdx (Array (ImportF NIdx)))
      (fl : Array LoadFlags) (is : Array (Array (ImportF NIdx))) (ix : Std.HashMap NIdx Nat),
      (HeaderLoads.ofStateGo fm ms i im fl is ix).2.2 =
        (ms.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
          (ix, i)).1
  | [], _, _, _, _, _ => by simp [HeaderLoads.ofStateGo]
  | m :: ms, i, im, fl, is, ix => by
    rw [HeaderLoads.ofStateGo, ofStateGo_index fm ms]
    rfl

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint — the fixpoint's state
as loads, related, its order without duplicates. -/
theorem ofState_rel {st : EStore} (hw : NStoreWF st.ns) {x : LvState}
    {xC : ConLeche.Frontend.Olean.LvState} (h : StRel st x xC) (hnd : xC.order.toList.Nodup) :
    LoadsRel st (HeaderLoads.ofState x)
      { order := xC.order, flags := xC.order.map fun m => (xC.flags[m]?).getD default,
        imports := xC.order.map fun m => (xC.imports[m]?).getD #[],
        index := xC.order.foldl (fun (acc : Std.HashMap ConLeche.Name Nat × Nat) m =>
          (acc.1.insert m acc.2, acc.2 + 1)) ({}, 0) |>.1 } := by
  have hnd' : x.order.toList.Nodup := (ListRel.nodup_iff_denoteN hw h.order).2 hnd
  have hf := ofStateGo_flags x.flags x.order.toList 0 x.imports #[] #[] {}
  have hi := ofStateGo_imports x.flags x.order.toList hnd' 0 x.imports #[] #[] {}
  have hx := ofStateGo_index x.flags x.order.toList 0 x.imports #[] #[] {}
  unfold HeaderLoads.ofState
  generalize HeaderLoads.ofStateGo x.flags x.order.toList 0 x.imports #[] #[] {} = r at hf hi hx
  obtain ⟨fl, is, ix⟩ := r
  simp only [List.nil_append] at hf hi hx
  refine ⟨h.order, ?_, ?_, ?_⟩
  · apply Array.toList_inj.mp
    simp only [hf, Array.toList_map]
    exact listRel_map_eq (fun a b hab => by rw [h.flags.get_eq hw hab]) h.order
  · simp only [hi, Array.toList_map]
    refine ListRel.map_left (ListRel.map_right (ListRel.mono' (fun a b hab => ?_) h.order))
    rcases optRel_cases (h.imports.get hw hab) with ⟨h1, h2⟩ | ⟨is, isC, h1, h2, h3⟩
    · rw [h1, h2]; rfl
    · rw [h1, h2]; exact h3
  · intro a n hd
    simp only [hx]
    rw [← Array.foldl_toList]
    exact indexFold_rel hw h.order _ _ _ (fun _ _ _ => by simp) a n hd

/-! ## The public-import closures -/

/-- con-leche: ConLeche/Frontend/Olean/Levels.lean:179-193 pubClosures — **the twin's
public-import closures are upstream's**, of loads read back. -/
theorem pubClosures_eq {st : EStore} {ld : HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (h : LoadsRel st ld ldC) :
    ConRon.Arena.Frontend.Olean.pubClosures ld = ConLeche.Frontend.Olean.pubClosures ldC := by
  have hn : ld.order.size = ldC.order.size := by
    rw [← Array.length_toList, ← Array.length_toList]; exact h.order.length_eq
  unfold ConRon.Arena.Frontend.Olean.pubClosures ConLeche.Frontend.Olean.pubClosures
  dsimp only
  rw [hn]
  congr 1
  funext acc i
  congr 1
  rw [← Array.getElem?_toList, ← Array.getElem?_toList]
  rcases optRel_cases (listRel_getElem? h.imports i) with ⟨h1, h2⟩ | ⟨is, isC, h1, h2, h3⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2, Option.getD_some, Option.getD_some, ← Array.foldl_toList, ← Array.foldl_toList]
    refine listRel_foldl_eq (fun c a b hab => ?_) (listRel_of_mapM h3) _
    obtain ⟨y, hy, rfl⟩ := denoteImport_eq hab
    rw [h.index _ _ hy]
    rfl

/-! ## Upstream's facts, of the twin's loads -/

end ConRon.Bridge.Frontend.Olean
