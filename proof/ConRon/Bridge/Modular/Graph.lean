/-
# `ConRon.Bridge.Modular.Graph` — the import graph check, Theorem 1 (task #166)

**The twin's `graphOf` gives upstream's `graphOf_ok` facts** (`graphOf_run`): an accepting run on
a snapshot `F` yields the closure as upstream's nodes (`CC`, the twin's closure denoted), each
module's imports what its header read answers on `F` with the run's added imports
(`Graph.NodeOk`), every root a module of `CC`, a rank function one-to-one on `CC` under which
every import edge goes to a smaller rank.  As upstream's, what is proved is the validation
(`verdict_none`, the twin's verdict over handles, upstream's proof), not Kahn's algorithm.  The
walk is not related to upstream's step by step: each header read is `moduleImports_run`'s
upstream read, so every node returned is good (`closureLevels_run`).
-/
module

public import ConRon.Arena.Modular.Graph
public import ConRon.Bridge.Frontend.Olean.Closure
public import ConLeche.Verify.Driver.Graph
import Std.Data.HashSet.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins)
open ConRon.Arena.Modular (Node hdrOf expand closureLevels dedup indexOf depsOf rankOf namesOf edgeOk
  verdict Fault graphOf cmpExtra solutionImport missingOn)
open ConLeche.Frontend.Olean (ImportF ImportRec Roots)
open ConLeche.Driver.Graph (NodeOk rankLt rankLt_iff)

/-! ## The verdict, over handles (upstream's `verdict_none`) -/

theorem namesOf_contains_go {a : NIdx} :
    ∀ (C : List Node) (s : Std.HashSet NIdx),
      (C.foldl (fun s e => s.insert e.1) s).contains a = true → a ∈ C.map (·.1) ∨ s.contains a = true
  | [], _, h => Or.inr h
  | e :: C, s, h => by
    rcases namesOf_contains_go C _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr h

theorem namesOf_contains {C : List Node} {a : NIdx} (h : (namesOf C).contains a = true) :
    a ∈ C.map (·.1) := by
  rcases namesOf_contains_go C {} h with h | h
  · exact h
  · simp at h

/-- **What a verdict of none says**: the numbering is topological on the closure. -/
theorem verdict_none {roots : List NIdx} {C : List Node} {rk : NIdx → Option Nat}
    (h : verdict roots C rk = none) :
    (∀ r ∈ roots, r ∈ C.map (·.1)) ∧
    (∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rankLt (rk i.module) (rk e.1) = true) ∧
    (∀ e ∈ C, (rk e.1).isSome = true) ∧
    (C.map fun e => rk e.1).Nodup := by
  unfold verdict at h
  simp only at h
  split at h
  · cases h
  rename_i hroots
  split at h
  · cases h
  rename_i hrk
  split at h
  · cases h
  rename_i hdist
  split at h
  · cases h
  rename_i hedge
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hdist
  refine ⟨?_, ?_, ?_, ((ConLeche.Frontend.Olean.distinctGo_iff _ _).1 hdist).1⟩
  · intro r hr
    have := List.find?_eq_none.1 (by
      cases hf : roots.find? (fun x => !(namesOf C).contains x) with
      | none => rfl
      | some x => exact absurd hf (hroots x)) r hr
    simp only [Bool.not_eq_true', Bool.not_eq_false] at this
    exact namesOf_contains this
  · intro e he i hi
    have hn : C.find? (fun e => !e.2.all (edgeOk (namesOf C) rk e.1)) = none := by
      cases hf : C.find? (fun e => !e.2.all (edgeOk (namesOf C) rk e.1)) with
      | none => rfl
      | some x => exact absurd hf (hedge x.1 x.2)
    have := List.find?_eq_none.1 hn e he
    simp only [Bool.not_eq_true', Bool.not_eq_false, Array.all_eq_true'] at this
    have hi' := this i hi
    simp only [edgeOk, Bool.and_eq_true] at hi'
    exact ⟨namesOf_contains hi'.1, hi'.2⟩
  · intro e he
    have hn : C.find? (fun e => (rk e.1).isNone) = none := by
      cases hf : C.find? (fun e => (rk e.1).isNone) with
      | none => rfl
      | some x => exact absurd hf (hrk x.1 x.2)
    have := List.find?_eq_none.1 hn e he
    simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using this

/-! ## Lists read back -/

theorem list_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {zs : List β}, l.mapM f = some zs → ∀ {x : α}, x ∈ l → ∃ z, f x = some z ∧ z ∈ zs
  | [], _, _, _, hx => by simp at hx
  | a :: l, zs, h, x, hx => by
    simp only [List.mapM_cons] at h
    obtain ⟨z, hz, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    obtain ⟨zs', hzs, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨z, hz, List.mem_cons_self⟩
    · obtain ⟨w, hw, hm⟩ := list_mapM_mem hzs hx
      exact ⟨w, hw, List.mem_cons_of_mem _ hm⟩

theorem list_mapM_mem_rev {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {zs : List β}, l.mapM f = some zs → ∀ {z : β}, z ∈ zs → ∃ x ∈ l, f x = some z
  | [], zs, h, _, hz => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; simp at hz
  | a :: l, zs, h, z, hz => by
    simp only [List.mapM_cons] at h
    obtain ⟨w, hw, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    obtain ⟨zs', hzs, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨a, List.mem_cons_self, hw⟩
    · obtain ⟨x, hx, hf⟩ := list_mapM_mem_rev hzs hz
      exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩

/-! ## Nodes and the imports a run adds -/

/-- **A twin node and upstream's**: the module's name and its imports read back. -/
@[expose] def NodeD (st : EStore) (e : Node) (eC : ConLeche.Driver.Graph.Node) : Prop :=
  denoteN st.ns e.1 = some eC.1 ∧ e.2.toList.mapM (denoteImport st) = some eC.2.toList

theorem mapM_denoteImport_ext {st st' : EStore} (hx : Ext st st') :
    ∀ {l : List (ImportF NIdx)} {zs : List ImportRec},
      l.mapM (denoteImport st) = some zs → l.mapM (denoteImport st') = some zs
  | [], zs, h => h
  | i :: l, zs, h => by
    simp only [List.mapM_cons] at h ⊢
    obtain ⟨z, hz, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    obtain ⟨zs', hzs, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    rw [denoteImport_ext hx hz, mapM_denoteImport_ext hx hzs]
    exact h

theorem NodeD.ext {st st' : EStore} (hx : Ext st st') {e : Node} {eC : ConLeche.Driver.Graph.Node}
    (h : NodeD st e eC) : NodeD st' e eC :=
  ⟨denoteN_ext h.1 hx, mapM_denoteImport_ext hx h.2⟩

/-- **The imports a run adds, denoted**: none, or upstream's `cmpExtra` at the denoted pair. -/
@[expose] def ExtraRel (st : EStore) : Option (NIdx × NIdx) → (ConLeche.Name → Array ImportRec) → Prop
  | none, extra => ∀ n, extra n = #[]
  | some (c, s), extra => ∃ cn sn, denoteN st.ns c = some cn ∧ denoteN st.ns s = some sn ∧
      extra = ConLeche.Driver.Graph.cmpExtra cn sn

theorem ExtraRel.ext {st st' : EStore} (hx : Ext st st') {cmp : Option (NIdx × NIdx)}
    {extra : ConLeche.Name → Array ImportRec} (h : ExtraRel st cmp extra) : ExtraRel st' cmp extra := by
  match cmp, h with
  | none, h => exact h
  | some (c, s), ⟨cn, sn, h1, h2, h3⟩ => exact ⟨cn, sn, denoteN_ext h1 hx, denoteN_ext h2 hx, h3⟩

theorem cmpExtra_den {st : EStore} (hw : NStoreWF st.ns) {cmp : Option (NIdx × NIdx)}
    {extra : ConLeche.Name → Array ImportRec} (h : ExtraRel st cmp extra) {m : NIdx} {mn : ConLeche.Name}
    (hm : denoteN st.ns m = some mn) :
    (cmpExtra cmp m).toList.mapM (denoteImport st) = some (extra mn).toList := by
  match cmp, h with
  | none, h => simp [cmpExtra, h mn]
  | some (c, s), ⟨cn, sn, h1, h2, h3⟩ =>
    subst h3
    simp only [cmpExtra, ConLeche.Driver.Graph.cmpExtra]
    by_cases hc : m = c
    · subst hc
      have : mn = cn := Option.some.inj (hm.symm.trans h1)
      subst this
      simp [solutionImport, ConLeche.Driver.Graph.solutionImport, denoteImport, ImportF.mapM, h2]
    · have hn : ¬ mn = cn := fun he => hc (denoteN_inj hw hm (he ▸ h1))
      simp [hc, hn]

/-! ## The walk -/

theorem catchAt_bind_ok {α β : Type} {x : AM α} {k : Except Arena.CheckError α → AM β} {s s' : AState} {b : β}
    (h : (ConRon.Arena.Modular.AM.catchAt x >>= k) s = .ok (b, s')) :
    (∃ a s₁, x s = .ok (a, s₁) ∧ k (.ok a) s₁ = .ok (b, s')) ∨
      (∃ e, x s = .error e ∧ k (.error e) s = .ok (b, s')) := by
  obtain ⟨r, s₁, h1, h2⟩ := AM.bind_ok h
  unfold ConRon.Arena.Modular.AM.catchAt at h1
  cases hx : x s with
  | ok p =>
    rw [hx] at h1
    cases h1
    exact Or.inl ⟨p.1, p.2, rfl, h2⟩
  | error e =>
    rw [hx] at h1
    cases h1
    exact Or.inr ⟨e, rfl, h2⟩

theorem fail_not_ok {α : Type} {e : Arena.CheckError} {s s' : AState} {a : α} :
    ¬ (Arena.fail e : AM α) s = .ok (a, s') := by
  intro h; cases h

theorem denoteImport_module {st : EStore} {i : ImportF NIdx} {z : ImportRec}
    (h : denoteImport st i = some z) : denoteN st.ns i.module = some z.module := by
  unfold denoteImport ImportF.mapM at h
  obtain ⟨y, hy, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  exact hy

/-- **A header read that answers** is upstream's header read on the snapshot, with the run's
imports added. -/
theorem hdrOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {cmp : Option (NIdx × NIdx)} {extra : ConLeche.Name → Array ImportRec} {m : NIdx} {mn : ConLeche.Name}
    {e : Node} {s s' : AState} (hctx : Ctx pk s) (hx : ExtraRel s.store cmp extra)
    (hm : denoteN s.store.ns m = some mn)
    (h : hdrOf (modelFs F) pk sp cmp m s = .ok (e, s')) :
    ParseStep s s' ∧ e.1 = m ∧ ∃ eC, NodeD s'.store e eC ∧ eC.1 = mn ∧ NodeOk sp F extra eC := by
  unfold hdrOf at h
  rcases catchAt_bind_ok h with ⟨imps, s₁, h1, h2⟩ | ⟨err, _, h2⟩
  · obtain ⟨hv, hs⟩ := AM.pure_ok h2
    subst hv hs
    obtain ⟨hst, zs, hz, hd⟩ := moduleImports_run (roots_ok_of_bare hsp) rfl hm hctx h1
    have hw := nsWF_of_StateOK hst.ok
    have hm1 := denoteN_ext hm hst.ext
    refine ⟨hst, rfl, (mn, zs ++ extra mn), ⟨hm1, ?_⟩, rfl, zs, hsp ▸ hz.canGive, rfl⟩
    simp only [Array.toList_append, List.mapM_append, hd, cmpExtra_den hw (hx.ext hst.ext) hm1]
    rfl
  · exfalso
    obtain ⟨b, s₂, -, h3⟩ := AM.bind_ok h2
    cases b with
    | true =>
      obtain ⟨_, _, _, h4⟩ := AM.bind_ok h3
      exact fail_not_ok h4
    | false => exact fail_not_ok h3

/-- A level's headers read in order: each a good node of its module, in the header closure
`H` its module is in. -/
theorem mapM_hdrOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {cmp : Option (NIdx × NIdx)} {extra : ConLeche.Name → Array ImportRec} (H : ConLeche.Name → Prop) :
    ∀ (lvl : List NIdx) {rs : List Node} {s s' : AState}, Ctx pk s → ExtraRel s.store cmp extra →
      (∀ m ∈ lvl, ∃ mn, denoteN s.store.ns m = some mn ∧ H mn) →
      lvl.mapM (hdrOf (modelFs F) pk sp cmp) s = .ok (rs, s') →
      ParseStep s s' ∧ rs.map (·.1) = lvl ∧
        ∀ e ∈ rs, ∃ eC, NodeD s'.store e eC ∧ NodeOk sp F extra eC ∧ H eC.1
  | [], rs, s, s', hctx, _, _, h => by
    simp only [List.mapM_nil] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    subst hv hs
    exact ⟨ParseStep.refl hctx.ok, rfl, by simp⟩
  | m :: lvl, rs, s, s', hctx, hx, hd, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨e, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨rs', s₂, h2, h⟩ := AM.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    subst hv hs
    obtain ⟨mn, hmn, hH⟩ := hd m List.mem_cons_self
    obtain ⟨hst1, he1, eC, hD, he, hok⟩ := hdrOf_run hsp hctx hx hmn h1
    obtain ⟨hst2, hmap, hall⟩ := mapM_hdrOf_run hsp H lvl (hctx.step hst1) (hx.ext hst1.ext)
      (fun m' hm' => by
        obtain ⟨n, hn, hHn⟩ := hd m' (List.mem_cons_of_mem _ hm')
        exact ⟨n, denoteN_ext hn hst1.ext, hHn⟩) h2
    refine ⟨hst1.trans hst2, by simp [he1, hmap], ?_⟩
    intro e' he'
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact ⟨eC, hD.ext hst2.ext, hok, he ▸ hH⟩
    · exact hall e' he'

/-- The walk's next level: modules the level's imports name. -/
theorem expand_good (P : Node → Prop) (Q : NIdx → Prop) :
    ∀ (rs : List Node) (seen : Std.HashSet NIdx) (out : Array Node) (next : Array NIdx),
      (∀ e ∈ rs, P e ∧ ∀ i ∈ e.2, Q i.module) → (∀ e ∈ out.toList, P e) → (∀ x ∈ next.toList, Q x) →
      (∀ e ∈ (expand seen out next rs).2.1.toList, P e) ∧ (∀ x ∈ (expand seen out next rs).2.2.toList, Q x)
  | [], _, _, _, _, ho, hn => ⟨ho, hn⟩
  | (m, imps) :: rest, seen, out, next, hr, ho, hn => by
    simp only [expand]
    have hfold : ∀ (l : List ConRon.Arena.Frontend.Olean.ImportRec) (acc : Std.HashSet NIdx × Array NIdx), (∀ i ∈ l, Q i.module) →
        (∀ x ∈ acc.2.toList, Q x) →
        ∀ x ∈ (l.foldl (fun (sn : Std.HashSet NIdx × Array NIdx) i =>
          if sn.1.contains i.module then (sn.1, sn.2) else (sn.1.insert i.module, sn.2.push i.module)) acc).2.toList, Q x := by
      intro l
      induction l with
      | nil => intro acc _ h; exact h
      | cons i l ih =>
        intro acc hl ha
        simp only [List.foldl_cons]
        refine ih _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ?_
        split
        · exact ha
        · intro x hx
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact ha x hx
          · exact hl i List.mem_cons_self
    obtain ⟨hp, hq⟩ := hr (m, imps) List.mem_cons_self
    refine expand_good P Q rest _ _ _ (fun e he => hr e (List.mem_cons_of_mem _ he)) ?_ ?_
    · intro e he
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ho e he
      · exact hp
    · have := hfold imps.toList (seen, next) (fun i hi => hq i (Array.mem_toList_iff.mp hi)) hn
      rw [Array.foldl_toList] at this
      exact this

/-- **Every module the walk returns is a good node**, in the header closure of `roots'` where
the walk's level is and every added import's module is a root of it. -/
theorem closureLevels_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {cmp : Option (NIdx × NIdx)} {extra : ConLeche.Name → Array ImportRec} {roots' : List ConLeche.Name}
    (hxr : ∀ m, ∀ i ∈ extra m, i.module ∈ roots') :
    ∀ (fuel : Nat) (lvl : List NIdx) (seen : Std.HashSet NIdx) (out C : Array Node) {s s' : AState},
      Ctx pk s → ExtraRel s.store cmp extra →
      (∀ m ∈ lvl, ∃ mn, denoteN s.store.ns m = some mn ∧ ConLeche.Frontend.Olean.HdrClosure sp F roots' mn) →
      (∀ e ∈ out.toList, ∃ eC, NodeD s.store e eC ∧ NodeOk sp F extra eC ∧
        ConLeche.Frontend.Olean.HdrClosure sp F roots' eC.1) →
      closureLevels (modelFs F) pk sp cmp fuel lvl seen out s = .ok (C, s') →
      ParseStep s s' ∧ ∀ e ∈ C.toList, ∃ eC, NodeD s'.store e eC ∧ NodeOk sp F extra eC ∧
        ConLeche.Frontend.Olean.HdrClosure sp F roots' eC.1
  | _, [], _, out, C, s, s', hctx, _, _, hout, h => by
    rw [closureLevels] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    subst hv hs
    exact ⟨ParseStep.refl hctx.ok, hout⟩
  | 0, _ :: _, _, _, _, _, _, _, _, _, _, h => by rw [closureLevels] at h; exact absurd h fail_not_ok
  | fuel + 1, x :: xs, seen, out, C, s, s', hctx, hx, hd, hout, h => by
    rw [closureLevels] at h
    obtain ⟨rs, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hst1, -, hrs⟩ := mapM_hdrOf_run hsp (ConLeche.Frontend.Olean.HdrClosure sp F roots')
      (x :: xs) hctx hx hd h1
    let P : Node → Prop := fun e => ∃ eC, NodeD s₁.store e eC ∧ NodeOk sp F extra eC ∧
      ConLeche.Frontend.Olean.HdrClosure sp F roots' eC.1
    let Q : NIdx → Prop := fun m => ∃ mn, denoteN s₁.store.ns m = some mn ∧
      ConLeche.Frontend.Olean.HdrClosure sp F roots' mn
    have hE := expand_good P Q rs seen out #[]
      (fun e he => by
        obtain ⟨eC, hD, hok, hH⟩ := hrs e he
        refine ⟨⟨eC, hD, hok, hH⟩, fun i hi => ?_⟩
        obtain ⟨z, hz, hzm⟩ := list_mapM_mem hD.2 (Array.mem_toList_iff.mpr hi)
        exact ⟨z.module, denoteImport_module hz,
          ConLeche.Frontend.Olean.HdrClosure.of_node hok hxr hH (Array.mem_toList_iff.mp hzm)⟩)
      (fun e he => by
        obtain ⟨eC, hD, hok, hH⟩ := hout e he
        exact ⟨eC, hD.ext hst1.ext, hok, hH⟩)
      (by simp)
    obtain ⟨hst2, hC⟩ := closureLevels_run hsp hxr fuel _ _ _ C (hctx.step hst1) (hx.ext hst1.ext)
      (fun m hm => hE.2 m (by simpa using hm)) hE.1 h
    exact ⟨hst1.trans hst2, hC⟩

/-! ## The check -/

theorem dedup_mem {xs : List NIdx} : ∀ x ∈ (dedup xs).1, x ∈ xs := by
  intro x hx
  unfold dedup at hx
  suffices H : ∀ (l : List NIdx) (s : Std.HashSet NIdx) (acc : Array NIdx),
      x ∈ (l.foldl (fun (sa : Std.HashSet NIdx × Array NIdx) y =>
        if sa.1.contains y then sa else (sa.1.insert y, sa.2.push y)) (s, acc)).2.toList →
      x ∈ acc.toList ∨ x ∈ l by
    rcases H xs {} #[] hx with h | h
    · simp at h
    · exact h
  intro l
  induction l with
  | nil => intro s acc h; exact Or.inl h
  | cons y l ih =>
    intro s acc h
    simp only [List.foldl_cons] at h
    split at h
    · rcases ih _ _ h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')
    · rcases ih _ _ h with h' | h'
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h'
        rcases h' with h' | rfl
        · exact Or.inl h'
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h')

theorem listRel_choose {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ l', ListRel R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl⟩ := listRel_choose (l := l) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: l', .cons hb hl⟩

theorem listRel_memL {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → ∀ {a : α}, a ∈ l → ∃ b ∈ l', R a b
  | _, _, .nil, _, ha => by simp at ha
  | _, _, .cons hab hr, a, ha => by
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := listRel_memL hr ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem listRel_memR {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → ∀ {b : β}, b ∈ l' → ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hab hr, b, hb => by
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := listRel_memR hr hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem listRel_mono {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → ListRel R' l l'
  | _, _, .nil => .nil
  | _, _, .cons a b => .cons (h _ _ a) (listRel_mono h b)

/-- A rank function on names, from one on the closure's handles. -/
@[expose] def rankC (st : EStore) (C : List Node) (rk : NIdx → Option Nat) (n : ConLeche.Name) : Nat :=
  ((C.find? fun e => decide (denoteN st.ns e.1 = some n)).bind fun e => rk e.1).getD 0

theorem rankC_eq {st : EStore} (hw : NStoreWF st.ns) {C : List Node} {rk : NIdx → Option Nat}
    {e : Node} (he : e ∈ C) {n : ConLeche.Name} (hn : denoteN st.ns e.1 = some n) :
    rankC st C rk n = (rk e.1).getD 0 := by
  unfold rankC
  cases hf : C.find? fun e => decide (denoteN st.ns e.1 = some n) with
  | none =>
    have := List.find?_eq_none.1 hf e he
    simp [hn] at this
  | some e' =>
    have := List.find?_some hf
    simp only [decide_eq_true_eq] at this
    have : e'.1 = e.1 := denoteN_inj hw this hn
    simp [this]

/-- **The graph checked, over the twin** (upstream's `graphOf_ok`): an accepting run gives the
closure as upstream's nodes `CC`, each module's imports what its header read answers on the
snapshot with the run's added imports, every root a module of `CC`, and a rank function under
which every import edge goes to a smaller rank, one-to-one on `CC`. -/
theorem graphOf_run {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {roots : List NIdx} {rootsC roots' : List ConLeche.Name} {cmp : Option (NIdx × NIdx)}
    {extra : ConLeche.Name → Array ImportRec} {C : Array Node} {s s' : AState}
    (hctx : Ctx pk s) (hx : ExtraRel s.store cmp extra) (hr : ListRel (NR s.store) roots rootsC)
    (hrr : ∀ r ∈ rootsC, r ∈ roots') (hxr : ∀ m, ∀ i ∈ extra m, i.module ∈ roots')
    (h : graphOf (modelFs F) pk sp roots cmp s = .ok (C, s')) :
    ParseStep s s' ∧ ∃ CC : List ConLeche.Driver.Graph.Node, ListRel (NodeD s'.store) C.toList CC ∧
      ∃ rk : ConLeche.Name → Nat,
        (∀ e ∈ CC, NodeOk sp F extra e) ∧
        (∀ r ∈ rootsC, r ∈ CC.map (·.1)) ∧
        (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
        (CC.map fun e => rk e.1).Nodup ∧
        (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure sp F roots' e.1) := by
  unfold graphOf at h
  obtain ⟨C', s₁, h1, h⟩ := AM.bind_ok h
  have hroots : ∀ m ∈ (dedup roots).1, ∃ mn, denoteN s.store.ns m = some mn ∧
      ConLeche.Frontend.Olean.HdrClosure sp F roots' mn := by
    intro m hm
    obtain ⟨mn, hmn1, hmn⟩ := listRel_memL hr (dedup_mem m hm)
    exact ⟨mn, hmn, .root (hrr mn hmn1)⟩
  obtain ⟨hst1, hgood⟩ := closureLevels_run hsp hxr _ _ _ _ C' hctx hx hroots (by simp) h1
  -- the cycle and the verdict
  dsimp only at h
  cases hc : ConRon.Arena.Modular.cycleOf (depsOf (indexOf C') C')
      (ConRon.Arena.Modular.kahn (depsOf (indexOf C') C')) with
  | some cyc =>
    exfalso
    rw [hc] at h
    obtain ⟨_, _, _, h'⟩ := AM.bind_ok h
    obtain ⟨_, _, h'', _⟩ := AM.bind_ok h'
    exact fail_not_ok h''
  | none =>
  rw [hc] at h
  cases hv : verdict roots C'.toList (rankOf (indexOf C') (ConRon.Arena.Modular.ranksOf C'.size
      (ConRon.Arena.Modular.kahn (depsOf (indexOf C') C')))) with
  | some f =>
    exfalso
    simp only [hv] at h
    obtain ⟨_, _, _, h'⟩ := AM.bind_ok h
    obtain ⟨_, _, _, h''⟩ := AM.bind_ok h'
    exact fail_not_ok h''
  | none =>
  simp only [hv] at h
  obtain ⟨hv', hs⟩ := AM.pure_ok h
  subst hv' hs
  have hw := nsWF_of_StateOK hst1.ok
  generalize hrk : rankOf (indexOf C) (ConRon.Arena.Modular.ranksOf C.size
    (ConRon.Arena.Modular.kahn (depsOf (indexOf C) C))) = rk at hv
  obtain ⟨v1, v2, v3, v4⟩ := verdict_none hv
  obtain ⟨CC, hCC⟩ := listRel_choose (R := fun e eC => NodeD s'.store e eC ∧ NodeOk sp F extra eC ∧
    ConLeche.Frontend.Olean.HdrClosure sp F roots' eC.1) hgood
  refine ⟨hst1, CC, listRel_mono (fun _ _ h => h.1) hCC, rankC s'.store C.toList rk, ?_, ?_, ?_, ?_, ?_⟩
  · intro eC heC
    obtain ⟨e, -, _, hok, -⟩ := listRel_memR hCC heC
    exact hok
  · intro rC hrC
    obtain ⟨r, hr1, hr2⟩ := listRel_memR hr hrC
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (v1 r hr1)
    obtain ⟨eC, heC, hD, -⟩ := listRel_memL hCC he
    have : eC.1 = rC := Option.some.inj (hD.1.symm.trans (denoteN_ext hr2 hst1.ext))
    exact List.mem_map.2 ⟨eC, heC, this⟩
  · intro eC heC i' hi'
    obtain ⟨e, he, hD, -⟩ := listRel_memR hCC heC
    obtain ⟨i, hi, hdi⟩ := list_mapM_mem_rev hD.2 (Array.mem_toList_iff.mpr hi')
    obtain ⟨hmem, hlt⟩ := v2 e he i (Array.mem_toList_iff.mp hi)
    obtain ⟨e2, he2, he2m⟩ := List.mem_map.1 hmem
    obtain ⟨eC2, heC2, hD2, -⟩ := listRel_memL hCC he2
    have hmod := denoteImport_module hdi
    rw [← he2m] at hmod
    have h2 : eC2.1 = i'.module := Option.some.inj (hD2.1.symm.trans hmod)
    refine ⟨List.mem_map.2 ⟨eC2, heC2, h2⟩, ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ := rankLt_iff.1 hlt
    rw [rankC_eq hw he2 (h2 ▸ hD2.1), rankC_eq hw he hD.1, he2m, ha, hb]
    exact hab
  · have hmap : CC.map (fun e => rankC s'.store C.toList rk e.1) =
        C.toList.map (fun e => (rk e.1).getD 0) := by
      have : ∀ {l : List Node} {l' : List ConLeche.Driver.Graph.Node},
          ListRel (fun e eC => NodeD s'.store e eC ∧ NodeOk sp F extra eC ∧
            ConLeche.Frontend.Olean.HdrClosure sp F roots' eC.1) l l' → (∀ e ∈ l, e ∈ C.toList) →
          l'.map (fun e => rankC s'.store C.toList rk e.1) = l.map (fun e => (rk e.1).getD 0) := by
        intro l l' hl
        induction hl with
        | nil => intro _; rfl
        | @cons a b _ _ hab _ ih =>
          intro hsub
          simp only [List.map_cons]
          rw [rankC_eq hw (hsub a List.mem_cons_self) hab.1.1,
            ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))]
      exact this hCC (fun _ h => h)
    rw [hmap]
    unfold List.Nodup at v4 ⊢
    rw [List.pairwise_map] at v4 ⊢
    refine v4.imp_of_mem fun {e e'} he he' hne heq => hne ?_
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (v3 e he)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (v3 e' he')
    simp only [ha, hb, Option.getD_some] at heq
    rw [ha, hb, heq]
  · intro eC heC
    obtain ⟨e, -, _, -, hH⟩ := listRel_memR hCC heC
    exact hH

end ConRon.Bridge.Modular
