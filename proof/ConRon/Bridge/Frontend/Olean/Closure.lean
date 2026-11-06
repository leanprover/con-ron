/-
# `ConRon.Bridge.Frontend.Olean.Closure` — the import closure, loaded

The walk `closureGo` is upstream's, over handles: the sets of handles denote upstream's sets of
names (`SetRel`), so each `contains` answers alike, `denoteN` being injective on a well formed
store, and the twin's run is a value outcome of upstream's at `ModelIO`, which `closureOrder_ok`
speaks of.

`uses` is upstream's `partial` `constsOf`, so that no equation relates the two; nothing proved of
the merge or the emission reads what it holds.  The theorem here says only that its handles
denote (`constsGo_run`): a twin's `CEntry` denotes upstream's with those names as its `uses`.
-/
module

public import ConRon.Bridge.Frontend.Olean.Files
import ConRon.Bridge.SpecsL
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins OleanFs closureGo addN constsGo CEntry entryDeps)
open ConLeche.Frontend.Olean (ImportF ImportRec SearchPath CEntryF CKindF mkN)

/-! ## Lists, sets -/

/-- con-leche: none — a handle list against a list of values. -/
theorem listRel_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → ListRel (fun a b => f a = some b) l ys
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact .nil
  | x :: l, ys, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    obtain ⟨ys', hys, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact .cons hy (listRel_of_mapM hys)

theorem ListRel.mono' {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) :
    ∀ {l : List α} {ys : List β}, ListRel R l ys → ListRel R' l ys
  | _, _, .nil => .nil
  | _, _, .cons a b => .cons (h _ _ a) (ListRel.mono' h b)

theorem ListRel.map_left {α β γ : Type} {R : α → β → Prop} {f : γ → α} :
    ∀ {l : List γ} {ys : List β}, ListRel (fun c b => R (f c) b) l ys → ListRel R (l.map f) ys
  | _, _, .nil => .nil
  | _, _, .cons a b => .cons a (ListRel.map_left b)

theorem ListRel.map_right {α β γ : Type} {R : α → β → Prop} {f : γ → β} :
    ∀ {l : List α} {ys : List γ}, ListRel (fun a c => R a (f c)) l ys → ListRel R l (ys.map f)
  | _, _, .nil => .nil
  | _, _, .cons a b => .cons a (ListRel.map_right b)

/-- The name relation. -/
abbrev NR (st : EStore) : NIdx → ConLeche.Name → Prop := fun h n => denoteN st.ns h = some n

theorem NR_list_ext {st st' : EStore} (hx : Ext st st') {l : List NIdx} {ys : List ConLeche.Name}
    (h : ListRel (NR st) l ys) : ListRel (NR st') l ys :=
  ListRel.mono' (fun _ _ ha => denoteN_ext ha hx) h

/-- con-leche: none — **a set of handles against a set of names**: each holds what the other's
elements denote. -/
structure SetRel (st : EStore) (t : Std.HashSet NIdx) (tC : Std.HashSet ConLeche.Name) : Prop where
  fwd : ∀ x ∈ t, ∃ n, denoteN st.ns x = some n ∧ n ∈ tC
  bwd : ∀ n ∈ tC, ∃ x ∈ t, denoteN st.ns x = some n

theorem SetRel.empty (st : EStore) : SetRel st {} {} :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem SetRel.ext {st st' : EStore} {t : Std.HashSet NIdx} {tC : Std.HashSet ConLeche.Name}
    (h : SetRel st t tC) (hx : Ext st st') : SetRel st' t tC :=
  ⟨fun x hm => by
      obtain ⟨n, a, b⟩ := h.fwd x hm
      exact ⟨n, denoteN_ext a hx, b⟩,
   fun n hm => by
      obtain ⟨x, a, b⟩ := h.bwd n hm
      exact ⟨x, a, denoteN_ext b hx⟩⟩

theorem SetRel.insert {st : EStore} {t : Std.HashSet NIdx} {tC : Std.HashSet ConLeche.Name}
    (h : SetRel st t tC) {x : NIdx} {n : ConLeche.Name} (hd : denoteN st.ns x = some n) :
    SetRel st (t.insert x) (tC.insert n) := by
  constructor
  · intro y hy
    rw [Std.HashSet.mem_insert] at hy
    rcases hy with hy | hy
    · have : x = y := by simpa using hy
      subst this
      exact ⟨n, hd, by simp [Std.HashSet.mem_insert]⟩
    · obtain ⟨k, a, b⟩ := h.fwd y hy
      exact ⟨k, a, by simp [Std.HashSet.mem_insert, b]⟩
  · intro k hk
    rw [Std.HashSet.mem_insert] at hk
    rcases hk with hk | hk
    · have : n = k := by simpa using hk
      subst this
      exact ⟨x, by simp [Std.HashSet.mem_insert], hd⟩
    · obtain ⟨y, a, b⟩ := h.bwd k hk
      exact ⟨y, by simp [Std.HashSet.mem_insert, a], b⟩

/-- `contains` answers alike. -/
theorem SetRel.contains {st : EStore} (hw : NStoreWF st.ns) {t : Std.HashSet NIdx}
    {tC : Std.HashSet ConLeche.Name} (h : SetRel st t tC) {x : NIdx} {n : ConLeche.Name}
    (hd : denoteN st.ns x = some n) : t.contains x = tC.contains n := by
  cases hc : tC.contains n with
  | true =>
    obtain ⟨y, a, b⟩ := h.bwd n (Std.HashSet.mem_iff_contains.mpr hc)
    have : y = x := denoteN_inj hw b hd
    subst this
    exact Std.HashSet.mem_iff_contains.mp a
  | false =>
    cases hx : t.contains x with
    | false => rfl
    | true =>
      obtain ⟨k, a, b⟩ := h.fwd x (Std.HashSet.mem_iff_contains.mpr hx)
      have : k = n := Option.some.inj (a.symm.trans hd)
      subst this
      rw [Std.HashSet.mem_iff_contains, hc] at b
      cases b

/-! ## The closure's walk -/

/-- A stack of the walk against upstream's. -/
abbrev StackR (st : EStore) : NIdx × Bool → ConLeche.Name × Bool → Prop :=
  fun a b => denoteN st.ns a.1 = some b.1 ∧ a.2 = b.2

theorem StackR_list_ext {st st' : EStore} (hx : Ext st st') {l : List (NIdx × Bool)}
    {ys : List (ConLeche.Name × Bool)} (h : ListRel (StackR st) l ys) : ListRel (StackR st') l ys :=
  ListRel.mono' (fun _ _ ha => ⟨denoteN_ext ha.1 hx, ha.2⟩) h

theorem array_rel_push {st : EStore} {out : Array NIdx} {outC : Array ConLeche.Name}
    (h : ListRel (NR st) out.toList outC.toList) {x : NIdx} {n : ConLeche.Name}
    (hd : denoteN st.ns x = some n) : ListRel (NR st) (out.push x).toList (outC.push n).toList := by
  simp only [Array.toList_push]
  exact ListRel.append h (.cons hd .nil)

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:96-123 closureGo — `kids`, related. -/
theorem kids_rel {st : EStore} (hw : NStoreWF st.ns) {t : Std.HashSet NIdx}
    {tC : Std.HashSet ConLeche.Name} (hs : SetRel st t tC) :
    ∀ {l : List NIdx} {ys : List ConLeche.Name}, ListRel (NR st) l ys →
      ListRel (StackR st) ((l.filter (!t.contains ·)).map (·, false))
        ((ys.filter (!tC.contains ·)).map (·, false))
  | _, _, .nil => .nil
  | x :: xs, y :: ys, .cons a b => by
    have hc := hs.contains hw a
    have ih := kids_rel hw hs b
    simp only [List.filter_cons, hc]
    split
    · exact .cons ⟨a, rfl⟩ ih
    · exact ih

/-- The modules of some imports, related. -/
theorem modules_rel {st : EStore} {imps : Array (ImportF NIdx)} {zs : Array ImportRec}
    (h : ListRel (fun a b => denoteImport st a = some b) imps.toList zs.toList) :
    ListRel (NR st) (imps.map (·.module)).toList (zs.map (·.module)).toList := by
  simp only [Array.toList_map]
  refine ListRel.map_left (ListRel.map_right (ListRel.mono' ?_ h))
  intro a b hab
  simp only [denoteImport, ImportF.mapM] at hab
  obtain ⟨y, hy, hab⟩ := ConLeche.Frontend.Olean.bind_some_left hab
  simp only [pure, Option.some.injEq] at hab
  subst hab
  exact hy

/-- A search of the imports that finds nothing, on both sides. -/
theorem find_none_rel {st : EStore} (hw : NStoreWF st.ns) {a aC b bC}
    (ha : SetRel st a aC) (hb : SetRel st b bC) :
    ∀ {l : List NIdx} {ys : List ConLeche.Name}, ListRel (NR st) l ys →
      l.find? (fun i => a.contains i && !b.contains i) = none →
      ys.find? (fun i => aC.contains i && !bC.contains i) = none
  | _, _, .nil, _ => rfl
  | x :: xs, y :: ys, .cons h1 h2, h => by
    simp only [List.find?_cons] at h ⊢
    rw [← ha.contains hw h1, ← hb.contains hw h1]
    cases hp : (a.contains x && !b.contains x) with
    | true => simp [hp] at h
    | false =>
      simp only [hp] at h ⊢
      exact find_none_rel hw ha hb h2 h

/-- con-leche: ConLeche/Verify/Frontend/Olean/Closure.lean:105 closureGo_ok — **the twin's walk
is a value outcome of upstream's**, the same step for step. -/
theorem closureGo_run {pk : OleanPins} {F : FS} {sp : SearchPath} :
    ∀ (fuel : Nat) (stack : List (NIdx × Bool)) (seen done : Std.HashSet NIdx) (out outF : Array NIdx)
      (stackC : List (ConLeche.Name × Bool)) (seenC doneC : Std.HashSet ConLeche.Name)
      (outC : Array ConLeche.Name) {s s' : AState}, Ctx pk s →
      ListRel (StackR s.store) stack stackC → SetRel s.store seen seenC → SetRel s.store done doneC →
      ListRel (NR s.store) out.toList outC.toList →
      closureGo (modelFs F) pk sp fuel stack seen done out s = .ok (outF, s') →
      ParseStep s s' ∧ ∃ outFC : Array ConLeche.Name,
        (ConLeche.Frontend.Olean.closureGo sp fuel stackC seenC doneC outC : ModelIO _) F
          (.ok (.ok outFC)) ∧ ListRel (NR s'.store) outF.toList outFC.toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack seen done out outF stackC seenC doneC outC s s' hctx hst hse hdo hou h
    cases hst with
    | nil =>
      rw [closureGo] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      cases hv
      subst hs
      exact ⟨ParseStep.refl hctx.ok, outC, by rw [ConLeche.Frontend.Olean.closureGo]; rfl, hou⟩
    | cons _ _ =>
      rw [closureGo] at h
      cases h
  | succ fuel ih =>
    intro stack seen done out outF stackC seenC doneC outC s s' hctx hst hse hdo hou h
    cases hst with
    | nil =>
      rw [closureGo] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      cases hv
      subst hs
      exact ⟨ParseStep.refl hctx.ok, outC, by rw [ConLeche.Frontend.Olean.closureGo]; rfl, hou⟩
    | @cons a b as bs hab hrest =>
      obtain ⟨m, f⟩ := a
      obtain ⟨mC, fC⟩ := b
      obtain ⟨hm, hf⟩ := hab
      simp only at hm hf
      subst hf
      cases f with
      | true =>
        rw [closureGo] at h
        rw [ConLeche.Frontend.Olean.closureGo]
        exact ih _ _ _ _ _ _ _ _ _ hctx hrest hse (hdo.insert hm) (array_rel_push hou hm) h
      | false =>
        rw [closureGo] at h
        rw [ConLeche.Frontend.Olean.closureGo]
        have hw := nsWF_of_StateOK hctx.ok
        have hcs := hse.contains hw hm
        by_cases hc : seen.contains m = true
        · have hcC : seenC.contains mC = true := by rw [← hcs]; exact hc
          simp only [hc, ↓reduceIte] at h
          rw [ite_eq_left hcC]
          exact ih _ _ _ _ _ _ _ _ _ hctx hrest hse hdo hou h
        · have hcC : ¬ seenC.contains mC = true := by rw [← hcs]; exact hc
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
          rw [ite_eq_right hcC]
          obtain ⟨imps, s₁, h1, h2⟩ := AM.bind_ok h
          obtain ⟨hst1, zs, hz, hd⟩ := moduleImports_run hm hctx h1
          have hctx1 := hctx.step hst1
          have hw1 := nsWF_of_StateOK hctx1.ok
          have hm1 := denoteN_ext hm hst1.ext
          have hse1 := (hse.ext hst1.ext).insert hm1
          have hdo1 := hdo.ext hst1.ext
          have hmods := modules_rel (st := s₁.store) (listRel_of_mapM hd)
          cases hfind : (imps.map (·.module)).find?
              (fun i => (seen.insert m).contains i && !done.contains i) with
          | some c =>
            simp only [hfind] at h2
            obtain ⟨x, s₂, h3, h4⟩ := AM.bind_ok h2
            obtain ⟨y, s₃, h5, h6⟩ := AM.bind_ok h4
            cases h6
          | none =>
            simp only [hfind] at h2
            have hfindC : (zs.map (·.module)).find?
                (fun i => (seenC.insert mC).contains i && !doneC.contains i) = none := by
              have hl := find_none_rel hw1 hse1 hdo1 hmods (by
                rw [Array.find?_toList]; exact hfind)
              rw [Array.find?_toList] at hl
              exact hl
            have hrec := ih _ _ _ _ _
              ((((zs.map (·.module)).toList.filter (!(seenC.insert mC).contains ·)).map (·, false))
                ++ (mC, true) :: bs) _ _ _ hctx1
              (ListRel.append (kids_rel hw1 hse1 hmods)
                (.cons ⟨hm1, rfl⟩ (StackR_list_ext hst1.ext hrest)))
              hse1 hdo1 (NR_list_ext hst1.ext hou) h2
            obtain ⟨hst2, outFC, hC, hR⟩ := hrec
            refine ⟨hst1.trans hst2, outFC, ?_, hR⟩
            refine (ModelIO.bind_ok _ _ _ _).2 ⟨.ok zs, hz, ?_⟩
            dsimp only
            rw [hfindC]
            exact hC

/-! ## The reader's known handles -/

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:22-23 mkN — the handles the reader interns
before any file, denoting. -/
structure PinsRel (st : EStore) (pk : OleanPins) : Prop where
  nulls : NullsRel st pk
  nNat : denoteN st.ns pk.nNat = some (mkN ["Nat"])
  nCharOfNat : denoteN st.ns pk.nCharOfNat = some (mkN ["Char", "ofNat"])
  nStringOfList : denoteN st.ns pk.nStringOfList = some (mkN ["String", "ofList"])
  nEq : denoteN st.ns pk.nEq = some (mkN ["Eq"])
  nQuot : denoteN st.ns pk.nQuot = some (mkN ["Quot"])
  nQuotMk : denoteN st.ns pk.nQuotMk = some (mkN ["Quot", "mk"])
  nQuotLift : denoteN st.ns pk.nQuotLift = some (mkN ["Quot", "lift"])
  nQuotInd : denoteN st.ns pk.nQuotInd = some (mkN ["Quot", "ind"])

theorem PinsRel.ext {st st' : EStore} {pk : OleanPins} (h : PinsRel st pk) (hx : Ext st st') :
    PinsRel st' pk :=
  ⟨h.nulls.ext hx, denoteN_ext h.nNat hx, denoteN_ext h.nCharOfNat hx,
    denoteN_ext h.nStringOfList hx, denoteN_ext h.nEq hx, denoteN_ext h.nQuot hx,
    denoteN_ext h.nQuotMk hx, denoteN_ext h.nQuotLift hx, denoteN_ext h.nQuotInd hx⟩

/-- A name's component interned. -/
theorem internStr_step {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    {p h : NIdx} {q : ConLeche.Name} {str : String} (hp : denoteN s.store.ns p = some q)
    (hin : internNNode (.str p str) s = .ok (h, s')) :
    IStep s s' ∧ denoteN s'.store.ns h = some (.str q str) := by
  obtain ⟨hst, -, hd⟩ := internNNode_istep hok hoff (v := .str p str)
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc; exact nview_isSome_of_denote hp) hin
  refine ⟨hst, ?_⟩
  rw [hd]
  simp only [denoteNView, denoteN_ext hp hst.ext, Option.map_some]

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:22-23 mkN -/
theorem oleanPins_run {pk : OleanPins} {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false)
    (h : ConRon.Arena.Frontend.Olean.oleanPins s = .ok (pk, s')) :
    ParseStep s s' ∧ PinsRel s'.store pk := by
  unfold ConRon.Arena.Frontend.Olean.oleanPins at h
  obtain ⟨anon, s1, h1, h⟩ := AM.bind_ok h
  obtain ⟨hs1, -, d1⟩ := internNNode_istep hok hoff (v := .anonymous)
    (by intro c hc; simp [NNodeView.children] at hc) h1
  have d1 : denoteN s1.store.ns anon = some .anonymous := by rw [d1]; rfl
  obtain ⟨zero, s2, h2, h⟩ := AM.bind_ok h
  obtain ⟨hs2, -, d2⟩ := internLNode_istep hs1.ok hs1.off (v := .zero)
    ⟨by intro c hc; simp [LNodeView.lchildren] at hc,
     by intro c hc; simp [LNodeView.nchildren] at hc⟩ h2
  have d2 : denoteL s2.store.ls zero = some .zero := by rw [d2]; rfl
  obtain ⟨nil, s3, h3, h⟩ := AM.bind_ok h
  obtain ⟨hs3, d3⟩ := internLsNode_istep hs2.ok hs2.off (v := [])
    (lsViewOK_of_denoteLList (st := s2.store) _ [] rfl) h3
  have d3 : denoteLs s3.store.lss nil = some [] := by rw [d3]; rfl
  obtain ⟨nNat, s4, h4, h⟩ := AM.bind_ok h
  have x12 := (hs2.ext.trans hs3.ext)
  obtain ⟨hs4, d4⟩ := internStr_step hs3.ok hs3.off (denoteN_ext d1 x12) h4
  obtain ⟨nChar, s5, h5, h⟩ := AM.bind_ok h
  obtain ⟨hs5, d5⟩ := internStr_step hs4.ok hs4.off (denoteN_ext d1 (x12.trans hs4.ext)) h5
  obtain ⟨nCharOfNat, s6, h6, h⟩ := AM.bind_ok h
  obtain ⟨hs6, d6⟩ := internStr_step hs5.ok hs5.off d5 h6
  obtain ⟨nString, s7, h7, h⟩ := AM.bind_ok h
  have x16 := ((x12.trans hs4.ext).trans hs5.ext).trans hs6.ext
  obtain ⟨hs7, d7⟩ := internStr_step hs6.ok hs6.off (denoteN_ext d1 x16) h7
  obtain ⟨nStringOfList, s8, h8, h⟩ := AM.bind_ok h
  obtain ⟨hs8, d8⟩ := internStr_step hs7.ok hs7.off d7 h8
  obtain ⟨nEq, s9, h9, h⟩ := AM.bind_ok h
  have x18 := (x16.trans hs7.ext).trans hs8.ext
  obtain ⟨hs9, d9⟩ := internStr_step hs8.ok hs8.off (denoteN_ext d1 x18) h9
  obtain ⟨nQuot, s10, h10, h⟩ := AM.bind_ok h
  obtain ⟨hs10, d10⟩ := internStr_step hs9.ok hs9.off (denoteN_ext d1 (x18.trans hs9.ext)) h10
  obtain ⟨nQuotMk, s11, h11, h⟩ := AM.bind_ok h
  obtain ⟨hs11, d11⟩ := internStr_step hs10.ok hs10.off d10 h11
  obtain ⟨nQuotLift, s12, h12, h⟩ := AM.bind_ok h
  obtain ⟨hs12, d12⟩ := internStr_step hs11.ok hs11.off (denoteN_ext d10 hs11.ext) h12
  obtain ⟨nQuotInd, s13, h13, h⟩ := AM.bind_ok h
  obtain ⟨hs13, d13⟩ := internStr_step hs12.ok hs12.off
    (denoteN_ext d10 (hs11.ext.trans hs12.ext)) h13
  obtain ⟨hv, hs⟩ := AM.pure_ok h
  cases hv
  subst hs
  have hall := hs1.trans hs2 |>.trans hs3 |>.trans hs4 |>.trans hs5 |>.trans hs6 |>.trans hs7
    |>.trans hs8 |>.trans hs9 |>.trans hs10 |>.trans hs11 |>.trans hs12 |>.trans hs13
  have e13 := hs13.ext
  have e12 := hs12.ext.trans e13
  have e11 := hs11.ext.trans e12
  have e10 := hs10.ext.trans e11
  have e9 := hs9.ext.trans e10
  have e8 := hs8.ext.trans e9
  have e7 := hs7.ext.trans e8
  have e6 := hs6.ext.trans e7
  have e5 := hs5.ext.trans e6
  have e4 := hs4.ext.trans e5
  have e3 := hs3.ext.trans e4
  have e2 := hs2.ext.trans e3
  refine ⟨hall.toParse hoff, ⟨⟨denoteN_ext d1 e2, denoteL_ext d2 e3, denoteLs_ext d3 e4⟩,
    denoteN_ext d4 e5, denoteN_ext d6 e7, denoteN_ext d8 e9, denoteN_ext d9 e10,
    denoteN_ext d10 e11, denoteN_ext d11 e12, denoteN_ext d12 e13, d13⟩⟩

/-! ## What a constant mentions -/

theorem opt2_isSome {α β γ : Type} {f : α → β → γ} {a : Option α} {b : Option β}
    (h : (opt2 f a b).isSome = true) : a.isSome = true ∧ b.isSome = true := by
  cases a <;> cases b <;> simp_all [opt2]

theorem opt3_isSome {α β γ δ : Type} {f : α → β → γ → δ} {a : Option α} {b : Option β}
    {c : Option γ} (h : (opt3 f a b c).isSome = true) :
    a.isSome = true ∧ b.isSome = true ∧ c.isSome = true := by
  cases a <;> cases b <;> cases c <;> simp_all [opt3]

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo — **the names it finds
denote**, on a store it leaves alone. -/
theorem constsGo_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hp : PinsRel s.store pk) :
    ∀ (fuel : Nat) (es : List EIdx) (seen : Std.HashSet EIdx) (seenN : Std.HashSet NIdx)
      (out out' : Array NIdx) {s' : AState},
      (∀ e ∈ es, (denoteE s.store e).isSome) → (∀ n ∈ out, (denoteN s.store.ns n).isSome) →
      constsGo pk fuel es seen seenN out s = .ok (out', s') →
      s' = s ∧ ∀ n ∈ out', (denoteN s.store.ns n).isSome := by
  have hadd : ∀ {seenN : Std.HashSet NIdx} {out : Array NIdx} {n : NIdx},
      (∀ k ∈ out, (denoteN s.store.ns k).isSome) → (denoteN s.store.ns n).isSome →
      ∀ k ∈ (addN seenN out n).2, (denoteN s.store.ns k).isSome := by
    intro seenN out n ho hn k hk
    simp only [addN] at hk
    split at hk
    · exact ho k hk
    · simp only [Array.mem_push] at hk
      rcases hk with hk | rfl
      · exact ho k hk
      · exact hn
  intro fuel
  induction fuel with
  | zero =>
    intro es seen seenN out out' s' he ho h
    cases es with
    | nil =>
      rw [constsGo] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      cases hv
      exact ⟨hs, ho⟩
    | cons _ _ =>
      rw [constsGo] at h
      cases h
  | succ fuel ih =>
    intro es seen seenN out out' s' he ho h
    cases es with
    | nil =>
      rw [constsGo] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      cases hv
      exact ⟨hs, ho⟩
    | cons e rest =>
      rw [constsGo] at h
      have hem : (denoteE s.store e).isSome := he e (by simp)
      have hrest : ∀ x ∈ rest, (denoteE s.store x).isSome :=
        fun x hx => he x (List.mem_cons_of_mem _ hx)
      have hwk : ∀ {seen : Std.HashSet EIdx} {seenN : Std.HashSet NIdx} {out : Array NIdx}
          {xs : List EIdx}, (∀ x ∈ xs, (denoteE s.store x).isSome) →
          (∀ n ∈ out, (denoteN s.store.ns n).isSome) →
          constsGo pk fuel (xs ++ rest) seen seenN out s = .ok (out', s') →
          s' = s ∧ ∀ n ∈ out', (denoteN s.store.ns n).isSome := by
        intro seen seenN out xs hx hn hr
        refine ih _ _ _ _ _ (fun x hm => ?_) hn hr
        rcases List.mem_append.mp hm with hm | hm
        · exact hx x hm
        · exact hrest x hm
      have hnil : ∀ {seen : Std.HashSet EIdx} {seenN : Std.HashSet NIdx} {out : Array NIdx},
          (∀ n ∈ out, (denoteN s.store.ns n).isSome) →
          constsGo pk fuel rest seen seenN out s = .ok (out', s') →
          s' = s ∧ ∀ n ∈ out', (denoteN s.store.ns n).isSome :=
        fun hn hr => hwk (xs := []) (by simp) hn hr
      by_cases c1 : (e.tag == ETag.const || e.tag == ETag.lit) = true
      · simp only [c1, ↓reduceIte] at h
        obtain ⟨v, s₁, h1, h2⟩ := AM.bind_ok h
        obtain ⟨hs1, hv⟩ := view_run h1
        rw [hs1] at h2
        rw [denoteE_view_eq hok.wf hv] at hem
        cases v with
        | const n us =>
          exact hnil (hadd ho (opt2_isSome hem).1) h2
        | lit l =>
          cases l with
          | natVal k => exact hnil (hadd ho (by rw [hp.nNat]; rfl)) h2
          | strVal t =>
            exact hnil (hadd (hadd ho (by rw [hp.nCharOfNat]; rfl))
              (by rw [hp.nStringOfList]; rfl)) h2
        | bvar _ => exact hnil ho h2
        | fvar _ _ => exact hnil ho h2
        | sort _ => exact hnil ho h2
        | app _ _ => exact hnil ho h2
        | lam _ _ => exact hnil ho h2
        | forallE _ _ => exact hnil ho h2
        | letE _ _ _ => exact hnil ho h2
        | proj _ _ _ => exact hnil ho h2
      · simp only [c1, Bool.false_eq_true, ↓reduceIte] at h
        by_cases c2 : (e.tag == ETag.bvar || e.tag == ETag.sort || seen.contains e) = true
        · simp only [c2, ↓reduceIte] at h
          exact hnil ho h
        · simp only [c2, Bool.false_eq_true, ↓reduceIte] at h
          by_cases c3 : ETag.proj < e.tag
          · simp only [c3, ↓reduceIte] at h
            exact hnil ho h
          simp only [c3, ↓reduceIte] at h
          obtain ⟨v, s₁, h1, h2⟩ := AM.bind_ok h
          obtain ⟨hs1, hv⟩ := view_run h1
          rw [hs1] at h2
          rw [denoteE_view_eq hok.wf hv] at hem
          cases v with
          | app f a =>
            have := opt2_isSome hem
            exact hwk (xs := [f, a]) (by simpa using this) ho h2
          | lam t b =>
            have := opt2_isSome hem
            exact hwk (xs := [t, b]) (by simpa using this) ho h2
          | forallE t b =>
            have := opt2_isSome hem
            exact hwk (xs := [t, b]) (by simpa using this) ho h2
          | letE t w b =>
            have := opt3_isSome hem
            exact hwk (xs := [t, w, b]) (by simpa using this) ho h2
          | proj n i x =>
            have := opt2_isSome hem
            exact hwk (xs := [x]) (by simpa using this.2) ho h2
          | fvar k t =>
            have : (denoteE s.store t).isSome := by simpa [denoteEView] using hem
            exact hwk (xs := [t]) (by simpa using this) ho h2
          | bvar _ => exact hnil ho h2
          | sort _ => exact hnil ho h2
          | const _ _ => exact hnil ho h2
          | lit _ => exact hnil ho h2

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:64-69 constsOf -/
theorem constsOf_run {pk : OleanPins} {s s' : AState} (hok : StateOK s) (hp : PinsRel s.store pk)
    {es : List EIdx} {out : Array NIdx} (he : ∀ e ∈ es, (denoteE s.store e).isSome)
    (h : ConRon.Arena.Frontend.Olean.constsOf pk es s = .ok (out, s')) :
    s' = s ∧ ∀ n ∈ out, (denoteN s.store.ns n).isSome :=
  constsGo_run hok hp _ _ _ _ _ _ he (fun _ hn => by simp at hn) h

/-! ## A loaded constant, a loaded module -/

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:71-75 CEntry — **a stored constant read
back**, with the twin's own `uses`. -/
@[expose] def denoteCEntry (st : EStore) (x : CEntry) : Option ConLeche.Frontend.Olean.CEntry := do
  let e ← denoteEntry st x.c
  let u ← x.uses.toList.mapM (denoteN st.ns)
  pure { toCEntryF := e, uses := u.toArray }

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:135-138 Loaded -/
@[expose] def denoteLoaded (st : EStore) (l : ConRon.Arena.Frontend.Olean.Loaded) :
    Option ConLeche.Frontend.Olean.Loaded := do
  let n ← denoteN st.ns l.name
  let cs ← l.constants.toList.mapM (denoteCEntry st)
  pure ⟨n, cs.toArray⟩

theorem list_some_of {α β : Type} {f : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    obtain ⟨ys, hys⟩ := list_some_of l (fun w hw => h w (List.mem_cons_of_mem _ hw))
    exact ⟨y :: ys, by simp only [List.mapM_cons, hy, hys]; rfl⟩

theorem entryDeps_eq (c : CEntryF NIdx EIdx) : entryDeps c = c.exprs := by
  rcases c with ⟨n, l, t, k⟩
  cases k <;> rfl

theorem denoteCEntry_ext {st st' : EStore} (hx : Ext st st') {c : CEntry}
    {z : ConLeche.Frontend.Olean.CEntry} (h : denoteCEntry st c = some z) :
    denoteCEntry st' c = some z := by
  unfold denoteCEntry at h ⊢
  obtain ⟨e, h1, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  obtain ⟨u, h2, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  simp only [denoteEntry_ext hx h1, list_mono (fun _ _ hy => denoteN_ext hy hx) _ h2]
  exact h

theorem denoteLoaded_ext {st st' : EStore} (hx : Ext st st') {c : ConRon.Arena.Frontend.Olean.Loaded}
    {z : ConLeche.Frontend.Olean.Loaded} (h : denoteLoaded st c = some z) :
    denoteLoaded st' c = some z := by
  unfold denoteLoaded at h ⊢
  obtain ⟨e, h1, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  obtain ⟨u, h2, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  simp only [denoteN_ext h1 hx, list_mono (fun _ _ hy => denoteCEntry_ext hx hy) _ h2]
  exact h

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:89-92 CEntry.ofRead -/
theorem ofRead_run {pk : OleanPins} {s s' : AState} (hok : StateOK s) (hp : PinsRel s.store pk)
    {c : CEntryF NIdx EIdx} {e : CEntryF ConLeche.Name Expr} (hc : denoteEntry s.store c = some e)
    {x : CEntry} (h : ConRon.Arena.Frontend.Olean.CEntry.ofRead pk c s = .ok (x, s')) :
    s' = s ∧ ∃ z, denoteCEntry s.store x = some z ∧ z.toCEntryF = e := by
  unfold ConRon.Arena.Frontend.Olean.CEntry.ofRead at h
  obtain ⟨u, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hv, hs⟩ := AM.pure_ok h2
  cases hv
  subst hs
  obtain ⟨hs1, hu⟩ := constsOf_run hok hp (es := entryDeps c) (fun y hy => by
    rw [entryDeps_eq] at hy
    exact (ConLeche.Frontend.Olean.CEntryF.mapM_some c hc).2 y hy) h1
  obtain ⟨ys, hys⟩ := list_some_of (f := denoteN s.store.ns) u.toList (fun n hn => hu n (by simpa using hn))
  subst hs1
  refine ⟨rfl, { toCEntryF := e, uses := ys.toArray }, ?_, rfl⟩
  simp only [denoteCEntry, hc, hys]
  rfl

/-- The constants of a module with what each mentions. -/
theorem ofReadAll_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hp : PinsRel s.store pk) :
    ∀ (cs : List (CEntryF NIdx EIdx)) {es : List (CEntryF ConLeche.Name Expr)} {xs : List CEntry}
      {s' : AState}, cs.mapM (denoteEntry s.store) = some es →
      cs.mapM (ConRon.Arena.Frontend.Olean.CEntry.ofRead pk) s = .ok (xs, s') →
      s' = s ∧ ∃ zs, xs.mapM (denoteCEntry s.store) = some zs ∧ zs.map (·.toCEntryF) = es
  | [], es, xs, s', he, h => by
    simp only [List.mapM_nil] at he h
    cases he
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    exact ⟨hs, [], rfl, rfl⟩
  | c :: cs, es, xs, s', he, h => by
    simp only [List.mapM_cons] at he h
    obtain ⟨e, he1, he⟩ := ConLeche.Frontend.Olean.bind_some_left he
    obtain ⟨es', he2, he⟩ := ConLeche.Frontend.Olean.bind_some_left he
    simp only [pure, Option.some.injEq] at he
    subst he
    obtain ⟨x, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨xs', s₂, h2, h⟩ := AM.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    obtain ⟨hs1, z, hz, hzc⟩ := ofRead_run hok hp he1 h1
    subst hs1
    obtain ⟨hs2, zs, hzs, hmap⟩ := ofReadAll_run hok hp cs he2 h2
    subst hs2
    refine ⟨rfl, z :: zs, ?_, by simp [hzc, hmap]⟩
    simp only [List.mapM_cons, hz, hzs]
    rfl

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:140-146 loadModule -/
theorem loadModule_run {pk : OleanPins} {F : FS} {sp : SearchPath} {m : NIdx} {mn : ConLeche.Name}
    {l : ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState} (hctx : Ctx pk s)
    (hp : PinsRel s.store pk) (hm : denoteN s.store.ns m = some mn)
    (h : ConRon.Arena.Frontend.Olean.loadModule (modelFs F) pk sp m s = .ok (l, s')) :
    ParseStep s s' ∧ ∃ lC dC, denoteLoaded s'.store l = some lC ∧ lC.name = mn ∧
      (ConLeche.Frontend.Olean.readView sp mn .private : ModelIO _) F (.ok (.ok dC)) ∧
      lC.constants.map (·.toCEntryF) = dC.constants := by
  unfold ConRon.Arena.Frontend.Olean.loadModule at h
  obtain ⟨d, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hst, dC, hd1, hd2⟩ := readView_run hm hctx h1
  have hctx1 := hctx.step hst
  have hp1 := hp.ext hst.ext
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hv, hs⟩ := AM.pure_ok h4
  cases hv
  subst hs
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h3
  obtain ⟨xs, s₃, h5, h6⟩ := AM.bind_ok h3
  obtain ⟨hv, hs⟩ := AM.pure_ok h6
  cases hv
  subst hs
  unfold denoteMod at hd2
  obtain ⟨is, h7, hd2⟩ := ConLeche.Frontend.Olean.bind_some_left hd2
  obtain ⟨es, h8, hd2⟩ := ConLeche.Frontend.Olean.bind_some_left hd2
  simp only [pure, Option.some.injEq] at hd2
  subst hd2
  obtain ⟨hs3, zs, hzs, hmap⟩ := ofReadAll_run hctx1.ok hp1 _ h8 h5
  subst hs3
  refine ⟨hst, ⟨mn, zs.toArray⟩, _, ?_, rfl, hd1, ?_⟩
  · simp only [denoteLoaded, denoteN_ext hm hst.ext, hzs]
    rfl
  · simp [hmap]

/-! ## The closure -/

theorem rootsStack_rel {st : EStore} :
    ∀ {l : List NIdx} {ys : List ConLeche.Name}, ListRel (NR st) l ys →
      ListRel (StackR st) (l.map (·, false)) (ys.map (·, false))
  | _, _, .nil => .nil
  | _, _, .cons a b => .cons ⟨a, rfl⟩ (rootsStack_rel b)

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:129-131 closureOrder -/
theorem closureOrder_run {pk : OleanPins} {F : FS} {sp : SearchPath} {roots order : Array NIdx}
    {rootsC : Array ConLeche.Name} {s s' : AState} (hctx : Ctx pk s)
    (hr : ListRel (NR s.store) roots.toList rootsC.toList)
    (h : ConRon.Arena.Frontend.Olean.closureOrder (modelFs F) pk sp roots s = .ok (order, s')) :
    ParseStep s s' ∧ ∃ orderC : Array ConLeche.Name,
      (ConLeche.Frontend.Olean.closureOrder sp rootsC : ModelIO _) F (.ok (.ok orderC)) ∧
      ListRel (NR s'.store) order.toList orderC.toList :=
  closureGo_run _ _ _ _ _ _ _ _ _ _ hctx (rootsStack_rel hr) (SetRel.empty _) (SetRel.empty _) .nil h

/-- The modules of the order, loaded. -/
theorem loadAll_run {pk : OleanPins} {F : FS} {sp : SearchPath} :
    ∀ (l : List NIdx) {ns : List ConLeche.Name} {ys : List ConRon.Arena.Frontend.Olean.Loaded}
      {s s' : AState}, Ctx pk s → PinsRel s.store pk → ListRel (NR s.store) l ns →
      l.mapM (ConRon.Arena.Frontend.Olean.loadModule (modelFs F) pk sp) s = .ok (ys, s') →
      ParseStep s s' ∧ ∃ lsC, ListRel (fun y c => denoteLoaded s'.store y = some c) ys lsC ∧
        lsC.map (·.name) = ns ∧ ∀ lC ∈ lsC, ∃ dC,
          (ConLeche.Frontend.Olean.readView sp lC.name .private : ModelIO _) F (.ok (.ok dC)) ∧
          lC.constants.map (·.toCEntryF) = dC.constants
  | [], ns, ys, s, s', hctx, _, hl, h => by
    cases hl
    simp only [List.mapM_nil] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hctx.ok, [], .nil, rfl, by simp⟩
  | m :: l, ns, ys, s, s', hctx, hp, hl, h => by
    cases hl with
    | @cons _ mn _ ns' hm hrest =>
      simp only [List.mapM_cons] at h
      obtain ⟨y, s₁, h1, h⟩ := AM.bind_ok h
      obtain ⟨ys', s₂, h2, h⟩ := AM.bind_ok h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      cases hv
      subst hs
      obtain ⟨hst1, lC, dC, hd, hn, hv, hc⟩ := loadModule_run hctx hp hm h1
      obtain ⟨hst2, lsC, hR, hmap, hall⟩ := loadAll_run l (hctx.step hst1) (hp.ext hst1.ext)
        (NR_list_ext hst1.ext hrest) h2
      refine ⟨hst1.trans hst2, lC :: lsC, .cons (denoteLoaded_ext hst2.ext hd) hR, ?_, ?_⟩
      · simp [hn, hmap]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨dC, by rw [hn]; exact hv, hc⟩
        · exact hall x hx

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:148-158 loadClosure — **the closure,
loaded, on the snapshot**: the walk's order is upstream's, and each module its private view. -/
theorem loadClosure_run {pk : OleanPins} {F : FS} {sp : SearchPath} {roots : Array NIdx}
    {rootsC : Array ConLeche.Name} {ls : Array ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState}
    (hctx : Ctx pk s) (hp : PinsRel s.store pk)
    (hr : ListRel (NR s.store) roots.toList rootsC.toList)
    (h : ConRon.Arena.Frontend.Olean.loadClosure (modelFs F) pk sp roots s = .ok (ls, s')) :
    ParseStep s s' ∧ ∃ (orderC : Array ConLeche.Name) (lsC : List ConLeche.Frontend.Olean.Loaded),
      (ConLeche.Frontend.Olean.closureOrder sp rootsC : ModelIO _) F (.ok (.ok orderC)) ∧
      ListRel (fun y c => denoteLoaded s'.store y = some c) ls.toList lsC ∧
      lsC.map (·.name) = orderC.toList ∧ ∀ lC ∈ lsC, ∃ dC,
        (ConLeche.Frontend.Olean.readView sp lC.name .private : ModelIO _) F (.ok (.ok dC)) ∧
        lC.constants.map (·.toCEntryF) = dC.constants := by
  unfold ConRon.Arena.Frontend.Olean.loadClosure at h
  obtain ⟨order, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, orderC, hC, hR⟩ := closureOrder_run hctx hr h1
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h
  obtain ⟨ys, s₂, h2, h⟩ := AM.bind_ok h
  obtain ⟨hv, hs⟩ := AM.pure_ok h
  cases hv
  subst hs
  obtain ⟨hst2, lsC, hL, hmap, hall⟩ := loadAll_run _ (hctx.step hst1) (hp.ext hst1.ext) hR h2
  exact ⟨hst1.trans hst2, orderC, lsC, hC, by simpa using hL, hmap, hall⟩

end ConRon.Bridge.Frontend.Olean
