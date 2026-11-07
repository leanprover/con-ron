/-
# `ConRon.Bridge.Frontend.Olean.Closure` — the import closure, loaded

The walk `closureGo` is upstream's, over handles: the sets of handles denote upstream's sets of
names (`SetRel`), so each `contains` answers alike, `denoteN` being injective on a well formed
store, and the twin's run is what upstream's gives at `ModelIO` (`ModelIO.Gives`), so a value
upstream's can give (`ModelIO.CanGive`), which `closureOrder_ok` speaks of.

A module's load (`loadAt`) is upstream's `loadAt_spec` over handles: its constants are the
specification's lazy entries (`LazyOf`), a theorem's value the reference upstream's is.  `uses`
is read by upstream's `partial` byte walk (`usesOf`), so no equation relates it to anything; nothing
proved of the merge or the emission reads what it holds, and the theorem here says only that its
handles denote (`usesRead_den`).  Nothing of the records reads the frontier either, so
`LoadedRel` leaves it out.
-/
module

public import ConRon.Bridge.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.Olean.Lazy
import Std.Data.HashSet.Lemmas
import ConRon.Bridge.SpecsL
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins OleanFs closureGo CEntry DS)
open ConLeche.Frontend.Olean (ImportF ImportRec SearchPath CEntryF CKindF mkN Region ModSkel LazyOf
  lazyEntry lazyRoots usesNames usesNat usesStr nameP exprP moduleSkel constSkel nameAt levelAt levelsAt
  exprAt IsKind kName kLevel kLevels kExpr)

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
is what upstream's gives**, the same step for step. -/
theorem closureGo_run {pk : OleanPins} {F : FS} {sp : SearchPath} :
    ∀ (fuel : Nat) (stack : List (NIdx × Bool)) (seen done : Std.HashSet NIdx) (out outF : Array NIdx)
      (stackC : List (ConLeche.Name × Bool)) (seenC doneC : Std.HashSet ConLeche.Name)
      (outC : Array ConLeche.Name) {s s' : AState}, Ctx pk s →
      ListRel (StackR s.store) stack stackC → SetRel s.store seen seenC → SetRel s.store done doneC →
      ListRel (NR s.store) out.toList outC.toList →
      closureGo (modelFs F) pk sp fuel stack seen done out s = .ok (outF, s') →
      ParseStep s s' ∧ ∃ outFC : Array ConLeche.Name,
        ModelIO.Gives (ConLeche.Frontend.Olean.closureGo sp fuel stackC seenC doneC outC : ModelIO _)
          F (.ok outFC) ∧ ListRel (NR s'.store) outF.toList outFC.toList := by
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
      exact ⟨ParseStep.refl hctx.ok, outC, by
        rw [ConLeche.Frontend.Olean.closureGo]; exact ModelIO.gives_pure _ _, hou⟩
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
      exact ⟨ParseStep.refl hctx.ok, outC, by
        rw [ConLeche.Frontend.Olean.closureGo]; exact ModelIO.gives_pure _ _, hou⟩
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
            refine hz.bind ?_
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

/-! ## A loaded constant, a loaded module -/

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:167-168 CEntry — **a stored constant read
back**, with the twin's own `uses`: an array of its own, read back as the slice of all of it
(upstream's constants slice one array per module). -/
@[expose] def denoteCEntry (st : EStore) (x : CEntry) : Option ConLeche.Frontend.Olean.CEntry := do
  let e ← denoteEntry st x.c
  let u ← x.uses.toList.mapM (denoteN st.ns)
  pure { toCEntryF := e, uses := u.toArray.toSubarray }

/-- The slice of all of a list's array holds the list. -/
@[simp] theorem toArray_toSubarray_toList {α : Type} (u : List α) :
    u.toArray.toSubarray.toArray.toList = u := by
  simp [Subarray.toList_toArray, Subarray.toList_eq]

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:177-180 Loaded — **a loaded module read back**:
its name and its constants.  The frontier is not related: nothing of the records reads it. -/
structure LoadedRel (st : EStore) (l : ConRon.Arena.Frontend.Olean.Loaded)
    (lC : ConLeche.Frontend.Olean.Loaded) : Prop where
  name : denoteN st.ns l.name = some lC.name
  constants : l.constants.toList.mapM (denoteCEntry st) = some lC.constants.toList

theorem denoteCEntry_ext {st st' : EStore} (hx : Ext st st') {c : CEntry}
    {z : ConLeche.Frontend.Olean.CEntry} (h : denoteCEntry st c = some z) :
    denoteCEntry st' c = some z := by
  unfold denoteCEntry at h ⊢
  obtain ⟨e, h1, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  obtain ⟨u, h2, h⟩ := ConLeche.Frontend.Olean.bind_some_left h
  simp only [denoteEntry_ext hx h1, list_mono (fun _ _ hy => denoteN_ext hy hx) _ h2]
  exact h

theorem LoadedRel.ext {st st' : EStore} (hx : Ext st st') {l : ConRon.Arena.Frontend.Olean.Loaded}
    {lC : ConLeche.Frontend.Olean.Loaded} (h : LoadedRel st l lC) : LoadedRel st' l lC :=
  ⟨denoteN_ext h.name hx, list_mono (fun _ _ hy => denoteCEntry_ext hx hy) _ h.constants⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Lazy.lean:191 loadAt_spec — **what a module's load
is, by the specification**: the constants of the private view of its files, up to the theorems'
values, which are references (`LazyOf`). -/
@[expose] def LoadSpec (f : ConLeche.Frontend.Olean.ModFiles) (i : Nat)
    (lC : ConLeche.Frontend.Olean.Loaded) : Prop :=
  ∃ r a sk skels, f.viewRegion .private = some (r, a) ∧ moduleSkel r a = some sk ∧
    sk.consts.mapM (constSkel r) = some skels ∧ LazyOf r i skels lC.constants.toList

/-! ## What a constant mentions -/

theorem usesNames_go_sub : ∀ (out : List UInt64) (acc : Array UInt64),
    ∀ v ∈ acc, v ∈ out.foldl (fun acc v =>
      if v == usesNat || v == usesStr then acc else acc.push v) acc
  | [], acc, v, hv => hv
  | w :: out, acc, v, hv => by
    simp only [List.foldl_cons]
    apply usesNames_go_sub out
    split
    · exact hv
    · exact Array.mem_push_of_mem _ hv

theorem usesNames_go_mem : ∀ (out : List UInt64) (acc : Array UInt64),
    ∀ v ∈ out, v ≠ usesNat → v ≠ usesStr → v ∈ out.foldl (fun acc v =>
      if v == usesNat || v == usesStr then acc else acc.push v) acc
  | [], acc, v, hv, _, _ => by simp at hv
  | w :: out, acc, v, hv, h1, h2 => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · apply usesNames_go_sub
      have : (v == usesNat || v == usesStr) = false := by
        simp [h1, h2]
      rw [this]
      exact Array.mem_push_self
    · exact usesNames_go_mem out _ v hv h1 h2

theorem usesNames_outer_sub : ∀ (outs : List (Array UInt64)) (acc : Array UInt64),
    ∀ v ∈ acc, v ∈ outs.foldl (fun acc out => out.foldl (fun acc v =>
      if v == usesNat || v == usesStr then acc else acc.push v) acc) acc
  | [], acc, v, hv => hv
  | o :: outs, acc, v, hv => by
    simp only [List.foldl_cons]
    apply usesNames_outer_sub outs
    rw [← Array.foldl_toList]
    exact usesNames_go_sub _ _ v hv

theorem usesNames_outer_mem : ∀ (outs : List (Array UInt64)) (acc : Array UInt64),
    ∀ o ∈ outs, ∀ v ∈ o, v ≠ usesNat → v ≠ usesStr → v ∈ outs.foldl (fun acc out => out.foldl
      (fun acc v => if v == usesNat || v == usesStr then acc else acc.push v) acc) acc
  | [], acc, o, ho, _, _, _, _ => by simp at ho
  | o' :: outs, acc, o, ho, v, hv, h1, h2 => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ho with rfl | ho
    · apply usesNames_outer_sub
      rw [← Array.foldl_toList]
      exact usesNames_go_mem _ _ v (by simpa using hv) h1 h2
    · exact usesNames_outer_mem outs _ o ho v hv h1 h2

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:128-132 usesNames — every name the walk wrote
is a root of the load. -/
theorem mem_usesNames {outs : Array (Array UInt64)} {k : Nat} {v : UInt64}
    (hv : v ∈ outs.getD k #[]) (h1 : v ≠ usesNat) (h2 : v ≠ usesStr) : v ∈ usesNames outs := by
  unfold usesNames
  rw [← Array.foldl_toList, Array.mem_toList_iff]
  by_cases hk : k < outs.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some] at hv
    exact usesNames_outer_mem _ _ _ (by simp) v hv h1 h2
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none] at hv
    simp at hv

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:139-150 usesRead — **the names it keeps
denote**: the reader's pins, and the names of the memo. -/
theorem usesRead_den {st : EStore} {pk : OleanPins} (hp : PinsRel st pk)
    {nm : UInt64 → Option NIdx} (out : Array UInt64)
    (hn : ∀ v ∈ out, v ≠ usesNat → v ≠ usesStr → ∀ y, nm v = some y → (denoteN st.ns y).isSome) :
    ∀ n ∈ ConRon.Arena.Frontend.Olean.usesRead pk nm out, (denoteN st.ns n).isSome := by
  have hadd : ∀ {x : Std.HashSet NIdx × Array NIdx} {n : NIdx},
      (∀ k ∈ x.2, (denoteN st.ns k).isSome) → (denoteN st.ns n).isSome →
      ∀ k ∈ (ConRon.Arena.Frontend.Olean.addUse x n).2, (denoteN st.ns k).isSome := by
    intro x n ho hn k hk
    simp only [ConRon.Arena.Frontend.Olean.addUse] at hk
    split at hk
    · exact ho k hk
    · simp only [Array.mem_push] at hk
      rcases hk with hk | rfl
      · exact ho k hk
      · exact hn
  have hgo : ∀ (l : List UInt64) (x : Std.HashSet NIdx × Array NIdx),
      (∀ v ∈ l, v ≠ usesNat → v ≠ usesStr → ∀ y, nm v = some y → (denoteN st.ns y).isSome) →
      (∀ k ∈ x.2, (denoteN st.ns k).isSome) →
      ∀ k ∈ (l.foldl (fun x v =>
        if v == usesNat then ConRon.Arena.Frontend.Olean.addUse x pk.nNat
        else if v == usesStr then ConRon.Arena.Frontend.Olean.addUse
          (ConRon.Arena.Frontend.Olean.addUse x pk.nCharOfNat) pk.nStringOfList
        else match nm v with
          | some n => ConRon.Arena.Frontend.Olean.addUse x n
          | none => x) x).2, (denoteN st.ns k).isSome := by
    intro l
    induction l with
    | nil => intro x _ hx; exact hx
    | cons v l ih =>
      intro x hl hx
      simp only [List.foldl_cons]
      apply ih _ (fun w hw => hl w (List.mem_cons_of_mem _ hw))
      by_cases h1 : v = usesNat
      · simp only [h1, BEq.rfl, ↓reduceIte]
        exact hadd hx (by simp [hp.nNat])
      · simp only [beq_iff_eq, h1, ↓reduceIte]
        by_cases h2 : v = usesStr
        · simp only [h2, ↓reduceIte]
          exact hadd (hadd hx (by simp [hp.nCharOfNat])) (by simp [hp.nStringOfList])
        · simp only [h2, ↓reduceIte]
          cases hv : nm v with
          | none => exact hx
          | some y => exact hadd hx (hl v (by simp) h1 h2 y hv)
  unfold ConRon.Arena.Frontend.Olean.usesRead
  rw [← Array.foldl_toList]
  exact hgo out.toList _ (fun v hv => hn v (by simpa using hv)) (by simp)

theorem list_some_of {α β : Type} {f : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    obtain ⟨ys, hys⟩ := list_some_of l (fun w hw => h w (List.mem_cons_of_mem _ hw))
    exact ⟨y :: ys, by simp only [List.mapM_cons, hy, hys]; rfl⟩

/-! ## The frontier -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:50 Table.Good — **a table whose every
entry satisfies `P`**, its two arrays of one length (upstream's `Table.Sized`). -/
structure TableRel {α : Type} (P : Nat → α → Prop) (t : ConLeche.Frontend.Olean.Table α) : Prop where
  sized : t.keys.size = t.vals.size
  good : ∀ (i c : Nat) (v : α), t.keys[i]? = some c → t.vals[i]? = some v → P c v

theorem TableRel.empty {α : Type} (P : Nat → α → Prop) : TableRel P ({} : ConLeche.Frontend.Olean.Table α) :=
  ⟨rfl, fun i c v h => by simp at h⟩

theorem TableRel.mono {α : Type} {P Q : Nat → α → Prop} (hm : ∀ c v, P c v → Q c v)
    {t : ConLeche.Frontend.Olean.Table α} (h : TableRel P t) : TableRel Q t :=
  ⟨h.sized, fun i c v h1 h2 => hm c v (h.good i c v h1 h2)⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:53 Table.search_good -/
theorem TableRel.search {α : Type} {P : Nat → α → Prop} {t : ConLeche.Frontend.Olean.Table α}
    (ht : TableRel P t) {c : Nat} :
    ∀ (d lo hi : Nat), hi - lo = d → ∀ {v : α}, t.search c lo hi = some v → P c v := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro lo hi hd v h
    rw [ConLeche.Frontend.Olean.Table.search] at h
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i k hk
        split at h
        · rename_i hkc
          subst hkc
          exact ht.good _ _ _ hk h
        · split at h
          · exact ih _ (by omega) _ _ rfl h
          · exact ih _ (by omega) _ _ rfl h
    · cases h

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:75 Table.get_good -/
theorem TableRel.get {α : Type} {P : Nat → α → Prop} {t : ConLeche.Frontend.Olean.Table α}
    (ht : TableRel P t) {c : Nat} {v : α} (h : t.get c = some v) : P c v :=
  ht.search _ _ _ rfl h

/-- con-leche: ConLeche/Verify/Frontend/Olean/Lazy.lean:38 Table.add_good -/
theorem TableRel.add {α : Type} {P : Nat → α → Prop} {t : ConLeche.Frontend.Olean.Table α}
    (ht : TableRel P t) {c : Nat} {v : α} (hp : P c v) : TableRel P (t.add c v) := by
  obtain ⟨keys, vals⟩ := t
  obtain ⟨hs, hg⟩ := ht
  refine ⟨by simp [ConLeche.Frontend.Olean.Table.add, hs], fun i c' v' h1 h2 => ?_⟩
  simp only [ConLeche.Frontend.Olean.Table.add, Array.getElem?_push] at h1 h2
  by_cases hi : i = keys.size
  · simp only [hi, ite_true] at h1
    simp only [hi.trans hs, ite_true] at h2
    cases h1; cases h2; exact hp
  · simp only [hi, ite_false] at h1
    simp only [show ¬ i = vals.size from fun e => hi (e.trans hs.symm), ite_false] at h2
    exact hg i c' v' h1 h2

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:81 Frontier.Good — **a frontier of
handles that denote the specification's values** at their locations. -/
structure FrontierGood (st : EStore) (r : Region) (b : ConRon.Arena.Frontend.Olean.Frontier) : Prop where
  names : TableRel (fun c h => ∃ n, nameAt r c = some n ∧ denoteN st.ns h = some n) b.names
  levels : TableRel (fun c h => ∃ u, levelAt r c = some u ∧ denoteL st.ls h = some u) b.levels
  lists : TableRel (fun c h => ∃ us, levelsAt r c = some us ∧ denoteLs st.lss h = some us) b.lists
  exprs : TableRel (fun c h => ∃ e, exprAt r c = some e ∧ denoteE st h = some e) b.exprs

theorem FrontierGood.empty (st : EStore) (r : Region) : FrontierGood st r {} :=
  ⟨TableRel.empty _, TableRel.empty _, TableRel.empty _, TableRel.empty _⟩

theorem FrontierGood.ext {st st' : EStore} {r : Region} {b : ConRon.Arena.Frontend.Olean.Frontier}
    (h : FrontierGood st r b) (hx : Ext st st') : FrontierGood st' r b :=
  ⟨h.names.mono fun _ _ ⟨n, a, b⟩ => ⟨n, a, denoteN_ext b hx⟩,
   h.levels.mono fun _ _ ⟨n, a, b⟩ => ⟨n, a, denoteL_ext b hx⟩,
   h.lists.mono fun _ _ ⟨n, a, b⟩ => ⟨n, a, denoteLs_ext b hx⟩,
   h.exprs.mono fun _ _ ⟨n, a, b⟩ => ⟨n, a, denote_ext b hx⟩⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Lazy.lean:109 frontierOf_good — **the frontier takes
only values the passes built**: a slot it adds is one the marks hold, so `Built` answers. -/
theorem frontierOf_good {st : EStore} {r : Region} {m fr : ByteArray} {memo : DS} {n : Nat}
    (hb : Built st r m memo n) :
    ∀ (d p : Nat), n - p = d → ∀ (b : ConRon.Arena.Frontend.Olean.Frontier), FrontierGood st r b →
      FrontierGood st r (ConRon.Arena.Frontend.Olean.frontierOf m fr memo n p b) := by
  have hk1 : IsKind kName := Or.inl rfl
  have hk2 : IsKind kLevel := Or.inr (Or.inl rfl)
  have hk3 : IsKind kExpr := Or.inr (Or.inr (Or.inl rfl))
  have hk4 : IsKind kLevels := Or.inr (Or.inr (Or.inr rfl))
  intro d
  induction d with
  | zero =>
    intro p hd b hgood
    rw [ConRon.Arena.Frontend.Olean.frontierOf, ite_eq_right (by omega)]
    exact hgood
  | succ d ih =>
    intro p hd b hgood
    have hp : p < n := by omega
    rw [ConRon.Arena.Frontend.Olean.frontierOf, ite_eq_left hp]
    apply ih (p + 1) (by omega)
    unfold ConRon.Arena.Frontend.Olean.frontierStep
    split
    · exact hgood
    obtain ⟨names, levels, lists, exprs⟩ := b
    obtain ⟨g1, g2, g3, g4⟩ := hgood
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only
      split
      · rename_i hm
        simp only [Bool.and_eq_true] at hm
        exact g1.add ((hb p hp kName hk1 hm.2).1 rfl)
      · exact g1
    · dsimp only
      split
      · rename_i hm
        simp only [Bool.and_eq_true] at hm
        exact g2.add ((hb p hp kLevel hk2 hm.2).2.1 rfl)
      · exact g2
    · dsimp only
      split
      · rename_i hm
        simp only [Bool.and_eq_true] at hm
        exact g3.add ((hb p hp kLevels hk4 hm.2).2.2.1 rfl)
      · exact g3
    · dsimp only
      split
      · rename_i hm
        simp only [Bool.and_eq_true] at hm
        exact g4.add ((hb p hp kExpr hk3 hm.2).2.2.2 rfl)
      · exact g4

/-- con-leche: ConLeche/Verify/Frontend/Olean/Lazy.lean:191 loadAt_spec — the frontier of a load
is good on the region of the files it was loaded from. -/
@[expose] def FrontGoodAt (st : EStore) (f : ConLeche.Frontend.Olean.ModFiles)
    (b : ConRon.Arena.Frontend.Olean.Frontier) : Prop :=
  ∃ r a, f.viewRegion .private = some (r, a) ∧ FrontierGood st r b

theorem FrontGoodAt.ext {st st' : EStore} {f : ConLeche.Frontend.Olean.ModFiles}
    {b : ConRon.Arena.Frontend.Olean.Frontier} (h : FrontGoodAt st f b) (hx : Ext st st') :
    FrontGoodAt st' f b :=
  let ⟨r, a, h1, h2⟩ := h
  ⟨r, a, h1, h2.ext hx⟩

/-! ## A module's load -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM — a constant read off the
memo, every name and expression: the specification's, read back. -/
theorem entryMap_run {pk : OleanPins} {r : Region} {st : DS} {c : CEntryF UInt64 UInt64}
    {e : CEntryF NIdx EIdx} {s s' : AState}
    (hN : ∀ x ∈ c.names, ∀ y, st.nameOf pk r x = some y →
      ∃ z, nameP r x = some z ∧ denoteN s.store.ns y = some z)
    (hE : ∀ x ∈ c.exprs, ∀ y, st.exprOf r x = some y →
      ∃ z, exprP r x = some z ∧ denoteE s.store y = some z)
    (h : ConRon.Arena.Frontend.Olean.entryMap (DS.read pk r st) c s = .ok (some e, s')) :
    s' = s ∧ ∃ z, c.mapM (nameP r) (exprP r) = some z ∧ denoteEntry s.store e = some z := by
  have hpr := PR.entryMap (fn := fun v => OptionT.mk ((DS.read pk r st).rdName v))
    (fe := fun v => OptionT.mk ((DS.read pk r st).rdExpr v))
    (gn := st.nameOf pk r) (ge := st.exprOf r) (fun _ _ => rfl) (fun _ _ => rfl) c s
  have h2 : ConRon.Arena.Frontend.Olean.entryMap (DS.read pk r st) c s =
      .ok (c.mapM (st.nameOf pk r) (st.exprOf r), s) := hpr
  rw [h2] at h
  injection h with h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hm, rfl⟩ := h
  obtain ⟨z, hz, hdz⟩ := entry_sim (fnC := nameP r) (feC := exprP r) (dn := denoteN s.store.ns)
    (de := denoteE s.store) c hm hN hE
  exact ⟨rfl, z, hz, hdz⟩

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:194-206 lazyEntry — **a constant read off the
memo is the specification's lazy entry**: a theorem's value is the reference upstream's is. -/
theorem lazyEntry_run {pk : OleanPins} {r : Region} {st : DS} {i : Nat}
    {sk : CEntryF UInt64 UInt64} {e : CEntryF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s)
    (hN : ∀ x ∈ sk.names, ∀ y, st.nameOf pk r x = some y →
      ∃ z, nameP r x = some z ∧ denoteN s.store.ns y = some z)
    (hE : ∀ x ∈ lazyRoots sk, ∀ y, st.exprOf r x = some y →
      ∃ z, exprP r x = some z ∧ denoteE s.store y = some z)
    (h : ConRon.Arena.Frontend.Olean.lazyEntry pk r st i sk s = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ eC, denoteEntry s'.store e = some eC ∧
      lazyEntry (nameP r) (exprP r) r i sk = some eC := by
  rcases sk with ⟨name, lps, type, kind⟩
  cases kind with
  | thm v all =>
    simp only [ConRon.Arena.Frontend.Olean.lazyEntry] at h
    split at h
    rotate_left
    · cases (AM.pure_ok h).1
    rename_i hi
    obtain ⟨u, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨-, rfl⟩ := AM.pure_ok h1
    split at h
    rotate_left
    · cases (AM.pure_ok h).1
    rename_i g hg
    split at h
    rotate_left
    · cases (AM.pure_ok h).1
    obtain ⟨u, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨-, rfl⟩ := AM.pure_ok h1
    split at h
    rotate_left
    · cases (AM.pure_ok h).1
    rename_i n hn
    split at h
    rotate_left
    · cases (AM.pure_ok h).1
    rename_i lps' hl
    split at h
    rotate_left
    · cases (AM.pure_ok h).1
    rename_i t ht
    split at h
    rotate_left
    · cases (AM.pure_ok h).1
    rename_i all' ha
    simp only [pure_bind] at h
    obtain ⟨vh, s₂, hv, h⟩ := AM.bind_ok h
    obtain ⟨he, rfl⟩ := AM.pure_ok h
    cases he
    unfold ConRon.Arena.Frontend.Olean.valueRef at hv
    obtain ⟨hst, -, hden⟩ := internE_istep hctx.ok hctx.off viewOK_bvar hv
    have hmemN : ∀ x ∈ lps, x ∈ (CEntryF.mk name lps type (.thm v all)).names := fun x hx => by
      simp [ConLeche.Frontend.Olean.CEntryF.names, hx]
    have hmemA : ∀ x ∈ all, x ∈ (CEntryF.mk name lps type (.thm v all)).names := fun x hx => by
      simp [ConLeche.Frontend.Olean.CEntryF.names, hx]
    obtain ⟨zn, hzn, hdn⟩ := hN name (by simp [ConLeche.Frontend.Olean.CEntryF.names]) n hn
    obtain ⟨zl, hzl, hdl⟩ := list_sim lps hl
      (fun x hx y hy => hN x (hmemN x hx) y hy)
    obtain ⟨zt, hzt, hdt⟩ := hE type (by simp [lazyRoots]) t ht
    obtain ⟨za, hza, hda⟩ := list_sim all ha
      (fun x hx y hy => hN x (hmemA x hx) y hy)
    refine ⟨hst.toParse hctx.off, ⟨zn, zl, zt, .thm (.bvar (g * ConLeche.Frontend.Olean.refBase + i)) za⟩,
      ?_, ?_⟩
    · simp only [denoteEntry, ConLeche.Frontend.Olean.CEntryF.mapM, ConLeche.Frontend.Olean.CKindF.mapM,
        denoteN_ext hdn hst.ext, list_mono (fun _ _ hy => denoteN_ext hy hst.ext) _ hdl,
        denote_ext hdt hst.ext, hden, denoteEView,
        list_mono (fun _ _ hy => denoteN_ext hy hst.ext) _ hda]
      rfl
    · simp only [lazyEntry, hi, hg, hzn, hzl, hzt, hza]
      rfl
  | _ =>
    simp only [ConRon.Arena.Frontend.Olean.lazyEntry] at h
    obtain ⟨rfl, z, hz, hdz⟩ := entryMap_run hN (fun x hx => hE x (by simpa [lazyRoots] using hx)) h
    exact ⟨ParseStep.refl hctx.ok, z, hdz, by simpa only [lazyEntry] using hz⟩

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:208-218 lazyEntries -/
theorem lazyEntries_run {pk : OleanPins} {r : Region} {st : DS} {i : Nat}
    {outs : Array (Array UInt64)} :
    ∀ (ss : List (CEntryF UInt64 UInt64)) (k : Nat) {cs : List CEntry} {s s' : AState},
      Ctx pk s → PinsRel s.store pk →
      (∀ sk ∈ ss, ∀ x ∈ sk.names, ∀ y, st.nameOf pk r x = some y →
        ∃ z, nameP r x = some z ∧ denoteN s.store.ns y = some z) →
      (∀ sk ∈ ss, ∀ x ∈ lazyRoots sk, ∀ y, st.exprOf r x = some y →
        ∃ z, exprP r x = some z ∧ denoteE s.store y = some z) →
      (∀ k, ∀ n ∈ ConRon.Arena.Frontend.Olean.usesRead pk (st.nameOf pk r) (outs.getD k #[]),
        (denoteN s.store.ns n).isSome) →
      ConRon.Arena.Frontend.Olean.lazyEntries pk r st i outs k ss s = .ok (some cs, s') →
      ParseStep s s' ∧ ∃ csC, cs.mapM (denoteCEntry s'.store) = some csC ∧ LazyOf r i ss csC
  | [], k, cs, s, s', hctx, _, _, _, _, h => by
    rw [ConRon.Arena.Frontend.Olean.lazyEntries] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hctx.ok, [], rfl, ⟨by simp, by simp⟩⟩
  | sk :: ss, k, cs, s, s', hctx, hp, hN, hE, hU, h => by
    rw [ConRon.Arena.Frontend.Olean.lazyEntries] at h
    obtain ⟨o, s₁, h1, h⟩ := AM.bind_ok h
    cases o with
    | none => cases (AM.pure_ok h).1
    | some e =>
    obtain ⟨o', s₂, h2, h⟩ := AM.bind_ok h
    cases o' with
    | none => cases (AM.pure_ok h).1
    | some es =>
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    obtain ⟨hst1, eC, hde, hle⟩ := lazyEntry_run hctx (hN sk (by simp)) (hE sk (by simp)) h1
    obtain ⟨hst2, esC, hes, hlazy⟩ := lazyEntries_run ss (k + 1) (hctx.step hst1) (hp.ext hst1.ext)
      (fun sk' hsk x hx y hy => by
        obtain ⟨z, hz, hd⟩ := hN sk' (List.mem_cons_of_mem _ hsk) x hx y hy
        exact ⟨z, hz, denoteN_ext hd hst1.ext⟩)
      (fun sk' hsk x hx y hy => by
        obtain ⟨z, hz, hd⟩ := hE sk' (List.mem_cons_of_mem _ hsk) x hx y hy
        exact ⟨z, hz, denote_ext hd hst1.ext⟩)
      (fun k' n hn => by
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hU k' n hn)
        rw [denoteN_ext hz hst1.ext]
        rfl) h2
    have hx := hst1.ext.trans hst2.ext
    obtain ⟨us, hus⟩ := list_some_of (f := denoteN s'.store.ns)
      (ConRon.Arena.Frontend.Olean.usesRead pk (st.nameOf pk r) (outs.getD k #[])).toList
      (fun n hn => by
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hU k n (by simpa using hn))
        rw [denoteN_ext hz hx]
        rfl)
    refine ⟨hst1.trans hst2, { toCEntryF := eC, uses := us.toArray.toSubarray } :: esC, ?_, ?_⟩
    · simp only [List.mapM_cons, hes, denoteCEntry, denoteEntry_ext hst2.ext hde, hus]
      rfl
    · refine ⟨fun s0 hs0 => ?_, fun e0 he0 => ?_⟩
      · rcases List.mem_cons.mp hs0 with rfl | hs0
        · exact ⟨_, List.mem_cons_self, hle⟩
        · obtain ⟨x, hx, h⟩ := hlazy.of_skel s0 hs0
          exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
      · rcases List.mem_cons.mp he0 with rfl | he0
        · exact ⟨sk, List.mem_cons_self, hle⟩
        · obtain ⟨x, hx, h⟩ := hlazy.to_skel e0 he0
          exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:279-297 loadAt — the imports' check moves the
state as a read does. -/
theorem loadImports_run {pk : OleanPins} {r : Region} {st : DS} {sk : ModSkel}
    {f : ConLeche.Frontend.Olean.ModFiles} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.loadImports pk r st sk f s = .ok (true, s')) :
    ParseStep s s' := by
  generalize hF : ConRon.Arena.Frontend.Olean.loadImports pk r st sk f = fn at h
  unfold ConRon.Arena.Frontend.Olean.loadImports at hF
  split at hF
  · subst hF
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none => cases (AM.pure_ok h2).1
    | some pre =>
      obtain ⟨-, hs⟩ := AM.pure_ok h2
      subst hs
      exact (importsPre_run hctx h1).1
  · subst hF
    cases (AM.pure_ok h).1

/-- con-leche: ConLeche/Verify/Frontend/Olean/Lazy.lean:191 loadAt_spec — **the twin's load of a
module's private view is the specification's, up to its theorems' values.** -/
theorem loadAt_run {pk : OleanPins} {i : Nat} {m : NIdx} {mn : ConLeche.Name}
    {f : ConLeche.Frontend.Olean.ModFiles} {l : ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState}
    (hctx : Ctx pk s) (hp : PinsRel s.store pk) (hm : denoteN s.store.ns m = some mn)
    (h : ConRon.Arena.Frontend.Olean.loadAt pk i m f s = .ok (some l, s')) :
    ParseStep s s' ∧ FrontGoodAt s'.store f l.frontier ∧
      ∃ lC, LoadedRel s'.store l lC ∧ lC.name = mn ∧ LoadSpec f i lC := by
  generalize hF : ConRon.Arena.Frontend.Olean.loadAt pk i m f = fn at h
  unfold ConRon.Arena.Frontend.Olean.loadAt at hF
  split at hF
  rotate_left
  · subst hF
    cases (AM.pure_ok h).1
  rename_i r a hvr
  subst hF
  obtain ⟨b, s₁, h1, h⟩ := AM.bind_ok h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases (AM.pure_ok h).1
  | true =>
  obtain ⟨hst1, -⟩ := constNamesOk_run hctx h1
  simp only [↓reduceIte, pure_bind] at h
  cases hsk : moduleSkel r a with
  | none =>
    simp only [hsk] at h
    cases (AM.pure_ok h).1
  | some sk =>
  simp only [hsk] at h
  obtain ⟨o, s₂, h2, h⟩ := AM.bind_ok h
  cases o with
  | none => cases (AM.pure_ok h).1
  | some skels =>
  obtain ⟨hs2, hskels⟩ := constsSkel_run _ h2
  rw [hs2] at h
  cases hU : ConRon.Arena.Frontend.Olean.usesOf r (Array.replicate
      (ConLeche.Frontend.Olean.maxLoc r (ConRon.Arena.Frontend.Olean.loadRoots sk skels).snd
        (ConLeche.Frontend.Olean.maxLoc r (ConRon.Arena.Frontend.Olean.loadRoots sk skels).fst 0)
        / 8 + 1) 0) 1 skels (Array.mkEmpty skels.length) with
  | none =>
    simp only [hU] at h
    cases (AM.pure_ok h).1
  | some outs =>
  simp only [hU] at h
  obtain ⟨o, s₃, h3, h⟩ := AM.bind_ok h
  rcases o with _ | ⟨nm, ms, st⟩
  · cases (AM.pure_ok h).1
  obtain ⟨hst3, hN, hE, hbuilt⟩ := runMarked_run (hctx.step hst1) h3
  obtain ⟨b, s₄, h4, h⟩ := AM.bind_ok h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases (AM.pure_ok h).1
  | true =>
  have hst4 := loadImports_run (hctx.step (hst1.trans hst3)) h4
  simp only [↓reduceIte] at h
  obtain ⟨o, s₅, h5, h⟩ := AM.bind_ok h
  cases o with
  | none => cases (AM.pure_ok h).1
  | some cs =>
  obtain ⟨hv, hs⟩ := AM.pure_ok h
  cases hv
  subst hs
  have hst := (hst1.trans hst3).trans hst4
  obtain ⟨hst5, csC, hcs, hlazy⟩ := lazyEntries_run skels 0 (hctx.step hst) (hp.ext hst.ext)
    (fun sk' hsk' x hx y hy => by
      obtain ⟨z, hz, hd⟩ := hN x (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨sk', hsk', hx⟩))) y hy
      exact ⟨z, hz, denoteN_ext hd hst4.ext⟩)
    (fun sk' hsk' x hx y hy => by
      obtain ⟨z, hz, hd⟩ := hE x (List.mem_flatMap.mpr ⟨sk', hsk', hx⟩) y hy
      exact ⟨z, hz, denote_ext hd hst4.ext⟩)
    (fun k => usesRead_den (hp.ext hst.ext) (outs.getD k #[]) (fun v hv h1 h2 y hy => by
      obtain ⟨z, -, hd⟩ := hN v (List.mem_append_right _ (mem_usesNames hv h1 h2)) y hy
      rw [denoteN_ext hd hst4.ext]
      rfl)) h5
  refine ⟨hst.trans hst5, ⟨r, a, hvr, (frontierOf_good hbuilt _ 0 rfl _ (FrontierGood.empty _ r)).ext
      (hst4.ext.trans hst5.ext)⟩, { name := mn, constants := csC.toArray, frontier := {} },
    ⟨denoteN_ext hm (hst.trans hst5).ext, by simpa using hcs⟩, rfl,
    r, a, sk, skels, hvr, hsk, hskels, by simpa using hlazy⟩

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:62-74 loadModule -/
theorem loadModule_run {pk : OleanPins} {F : FS} {sp : SearchPath} {total : Nat} {m : NIdx}
    {mn : ConLeche.Name} {idx : Nat} {l : ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState}
    (hctx : Ctx pk s) (hp : PinsRel s.store pk) (hm : denoteN s.store.ns m = some mn)
    (h : ConRon.Arena.Frontend.Olean.loadModule (modelFs F) pk sp total m idx s = .ok (l, s')) :
    ParseStep s s' ∧ ∃ lC f, LoadedRel s'.store l lC ∧ lC.name = mn ∧
      ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp mn .private : ModelIO _) F (.ok f) ∧
      LoadSpec f idx lC ∧ FrontGoodAt s'.store f l.frontier := by
  unfold ConRon.Arena.Frontend.Olean.loadModule at h
  obtain ⟨mn', s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hs1, hd1⟩ := readName_run h1
  subst hs1
  have hmn : mn' = mn := Option.some.inj (hd1.symm.trans hm)
  subst hmn
  obtain ⟨f, s₂, h3, h4⟩ := AM.bind_ok h2
  cases hrf : ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp mn' .private with
  | error e =>
    simp only [hrf, ConRon.Arena.Frontend.Olean.liftE] at h3
    cases h3
  | ok f' =>
  simp only [hrf, ConRon.Arena.Frontend.Olean.liftE] at h3
  obtain ⟨hv, hs⟩ := AM.pure_ok h3
  cases hv
  rw [hs] at h4
  obtain ⟨l', s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨hv, hs⟩ := AM.pure_ok h6
  cases hv
  rw [← hs] at h5
  unfold ConRon.Arena.Frontend.Olean.loadView at h5
  obtain ⟨o, s₄, h7, h8⟩ := AM.bind_ok h5
  cases o with
  | none =>
    obtain ⟨e, s₅, -, h9⟩ := AM.bind_ok h8
    obtain ⟨e', s₆, -, h10⟩ := AM.bind_ok h9
    exact absurd (AM.fail_ok h10) (by simp)
  | some l'' =>
  obtain ⟨hv, hs⟩ := AM.pure_ok h8
  cases hv
  rw [← hs] at h7
  obtain ⟨hst, hfg, lC, hrel, hn, hspec⟩ := loadAt_run hctx hp hm h7
  exact ⟨hst, lC, f, hrel, hn, readFiles_sim hrf, hspec, hfg⟩

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
      ModelIO.Gives (ConLeche.Frontend.Olean.closureOrder sp rootsC : ModelIO _) F (.ok orderC) ∧
      ListRel (NR s'.store) order.toList orderC.toList :=
  closureGo_run _ _ _ _ _ _ _ _ _ _ hctx (rootsStack_rel hr) (SetRel.empty _) (SetRel.empty _) .nil h

/-- Two related lists, numbered alike. -/
theorem listRel_zipIdx {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListRel R l l' → ∀ (n : Nat),
      ListRel (fun a b => R a.1 b.1 ∧ a.2 = b.2) (l.zipIdx n) (l'.zipIdx n)
  | _, _, .nil, _ => .nil
  | _, _, .cons hab hr, n => .cons ⟨hab, rfl⟩ (listRel_zipIdx hr (n + 1))

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:76-79 ModRef — a loaded module's frontier is
good on the region of its files on the snapshot. -/
@[expose] def ModFront (sp : SearchPath) (F : FS) (st : EStore)
    (l : ConRon.Arena.Frontend.Olean.Loaded) (lC : ConLeche.Frontend.Olean.Loaded) : Prop :=
  ∃ f, ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp lC.name .private : ModelIO _) F (.ok f) ∧
    FrontGoodAt st f l.frontier

theorem ModFront.ext {sp : SearchPath} {F : FS} {st st' : EStore}
    {l : ConRon.Arena.Frontend.Olean.Loaded} {lC : ConLeche.Frontend.Olean.Loaded}
    (h : ModFront sp F st l lC) (hx : Ext st st') : ModFront sp F st' l lC :=
  let ⟨f, h1, h2⟩ := h
  ⟨f, h1, h2.ext hx⟩

/-- The modules of the order, loaded, each at its position. -/
theorem loadAll_go {pk : OleanPins} {F : FS} {sp : SearchPath} {total : Nat} :
    ∀ (l : List (NIdx × Nat)) {ns : List (ConLeche.Name × Nat)}
      {ys : List ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState}, Ctx pk s →
      PinsRel s.store pk → ListRel (fun a b => NR s.store a.1 b.1 ∧ a.2 = b.2) l ns →
      l.mapM (fun (p : NIdx × Nat) =>
        ConRon.Arena.Frontend.Olean.loadModule (modelFs F) pk sp total p.1 p.2) s = .ok (ys, s') →
      ParseStep s s' ∧ ∃ lsC, ListRel (LoadedRel s'.store) ys lsC ∧
        ListRel (ModFront sp F s'.store) ys lsC ∧ lsC.map (·.name) = ns.map (·.1) ∧ ∀ lC ∈ lsC, ∃ i f, (lC.name, i) ∈ ns ∧
          ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp lC.name .private : ModelIO _) F (.ok f) ∧
          LoadSpec f i lC
  | [], ns, ys, s, s', hctx, _, hl, h => by
    cases hl
    simp only [List.mapM_nil] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hctx.ok, [], .nil, .nil, rfl, by simp⟩
  | p :: l, ns, ys, s, s', hctx, hp, hl, h => by
    cases hl with
    | @cons _ q _ ns' hm hrest =>
      obtain ⟨hm, hi⟩ := hm
      simp only [List.mapM_cons] at h
      obtain ⟨y, s₁, h1, h⟩ := AM.bind_ok h
      obtain ⟨ys', s₂, h2, h⟩ := AM.bind_ok h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      cases hv
      subst hs
      obtain ⟨hst1, lC, f, hd, hn, hf, hspec, hfg⟩ := loadModule_run hctx hp hm h1
      obtain ⟨hst2, lsC, hR, hF, hmap, hall⟩ := loadAll_go l (hctx.step hst1) (hp.ext hst1.ext)
        (ListRel.mono' (fun a b hab => ⟨denoteN_ext hab.1 hst1.ext, hab.2⟩) hrest) h2
      refine ⟨hst1.trans hst2, lC :: lsC, .cons (hd.ext hst2.ext) hR,
        .cons ⟨f, by rw [hn]; exact hf, hfg.ext hst2.ext⟩ hF, ?_, ?_⟩
      · simp [hn, hmap]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · refine ⟨q.2, f, ?_, by rw [hn]; exact hf, by rw [← hi]; exact hspec⟩
          rw [hn]
          exact List.mem_cons_self
        · obtain ⟨i, f', h1, h2, h3⟩ := hall x hx
          exact ⟨i, f', List.mem_cons_of_mem _ h1, h2, h3⟩

/-- con-leche: ConLeche/Frontend/Olean/Closure.lean:76-88 loadClosure — **the closure,
loaded, on the snapshot**: the walk's order is upstream's, and each module is its files'
private view, loaded (`LoadSpec`) at its position in the order. -/
theorem loadClosure_run {pk : OleanPins} {F : FS} {sp : SearchPath} {roots : Array NIdx}
    {rootsC : Array ConLeche.Name} {ls : Array ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState}
    (hctx : Ctx pk s) (hp : PinsRel s.store pk)
    (hr : ListRel (NR s.store) roots.toList rootsC.toList)
    (h : ConRon.Arena.Frontend.Olean.loadClosure (modelFs F) pk sp roots s = .ok (ls, s')) :
    ParseStep s s' ∧ ∃ (orderC : Array ConLeche.Name) (lsC : List ConLeche.Frontend.Olean.Loaded),
      ModelIO.Gives (ConLeche.Frontend.Olean.closureOrder sp rootsC : ModelIO _) F (.ok orderC) ∧
      ListRel (LoadedRel s'.store) ls.toList lsC ∧ ListRel (ModFront sp F s'.store) ls.toList lsC ∧
      lsC.map (·.name) = orderC.toList ∧ ∀ lC ∈ lsC, ∃ i f, (lC.name, i) ∈ orderC.toList.zipIdx ∧
        ModelIO.Gives (ConLeche.Frontend.Olean.readFiles sp lC.name .private : ModelIO _) F (.ok f) ∧
        LoadSpec f i lC := by
  unfold ConRon.Arena.Frontend.Olean.loadClosure at h
  obtain ⟨order, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hst1, orderC, hC, hR⟩ := closureOrder_run hctx hr h1
  unfold ConRon.Arena.Frontend.Olean.loadAll at h
  simp only [StateT.map] at h
  cases h2 : (order.toList.zipIdx.mapM fun (p : NIdx × Nat) =>
      ConRon.Arena.Frontend.Olean.loadModule (modelFs F) pk sp order.size p.1 p.2) s₁ with
  | error e =>
    rw [h2] at h
    cases h
  | ok p =>
  obtain ⟨ys, s₂⟩ := p
  rw [h2] at h
  cases h
  obtain ⟨hst2, lsC, hL, hF, hmap, hall⟩ := loadAll_go _ (hctx.step hst1) (hp.ext hst1.ext)
    (listRel_zipIdx hR 0) h2
  refine ⟨hst1.trans hst2, orderC, lsC, hC, by simpa using hL, by simpa using hF, ?_, hall⟩
  rw [hmap]
  simp

end ConRon.Bridge.Frontend.Olean
