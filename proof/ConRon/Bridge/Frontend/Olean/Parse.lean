/-
# `ConRon.Bridge.Frontend.Olean.Parse` — one view of a module, by the specification

Where the twin's `parseView` has a value, `decodeModuleSpec` has its denotation
(`parseView_run`).  The name table's check, the imports off the start of a file, and the two
passes each meet the specification here; `Read.lean` holds the value's read off the memo.
-/
module

public import ConRon.Arena.Frontend.Olean.View
public import ConRon.Bridge.Frontend.Olean.Read
public import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.Frontend.Olean.Build
public import ConLeche.Verify.Frontend.Olean.Reads

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Sub DS PtrRead entryMap buildPass)
open ConLeche.Frontend.Olean (Region CEntryF CKindF ImportF ImportRec ModSkel nameAt nameP exprP
  bind_some_left constSkel moduleSkel importSkel decodeAt kName kExpr marked IsKind Closed OLeanLevel
  ModFiles Part)

/-! ## `OptionT` runs -/

theorem OT.bind_ok {α β : Type} {x : OptionT AM α} {f : α → OptionT AM β} {y : β} {s s' : AState}
    (h : (x >>= f) s = .ok (some y, s')) :
    ∃ a s₁, x s = .ok (some a, s₁) ∧ f a s₁ = .ok (some y, s') := by
  have h' : (Bind.bind (m := AM) (x : AM (Option α)) (fun (o : Option α) => match o with
      | some a => (f a : AM (Option β))
      | none => (pure none : AM (Option β)))) s = .ok (some y, s') := h
  obtain ⟨o, s₁, hx, hrest⟩ := AM.bind_ok h'
  cases o with
  | none =>
    have := (AM.pure_ok hrest).1
    cases this
  | some a => exact ⟨a, s₁, hx, hrest⟩

/-- A `List.mapM` in `OptionT AM`, each step answering upstream's `g` through a denotation
that survives the store's growth. -/
theorem optT_list_run {α β γ : Type} {pk : OleanPins} {den : EStore → β → Option γ}
    {f : α → OptionT AM β} {g : α → Option γ}
    (hden : ∀ {st st' : EStore} {y : β} {z : γ}, Ext st st' → den st y = some z → den st' y = some z)
    (hstep : ∀ a s s' y, Ctx pk s → f a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, g a = some z ∧ den s'.store y = some z) :
    ∀ (l : List α) {ys : List β} {s s' : AState}, Ctx pk s →
      l.mapM f s = .ok (some ys, s') →
      ParseStep s s' ∧ ∃ zs, l.mapM g = some zs ∧ ys.mapM (den s'.store) = some zs := by
  intro l
  induction l with
  | nil =>
    intro ys s s' hctx h
    simp only [List.mapM_nil] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hctx.ok, [], rfl, rfl⟩
  | cons x l ih =>
    intro ys s s' hctx h
    simp only [List.mapM_cons] at h
    obtain ⟨y, s₁, h1, h⟩ := OT.bind_ok h
    obtain ⟨ys', s₂, h2, h⟩ := OT.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    obtain ⟨hst1, z, hz, hd⟩ := hstep x s s₁ y hctx h1
    obtain ⟨hst2, zs, hzs, hds⟩ := ih (hctx.step hst1) h2
    refine ⟨hst1.trans hst2, z :: zs, ?_, ?_⟩
    · simp only [List.mapM_cons, hz, hzs]; rfl
    · simp only [List.mapM_cons, hden hst2.ext hd, hds]; rfl

/-! ## Both passes -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Engine.lean:135 runPasses_spec — **every root's
memo value denotes its specification's**.  Upstream's `RootsOK` is not needed: a pass of the
twin that answers read every marked object. -/
theorem runPasses_run {pk : OleanPins} {r : Region} {names exprs : List UInt64} {memo : DS}
    {s s' : AState} (hctx : Ctx pk s)
    (hrun : ConRon.Arena.Frontend.Olean.runPasses pk r names exprs s = .ok (some memo, s')) :
    ParseStep s s' ∧
      (∀ v ∈ names, ∀ y, memo.nameOf pk r v = some y →
        ∃ z, nameP r v = some z ∧ denoteN s'.store.ns y = some z) ∧
      (∀ v ∈ exprs, ∀ y, memo.exprOf r v = some y →
        ∃ z, exprP r v = some z ∧ denoteE s'.store y = some z) := by
  have hK1 : IsKind kName := Or.inl rfl
  have hK2 : IsKind kExpr := Or.inr (Or.inr (Or.inl rfl))
  generalize hF : ConRon.Arena.Frontend.Olean.runPasses pk r names exprs = f at hrun
  unfold ConRon.Arena.Frontend.Olean.runPasses at hF
  simp only [] at hF
  generalize hn : ConLeche.Frontend.Olean.maxLoc r exprs (ConLeche.Frontend.Olean.maxLoc r names 0) / 8 + 1 = n at hF
  have hbN : ∀ v ∈ names, r.locGo v r.segs.size / 8 < n := by
    intro v hv
    have := Nat.le_trans (ConLeche.Frontend.Olean.maxLoc_ge r names 0 v hv)
      (ConLeche.Frontend.Olean.maxLoc_ge_init r exprs _)
    have := Nat.div_le_div_right (c := 8) this
    omega
  have hbE : ∀ v ∈ exprs, r.locGo v r.segs.size / 8 < n := by
    intro v hv
    have := Nat.div_le_div_right (c := 8) (ConLeche.Frontend.Olean.maxLoc_ge r exprs
      (ConLeche.Frontend.Olean.maxLoc r names 0) v hv)
    omega
  split at hF
  · subst hF
    exact (none_not_some hrun).elim
  · rename_i st1 he1
    split at hF
    · subst hF
      exact (none_not_some hrun).elim
    · rename_i st2 he2
      obtain ⟨hs1, hf1, hsub1, hm1⟩ := rootsFold_some hK1 names _ st1
        (ConLeche.Frontend.Olean.size_zeros n) hbN he1
      obtain ⟨hs2, hf2, hsub2, hm2⟩ := rootsFold_some hK2 exprs st1 st2 hs1 hbE he2
      have hf2' : ConLeche.Frontend.Olean.failedM st2 = false := by
        rw [hf2, hf1, ConLeche.Frontend.Olean.failedM_zeros]
      have h3 := ConLeche.Frontend.Olean.markPass_spec (r := r) (A := False) (n := n) (by omega)
        n st2 (Nat.le_refl n) hs2 hf2' (fun _ _ _ _ a => a.elim)
        (fun s h1 h2 => absurd h2 (by omega))
      generalize e3 : ConLeche.Frontend.Olean.markPass r st2 n = st3 at h3 hF
      cases hf3 : ConLeche.Frontend.Olean.failedM st3 with
      | true =>
        simp only [hf3, ↓reduceIte] at hF
        subst hF
        exact (none_not_some hrun).elim
      | false =>
        simp only [hf3, Bool.false_eq_true, ↓reduceIte] at hF
        subst hF
        obtain ⟨hsub3, -, hc3⟩ := h3.2 hf3
        obtain ⟨hst, hb, -⟩ := buildPass_run hc3 _ 0 (Nat.le_refl _) hctx (sized_fresh n)
          (fun _ h => absurd h (by omega)) hrun
        have hb' := hb (by omega)
        refine ⟨hst, ?_, ?_⟩
        · intro v hv y hy
          by_cases e : v = 1
          · subst e
            simp only [ConRon.Arena.Frontend.Olean.DS.nameOf, BEq.rfl, ↓reduceIte,
              Option.some.injEq] at hy
            subst hy
            exact ⟨.anonymous, by simp [nameP], (hctx.step hst).nulls.anon⟩
          · obtain ⟨c, hl, hmc⟩ := hm1 v hv (fun h => e h.2)
            have hmc3 := hsub3 kName (c / 8) hK1 (hsub2 kName (c / 8) hK1 hmc)
            have hcn : c / 8 < n := by
              have := hbN v hv; rw [ConLeche.Frontend.Olean.loc_eq hl] at this; exact this
            obtain ⟨z, ha, hd⟩ := (hb' (c / 8) hcn kName hK1 hmc3).1 rfl
            rw [ConLeche.Frontend.Olean.eight_div (ConLeche.Frontend.Olean.loc_mod hl)] at ha
            simp only [ConRon.Arena.Frontend.Olean.DS.nameOf, e, beq_iff_eq, ↓reduceIte, hl,
              Option.some.injEq] at hy
            subst hy
            exact ⟨z, by simp only [nameP, e, beq_iff_eq, ↓reduceIte, hl, ha], hd⟩
        · intro v hv y hy
          obtain ⟨c, hl, hmc⟩ := hm2 v hv (fun h => by cases h.1)
          have hmc3 := hsub3 kExpr (c / 8) hK2 hmc
          have hcn : c / 8 < n := by
            have := hbE v hv; rw [ConLeche.Frontend.Olean.loc_eq hl] at this; exact this
          obtain ⟨z, ha, hd⟩ := (hb' (c / 8) hcn kExpr hK2 hmc3).2.2.2 rfl
          rw [ConLeche.Frontend.Olean.eight_div (ConLeche.Frontend.Olean.loc_mod hl)] at ha
          simp only [ConRon.Arena.Frontend.Olean.DS.exprOf, hl, Option.some.injEq] at hy
          subst hy
          exact ⟨z, by simp only [exprP, hl, ha], hd⟩

/-! ## The name table -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:448-457 constNamesGo — `seen` holds, by
handle, every name upstream's holds. -/
theorem constNamesGo_run {pk : OleanPins} {r : Region} :
    ∀ (ns cs : List Nat) (seen : Std.HashSet NIdx) (seenC : Std.HashSet ConLeche.Name)
      {s s' : AState}, Ctx pk s →
      (∀ n ∈ seenC, ∃ x ∈ seen, denoteN s.store.ns x = some n) →
      ConRon.Arena.Frontend.Olean.constNamesGo pk r ns cs seen s = .ok (true, s') →
      ParseStep s s' ∧ ConLeche.Frontend.Olean.constNamesGo r ns cs seenC = true
  | [], [], seen, seenC, s, s', hctx, _, h => by
    rw [ConRon.Arena.Frontend.Olean.constNamesGo] at h
    obtain ⟨-, hs⟩ := AM.pure_ok h
    subst hs
    exact ⟨ParseStep.refl hctx.ok, by simp [ConLeche.Frontend.Olean.constNamesGo]⟩
  | [], _ :: _, seen, seenC, s, s', hctx, _, h => by
    simp only [ConRon.Arena.Frontend.Olean.constNamesGo] at h
    cases (AM.pure_ok h).1
  | _ :: _, [], seen, seenC, s, s', hctx, _, h => by
    simp only [ConRon.Arena.Frontend.Olean.constNamesGo] at h
    cases (AM.pure_ok h).1
  | n :: ns, c :: cs, seen, seenC, s, s', hctx, hseen, h => by
    rw [ConRon.Arena.Frontend.Olean.constNamesGo] at h
    rw [ConLeche.Frontend.Olean.constNamesGo]
    cases hsk : constSkel r c with
    | none =>
      simp only [hsk] at h
      cases (AM.pure_ok h).1
    | some sk =>
      simp only [hsk] at h
      obtain ⟨o, s₁, hat, hrest⟩ := AM.bind_ok h
      cases o with
      | none => cases (AM.pure_ok hrest).1
      | some a =>
        obtain ⟨hst1, nC, hnC, hda⟩ := nameAt_run n hctx.ok hctx.off hctx.nulls hat
        have hctx1 := hctx.step hst1
        simp only [hnC]
        simp only [] at hrest
        have hkey : ∃ (b : Bool) (s₂ : AState), ParseStep s₁ s₂ ∧ (b = true →
            (r.loc sk.name == some n || nameP r sk.name == some nC) = true) ∧
            (if (!b) = true then (pure false : AM Bool)
              else if (seen.containsThenInsert a).fst = true then pure false
              else ConRon.Arena.Frontend.Olean.constNamesGo pk r ns cs
                (seen.containsThenInsert a).snd) s₂ = .ok (true, s') := by
          by_cases hso : (r.loc sk.name == some n) = true
          · simp only [hso, ↓reduceIte, pure_bind] at hrest
            exact ⟨true, s₁, ParseStep.refl hctx1.ok, fun _ => by simp [hso], hrest⟩
          · simp only [hso, Bool.false_eq_true, ↓reduceIte] at hrest
            obtain ⟨o', s₃, hp, hrest'⟩ := AM.bind_ok hrest
            cases o' with
            | none =>
              simp only [pure_bind] at hrest'
              simp only [Bool.not_false, ↓reduceIte] at hrest'
              cases (AM.pure_ok hrest').1
            | some q =>
              simp only [pure_bind] at hrest'
              obtain ⟨hst, z, hz, hdz⟩ := nameP_run hctx1.ok hctx1.off hctx1.nulls hp
              refine ⟨q == a, s₃, hst, fun hbt => ?_, hrest'⟩
              have hqa : q = a := by simpa using hbt
              subst hqa
              have hzn : z = nC := Option.some.inj (hdz.symm.trans (denoteN_ext hda hst.ext))
              subst hzn
              simp [hz]
        obtain ⟨b, s₂, hst2, hsm, hrest⟩ := hkey
        have hctx2 := hctx1.step hst2
        cases hbb : b with
        | false =>
          simp only [hbb, Bool.not_false, ↓reduceIte] at hrest
          cases (AM.pure_ok hrest).1
        | true =>
          simp only [hbb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrest
          have hcond := hsm hbb
          rw [hcond, Bool.true_and]
          simp only [Std.HashSet.containsThenInsert_fst, Std.HashSet.containsThenInsert_snd] at hrest ⊢
          cases hca : seen.contains a with
          | true =>
            simp only [hca, ↓reduceIte] at hrest
            cases (AM.pure_ok hrest).1
          | false =>
            simp only [hca, Bool.false_eq_true, ↓reduceIte] at hrest
            have hcn : seenC.contains nC = false := by
              cases hcn : seenC.contains nC with
              | false => rfl
              | true =>
                obtain ⟨x, hx, hdx⟩ := hseen nC (Std.HashSet.mem_iff_contains.mpr hcn)
                have hxa : x = a := denoteN_inj (nsWF_of_StateOK hctx1.ok)
                  (denoteN_ext hdx hst1.ext) hda
                subst hxa
                rw [Std.HashSet.mem_iff_contains, hca] at hx
                cases hx
            have hseen' : ∀ k ∈ seenC.insert nC, ∃ x ∈ seen.insert a, denoteN s₂.store.ns x = some k := by
              intro k hk
              rw [Std.HashSet.mem_insert] at hk
              rcases hk with hk | hk
              · have hk' : nC = k := by simpa using hk
                subst hk'
                exact ⟨a, by simp [Std.HashSet.mem_insert], denoteN_ext hda hst2.ext⟩
              · obtain ⟨x, hx, hdx⟩ := hseen k hk
                exact ⟨x, by simp [Std.HashSet.mem_insert, hx],
                  denoteN_ext hdx (hst1.ext.trans hst2.ext)⟩
            obtain ⟨hst3, hgo⟩ := constNamesGo_run ns cs _ _ hctx2 hseen' hrest
            refine ⟨(hst1.trans hst2).trans hst3, ?_⟩
            simp [hcn, hgo]

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:469-479 constNamesOk -/
theorem constNamesOk_run {pk : OleanPins} {r : Region} {root : UInt64} {s s' : AState}
    (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.constNamesOk pk r root s = .ok (true, s')) :
    ParseStep s s' ∧ ConLeche.Frontend.Olean.constNamesOk r root = true := by
  generalize hF : ConRon.Arena.Frontend.Olean.constNamesOk pk r root = f at h
  unfold ConRon.Arena.Frontend.Olean.constNamesOk at hF
  unfold ConLeche.Frontend.Olean.constNamesOk
  split at hF
  · subst hF
    cases (AM.pure_ok h).1
  · rename_i g hg
    simp only [hg]
    by_cases hc : r.isCtor g 0 5 = true
    · simp only [hc, ↓reduceIte] at hF ⊢
      split at hF
      · rename_i ns cs hns hcs
        by_cases he : (ns.size == cs.size) = true
        · simp only [he, ↓reduceIte] at hF
          subst hF
          obtain ⟨hst, hgo⟩ := constNamesGo_run ns.toList cs.toList _
            (Std.HashSet.emptyWithCapacity ns.size) hctx (fun n hn => by simp at hn) h
          refine ⟨hst, ?_⟩
          simp [hns, hcs, he, hgo]
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hF
          subst hF
          cases (AM.pure_ok h).1
      · subst hF
        cases (AM.pure_ok h).1
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
      subst hF
      cases (AM.pure_ok h).1

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany — `addrs.all (constNamesOk r)` -/
theorem allConstNamesOk_run {pk : OleanPins} {r : Region} :
    ∀ (addrs : List UInt64) {s s' : AState}, Ctx pk s →
      ConRon.Arena.Frontend.Olean.allConstNamesOk pk r addrs s = .ok (true, s') →
      ParseStep s s' ∧ ∀ a ∈ addrs, ConLeche.Frontend.Olean.constNamesOk r a = true
  | [], s, s', hctx, h => by
    rw [ConRon.Arena.Frontend.Olean.allConstNamesOk] at h
    obtain ⟨-, hs⟩ := AM.pure_ok h
    subst hs
    exact ⟨ParseStep.refl hctx.ok, by simp⟩
  | a :: as, s, s', hctx, h => by
    rw [ConRon.Arena.Frontend.Olean.allConstNamesOk] at h
    obtain ⟨b, s₁, h1, hrest⟩ := AM.bind_ok h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrest
      cases (AM.pure_ok hrest).1
    | true =>
      simp only [↓reduceIte] at hrest
      obtain ⟨hst1, ha⟩ := constNamesOk_run hctx h1
      obtain ⟨hst2, has⟩ := allConstNamesOk_run as (hctx.step hst1) hrest
      refine ⟨hst1.trans hst2, ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact has x hx

/-! ## The skeletons -/

/-- con-leche: none — `skelFits` leaves the state alone where it answers. -/
theorem skelFits_run {N E : Type} {c : CEntryF N E} {u : Unit} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.skelFits c s = .ok (u, s')) : s' = s := by
  generalize hF : ConRon.Arena.Frontend.Olean.skelFits c = f at h
  unfold ConRon.Arena.Frontend.Olean.skelFits at hF
  split at hF <;> (try dsimp only at hF) <;> (try split at hF) <;> subst hF <;>
    first
    | exact (AM.pure_ok h).2
    | (obtain ⟨k, s₁, h1, h2⟩ := AM.bind_ok h
       exact (AM.pure_ok h2).2.trans (natWord_run h1).2)

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany -/
theorem constsSkel_run {r : Region} :
    ∀ (cs : List Nat) {l : List (CEntryF UInt64 UInt64)} {s s' : AState},
      ConRon.Arena.Frontend.Olean.constsSkel r cs s = .ok (some l, s') →
      s' = s ∧ cs.mapM (constSkel r) = some l
  | [], l, s, s', h => by
    rw [ConRon.Arena.Frontend.Olean.constsSkel] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    exact ⟨hs, rfl⟩
  | c :: cs, l, s, s', h => by
    rw [ConRon.Arena.Frontend.Olean.constsSkel] at h
    cases hc : constSkel r c with
    | none =>
      simp only [hc] at h
      exact (none_not_some h).elim
    | some sk =>
      simp only [hc] at h
      obtain ⟨u, s₁, h1, hr1⟩ := AM.bind_ok h
      have hs1 := skelFits_run h1
      subst hs1
      obtain ⟨o, s₂, h2, hr2⟩ := AM.bind_ok hr1
      cases o with
      | none => exact (none_not_some hr2).elim
      | some rest =>
        obtain ⟨hv, hs⟩ := AM.pure_ok hr2
        cases hv
        subst hs
        obtain ⟨hs2, hm⟩ := constsSkel_run cs h2
        exact ⟨hs2, by simp only [List.mapM_cons, hc, hm]; rfl⟩

/-- A module's skeleton, with its constants'. -/
@[expose] def SkelOf (r : Region) (a : UInt64) (p : ModSkel × List (CEntryF UInt64 UInt64)) : Prop :=
  moduleSkel r a = some p.1 ∧ p.1.consts.mapM (constSkel r) = some p.2

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany -/
theorem manySkels_run {r : Region} :
    ∀ (addrs : List UInt64) {ms : List (ModSkel × List (CEntryF UInt64 UInt64))} {s s' : AState},
      ConRon.Arena.Frontend.Olean.manySkels r addrs s = .ok (some ms, s') →
      s' = s ∧ ListRel (SkelOf r) addrs ms
  | [], ms, s, s', h => by
    rw [ConRon.Arena.Frontend.Olean.manySkels] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    exact ⟨hs, .nil⟩
  | a :: as, ms, s, s', h => by
    rw [ConRon.Arena.Frontend.Olean.manySkels] at h
    cases hc : moduleSkel r a with
    | none =>
      simp only [hc] at h
      exact (none_not_some h).elim
    | some sk =>
      simp only [hc] at h
      obtain ⟨o, s₁, h1, h⟩ := AM.bind_ok h
      cases o with
      | none => exact (none_not_some h).elim
      | some cs =>
        obtain ⟨o', s₂, h2, h⟩ := AM.bind_ok h
        cases o' with
        | none => exact (none_not_some h).elim
        | some rest =>
          obtain ⟨hv, hs⟩ := AM.pure_ok h
          cases hv
          subst hs
          obtain ⟨rfl, hcs⟩ := constsSkel_run _ h1
          obtain ⟨rfl, hrest⟩ := manySkels_run as h2
          exact ⟨rfl, .cons ⟨hc, hcs⟩ hrest⟩

/-! ## The memo's reads -/

/-- The module values of the memo's reads are the specification's, address by address. -/
theorem readAll_spec {st : EStore} {r : Region} {nm : UInt64 → Option NIdx}
    {ex : UInt64 → Option EIdx} {names exprs : List UInt64}
    (hN : ∀ v ∈ names, ∀ y, nm v = some y → ∃ z, nameP r v = some z ∧ denoteN st.ns y = some z)
    (hE : ∀ v ∈ exprs, ∀ y, ex v = some y → ∃ z, exprP r v = some z ∧ denoteE st y = some z) :
    ∀ {addrs : List UInt64} {ms : List (ModSkel × List (CEntryF UInt64 UInt64))}
      {ds : List ConRon.Arena.Frontend.Olean.ModDecoded}, ListRel (SkelOf r) addrs ms →
      (∀ a ∈ addrs, ConLeche.Frontend.Olean.constNamesOk r a = true) →
      (∀ p ∈ ms, ∀ i ∈ p.1.imports, i.module ∈ names) →
      (∀ p ∈ ms, ∀ c ∈ p.2, ∀ v ∈ c.names, v ∈ names) →
      (∀ p ∈ ms, ∀ c ∈ p.2, ∀ v ∈ c.exprs, v ∈ exprs) →
      ms.mapM (fun p => readOf nm ex p.1 p.2) = some ds →
      ∃ zs, addrs.mapM (decodeAt r) = some zs ∧ ds.mapM (denoteMod st) = some zs := by
  intro addrs ms ds hrel
  induction hrel generalizing ds with
  | nil =>
    intro _ _ _ _ h
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | @cons a p as ps hp _ ih =>
    intro hok hi hn he h
    simp only [List.mapM_cons] at h
    obtain ⟨d, hd, h⟩ := bind_some_left h
    obtain ⟨ds', hds, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    obtain ⟨z, hz, hdz⟩ := readOf_spec (r := r) (st := st) hd
      (fun i hm y hy => hN _ (hi p (by simp) i hm) y hy)
      (fun c hc v hv y hy => hN v (hn p (by simp) c hc v hv) y hy)
      (fun c hc v hv y hy => hE v (he p (by simp) c hc v hv) y hy)
    obtain ⟨zs, h1, h2⟩ := ih (fun x hx => hok x (List.mem_cons_of_mem _ hx))
      (fun q hq => hi q (List.mem_cons_of_mem _ hq)) (fun q hq => hn q (List.mem_cons_of_mem _ hq))
      (fun q hq => he q (List.mem_cons_of_mem _ hq)) hds
    have hdec : decodeAt r a = some z := by
      rw [ConLeche.Frontend.Olean.decodeAt_skels r a (hok a (by simp)), hp.1]
      show (p.1.consts.mapM (constSkel r) >>= _) = _
      rw [hp.2]
      exact hz
    refine ⟨z :: zs, ?_, ?_⟩
    · simp only [List.mapM_cons, hdec, h1]; rfl
    · simp only [List.mapM_cons, hdz, h2]; rfl

/-- con-leche: ConLeche/Verify/Frontend/Olean/Equiv.lean:393 parseMany_eq — **the modules read
fast are the specification's**. -/
theorem parseMany_run {pk : OleanPins} {r : Region} {addrs : List UInt64}
    {ds : List ConRon.Arena.Frontend.Olean.ModDecoded} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.parseMany pk r addrs s = .ok (some ds, s')) :
    ParseStep s s' ∧ ∃ zs, addrs.mapM (decodeAt r) = some zs ∧
      ds.mapM (denoteMod s'.store) = some zs := by
  unfold ConRon.Arena.Frontend.Olean.parseMany at h
  obtain ⟨b, s₁, h1, h⟩ := AM.bind_ok h
  cases b with
  | false =>
    dsimp only at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact (none_not_some h).elim
  | true =>
    dsimp only at h
    simp only [↓reduceIte, pure_bind] at h
    obtain ⟨hst1, hok⟩ := allConstNamesOk_run addrs hctx h1
    have hctx1 := hctx.step hst1
    obtain ⟨o, s₂, h2, hr1⟩ := AM.bind_ok h
    cases o with
    | none => exact (none_not_some hr1).elim
    | some ms =>
      obtain ⟨hs2, hrel⟩ := manySkels_run addrs h2
      subst hs2
      obtain ⟨o', s₃, h3, hr2⟩ := AM.bind_ok hr1
      cases o' with
      | none => exact (none_not_some hr2).elim
      | some memo =>
        obtain ⟨hst2, hN, hE⟩ := runPasses_run hctx1 h3
        have hpr := PR.mapM (f := fun p : ModSkel × List (CEntryF UInt64 UInt64) =>
            OptionT.mk (ConRon.Arena.Frontend.Olean.ModSkel.read (DS.read pk r memo) p.1 p.2))
          (g := fun p => readOf (memo.nameOf pk r) (memo.exprOf r) p.1 p.2)
          (fun p => modSkelRead_pr (fun _ => rfl) (fun _ => rfl) p.1 p.2) ms s₃
        have hh : (ms.mapM (fun p => OptionT.mk
            (ConRon.Arena.Frontend.Olean.ModSkel.read (DS.read pk r memo) p.1 p.2))) s₃
            = .ok (some ds, s') := hr2
        rw [hpr] at hh
        injection hh with hh
        simp only [Prod.mk.injEq] at hh
        obtain ⟨hreads, rfl⟩ := hh
        obtain ⟨zs, h4, h5⟩ := readAll_spec hN hE hrel hok
          (fun p hp i hi => by
            simp only [List.mem_append, List.mem_flatMap, List.mem_map]
            exact .inl ⟨p.1, ⟨p, hp, rfl⟩, i, hi, rfl⟩)
          (fun p hp c hc v hv => by
            simp only [List.mem_append, List.mem_flatMap, List.mem_map]
            refine .inr ⟨c, ?_, hv⟩
            simp only [List.mem_flatten, List.mem_map]
            exact ⟨p.2, ⟨p, hp, rfl⟩, hc⟩)
          (fun p hp c hc v hv => by
            simp only [List.mem_flatMap]
            refine ⟨c, ?_, hv⟩
            simp only [List.mem_flatten, List.mem_map]
            exact ⟨p.2, ⟨p, hp, rfl⟩, hc⟩)
          hreads
        exact ⟨hst1.trans hst2, zs, h4, h5⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Equiv.lean:434 parseAt_eq_spec -/
theorem parseAt_run {pk : OleanPins} {r : Region} {a : UInt64}
    {d : ConRon.Arena.Frontend.Olean.ModDecoded} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.parseAt pk r a s = .ok (some d, s')) :
    ParseStep s s' ∧ ∃ z, decodeAt r a = some z ∧ denoteMod s'.store d = some z := by
  unfold ConRon.Arena.Frontend.Olean.parseAt at h
  obtain ⟨o, s₁, h1, h⟩ := AM.bind_ok h
  have hres : o = some [d] ∧ s₁ = s' := by
    generalize hO : o = o' at h
    match o', h with
    | some [_], h =>
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      cases hv
      exact ⟨rfl, hs.symm⟩
    | none, h => cases (AM.pure_ok h).1
    | some [], h => cases (AM.pure_ok h).1
    | some (_ :: _ :: _), h => cases (AM.pure_ok h).1
  obtain ⟨rfl, rfl⟩ := hres
  obtain ⟨hst, zs, hz1, hz2⟩ := parseMany_run hctx h1
  simp only [List.mapM_cons, List.mapM_nil] at hz1 hz2
  cases hdec : decodeAt r a with
  | none => simp [hdec, bind, Option.bind] at hz1
  | some z =>
    cases hden : denoteMod s₁.store d with
    | none => simp [hden, bind, Option.bind] at hz2
    | some w =>
      simp [hdec, bind, Option.bind, pure] at hz1
      simp [hden, bind, Option.bind, pure] at hz2
      subst hz1
      have hzw : w = z := by simpa using hz2
      subst hzw
      exact ⟨hst, w, rfl, rfl⟩

/-! ## The imports off the start of a file -/

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn — the imports read. -/
theorem importsRead_run {pk : OleanPins} {r : Region} {imps : Array Nat}
    {xs : Array (ImportF NIdx)} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.importsRead pk r imps s = .ok (some xs, s')) :
    ParseStep s s' ∧ ∃ zs, imps.mapM (fun i => importSkel r i >>= ImportF.mapM (nameP r)) = some zs ∧
      xs.toList.mapM (denoteImport s'.store) = some zs.toList := by
  unfold ConRon.Arena.Frontend.Olean.importsRead at h
  have h' : (imps.mapM (m := OptionT AM) fun i => do
      let sk ← OptionT.mk (pure (importSkel r i))
      sk.mapM (m := OptionT AM) fun v => OptionT.mk (ConRon.Arena.Frontend.Olean.nameP pk r v)) s
      = .ok (some xs, s') := h
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h'
  obtain ⟨ys, s₁, h1, h2⟩ := OT.bind_ok h'
  obtain ⟨hv, hs⟩ := AM.pure_ok h2
  cases hv
  subst hs
  obtain ⟨hst, zs, hzs, hds⟩ := optT_list_run (pk := pk) (den := denoteImport)
    (g := fun i => importSkel r i >>= ImportF.mapM (nameP r))
    (fun hx hy => denoteImport_ext hx hy)
    (fun i s s' y hctx hrun => by
      obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok hrun
      obtain ⟨hv, hs⟩ := AM.pure_ok h1
      have hsk : importSkel r i = some a := by
        cases hsk : importSkel r i with
        | none => rw [hsk] at hv; cases hv
        | some b => rw [hsk] at hv; cases hv; rfl
      subst hs
      obtain ⟨q, s₂, h3, h4⟩ := OT.bind_ok h2
      obtain ⟨hv', hs'⟩ := AM.pure_ok h4
      cases hv'
      subst hs'
      obtain ⟨hst, z, hz, hd⟩ := nameP_run hctx.ok hctx.off hctx.nulls h3
      refine ⟨hst, { a with module := z }, ?_, ?_⟩
      · rw [hsk]
        show ImportF.mapM (nameP r) a = _
        simp only [ImportF.mapM, hz]; rfl
      · simp only [denoteImport, ImportF.mapM, hd]; rfl) imps.toList hctx h1
  refine ⟨hst, zs.toArray, ?_, ?_⟩
  · rw [Array.mapM_eq_mapM_toList, hzs]; rfl
  · simpa using hds

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn -/
theorem importsIn_run {pk : OleanPins} {r : Region} {c : Nat}
    {xs : Array (ImportF NIdx)} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.importsIn pk r c s = .ok (some xs, s')) :
    ParseStep s s' ∧ ∃ zs, ConLeche.Frontend.Olean.importsIn r c = some zs ∧
      xs.toList.mapM (denoteImport s'.store) = some zs.toList := by
  generalize hF : ConRon.Arena.Frontend.Olean.importsIn pk r c = f at h
  unfold ConRon.Arena.Frontend.Olean.importsIn at hF
  unfold ConLeche.Frontend.Olean.importsIn
  by_cases h1 : (r.tag c == ConLeche.Frontend.Olean.tagArray) = true
  · simp only [h1, ↓reduceIte] at hF
    by_cases h2 : c + 24 + 8 * (ConLeche.Frontend.Olean.rdU64 r.bytes (c + 8)).toNat ≤ r.fileEnd c
    · simp only [h2, ↓reduceIte] at hF
      split at hF
      · subst hF
        exact (none_not_some h).elim
      · rename_i imps himps
        subst hF
        obtain ⟨hst, zs, hz, hd⟩ := importsRead_run hctx h
        refine ⟨hst, zs, ?_, hd⟩
        have himps' : r.objArrayGo c (c + 24) (ConLeche.Frontend.Olean.rdU64 r.bytes (c + 8)).toNat 0 #[]
            = some imps := by simpa using himps
        simp only [bind, Option.bind] at hz
        simp [h1, h2, himps', hz, bind, Option.bind]
    · simp only [h2, ↓reduceIte] at hF
      subst hF
      exact (none_not_some h).elim
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF
    exact (none_not_some h).elim

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:75-83 importsPre -/
theorem importsPre_run {pk : OleanPins} {b : ByteArray}
    {xs : Array (ImportF NIdx)} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.importsPre pk b s = .ok (some xs, s')) :
    ParseStep s s' ∧ ∃ zs, ConLeche.Frontend.Olean.importsPre b = some zs ∧
      xs.toList.mapM (denoteImport s'.store) = some zs.toList := by
  generalize hF : ConRon.Arena.Frontend.Olean.importsPre pk b = f at h
  unfold ConRon.Arena.Frontend.Olean.importsPre at hF
  unfold ConLeche.Frontend.Olean.importsPre
  split at hF
  · rename_i c e hw
    subst hF
    simp only [hw]
    exact importsIn_run hctx h
  · subst hF
    exact (none_not_some h).elim

/-! ## One view -/

instance : LawfulBEq (ImportF NIdx) where
  eq_of_beq {a b} h := by
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases b with ⟨b1, b2, b3, b4⟩
    change (a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    rfl
  rfl {a} := by
    rcases a with ⟨a1, a2, a3, a4⟩
    change (a1 == a1 && a2 == a2 && a3 == a3 && a4 == a4) = true
    simp

/-- con-leche: ConLeche/Verify/Frontend/Olean/View.lean:27 parseView_eq_spec — **where the
twin's view reads, the specification has its denotation.**  The twin's check of the imports
is on handles; a handle equal is a denotation equal. -/
theorem parseView_run {pk : OleanPins} {f : ModFiles} {level : OLeanLevel}
    {d : ConRon.Arena.Frontend.Olean.ModDecoded} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.parseView pk f level s = .ok (some d, s')) :
    ParseStep s s' ∧ ∃ z, ConLeche.Frontend.Olean.decodeModuleSpec f level = some z ∧
      denoteMod s'.store d = some z := by
  generalize hF : ConRon.Arena.Frontend.Olean.parseView pk f level = fn at h
  unfold ConRon.Arena.Frontend.Olean.parseView at hF
  split at hF
  · subst hF
    exact (none_not_some h).elim
  · rename_i r a hvr
    subst hF
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none => exact (none_not_some h2).elim
    | some d' =>
      obtain ⟨hst1, z, hz, hdz⟩ := parseAt_run hctx h1
      have hctx1 := hctx.step hst1
      unfold ConRon.Arena.Frontend.Olean.checkImportsPre at h2
      obtain ⟨o', s₂, h3, h4⟩ := AM.bind_ok h2
      cases o' with
      | none => exact (none_not_some h4).elim
      | some pre =>
        by_cases he : (pre == d'.imports) = true
        · simp only [he, ↓reduceIte] at h4
          obtain ⟨hv, hs⟩ := AM.pure_ok h4
          cases hv
          subst hs
          obtain ⟨hst2, preC, hp, hdp⟩ := importsPre_run hctx1 h3
          have hpe : pre = d.imports := by simpa using he
          subst hpe
          have hdz2 := denoteMod_ext hst2.ext hdz
          have hdz3 := hdz2
          unfold denoteMod at hdz3
          obtain ⟨is, h5, hdz3⟩ := bind_some_left hdz3
          obtain ⟨cs, h6, hdz3⟩ := bind_some_left hdz3
          simp only [pure, Option.some.injEq] at hdz3
          have hic : preC.toList = is := Option.some.inj (hdp.symm.trans h5)
          have hic' : preC = z.imports := by
            rw [← hdz3, ← hic]
          refine ⟨hst1.trans hst2, z, ?_, hdz2⟩
          simp only [ConLeche.Frontend.Olean.decodeModuleSpec, hvr]
          show (decodeAt r a >>= _) = _
          rw [hz]
          show (if (ConLeche.Frontend.Olean.importsPre f.exported.bytes == some z.imports) = true
            then _ else _) = _
          rw [hp, hic']
          simp
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at h4
          exact (none_not_some h4).elim

end ConRon.Bridge.Frontend.Olean
