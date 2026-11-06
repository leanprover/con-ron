/-
# `ConRon.Refine2.Frontend.Olean.Lazy` — `olean/lazy.rs` against the twin's

**Task #143, Theorem 2** (upstream task #481).  A module's load, its theorems' values left in
the file: what each constant mentions, read off the file (`uses_go`, `uses_roots`, `uses_of`,
`uses_read`), the constants with a theorem's value a reference (`lazy_entry`, `value_ref`),
the frontier (`frontier_walk`, `frontier_of`), and the load around them (`load_at`,
`load_view`).  The two walks carry fuel on both sides (the twin's `Arena/Frontend/Olean/
Lazy.lean` note); a stack is a `Vec` and its top against a `List` (`StackRel`).

A load is reached through a file read (`load_module`), so each statement here claims the
Rust's accept: its `Ok` is the twin's `some`, the answers and the states related.
-/
import ConRon.Refine2.Frontend.Olean.Sparse
import ConRon.Refine2.Frontend.Olean.Closure
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Refine2.Frontend.Olean.FastRoots
import ConRon.Arena.Frontend.Olean.Lazy

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.lazy

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (loadAt loadView loadRoots valueRoots lazyEntries loadImports
  usesOf frontierWalk frontierOf)
open ConLeche.Frontend.Olean (usesNames lazyRoots maxLoc closureFuel moduleSkel)

/-! ## The judgement of an accepted read -/

/-- **A read's accept**: the Rust's `Ok` is the twin's `some`, the answers related by `R` and
the states as every reader relates them. -/
def AR {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore))
    (x : AM (Option β)) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ a s', m = ok (.Ok a, s') →
      ∃ b lst', x.run lst = .ok (some b, lst') ∧ R a b ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')

/-- A read's lockstep judgement claims its accept. -/
theorem RS.ar {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {m} {x : AM (Option β)} (h : RS pers R st lst m x) :
    AR pers R st lst m x := by
  intro hrel hinv a s' hm
  exact h hrel hinv _ _ hm

/-! ## The relations of a load's data -/

/-- The walk's stamps, by slot, as the twin's. -/
def StampsRel (s : alloc.vec.Vec Std.U64) (t : Array Nat) : Prop := s.val.map (·.val) = t.toList

/-- What the walk writes, as the twin's words. -/
def OutRel (o : alloc.vec.Vec Std.U64) (t : Array UInt64) : Prop := o.val.map absWord = t.toList

/-- Every constant's output. -/
def OutsRel (o : alloc.vec.Vec (alloc.vec.Vec Std.U64)) (t : Array (Array UInt64)) : Prop :=
  List.Forall₂ OutRel o.val t.toList

/-! ## The kinds' codes -/

/-- `kind_code` is `kindCode`. -/
theorem kind_code_eq {k : Std.U8} {c : Std.U64} (h : kind_code k = ok c) :
    c.val = ConLeche.Frontend.Olean.kindCode (absByte k) := by
  rw [kind_code] at h
  rw [ConLeche.Frontend.Olean.kindCode]
  simp only [← absByte_k_name, ← absByte_k_level, ← absByte_k_levels]
  by_cases h1 : k = frontend.olean.fast.K_NAME
  · rw [ite_eq_left h1] at h; rw [ite_eq_left (kind_test.mp h1)]; cases Result.ok_injective h; rfl
  · rw [ite_eq_right h1] at h; rw [ite_eq_right (fun he => h1 (kind_test.mpr he))]
    by_cases h2 : k = frontend.olean.fast.K_LEVEL
    · rw [ite_eq_left h2] at h; rw [ite_eq_left (kind_test.mp h2)]; cases Result.ok_injective h; rfl
    · rw [ite_eq_right h2] at h; rw [ite_eq_right (fun he => h2 (kind_test.mpr he))]
      by_cases h3 : k = frontend.olean.fast.K_LEVELS
      · rw [ite_eq_left h3] at h; rw [ite_eq_left (kind_test.mp h3)]; cases Result.ok_injective h; rfl
      · rw [ite_eq_right h3] at h; rw [ite_eq_right (fun he => h3 (kind_test.mpr he))]
        cases Result.ok_injective h; rfl

/-! ## The roots of a load -/

/-- A `flatMap` against a `filterMap` over related lists. -/
theorem forall₂_flatMap_filterMap {α β γ : Type} {R : α → β → Prop}
    {g : α → List γ} {g' : β → Option γ} (hg : ∀ a b, R a b → g a = (g' b).toList) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.flatMap g = l'.filterMap g'
  | _, _, .nil => rfl
  | _, _, .cons hab h => by
    rw [List.flatMap_cons, hg _ _ hab, forall₂_flatMap_filterMap hg h, List.filterMap_cons]
    cases g' _ <;> rfl

/-- A `flatMap` over related lists, each part related. -/
theorem forall₂_flatMap_map {α β γ δ : Type} {R : α → β → Prop} {A : γ → δ}
    {g : α → List γ} {g' : β → List δ} (hg : ∀ a b, R a b → (g a).map A = g' b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → (l.flatMap g).map A = l'.flatMap g'
  | _, _, .nil => rfl
  | _, _, .cons hab h => by
    simp only [List.flatMap_cons, List.map_append, hg _ _ hab, forall₂_flatMap_map hg h]

/-- **`load_roots` is `loadRoots`**: the imports' names and every constant's names, and every
constant's expressions. -/
theorem load_roots_val {sk : frontend.olean.spec.ModSkel} {sk' : ConLeche.Frontend.Olean.ModSkel}
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hsk : ModSkelRel sk sk')
    (hv : List.Forall₂ EV v.val skels) {nb ea}
    (h : load_roots sk v = ok (nb, ea)) :
    nb.val.map absWord = (loadRoots sk' skels).1 ∧ ea.val.map absWord = (loadRoots sk' skels).2 := by
  rw [load_roots] at h
  peel h as names, hnames
  have e0 := append_loop0 (src := sk.imports.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val)
    (f := fun x => [x.module]) (loop := load_roots_loop0 sk) (fun s j o h => by
      rw [load_roots_loop0] at h
      by_cases hj : j < alloc.vec.Vec.len sk.imports
      · right
        rw [ite_eq_left hj] at h
        peel h as x, hx
        peel h as s2, hs2
        peel h as j1, hj1
        exact ⟨x, s2, j1, ConRon.Refine.ExprOps.vec_index_getElem? hx, ConRon.Refine.vec_push_val hs2,
          ConRon.Refine.HashMap.uscalar_add_eq hj1, h⟩
      · left
        rw [ite_eq_right hj] at h
        exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩) hnames
  have hnew : (alloc.vec.Vec.new Std.U64).val = [] := Slice.from_val _ _
  have hstep : ∀ (Ab : (alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64) → List Std.U64)
      (fn : frontend.olean.spec.CEntryF Std.U64 Std.U64 → List Std.U64),
      (∀ {c n e n1 e1}, frontend.olean.fast.c_entry_names c n = ok n1 →
        frontend.olean.fast.c_entry_exprs c e = ok e1 → Ab (n1, e1) = Ab (n, e) ++ fn c) →
      ∀ s i o, load_roots_loop1 v s.1 s.2 i = ok o → (v.val.length ≤ i.val ∧ o = s) ∨
        ∃ x s1 i1, v.val[i.val]? = some x ∧ Ab s1 = Ab s ++ fn x ∧ i1.val = i.val + 1 ∧
          load_roots_loop1 v s1.1 s1.2 i1 = ok o := by
    intro Ab fn hf s i o h
    rw [load_roots_loop1] at h
    by_cases hi : i < alloc.vec.Vec.len v
    · right
      rw [ite_eq_left hi] at h
      peel h as c, hc
      peel h as n1, hn1
      peel h as e1, he1
      peel h as i1, hi1
      exact ⟨c, (n1, e1), i1, ConRon.Refine.ExprOps.vec_index_getElem? hc, hf hn1 he1,
        ConRon.Refine.HashMap.uscalar_add_eq hi1, h⟩
    · left
      rw [ite_eq_right hi] at h
      exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩
  have en := append_loop0 (src := v.val)
    (Ab := fun s : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64 => s.1.val) (f := namesL)
    (loop := fun s i => load_roots_loop1 v s.1 s.2 i) (s := (names, alloc.vec.Vec.new Std.U64))
    (hstep _ _ (fun h1 _ => c_entry_names_val h1)) h
  have ee := append_loop0 (src := v.val)
    (Ab := fun s : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64 => s.2.val) (f := exprsL)
    (loop := fun s i => load_roots_loop1 v s.1 s.2 i) (s := (names, alloc.vec.Vec.new Std.U64))
    (hstep _ _ (fun _ h2 => c_entry_exprs_val h2)) h
  simp only at en ee
  rw [hnew, List.nil_append] at e0
  rw [hnew, List.nil_append] at ee
  refine ⟨?_, ?_⟩
  · rw [en, e0, List.map_append, forall₂_flatMap_map (fun _ _ h => namesL_abs h) hv]
    simp only [loadRoots, ← hsk.imports]
    congr 1
    induction sk.imports.val with
    | nil => rfl
    | cons x t ih => simp [absImportF, ih]
  · rw [ee, forall₂_flatMap_map (fun _ _ h => exprsL_abs h) hv]
    rfl

/-- **`uses_of` is `usesOf`**, from fresh stamps: every constant's output. -/
theorem uses_of_ok {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {stamps : alloc.vec.Vec Std.U64} {ts : Array Nat} (hs : StampsRel stamps ts)
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels)
    {o3 s'} (h : uses_of bs r stamps 1#u64 v = ok (some o3, s')) :
    ∃ outs, usesOf (absRegion bs r) ts 1 skels (Array.mkEmpty skels.length) = some outs ∧
      OutsRel o3 outs := by
  sorry -- T143-STUB

/-- **`uses_names` appends `usesNames`.** -/
theorem uses_names_val {o3 : alloc.vec.Vec (alloc.vec.Vec Std.U64)} {outs : Array (Array UInt64)}
    (ho : OutsRel o3 outs) {acc acc' : alloc.vec.Vec Std.U64}
    (h : uses_names o3 acc = ok acc') :
    acc'.val.map absWord = acc.val.map absWord ++ usesNames outs := by
  -- the twin's two folds, as a `flatMap` of `filter`s
  have hpush : ∀ (l : List UInt64) (a : Array UInt64),
      (l.foldl (fun acc v => if v == ConLeche.Frontend.Olean.usesNat ||
          v == ConLeche.Frontend.Olean.usesStr then acc else acc.push v) a).toList =
        a.toList ++ l.filter (fun v => !(v == ConLeche.Frontend.Olean.usesNat ||
          v == ConLeche.Frontend.Olean.usesStr)) := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x t ih =>
      intro a
      rw [List.foldl_cons, ih, List.filter_cons]
      by_cases hx : (x == ConLeche.Frontend.Olean.usesNat || x == ConLeche.Frontend.Olean.usesStr) = true
      · simp [hx]
      · simp only [Bool.not_eq_true] at hx
        simp [hx]
  have hwords : ∀ (l : List (Array UInt64)) (a : Array UInt64),
      (l.foldl (fun acc out => out.foldl (fun acc v => if v == ConLeche.Frontend.Olean.usesNat ||
          v == ConLeche.Frontend.Olean.usesStr then acc else acc.push v) acc) a).toList =
        a.toList ++ l.flatMap (fun o => o.toList.filter (fun v => !(v == ConLeche.Frontend.Olean.usesNat ||
          v == ConLeche.Frontend.Olean.usesStr))) := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x t ih =>
      intro a
      rw [List.foldl_cons, ih, List.flatMap_cons, ← List.append_assoc, ← Array.foldl_toList, hpush]
  have hun : usesNames outs = outs.toList.flatMap (fun o => o.toList.filter (fun v =>
      !(v == ConLeche.Frontend.Olean.usesNat || v == ConLeche.Frontend.Olean.usesStr))) := by
    rw [usesNames, ← Array.foldl_toList, hwords]; rfl
  -- the Rust's two loops
  let g : Std.U64 → List Std.U64 := fun v =>
    if v = frontend.olean.lazy.USES_NAT then [] else if v = frontend.olean.lazy.USES_STR then [] else [v]
  have inner : ∀ (i : Std.Usize) (x : alloc.vec.Vec Std.U64), o3.val[i.val]? = some x →
      ∀ s j o, uses_names_loop0_loop0 o3 s i j = ok o → (x.val.length ≤ j.val ∧ o = s) ∨
        ∃ y s1 j1, x.val[j.val]? = some y ∧ s1.val = s.val ++ g y ∧ j1.val = j.val + 1 ∧
          uses_names_loop0_loop0 o3 s1 i j1 = ok o := by
    intro i x hx s j o h
    rw [uses_names_loop0_loop0] at h
    peel h as w, hw
    have hw2 := ConRon.Refine.ExprOps.vec_index_getElem? hw
    rw [hx] at hw2
    cases Option.some.inj hw2
    by_cases hj : j < alloc.vec.Vec.len x
    · right
      rw [ite_eq_left hj] at h
      peel h as y, hy
      peel h as s1, hs1
      peel h as j1, hj1
      refine ⟨y, s1, j1, ConRon.Refine.ExprOps.vec_index_getElem? hy, ?_,
        ConRon.Refine.HashMap.uscalar_add_eq hj1, h⟩
      by_cases h0 : y = frontend.olean.lazy.USES_NAT
      · rw [ite_eq_left h0] at hs1; cases Result.ok_injective hs1; simp [g, h0]
      · rw [ite_eq_right h0] at hs1
        by_cases h2 : y = frontend.olean.lazy.USES_STR
        · rw [ite_eq_left h2] at hs1; cases Result.ok_injective hs1; simp [g, h0, h2]
        · rw [ite_eq_right h2] at hs1; rw [ConRon.Refine.vec_push_val hs1]; simp [g, h0, h2]
    · left
      rw [ite_eq_right hj] at h
      exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩
  have e := append_loop0 (src := o3.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val)
    (f := fun x => x.val.flatMap g) (loop := uses_names_loop0 o3) (fun s i o h => by
      rw [uses_names_loop0] at h
      by_cases hi : i < alloc.vec.Vec.len o3
      · right
        rw [ite_eq_left hi] at h
        have hlt : i.val < o3.val.length := by scalar_tac
        have hx : o3.val[i.val]? = some (o3.val[i.val]'hlt) := List.getElem?_eq_getElem hlt
        peel h as s1, hs1
        peel h as i2, hi2
        exact ⟨_, s1, i2, hx, append_loop0 (src := (o3.val[i.val]'hlt).val)
          (Ab := fun s : alloc.vec.Vec Std.U64 => s.val) (f := g)
          (loop := fun s j => uses_names_loop0_loop0 o3 s i j) (inner i _ hx) hs1,
          ConRon.Refine.HashMap.uscalar_add_eq hi2, h⟩
      · left
        rw [ite_eq_right hi] at h
        exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩) h
  rw [e, List.map_append, hun]
  congr 1
  refine forall₂_flatMap_map (fun x t hxt => ?_) ho
  rw [← (hxt : x.val.map absWord = t.toList)]
  induction x.val with
  | nil => rfl
  | cons y l ih =>
    rw [List.flatMap_cons, List.map_append, ih, List.map_cons, List.filter_cons]
    have hn : (absWord y == ConLeche.Frontend.Olean.usesNat) = decide (y = frontend.olean.lazy.USES_NAT) := by
      rw [show ConLeche.Frontend.Olean.usesNat = absWord frontend.olean.lazy.USES_NAT by
        unfold frontend.olean.lazy.USES_NAT; rfl]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, absWord_eq_iff]
    have hs : (absWord y == ConLeche.Frontend.Olean.usesStr) = decide (y = frontend.olean.lazy.USES_STR) := by
      rw [show ConLeche.Frontend.Olean.usesStr = absWord frontend.olean.lazy.USES_STR by
        unfold frontend.olean.lazy.USES_STR; rfl]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, absWord_eq_iff]
    rw [hn, hs]
    by_cases h0 : y = frontend.olean.lazy.USES_NAT
    · simp [g, h0, hn, hs]
    · by_cases h2 : y = frontend.olean.lazy.USES_STR
      · simp [g, h0, h2, hn, hs]
      · simp [g, h0, h2, hn, hs]

/-- **`load_at`'s loop collects `lazyRoots`.** -/
theorem load_at_loop_val {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels)
    {o} (h : load_at_loop v (alloc.vec.Vec.new Std.U64) 0#usize = ok o) :
    o.val.map absWord = skels.flatMap lazyRoots := by
  have hnew : (alloc.vec.Vec.new Std.U64).val = [] := Slice.from_val _ _
  have e := append_loop0 (src := v.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val)
    (f := fun c => match c.kind with
      | .Thm _ _ => [c.ty]
      | _ => exprsL c)
    (loop := load_at_loop v) (fun s k o h => by
      rw [load_at_loop] at h
      by_cases hk : k < alloc.vec.Vec.len v
      · right
        rw [ite_eq_left hk] at h
        peel h as c, hc
        peel h as s1, hs1
        peel h as k1, hk1
        refine ⟨c, s1, k1, ConRon.Refine.ExprOps.vec_index_getElem? hc, ?_,
          ConRon.Refine.HashMap.uscalar_add_eq hk1, h⟩
        rw [lazy_roots] at hs1
        cases hck : c.kind <;> rw [hck] at hs1 <;> simp only at hs1 ⊢ <;>
          first | exact c_entry_exprs_val hs1 | exact ConRon.Refine.vec_push_val hs1
      · left
        rw [ite_eq_right hk] at h
        exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩) h
  rw [e, hnew, List.nil_append]
  refine forall₂_flatMap_map (fun c c' hab => ?_) hv
  have hx := exprsL_abs hab
  obtain ⟨-, -, hty, hk⟩ := hab
  rw [lazyRoots]
  obtain ⟨n, lp, ty, k⟩ := c
  obtain ⟨n', lp', ty', k'⟩ := c'
  cases k <;> cases k' <;> try exact hk.elim
  all_goals first
    | (simp only at hty ⊢; simp [hty])
    | exact hx

/-- **`load_imports`' accept is `loadImports`' `true`.** -/
theorem load_imports_ok {pk pers st lst} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t)
    {sk : frontend.olean.spec.ModSkel} {sk' : ConLeche.Frontend.Olean.ModSkel} (hsk : ModSkelRel sk sk')
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f') :
    AR pers (fun (_ : Unit) (b : Unit) => b = ()) st lst (load_imports pk pers st.store bs r d sk f)
      (do if ← loadImports (absPins pk) (absRegion bs r) t sk' f' then pure (some ()) else pure none) := by
  sorry -- T143-STUB

/-- **`lazy_entries`' accept is `lazyEntries`'**: each constant read, a theorem's value its
reference, with what it mentions. -/
theorem lazy_entries_ok {pk pers st lst} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t) {i : Std.U64}
    {o3 : alloc.vec.Vec (alloc.vec.Vec Std.U64)} {outs : Array (Array UInt64)} (ho : OutsRel o3 outs)
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels) :
    AR pers (fun cs L => List.Forall₂ CEntryRel cs.val L) st lst
      (lazy_entries pk pers st.store bs r d i o3 v)
      (lazyEntries (absPins pk) (absRegion bs r) t i.val outs 0 skels) := by
  sorry -- T143-STUB

/-- **`value_roots` is `valueRoots`.** -/
theorem value_roots_val {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels)
    {o} (h : value_roots r v = ok o) : o.val.map (·.val) = valueRoots (absRegion bs r) skels := by
  rw [value_roots] at h
  have hnew : (alloc.vec.Vec.new Std.U64).val = [] := Slice.from_val _ _
  have e := append_loop0 (src := v.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val.map (·.val))
    (f := fun c => match c.kind with
      | .Thm w _ => ((absRegion bs r).loc (absWord w)).toList.map (· + 3)
      | _ => [])
    (loop := fun out i => value_roots_from r v i out) (fun s i o h => by
      rw [value_roots_from] at h
      by_cases hi : i ≥ alloc.vec.Vec.len v
      · left
        rw [ite_eq_left hi] at h
        exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩
      · right
        rw [ite_eq_right hi] at h
        peel h as c, hc
        peel h as g, hg
        peel h as out1, hout1
        peel h as i2, hi2
        refine ⟨c, out1, i2, ConRon.Refine.ExprOps.vec_index_getElem? hc, ?_,
          ConRon.Refine.HashMap.uscalar_add_eq hi2, h⟩
        cases hck : c.kind with
        | Thm w all =>
          rw [hck] at hg
          have el := region_loc_eq bs hg
          simp only
          rw [← el]
          cases g with
          | none => cases Result.ok_injective hout1; simp
          | some g1 =>
            simp only at hout1
            peel hout1 as k3, hk3
            peel hout1 as g3, hg3
            have ek := kind_code_eq hk3
            rw [absByte_k_expr] at ek
            have eg := ConRon.Refine.HashMap.uscalar_add_eq hg3
            rw [ConRon.Refine.vec_push_val hout1]
            simp [eg, ek, ConLeche.Frontend.Olean.kindCode, ConLeche.Frontend.Olean.kExpr,
              ConLeche.Frontend.Olean.kName, ConLeche.Frontend.Olean.kLevel, ConLeche.Frontend.Olean.kLevels]
        | _ => rw [hck] at hg; cases Result.ok_injective hg; cases Result.ok_injective hout1; simp)
    (s := alloc.vec.Vec.new Std.U64) h
  rw [e, hnew, List.map_nil, List.nil_append, valueRoots]
  refine forall₂_flatMap_filterMap (fun c c' hab => ?_) hv
  obtain ⟨-, -, -, hk⟩ := hab
  obtain ⟨n, lp, ty, k⟩ := c
  obtain ⟨n', lp', ty', k'⟩ := c'
  cases k <;> cases k' <;> try exact hk.elim
  case Thm.thm w all w' all' =>
    obtain ⟨hw, -⟩ := hk
    simp only
    rw [← hw]
    cases (absRegion bs r).loc (absWord w) <;> rfl
  all_goals rfl

/-- **`frontier_walk` is `frontierWalk`**, from the value roots on the stack. -/
theorem frontier_walk_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {env seen fr : alloc.vec.Vec Std.U8} {values : alloc.vec.Vec Std.U64}
    {o} (h : frontier_walk bs r env seen fr values (alloc.vec.Vec.len values) = ok o) :
    absM o.2.1 = frontierWalk (absRegion bs r) (absM env) (absM seen) (absM fr) closureFuel
      (values.val.map (·.val)).reverse := by
  sorry -- T143-STUB

/-- **`frontier_of` is `frontierOf`**, from the empty frontier. -/
theorem frontier_of_rel {m fr : alloc.vec.Vec Std.U8} {d : frontend.olean.fast.DS} {t : TDS}
    (hd : DSRel d t) {n : Std.U64} {b0 b} (hb0 : frontend.olean.sparse.frontier_empty = ok b0)
    (h : frontier_of m fr d n 0#u64 b0 = ok b) :
    FrontierRel b (frontierOf (absM m) (absM fr) t n.val 0 {}) := by
  sorry -- T143-STUB

/-! ## The load -/

/-- **`load_at`'s accept is `loadAt`'s**: the load of a module's private view, everything but
its theorems' values. -/
theorem load_at_ok {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {i : Std.U64} {m : arena.handle.NIdx}
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles}
    (hf : ModFilesRel f f') :
    AR pers LoadedRel st lst (load_at pk pers st.store i m f)
      (loadAt (absPins pk) i.val (absNIdx m) f') := by
  intro hrel hinv a s' h
  rw [load_at] at h
  peel h as o, ho
  have hV := mod_files_view_region_eq hf ho
  cases o with
  | none => cases (Prod.mk.inj (Result.ok_injective h)).1
  | some p =>
  obtain ⟨vb, a0⟩ := p
  peel h as bs, hbs
  peel h as r, hr
  obtain ⟨hvr, hfit⟩ := hV bs r hbs hr
  obtain ⟨⟨r1, ar1⟩, hq1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hC := const_names_ok_refines (pk := pk) (root := a0) hfit hrel hinv r1 ar1 hq1
  cases r1 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok b =>
  obtain ⟨b', lst1, hx1, hb', hrel1, hinv1⟩ := hC
  subst hb'
  cases b with
  | false => cases (Prod.mk.inj (Result.ok_injective h)).1
  | true =>
  dsimp only [↓reduceIte] at h
  peel h as o1, ho1
  have hsk := module_skel_eq hfit ho1
  cases o1 with
  | none => cases (Prod.mk.inj (Result.ok_injective h)).1
  | some sk =>
  obtain ⟨sk', hsk', hskR⟩ : ∃ sk', moduleSkel (absRegion bs r) (absWord a0) = some sk' ∧
      ModSkelRel sk sk' := by
    cases hh : moduleSkel (absRegion bs r) (absWord a0) with
    | none => rw [hh] at hsk; cases hsk
    | some sk' => rw [hh] at hsk; cases hsk with | some h => exact ⟨sk', rfl, h⟩
  peel h as r2, hr2
  have hP := consts_skel_ps (bs := bs) (r := r) hskR.consts r2 hr2 lst1
  cases r2 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok v =>
  obtain ⟨skels, hx2, hEV⟩ := hP
  dsimp only at h
  obtain ⟨⟨nb, ea⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hnb, hea⟩ := load_roots_val hskR hEV hq
  peel h as i1, hi1
  peel h as i2, hi2
  peel h as i3, hi3
  peel h as n, hn
  peel h as i4, hi4
  peel h as stamps, hstamps
  have e1 := max_loc_eq (bs := bs) hi1
  have e2 := max_loc_eq (bs := bs) hi2
  have e3 := ConRon.Refine.HashMap.uscalar_div_eq hi3
  have e4 := ConRon.Refine.HashMap.uscalar_add_eq hn
  have hnv : n.val = maxLoc (absRegion bs r) (loadRoots sk' skels).2
      (maxLoc (absRegion bs r) (loadRoots sk' skels).1 0) / 8 + 1 := by
    rw [e4, e3, e2, e1, hnb, hea]; rfl
  have hle := maxLoc_le hfit (ea.val.map absWord) (maxLoc_le hfit (nb.val.map absWord) (Nat.zero_le _))
  have hL := bytes_le_max bs
  have hLn : n.val = maxLoc (absRegion bs r) (ea.val.map absWord)
      (maxLoc (absRegion bs r) (nb.val.map absWord) 0) / 8 + 1 := by
    rw [e4, e3, e2, e1]; rfl
  have hmx := usize_max_ge
  have hnm : n.val ≤ Std.Usize.max := by omega
  have hi4v : i4.val = n.val := by
    simp only [lift] at hi4
    rw [← Result.ok_injective hi4]
    exact ConRon.Refine.ExprOps.u64_cast_usize_val hnm
  have hstv : StampsRel stamps (Array.replicate n.val 0) := by
    sorry -- T143-STUB
  obtain ⟨⟨o2, s2⟩, hq2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o2 with
  | none => cases (Prod.mk.inj (Result.ok_injective h)).1
  | some o3 =>
  obtain ⟨outs, hU, hO⟩ := uses_of_ok hfit hstv hEV hq2
  peel h as nb1, hnb1
  have enb1 := uses_names_val hO hnb1
  peel h as lz, hlz
  have elz := load_at_loop_val hEV hlz
  obtain ⟨⟨r3, ar2⟩, hq3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hM := run_marked_refines (pk := pk) (pers := pers) (st := withStore st ar1) (lst := lst1)
    (names := nb1) (exprs := lz) hfit hrel1 hinv1 r3 ar2 hq3
  cases r3 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok x =>
  obtain ⟨nm, ms, d⟩ := x
  obtain ⟨⟨nm', ms', t⟩, lst3, hx3, ⟨hnmv, hmsv, hd⟩, hrel3, hinv3⟩ := hM
  obtain ⟨⟨r4, ar3⟩, hq4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r4 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok u =>
  obtain ⟨u', lst4, hx4, -, hrel4, hinv4⟩ := load_imports_ok (pk := pk) hfit hd hskR hf hrel3 hinv3 _ _ hq4
  obtain ⟨⟨r5, ar4⟩, hq5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r5 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok cs =>
  obtain ⟨cs', lst5, hx5, hcs, hrel5, hinv5⟩ :=
    lazy_entries_ok (pk := pk) (i := i) hfit hd hO hEV hrel4 hinv4 _ _ hq5
  peel h as values, hvalues
  have evals := value_roots_val (bs := bs) hEV hvalues
  peel h as i5, hi5
  peel h as seen, hseen
  peel h as i6, hi6
  peel h as fr, hfr
  obtain ⟨⟨seen1, fr1, st1⟩, hq6, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have efw := frontier_walk_eq hfit hq6
  peel h as b0, hb0
  peel h as frontier, hfront
  have efo := frontier_of_rel hd hb0 hfront
  peel h as n1, hn1
  obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  cases h1
  have hvr' : f'.viewRegion .private = some (absRegion bs r, absWord a0) := hvr
  refine ⟨⟨absNIdx m, cs'.toArray, frontierOf (absM ms) (absM fr1) t nm.val 0 {}⟩, lst5, ?_,
    ⟨by rw [nidx_dup2_ok hn1], by simpa using hcs, ?_⟩, hrel5, hinv5⟩
  · rw [loadAt]
    simp only [hvr']
    rw [StateT.run_bind, hx1]
    simp only [hsk']
    -- the twin's imports' check, out of its `Option` wrapper
    have hli : (loadImports (absPins pk) (absRegion bs r) t sk' f').run lst3 = .ok (true, lst4) := by
      rw [StateT.run_bind] at hx4
      cases hl : (loadImports (absPins pk) (absRegion bs r) t sk' f').run lst3 with
      | error e => rw [hl] at hx4; cases hx4
      | ok p =>
        obtain ⟨bb, l⟩ := p
        rw [hl] at hx4
        cases bb with
        | true => cases hx4; rfl
        | false => cases hx4
    rw [hnmv, hmsv] at efo
    rw [hnv] at hU
    rw [enb1, hnb, elz] at hx3
    have hi5v : i5.val = n.val := by
      simp only [lift] at hi5
      rw [← Result.ok_injective hi5]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val hnm
    have hi6v : i6.val = n.val := by
      simp only [lift] at hi6
      rw [← Result.ok_injective hi6]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val hnm
    rw [zeros_eq hseen, zeros_eq hfr, hi5v, hi6v, evals, hnv] at efw
    simp only [ConRon.Refine2.except_ok_bind, ↓reduceIte, StateT.run_bind, StateT.run_pure, pure_bind,
      hx2, hU, hx3, hli, hx5,
      hmsv, efw]
    rw [hnmv]
    rfl
  · exact efo

/-- **`load_view`'s accept is `loadView`'s.** -/
theorem load_view_refines {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {i : Std.U64} {m : arena.handle.NIdx}
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles}
    (hf : ModFilesRel f f') :
    AS pers LoadedRel st lst (load_view pk pers st.store i m f)
      (loadView (absPins pk) i.val (absNIdx m) f') := by
  intro hrel hinv a s' h
  rw [load_view] at h
  obtain ⟨⟨r, ar1⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Ok l =>
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := load_at_ok hf hrel hinv _ _ hq
    refine ⟨b, lst1, ?_, hR, hrel1, hinv1⟩
    rw [loadView, StateT.run_bind, hx]
    rfl
  | Err e =>
    cases e with
    | Bad =>
      obtain ⟨⟨ce, ar2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases (Prod.mk.inj (Result.ok_injective h)).1
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1

end ConRon.Refine2.Frontend.Olean
