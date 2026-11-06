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
  usesOf usesGo usesRoots frontierWalk frontierOf importsPre)
open ConLeche.Frontend.Olean (usesNames lazyRoots maxLoc closureFuel moduleSkel refBase)

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

/-! ## What each constant mentions: the walk -/

theorem stamps_len {stamps : alloc.vec.Vec Std.U64} {ts : Array Nat} (hs : StampsRel stamps ts) :
    stamps.val.length = ts.size := by
  have := congrArg List.length hs
  simpa using this

theorem stamps_get {stamps : alloc.vec.Vec Std.U64} {ts : Array Nat} (hs : StampsRel stamps ts)
    {k : Nat} (hk : k < stamps.val.length) : ts[k]! = (stamps.val[k]'hk).val := by
  have hk' : k < ts.size := by rw [← stamps_len hs]; exact hk
  rw [getElem!_pos ts k hk']
  have e : ts[k]? = (stamps.val.map (·.val))[k]? := by rw [← Array.getElem?_toList, ← hs]
  rw [Array.getElem?_eq_getElem hk', List.getElem?_map, List.getElem?_eq_getElem hk] at e
  exact Option.some.inj e

/-- `stamp_at` is `stamps[s]!`. -/
theorem stamp_at_eq {stamps : alloc.vec.Vec Std.U64} {ts : Array Nat} (hs : StampsRel stamps ts)
    {s i : Std.U64} (h : stamp_at stamps s = ok i) : i.val = ts[s.val]! := by
  rw [stamp_at] at h
  simp only [lift, bind_ok] at h
  have hl := stamps_len hs
  by_cases hlt : s.val < stamps.val.length
  · have hc : s < UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len stamps) := by
      show s.val < (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len stamps)).val
      rw [cast_u64_usize, vec_len_val]; exact hlt
    rw [ite_eq_left hc] at h
    obtain ⟨hl2, rfl⟩ := vec_index_eq h
    have e : (UScalar.cast UScalarTy.Usize s).val = s.val :=
      ConRon.Refine.ExprOps.u64_cast_usize_val (by scalar_tac)
    rw [stamps_get hs hlt]
    simp only [e]
  · have hc : ¬ s < UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len stamps) := by
      show ¬ s.val < (UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len stamps)).val
      rw [cast_u64_usize, vec_len_val]; exact hlt
    rw [ite_eq_right hc] at h
    cases Result.ok_injective h
    rw [getElem!_neg ts s.val (by omega)]
    rfl

/-- The stamp's write is `set!`. -/
theorem stamps_set_rel {stamps : alloc.vec.Vec Std.U64} {ts : Array Nat} (hs : StampsRel stamps ts)
    {s stamp : Std.U64} {i2 : Std.U64} (hi2 : i2.val = stamps.val.length) {stamps1}
    (h : (if s < i2 then do
        let (_, back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Std.U64) stamps
          (UScalar.cast UScalarTy.Usize s)
        ok (back stamp)
      else ok stamps) = ok stamps1) :
    StampsRel stamps1 (ts.set! s.val stamp.val) := by
  have hl := stamps_len hs
  rw [Array.set!_eq_setIfInBounds]
  show stamps1.val.map (·.val) = (ts.setIfInBounds s.val stamp.val).toList
  rw [Array.toList_setIfInBounds, ← hs]
  by_cases hlt : s < i2
  · rw [ite_eq_left hlt] at h
    peel h as p, hp
    obtain ⟨y, back⟩ := p
    obtain ⟨hl2, -, rfl⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hp
    have h' : ok (stamps.set (UScalar.cast UScalarTy.Usize s) stamp) = ok stamps1 := h
    cases Result.ok_injective h'
    have e : (UScalar.cast UScalarTy.Usize s).val = s.val :=
      ConRon.Refine.ExprOps.u64_cast_usize_val (by scalar_tac)
    simp only [alloc.vec.Vec.set, e]
    have e0 : ∀ (l : List Std.U64) (hl), (alloc.vec.Vec.from l hl).val = l := fun l hl => Slice.from_val _ _
    rw [e0, List.map_set]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have : stamps.val.length ≤ s.val := by
      have : ¬ s.val < i2.val := hlt
      omega
    rw [List.set_eq_of_length_le (by simpa using this)]

/-- `t.val ≠ K.val` from `t.val ≠ k`, `K` the literal `k#u64`. -/
local macro "rfl_or_exact" : tactic => `(tactic| first | (show _ ≠ (_ : Nat); assumption) | omega)

theorem u64_val_0 : (0#u64 : Std.U64).val = 0 := rfl
theorem u64_val_1 : (1#u64 : Std.U64).val = 1 := rfl
theorem u64_val_2 : (2#u64 : Std.U64).val = 2 := rfl
theorem u64_val_3 : (3#u64 : Std.U64).val = 3 := rfl

/-- The dispatch's answer, by components. -/
theorem triple_ok {α β γ : Type} {a a' : α} {b b' : β} {c c' : γ}
    (h : (ok (a, b, c) : Result (α × β × γ)) = ok (a', b', c')) : a = a' ∧ b = b' ∧ c = c' := by
  cases Result.ok_injective h
  exact ⟨rfl, rfl, rfl⟩

/-- A pushed kid against the twin's: both `none`, or both a stack. -/
def KidRel (q : Option Std.Usize × alloc.vec.Vec Std.U64) (o : Option (List Nat)) : Prop :=
  (q.1 = none ∧ o = none) ∨ ∃ sp l, q.1 = some sp ∧ o = some l ∧ StackRel (·.val) q.2 sp l

/-- `push_kid` is `pushKid`. -/
theorem push_kid_rel {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g i : Std.U64}
    {stack : alloc.vec.Vec Std.U64} {sp : Option Std.Usize} {o : Option (List Nat)}
    (hin : KidRel (sp, stack) o) {q} (h : push_kid bs r g i stack sp = ok q) :
    KidRel q (ConRon.Arena.Frontend.Olean.pushKid (absRegion bs r) g.val i.val o) := by
  rw [frontend.olean.lazy.push_kid.eq_def] at h
  rcases hin with ⟨h1, rfl⟩ | ⟨sp1, l, h1, rfl, hs⟩
  · simp only at h1
    subst h1
    cases Result.ok_injective h
    exact Or.inl ⟨rfl, rfl⟩
  · simp only at h1
    subst h1
    simp only at h
    peel h as v, hv
    peel h as oc, hoc
    have ev := region_fld_eq bs (r := r) hv
    have eo := region_down_eq bs hoc
    simp only [ConRon.Arena.Frontend.Olean.pushKid]
    rw [← ev, ← eo]
    cases oc with
    | none =>
      cases Result.ok_injective h
      exact Or.inl ⟨rfl, rfl⟩
    | some c =>
      obtain ⟨⟨i2, st1⟩, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      rw [push_at] at hp
      peel hp as st2, hst2
      peel hp as i3, hi3
      cases Result.ok_injective hp
      exact Or.inr ⟨_, _, rfl, rfl, hs.push hst2 hi3⟩

/-- **`uses_go`'s loop is `usesGo`**, fuel for fuel, where the Rust's walk finishes. -/
theorem uses_go_loop_ok {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {stamp : Std.U64} :
    ∀ (n : Nat) (fuel : Std.U64) (stamps : alloc.vec.Vec Std.U64) (ts : Array Nat)
      (stack : alloc.vec.Vec Std.U64) (sp : Std.Usize) (l : List Nat) (out : alloc.vec.Vec Std.U64)
      (out' : Array UInt64) {stamps' stack' out''}, fuel.val = n → StampsRel stamps ts →
      StackRel (·.val) stack sp l → OutRel out out' →
      frontend.olean.lazy.uses_go_loop bs r stamps stamp stack out sp fuel = ok (true, stamps', stack', out'') →
      ∃ ts' o', usesGo (absRegion bs r) ts stamp.val out' n l = some (ts', o') ∧
        StampsRel stamps' ts' ∧ OutRel out'' o' := by
  intro n
  induction n with
  | zero =>
    intro fuel stamps ts stack sp l out out' stamps' stack' out'' hf hs hst ho h
    rw [frontend.olean.lazy.uses_go_loop] at h
    by_cases hp : sp > 0#usize
    · rw [ite_eq_left hp] at h
      have hz : fuel = 0#u64 := UScalar.eq_of_val_eq (by rw [hf]; rfl)
      rw [ite_eq_left hz] at h
      cases (Prod.mk.inj (Result.ok_injective h)).1
    · rw [ite_eq_right hp] at h
      obtain ⟨-, h2⟩ := Prod.mk.inj (Result.ok_injective h)
      obtain ⟨rfl, h3⟩ := Prod.mk.inj h2
      obtain ⟨-, rfl⟩ := Prod.mk.inj h3
      rw [hst.nil_of_zero hp]
      exact ⟨ts, out', by rw [usesGo], hs, ho⟩
  | succ n ih =>
    intro fuel stamps ts stack sp l out out' stamps' stack' out'' hf hs hst ho h
    rw [frontend.olean.lazy.uses_go_loop] at h
    by_cases hp : sp > 0#usize
    · rw [ite_eq_left hp] at h
      have hz : ¬ fuel = 0#u64 := fun he => by rw [he] at hf; simp at hf
      rw [ite_eq_right hz] at h
      peel h as fuel1, hfuel1
      have ef := fuel_pred hfuel1
      peel h as sp1, hsp1
      obtain ⟨hi, l', rfl, hs1⟩ := hst.pop hp hsp1
      peel h as g, hg
      obtain ⟨_hlt, rfl⟩ := vec_index_eq hg
      peel h as s, hs'
      have es : s.val = stack.val[sp1.val].val / 8 := by
        rw [ConRon.Refine.HashMap.uscalar_div_eq hs']; rfl
      peel h as i, hi'
      have ei := stamp_at_eq hs hi'
      have hf1 : fuel1.val = n := by rw [ef, hf]; rfl
      rw [usesGo]
      simp only
      rw [← es, ← ei]
      by_cases hne : (i != stamp) = true
      · rw [ite_eq_left hne] at h
        have hne' : ¬ (i.val == stamp.val) = true := by
          intro he; simp only [bne_iff_ne, ne_eq] at hne
          exact hne (UScalar.eq_of_val_eq (by simpa using he))
        rw [ite_eq_right hne']
        simp only [lift, bind_ok] at h
        obtain ⟨stamps1, hst1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hS1 := stamps_set_rel hs (by rw [cast_u64_usize, vec_len_val]) hst1
        peel h as b, hb
        have eb := region_fits_eq bs hb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases (Prod.mk.inj (Result.ok_injective h)).1
        | true =>
          simp only [↓reduceIte] at h
          rw [← eb]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          peel h as t, ht
          peel h as nn, hn
          have et := region_tag_eq bs (r := r) ht
          have en := region_nobjs_eq bs (r := r) hn
          rw [← et, ← en]
          obtain ⟨⟨stack1, out1, next⟩, hD, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases next with
          | none => cases (Prod.mk.inj (Result.ok_injective h)).1
          | some s2 =>
          have fin : ∀ L O, StackRel (·.val) stack1 s2 L → OutRel out1 O →
              ∃ ts' o', usesGo (absRegion bs r) (ts.set! s.val stamp.val) stamp.val O n L = some (ts', o') ∧
                StampsRel stamps' ts' ∧ OutRel out'' o' :=
            fun L O hL hO => ih fuel1 stamps1 _ stack1 s2 L out1 O hf1 hS1 hL hO h
          have hK0 : KidRel (some sp1, stack) (some l') := Or.inr ⟨sp1, l', rfl, rfl, hs1⟩
          have tne : ∀ {K : Std.U64}, t.val ≠ K.val → t ≠ K := fun hk he => hk (by rw [he])
          have nne : ∀ {K : Std.U64}, nn.val ≠ K.val → nn ≠ K := fun hk he => hk (by rw [he])
          have none_out : ∀ {st : alloc.vec.Vec Std.U64} {o : alloc.vec.Vec Std.U64},
              (ok (st, o, none) : Result _) = ok (stack1, out1, some s2) → False := fun hD => by
            cases (triple_ok hD).2.2
          -- one kid onto the stack, then the walk on
          have kid1 : ∀ {i : Std.U64} {st2 : alloc.vec.Vec Std.U64},
              push_kid bs r stack.val[sp1.val] i stack (some sp1) = ok (some s2, st2) → st2 = stack1 →
              ∃ L, ConRon.Arena.Frontend.Olean.pushKid (absRegion bs r) stack.val[sp1.val].val i.val (some l') = some L ∧
                StackRel (·.val) stack1 s2 L := by
            intro i st2 hk e
            subst e
            rcases push_kid_rel hK0 hk with ⟨h1, -⟩ | ⟨sp, L, hsp, hL, hSt⟩
            · cases h1
            · cases hsp
              exact ⟨L, hL, hSt⟩
          rcases (by omega : t.val = 0 ∨ t.val = 3 ∨ t.val = 4 ∨ t.val = 5 ∨ t.val = 6 ∨ t.val = 7 ∨
              t.val = 8 ∨ t.val = 9 ∨ t.val = 10 ∨ t.val = 11 ∨
              (t.val ≠ 0 ∧ t.val ≠ 3 ∧ t.val ≠ 4 ∧ t.val ≠ 5 ∧ t.val ≠ 6 ∧ t.val ≠ 7 ∧ t.val ≠ 8 ∧
                t.val ≠ 9 ∧ t.val ≠ 10 ∧ t.val ≠ 11)) with
            ht0 | ht0 | ht0 | ht0 | ht0 | ht0 | ht0 | ht0 | ht0 | ht0 | hother
          -- `0, 1` and `3, 1`: nothing below
          · rw [ht0]
            obtain rfl : t = 0#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 1
            · rw [hn]
              obtain rfl : nn = 1#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              exact fin l' out' hs1 ho
            · exfalso
              have hn' := nne (K := 1#u64) (by rw [u64_val_1]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          · rw [ht0]
            obtain rfl : t = 3#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 1
            · rw [hn]
              obtain rfl : nn = 1#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              exact fin l' out' hs1 ho
            · exfalso
              have hn' := nne (K := 1#u64) (by rw [u64_val_1]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- `4, 2`: the constant's name
          · rw [ht0]
            obtain rfl : t = 4#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 2
            · rw [hn]
              obtain rfl : nn = 2#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              peel hD as i3, hi3
              peel hD as out2, hout2
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              refine fin l' _ hs1 ?_
              show List.map absWord _ = _
              rw [ConRon.Refine.vec_push_val hout2, List.map_append, ho, List.map_cons, List.map_nil,
                region_fld_eq bs hi3, u64_val_0, Array.toList_push]
            · exfalso
              have hn' := nne (K := 2#u64) (by rw [u64_val_2]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- `5, 2`: two kids
          · rw [ht0]
            obtain rfl : t = 5#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 2
            · rw [hn]
              obtain rfl : nn = 2#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨⟨a, st2⟩, hk1, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨⟨nx, st3⟩, hk2, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              have K1 := push_kid_rel hK0 hk1
              have K2 := push_kid_rel K1 hk2
              rw [u64_val_1, u64_val_0] at K2
              rcases K2 with ⟨h1, -⟩ | ⟨sp, L, hsp, hL, hSt⟩
              · cases h1
              · cases hsp
                rw [hL]
                exact fin L out' hSt ho
            · exfalso
              have hn' := nne (K := 2#u64) (by rw [u64_val_2]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- `6, 3` and `7, 3`: two kids
          · rw [ht0]
            obtain rfl : t = 6#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 3
            · rw [hn]
              obtain rfl : nn = 3#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨⟨a, st2⟩, hk1, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨⟨nx, st3⟩, hk2, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              have K1 := push_kid_rel hK0 hk1
              have K2 := push_kid_rel K1 hk2
              rw [u64_val_2, u64_val_1] at K2
              rcases K2 with ⟨h1, -⟩ | ⟨sp, L, hsp, hL, hSt⟩
              · cases h1
              · cases hsp
                rw [hL]
                exact fin L out' hSt ho
            · exfalso
              have hn' := nne (K := 3#u64) (by rw [u64_val_3]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          · rw [ht0]
            obtain rfl : t = 7#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 3
            · rw [hn]
              obtain rfl : nn = 3#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨⟨a, st2⟩, hk1, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨⟨nx, st3⟩, hk2, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              have K1 := push_kid_rel hK0 hk1
              have K2 := push_kid_rel K1 hk2
              rw [u64_val_2, u64_val_1] at K2
              rcases K2 with ⟨h1, -⟩ | ⟨sp, L, hsp, hL, hSt⟩
              · cases h1
              · cases hsp
                rw [hL]
                exact fin L out' hSt ho
            · exfalso
              have hn' := nne (K := 3#u64) (by rw [u64_val_3]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- `8, 4`: three kids
          · rw [ht0]
            obtain rfl : t = 8#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 4
            · rw [hn]
              obtain rfl : nn = 4#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨⟨a, st2⟩, hk1, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨⟨b1, st3⟩, hk2, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨⟨nx, st4⟩, hk3, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              have K1 := push_kid_rel hK0 hk1
              have K2 := push_kid_rel K1 hk2
              have K3 := push_kid_rel K2 hk3
              rw [u64_val_3, u64_val_2, u64_val_1] at K3
              rcases K3 with ⟨h1, -⟩ | ⟨sp, L, hsp, hL, hSt⟩
              · cases h1
              · cases hsp
                rw [hL]
                exact fin L out' hSt ho
            · exfalso
              have hn' := nne (K := 4#u64) (by rfl_or_exact)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- `9, 1`: a literal
          · rw [ht0]
            obtain rfl : t = 9#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 1
            · rw [hn]
              obtain rfl : nn = 1#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              peel hD as i3, hi3
              peel hD as oc, hoc
              obtain ⟨⟨v1, o1⟩, hm, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              have ef : (absRegion bs r).fld stack.val[sp1.val].val 0 = absWord i3 := by
                rw [region_fld_eq bs hi3, u64_val_0]
              rw [ef, ← region_down_eq bs hoc]
              cases oc with
              | none =>
                cases Result.ok_injective hm
                cases hc
              | some c =>
                simp only [locOf, Option.map_some]
                peel hm as b1, hb1
                have e1 := region_is_ctor_eq bs hb1
                rw [u64_val_0, u64_val_1] at e1
                rw [← e1]
                cases b1 with
                | true =>
                  simp only [↓reduceIte] at hm ⊢
                  peel hm as out2, hout2
                  cases Result.ok_injective hm
                  cases hc
                  refine fin l' _ hs1 ?_
                  show List.map absWord _ = _
                  rw [ConRon.Refine.vec_push_val hout2, List.map_append, ho]
                  simp only [List.map_cons, List.map_nil, Array.toList_push]
                  unfold frontend.olean.lazy.USES_NAT; rfl
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
                  peel hm as b2, hb2
                  have e2 := region_is_ctor_eq bs hb2
                  rw [u64_val_1] at e2
                  rw [← e2]
                  cases b2 with
                  | true =>
                    simp only [↓reduceIte] at hm ⊢
                    peel hm as out2, hout2
                    cases Result.ok_injective hm
                    cases hc
                    refine fin l' _ hs1 ?_
                    show List.map absWord _ = _
                    rw [ConRon.Refine.vec_push_val hout2, List.map_append, ho]
                    simp only [List.map_cons, List.map_nil, Array.toList_push]
                    unfold frontend.olean.lazy.USES_STR; rfl
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at hm
                    cases Result.ok_injective hm
                    cases hc
            · exfalso
              have hn' := nne (K := 1#u64) (by rw [u64_val_1]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- `10, 2`: one kid
          · rw [ht0]
            obtain rfl : t = 10#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 2
            · rw [hn]
              obtain rfl : nn = 2#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨⟨st2, nx⟩, hk1, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨⟨nx', st2'⟩, hk1', he⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk1
              cases Result.ok_injective he
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              obtain ⟨L, hL, hSt⟩ := kid1 hk1' rfl
              rw [u64_val_1] at hL
              rw [hL]
              exact fin L out' hSt ho
            · exfalso
              have hn' := nne (K := 2#u64) (by rw [u64_val_2]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- `11, 3`: one kid
          · rw [ht0]
            obtain rfl : t = 11#u64 := UScalar.eq_of_val_eq (ht0.trans rfl)
            by_cases hn : nn.val = 3
            · rw [hn]
              obtain rfl : nn = 3#u64 := UScalar.eq_of_val_eq (hn.trans rfl)
              simp (config := {decide := true}) only [↓reduceIte] at hD
              obtain ⟨⟨st2, nx⟩, hk1, hD⟩ := ConRon.Refine.bind_eq_ok_iff.mp hD
              obtain ⟨⟨nx', st2'⟩, hk1', he⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk1
              cases Result.ok_injective he
              obtain ⟨rfl, rfl, hc⟩ := triple_ok hD
              cases hc
              obtain ⟨L, hL, hSt⟩ := kid1 hk1' rfl
              rw [u64_val_2] at hL
              rw [hL]
              exact fin L out' hSt ho
            · exfalso
              have hn' := nne (K := 3#u64) (by rw [u64_val_3]; exact hn)
              simp (config := {decide := true}) only [↓reduceIte, hn', bind_ok] at hD
              exact none_out hD
          -- no expression object
          · exfalso
            obtain ⟨n0, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hother
            have t0 := tne (K := 0#u64) (by rw [u64_val_0]; exact n0)
            have t3 := tne (K := 3#u64) (by rw [u64_val_3]; exact n3)
            have t4 := tne (K := 4#u64) (by rfl_or_exact)
            have t5 := tne (K := 5#u64) (by rfl_or_exact)
            have t6 := tne (K := 6#u64) (by rfl_or_exact)
            have t7 := tne (K := 7#u64) (by rfl_or_exact)
            have t8 := tne (K := 8#u64) (by rfl_or_exact)
            have t9 := tne (K := 9#u64) (by rfl_or_exact)
            have t10 := tne (K := 10#u64) (by rfl_or_exact)
            have t11 := tne (K := 11#u64) (by rfl_or_exact)
            simp only [↓reduceIte, t0, t3, t4, t5, t6, t7, t8, t9, t10, t11, bind_ok] at hD
            exact none_out hD
      · simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hne
        subst hne
        rw [ite_eq_right (by simp)] at h
        rw [ite_eq_left (by simp)]
        exact ih fuel1 stamps ts stack sp1 l' out out' hf1 hs hs1 ho h
    · rw [ite_eq_right hp] at h
      obtain ⟨-, h2⟩ := Prod.mk.inj (Result.ok_injective h)
      obtain ⟨rfl, h3⟩ := Prod.mk.inj h2
      obtain ⟨-, rfl⟩ := Prod.mk.inj h3
      rw [hst.nil_of_zero hp]
      exact ⟨ts, out', by rw [usesGo], hs, ho⟩

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
        · rw [ite_eq_left h2] at hs1; cases Result.ok_injective hs1; simp [g, h2]
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
    · simp [g, h0]
    · by_cases h2 : y = frontend.olean.lazy.USES_STR
      · simp [g, h2]
      · simp [g, h0, h2]

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

/-- The memo's `PtrRead` maps an import as the twin's pure `nameOf`, the state untouched. -/
theorem import_mapM_ds {pk : ConRon.Arena.Frontend.Olean.OleanPins} {R : ConLeche.Frontend.Olean.Region}
    {t : TDS} (x : ConLeche.Frontend.Olean.ImportF UInt64) (lst : AState) :
    StateT.run (ConLeche.Frontend.Olean.ImportF.mapM (m := OptionT AM)
      (fun v => OptionT.mk ((ConRon.Arena.Frontend.Olean.DS.read pk R t).rdName v)) x) lst =
      .ok (x.mapM (ConRon.Arena.Frontend.Olean.DS.nameOf pk R t), lst) := by
  simp only [ConLeche.Frontend.Olean.ImportF.mapM, ConRon.Arena.Frontend.Olean.DS.read]
  cases ConRon.Arena.Frontend.Olean.DS.nameOf pk R t x.module <;> rfl

/-- `loadImports`' maps over the skeleton's imports. -/
theorem mapM_imports_map {pk : ConRon.Arena.Frontend.Olean.OleanPins} {R : ConLeche.Frontend.Olean.Region}
    {t : TDS} (l : List (frontend.olean.spec.ImportF Std.U64)) :
    (l.map (absImportF absWord)).mapM (fun i => i.mapM (ConRon.Arena.Frontend.Olean.DS.nameOf pk R t)) =
      l.mapM (fun i => (absImportF absWord i).mapM (ConRon.Arena.Frontend.Olean.DS.nameOf pk R t)) := by
  induction l with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons, List.mapM_cons, ih]

/-- **`load_imports`' loop**: from import `i` on, each mapped by the memo, then the file's
imports against them. -/
theorem load_imports_loop_ok {pk pers st} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t)
    {v : alloc.vec.Vec (frontend.olean.spec.ImportF Std.U64)}
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f') :
    ∀ (k : Nat) (i : Std.Usize) (ar : arena.store.EStore)
      (imports : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (lst : AState) {s'},
      v.val.length - i.val = k →
      AStateRel₀ pers (withStore st ar) lst → AStateInv pers (withStore st ar) →
      load_imports_loop pk pers ar bs r d v f imports i = ok (.Ok (), s') →
      ∃ rest pre lst', (v.val.drop i.val).mapM (fun i => (absImportF absWord i).mapM
          (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t)) = some rest ∧
        (importsPre (absPins pk) f'.exported.bytes).run lst = .ok (some pre, lst') ∧
        (pre == (imports.val.map (absImportF absNIdx) ++ rest).toArray) = true ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s') := by
  intro k
  induction k with
  | zero =>
    intro i ar imports lst s' hk hrel hinv h
    rw [load_imports_loop] at h
    have hi : ¬ i < alloc.vec.Vec.len v := by
      have : ¬ i.val < v.val.length := by omega
      exact this
    rw [ite_eq_right hi] at h
    obtain ⟨⟨r1, ar1⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok pre =>
      peel h as b, hb
      have eb := imports_beq_eq hb
      cases b with
      | false => cases (Prod.mk.inj (Result.ok_injective h)).1
      | true =>
        simp only [ite_true] at h
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
        obtain ⟨pre', lst', hx, hpre, hrel1, hinv1⟩ :=
          (imports_pre_ok (pk := pk) (pers := pers) hf (withStore st ar) lst).ar hrel hinv _ _ hq
        refine ⟨[], pre', lst', by rw [List.drop_of_length_le (by omega)]; rfl, ?_, ?_, hrel1, hinv1⟩
        · rw [hf.exported]; exact hx
        · simp only [EqA] at hpre
          subst hpre
          rw [List.append_nil]
          exact eb.symm
  | succ k ih =>
    intro i ar imports lst s' hk hrel hinv h
    rw [load_imports_loop] at h
    have hlt : i.val < v.val.length := by omega
    have hi : i < alloc.vec.Vec.len v := hlt
    rw [ite_eq_left hi] at h
    peel h as x, hx
    obtain ⟨_hl, rfl⟩ := vec_index_eq hx
    obtain ⟨⟨r1, ar1⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok y =>
      peel h as imports1, himp
      peel h as i2, hi2
      obtain ⟨b, lst1, hx1, hb, hrel1, hinv1⟩ :=
        (import_map_refines (ds_ptr_rel (pk := pk) (pers := pers) hr hd) (withStore st ar) lst).ar
          hrel hinv _ _ hq
      rw [import_mapM_ds] at hx1
      obtain ⟨hm, rfl⟩ := Prod.mk.inj (Except.ok.inj hx1)
      have ei := ConRon.Refine.HashMap.uscalar_add_eq hi2
      obtain ⟨rest, pre, lst', hrest, hpre, hbeq, hrel2, hinv2⟩ :=
        ih i2 ar1 imports1 _ (by rw [ei]; simp; omega) hrel1 hinv1 h
      refine ⟨absImportF absNIdx y :: rest, pre, lst', ?_, hpre, ?_, hrel2, hinv2⟩
      · rw [List.drop_eq_getElem_cons hlt, List.mapM_cons, hm, ← hb]
        have e2 : i2.val = i.val + 1 := by rw [ei]; rfl
        rw [← e2, hrest]
        rfl
      · rw [ConRon.Refine.vec_push_val himp] at hbeq
        simpa using hbeq

/-- **`load_imports`' accept is `loadImports`' `true`.** -/
theorem load_imports_ok {pk pers st lst} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t)
    {sk : frontend.olean.spec.ModSkel} {sk' : ConLeche.Frontend.Olean.ModSkel} (hsk : ModSkelRel sk sk')
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f') :
    AR pers (fun (_ : Unit) (b : Unit) => b = ()) st lst (load_imports pk pers st.store bs r d sk f)
      (do if ← loadImports (absPins pk) (absRegion bs r) t sk' f' then pure (some ()) else pure none) := by
  intro hrel hinv a s' h
  rw [load_imports] at h
  have hnew : (alloc.vec.Vec.with_capacity (frontend.olean.spec.ImportF arena.handle.NIdx)
      (alloc.vec.Vec.len sk.imports)).val = [] := rfl
  obtain ⟨rest, pre, lst', hrest, hpre, hbeq, hrel1, hinv1⟩ :=
    load_imports_loop_ok hr hd hf _ 0#usize st.store _ lst rfl hrel hinv h
  rw [hnew, List.map_nil, List.nil_append] at hbeq
  refine ⟨(), lst', ?_, rfl, hrel1, hinv1⟩
  rw [loadImports, ← hsk.imports, mapM_imports_map]
  rw [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hrest
  rw [hrest]
  dsimp only
  have hin : StateT.run ((do
      let o ← importsPre (absPins pk) f'.exported.bytes
      match o with
      | some pre => pure (pre == rest.toArray)
      | none => pure false) : AM Bool) lst = Except.ok (true, lst') := by
    rw [am_bind_ok hpre, ← hbeq]; rfl
  exact (am_bind_ok (g := fun b => if b = true then pure (some ()) else pure none) hin).trans rfl
/-! ## The constants -/

/-- A pure read's `some`. -/
theorem pure_run_some {α : Type} {x : Option α} {b : α} {lst lst' : AState}
    (h : StateT.run (pure x : AM (Option α)) lst = .ok (some b, lst')) : x = some b ∧ lst' = lst := by
  cases x <;> simp [StateT.run, pure, StateT.pure, Except.pure] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- The memo's `PtrRead` maps names as the twin's pure `nameOf`, the state untouched. -/
theorem names_mapM_ds {pk : ConRon.Arena.Frontend.Olean.OleanPins} {R : ConLeche.Frontend.Olean.Region}
    {t : TDS} (l : List UInt64) (lst : AState) :
    StateT.run (l.mapM (m := OptionT AM)
      (fun v => OptionT.mk ((ConRon.Arena.Frontend.Olean.DS.read pk R t).rdName v))) lst =
      .ok (l.mapM (ConRon.Arena.Frontend.Olean.DS.nameOf pk R t), lst) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mapM_cons, ConRon.Arena.Frontend.Olean.DS.read]
    cases hx : ConRon.Arena.Frontend.Olean.DS.nameOf pk R t x with
    | none => rfl
    | some n =>
      show StateT.run (OptionT.run _) lst = _
      simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, bind_pure_comp, pure_bind, Option.elim,
        OptionT.run_map]
      simp only [ConRon.Arena.Frontend.Olean.DS.read] at ih
      rw [StateT.run_map]
      erw [ih]
      cases List.mapM (ConRon.Arena.Frontend.Olean.DS.nameOf pk R t) l <;> rfl

/-- **`lazy_entry`'s accept is `lazyEntry`'s.** -/
theorem lazy_entry_ok {pk pers st lst} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t) {i : Std.U64}
    {s : frontend.olean.spec.CEntryF Std.U64 Std.U64} {s' : ConLeche.Frontend.Olean.CEntryF UInt64 UInt64}
    (hs : EV s s') :
    AR pers (EntryRel absNIdx absEIdx ValRel) st lst (lazy_entry pk pers st.store bs r d i s)
      (ConRon.Arena.Frontend.Olean.lazyEntry (absPins pk) (absRegion bs r) t i.val s') := by
  have hp := ds_ptr_rel (pk := pk) (pers := pers) hr hd
  have hmap := fun st lst => (c_entry_map_refines hp hs st lst).ar
  obtain ⟨n, lp, ty, k⟩ := s
  obtain ⟨n', lp', ty', k'⟩ := s'
  obtain ⟨hn, hlp, hty, hk⟩ := hs
  cases k <;> cases k' <;> try exact hk.elim
  case Thm.thm w all w' all' =>
    obtain ⟨hw, hall⟩ := hk
    dsimp only at hn hty
    intro hrel hinv a s2 h
    simp only [lazy_entry] at h
    peel h as i1, hi1
    have eb := ref_base_val hi1
    by_cases hi : i < i1
    · rw [ite_eq_left hi] at h
      have hiv : i.val < refBase := by rw [← eb]; exact hi
      peel h as o, ho
      have eo := region_loc_eq bs ho
      cases o with
      | none => cases (Prod.mk.inj (Result.ok_injective h)).1
      | some g =>
        simp only at h
        by_cases hg : g < i1
        · rw [ite_eq_left hg] at h
          have hgv : g.val < refBase := by rw [← eb]; exact hg
          obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases r1 with
          | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
          | Ok nn =>
          obtain ⟨b1, lst1, hx1, hb1, hrel1, hinv1⟩ := (hp.nm st lst n).ar hrel hinv _ _ h1
          obtain ⟨hnm, rfl⟩ := pure_run_some hx1
          obtain ⟨⟨r2, ar2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases r2 with
          | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
          | Ok x =>
          obtain ⟨b2, lst2, hx2, hb2, hrel2, hinv2⟩ :=
            (names_map_refines hp hlp (withStore st ar1) _).ar hrel1 hinv1 _ _ h2
          rw [names_mapM_ds] at hx2
          obtain ⟨hlps, rfl⟩ := Prod.mk.inj (Except.ok.inj hx2)
          obtain ⟨⟨r3, ar3⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases r3 with
          | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
          | Ok tt =>
          obtain ⟨b3, lst3, hx3, hb3, hrel3, hinv3⟩ := (hp.ex (withStore st ar2) _ ty).ar hrel2 hinv2 _ _ h3
          obtain ⟨hex, rfl⟩ := pure_run_some hx3
          obtain ⟨⟨r4, ar4⟩, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases r4 with
          | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
          | Ok x1 =>
          obtain ⟨b4, lst4, hx4, hb4, hrel4, hinv4⟩ :=
            (names_map_refines hp hall (withStore st ar3) _).ar hrel3 hinv3 _ _ h4
          rw [names_mapM_ds] at hx4
          obtain ⟨hall', rfl⟩ := Prod.mk.inj (Except.ok.inj hx4)
          obtain ⟨⟨r5, ar5⟩, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases r5 with
          | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
          | Ok vr =>
          obtain ⟨h6, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
          cases h6
          rw [value_ref] at h5
          peel h5 as j1, hj1
          peel h5 as j2, hj2
          peel h5 as j3, hj3
          have ej : j3.val = g.val * refBase + i.val := by
            rw [ConRon.Refine.HashMap.uscalar_add_eq hj3, ConRon.Refine.HashMap.uscalar_mul_eq hj2,
              ref_base_val hj1]
          have hS := intern_e_bvar_run₀ hrel4 hinv4 j3 (o := (.Ok vr, withStore st ar5))
            (by rw [arena.monad.intern_e_bvar]; erw [h5]; simp only [bind_ok]; rfl)
          obtain ⟨lst5, hx5, hrel5, hinv5⟩ := Sim₀.apply hS
          refine ⟨⟨b1, b2, b3, .thm (absEIdx vr) b4⟩, lst5, ?_, ⟨hb1.symm, hb2, hb3.symm, ⟨rfl, hb4⟩⟩,
            hrel5, hinv5⟩
          simp only [ConRon.Arena.Frontend.Olean.lazyEntry]
          rw [← hw, ← eo, ← hn, ← hty]
          simp only [locOf, Option.map_some, hiv, hgv, hnm, hlps, hex, hall', ite_true]
          have hx5' : StateT.run (ConRon.Arena.Frontend.Olean.valueRef i.val g.val) lst3 =
              Except.ok (absEIdx vr, lst5) := by
            have : absU j3 = g.val * refBase + i.val := ej
            rw [ConRon.Arena.Frontend.Olean.valueRef, ← this]
            exact hx5
          simp only [pure_bind]
          rw [am_bind_ok hx5']
          rfl
        · rw [ite_eq_right hg] at h; cases (Prod.mk.inj (Result.ok_injective h)).1
    · rw [ite_eq_right hi] at h; cases (Prod.mk.inj (Result.ok_injective h)).1
  all_goals
    simp only [lazy_entry, ConRon.Arena.Frontend.Olean.lazyEntry]
    exact hmap st lst

/-! ## What a constant mentions, as names -/

/-- **The memo's `rd_name` is `nameOf`**: the store untouched, `Ok` its `some`. -/
theorem ds_rd_name_eq {pk : frontend.olean.spec.OleanPins} {pers} {bs : Slice Std.U8}
    {r : frontend.olean.region.Region} {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r)
    (hd : DSRel d t) {ar : arena.store.EStore} {v : Std.U64} {o ar'}
    (h : frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_name d pk pers ar bs r v =
      ok (o, ar')) :
    ar' = ar ∧ (match o with | .Ok n => some (absNIdx n) | .Err _ => none) =
      ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t (absWord v) := by
  rw [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_name] at h
  simp only [ConRon.Arena.Frontend.Olean.DS.nameOf]
  by_cases hv : v = 1#u64
  · rw [ite_eq_left hv] at h
    rw [ite_eq_left (word_eq_one.mpr hv)]
    peel h as n, hn
    cases nidx_dup2_ok hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hv] at h
    rw [ite_eq_right (fun he => hv (word_eq_one.mp he))]
    peel h as o1, ho
    rw [← region_loc_eq bs ho]
    cases o1 with
    | none =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨rfl, rfl⟩
    | some c =>
      simp only [lift, bind_ok] at h
      peel h as i, hi
      peel h as x, hx
      peel h as n, hn
      cases Result.ok_injective hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      refine ⟨rfl, ?_⟩
      simp only [locOf, Option.map_some]
      rw [memo_word hd.names (region_loc_fits hr ho) hi hx]

/-- What a constant's mentions read so far, as the twin's: the set seen and the names. -/
def UsesRel (q : ron.hashmap2.HashMap2 arena.handle.NIdx Bool × alloc.vec.Vec arena.handle.NIdx)
    (x : _root_.Std.HashSet NIdx × Array NIdx) : Prop :=
  SetRel arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable absNIdx q.1 x.1 ∧
    q.2.val.map absNIdx = x.2.toList

/-- `add_use` is `addUse`. -/
theorem add_use_rel {seen acc x} (hx : UsesRel (seen, acc) x) {n : arena.handle.NIdx} {q}
    (h : add_use seen acc n = ok q) :
    UsesRel q (ConRon.Arena.Frontend.Olean.addUse x (absNIdx n)) := by
  rw [add_use] at h
  peel h as b, hb
  have eb := SetRel.contains_key nidx_eq2 hx.1 hb
  simp only [ConRon.Arena.Frontend.Olean.addUse]
  cases b with
  | true =>
    cases Result.ok_injective h
    rw [ite_eq_left eb.symm]
    exact hx
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [ite_eq_right (by rw [← eb]; simp)]
    peel h as n1, hn1
    cases nidx_dup2_ok hn1
    obtain ⟨⟨old, seen1⟩, hins, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    peel h as acc1, hacc
    cases Result.ok_injective h
    refine ⟨SetRel.insert nidx_eq2 (fun a b e => absNIdx_inj e) hx.1 hins, ?_⟩
    show acc1.val.map absNIdx = _
    rw [ConRon.Refine.vec_push_val hacc, List.map_append, hx.2]
    simp

/-- The twin's step of `usesRead`. -/
def usesStep (pk : ConRon.Arena.Frontend.Olean.OleanPins) (nm : UInt64 → Option NIdx)
    (x : _root_.Std.HashSet NIdx × Array NIdx) (v : UInt64) : _root_.Std.HashSet NIdx × Array NIdx :=
  if v == ConLeche.Frontend.Olean.usesNat then ConRon.Arena.Frontend.Olean.addUse x pk.nNat
  else if v == ConLeche.Frontend.Olean.usesStr then
    ConRon.Arena.Frontend.Olean.addUse (ConRon.Arena.Frontend.Olean.addUse x pk.nCharOfNat) pk.nStringOfList
  else match nm v with
    | some n => ConRon.Arena.Frontend.Olean.addUse x n
    | none => x

theorem word_uses_nat (y : Std.U64) :
    (absWord y == ConLeche.Frontend.Olean.usesNat) = decide (y = frontend.olean.lazy.USES_NAT) := by
  rw [show ConLeche.Frontend.Olean.usesNat = absWord frontend.olean.lazy.USES_NAT by
    unfold frontend.olean.lazy.USES_NAT; rfl]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, absWord_eq_iff]

theorem word_uses_str (y : Std.U64) :
    (absWord y == ConLeche.Frontend.Olean.usesStr) = decide (y = frontend.olean.lazy.USES_STR) := by
  rw [show ConLeche.Frontend.Olean.usesStr = absWord frontend.olean.lazy.USES_STR by
    unfold frontend.olean.lazy.USES_STR; rfl]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, absWord_eq_iff]

/-- **`uses_read`'s loop is `usesRead`'s fold**, the store untouched. -/
theorem uses_read_loop_eq {pk pers} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t)
    {out : alloc.vec.Vec Std.U64} :
    ∀ (k : Nat) (i : Std.Usize) (ar : arena.store.EStore) (seen) (acc) (x) {acc' ar'},
      out.val.length - i.val = k → UsesRel (seen, acc) x →
      uses_read_loop pk pers ar bs r d out seen acc i = ok (acc', ar') →
      ar' = ar ∧ acc'.val.map absNIdx = (((out.val.drop i.val).map absWord).foldl
        (usesStep (absPins pk) (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t)) x).2.toList := by
  intro k
  induction k with
  | zero =>
    intro i ar seen acc x acc' ar' hk hx h
    rw [uses_read_loop] at h
    have hi : ¬ i < alloc.vec.Vec.len out := by
      have : ¬ i.val < out.val.length := by omega
      exact this
    rw [ite_eq_right hi] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    rw [List.drop_of_length_le (by omega)]
    exact ⟨rfl, hx.2⟩
  | succ k ih =>
    intro i ar seen acc x acc' ar' hk hx h
    rw [uses_read_loop] at h
    have hlt : i.val < out.val.length := by omega
    have hi : i < alloc.vec.Vec.len out := hlt
    rw [ite_eq_left hi] at h
    peel h as v, hv
    obtain ⟨_hl, rfl⟩ := vec_index_eq hv
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldl_cons]
    obtain ⟨⟨pk1, ar1, seen1, acc1⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    peel h as i2, hi2
    have ei := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have e2 : i2.val = i.val + 1 := by rw [ei]; rfl
    have step : pk1 = pk ∧ ar1 = ar ∧ UsesRel (seen1, acc1)
        (usesStep (absPins pk) (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t) x
          (absWord out.val[i.val])) := by
      simp only [usesStep, word_uses_nat, word_uses_str]
      by_cases h0 : out.val[i.val] = frontend.olean.lazy.USES_NAT
      · rw [ite_eq_left h0] at hq
        simp only [decide_eq_true h0, ↓reduceIte]
        obtain ⟨⟨s2, a2⟩, hu, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
        cases Result.ok_injective hq
        exact ⟨rfl, rfl, add_use_rel hx hu⟩
      · rw [ite_eq_right h0] at hq
        simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : out.val[i.val] = frontend.olean.lazy.USES_STR
        · rw [ite_eq_left h2] at hq
          simp only [decide_eq_true h2, ↓reduceIte]
          obtain ⟨⟨s2, a2⟩, hu, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
          obtain ⟨⟨s3, a3⟩, hu3, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
          cases Result.ok_injective hq
          exact ⟨rfl, rfl, add_use_rel (add_use_rel hx hu) hu3⟩
        · rw [ite_eq_right h2] at hq
          simp only [decide_eq_false h2, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨⟨r1, ar2⟩, hn, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
          obtain ⟨rfl, en⟩ := ds_rd_name_eq hr hd hn
          rw [← en]
          cases r1 with
          | Ok n =>
            obtain ⟨⟨s2, a2⟩, hu, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
            cases Result.ok_injective hq
            exact ⟨rfl, rfl, add_use_rel hx hu⟩
          | Err e =>
            obtain ⟨⟨s2, a2⟩, hu, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
            cases Result.ok_injective hu
            cases Result.ok_injective hq
            exact ⟨rfl, rfl, hx⟩
    obtain ⟨ep, ea, hx1⟩ := step
    rw [ep, ea] at h
    rw [← e2]
    exact ih i2 _ seen1 acc1 _ (by rw [e2]; omega) hx1 h

/-- **`uses_read` is `usesRead`**, the store untouched. -/
theorem uses_read_eq {pk pers} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t)
    {out : alloc.vec.Vec Std.U64} {out' : Array UInt64} (ho : OutRel out out') {ar acc' ar'}
    (h : uses_read pk pers ar bs r d out = ok (acc', ar')) :
    ar' = ar ∧ acc'.val.map absNIdx = (ConRon.Arena.Frontend.Olean.usesRead (absPins pk)
      (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t) out').toList := by
  rw [uses_read] at h
  peel h as seen, hseen
  have hs : UsesRel (seen, alloc.vec.Vec.new arena.handle.NIdx)
      ((_root_.Std.HashSet.emptyWithCapacity 64 : _root_.Std.HashSet NIdx), #[]) :=
    ⟨SetRel.with_capacity hseen, by simp⟩
  obtain ⟨rfl, e⟩ := uses_read_loop_eq hr hd _ 0#usize ar seen _ _ rfl hs h
  refine ⟨rfl, ?_⟩
  rw [e, ConRon.Arena.Frontend.Olean.usesRead, ← Array.foldl_toList, ← (ho : out.val.map absWord = out'.toList)]
  rfl

/-- Related lists, at a position. -/
theorem forall₂_getElem {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} (h1 : i < l.length) (h2 : i < l'.length) : R l[i] l'[i] := by
  simpa using (List.forall₂_iff_get.mp h).2 i h1 h2

/-- **`lazy_entries`' loop is `lazyEntries`** from constant `k` on. -/
theorem lazy_entries_loop_ok {pk pers st} {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r) (hd : DSRel d t) {i : Std.U64}
    {o3 : alloc.vec.Vec (alloc.vec.Vec Std.U64)} {outs : Array (Array UInt64)} (ho : OutsRel o3 outs)
    {v : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} (hv : List.Forall₂ EV v.val skels) :
    ∀ (n : Nat) (k : Std.Usize) (ar : arena.store.EStore) (es : alloc.vec.Vec frontend.olean.lazy.CEntry)
      (lst : AState) {es' s'}, v.val.length - k.val = n →
      AStateRel₀ pers (withStore st ar) lst → AStateInv pers (withStore st ar) →
      lazy_entries_loop pk pers ar bs r d i o3 v es k = ok (.Ok es', s') →
      ∃ L lst', (ConRon.Arena.Frontend.Olean.lazyEntries (absPins pk) (absRegion bs r) t i.val outs k.val
          (skels.drop k.val)).run lst = .ok (some L, lst') ∧
        es'.val = es.val ++ es'.val.drop es.val.length ∧ List.Forall₂ CEntryRel (es'.val.drop es.val.length) L ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s') := by
  have hlen := hv.length_eq
  have hlo : o3.val.length = outs.size := by rw [ho.length_eq]; simp
  intro n
  induction n with
  | zero =>
    intro k ar es lst es' s' hk hrel hinv h
    rw [lazy_entries_loop] at h
    have hi : ¬ k < alloc.vec.Vec.len v := by
      have : ¬ k.val < v.val.length := by omega
      exact this
    rw [ite_eq_right hi] at h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
    refine ⟨[], lst, ?_, by simp, by simp, hrel, hinv⟩
    rw [List.drop_of_length_le (by omega)]
    rfl
  | succ n ih =>
    intro k ar es lst es' s' hk hrel hinv h
    rw [lazy_entries_loop] at h
    have hlt : k.val < v.val.length := by omega
    have hi : k < alloc.vec.Vec.len v := hlt
    rw [ite_eq_left hi] at h
    peel h as cf, hcf
    obtain ⟨_hl, rfl⟩ := vec_index_eq hcf
    obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r1 with
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok c =>
    have hlt' : k.val < skels.length := by omega
    have hEV : EV v.val[k.val] skels[k.val] := forall₂_getElem hv hlt hlt'
    obtain ⟨c', lst1, hx1, hc, hrel1, hinv1⟩ := (lazy_entry_ok (pk := pk) (i := i) hr hd hEV) hrel hinv _ _ h1
    obtain ⟨⟨ar2, uses⟩, hq, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    clear h
    have hu : ar2 = ar1 ∧ uses.val.map absNIdx = (ConRon.Arena.Frontend.Olean.usesRead (absPins pk)
        (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t) (outs.getD k.val #[])).toList := by
      by_cases ho2 : k < alloc.vec.Vec.len o3
      · rw [ite_eq_left ho2] at hq
        peel hq as w, hw
        obtain ⟨hwl, rfl⟩ := vec_index_eq hw
        obtain ⟨⟨u1, ar3⟩, hu1, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hq)
        have hkl : k.val < outs.size := by rw [← hlo]; exact hwl
        have hor : OutRel o3.val[k.val] outs[k.val] := by
          have := forall₂_getElem ho hwl (by simpa using hkl)
          simpa using this
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkl, Option.getD_some]
        exact uses_read_eq hr hd hor hu1
      · rw [ite_eq_right ho2] at hq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hq)
        have hkl : ¬ k.val < outs.size := by rw [← hlo]; exact ho2
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
        exact ⟨rfl, by simp [Slice.from_val]; rfl⟩
    obtain ⟨rfl, hU⟩ := hu
    peel h2 as es1, hes1
    peel h2 as k1, hk1
    have ek : k1.val = k.val + 1 := by rw [ConRon.Refine.HashMap.uscalar_add_eq hk1]; rfl
    obtain ⟨L, lst', hxL, hpre, hL, hrel2, hinv2⟩ := ih k1 _ es1 lst1 (by omega) hrel1 hinv1 h2
    have hes1v := ConRon.Refine.vec_push_val hes1
    refine ⟨{ c := c', uses := (ConRon.Arena.Frontend.Olean.usesRead (absPins pk)
        (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t) (outs.getD k.val #[])) } :: L,
      lst', ?_, ?_, ?_, hrel2, hinv2⟩
    · rw [List.drop_eq_getElem_cons hlt', ConRon.Arena.Frontend.Olean.lazyEntries, am_bind_ok hx1]
      dsimp only
      rw [← ek, am_bind_ok hxL]
      rfl
    · rw [hes1v] at hpre
      simp only [List.length_append, List.length_singleton] at hpre
      rw [hpre]
      simp
    · rw [hes1v] at hpre hL
      simp only [List.length_append, List.length_singleton] at hpre hL
      have : es'.val.drop es.val.length = { c := c, uses := uses } :: es'.val.drop (es.val.length + 1) := by
        rw [hpre]; simp
      rw [this]
      exact List.Forall₂.cons ⟨hc, hU⟩ hL

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
  intro hrel hinv es' s' h
  rw [lazy_entries] at h
  obtain ⟨L, lst', hx, -, hL, hrel1, hinv1⟩ :=
    lazy_entries_loop_ok hr hd ho hv _ 0#usize st.store _ lst rfl hrel hinv h
  have e0 : (alloc.vec.Vec.with_capacity frontend.olean.lazy.CEntry (alloc.vec.Vec.len v)).val = [] := rfl
  rw [e0] at hL
  exact ⟨L, lst', hx, by simpa using hL, hrel1, hinv1⟩

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

/-! ## The frontier walk -/

/-- `kind_of_code` is `kindOfCode`. -/
theorem kind_of_code_eq {c : Std.U64} {k : Std.U8} (h : kind_of_code c = ok k) :
    absByte k = ConLeche.Frontend.Olean.kindOfCode c.val := by
  rw [kind_of_code] at h
  rw [ConLeche.Frontend.Olean.kindOfCode]
  by_cases h0 : c = 0#u64
  · rw [ite_eq_left h0] at h; cases Result.ok_injective h
    rw [ite_eq_left (by rw [h0]; rfl)]; exact absByte_k_name
  · rw [ite_eq_right h0] at h
    have h0' : c.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq (by rw [he]; rfl))
    rw [ite_eq_right h0']
    by_cases h1 : c = 1#u64
    · rw [ite_eq_left h1] at h; cases Result.ok_injective h
      rw [ite_eq_left (by rw [h1]; rfl)]; exact absByte_k_level
    · rw [ite_eq_right h1] at h
      have h1' : c.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq (by rw [he]; rfl))
      rw [ite_eq_right h1']
      by_cases h2 : c = 2#u64
      · rw [ite_eq_left h2] at h; cases Result.ok_injective h
        rw [ite_eq_left (by rw [h2]; rfl)]; exact absByte_k_levels
      · rw [ite_eq_right h2] at h
        have h2' : c.val ≠ 2 := fun he => h2 (UScalar.eq_of_val_eq (by rw [he]; rfl))
        rw [ite_eq_right h2']
        cases Result.ok_injective h; exact absByte_k_expr

/-- The twin's push of one kid onto the frontier walk's stack. -/
def kidPush (R : ConLeche.Frontend.Olean.Region) (g : Nat) (st : List Nat) (f : Nat × UInt8 × Bool) :
    List Nat :=
  if f.2.2 && R.fld g f.1 == 1 then st
  else match R.down g (R.fld g f.1) with
    | some c => (c + ConLeche.Frontend.Olean.kindCode f.2.1) :: st
    | none => st

/-- Entries of a walk's stack lie inside the bytes. -/
def InBytes (bs : Slice Std.U8) (l : List Nat) : Prop := ∀ x ∈ l, x ≤ bs.val.length

/-- One kid onto the stack. -/
theorem kid_push_rel {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {g : Std.U64} {stack : alloc.vec.Vec Std.U64} {sp : Std.Usize} {l : List Nat}
    (hs : StackRel (·.val) stack sp l) (hb : InBytes bs l) {v : Std.U64} {k : Std.U8}
    {o : Option Std.U64} (ho : frontend.olean.region.region_down r g v = ok o) {q}
    (h : (match o with
      | none => ok (stack, sp)
      | some c => do
        let i3 ← kind_code k
        let i4 ← c + i3
        let (sp2, stack2) ← push_at stack sp i4
        ok (stack2, sp2)) = ok q) :
    StackRel (·.val) q.1 q.2 (match (absRegion bs r).down g.val (absWord v) with
      | some c => (c + ConLeche.Frontend.Olean.kindCode (absByte k)) :: l
      | none => l) ∧
    InBytes bs (match (absRegion bs r).down g.val (absWord v) with
      | some c => (c + ConLeche.Frontend.Olean.kindCode (absByte k)) :: l
      | none => l) := by
  have e := region_down_eq bs ho
  cases o with
  | none =>
    rw [← e]; cases Result.ok_injective h; exact ⟨hs, hb⟩
  | some c =>
    rw [← e]
    simp only at h
    have hc := region_down_fits hr ho
    peel h as i3, hi3
    peel h as i4, hi4
    obtain ⟨⟨sp2, st2⟩, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have e3 := kind_code_eq hi3
    have e4 := ConRon.Refine.HashMap.uscalar_add_eq hi4
    have hk3 : ConLeche.Frontend.Olean.kindCode (absByte k) ≤ 3 := by
      unfold ConLeche.Frontend.Olean.kindCode; split <;> try split <;> try split
      all_goals omega
    rw [push_at] at hp
    peel hp as st1, hst1
    peel hp as i1, hi1
    cases Result.ok_injective hp
    have hS := hs.push hst1 hi1
    simp only [Option.map_some]
    rw [e4, e3] at hS
    refine ⟨hS, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact hb x hx

/-- **The kids' loop of `frontier_walk`** pushes the twin's `kidPush` fold. -/
theorem frontier_kids_loop {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {g : Std.U64} {fs : alloc.vec.Vec (Std.U64 × Std.U8 × Bool)} :
    ∀ (n : Nat) (j : Std.Usize) (stack : alloc.vec.Vec Std.U64) (sp : Std.Usize) (l : List Nat) {q},
      fs.val.length - j.val = n → StackRel (·.val) stack sp l → InBytes bs l →
      frontier_walk_loop0_loop0 bs r stack sp g fs j = ok q →
      StackRel (·.val) q.1 q.2 (((fs.val.drop j.val).map absKid).foldl (kidPush (absRegion bs r) g.val) l) ∧
      InBytes bs (((fs.val.drop j.val).map absKid).foldl (kidPush (absRegion bs r) g.val) l) := by
  intro n
  induction n with
  | zero =>
    intro j stack sp l q hn hs hb h
    rw [frontier_walk_loop0_loop0] at h
    have hj : ¬ j < alloc.vec.Vec.len fs := by
      have : ¬ j.val < fs.val.length := by omega
      exact this
    rw [ite_eq_right hj] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by omega)]
    exact ⟨hs, hb⟩
  | succ n ih =>
    intro j stack sp l q hn hs hb h
    rw [frontier_walk_loop0_loop0] at h
    have hlt : j.val < fs.val.length := by omega
    have hj : j < alloc.vec.Vec.len fs := hlt
    rw [ite_eq_left hj] at h
    obtain ⟨⟨i1, i2, b⟩, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx' := ConRon.Refine.ExprOps.vec_index_getElem? hx
    have hx'' : fs.val[j.val]'hlt = (i1, i2, b) := by
      rw [List.getElem?_eq_getElem hlt] at hx'; exact Option.some.inj hx'
    have hdrop : fs.val.drop j.val = fs.val[j.val]'hlt :: fs.val.drop (j.val + 1) :=
      List.drop_eq_getElem_cons hlt
    rw [hdrop, hx'', List.map_cons, List.foldl_cons]
    peel h as v, hv
    have ev := region_fld_eq bs (r := r) hv
    have step : ∀ {q1 : alloc.vec.Vec Std.U64 × Std.Usize} (l1 : List Nat), StackRel (·.val) q1.1 q1.2 l1 →
        InBytes bs l1 → kidPush (absRegion bs r) g.val l (absKid (i1, i2, b)) = l1 →
        (do let j1 ← j + 1#usize
            frontier_walk_loop0_loop0 bs r q1.1 q1.2 g fs j1) = ok q →
        StackRel (·.val) q.1 q.2 (((fs.val.drop (j.val + 1)).map absKid).foldl
          (kidPush (absRegion bs r) g.val) (kidPush (absRegion bs r) g.val l (absKid (i1, i2, b)))) ∧
        InBytes bs (((fs.val.drop (j.val + 1)).map absKid).foldl
          (kidPush (absRegion bs r) g.val) (kidPush (absRegion bs r) g.val l (absKid (i1, i2, b)))) := by
      intro q1 l1 hs1 hb1 he h1
      peel h1 as j1, hj1
      have ej := ConRon.Refine.HashMap.uscalar_add_eq hj1
      rw [he, show j.val + 1 = j1.val by rw [ej]; rfl]
      exact ih j1 q1.1 q1.2 l1 (by rw [ej]; simp; omega) hs1 hb1 h1
    have hpush : ∀ {o : Option Std.U64} {q1 : alloc.vec.Vec Std.U64 × Std.Usize},
        frontend.olean.region.region_down r g v = ok o →
        (match o with
          | none => ok (stack, sp)
          | some c => do
            let i3 ← kind_code i2
            let i4 ← c + i3
            let (sp2, stack2) ← push_at stack sp i4
            ok (stack2, sp2)) = ok q1 → ¬ (b && (absRegion bs r).fld g.val i1.val == 1) = true →
        StackRel (·.val) q1.1 q1.2 (kidPush (absRegion bs r) g.val l (absKid (i1, i2, b))) ∧
        InBytes bs (kidPush (absRegion bs r) g.val l (absKid (i1, i2, b))) := by
      intro o q1 ho h1 hnb
      have := kid_push_rel hr hs hb ho h1
      simp only [kidPush, absKid]
      rw [ite_eq_right hnb, ← ev]
      exact this
    cases b with
    | true =>
      simp only [ite_true] at h
      by_cases h1 : v = 1#u64
      · rw [ite_eq_left h1] at h
        refine step (q1 := (stack, sp)) l hs hb ?_ h
        simp only [kidPush, absKid, ← ev, h1]
        rfl
      · rw [ite_eq_right h1] at h
        peel h as o, ho
        obtain ⟨q1, hq1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hne : ¬ (true && (absRegion bs r).fld g.val i1.val == 1) = true := by
          rw [← ev]; simp only [Bool.true_and, beq_iff_eq]
          intro he; exact h1 (absWord_inj (by rw [he]; rfl))
        obtain ⟨a1, a2⟩ := hpush ho hq1 hne
        exact step _ a1 a2 rfl h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      peel h as o, ho
      obtain ⟨q1, hq1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨a1, a2⟩ := hpush ho hq1 (by simp)
      exact step _ a1 a2 rfl h

/-- **`frontier_walk`'s loop is `frontierWalk`**, fuel for fuel. -/
theorem frontier_walk_loop_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {env : alloc.vec.Vec Std.U8} :
    ∀ (n : Nat) (fuel : Std.U64) (seen fr : alloc.vec.Vec Std.U8) (stack : alloc.vec.Vec Std.U64)
      (sp : Std.Usize) (l : List Nat) {o}, fuel.val = n → StackRel (·.val) stack sp l → InBytes bs l →
      frontier_walk_loop0 bs r env seen fr stack sp fuel = ok o →
      absM o.2.1 = frontierWalk (absRegion bs r) (absM env) (absM seen) (absM fr) n l := by
  have hL := bytes_le_max bs
  intro n
  induction n with
  | zero =>
    intro fuel seen fr stack sp l o hf hs hb h
    rw [frontier_walk_loop0] at h
    by_cases hp : sp > 0#usize
    · rw [ite_eq_left hp] at h
      have hz : ¬ fuel > 0#u64 := by
        have : ¬ (0#u64 : Std.U64).val < fuel.val := by rw [hf]; decide
        exact this
      rw [ite_eq_right hz] at h
      cases Result.ok_injective h
      obtain ⟨y, l', rfl⟩ := hs.exists_cons hp
      rw [frontierWalk]
    · rw [ite_eq_right hp] at h
      cases Result.ok_injective h
      rw [hs.nil_of_zero hp, frontierWalk]
  | succ n ih =>
    intro fuel seen fr stack sp l o hf hs hb h
    rw [frontier_walk_loop0] at h
    by_cases hp : sp > 0#usize
    · rw [ite_eq_left hp] at h
      have hz : fuel > 0#u64 := by
        have : (0#u64 : Std.U64).val < fuel.val := by rw [hf]; show 0 < n + 1; omega
        exact this
      rw [ite_eq_left hz] at h
      peel h as fuel1, hfuel1
      have ef := fuel_pred hfuel1
      peel h as sp1, hsp1
      obtain ⟨hi, l', rfl, hs1⟩ := hs.pop hp hsp1
      peel h as e, he
      obtain ⟨_hlt, rfl⟩ := vec_index_eq he
      peel h as i, hi'
      peel h as g, hg
      peel h as i1, hi1
      peel h as k, hk
      peel h as s, hs'
      have eg : g.val = stack.val[sp1.val].val / 8 * 8 := by
        rw [ConRon.Refine.HashMap.uscalar_mul_eq hg, ConRon.Refine.HashMap.uscalar_div_eq hi']; rfl
      have es : s.val = stack.val[sp1.val].val / 8 * 8 / 8 := by
        rw [ConRon.Refine.HashMap.uscalar_div_eq hs', eg]; rfl
      have ek : absByte k = ConLeche.Frontend.Olean.kindOfCode (stack.val[sp1.val].val % 8) := by
        rw [kind_of_code_eq hk, ConRon.Refine.HashMap2.uscalar_rem_eq hi1]; rfl
      have hb0 : stack.val[sp1.val].val ≤ bs.val.length := hb _ (List.mem_cons_self ..)
      have hb1 : InBytes bs l' := fun x hx => hb x (List.mem_cons_of_mem _ hx)
      have hsm : s.val ≤ Std.Usize.max := by omega
      rw [frontierWalk]
      simp only
      rw [← es, ← ek, ← eg]
      peel h as bm, hbm
      have ebm := marked_eq hbm
      by_cases hm : bm = true
      · rw [ite_eq_left hm] at h
        rw [← ebm, ite_eq_left hm]
        peel h as fr1, hfr1
        rw [← mark_eq hsm hfr1]
        exact ih fuel1 seen fr1 stack sp1 l' (by rw [ef, hf]; rfl) hs1 hb1 h
      · rw [ite_eq_right hm] at h
        rw [← ebm, ite_eq_right hm]
        peel h as bs1, hbs1
        have ebs1 := marked_eq hbs1
        by_cases hm1 : bs1 = true
        · rw [ite_eq_left hm1] at h
          rw [← ebs1, ite_eq_left hm1]
          exact ih fuel1 seen fr stack sp1 l' (by rw [ef, hf]; rfl) hs1 hb1 h
        · rw [ite_eq_right hm1] at h
          rw [← ebs1, ite_eq_right hm1]
          peel h as seen1, hseen1
          rw [← mark_eq hsm hseen1]
          peel h as i2, hi2
          peel h as i3, hi3
          peel h as ot, hot
          have kt := kid_table_ks ot hot
          rw [← region_tag_eq bs hi2, ← region_nobjs_eq bs hi3, ← kt]
          cases ot with
          | none => exact ih fuel1 seen1 fr stack sp1 l' (by rw [ef, hf]; rfl) hs1 hb1 h
          | some fs =>
            obtain ⟨⟨st2, sp2⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨hS, hB⟩ := frontier_kids_loop hr _ 0#usize stack sp1 l' rfl hs1 hb1 hq
            simp only [Option.map_some]
            exact ih fuel1 seen1 fr st2 sp2 (((fs.val).map absKid).foldl (kidPush (absRegion bs r) g.val) l')
              (by rw [ef, hf]; rfl) hS hB h
    · rw [ite_eq_right hp] at h
      cases Result.ok_injective h
      rw [hs.nil_of_zero hp, frontierWalk]

/-- A location of the twin's region lies inside the bytes. -/
theorem abs_loc_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {a : UInt64} {g : Nat} (h : (absRegion bs r).loc a = some g) : g + 8 ≤ bs.val.length := by
  simp only [ConLeche.Frontend.Olean.Region.loc] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hg
      rw [← Option.some.inj h]
      have hne : (absRegion bs r).locGo a (absRegion bs r).segs.size ≠ 0 := by simpa using hg
      rcases locGo_fits hr a (absRegion bs r).segs.size with h0 | h1
      · exact absurd h0 hne
      · exact h1

/-- The value roots lie inside the bytes. -/
theorem value_roots_fits {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {skels : List (ConLeche.Frontend.Olean.CEntryF UInt64 UInt64)} {x : Nat}
    (hx : x ∈ valueRoots (absRegion bs r) skels) : x ≤ bs.val.length := by
  simp only [valueRoots, List.mem_filterMap] at hx
  obtain ⟨c, -, hc⟩ := hx
  split at hc
  · rename_i v _ _
    cases hl : (absRegion bs r).loc v with
    | none => rw [hl] at hc; cases hc
    | some g =>
      rw [hl] at hc
      cases Option.some.inj hc
      have := abs_loc_fits hr hl
      have h3 : ConLeche.Frontend.Olean.kindCode ConLeche.Frontend.Olean.kExpr = 3 := by decide
      simp only [h3]
      omega
  · cases hc

/-- **`frontier_walk` is `frontierWalk`**, from the value roots on the stack. -/
theorem frontier_walk_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} (hr : RegionFits bs r)
    {env seen fr : alloc.vec.Vec Std.U8} {values : alloc.vec.Vec Std.U64}
    (hv : ∀ x ∈ values.val, x.val ≤ bs.val.length)
    {o} (h : frontier_walk bs r env seen fr values (alloc.vec.Vec.len values) = ok o) :
    absM o.2.1 = frontierWalk (absRegion bs r) (absM env) (absM seen) (absM fr) closureFuel
      (values.val.map (·.val)).reverse := by
  rw [frontier_walk] at h
  peel h as fuel, hfuel
  have hs : StackRel (·.val) values (alloc.vec.Vec.len values) (values.val.map (·.val)).reverse :=
    ⟨by simp, by simp⟩
  refine frontier_walk_loop_eq hr _ fuel seen fr values _ _ (closure_fuel_val hfuel) hs ?_ h
  intro x hx
  simp only [List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hv y hy

/-- `table_add` is upstream's `Table.add`. -/
theorem table_add_rel {T α : Type} {A : T → α} {tb : frontend.olean.sparse.Table T}
    {tb' : ConLeche.Frontend.Olean.Table α} (ht : TableRel A tb tb') {c : Std.U64} {v : T} {t2}
    (h : table_add tb c v = ok t2) : TableRel A t2 (tb'.add c.val (A v)) := by
  rw [table_add] at h
  peel h as k1, hk1
  peel h as v1, hv1
  cases Result.ok_injective h
  refine ⟨?_, ?_⟩
  · show k1.val.map (·.val) = (tb'.keys.push c.val).toList
    rw [ConRon.Refine.vec_push_val hk1, List.map_append, ht.keys]; simp
  · show v1.val.map A = (tb'.vals.push (A v)).toList
    rw [ConRon.Refine.vec_push_val hv1, List.map_append, ht.vals]; simp

/-- One kind's arm of `frontier_step`: a slot both marks hold goes into the table, with the
memo's value there. -/
theorem frontier_arm {T α : Type} {A : T → α} {m fr : alloc.vec.Vec Std.U8} {k : Std.U8}
    {p c : Std.U64} {sub : Result (Option T)} {get : α}
    (hsub : ∀ o, sub = ok o → o.map A = some get)
    {tb : frontend.olean.sparse.Table T} {tb' : ConLeche.Frontend.Olean.Table α} (ht : TableRel A tb tb')
    {R : Type} {mk : frontend.olean.sparse.Table T → R} {r0 : R} (hr0 : r0 = mk tb) {res}
    {K : Option T → Result R}
    (hKs : ∀ v, K (some v) = Std.bind (table_add tb c v) (fun t => ok (mk t)))
    {b1 : Bool} (hb1 : frontend.olean.fast.marked fr k p = ok b1)
    (h : (if b1 then Std.bind (frontend.olean.fast.marked m k p) (fun b3 =>
          if b3 then Std.bind sub K else ok r0)
        else ok r0) = ok res) :
    ∃ t2, res = mk t2 ∧ TableRel A t2
      (if ConLeche.Frontend.Olean.marked (absM fr) (absByte k) p.val &&
          ConLeche.Frontend.Olean.marked (absM m) (absByte k) p.val
        then tb'.add c.val get else tb') := by
  rw [← marked_eq hb1]
  cases b1 with
  | false => cases Result.ok_injective h; exact ⟨tb, hr0, by simpa using ht⟩
  | true =>
    simp only [↓reduceIte] at h
    peel h as b3, hb3
    rw [← marked_eq hb3]
    cases b3 with
    | false => cases Result.ok_injective h; exact ⟨tb, hr0, by simpa using ht⟩
    | true =>
      simp only [↓reduceIte] at h
      peel h as o, ho
      have e := hsub o ho
      cases o with
      | none => cases e
      | some v =>
        rw [hKs] at h
        peel h as t2, ht2
        cases Result.ok_injective h
        simp only [Option.map_some, Option.some.injEq] at e
        refine ⟨t2, rfl, ?_⟩
        simp only [Bool.and_self, ↓reduceIte]
        rw [← e]
        exact table_add_rel ht ht2

/-- **`frontier_step` is `frontierStep`.** -/
theorem frontier_step_rel {m fr : alloc.vec.Vec Std.U8} {d : frontend.olean.fast.DS} {t : TDS}
    (hd : DSRel d t) {p : Std.U64} (hp : p.val ≤ Std.Usize.max) {b : frontend.olean.sparse.Frontier}
    {b' : Arena.Frontend.Olean.Frontier} (hb : FrontierRel b b') {b2}
    (h : frontier_step m fr d p b = ok b2) :
    FrontierRel b2 (Arena.Frontend.Olean.frontierStep (absM m) (absM fr) t p.val b') := by
  rw [frontier_step] at h
  rw [Arena.Frontend.Olean.frontierStep]
  peel h as i, hi
  have ei := marks_at_eq hi
  by_cases hz : i = 0#u8
  · rw [ite_eq_left hz] at h
    cases Result.ok_injective h
    rw [ite_eq_left (by rw [← ei, hz]; rfl)]
    exact hb
  rw [ite_eq_right hz] at h
  rw [ite_eq_right (by rw [← ei]; intro he; exact hz (absByte_inj (by simpa using he)))]
  peel h as c, hc
  have hcv : c.val = 8 * p.val := by rw [ConRon.Refine.HashMap.uscalar_mul_eq hc]; simp
  have hcp : tr (c.val / 8) = p.val := by rw [hcv, Nat.mul_div_cancel_left _ (by decide), tr_of_le hp]
  have hs := ds_subrel hd
  peel h as m1, hm1
  obtain ⟨q1, hq1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n2, rfl, hN⟩ := frontier_arm (A := absNIdx) (k := frontend.olean.fast.K_NAME) (m := m) (fr := fr) (p := p) (c := c)
    (get := t.names.getD p.val default)
    (fun o ho => by rw [hs.nm c o ho]; show some (t.names.getD (tr (c.val / 8)) default) = _; rw [hcp])
    hb.names (mk := fun tb => { b with names := tb }) (r0 := b) rfl (fun _ => rfl) hm1 hq1
  peel h as m2, hm2
  obtain ⟨q2, hq2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l2, rfl, hL⟩ := frontier_arm (A := absLIdx) (k := frontend.olean.fast.K_LEVEL) (m := m) (fr := fr) (p := p) (c := c)
    (get := t.levels.getD p.val default)
    (fun o ho => by rw [hs.lv c o ho]; show some (t.levels.getD (tr (c.val / 8)) default) = _; rw [hcp])
    hb.levels (mk := fun tb => { b with names := n2, levels := tb }) (r0 := { b with names := n2 }) rfl (fun _ => rfl) hm2 hq2
  peel h as m3, hm3
  obtain ⟨q3, hq3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨s2, rfl, hS⟩ := frontier_arm (A := absLsIdx) (k := frontend.olean.fast.K_LEVELS) (m := m) (fr := fr) (p := p) (c := c)
    (get := t.lists.getD p.val default)
    (fun o ho => by rw [hs.lvs c o ho]; show some (t.lists.getD (tr (c.val / 8)) default) = _; rw [hcp])
    hb.lists (mk := fun tb => { b with names := n2, levels := l2, lists := tb })
    (r0 := { b with names := n2, levels := l2 }) rfl (fun _ => rfl) hm3 hq3
  peel h as m4, hm4
  obtain ⟨e2, rfl, hE⟩ := frontier_arm (A := absEIdx) (k := frontend.olean.fast.K_EXPR) (m := m) (fr := fr) (p := p) (c := c)
    (get := t.exprs.getD p.val default)
    (fun o ho => by rw [hs.ex c o ho]; show some (t.exprs.getD (tr (c.val / 8)) default) = _; rw [hcp])
    hb.exprs (mk := fun tb => { b with names := n2, levels := l2, lists := s2, exprs := tb })
    (r0 := { b with names := n2, levels := l2, lists := s2 }) rfl (fun _ => rfl) hm4 h
  rw [hcv] at hN hL hS hE
  simp only [absByte_k_name, absByte_k_level, absByte_k_levels, absByte_k_expr] at hN hL hS hE
  exact ⟨hN, hL, hS, hE⟩

/-- **`frontier_of` is `frontierOf`**, from the empty frontier. -/
theorem frontier_of_rel {m fr : alloc.vec.Vec Std.U8} {d : frontend.olean.fast.DS} {t : TDS}
    (hd : DSRel d t) {n : Std.U64} (hn : n.val ≤ Std.Usize.max) {b0 b}
    (hb0 : frontend.olean.sparse.frontier_empty = ok b0)
    (h : frontier_of m fr d n 0#u64 b0 = ok b) :
    FrontierRel b (frontierOf (absM m) (absM fr) t n.val 0 {}) := by
  have H : ∀ (k : Nat) (q : Std.U64) (c : frontend.olean.sparse.Frontier)
      (c' : Arena.Frontend.Olean.Frontier) {r}, n.val - q.val = k → FrontierRel c c' →
      frontier_of_loop m fr d n c q = ok r →
      FrontierRel r (frontierOf (absM m) (absM fr) t n.val q.val c') := by
    intro k
    induction k with
    | zero =>
      intro q c c' r hk hc h
      rw [frontier_of_loop, ite_eq_right (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [frontierOf, ite_eq_right (by omega)]
      exact hc
    | succ k ih =>
      intro q c c' r hk hc h
      rw [frontier_of_loop, ite_eq_left (by scalar_tac)] at h
      peel h as c2, hc2
      peel h as q1, hq1
      have hq1v : q1.val = q.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hq1
      have hs := frontier_step_rel hd (p := q) (by omega) hc hc2
      rw [frontierOf, ite_eq_left (by omega)]
      have := ih q1 c2 _ (by omega) hs h
      rwa [hq1v] at this
  exact H _ 0#u64 b0 {} rfl (frontier_empty_rel hb0) h

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
    rw [alloc.vec.Vec.resize] at hstamps
    have hv : stamps.val = List.replicate i4.val 0#u64 := by
      split at hstamps
      · rename_i hlt
        simp at hlt
      · peel hstamps as x, hx
        have hx0 : 0#u64 = x := Result.ok_injective hx
        subst hx0
        cases Result.ok_injective hstamps
        have e0 : ∀ (l : List Std.U64) (hl), (alloc.vec.Vec.from l hl).val = l := fun l hl => Slice.from_val _ _
        have e1 : (alloc.vec.Vec.new Std.U64).val = [] := Slice.from_val _ _
        rw [e0, e1]
        simp [List.resize]
    rw [StampsRel, hv, hi4v]
    simp
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
  obtain ⟨⟨nm', ms', t⟩, lst3, hx3, ⟨hnmv, hnmb, hmsv, hd⟩, hrel3, hinv3⟩ := hM
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
  have efw := frontier_walk_eq hfit (fun x hx => value_roots_fits hfit
    (evals ▸ List.mem_map_of_mem (f := fun y : Std.U64 => y.val) hx)) hq6
  peel h as b0, hb0
  peel h as frontier, hfront
  have efo := frontier_of_rel hd hnmb hb0 hfront
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
