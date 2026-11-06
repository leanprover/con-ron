/-
# `ConRon.Refine2.Frontend.Olean.Sparse` — `olean/sparse.rs` against the twin's

**Task #142, Theorem 2.**  The kid tables against upstream's; the memo, four `HashMap2`s keyed
by `u64` against `Std.HashMap Nat _` (`SMRel`); `s_go` and `kids_go`, in lockstep with the
twin's mutual recursion, by strong induction on the location.
-/
import ConRon.Refine2.Frontend.Olean.FastBuild
import ConRon.Refine2.Frontend.Olean.SpecEntry

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_fld region_down region_tag region_nobjs region_fits region_loc)
open frontend.olean.spec (name_node level_node levels_node expr_node)
open frontend.olean.fast (K_NAME K_LEVEL K_LEVELS K_EXPR)
open frontend.olean.sparse (kids_if kids1 kids2 name_kids level_kids levels_kids expr_kids kid_table
  sm_has sm_build s_go kids_go sm_empty sparse_name_p sparse_expr_p sparse_entry)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (Sub sGo kidsGo nameNode levelNode levelsNode exprNode sparseNameP
  sparseExprP sparseEntry)
open ConLeche.Frontend.Olean (kName kLevel kLevels kExpr kidTable nameKids levelKids levelsKids exprKids
  CEntryF)
open ConRon.Refine.HashMap (uscalar_add_eq)
open ConRon.Refine.HashMap2 (Inv KeysOk toFun)

/-- A table of the memo. -/
abbrev TSM := ConRon.Arena.Frontend.Olean.SM

/-! ## The kid tables -/

/-- A kid of an object, as upstream's. -/
def absKid (a : Std.U64 × Std.U8 × Bool) : Nat × UInt8 × Bool := (a.1.val, absByte a.2.1, a.2.2)

/-- A kid table of the Rust against upstream's. -/
def KS (x : Result (Option (alloc.vec.Vec (Std.U64 × Std.U8 × Bool))))
    (y : Option (List (Nat × UInt8 × Bool))) : Prop :=
  ∀ o, x = ok o → o.map (fun v => v.val.map absKid) = y

theorem KS.none : KS (ok none) none := by
  intro o h; cases Result.ok_injective h; rfl

theorem kids1_val {a v} (h : kids1 a = ok v) : v.val = [a] := by
  rw [kids1] at h
  rw [ConRon.Refine.vec_push_val h]; rfl

theorem kids2_val {a b v} (h : kids2 a b = ok v) : v.val = [a, b] := by
  rw [kids2] at h
  peel h as v1, h1
  rw [ConRon.Refine.vec_push_val h, ConRon.Refine.vec_push_val h1]; rfl

/-- The arm of no kid. -/
theorem kids0_arm {n w : Std.U64} :
    KS (kids_if (decide (n = w)) (alloc.vec.Vec.new (Std.U64 × Std.U8 × Bool)))
      (if n.val = w.val then some [] else none) := by
  intro o h
  rw [kids_if] at h
  by_cases hn : n = w
  · subst hn
    simp only [decide_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_left rfl]
    rfl
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_right (u64_lit_ne hn)]
    rfl

/-- The arm of one kid. -/
theorem kids1_arm {n w i : Std.U64} {k : Std.U8} {b : Bool} :
    KS (do
        let v ← kids1 (i, k, b)
        kids_if (decide (n = w)) v)
      (if n.val = w.val then some [(i.val, absByte k, b)] else none) := by
  intro o h
  peel h as v, hv
  rw [kids_if] at h
  by_cases hn : n = w
  · subst hn
    simp only [decide_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_left rfl]
    simp [kids1_val hv, absKid]
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_right (u64_lit_ne hn)]
    rfl

/-- The arm of two kids. -/
theorem kids2_arm {n w i j : Std.U64} {k l : Std.U8} {b c : Bool} :
    KS (do
        let v ← kids2 (i, k, b) (j, l, c)
        kids_if (decide (n = w)) v)
      (if n.val = w.val then some [(i.val, absByte k, b), (j.val, absByte l, c)] else none) := by
  intro o h
  peel h as v, hv
  rw [kids_if] at h
  by_cases hn : n = w
  · subst hn
    simp only [decide_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_left rfl]
    simp [kids2_val hv, absKid]
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_right (u64_lit_ne hn)]
    rfl

/-- The arm of three kids. -/
theorem kids3_arm {n w i j m : Std.U64} {k l q : Std.U8} {b c d : Bool} :
    KS (do
        let v ← kids2 (i, k, b) (j, l, c)
        let v1 ← alloc.vec.Vec.push v (m, q, d)
        kids_if (decide (n = w)) v1)
      (if n.val = w.val then some [(i.val, absByte k, b), (j.val, absByte l, c), (m.val, absByte q, d)]
       else none) := by
  intro o h
  peel h as v, hv
  peel h as v1, hv1
  rw [kids_if] at h
  by_cases hn : n = w
  · subst hn
    simp only [decide_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_left rfl]
    simp [ConRon.Refine.vec_push_val hv1, kids2_val hv, absKid]
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    cases Result.ok_injective h
    rw [ite_eq_right (u64_lit_ne hn)]
    rfl

/-- **`name_kids` is `nameKids`.** -/
theorem name_kids_ks {t n : Std.U64} : KS (name_kids t n) (nameKids t.val n.val) := by
  rw [name_kids]
  by_cases h1 : t = 1#u64
  · subst h1
    rw [ite_eq_left rfl]
    mark_arm n 2#u64 (show KS (if n = 2#u64 then do
        let v ← kids1 (0#u64, K_NAME, true)
        ok (some v) else ok none) (if n.val = (2#u64 : Std.U64).val then some [((0#u64 : Std.U64).val, absByte K_NAME, true)] else none) by
      intro o h
      by_cases hn : n = 2#u64
      · rw [ite_eq_left hn] at h
        peel h as v, hv
        cases Result.ok_injective h
        rw [ite_eq_left (by rw [hn])]
        simp [kids1_val hv, absKid]
      · rw [ite_eq_right hn] at h
        cases Result.ok_injective h
        rw [ite_eq_right (u64_lit_ne hn)]
        rfl)
  · rw [ite_eq_right h1]
    by_cases h2 : t = 2#u64
    · subst h2
      rw [ite_eq_left rfl]
      mark_arm n 2#u64 (show KS (if n = 2#u64 then do
          let v ← kids1 (0#u64, K_NAME, true)
          ok (some v) else ok none) (if n.val = (2#u64 : Std.U64).val then some [((0#u64 : Std.U64).val, absByte K_NAME, true)] else none) by
        intro o h
        by_cases hn : n = 2#u64
        · rw [ite_eq_left hn] at h
          peel h as v, hv
          cases Result.ok_injective h
          rw [ite_eq_left (by rw [hn])]
          simp [kids1_val hv, absKid]
        · rw [ite_eq_right hn] at h
          cases Result.ok_injective h
          rw [ite_eq_right (u64_lit_ne hn)]
          rfl)
    · rw [ite_eq_right h2]
      have e1 : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq he)
      have e2 : t.val ≠ 2 := fun he => h2 (UScalar.eq_of_val_eq he)
      generalize UScalar.val t = T at e1 e2 ⊢
      rcases T with _ | _ | _ | T
      · exact KS.none
      · exact absurd rfl e1
      · exact absurd rfl e2
      · exact KS.none

/-- **`level_kids` is `levelKids`.** -/
theorem level_kids_ks {t n : Std.U64} : KS (level_kids t n) (levelKids t.val n.val) := by
  unfold level_kids
  split
  · mark_arm n 0#u64 (kids0_arm (n := n) (w := 0#u64))
  · mark_arm n 1#u64 (kids1_arm (n := n) (w := 1#u64) (i := 0#u64) (k := K_LEVEL) (b := true))
  · mark_arm n 2#u64 (kids2_arm (n := n) (w := 2#u64) (i := 0#u64) (j := 1#u64) (k := K_LEVEL) (l := K_LEVEL) (b := true) (c := true))
  · mark_arm n 2#u64 (kids2_arm (n := n) (w := 2#u64) (i := 0#u64) (j := 1#u64) (k := K_LEVEL) (l := K_LEVEL) (b := true) (c := true))
  · mark_arm n 1#u64 (kids1_arm (n := n) (w := 1#u64) (i := 0#u64) (k := K_NAME) (b := true))
  · rename_i h0 h1 h2 h3 h4
    have e0 : t.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq he)
    have e1 : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq he)
    have e2 : t.val ≠ 2 := fun he => h2 (UScalar.eq_of_val_eq he)
    have e3 : t.val ≠ 3 := fun he => h3 (UScalar.eq_of_val_eq he)
    have e4 : t.val ≠ 4 := fun he => h4 (UScalar.eq_of_val_eq he)
    generalize UScalar.val t = T at e0 e1 e2 e3 e4 ⊢
    rcases T with _ | _ | _ | _ | _ | T
    · exact absurd rfl e0
    · exact absurd rfl e1
    · exact absurd rfl e2
    · exact absurd rfl e3
    · exact absurd rfl e4
    · exact KS.none

/-- **`levels_kids` is `levelsKids`.** -/
theorem levels_kids_ks {t n : Std.U64} : KS (levels_kids t n) (levelsKids t.val n.val) := by
  rw [levels_kids]
  by_cases h1 : t = 1#u64
  · subst h1
    rw [ite_eq_left rfl]
    mark_arm n 2#u64 (show KS (if n = 2#u64 then do
        let v ← kids2 (0#u64, K_LEVEL, true) (1#u64, K_LEVELS, true)
        ok (some v) else ok none) (if n.val = (2#u64 : Std.U64).val then some [((0#u64 : Std.U64).val, absByte K_LEVEL, true), ((1#u64 : Std.U64).val, absByte K_LEVELS, true)] else none) by
      intro o h
      by_cases hn : n = 2#u64
      · rw [ite_eq_left hn] at h
        peel h as v, hv
        cases Result.ok_injective h
        rw [ite_eq_left (by rw [hn])]
        simp [kids2_val hv, absKid]
      · rw [ite_eq_right hn] at h
        cases Result.ok_injective h
        rw [ite_eq_right (u64_lit_ne hn)]
        rfl)
  · rw [ite_eq_right h1]
    have e1 : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq he)
    generalize UScalar.val t = T at e1 ⊢
    rcases T with _ | _ | T
    · exact KS.none
    · exact absurd rfl e1
    · exact KS.none

/-- **`expr_kids` is `exprKids`.** -/
theorem expr_kids_ks {t n : Std.U64} : KS (expr_kids t n) (exprKids t.val n.val) := by
  unfold expr_kids
  split
  · mark_arm n 1#u64 (kids0_arm (n := n) (w := 1#u64))
  · mark_arm n 1#u64 (kids1_arm (n := n) (w := 1#u64) (i := 0#u64) (k := K_LEVEL) (b := true))
  · mark_arm n 2#u64 (kids2_arm (n := n) (w := 2#u64) (i := 0#u64) (j := 1#u64) (k := K_NAME) (l := K_LEVELS) (b := true) (c := true))
  · mark_arm n 2#u64 (kids2_arm (n := n) (w := 2#u64) (i := 0#u64) (j := 1#u64) (k := K_EXPR) (l := K_EXPR) (b := false) (c := false))
  · mark_arm n 3#u64 (kids2_arm (n := n) (w := 3#u64) (i := 1#u64) (j := 2#u64) (k := K_EXPR) (l := K_EXPR) (b := false) (c := false))
  · mark_arm n 3#u64 (kids2_arm (n := n) (w := 3#u64) (i := 1#u64) (j := 2#u64) (k := K_EXPR) (l := K_EXPR) (b := false) (c := false))
  · mark_arm n 4#u64 (kids3_arm (n := n) (w := 4#u64) (i := 1#u64) (j := 2#u64) (m := 3#u64) (k := K_EXPR) (l := K_EXPR) (q := K_EXPR) (b := false) (c := false) (d := false))
  · mark_arm n 1#u64 (kids0_arm (n := n) (w := 1#u64))
  · mark_arm n 2#u64 (kids1_arm (n := n) (w := 2#u64) (i := 1#u64) (k := K_EXPR) (b := false))
  · mark_arm n 3#u64 (kids2_arm (n := n) (w := 3#u64) (i := 0#u64) (j := 2#u64) (k := K_NAME) (l := K_EXPR) (b := true) (c := false))
  · rename_i h0 h3 h4 h5 h6 h7 h8 h9 h10 h11
    have e0 : t.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq he)
    have e3 : t.val ≠ 3 := fun he => h3 (UScalar.eq_of_val_eq he)
    have e4 : t.val ≠ 4 := fun he => h4 (UScalar.eq_of_val_eq he)
    have e5 : t.val ≠ 5 := fun he => h5 (UScalar.eq_of_val_eq he)
    have e6 : t.val ≠ 6 := fun he => h6 (UScalar.eq_of_val_eq he)
    have e7 : t.val ≠ 7 := fun he => h7 (UScalar.eq_of_val_eq he)
    have e8 : t.val ≠ 8 := fun he => h8 (UScalar.eq_of_val_eq he)
    have e9 : t.val ≠ 9 := fun he => h9 (UScalar.eq_of_val_eq he)
    have e10 : t.val ≠ 10 := fun he => h10 (UScalar.eq_of_val_eq he)
    have e11 : t.val ≠ 11 := fun he => h11 (UScalar.eq_of_val_eq he)
    generalize UScalar.val t = T at e0 e3 e4 e5 e6 e7 e8 e9 e10 e11 ⊢
    rcases T with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | T
    · exact absurd rfl e0
    · exact KS.none
    · exact KS.none
    · exact absurd rfl e3
    · exact absurd rfl e4
    · exact absurd rfl e5
    · exact absurd rfl e6
    · exact absurd rfl e7
    · exact absurd rfl e8
    · exact absurd rfl e9
    · exact absurd rfl e10
    · exact absurd rfl e11
    · exact KS.none

theorem absByte_inj {a b : Std.U8} (h : absByte a = absByte b) : a = b := by
  have := congrArg UInt8.toNat h
  rw [absByte_toNat, absByte_toNat] at this
  exact UScalar.eq_of_val_eq this

/-- The test of a kind, as upstream's. -/
theorem kind_test {k K : Std.U8} : k = K ↔ absByte k = absByte K :=
  ⟨fun h => by rw [h], absByte_inj⟩

/-- **`kid_table` is `kidTable`.** -/
theorem kid_table_ks {k : Std.U8} {t n : Std.U64} : KS (kid_table k t n) (kidTable (absByte k) t.val n.val) := by
  rw [kid_table, kidTable]
  simp only [← absByte_k_name, ← absByte_k_level, ← absByte_k_levels]
  by_cases h1 : k = K_NAME
  · rw [ite_eq_left h1, ite_eq_left (kind_test.mp h1)]
    exact name_kids_ks
  · rw [ite_eq_right h1, ite_eq_right (fun he => h1 (kind_test.mpr he))]
    by_cases h2 : k = K_LEVEL
    · rw [ite_eq_left h2, ite_eq_left (kind_test.mp h2)]
      exact level_kids_ks
    · rw [ite_eq_right h2, ite_eq_right (fun he => h2 (kind_test.mpr he))]
      by_cases h3 : k = K_LEVELS
      · rw [ite_eq_left h3, ite_eq_left (kind_test.mp h3)]
        exact levels_kids_ks
      · rw [ite_eq_right h3, ite_eq_right (fun he => h3 (kind_test.mpr he))]
        exact expr_kids_ks

/-! ## The memo -/

/-- The hash of the memo's keys. -/
abbrev hU64 := U64.Insts.Con_ron_coreRonHashmapHashable

/-- **A table of the memo**, by location. -/
structure MapRel {V V' : Type} (A : V → V') (m : ron.hashmap2.HashMap2 Std.U64 V)
    (s : _root_.Std.HashMap Nat V') : Prop where
  inv : Inv hU64 m
  get : ∀ k, (toFun m k).map A = s[k.val]?

section MapRel
variable {V V' : Type} {A : V → V'} {m : ron.hashmap2.HashMap2 Std.U64 V} {s : _root_.Std.HashMap Nat V'}

theorem MapRel.get_eq (h : MapRel A m s) {k : Std.U64} {o : Option V}
    (hg : ron.hashmap2.HashMap2.get hU64 eU64 m k = ok o) : o.map A = s[k.val]? := by
  rw [ConRon.Refine.HashMap2.get_refines_gen (P := fun _ => True) u64Eq2Fwd h.inv (fun _ _ => trivial)
    trivial hg]
  exact h.get k

theorem MapRel.contains_eq (h : MapRel A m s) {k : Std.U64} {b : Bool}
    (hg : ron.hashmap2.HashMap2.contains_key hU64 eU64 m k = ok b) : b = s.contains k.val := by
  rw [ConRon.Refine.HashMap2.contains_key_refines_gen (P := fun _ => True) u64Eq2Fwd h.inv
    (fun _ _ => trivial) trivial hg, _root_.Std.HashMap.contains_eq_isSome_getElem?, ← h.get k]
  cases toFun m k <;> rfl

theorem MapRel.insert (h : MapRel A m s) {k : Std.U64} {v : V} {old} {m'}
    (hi : ron.hashmap2.HashMap2.insert hU64 eU64 m k v = ok (old, m')) :
    MapRel A m' (s.insert k.val (A v)) := by
  obtain ⟨hinv, -, hupd, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen (P := fun _ => True) u64Eq2Fwd
    h.inv (fun _ _ => trivial) trivial hi
  refine ⟨hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hk : k1 = k
  · subst hk; simp
  · have hne : (k.val == k1.val) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (UScalar.eq_of_val_eq he.symm)
    rw [ite_eq_right hk, hne]
    simpa using h.get k1

theorem MapRel.empty {m : ron.hashmap2.HashMap2 Std.U64 V} (hn : ron.hashmap2.HashMap2.new Std.U64 V = ok m) :
    MapRel A m {} := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines (HashableInst := hU64) hn
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

end MapRel

/-- **The sparse memo, table by table.** -/
structure SMRel (d : frontend.olean.sparse.SM) (t : TSM) : Prop where
  names : MapRel absNIdx d.names t.names
  levels : MapRel absLIdx d.levels t.levels
  lists : MapRel absLsIdx d.lists t.lists
  exprs : MapRel absEIdx d.exprs t.exprs

/-- `sm_empty` is the empty memo. -/
theorem sm_empty_rel {d} (h : sm_empty = ok d) : SMRel d {} := by
  rw [sm_empty] at h
  peel h as h1, hh1
  peel h as h2, hh2
  peel h as h3, hh3
  peel h as h4, hh4
  cases Result.ok_injective h
  exact ⟨MapRel.empty hh1, MapRel.empty hh2, MapRel.empty hh3, MapRel.empty hh4⟩

/-- **`sm_has` is `SM.has`.** -/
theorem sm_has_eq {d t} (hd : SMRel d t) {k : Std.U8} {g : Std.U64} {b : Bool} (h : sm_has d k g = ok b) :
    b = ConRon.Arena.Frontend.Olean.SM.has t (absByte k) g.val := by
  rw [sm_has] at h
  rw [ConRon.Arena.Frontend.Olean.SM.has]
  simp only [← absByte_k_name, ← absByte_k_level, ← absByte_k_levels]
  by_cases h1 : k = K_NAME
  · rw [ite_eq_left h1] at h
    rw [ite_eq_left (kind_test.mp h1)]
    exact hd.names.contains_eq h
  · rw [ite_eq_right h1] at h
    rw [ite_eq_right (fun he => h1 (kind_test.mpr he))]
    by_cases h2 : k = K_LEVEL
    · rw [ite_eq_left h2] at h
      rw [ite_eq_left (kind_test.mp h2)]
      exact hd.levels.contains_eq h
    · rw [ite_eq_right h2] at h
      rw [ite_eq_right (fun he => h2 (kind_test.mpr he))]
      by_cases h3 : k = K_LEVELS
      · rw [ite_eq_left h3] at h
        rw [ite_eq_left (kind_test.mp h3)]
        exact hd.lists.contains_eq h
      · rw [ite_eq_right h3] at h
        rw [ite_eq_right (fun he => h3 (kind_test.mpr he))]
        exact hd.exprs.contains_eq h

/-- **The sparse memo as `Sub`.** -/
theorem sm_subrel {d t} (hd : SMRel d t) :
    SubRel frontend.olean.sparse.SM.Insts.Con_ron_coreFrontendOleanSpecSub d
      (ConRon.Arena.Frontend.Olean.SM.sub t) where
  nm c o hc := by
    simp only [frontend.olean.sparse.SM.Insts.Con_ron_coreFrontendOleanSpecSub.sub_name] at hc
    peel hc as o1, ho1
    have e := hd.names.get_eq ho1
    cases o1 with
    | none => cases Result.ok_injective hc; exact e
    | some h =>
      dsimp only at hc
      peel hc as n, hn
      cases Result.ok_injective hc
      rw [nidx_dup2_ok hn]
      exact e
  lv c o hc := by
    simp only [frontend.olean.sparse.SM.Insts.Con_ron_coreFrontendOleanSpecSub.sub_level] at hc
    peel hc as o1, ho1
    have e := hd.levels.get_eq ho1
    cases o1 with
    | none => cases Result.ok_injective hc; exact e
    | some h =>
      dsimp only at hc
      peel hc as n, hn
      cases Result.ok_injective hc
      rw [lidx_dup2_ok hn]
      exact e
  lvs c o hc := by
    simp only [frontend.olean.sparse.SM.Insts.Con_ron_coreFrontendOleanSpecSub.sub_levels] at hc
    peel hc as o1, ho1
    have e := hd.lists.get_eq ho1
    cases o1 with
    | none => cases Result.ok_injective hc; exact e
    | some h =>
      dsimp only at hc
      peel hc as n, hn
      cases Result.ok_injective hc
      rw [lsidx_dup2_ok hn]
      exact e
  ex c o hc := by
    simp only [frontend.olean.sparse.SM.Insts.Con_ron_coreFrontendOleanSpecSub.sub_expr] at hc
    peel hc as o1, ho1
    have e := hd.exprs.get_eq ho1
    cases o1 with
    | none => cases Result.ok_injective hc; exact e
    | some h =>
      dsimp only at hc
      peel hc as n, hn
      cases Result.ok_injective hc
      rw [eidx_dup2_ok hn]
      exact e

set_option hygiene false in
/-- One arm of `sm_build`: the node function and the insert.  A script: the Rust's `match` is
its own matcher.  It reads `hd`. -/
macro "build_arm " hn:term " , " hu:term : tactic =>
  `(tactic| (
    intro hrel hinv o s' d' hm
    obtain ⟨⟨r1, ar1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hF := $hn:term hrel hinv r1 ar1 h1
    cases r1 with
    | Ok a =>
      obtain ⟨b, lst1, hx, hR, h3, h4⟩ := hF
      cases hR
      rw [am_bind_ok hx]
      peel h2 as q, hq
      obtain ⟨old, hm1⟩ := q
      cases Result.ok_injective h2
      exact ⟨_, lst1, rfl, $hu:term, h3, h4⟩
    | Err e =>
      cases Result.ok_injective h2
      exact rdout_err_bind hF rfl))

/-- **`sm_build` is `SM.build`.** -/
theorem sm_build_ts {pk bs r pers st lst} {k : Std.U8} {g : Std.U64} {d t} (hr : RegionFits bs r)
    (hd : SMRel d t) :
    TS SMRel pers st lst (sm_build pk pers st.store bs r k g d)
      (ConRon.Arena.Frontend.Olean.SM.build (absPins pk) (absRegion bs r) (absByte k) g.val t) := by
  have hs := sm_subrel hd
  rw [sm_build, ConRon.Arena.Frontend.Olean.SM.build]
  simp only [← absByte_k_name, ← absByte_k_level, ← absByte_k_levels]
  by_cases h1 : k = K_NAME
  · rw [ite_eq_left h1, ite_eq_left (kind_test.mp h1)]
    build_arm (name_node_refines (pk := pk) (g := g) hr hs),
      ⟨hd.names.insert hq, hd.levels, hd.lists, hd.exprs⟩
  · rw [ite_eq_right h1, ite_eq_right (fun he => h1 (kind_test.mpr he))]
    by_cases h2 : k = K_LEVEL
    · rw [ite_eq_left h2, ite_eq_left (kind_test.mp h2)]
      build_arm (level_node_refines (pk := pk) (bs := bs) (r := r) (g := g) hs),
        ⟨hd.names, hd.levels.insert hq, hd.lists, hd.exprs⟩
    · rw [ite_eq_right h2, ite_eq_right (fun he => h2 (kind_test.mpr he))]
      by_cases h3 : k = K_LEVELS
      · rw [ite_eq_left h3, ite_eq_left (kind_test.mp h3)]
        build_arm (levels_node_refines (pk := pk) (bs := bs) (r := r) (g := g) hs),
          ⟨hd.names, hd.levels, hd.lists.insert hq, hd.exprs⟩
      · rw [ite_eq_right h3, ite_eq_right (fun he => h3 (kind_test.mpr he))]
        build_arm (expr_node_refines (pk := pk) (g := g) hr hs),
          ⟨hd.names, hd.levels, hd.lists, hd.exprs.insert hq⟩

/-! ## The recursion -/

theorem TS.none {δ τ : Type} {Rel : δ → τ → Prop} {pers st lst} {d : δ} :
    TS Rel pers st lst (ok (.Err .Bad, st.store, d)) (pure Option.none) := by
  intro hrel hinv o s' d' hm
  cases Result.ok_injective hm
  exact ⟨lst, rfl, hrel, hinv⟩

set_option hygiene false in
/-- The arm of a followed field of `kids_go`.  A script: the Rust's `match`es are its own
matchers.  It reads `IH`, `hd`, `next`, and the region's names. -/
macro "kid_tail" : tactic =>
  `(tactic| (
    refine TS.pure_step fun o ho => ?_
    have hloc := region_down_eq bs ho
    cases o with
    | none =>
      have hn : (absRegion bs r).down g.val (absWord v) = Option.none := hloc.symm
      refine TS.of_eq TS.none ?_
      split
      · rename_i heq
        rw [hn] at heq
        cases heq
      · rfl
    | some c =>
      have hn : (absRegion bs r).down g.val (absWord v) = Option.some c.val := hloc.symm
      have hlt1 : c.val < g.val := ConLeche.Frontend.Olean.Region.down_lt hn
      refine TS.of_eq (TS.bind (IH c.val (by omega) (k := kk) (g := c) (st := st) (lst := lst) rfl hd)
        (g := fun t1 => kidsGo (absPins pk) (absRegion bs r) g.val ((fs.val.drop (i.val + 1)).map absKid) t1)
        fun s1 d1 t1 lst1 h1 => ?_) ?_
      rotate_left
      · split
        · rename_i heq
          rw [hn] at heq
          cases Option.some.inj heq
          refine congrArg (_ >>= ·) (funext fun w => ?_)
          cases w <;> rfl
        · rename_i heq
          rw [hn] at heq
          cases heq
      · refine TS.pure_step fun i4 hi4 => ?_
        exact next hi4 h1))

/-- **`s_go` is `sGo`**, by strong induction on the location. -/
theorem s_go_ts {pk bs r pers} (hr : RegionFits bs r) :
    ∀ (G : Nat) {k : Std.U8} {g : Std.U64} {d t st lst}, g.val = G → SMRel d t →
      TS SMRel pers st lst (s_go pk pers st.store bs r k g d)
        (sGo (absPins pk) (absRegion bs r) (absByte k) g.val t) := by
  intro G
  induction G using Nat.strongRecOn with
  | ind G IH =>
    intro k g d t st lst hG hd
    have kids : ∀ (f : Nat) {fs : alloc.vec.Vec (Std.U64 × Std.U8 × Bool)} {i : Std.Usize} {d t st lst},
        fs.val.length - i.val ≤ f → SMRel d t →
        TS SMRel pers st lst (kids_go pk pers st.store bs r g fs i d)
          (kidsGo (absPins pk) (absRegion bs r) g.val ((fs.val.drop i.val).map absKid) t) := by
      intro f
      induction f with
      | zero =>
        intro fs i d t st lst hk hd
        rw [kids_go, ite_eq_left (by scalar_tac), List.drop_eq_nil_of_le (by omega), List.map_nil, kidsGo]
        exact TS.leaf hd
      | succ f ih =>
        intro fs i d t st lst hk hd
        rw [kids_go]
        by_cases hi : i >= alloc.vec.Vec.len fs
        · rw [ite_eq_left hi, List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, kidsGo]
          exact TS.leaf hd
        · rw [ite_eq_right hi]
          have hlt : i.val < fs.val.length := by scalar_tac
          refine TS.pure_step fun q hq => ?_
          obtain ⟨a, kk, bb⟩ := q
          obtain ⟨_, he⟩ := List.getElem?_eq_some_iff.mp (ConRon.Refine.ExprOps.vec_index_getElem? hq)
          rw [List.drop_eq_getElem_cons hlt, he, List.map_cons]
          show TS _ _ _ _ _ (kidsGo _ _ _ ((a.val, absByte kk, bb) :: _) t)
          rw [kidsGo]
          refine TS.pure_step fun v hv => ?_
          rw [← region_fld_eq bs hv]
          have next : ∀ {i4 s1 d1 t1 lst1}, i + 1#usize = ok i4 → SMRel d1 t1 →
              TS SMRel pers (withStore st s1) lst1 (kids_go pk pers s1 bs r g fs i4 d1)
                (kidsGo (absPins pk) (absRegion bs r) g.val ((fs.val.drop (i.val + 1)).map absKid) t1) := by
            intro i4 s1 d1 t1 lst1 hi4 h1
            have hiv : i4.val = i.val + 1 := uscalar_add_eq hi4
            rw [← hiv]
            exact ih (st := withStore st s1) (by omega) h1
          cases bb with
          | false =>
            simp only [↓reduceIte, Bool.false_and, Bool.false_eq_true]
            kid_tail
          | true =>
            simp only [↓reduceIte, Bool.true_and]
            by_cases hv1 : v = 1#u64
            · rw [ite_eq_left hv1, ite_eq_left (word_eq_one.mpr hv1)]
              refine TS.pure_step fun i4 hi4 => ?_
              exact next (s1 := st.store) hi4 hd
            · rw [ite_eq_right hv1, ite_eq_right (fun he => hv1 (word_eq_one.mp he))]
              kid_tail
    rw [s_go, sGo]
    refine TS.pure_step fun b hb => ?_
    rw [← sm_has_eq hd hb]
    cases b with
    | true => exact TS.leaf hd
    | false =>
      simp only [↓reduceIte, Bool.false_eq_true]
      refine TS.pure_step fun b1 hb1 => ?_
      rw [← region_fits_eq bs hb1]
      cases b1 with
      | false => exact TS.none
      | true =>
        simp only [↓reduceIte]
        refine TS.pure_step fun i hi => TS.pure_step fun i1 hi1 => TS.pure_step fun o1 ho1 => ?_
        rw [← region_tag_eq bs hi, ← region_nobjs_eq bs hi1, ← kid_table_ks o1 ho1]
        cases o1 with
        | none => exact TS.none
        | some fs =>
          have k0 := kids _ (fs := fs) (i := 0#usize) (st := st) (lst := lst) (Nat.le_refl _) hd
          rw [show (0#usize : Std.Usize).val = 0 by decide, List.drop_zero] at k0
          dsimp only [Option.map_some]
          refine TS.of_eq (TS.bind k0
            (g := fun t1 => ConRon.Arena.Frontend.Olean.SM.build (absPins pk) (absRegion bs r) (absByte k) g.val t1)
            fun s1 d1 t1 lst1 h1 => sm_build_ts hr h1) ?_
          refine congrArg (_ >>= ·) (funext fun w => ?_)
          cases w <;> rfl

/-- **`sparse_name_p` is `sparseNameP`.** -/
theorem sparse_name_p_refines {pk bs r pers st lst} {v : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absNIdx) st lst (sparse_name_p pk pers st.store bs r v)
      (sparseNameP (absPins pk) (absRegion bs r) (absWord v)) := by
  rw [sparse_name_p, sparseNameP]
  by_cases hv : v = 1#u64
  · rw [ite_eq_left hv, ite_eq_left (word_eq_one.mpr hv)]
    refine RS.pure_step fun n hn => ?_
    rw [nidx_dup2_ok hn]
    exact RS.some rfl
  · rw [ite_eq_right hv, ite_eq_right (fun he => hv (word_eq_one.mp he))]
    refine RS.pure_step fun o ho => ?_
    rw [← region_loc_eq bs ho]
    cases o with
    | none => exact RS.none
    | some c =>
      dsimp only [locOf, Option.map_some]
      refine RS.pure_step fun d0 hd0 => ?_
      rw [← absByte_k_name]
      intro hrel hinv o s' hm
      obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
      have hF := s_go_ts (pk := pk) (pers := pers) hr c.val (k := K_NAME) (g := c) (st := st) (lst := lst)
        rfl (sm_empty_rel hd0) hrel hinv r1 ar1 d1 h1
      cases r1 with
      | Ok u =>
        obtain ⟨t1, lst1, hx, hR, h3, h4⟩ := hF
        rw [am_bind_ok hx]
        peel h2 as o1, ho1
        have e := (sm_subrel hR).nm c o1 ho1
        have e' : t1.names[c.val]? = o1.map absNIdx := e.symm
        dsimp only
        rw [e']
        cases o1 with
        | none =>
          cases Result.ok_injective h2
          exact ⟨lst1, rfl, h3, h4⟩
        | some h =>
          cases Result.ok_injective h2
          exact ⟨_, lst1, rfl, rfl, h3, h4⟩
      | Err e =>
        cases Result.ok_injective h2
        cases e with
        | Bad =>
          obtain ⟨lst1, hx, h3, h4⟩ := hF
          rw [am_bind_ok hx]
          exact ⟨lst1, rfl, h3, h4⟩
        | Err e =>
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hF _

/-- **`sparse_expr_p` is `sparseExprP`.** -/
theorem sparse_expr_p_refines {pk bs r pers st lst} {v : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absEIdx) st lst (sparse_expr_p pk pers st.store bs r v)
      (sparseExprP (absPins pk) (absRegion bs r) (absWord v)) := by
  rw [sparse_expr_p, sparseExprP]
  refine RS.pure_step fun o ho => ?_
  rw [← region_loc_eq bs ho]
  cases o with
  | none => exact RS.none
  | some c =>
    dsimp only [locOf, Option.map_some]
    refine RS.pure_step fun d0 hd0 => ?_
    rw [← absByte_k_expr]
    intro hrel hinv o s' hm
    obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hF := s_go_ts (pk := pk) (pers := pers) hr c.val (k := K_EXPR) (g := c) (st := st) (lst := lst)
      rfl (sm_empty_rel hd0) hrel hinv r1 ar1 d1 h1
    cases r1 with
    | Ok u =>
      obtain ⟨t1, lst1, hx, hR, h3, h4⟩ := hF
      rw [am_bind_ok hx]
      peel h2 as o1, ho1
      have e := (sm_subrel hR).ex c o1 ho1
      have e' : t1.exprs[c.val]? = o1.map absEIdx := e.symm
      dsimp only
      rw [e']
      cases o1 with
      | none =>
        cases Result.ok_injective h2
        exact ⟨lst1, rfl, h3, h4⟩
      | some h =>
        cases Result.ok_injective h2
        exact ⟨_, lst1, rfl, rfl, h3, h4⟩
    | Err e =>
      cases Result.ok_injective h2
      cases e with
      | Bad =>
        obtain ⟨lst1, hx, h3, h4⟩ := hF
        rw [am_bind_ok hx]
        exact ⟨lst1, rfl, h3, h4⟩
      | Err e =>
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hF _

/-- **`SparseRead` is the twin's two reads.** -/
theorem sparse_read_rel {pk bs r pers} (hr : RegionFits bs r) :
    PtrRel frontend.olean.sparse.SparseRead.Insts.Con_ron_coreFrontendOleanSpecPtrRead ()
      ⟨sparseNameP (absPins pk) (absRegion bs r), sparseExprP (absPins pk) (absRegion bs r)⟩
      pk bs r pers where
  nm _ _ _ := sparse_name_p_refines hr
  ex _ _ _ := sparse_expr_p_refines hr

/-- **`sparse_entry` is `sparseEntry`.** -/
theorem sparse_entry_refines {pk bs r pers st lst} {c : frontend.olean.spec.CEntryF Std.U64 Std.U64}
    {c' : CEntryF UInt64 UInt64} (hr : RegionFits bs r) (hc : EntryRel absWord absWord ValRel c c') :
    RS pers (EntryRel absNIdx absEIdx ValRel) st lst (sparse_entry pk pers st.store bs r c)
      (sparseEntry (absPins pk) (absRegion bs r) c') := by
  rw [sparse_entry, sparseEntry]
  exact c_entry_map_refines (sparse_read_rel hr) hc st lst

end ConRon.Refine2.Frontend.Olean
