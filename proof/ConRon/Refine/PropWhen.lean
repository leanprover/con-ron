/-
`ConRon.Refine.PropWhen` -- the refinement lemmas of
`crates/con-ron-core/src/kernel/prop_when.rs` against
`ConLeche/Kernel/PropWhen.lean` (DESIGN.md §3.5).

**Task #119: the plain datum.**  con-leche's task #342 (S5A) replaced the
sealed, canonical five-constructor `PropWhen` (and its name order, `merge`,
`canon`, hash) by the plain `never | ifAllZero (ps : List Name)`, kept
uncanonicalised; the port followed.  `absPropWhen` (`Abs.lean`) is
constructor to constructor, `PropWhenWF` is "the names are well formed", and
every lemma below is exact: the abstraction is injective on well-formed data
because `absName` is.  The string order (`str_compare`) and name order
(`name_cmp`) this file used to refine went with the canonical form.
-/
import ConRon.Refine.Name

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.PropWhen

/-! ## The `List Name` helpers -/

theorem append_from_val (xs : alloc.vec.Vec name.Name) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec name.Name),
      xs.length - i.val ≤ k → prop_when.append_from xs i out = ok v →
      v.val = out.val ++ xs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out v hk h
    rw [prop_when.append_from.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    simp only [Result.ok.injEq] at h; subst h
    rw [List.drop_eq_nil_of_le (show xs.val.length ≤ i.val by scalar_tac)]
    simp
  | succ k ih =>
    intro i out v hk h
    rw [prop_when.append_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ xs.val.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_nil_of_le (show xs.val.length ≤ i.val by scalar_tac)]
      simp
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hi : i.val < xs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := xs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw, name_dup_eq,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨out1, hout1, h⟩ := h
      rw [ih w out1 v (by scalar_tac) h, vec_push_val hout1,
        List.drop_eq_getElem_cons hi, hwv]
      simp

theorem names_copy_val {xs v : alloc.vec.Vec name.Name}
    (h : prop_when.names_copy xs = ok v) : v.val = xs.val := by
  rw [prop_when.names_copy] at h
  have hv := append_from_val xs xs.length 0#usize _ v (by scalar_tac) h
  simpa [alloc.vec.Vec.new] using hv

theorem names_copy_wf {xs v : alloc.vec.Vec name.Name} (hxs : NamesWF xs)
    (h : prop_when.names_copy xs = ok v) : NamesWF v := by
  intro n hn; rw [names_copy_val h] at hn; exact hxs n hn

theorem names_copy_abs {xs v : alloc.vec.Vec name.Name}
    (h : prop_when.names_copy xs = ok v) : absNames v = absNames xs := by
  simp [absNames, names_copy_val h]

/-! ## `dup` -/

theorem dup_eq {pw c : prop_when.PropWhen} (h : prop_when.dup pw = ok c) : c = pw := by
  cases pw with
  | Never => simp only [prop_when.dup, Result.ok.injEq] at h; exact h.symm
  | IfAllZero ps =>
    simp only [prop_when.dup, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h
    rw [alloc.vec.Vec.ext _ _ (names_copy_val hv)]

/-! ## Injectivity -/

theorem names_map_inj : ∀ {l m : List name.Name}, (∀ n ∈ l, NameWF n) →
    (∀ n ∈ m, NameWF n) → l.map absName = m.map absName → l = m
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: l, y :: m, hl, hm, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Name.absName_injective (hl x (by simp)) (hm y (by simp)) h.1,
      names_map_inj (l := l) (m := m) (fun n hn => hl n (by simp [hn]))
        (fun n hn => hm n (by simp [hn])) h.2]

theorem absNames_injective {l m : alloc.vec.Vec name.Name} (hl : NamesWF l) (hm : NamesWF m)
    (h : absNames l = absNames m) : l = m :=
  alloc.vec.Vec.ext _ _ (names_map_inj hl hm h)

theorem absPropWhen_injective {a b : prop_when.PropWhen}
    (ha : PropWhenWF a) (hb : PropWhenWF b) (hab : absPropWhen a = absPropWhen b) :
    a = b := by
  cases a <;> cases b <;> simp_all [absPropWhen, PropWhenWF]
  exact absNames_injective ha hb hab

/-! ## `beq` -/

theorem names_beq_from_refines {ps qs : alloc.vec.Vec name.Name}
    (hps : NamesWF ps) (hqs : NamesWF qs) (hlen : ps.val.length = qs.val.length) :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), ps.length - i.val ≤ k →
      prop_when.names_beq_from ps qs i = ok b →
      (b = true ↔ ps.val.drop i.val = qs.val.drop i.val) := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [prop_when.names_beq_from.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac),
      List.drop_eq_nil_of_le (show qs.val.length ≤ i.val by scalar_tac)]
    simp
  | succ k ih =>
    intro i b hk h
    rw [prop_when.names_beq_from.eq_def] at h; simp only [] at h
    by_cases hp : i.val ≥ ps.val.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (show ps.val.length ≤ i.val by scalar_tac),
        List.drop_eq_nil_of_le (show qs.val.length ≤ i.val by scalar_tac)]
      simp
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hpi : i.val < ps.val.length := by scalar_tac
      have hqi : i.val < qs.val.length := by scalar_tac
      rw [List.drop_eq_getElem_cons hpi, List.drop_eq_getElem_cons hqi]
      have hwfp : NameWF ps.val[i.val] := hps _ (List.getElem_mem hpi)
      have hwfq : NameWF qs.val[i.val] := hqs _ (List.getElem_mem hqi)
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hpi)
      obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec qs i hqi)
      subst hyv; subst hzv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b1, hb1, h⟩ := h
      have e1 := Name.name_beq_exact' hwfp hwfq hb1
      split at h
      · rename_i hbt
        have heq : ps.val[i.val] = qs.val[i.val] :=
          Name.absName_injective hwfp hwfq (of_decide_eq_true (e1.symm.trans hbt))
        simp only [hw, bind_ok] at h
        rw [← hwv, ih w b (by scalar_tac) h]
        simp [heq]
      · rename_i hbf
        simp only [Result.ok.injEq] at h
        subst h
        have hne : ¬ absName ps.val[i.val] = absName qs.val[i.val] :=
          of_decide_eq_false (e1.symm.trans (by simpa using hbf))
        simp only [Bool.false_eq_true, false_iff, List.cons.injEq, not_and]
        exact fun hc _ => hne (by rw [hc])

theorem names_beq_refines {ps qs : alloc.vec.Vec name.Name} {b : Bool}
    (hps : NamesWF ps) (hqs : NamesWF qs) (h : prop_when.names_beq ps qs = ok b) :
    b = decide (absNames ps = absNames qs) := by
  rw [prop_when.names_beq] at h
  split at h
  · rename_i hlen
    have hl : ps.val.length = qs.val.length := by scalar_tac
    have := names_beq_from_refines hps hqs hl ps.length 0#usize b (by scalar_tac) h
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
    have hiff : absNames ps = absNames qs ↔ ps.val = qs.val :=
      ⟨fun he => names_map_inj hps hqs he, fun he => by simp [absNames, he]⟩
    cases b <;> simp_all
  · rename_i hlen
    simp only [Result.ok.injEq] at h; subst h
    symm; simp only [decide_eq_false_iff_not]
    intro he
    apply hlen
    have := congrArg List.length he
    simp [absNames] at this; scalar_tac

/-- `prop_when::beq` -- and the `Eq2` dictionary that *is* it -- decides
equality of the abstracted data exactly. -/
theorem beq_refines {a b : prop_when.PropWhen} {c : Bool} (ha : PropWhenWF a) (hb : PropWhenWF b)
    (h : prop_when.beq a b = ok c) : c = decide (absPropWhen a = absPropWhen b) := by
  cases a <;> cases b <;> simp only [prop_when.beq, Result.ok.injEq] at h <;> subst_vars
    <;> simp [absPropWhen]
  exact names_beq_refines ha hb h

/-! ## The constructors and readers -/

theorem never_wf {pw} (h : prop_when.never = ok pw) : PropWhenWF pw := by
  simp only [prop_when.never, Result.ok.injEq] at h; subst h; trivial

theorem if_all_zero_wf {ps pw} (hps : NamesWF ps) (h : prop_when.if_all_zero ps = ok pw) :
    PropWhenWF pw := by
  simp only [prop_when.if_all_zero, Result.ok.injEq] at h; subst h; exact hps

/-- `prop_when::never` refines `PropWhen.never`. -/
theorem never_refines {pw} (h : prop_when.never = ok pw) :
    absPropWhen pw = ConLeche.PropWhen.never := by
  simp only [prop_when.never, Result.ok.injEq] at h; subst h; rfl

/-- `prop_when::if_all_zero` refines `PropWhen.ifAllZero`. -/
theorem if_all_zero_refines {ps pw} (h : prop_when.if_all_zero ps = ok pw) :
    absPropWhen pw = ConLeche.PropWhen.ifAllZero (absNames ps) := by
  simp only [prop_when.if_all_zero, Result.ok.injEq] at h; subst h; rfl

/-- `prop_when::is_never` refines `PropWhen.isNever`. -/
theorem is_never_refines {pw b} (h : prop_when.is_never pw = ok b) :
    b = ConLeche.PropWhen.isNever (absPropWhen pw) := by
  cases pw <;> simp only [prop_when.is_never, Result.ok.injEq] at h <;> subst h <;> rfl

/-- `prop_when::inter` refines `PropWhen.inter`, and preserves well-formedness. -/
theorem inter_refines {a b c} (ha : PropWhenWF a) (hb : PropWhenWF b)
    (h : prop_when.inter a b = ok c) :
    absPropWhen c = ConLeche.PropWhen.inter (absPropWhen a) (absPropWhen b) ∧ PropWhenWF c := by
  cases a with
  | Never =>
    simp only [prop_when.inter, Result.ok.injEq] at h; subst h
    exact ⟨rfl, trivial⟩
  | IfAllZero ps =>
    cases b with
    | Never =>
      simp only [prop_when.inter, Result.ok.injEq] at h; subst h
      exact ⟨rfl, trivial⟩
    | IfAllZero qs =>
      simp only [prop_when.inter, bind_eq_ok_iff] at h
      obtain ⟨v, hv, v1, hv1, h⟩ := h
      simp only [Result.ok.injEq] at h; subst h
      have hval := append_from_val qs qs.length 0#usize v v1 (by scalar_tac) hv1
      rw [names_copy_val hv] at hval
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hval
      refine ⟨?_, ?_⟩
      · simp [absPropWhen, ConLeche.PropWhen.inter, absNames, hval]
      · intro n hn
        rw [hval, List.mem_append] at hn
        rcases hn with hn | hn
        · exact ha n hn
        · exact hb n hn

/-! ## `bind_z`

`bindZ`'s `f : Name → PropWhen` argument is a one-method trait dictionary in
the port (task #9, pattern 1); the hypothesis `hf` relates the dictionary to
the Lean function `Φ`. -/

theorem bind_z_go_from_refines {F : Type} {inst : prop_when.NameToPw F} {f : F}
    {ps : alloc.vec.Vec name.Name} (hps : NamesWF ps)
    (Φ : ConLeche.Name → ConLeche.PropWhen)
    (hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r →
      absPropWhen r = Φ (absName n) ∧ PropWhenWF r) :
    ∀ k : Nat, ∀ (i : Std.Usize) (c : prop_when.PropWhen), ps.length - i.val ≤ k →
      prop_when.bind_z_go_from inst f ps i = ok c →
      absPropWhen c = ConLeche.PropWhen.bindZ.go Φ ((ps.val.drop i.val).map absName)
        ∧ PropWhenWF c := by
  have hnil : ∀ (i : Std.Usize) (c : prop_when.PropWhen), ps.val.length ≤ i.val →
      prop_when.if_all_zero (alloc.vec.Vec.new name.Name) = ok c →
      absPropWhen c = ConLeche.PropWhen.bindZ.go Φ ((ps.val.drop i.val).map absName)
        ∧ PropWhenWF c := by
    intro i c hle h
    simp only [prop_when.if_all_zero, Result.ok.injEq] at h; subst h
    rw [List.drop_eq_nil_of_le hle]
    refine ⟨by simp [absPropWhen, absNames, alloc.vec.Vec.new, ConLeche.PropWhen.bindZ.go], ?_⟩
    intro n hn; simp [alloc.vec.Vec.new] at hn
  intro k
  induction k with
  | zero =>
    intro i c hk h
    rw [prop_when.bind_z_go_from.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
    exact hnil i c (by scalar_tac) h
  | succ k ih =>
    intro i c hk h
    rw [prop_when.bind_z_go_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ ps.val.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      exact hnil i c (by scalar_tac) h
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hi : i.val < ps.val.length := by scalar_tac
      have hwf : NameWF ps.val[i.val] := hps _ (List.getElem_mem hi)
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ps.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨r, hr, c1, hc1, h⟩ := h
      obtain ⟨hrabs, hrwf⟩ := hf _ hwf r hr
      obtain ⟨hc1abs, hc1wf⟩ := ih w c1 (by scalar_tac) hc1
      obtain ⟨habs, hwfc⟩ := inter_refines hrwf hc1wf h
      refine ⟨?_, hwfc⟩
      rw [habs, hrabs, hc1abs, hwv, List.drop_eq_getElem_cons hi, List.map_cons,
        ConLeche.PropWhen.bindZ.go]

/-- `prop_when::bind_z` refines `PropWhen.bindZ`.  `hf` is the hypothesis that
the port's `NameToPw` dictionary computes con-leche's `Φ : Name → PropWhen`. -/
theorem bind_z_refines {F : Type} {inst : prop_when.NameToPw F} {f : F} {pw c}
    (Φ : ConLeche.Name → ConLeche.PropWhen)
    (hf : ∀ n, NameWF n → ∀ r, inst.apply f n = ok r →
      absPropWhen r = Φ (absName n) ∧ PropWhenWF r)
    (hpw : PropWhenWF pw) (h : prop_when.bind_z inst f pw = ok c) :
    absPropWhen c = ConLeche.PropWhen.bindZ Φ (absPropWhen pw) ∧ PropWhenWF c := by
  cases pw with
  | Never =>
    simp only [prop_when.bind_z, Result.ok.injEq] at h; subst h
    exact ⟨rfl, trivial⟩
  | IfAllZero ps =>
    simp only [prop_when.bind_z, prop_when.bind_z_go] at h
    obtain ⟨habs, hwf⟩ := bind_z_go_from_refines hpw Φ hf ps.length 0#usize c (by scalar_tac) h
    refine ⟨?_, hwf⟩
    rw [habs]
    simp [absPropWhen, absNames, show (0#usize : Std.Usize).val = 0 from rfl]

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.PropWhen.inter_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inter_refines

/--
info: 'ConRon.Refine.PropWhen.bind_z_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bind_z_refines

/--
info: 'ConRon.Refine.PropWhen.beq_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms beq_refines

end ConRon.Refine.PropWhen
