/-
# `ConRon.Refine2.Checker.Basis` — Theorem 2 for `arena::basis`'s renaming half

**Task #143.**  `crates/con-ron-core/src/arena/basis.rs` against
`proof/ConRon/Arena/Basis.lean`, upstream task #480's half: a pinned block or a
quotient record is compared with its pin up to its level-parameter names, and the
environment holds each pin at the names its record declares.  So a pin is renamed
(`constant_info_at_lps`), a block compared copy by copy (`pin_copies_ok`) and link
by link (`block_links_ok`), recognised by its members' names (`basis_name_hit`),
and installed renamed (`basis_kind_at_block`, `quot_at`).

The pure helpers come first: they read nothing but their arguments.  The rest walk
the store through `param_levels`, `inst_lp_fast`, `subst_levels_at` and
`read_names_m`, which is why this file sits above `Inductives/StructParts.lean`.
-/
import ConRon.Refine2.Checker.Axioms
import ConRon.Refine2.Core.LS.Leaves

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The pure helpers -/

/-- `param_level_values` at the cursor: the transient levels `.param p` of the
names from `i` on, after `out`. -/
theorem param_level_values_val {ps : alloc.vec.Vec kernel.name.Name}
    (hps : ∀ n ∈ ps.val, ConRon.Refine.NameWF n) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out o : alloc.vec.Vec kernel.level.Level),
      ps.val.length - i.val ≤ k → (∀ l ∈ out.val, ConRon.Refine.LevelWF l) →
      arena.basis.param_level_values ps i out = ok o →
      o.val.map ConRon.Refine.absLevel = out.val.map ConRon.Refine.absLevel ++
          (ps.val.drop i.val).map (fun n => ConLeche.Level.param (ConRon.Refine.absName n)) ∧
        ∀ l ∈ o.val, ConRon.Refine.LevelWF l := by
  intro k
  induction k with
  | zero =>
    intro i out o hk hout h
    rw [arena.basis.param_level_values.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out o hk hout h
    rw [arena.basis.param_level_values.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ ps.val.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      exact ⟨by simp, hout⟩
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ps by scalar_tac)] at h
      have hlt : i.val < ps.val.length := by omega
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ps i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, ConRon.Refine.name_dup_eq, bind_ok] at h
      obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have hw : ConRon.Refine.NameWF ps.val[i.val] := hps _ (List.getElem_mem hlt)
      have hlw : ConRon.Refine.LevelWF l := ConRon.Refine.Level.param_wf' hl hw
      have hov := ConRon.Refine.vec_push_val hout1
      obtain ⟨ha, hwo⟩ := ih i2 out1 o (by omega) (by
        rw [hov]; intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hout x hx
        · rw [List.mem_singleton.mp hx]; exact hlw) h
      refine ⟨?_, hwo⟩
      rw [ha, hov, hi2v, List.drop_eq_getElem_cons hlt]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append, ConRon.Refine.Level.param_refines hl]

/-- `pin_link_rhs` at the cursor: the cited `Cp.map fun p => Level.subst Rp R (.param p)`
of the names from `i` on, after `out`. -/
theorem pin_link_rhs_val {rp cp : alloc.vec.Vec kernel.name.Name}
    {rs : alloc.vec.Vec kernel.level.Level}
    (hrp : ∀ n ∈ rp.val, ConRon.Refine.NameWF n) (hcp : ∀ n ∈ cp.val, ConRon.Refine.NameWF n)
    (hrs : ∀ l ∈ rs.val, ConRon.Refine.LevelWF l) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out o : alloc.vec.Vec kernel.level.Level),
      cp.val.length - i.val ≤ k → (∀ l ∈ out.val, ConRon.Refine.LevelWF l) →
      arena.basis.pin_link_rhs rp rs cp i out = ok o →
      o.val.map ConRon.Refine.absLevel = out.val.map ConRon.Refine.absLevel ++
          (cp.val.drop i.val).map (fun p => ConLeche.Level.subst
            (rp.val.map ConRon.Refine.absName) (rs.val.map ConRon.Refine.absLevel)
            (.param (ConRon.Refine.absName p))) ∧
        ∀ l ∈ o.val, ConRon.Refine.LevelWF l := by
  intro k
  induction k with
  | zero =>
    intro i out o hk hout h
    rw [arena.basis.pin_link_rhs.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len cp by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out o hk hout h
    rw [arena.basis.pin_link_rhs.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cp.val.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len cp by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      exact ⟨by simp, hout⟩
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cp by scalar_tac)] at h
      have hlt : i.val < cp.val.length := by omega
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cp i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, ConRon.Refine.name_dup_eq, bind_ok] at h
      obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨l1, hl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have hw : ConRon.Refine.NameWF cp.val[i.val] := hcp _ (List.getElem_mem hlt)
      have hlw : ConRon.Refine.LevelWF l := ConRon.Refine.Level.param_wf' hl hw
      obtain ⟨hs1, hw1⟩ := ConRon.Refine.Level.subst_refines hlw hrp hrs hl1
      have hov := ConRon.Refine.vec_push_val hout1
      obtain ⟨ha, hwo⟩ := ih i2 out1 o (by omega) (by
        rw [hov]; intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hout x hx
        · rw [List.mem_singleton.mp hx]; exact hw1) h
      refine ⟨?_, hwo⟩
      rw [ha, hov, hi2v, List.drop_eq_getElem_cons hlt]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append, hs1, ConRon.Refine.Level.param_refines hl]

/-- `level_list_beq` at the cursor: the two lists' tails from `i` are equal. -/
theorem level_list_beq_refines {a b : alloc.vec.Vec kernel.level.Level}
    (ha : ∀ l ∈ a.val, ConRon.Refine.LevelWF l) (hb : ∀ l ∈ b.val, ConRon.Refine.LevelWF l) :
    ∀ k : Nat, ∀ (i : Std.Usize) (o : Bool), a.val.length - i.val ≤ k →
      arena.basis.level_list_beq a b i = ok o →
      o = decide ((a.val.drop i.val).map ConRon.Refine.absLevel =
        (b.val.drop i.val).map ConRon.Refine.absLevel) := by
  intro k
  induction k with
  | zero =>
    intro i o hk h
    rw [arena.basis.level_list_beq.eq_def] at h; simp only [] at h
    have hal : a.val.length ≤ i.val := by omega
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le hal]
    by_cases hbl : b.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len b by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le hbl]; rfl
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac),
        ite_eq_left (show i ≥ alloc.vec.Vec.len a by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_getElem_cons (Nat.lt_of_not_le hbl)]; simp
      all_goals exact Nat.lt_of_not_le hbl
  | succ k ih =>
    intro i o hk h
    rw [arena.basis.level_list_beq.eq_def] at h; simp only [] at h
    by_cases hal : a.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le hal]
      by_cases hbl : b.val.length ≤ i.val
      · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len b by scalar_tac), Result.ok.injEq] at h
        subst h
        rw [List.drop_eq_nil_of_le hbl]; rfl
      · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac),
          ite_eq_left (show i ≥ alloc.vec.Vec.len a by scalar_tac), Result.ok.injEq] at h
        subst h
        rw [List.drop_eq_getElem_cons (Nat.lt_of_not_le hbl)]; simp
        all_goals exact Nat.lt_of_not_le hbl
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac),
        ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      have hla : i.val < a.val.length := Nat.lt_of_not_le hal
      by_cases hbl : b.val.length ≤ i.val
      · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len b by scalar_tac), Result.ok.injEq] at h
        subst h
        rw [List.drop_eq_nil_of_le hbl, List.drop_eq_getElem_cons hla]; simp
        all_goals exact hla
      · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len b by scalar_tac)] at h
        have hlb : i.val < b.val.length := Nat.lt_of_not_le hbl
        obtain ⟨x, hx, hxv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec a i hla)
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b i hlb)
        subst hxv hyv
        simp only [alloc.vec.Vec.index_slice_index, hx, hy, bind_ok] at h
        obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hcv := ConRon.Refine.Level.beq_refines (ha _ (List.getElem_mem hla))
          (hb _ (List.getElem_mem hlb)) hc
        rw [List.drop_eq_getElem_cons hla, List.drop_eq_getElem_cons hlb]
        simp only [List.map_cons, List.cons.injEq]
        cases c with
        | false =>
          simp only [Bool.false_eq_true, ite_false, Result.ok.injEq] at h
          subst h
          have hne : ¬ ConRon.Refine.absLevel a.val[i.val] = ConRon.Refine.absLevel b.val[i.val] :=
            of_decide_eq_false hcv.symm
          simp [hne]
        | true =>
          simp only [ite_true] at h
          have heq : ConRon.Refine.absLevel a.val[i.val] = ConRon.Refine.absLevel b.val[i.val] :=
            of_decide_eq_true hcv.symm
          have hmax : i.val + 1 ≤ Std.Usize.max := by have := a.slice.property; scalar_tac
          obtain ⟨w, hw, hwv⟩ := ConRon.Refine.usize_add_ok hmax
          rw [hw, bind_ok] at h
          rw [ih w o (by omega) h, hwv]
          simp [heq]

/-- `const_named` ⊑ `constNamed?`, at the cursor: the first constant of the list
from `i` on that carries the name, copied. -/
theorem const_named_refines {cs : alloc.vec.Vec arena.env.IConstantInfo} {n : arena.handle.NIdx} :
    ∀ k : Nat, ∀ (i : Std.Usize) (o : Option arena.env.IConstantInfo),
      cs.val.length - i.val ≤ k →
      arena.basis.const_named cs n i = ok o →
      o.map absIConstantInfo = constNamed? (absICILFrom cs i) (absNIdx n) := by
  intro k
  induction k with
  | zero =>
    intro i o hk h
    rw [arena.basis.const_named.eq_def] at h; simp only [] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    subst h
    simp only [absICILFrom]
    rw [List.drop_eq_nil_of_le (by scalar_tac)]; rfl
  | succ k ih =>
    intro i o hk h
    rw [arena.basis.const_named.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ cs.val.length
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
      subst h
      simp only [absICILFrom]
      rw [List.drop_eq_nil_of_le (by scalar_tac)]; rfl
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hlt : i.val < cs.val.length := by omega
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_ok] at h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hname := i_constant_info_name_abs hn1
      have hbv := nidx_eq2_abs hb
      have hcons : absICILFrom cs i = absIConstantInfo cs.val[i.val] ::
          (cs.val.drop (i.val + 1)).map absIConstantInfo := by
        simp only [absICILFrom]; rw [List.drop_eq_getElem_cons hlt]; rfl
      rw [hcons, constNamed?, List.find?_cons]
      cases b with
      | true =>
        simp only [ite_true] at h
        obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain rfl := (Result.ok_injective h).symm
        rw [← hname, ← hbv]
        simp [i_constant_info_dup_abs hc]
      | false =>
        simp only [Bool.false_eq_true, ite_false] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        rw [← hname, ← hbv]
        rw [ih i2 o (by omega) h]
        simp only [absICILFrom, hi2v, constNamed?]

/-- `pin_agrees` ⊑ `pinAgrees`: an inductive record against an inductive pin
compares the common data only. -/
theorem pin_agrees_refines {c c2 : arena.env.IConstantInfo} {o : Bool}
    (h : arena.basis.pin_agrees c c2 = ok o) :
    o = pinAgrees (absIConstantInfo c) (absIConstantInfo c2) := by
  cases c <;> cases c2 <;> simp only [arena.basis.pin_agrees] at h <;>
    first
    | (rw [i_constant_val_beq_refines h]; simp [pinAgrees, absIConstantInfo, beq_eq_decide])
    | (rw [i_constant_info_beq_refines h]; simp [pinAgrees, absIConstantInfo, beq_eq_decide])

/-- `param_level_values` from its entry: `ps.map Level.param`. -/
theorem param_level_values_entry {ps : alloc.vec.Vec kernel.name.Name}
    (hps : ∀ n ∈ ps.val, ConRon.Refine.NameWF n) {o : alloc.vec.Vec kernel.level.Level}
    (h : arena.basis.param_level_values ps 0#usize (alloc.vec.Vec.new _) = ok o) :
    o.val.map ConRon.Refine.absLevel = (ConRon.Refine.absNames ps).map ConLeche.Level.param ∧
      ∀ l ∈ o.val, ConRon.Refine.LevelWF l := by
  obtain ⟨ha, hw⟩ := param_level_values_val hps _ 0#usize _ o (le_refl _)
    (fun _ hl => by simp [alloc.vec.Vec.new] at hl) h
  refine ⟨?_, hw⟩
  rw [ha]
  simp [alloc.vec.Vec.new, ConRon.Refine.absNames]

/-! ## A recursor's link to its constructors -/

open Lockstep in
/-- `pin_link_ok` ⊑ `pinLinkOk`: four name reads, then the constructor's
parameters against the pin's at the recursor's names, on read-back levels. -/
@[lockstep] theorem pin_link_ok_ls {pers st lst}
    {r rp c cp : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.basis.pin_link_ok pers st r rp c cp) lst
      (pinLinkOk (r.val.map absNIdx) (rp.val.map absNIdx) (c.val.map absNIdx)
        (cp.val.map absNIdx)) := by
  rw [arena.basis.pin_link_ok]
  unfold pinLinkOk
  refine LS.bind (read_names_m_ls hrel hinv r) rfl (fun _ _ => errArm_ok) ?_
  intro rT b1 st1 lst1 ⟨w1, hb1⟩ hrel1 hinv1
  subst hb1
  refine LS.bind (read_names_m_ls hrel1 hinv1 rp) rfl (fun _ _ => errArm_ok) ?_
  intro rpT b2 st2 lst2 ⟨w2, hb2⟩ hrel2 hinv2
  subst hb2
  refine LS.bind (read_names_m_ls hrel2 hinv2 c) rfl (fun _ _ => errArm_ok) ?_
  intro cT b3 st3 lst3 ⟨w3, hb3⟩ hrel3 hinv3
  subst hb3
  refine LS.bind (read_names_m_ls hrel3 hinv3 cp) rfl (fun _ _ => errArm_ok) ?_
  intro cpT b4 st4 lst4 ⟨w4, hb4⟩ hrel4 hinv4
  subst hb4
  refine LS.bind_eq fun rs hrs => ?_
  refine LS.bind_eq fun lhs hlhs => ?_
  refine LS.bind_eq fun rhs hrhs => ?_
  refine LS.bind_eq fun b hb => ?_
  obtain ⟨ars, wrs⟩ := param_level_values_entry w1 hrs
  obtain ⟨alhs, wlhs⟩ := param_level_values_entry w3 hlhs
  obtain ⟨arhs, wrhs⟩ := pin_link_rhs_val w2 w4 wrs _ 0#usize _ rhs (le_refl _)
    (fun _ hl => by simp [alloc.vec.Vec.new] at hl) hrhs
  have hbv := level_list_beq_refines wlhs wrhs _ 0#usize b (le_refl _) hb
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hbv arhs
  refine LS.pure ?_ hrel4 hinv4
  rw [hbv, alhs, arhs, ars]
  simp only [alloc.vec.Vec.new, ConRon.Refine.absNames,
    List.map_map, id]
  cases h : (List.map (ConLeche.Level.param ∘ ConRon.Refine.absName) cT.val ==
      List.map (fun p => ConLeche.Level.subst (List.map ConRon.Refine.absName rpT.val)
        (List.map (ConLeche.Level.param ∘ ConRon.Refine.absName) rT.val)
        (ConLeche.Level.param (ConRon.Refine.absName p))) cpT.val) <;> simp_all [Function.comp_def]

open Lockstep in
private theorem rules_link_ok_aux {block pins : alloc.vec.Vec arena.env.IConstantInfo}
    {r rp : alloc.vec.Vec arena.handle.NIdx} {rules : alloc.vec.Vec arena.env.IRecRule}
    (k : Nat) :
    ∀ {pers st lst} (i : Std.Usize), rules.val.length - i.val = k →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = id a)
        (arena.basis.rules_link_ok pers st block pins r rp rules i) lst
        (rulesLinkOk (absICIL block) (absICIL pins) (r.val.map absNIdx) (rp.val.map absNIdx)
          ((rules.val.drop i.val).map absIRecRule)) := by
  induction k with
  | zero =>
    intro pers st lst i hk hrel hinv
    rw [arena.basis.rules_link_ok.eq_def]; simp only []
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len rules by scalar_tac),
      List.drop_eq_nil_of_le (by omega)]
    exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst i hk hrel hinv
    have hlt : i.val < rules.val.length := by omega
    rw [arena.basis.rules_link_ok.eq_def]; simp only []
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rules by scalar_tac),
      List.drop_eq_getElem_cons hlt]
    obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rules i hlt)
    subst hyv
    rw [alloc.vec.Vec.index_slice_index, hy, bind_ok]
    simp only [List.map_cons, rulesLinkOk]
    have hc : (absIRecRule rules.val[i.val]).ctor = absNIdx rules.val[i.val].ctor := rfl
    rw [hc]
    refine LS.bind_eq fun o ho => ?_
    have hco := const_named_refines _ 0#usize o (le_refl _) ho
    simp only [absICILFrom, show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hco
    refine LS.bind_eq fun lps hlps => ?_
    cases o with
    | none =>
      simp only [Result.ok.injEq] at hlps
      subst hlps
      rw [show constNamed? (absICIL block) (absNIdx rules.val[i.val].ctor) = none from hco.symm]
      exact LS.pure rfl hrel hinv
    | some cc =>
      simp only [] at hlps
      obtain ⟨o1, ho1, hlps⟩ := ConRon.Refine.bind_eq_ok_iff.mp hlps
      have hco1 := const_named_refines _ 0#usize o1 (le_refl _) ho1
      simp only [absICILFrom, show (0#usize : Std.Usize).val = 0 from rfl,
        List.drop_zero] at hco1
      rw [show constNamed? (absICIL block) (absNIdx rules.val[i.val].ctor)
        = some (absIConstantInfo cc) from hco.symm]
      cases o1 with
      | none =>
        simp only [Result.ok.injEq] at hlps
        subst hlps
        rw [show constNamed? (absICIL pins) (absNIdx rules.val[i.val].ctor) = none from hco1.symm]
        exact LS.pure rfl hrel hinv
      | some ccp =>
        simp only [] at hlps
        obtain ⟨iv, hiv, hlps⟩ := ConRon.Refine.bind_eq_ok_iff.mp hlps
        obtain ⟨iv1, hiv1, hlps⟩ := ConRon.Refine.bind_eq_ok_iff.mp hlps
        simp only [Result.ok.injEq] at hlps
        subst hlps
        rw [show constNamed? (absICIL pins) (absNIdx rules.val[i.val].ctor)
          = some (absIConstantInfo ccp) from hco1.symm]
        have e1 : (absIConstantInfo cc).toConstantVal.levelParams = iv.level_params.val.map absNIdx := by
          rw [← i_constant_info_to_constant_val_abs hiv]; rfl
        have e2 : (absIConstantInfo ccp).toConstantVal.levelParams = iv1.level_params.val.map absNIdx := by
          rw [← i_constant_info_to_constant_val_abs hiv1]; rfl
        simp only [e1, e2]
        refine LS.bind (pin_link_ok_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
        intro a b st1 lst1 hab hrel1 hinv1
        cases a with
        | false =>
          simp only [id] at hab; subst hab
          exact LS.pure rfl hrel1 hinv1
        | true =>
          simp only [id] at hab; subst hab
          simp only [ite_true]
          refine LS.bind_eq fun i2 hi2 => ?_
          have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
          have h := ih i2 (by omega) hrel1 hinv1
          rw [hi2v] at h
          exact h

open Lockstep in
/-- `rules_link_ok` ⊑ `rulesLinkOk` from its entry: each of the pin's rules'
constructors, found in both lists, linked as the pin links it. -/
@[lockstep] theorem rules_link_ok_ls {pers st lst}
    {block pins : alloc.vec.Vec arena.env.IConstantInfo}
    {r rp : alloc.vec.Vec arena.handle.NIdx} {rules : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.basis.rules_link_ok pers st block pins r rp rules 0#usize) lst
      (rulesLinkOk (absICIL block) (absICIL pins) (r.val.map absNIdx) (rp.val.map absNIdx)
        (rules.val.map absIRecRule)) := by
  have h := rules_link_ok_aux (block := block) (pins := pins) (r := r) (rp := rp)
    (rules := rules) _ 0#usize rfl
    hrel hinv
  simpa using h

/-! ## A pin at a stream's level-parameter names -/

open Lockstep in
/-- `rec_rule_fire_at_lps` ⊑ `IRecRuleFire.atLps`: a `.levels` firing mode's
comparands substituted, every other mode copied. -/
@[lockstep] theorem rec_rule_fire_at_lps_ls {pers st lst}
    {lps : alloc.vec.Vec kernel.name.Name} {us : alloc.vec.Vec kernel.level.Level}
    {f : arena.env.IRecRuleFire}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hks : ConRon.Refine.NamesWF lps) (hvs : ConRon.Refine.LevelsWF us) :
    LS pers (fun a b => b = absIRecRuleFire a) (arena.basis.rec_rule_fire_at_lps pers st lps us f)
      lst ((absIRecRuleFire f).atLps (ConRon.Refine.absNames lps) (ConRon.Refine.absLevels us)) := by
  rw [arena.basis.rec_rule_fire_at_lps.eq_def]
  cases f with
  | Plain =>
    refine LS.bind_eq fun a ha => ?_
    have h1 := i_rec_rule_fire_dup_abs ha
    simp only [absIRecRuleFire, IRecRuleFire.atLps] at h1 ⊢
    exact LS.pure h1.symm hrel hinv
  | Nested l p =>
    refine LS.bind_eq fun a ha => ?_
    have h1 := i_rec_rule_fire_dup_abs ha
    simp only [absIRecRuleFire, IRecRuleFire.atLps] at h1 ⊢
    exact LS.pure h1.symm hrel hinv
  | Levels lvls =>
    simp only [absIRecRuleFire, IRecRuleFire.atLps]
    refine LS.bind (subst_levels_at_ls hrel hinv hks hvs) rfl (fun _ _ => errArm_ok) ?_
    intro a b st1 lst1 hR hrel1 hinv1
    subst hR
    exact LS.pure rfl hrel1 hinv1

/-! ## What a quotient record's slot needs stored before it -/

attribute [local lockstep_simp] Option.isSome_map core.option.Option.is_some

open Lockstep in
/-- `quot_preds_ok` ⊑ `quotPredsOk`: three pin reads and three lookups, read off
the slot. -/
@[lockstep] theorem quot_preds_ok_ls {pers st lst} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers fe lfe) {k : kernel.env.QuotKind}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.basis.quot_preds_ok pers st fe k) st lst
      (quotPredsOk lfe (ConRon.Refine.absQuotKind k)) := by
  refine LSR.of_LS ?_
  rw [arena.basis.quot_preds_ok]
  unfold quotPredsOk
  cases k <;> simp only [ConRon.Refine.absQuotKind] <;> lockstep

end ConRon.Refine2
