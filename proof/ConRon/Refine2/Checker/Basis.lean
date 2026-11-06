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
import ConRon.Refine2.Checker.Base
import ConRon.Refine2.Inductives.StructParts

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

open Lockstep in
/-- `block_link_ok_at` ⊑ `blockLinkOkAt`: a constructor carries its former's
names; a recursor against the pin's recursor links its rules. -/
@[lockstep] theorem block_link_ok_at_ls {pers st lst}
    {block pins : alloc.vec.Vec arena.env.IConstantInfo}
    {former : alloc.vec.Vec arena.handle.NIdx} {c p : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.basis.block_link_ok_at pers st block pins former c p) lst
      (blockLinkOkAt (absICIL block) (absICIL pins) (former.val.map absNIdx)
        (absIConstantInfo c) (absIConstantInfo p)) := by
  rw [arena.basis.block_link_ok_at.eq_def]
  cases c <;> cases p <;> simp only [absIConstantInfo, blockLinkOkAt] <;>
    first
    | exact LS.pure rfl hrel hinv
    | exact rules_link_ok_ls hrel hinv
    | (refine LS.bind_eq fun b hb => ?_
       rw [nidx_vec_beq_spec _ _ b hb]
       exact LS.pure rfl hrel hinv)

open Lockstep in
private theorem block_links_ok_go_aux {block pins : alloc.vec.Vec arena.env.IConstantInfo}
    {former : alloc.vec.Vec arena.handle.NIdx} (k : Nat) :
    ∀ {pers st lst} (i : Std.Usize), block.val.length - i.val = k →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = id a)
        (arena.basis.block_links_ok_go pers st block pins former i) lst
        (blockLinksOkGo (absICIL block) (absICIL pins) (former.val.map absNIdx)
          (absICILFrom block i) (absICILFrom pins i)) := by
  induction k with
  | zero =>
    intro pers st lst i hk hrel hinv
    rw [arena.basis.block_links_ok_go.eq_def]; simp only []
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len block by scalar_tac)]
    have : absICILFrom block i = [] := by
      simp only [absICILFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [this]
    exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst i hk hrel hinv
    have hlt : i.val < block.val.length := by omega
    rw [arena.basis.block_links_ok_go.eq_def]; simp only []
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)]
    have hb : absICILFrom block i = absIConstantInfo block.val[i.val] ::
        (block.val.drop (i.val + 1)).map absIConstantInfo := by
      simp only [absICILFrom]; rw [List.drop_eq_getElem_cons hlt]; rfl
    rw [hb]
    by_cases hpl : pins.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len pins by scalar_tac)]
      have : absICILFrom pins i = [] := by
        simp only [absICILFrom]; rw [List.drop_eq_nil_of_le hpl]; rfl
      rw [this]
      exact LS.pure rfl hrel hinv
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len pins by scalar_tac)]
      have hlp : i.val < pins.val.length := Nat.lt_of_not_le hpl
      have hp : absICILFrom pins i = absIConstantInfo pins.val[i.val] ::
          (pins.val.drop (i.val + 1)).map absIConstantInfo := by
        simp only [absICILFrom]; rw [List.drop_eq_getElem_cons hlp]; rfl
      rw [hp]
      obtain ⟨x, hx, hxv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlt)
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlp)
      subst hxv hyv
      rw [alloc.vec.Vec.index_slice_index, hx, bind_ok, alloc.vec.Vec.index_slice_index, hy,
        bind_ok]
      simp only [blockLinksOkGo]
      refine LS.bind (block_link_ok_at_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
      intro a b st1 lst1 hab hrel1 hinv1
      cases a with
      | false =>
        simp only [id] at hab; subst hab
        exact LS.pure rfl hrel1 hinv1
      | true =>
        simp only [id] at hab; subst hab
        simp only [ite_true]
        refine LS.bind_eq fun i3 hi3 => ?_
        have hi3v : i3.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
        have h := ih i3 (by omega) hrel1 hinv1
        simp only [absICILFrom, hi3v] at h
        exact h

open Lockstep in
/-- `block_links_ok` ⊑ `blockLinksOk`: the pairs from the start, the former's
names those of the block's first member. -/
@[lockstep] theorem block_links_ok_ls {pers st lst}
    {block pins : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.basis.block_links_ok pers st block pins) lst
      (blockLinksOk (absICIL block) (absICIL pins)) := by
  rw [arena.basis.block_links_ok]
  unfold blockLinksOk
  refine LS.bind_eq fun former hf => ?_
  have hfv : former.val.map absNIdx =
      (((absICIL block).head?.map (·.toConstantVal.levelParams)).getD []) := by
    by_cases h0 : alloc.vec.Vec.len block = 0#usize
    · rw [ite_eq_left h0] at hf
      obtain rfl := (Result.ok_injective hf).symm
      have hl : block.val = [] := by
        have := congrArg Std.UScalar.val h0
        simpa [alloc.vec.Vec.len] using this
      simp [absICIL, hl, alloc.vec.Vec.new]
    · rw [ite_eq_right h0] at hf
      have hlt : 0 < block.val.length := by
        rcases hb : block.val with _ | ⟨c, cs⟩
        · exact absurd (Std.UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len, hb])) h0
        · simp
      obtain ⟨x, hx, hxv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec block 0#usize (by simpa using hlt))
      subst hxv
      rw [alloc.vec.Vec.index_slice_index, hx, bind_ok] at hf
      obtain ⟨iv, hiv, hf⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
      obtain rfl := (Result.ok_injective hf).symm
      have e := i_constant_info_to_constant_val_abs hiv
      rcases hb : block.val with _ | ⟨c, cs⟩
      · simp [hb] at hlt
      · simp only [absICIL, hb, List.map_cons, List.head?_cons, Option.map_some,
          Option.getD_some]
        have : (↑block : List _)[(0#usize : Std.Usize).val] = c := by simp [hb]
        rw [this] at e
        rw [← e]; rfl
  have h := block_links_ok_go_aux (block := block) (pins := pins) (former := former) _ 0#usize rfl
    hrel hinv
  simp only [absICILFrom, show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at h
  rw [hfv] at h
  exact h

/-! ## Recognising a pinned block by its members' names -/

open Lockstep in
theorem basis_name_hit_go_aux (k : Nat) :
    ∀ {pers st lst} (block : alloc.vec.Vec arena.env.IConstantInfo)
      (ks : alloc.vec.Vec kernel.env.BasisKind) (i : Std.Usize),
      ks.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (Option.map ConRon.Refine.absBasisKind) a)
        (arena.basis.basis_name_hit_go pers st block ks i) lst
        (basisNameHitGo (absICIL block) (absBasisKindLFrom ks i)) := by
  induction k with
  | zero =>
    intro pers st lst block ks i hn hrel hinv
    have hl := alloc.vec.Vec.len_val ks
    have : absBasisKindLFrom ks i = [] := by
      simp only [absBasisKindLFrom]; rw [List.drop_eq_nil_of_le (by omega)]; rfl
    rw [arena.basis.basis_name_hit_go, this, basisNameHitGo, ite_eq_left (by scalar_tac)]
    exact LS.pure rfl hrel hinv
  | succ m ih =>
    intro pers st lst block ks i hn hrel hinv
    have hl := alloc.vec.Vec.len_val ks
    have hi : i.val < ks.val.length := by omega
    have hcons : absBasisKindLFrom ks i = ConRon.Refine.absBasisKind ks.val[i.val] ::
        (ks.val.drop (i.val + 1)).map ConRon.Refine.absBasisKind := by
      simp only [absBasisKindLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl
    rw [arena.basis.basis_name_hit_go, hcons, basisNameHitGo, ite_eq_right (by scalar_tac)]
    simp only [absBasisKindLFrom] at ih
    lockstep

/-- `basis_name_hit` ⊑ `basisNameHit` — the four pinned inductive blocks, in
con-leche's order; `.quotK` is deliberately not among them. -/
theorem basis_name_hit_refines {pers st lst} {block : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.basis.basis_name_hit pers st block = ok o) :
    Sim₀ (Option.map ConRon.Refine.absBasisKind) pers lst o
      (basisNameHit (absICIL block)) := by
  rw [arena.basis.basis_name_hit] at hrun
  obtain ⟨ks, hks, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hk := ConRon.Refine.BasisRaw.block_pin_kinds_refines hks
  have h := Lockstep.LS.toSim₀ (basis_name_hit_go_aux _ block ks 0#usize rfl hrel hinv) hrun
  have e : absBasisKindLFrom ks 0#usize =
      [ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK] := by
    simp only [absBasisKindLFrom]; rw [← hk]; rfl
  rw [e] at h
  exact h

open Lockstep in
@[lockstep] theorem basis_name_hit_ls {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map ConRon.Refine.absBasisKind) a)
      (arena.basis.basis_name_hit pers st block) lst (basisNameHit (absICIL block)) :=
  LS.ofSim₀ fun _ h => basis_name_hit_refines hrel hinv h

/-! ## The pinned quotient package, slot by slot -/

open Lockstep in
/-- `quot_pin` ⊑ `quotPin`: the pinned quotient package's constant at the slot;
past the block, the default constant (`i_constant_info_dummy`, the twin's
`default`), which no slot reaches. -/
@[lockstep] theorem quot_pin_ls {pers st lst} {k : kernel.env.QuotKind}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.basis.quot_pin pers st k) lst
      (quotPin (ConRon.Refine.absQuotKind k)) := by
  rw [arena.basis.quot_pin]
  unfold quotPin
  refine LS.bind (basis_kind_decls_ls (k := .QuotK) hrel hinv) rfl (fun _ _ => errArm_ok) ?_
  intro blk b st1 lst1 hb hrel1 hinv1
  subst hb
  refine LS.bind_eq fun slot hslot => ?_
  have hsv := ConRon.Refine.BasisRaw.quot_kind_slot_refines hslot
  refine LS.bind_eq fun i1 hi1 => ?_
  have hi1v : i1.val = blk.val.length := by
    simp only [lift, Result.ok.injEq] at hi1
    subst hi1
    rw [usize_cast_u64_val']
    simp [alloc.vec.Vec.len]
  by_cases hge : slot ≥ i1
  · rw [ite_eq_left hge]
    refine LS.bind_eq fun d hd => ?_
    have hn : (absICIL blk).length ≤ (ConRon.Refine.absQuotKind k).slot := by
      simp only [absICIL, List.length_map]; scalar_tac
    rw [List.getD_eq_default _ _ hn]
    simp only [arena.env.i_constant_info_dummy, arena.handle.NIdx.of_word,
      arena.handle.EIdx.of_word, bind_ok, Result.ok.injEq] at hd
    subst hd
    exact LS.pure rfl hrel1 hinv1
  · rw [ite_eq_right hge]
    have hlt : slot.val < blk.val.length := by scalar_tac
    refine LS.bind_eq fun i2 hi2 => ?_
    have hi2v : i2.val = slot.val := by
      have hfit : slot.val ≤ Std.Usize.max := by have := blk.slice.property; scalar_tac
      rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hfit]
      exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi2).symm
    obtain ⟨x, hx, hxv⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec blk i2 (by rw [hi2v]; exact hlt))
    subst hxv
    rw [alloc.vec.Vec.index_slice_index, hx, bind_ok]
    refine LS.bind_eq fun c hc => ?_
    have hca := i_constant_info_dup_abs hc
    refine LS.pure ?_ hrel1 hinv1
    rw [hca]
    simp only [absICIL]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map]; omega)]
    simp [hi2v, hsv]

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

/-! ## The renaming walks -/

open Lockstep in
/-- `constant_val_at_lps` ⊑ `IConstantVal.atLps`: the type with the old names
replaced positionally, the new names stored. -/
@[lockstep] theorem constant_val_at_lps_ls {pers st lst} {cv : arena.env.IConstantVal}
    {ps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.basis.constant_val_at_lps pers st cv ps) lst
      ((absIConstantVal cv).atLps (ps.val.map absNIdx)) := by
  rw [arena.basis.constant_val_at_lps]
  unfold IConstantVal.atLps
  refine LS.bind (param_levels_ls (lps := ps) hrel hinv) rfl (fun _ _ => errArm_ok) ?_
  intro us b st1 lst1 hb hrel1 hinv1
  subst hb
  refine LS.bind (inst_lp_fast_ls hrel1 hinv1 _ _ _ _)
    (by simp only [core_walk_fuel_abs, absIConstantVal]) (fun _ _ => errArm_ok) ?_
  intro ty b2 st2 lst2 hb2 hrel2 hinv2
  subst hb2
  refine LS.bind_eq fun n hn => ?_
  refine LS.bind_eq fun v hv => ?_
  refine LS.pure ?_ hrel2 hinv2
  simp [absIConstantVal, dupId_nidx _ _ hn, nidx_vec_dup_val hv]

open Lockstep in
private theorem rules_at_lps_aux {lpsH : alloc.vec.Vec arena.handle.NIdx} {us : arena.handle.LsIdx}
    {lpsT : alloc.vec.Vec kernel.name.Name} {usT : alloc.vec.Vec kernel.level.Level}
    {rules : alloc.vec.Vec arena.env.IRecRule}
    (hks : ConRon.Refine.NamesWF lpsT) (hvs : ConRon.Refine.LevelsWF usT) (k : Nat) :
    ∀ {pers st lst} (i : Std.Usize) (out : alloc.vec.Vec arena.env.IRecRule),
      rules.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.val.map absIRecRule)
        (arena.basis.rules_at_lps pers st lpsH us lpsT usT rules i out) lst
        (do
          let rest ← rulesAtLps (lpsH.val.map absNIdx) (absLsIdx us)
            (ConRon.Refine.absNames lpsT) (ConRon.Refine.absLevels usT)
            ((rules.val.drop i.val).map absIRecRule)
          pure (out.val.map absIRecRule ++ rest)) := by
  induction k with
  | zero =>
    intro pers st lst i out hk hrel hinv
    rw [arena.basis.rules_at_lps.eq_def]; simp only []
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len rules by scalar_tac),
      List.drop_eq_nil_of_le (by omega)]
    simp only [List.map_nil, rulesAtLps, pure_bind, List.append_nil]
    exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst i out hk hrel hinv
    have hlt : i.val < rules.val.length := by omega
    rw [arena.basis.rules_at_lps.eq_def]; simp only []
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rules by scalar_tac),
      List.drop_eq_getElem_cons hlt]
    obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rules i hlt)
    subst hyv
    rw [alloc.vec.Vec.index_slice_index, hy, bind_ok]
    simp only [List.map_cons, rulesAtLps, bind_assoc]
    refine LS.bind (inst_lp_fast_ls hrel hinv _ _ _ _)
      (by simp only [core_walk_fuel_abs, absIRecRule]) (fun _ _ => errArm_ok) ?_
    intro rhs b st1 lst1 hb hrel1 hinv1
    subst hb
    refine LS.bind (rec_rule_fire_at_lps_ls hrel1 hinv1 hks hvs) (by simp only [absIRecRule])
      (fun _ _ => errArm_ok) ?_
    intro fire b2 st2 lst2 hb2 hrel2 hinv2
    subst hb2
    refine LS.bind_eq fun n hn => ?_
    refine LS.bind_eq fun out1 hout1 => ?_
    refine LS.bind_eq fun i2 hi2 => ?_
    have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
    have h := ih i2 out1 (by omega) hrel2 hinv2
    rw [hi2v, ConRon.Refine.vec_push_val hout1] at h
    refine LS.tail h ?_ (fun _ _ h => h)
    simp only [List.map_append, List.map_cons, List.map_nil, pure_bind,
      List.append_assoc, List.singleton_append, absIRecRule, dupId_nidx _ _ hn]

open Lockstep in
@[lockstep] theorem rules_at_lps_ls {pers st lst} {lpsH : alloc.vec.Vec arena.handle.NIdx}
    {us : arena.handle.LsIdx} {lpsT : alloc.vec.Vec kernel.name.Name}
    {usT : alloc.vec.Vec kernel.level.Level} {rules : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hks : ConRon.Refine.NamesWF lpsT) (hvs : ConRon.Refine.LevelsWF usT) :
    LS pers (fun a b => b = a.val.map absIRecRule)
      (arena.basis.rules_at_lps pers st lpsH us lpsT usT rules 0#usize (alloc.vec.Vec.new _)) lst
      (rulesAtLps (lpsH.val.map absNIdx) (absLsIdx us) (ConRon.Refine.absNames lpsT)
        (ConRon.Refine.absLevels usT) (rules.val.map absIRecRule)) := by
  have h := rules_at_lps_aux (lpsH := lpsH) (us := us) (rules := rules) hks hvs _ 0#usize
    (alloc.vec.Vec.new _) rfl hrel hinv
  refine LS.tail h ?_ (fun _ _ h => h)
  simp [alloc.vec.Vec.new]

open Lockstep in
/-- `constant_info_at_lps_rec` ⊑ `IConstantInfo.atLps`'s `.recInfo` arm. -/
theorem constant_info_at_lps_rec_ls {pers st lst} {cv : arena.env.IConstantVal}
    {mI rP : Std.U64} {isK : Bool} {rules : alloc.vec.Vec arena.env.IRecRule}
    {ps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a)
      (arena.basis.constant_info_at_lps_rec pers st cv mI rP isK rules ps) lst
      ((absIConstantInfo (.RecInfo cv mI rP isK rules)).atLps (ps.val.map absNIdx)) := by
  rw [arena.basis.constant_info_at_lps_rec]
  simp only [absIConstantInfo, IConstantInfo.atLps]
  refine LS.bind (constant_val_at_lps_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
  intro cv2 b st1 lst1 hb hrel1 hinv1
  subst hb
  refine LS.bind (param_levels_ls (lps := ps) hrel1 hinv1) rfl (fun _ _ => errArm_ok) ?_
  intro us b2 st2 lst2 hb2 hrel2 hinv2
  subst hb2
  refine LS.bind (read_names_m_ls hrel2 hinv2 cv.level_params) (by simp [absIConstantVal])
    (fun _ _ => errArm_ok) ?_
  intro lpsT b3 st3 lst3 ⟨w3, hb3⟩ hrel3 hinv3
  subst hb3
  refine LS.bind (read_names_m_ls hrel3 hinv3 ps) rfl (fun _ _ => errArm_ok) ?_
  intro psT b4 st4 lst4 ⟨w4, hb4⟩ hrel4 hinv4
  subst hb4
  refine LS.bind_eq fun usT husT => ?_
  obtain ⟨ausT, wusT⟩ := param_level_values_entry w4 husT
  have e : (ConRon.Refine.absNames psT).map ConLeche.Level.param = ConRon.Refine.absLevels usT := by
    rw [ConRon.Refine.absLevels, ausT]
  rw [e]
  refine LS.bind (rules_at_lps_ls hrel4 hinv4 w3 wusT) (by simp [absIConstantVal])
    (fun _ _ => errArm_ok) ?_
  intro rules2 b5 st5 lst5 hb5 hrel5 hinv5
  subst hb5
  exact LS.pure rfl hrel5 hinv5

open Lockstep in
/-- `constant_info_at_lps` ⊑ `IConstantInfo.atLps`: a stored constant at other
level-parameter names. -/
@[lockstep] theorem constant_info_at_lps_ls {pers st lst} {ci : arena.env.IConstantInfo}
    {ps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.basis.constant_info_at_lps pers st ci ps)
      lst ((absIConstantInfo ci).atLps (ps.val.map absNIdx)) := by
  cases ci with
  | RecInfo cv mI rP isK rules =>
    rw [arena.basis.constant_info_at_lps]
    exact constant_info_at_lps_rec_ls hrel hinv
  | _ =>
    rw [arena.basis.constant_info_at_lps]
    simp only [absIConstantInfo, IConstantInfo.atLps]
    lockstep

/-! ## A block's comparison with its pin -/

open Lockstep in
/-- `pin_copy_ok` ⊑ `pinCopyOk`: distinct names, as many as the pin's, and the
record agrees with the pin at its own names. -/
@[lockstep] theorem pin_copy_ok_ls {pers st lst} {ci pin : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.basis.pin_copy_ok pers st ci pin) lst
      (pinCopyOk (absIConstantInfo ci) (absIConstantInfo pin)) := by
  rw [arena.basis.pin_copy_ok]
  unfold pinCopyOk
  refine LS.bind_eq fun iv hiv => ?_
  have hps : (absIConstantInfo ci).toConstantVal.levelParams = iv.level_params.val.map absNIdx := by
    rw [← i_constant_info_to_constant_val_abs hiv]; rfl
  simp only [hps]
  refine LS.bind_eq fun b hb => ?_
  have hbv : nameNodup (iv.level_params.val.map absNIdx) = b := name_nodup_spec _ b hb
  cases b with
  | false =>
    rw [ite_eq_right (by simp), ite_eq_right (by simp [hbv])]
    exact LS.pure rfl hrel hinv
  | true =>
    rw [ite_eq_left rfl]
    refine LS.bind_eq fun iv1 hiv1 => ?_
    have hps1 : (absIConstantInfo pin).toConstantVal.levelParams =
        iv1.level_params.val.map absNIdx := by
      rw [← i_constant_info_to_constant_val_abs hiv1]; rfl
    by_cases hl : alloc.vec.Vec.len iv.level_params = alloc.vec.Vec.len iv1.level_params
    · rw [ite_eq_left hl]
      have hl' : iv.level_params.val.length = iv1.level_params.val.length := by
        have := congrArg Std.UScalar.val hl; simpa [alloc.vec.Vec.len] using this
      rw [ite_eq_left (by simp [hbv, hps1, hl'])]
      refine LS.bind (constant_info_at_lps_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
      intro pin2 b2 st1 lst1 hb2 hrel1 hinv1
      subst hb2
      refine LS.bind_eq fun b3 hb3 => ?_
      exact LS.pure (pin_agrees_refines hb3).symm hrel1 hinv1
    · rw [ite_eq_right hl]
      have hl' : ¬ iv.level_params.val.length = iv1.level_params.val.length := by
        intro h; exact hl (Std.UScalar.eq_of_val_eq (by simpa [alloc.vec.Vec.len] using h))
      rw [ite_eq_right (by simp [hbv, hps1, hl'])]
      exact LS.pure rfl hrel hinv

open Lockstep in
private theorem pin_copies_ok_aux {block pins : alloc.vec.Vec arena.env.IConstantInfo}
    (k : Nat) :
    ∀ {pers st lst} (i : Std.Usize), block.val.length - i.val ≤ k →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = id a) (arena.basis.pin_copies_ok pers st block pins i) lst
        (pinCopiesOk (absICILFrom block i) (absICILFrom pins i)) := by
  induction k with
  | zero =>
    intro pers st lst i hk hrel hinv
    have hb : block.val.length ≤ i.val := by omega
    rw [arena.basis.pin_copies_ok.eq_def]; simp only []
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len block by scalar_tac)]
    by_cases hp : pins.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len pins by scalar_tac)]
      simp only [absICILFrom, List.drop_eq_nil_of_le hb, List.drop_eq_nil_of_le hp,
        List.map_nil, pinCopiesOk]
      exact LS.pure rfl hrel hinv
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len pins by scalar_tac),
        ite_eq_left (show i ≥ alloc.vec.Vec.len block by scalar_tac)]
      simp only [absICILFrom, List.drop_eq_nil_of_le hb,
        List.drop_eq_getElem_cons (Nat.lt_of_not_le hp), List.map_nil, List.map_cons,
        pinCopiesOk]
      exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst i hk hrel hinv
    rw [arena.basis.pin_copies_ok.eq_def]; simp only []
    by_cases hb : block.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len block by scalar_tac)]
      by_cases hp : pins.val.length ≤ i.val
      · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len pins by scalar_tac)]
        simp only [absICILFrom, List.drop_eq_nil_of_le hb, List.drop_eq_nil_of_le hp,
          List.map_nil, pinCopiesOk]
        exact LS.pure rfl hrel hinv
      · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len pins by scalar_tac),
          ite_eq_left (show i ≥ alloc.vec.Vec.len block by scalar_tac)]
        simp only [absICILFrom, List.drop_eq_nil_of_le hb,
          List.drop_eq_getElem_cons (Nat.lt_of_not_le hp), List.map_nil, List.map_cons,
          pinCopiesOk]
        exact LS.pure rfl hrel hinv
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac),
        ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)]
      have hlb : i.val < block.val.length := Nat.lt_of_not_le hb
      by_cases hp : pins.val.length ≤ i.val
      · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len pins by scalar_tac)]
        simp only [absICILFrom, List.drop_eq_nil_of_le hp, List.drop_eq_getElem_cons hlb,
          List.map_nil, List.map_cons, pinCopiesOk]
        exact LS.pure rfl hrel hinv
      · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len pins by scalar_tac)]
        have hlp : i.val < pins.val.length := Nat.lt_of_not_le hp
        obtain ⟨x, hx, hxv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlb)
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlp)
        subst hxv hyv
        rw [alloc.vec.Vec.index_slice_index, hx, bind_ok, alloc.vec.Vec.index_slice_index, hy,
          bind_ok]
        simp only [absICILFrom, List.drop_eq_getElem_cons hlb, List.drop_eq_getElem_cons hlp,
          List.map_cons, pinCopiesOk]
        refine LS.bind (pin_copy_ok_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
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
          simp only [absICILFrom, hi2v] at h
          exact h

open Lockstep in
/-- `pin_list_ok` ⊑ `pinListOk`: the copies, then the links. -/
@[lockstep] theorem pin_list_ok_ls {pers st lst}
    {block pins : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.basis.pin_list_ok pers st block pins) lst
      (pinListOk (absICIL block) (absICIL pins)) := by
  rw [arena.basis.pin_list_ok]
  unfold pinListOk
  have h := pin_copies_ok_aux (block := block) (pins := pins) _ 0#usize (le_refl _) hrel hinv
  simp only [absICILFrom, show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at h
  refine LS.bind h rfl (fun _ _ => errArm_ok) ?_
  intro a b st1 lst1 hab hrel1 hinv1
  cases a with
  | false =>
    simp only [id] at hab; subst hab
    exact LS.pure rfl hrel1 hinv1
  | true =>
    simp only [id] at hab; subst hab
    simp only [ite_true]
    exact block_links_ok_ls hrel1 hinv1

/-! ## What a pinned block's check installs -/

open Lockstep in
private theorem basis_kind_at_block_go_aux {pins block : alloc.vec.Vec arena.env.IConstantInfo}
    (k : Nat) :
    ∀ {pers st lst} (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantInfo),
      pins.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absICIL a)
        (arena.basis.basis_kind_at_block_go pers st pins block i out) lst
        (do
          let rest ← atBlockGo (absICILFrom pins i) (absICILFrom block i)
          pure (absICIL out ++ rest)) := by
  induction k with
  | zero =>
    intro pers st lst i out hk hrel hinv
    have hp : pins.val.length ≤ i.val := by omega
    rw [arena.basis.basis_kind_at_block_go.eq_def]; simp only []
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len pins by scalar_tac)]
    simp only [absICILFrom, List.drop_eq_nil_of_le hp, List.map_nil, atBlockGo, pure_bind,
      List.append_nil]
    exact LS.pure rfl hrel hinv
  | succ k ih =>
    intro pers st lst i out hk hrel hinv
    rw [arena.basis.basis_kind_at_block_go.eq_def]; simp only []
    by_cases hp : pins.val.length ≤ i.val
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len pins by scalar_tac)]
      simp only [absICILFrom, List.drop_eq_nil_of_le hp, List.map_nil, atBlockGo, pure_bind,
        List.append_nil]
      exact LS.pure rfl hrel hinv
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len pins by scalar_tac)]
      have hlp : i.val < pins.val.length := Nat.lt_of_not_le hp
      by_cases hb : block.val.length ≤ i.val
      · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len block by scalar_tac)]
        simp only [absICILFrom, List.drop_eq_nil_of_le hb, List.drop_eq_getElem_cons hlp,
          List.map_nil, List.map_cons, atBlockGo, pure_bind, List.append_nil]
        exact LS.pure rfl hrel hinv
      · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)]
        have hlb : i.val < block.val.length := Nat.lt_of_not_le hb
        obtain ⟨x, hx, hxv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlb)
        subst hxv
        rw [alloc.vec.Vec.index_slice_index, hx, bind_ok]
        refine LS.bind_eq fun iv hiv => ?_
        have eiv := i_constant_info_to_constant_val_abs hiv
        obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec pins i hlp)
        subst hyv
        rw [alloc.vec.Vec.index_slice_index, hy, bind_ok]
        simp only [absICILFrom, List.drop_eq_getElem_cons hlb, List.drop_eq_getElem_cons hlp,
          List.map_cons, atBlockGo, bind_assoc]
        rw [← eiv]
        refine LS.bind (constant_info_at_lps_ls hrel hinv) (by simp [absIConstantVal])
          (fun _ _ => errArm_ok) ?_
        intro c b st1 lst1 hb' hrel1 hinv1
        subst hb'
        refine LS.bind_eq fun out1 hout1 => ?_
        refine LS.bind_eq fun i3 hi3 => ?_
        have hi3v : i3.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
        have h := ih i3 out1 (by omega) hrel1 hinv1
        simp only [absICILFrom, hi3v, absICIL, ConRon.Refine.vec_push_val hout1] at h
        refine LS.tail h ?_ (fun _ _ h => h)
        simp [absICIL, List.append_assoc]

open Lockstep in
/-- `basis_kind_at_block` ⊑ `BasisKind.atBlock`: each pin at the names its
record declares. -/
@[lockstep] theorem basis_kind_at_block_ls {pers st lst} {kind : kernel.env.BasisKind}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a) (arena.basis.basis_kind_at_block pers st kind block) lst
      (ConRon.Arena.BasisKind.atBlock (ConRon.Refine.absBasisKind kind) (absICIL block)) := by
  rw [arena.basis.basis_kind_at_block]
  unfold BasisKind.atBlock
  refine LS.bind (basis_kind_decls_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
  intro pins b st1 lst1 hb hrel1 hinv1
  subst hb
  have h := basis_kind_at_block_go_aux (pins := pins) (block := block) _ 0#usize
    (alloc.vec.Vec.new _) rfl hrel1 hinv1
  refine LS.tail h ?_ (fun _ _ h => h)
  simp [absICILFrom, absICIL, alloc.vec.Vec.new]

open Lockstep in
/-- `quot_pin_hit` ⊑ `quotPinHit`: the record is the slot's pin up to its
level-parameter names, distinct and as many as the pin's. -/
@[lockstep] theorem quot_pin_hit_ls {pers st lst} {k : kernel.env.QuotKind}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.basis.quot_pin_hit pers st k cv) lst
      (quotPinHit (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  rw [arena.basis.quot_pin_hit]
  unfold quotPinHit
  refine LS.bind (quot_pin_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
  intro pin b st1 lst1 hb hrel1 hinv1
  subst hb
  refine LS.bind_eq fun pcv hpcv => ?_
  have epcv := i_constant_info_to_constant_val_abs hpcv
  rw [← epcv]
  refine LS.bind_eq fun b hb => ?_
  have hbv : nameNodup (cv.level_params.val.map absNIdx) = b := name_nodup_spec _ b hb
  have hcv : (absIConstantVal cv).levelParams = cv.level_params.val.map absNIdx := rfl
  have hpc : (absIConstantVal pcv).levelParams = pcv.level_params.val.map absNIdx := rfl
  simp only [hcv, hpc]
  cases b with
  | false =>
    rw [ite_eq_right (by simp), ite_eq_right (by simp [hbv])]
    exact LS.pure rfl hrel1 hinv1
  | true =>
    rw [ite_eq_left rfl]
    by_cases hl : alloc.vec.Vec.len cv.level_params = alloc.vec.Vec.len pcv.level_params
    · rw [ite_eq_left hl]
      have hl' : cv.level_params.val.length = pcv.level_params.val.length := by
        have := congrArg Std.UScalar.val hl; simpa [alloc.vec.Vec.len] using this
      rw [ite_eq_left (by simp [hbv, hl'])]
      refine LS.bind (constant_val_at_lps_ls hrel1 hinv1) rfl (fun _ _ => errArm_ok) ?_
      intro pcv2 b2 st2 lst2 hb2 hrel2 hinv2
      subst hb2
      refine LS.bind_eq fun b3 hb3 => ?_
      refine LS.pure ?_ hrel2 hinv2
      rw [i_constant_val_beq_refines hb3]
      simp [beq_eq_decide]
    · rw [ite_eq_right hl]
      have hl' : ¬ cv.level_params.val.length = pcv.level_params.val.length := by
        intro h; exact hl (Std.UScalar.eq_of_val_eq (by simpa [alloc.vec.Vec.len] using h))
      rw [ite_eq_right (by simp [hbv, hl'])]
      exact LS.pure rfl hrel1 hinv1

open Lockstep in
/-- `quot_at` ⊑ `quotAt`: the slot's pin at the names the record declares. -/
@[lockstep] theorem quot_at_ls {pers st lst} {k : kernel.env.QuotKind}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.basis.quot_at pers st k cv) lst
      (quotAt (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) := by
  rw [arena.basis.quot_at]
  unfold quotAt
  refine LS.bind (quot_pin_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
  intro pin b st1 lst1 hb hrel1 hinv1
  subst hb
  exact constant_info_at_lps_ls hrel1 hinv1

end ConRon.Refine2
