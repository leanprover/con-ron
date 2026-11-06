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

end ConRon.Refine2
