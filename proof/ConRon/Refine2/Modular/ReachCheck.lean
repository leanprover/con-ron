/-
# `ConRon.Refine2.Modular.ReachCheck` — `modular/reach.rs`: the validation, the read order and the inferred flags

**Task #166, Theorem 2.**  The reach's store-only functions against their twins
(`Arena/Modular/Reach.lean`), in the arena's lockstep shape (`LS`): what a record reads
(`record_reads`), the names it installs (`decl_names`), the syntactic validation of a record
(`expr_ok` … `record_ok`, `validate_ctx`), the read order (`owner_map`, `sort_visit`,
`sort_from`, `read_order`) and the inferred flags (`infer_one`, `infer_flags`), which run at the
worker's frozen index as a job does (`record_job_refines`).

Each Rust `while` loop over a `Vec` is its own Aeneas `_loop`; its lemma is by induction on the
distance to the end, against the twin's structural recursion on the list from the cursor
(`absICILFrom` and friends).  The pure loops (`first_owner_add`, `owner_add`) are equations over
`IdxRel`.
-/
import ConRon.Refine2.Checker.Jobs
import ConRon.Refine2.Checker.Needs
import ConRon.Refine2.Checker.Install
import ConRon.Refine2.Inductives.StreamRecs
import ConRon.Refine2.Core.LS.Lits
import ConRon.Refine2.Modular.Graph
import ConRon.Refine2.Frontend.Olean.NamePos
import ConRon.Arena.Modular.Reach

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.reach

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Lockstep
open ConRon.Refine (NameWF NamesWF)
open ConRon.Refine2.Frontend.Olean (nidx_dup_id)
open ConRon.Refine.HashMap2 (toFun)

attribute [local lockstep] decl_constants_ls decl_tables_ls

/-- A Rust run that ends in `ok (.Err _, _)` after any binds does not accept. -/
macro "err_contra " h:ident : tactic =>
  `(tactic| (repeat (have h_ := ConRon.Refine.bind_eq_ok_iff.mp $h:ident; clear $h:ident;
                     obtain ⟨_, _, $h:ident⟩ := h_);
             first | (cases Result.ok_injective $h:ident) | (simp at $h:ident) |
               (split at $h:ident <;> simp at $h:ident)))

/-! ## What a record reads -/

theorem record_reads_consts_loop_aux (n : Nat) :
    ∀ {pers st lst} {cs : alloc.vec.Vec arena.env.IConstantInfo} {x : arena.needs.NeedsSt}
      {y : NeedsSt} {i : Std.Usize},
      cs.val.length - i.val = n → NSRel x y → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers NSRel (record_reads_consts_loop pers st cs x i) lst
        (Modular.recordReadsConsts y (absICILFrom cs i)) := by
  induction n with
  | zero =>
    intro pers st lst cs x y i hn hm hrel hinv
    rw [record_reads_consts_loop, ite_eq_right (by scalar_tac), absICILFrom,
      vecFrom_nil _ _ _ (by omega)]
    simp only [Modular.recordReadsConsts]
    lockstep
  | succ m ih =>
    intro pers st lst cs x y i hn hm hrel hinv
    rw [record_reads_consts_loop, ite_eq_left (by scalar_tac), absICILFrom,
      vecFrom_cons _ _ _ (by omega)]
    simp only [Modular.recordReadsConsts]
    lockstep


/-- `record_reads_consts` ⊑ `recordReadsConsts`. -/
@[lockstep] theorem record_reads_consts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt} (hm : NSRel x y)
    (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers NSRel (record_reads_consts pers st x cs) lst
      (Modular.recordReadsConsts y (cs.val.map absIConstantInfo)) := by
  have := record_reads_consts_loop_aux _ (cs := cs) (i := 0#usize) rfl hm hrel hinv
  simpa [absICILFrom] using this

theorem record_reads_tables_loop_aux (n : Nat) :
    ∀ {pers st lst} {ts : alloc.vec.Vec arena.env.IProjTable} {x : arena.needs.NeedsSt}
      {y : NeedsSt} {i : Std.Usize},
      ts.val.length - i.val = n → NSRel x y → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers NSRel (record_reads_tables_loop pers st ts x i) lst
        (Modular.recordReadsTables y ((ts.val.drop i.val).map absIProjTable)) := by
  induction n with
  | zero =>
    intro pers st lst ts x y i hn hm hrel hinv
    rw [record_reads_tables_loop, ite_eq_right (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
    simp only [Modular.recordReadsTables]
    lockstep
  | succ m ih =>
    intro pers st lst ts x y i hn hm hrel hinv
    rw [record_reads_tables_loop, ite_eq_left (by scalar_tac), vecFrom_cons _ _ _ (by omega)]
    simp only [Modular.recordReadsTables]
    lockstep

/-- `record_reads_tables` ⊑ `recordReadsTables`. -/
@[lockstep] theorem record_reads_tables_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt} (hm : NSRel x y)
    (ts : alloc.vec.Vec arena.env.IProjTable) :
    LS pers NSRel (record_reads_tables pers st x ts) lst
      (Modular.recordReadsTables y (ts.val.map absIProjTable)) := by
  have := record_reads_tables_loop_aux _ (ts := ts) (i := 0#usize) rfl hm hrel hinv
  simpa using this

/-- **`record_reads` ⊑ `recordReads`**: what a record reads, in order. -/
@[lockstep] theorem record_reads_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = absNIdxList a) (record_reads pers st d) lst
      (Modular.recordReads (absIDeclaration d)) := by
  rw [record_reads, Modular.recordReads]
  lockstep
  exact LS.pure hR.acc hrel hinv

/-! ## The names a record installs -/

theorem decl_names_loop_eq (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    ∀ (n : Nat) (out : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) {r},
      cs.val.length - i.val = n → decl_names_loop cs out i = ok r →
      r.val.map absNIdx = out.val.map absNIdx ++
        ((cs.val.drop i.val).map absIConstantInfo).map (·.name) := by
  intro n
  induction n with
  | zero =>
    intro out i r hn h
    rw [decl_names_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [vecFrom_nil _ _ _ (by omega)]; simp
  | succ m ih =>
    intro out i r hn h
    rw [decl_names_loop, ite_eq_left (by scalar_tac)] at h
    have hi : i.val < cs.val.length := by omega
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hcv : cs.val[i.val]? = some c := vec_index_some hc
    obtain ⟨nm, hnm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnmv := i_constant_info_name_ls c nm hnm
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hout1v : out1.val = out.val ++ [nm] := ConRon.Refine.vec_push_val hout1
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v := ConRon.Refine.Nat.uadd_val hi2
    rw [ih out1 i2 (by simp at hi2v; omega) h, hout1v, vecFrom_cons _ _ _ hi]
    have hc' : cs.val[i.val] = c := by
      rw [List.getElem?_eq_getElem hi] at hcv; exact Option.some_inj.mp hcv
    simp only [TwinEq] at hnmv
    simp at hi2v
    simp [hi2v, hc', hnmv]

/-- **`decl_names` ⊑ `declNames`**: a record's constants' names. -/
@[lockstep] theorem decl_names_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = absNIdxList a) (decl_names pers st d) lst
      (Modular.declNames (absIDeclaration d)) := by
  intro o st' hrun
  rw [decl_names] at hrun
  obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have H := decl_constants_ls hrel hinv _ _ h1
  rw [Modular.declNames, StateT.run_bind]
  cases r with
  | Err e =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    exact AErrSim.bind H _
  | Ok cs =>
    obtain ⟨cs', lst1, hx1, rfl, hrel1, hinv1⟩ := H
    obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    have e := decl_names_loop_eq cs _ _ 0#usize rfl hout1
    refine ⟨_, lst1, by rw [hx1]; rfl, ?_, hrel1, hinv1⟩
    simp only [absNIdxList]
    rw [e]; simp [alloc.vec.Vec.with_capacity]

/-! ## The validation of a record -/

/-- `expr_ok` ⊑ `exprOk`. -/
@[lockstep] theorem expr_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx) (k : Std.U64)
    (e : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (expr_ok pers st lps k e) lst
      (Modular.exprOk (absNIdxL lps) (absU k) (absEIdx e)) := by
  rw [expr_ok, Modular.exprOk]
  lockstep

theorem levels_defined_loop_aux (n : Nat) :
    ∀ {pers st lst} {ps : alloc.vec.Vec kernel.name.Name} {lvls : alloc.vec.Vec arena.handle.LIdx}
      {i : Std.Usize},
      lvls.val.length - i.val = n → NamesWF ps → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a) (levels_defined_loop pers st ps lvls i) lst
        (Modular.levelsDefined (ConRon.Refine.absNames ps) ((lvls.val.drop i.val).map absLIdx)) := by
  induction n with
  | zero =>
    intro pers st lst ps lvls i hn hp hrel hinv
    rw [levels_defined_loop, ite_eq_right (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
    simp only [Modular.levelsDefined]
    lockstep
  | succ m ih =>
    intro pers st lst ps lvls i hn hp hrel hinv
    rw [levels_defined_loop, ite_eq_left (by scalar_tac), vecFrom_cons _ _ _ (by omega)]
    simp only [Modular.levelsDefined]
    lockstep

/-- `levels_defined` ⊑ `levelsDefined`. -/
@[lockstep] theorem levels_defined_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ps : alloc.vec.Vec kernel.name.Name} (hp : NamesWF ps)
    (lvls : alloc.vec.Vec arena.handle.LIdx) :
    LS pers (fun a b => b = a) (levels_defined pers st ps lvls) lst
      (Modular.levelsDefined (ConRon.Refine.absNames ps) (lvls.val.map absLIdx)) := by
  have := levels_defined_loop_aux _ (lvls := lvls) (i := 0#usize) rfl hp hrel hinv
  simpa using this

theorem exprs_ok_loop_aux (n : Nat) :
    ∀ {pers st lst} {lps : alloc.vec.Vec arena.handle.NIdx} {k : Std.U64}
      {es : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize},
      es.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a) (exprs_ok_loop pers st lps k es i) lst
        (Modular.exprsOk (absNIdxL lps) (absU k) ((es.val.drop i.val).map absEIdx)) := by
  induction n with
  | zero =>
    intro pers st lst lps k es i hn hrel hinv
    rw [exprs_ok_loop, ite_eq_right (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
    simp only [Modular.exprsOk]
    lockstep
  | succ m ih =>
    intro pers st lst lps k es i hn hrel hinv
    rw [exprs_ok_loop, ite_eq_left (by scalar_tac), vecFrom_cons _ _ _ (by omega)]
    simp only [Modular.exprsOk]
    lockstep

/-- `exprs_ok` ⊑ `exprsOk`. -/
@[lockstep] theorem exprs_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx) (k : Std.U64)
    (es : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a) (exprs_ok pers st lps k es) lst
      (Modular.exprsOk (absNIdxL lps) (absU k) (es.val.map absEIdx)) := by
  have := exprs_ok_loop_aux _ (es := es) (i := 0#usize) (lps := lps) (k := k) rfl hrel hinv
  simpa using this


/-- A checked `u64` addition: `none` exactly past `u64`'s range. -/
theorem lift_u64_checked_add_spec (a b : Std.U64) :
    LSP (lift (Std.U64.checked_add a b) : Result (Option Std.U64))
      (fun o => (o = none → 2 ^ 64 ≤ a.val + b.val) ∧
        (∀ n, o = some n → n.val = a.val + b.val ∧ a.val + b.val < 2 ^ 64)) := by
  intro o h
  have ho : Std.U64.checked_add a b = o := Result.ok_injective h
  have hs := Std.U64.checked_add_bv_spec a b
  have hm : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
  rw [ho] at hs
  rcases o with _ | z
  · exact ⟨fun _ => by simp only at hs; omega, fun n hn => by cases hn⟩
  · refine ⟨fun hn => (by cases hn), fun n hn => ?_⟩
    cases hn; simp only at hs; exact ⟨hs.2.1, by omega⟩

attribute [local lockstep] lift_u64_checked_add_spec

/-- `nested_ok` ⊑ `nestedOk`. -/
@[lockstep] theorem nested_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx) (ty : arena.handle.EIdx)
    (m_i r_p : Std.U64) (fire : arena.env.IRecRuleFire) :
    LS pers (fun a b => b = a) (nested_ok pers st lps ty m_i r_p fire) lst
      (Modular.nestedOk (absNIdxL lps) (absEIdx ty) (absU m_i) (absU r_p)
        (absIRecRuleFire fire)) := by
  rw [nested_ok.eq_def]
  cases fire <;> simp only [absIRecRuleFire, Modular.nestedOk] <;> lockstep

/-- `rule_ok` ⊑ `ruleOk`. -/
@[lockstep] theorem rule_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx) (ty : arena.handle.EIdx)
    (m_i r_p : Std.U64) (r : arena.env.IRecRule) :
    LS pers (fun a b => b = a) (rule_ok pers st lps ty m_i r_p r) lst
      (Modular.ruleOk (absNIdxL lps) (absEIdx ty) (absU m_i) (absU r_p) (absIRecRule r)) := by
  rw [rule_ok, Modular.ruleOk]
  simp only [absIRecRule]
  lockstep

theorem rules_ok_loop_aux (n : Nat) :
    ∀ {pers st lst} {lps : alloc.vec.Vec arena.handle.NIdx} {ty : arena.handle.EIdx}
      {m_i r_p : Std.U64} {rules : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize},
      rules.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a) (rules_ok_loop pers st lps ty m_i r_p rules i) lst
        (Modular.rulesOk (absNIdxL lps) (absEIdx ty) (absU m_i) (absU r_p)
          ((rules.val.drop i.val).map absIRecRule)) := by
  induction n with
  | zero =>
    intro pers st lst lps ty m_i r_p rules i hn hrel hinv
    rw [rules_ok_loop, ite_eq_right (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
    simp only [Modular.rulesOk]
    lockstep
  | succ m ih =>
    intro pers st lst lps ty m_i r_p rules i hn hrel hinv
    rw [rules_ok_loop, ite_eq_left (by scalar_tac), vecFrom_cons _ _ _ (by omega)]
    simp only [Modular.rulesOk]
    lockstep

/-- `rules_ok` ⊑ `rulesOk`. -/
@[lockstep] theorem rules_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx) (ty : arena.handle.EIdx)
    (m_i r_p : Std.U64) (rules : alloc.vec.Vec arena.env.IRecRule) :
    LS pers (fun a b => b = a) (rules_ok pers st lps ty m_i r_p rules) lst
      (Modular.rulesOk (absNIdxL lps) (absEIdx ty) (absU m_i) (absU r_p)
        (rules.val.map absIRecRule)) := by
  have := rules_ok_loop_aux _ (i := 0#usize) (lps := lps) (ty := ty) (m_i := m_i) (r_p := r_p)
    (rules := rules) rfl hrel hinv
  simpa using this

/-- `ctor_head_ok` ⊑ `ctorHeadOk`. -/
@[lockstep] theorem ctor_head_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cv : arena.env.IConstantVal) (induct : arena.handle.NIdx) :
    LS pers (fun a b => b = a) (ctor_head_ok pers st cv induct) lst
      (Modular.ctorHeadOk (absIConstantVal cv) (absNIdx induct)) := by
  rw [ctor_head_ok, Modular.ctorHeadOk]
  simp only [absIConstantVal]
  lockstep

/-- `const_ok` ⊑ `constOk`. -/
@[lockstep] theorem const_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (c : arena.env.IConstantInfo) :
    LS pers (fun a b => b = a) (const_ok pers st c) lst
      (Modular.constOk (absIConstantInfo c)) := by
  rw [const_ok.eq_def]
  cases c <;> simp only [absIConstantInfo, Modular.constOk, absIConstantVal] <;> lockstep

/-- `table_ok` ⊑ `tableOk`. -/
@[lockstep] theorem table_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t : arena.env.IProjTable) :
    LS pers (fun a b => b = a) (table_ok pers st t) lst
      (Modular.tableOk (absIProjTable t)) := by
  rw [table_ok, Modular.tableOk]
  simp only [absIProjTable]
  lockstep
  rename_i v
  obtain ⟨hn1, hn2⟩ := hP.2 _ rfl
  have e1 : (1#u64 : Std.U64).val = 1 := rfl
  rw [e1] at hn1 hn2
  rw [ite_eq_right (by omega)]
  have := exprs_ok_ls hrel hinv t.level_params v t.bodies
  simpa [absNIdxL, absU, hn1] using this

theorem consts_ok_loop_aux (n : Nat) :
    ∀ {pers st lst} {cs : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize},
      cs.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a) (consts_ok_loop pers st cs i) lst
        (Modular.constsOk ((cs.val.drop i.val).map absIConstantInfo)) := by
  induction n with
  | zero =>
    intro pers st lst cs i hn hrel hinv
    rw [consts_ok_loop, ite_eq_right (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
    simp only [Modular.constsOk]
    lockstep
  | succ m ih =>
    intro pers st lst cs i hn hrel hinv
    rw [consts_ok_loop, ite_eq_left (by scalar_tac), vecFrom_cons _ _ _ (by omega)]
    simp only [Modular.constsOk]
    lockstep

/-- `consts_ok` ⊑ `constsOk`. -/
@[lockstep] theorem consts_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = a) (consts_ok pers st cs) lst
      (Modular.constsOk (cs.val.map absIConstantInfo)) := by
  have := consts_ok_loop_aux _ (i := 0#usize) (cs := cs) rfl hrel hinv
  simpa using this

theorem tables_ok_loop_aux (n : Nat) :
    ∀ {pers st lst} {ts : alloc.vec.Vec arena.env.IProjTable} {i : Std.Usize},
      ts.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a) (tables_ok_loop pers st ts i) lst
        (Modular.tablesOk ((ts.val.drop i.val).map absIProjTable)) := by
  induction n with
  | zero =>
    intro pers st lst ts i hn hrel hinv
    rw [tables_ok_loop, ite_eq_right (by scalar_tac), vecFrom_nil _ _ _ (by omega)]
    simp only [Modular.tablesOk]
    lockstep
  | succ m ih =>
    intro pers st lst ts i hn hrel hinv
    rw [tables_ok_loop, ite_eq_left (by scalar_tac), vecFrom_cons _ _ _ (by omega)]
    simp only [Modular.tablesOk]
    lockstep

/-- `tables_ok` ⊑ `tablesOk`. -/
@[lockstep] theorem tables_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ts : alloc.vec.Vec arena.env.IProjTable) :
    LS pers (fun a b => b = a) (tables_ok pers st ts) lst
      (Modular.tablesOk (ts.val.map absIProjTable)) := by
  have := tables_ok_loop_aux _ (i := 0#usize) (ts := ts) rfl hrel hinv
  simpa using this

/-- **`record_ok` ⊑ `recordOk`**: a record's syntactic validation. -/
@[lockstep] theorem record_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = a) (record_ok pers st d) lst
      (Modular.recordOk (absIDeclaration d)) := by
  rw [record_ok, Modular.recordOk]
  lockstep


/-! ## The owner maps -/

theorem IdxRel.contains_eq {m s} (h : IdxRel m s) {k : arena.handle.NIdx} {b : Bool}
    (hg : ron.hashmap2.HashMap2.contains_key hN eN m k = ok b) : b = s.contains (absNIdx k) := by
  rw [ConRon.Refine.HashMap2.contains_key_refines_gen (P := fun _ => True) nidx_eq2 h.inv
    (fun _ _ => trivial) trivial hg, _root_.Std.HashMap.contains_eq_isSome_getElem?, ← h.get k]
  cases toFun m k <;> rfl

/-- The twin's step of `firstOwner`'s inner fold. -/
def firstOwnerIns (j : Nat) (m : _root_.Std.HashMap NIdx Nat) (n : NIdx) : _root_.Std.HashMap NIdx Nat :=
  if m.contains n then m else m.insert n j

/-- The twin's step of `ownerMap`'s inner fold. -/
def ownerIns (j : Nat) (m : _root_.Std.HashMap NIdx Nat) (n : NIdx) : _root_.Std.HashMap NIdx Nat :=
  m.insert n j

/-- **`first_owner_add` is `firstOwner`'s inner fold**: a name owned already kept. -/
theorem first_owner_add_loop_eq (ns : alloc.vec.Vec arena.handle.NIdx) (j : Std.U64)
    (hj : j.val ≤ Std.Usize.max) :
    ∀ (n : Nat) (m : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64) s (i : Std.Usize) {r},
      ns.val.length - i.val = n → IdxRel m s → first_owner_add_loop m ns j i = ok r →
      IdxRel r (((ns.val.drop i.val).map absNIdx).foldl (firstOwnerIns j.val) s) := by
  intro n
  induction n with
  | zero =>
    intro m s i r hn hm h
    rw [first_owner_add_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [vecFrom_nil _ _ _ (by omega)]; exact hm
  | succ k ih =>
    intro m s i r hn hm h
    rw [first_owner_add_loop, ite_eq_left (by scalar_tac)] at h
    have hi : i.val < ns.val.length := by omega
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hxv⟩ := ExprOps.vecIndexAt hx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := hm.contains_eq hb
    obtain ⟨m1, hm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hrel1 : IdxRel m1 (firstOwnerIns j.val s (absNIdx x)) := by
      unfold firstOwnerIns
      cases b with
      | true => rw [ite_eq_left rfl] at hm1; cases Result.ok_injective hm1; rw [← hbv]; exact hm
      | false =>
        rw [ite_eq_right (by simp)] at hm1
        obtain ⟨x1, hx1, hm1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm1
        rw [nidx_dup_id _ _ hx1] at hm1
        obtain ⟨⟨old, m2⟩, hm2, hm1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm1
        cases Result.ok_injective hm1
        rw [← hbv]; exact hm.insert hj hm2
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v := ConRon.Refine.Nat.uadd_val hi2
    have := ih m1 _ i2 (by simp at hi2v; omega) hrel1 h
    rw [vecFrom_cons _ _ _ hi, List.foldl_cons, hxv]
    simp at hi2v; rwa [hi2v] at this

/-- **`owner_add` is `ownerMap`'s inner fold**: the last record storing a name kept. -/
theorem owner_add_loop_eq (ns : alloc.vec.Vec arena.handle.NIdx) (j : Std.U64)
    (hj : j.val ≤ Std.Usize.max) :
    ∀ (n : Nat) (m : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64) s (i : Std.Usize) {r},
      ns.val.length - i.val = n → IdxRel m s → owner_add_loop m ns j i = ok r →
      IdxRel r (((ns.val.drop i.val).map absNIdx).foldl (ownerIns j.val) s) := by
  intro n
  induction n with
  | zero =>
    intro m s i r hn hm h
    rw [owner_add_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [vecFrom_nil _ _ _ (by omega)]; exact hm
  | succ k ih =>
    intro m s i r hn hm h
    rw [owner_add_loop, ite_eq_left (by scalar_tac)] at h
    have hi : i.val < ns.val.length := by omega
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hxv⟩ := ExprOps.vecIndexAt hx
    obtain ⟨x1, hx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [nidx_dup_id _ _ hx1] at h
    obtain ⟨⟨old, m1⟩, hm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hrel1 : IdxRel m1 (ownerIns j.val s (absNIdx x)) := hm.insert hj hm1
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v := ConRon.Refine.Nat.uadd_val hi2
    have := ih m1 _ i2 (by simp at hi2v; omega) hrel1 h
    rw [vecFrom_cons _ _ _ hi, List.foldl_cons, hxv]
    simp at hi2v; rwa [hi2v] at this

theorem firstOwner_eq (ds : List IDeclaration) :
    Modular.firstOwner ds = (do
      let p ← ds.foldlM (fun (acc : _root_.Std.HashMap NIdx Nat × Nat) d => do
        let ns ← Modular.declNames d
        pure (ns.foldl (firstOwnerIns acc.2) acc.1, acc.2 + 1)) ({}, 0)
      pure p.1) := rfl

theorem ownerMap_eq (ds : List IDeclaration) :
    Modular.ownerMap ds = (do
      let p ← ds.foldlM (fun (acc : _root_.Std.HashMap NIdx Nat × Nat) d => do
        let ns ← Modular.declNames d
        pure (ns.foldl (ownerIns acc.2) acc.1, acc.2 + 1)) ({}, 0)
      pure p.1) := rfl

/-- The outer loop of `first_owner`/`owner_map`, generically over the inner step. -/
theorem owner_loop_aux {pers : arena.store.PersTier} (ds : alloc.vec.Vec arena.env.IDeclaration)
    (loop : arena.monad.AState → ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64 → Std.Usize →
      Result ((core.result.Result (ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64)
        kernel.core_types.CheckError) × arena.monad.AState))
    (add : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64 → alloc.vec.Vec arena.handle.NIdx →
      Std.U64 → Result (ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64))
    (ins : Nat → _root_.Std.HashMap NIdx Nat → NIdx → _root_.Std.HashMap NIdx Nat)
    (hadd : ∀ m s ns (j : Std.U64) r, j.val ≤ Std.Usize.max → IdxRel m s → add m ns j = ok r →
      IdxRel r ((ns.val.map absNIdx).foldl (ins j.val) s))
    (hloop : ∀ st m j, loop st m j =
      (if j < alloc.vec.Vec.len ds then do
         let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
           arena.env.IDeclaration) ds j
         let (r, st1) ← decl_names pers st i1
         match r with
         | core.result.Result.Ok ns =>
           let i2 ← lift (UScalar.cast .U64 j)
           let m1 ← add m ns i2
           let j1 ← j + 1#usize
           loop st1 m1 j1
         | core.result.Result.Err e => ok (core.result.Result.Err e, st1)
       else ok (core.result.Result.Ok m, st))) :
    ∀ (n : Nat) {st lst m s} {j : Std.Usize},
      ds.val.length - j.val = n → IdxRel m s → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => IdxRel a b.1) (loop st m j) lst
        (((ds.val.drop j.val).map absIDeclaration).foldlM
          (fun (acc : _root_.Std.HashMap NIdx Nat × Nat) d => do
            let ns ← Modular.declNames d
            pure (ns.foldl (ins acc.2) acc.1, acc.2 + 1)) (s, j.val)) := by
  intro n
  induction n with
  | zero =>
    intro st lst m s j hn hm hrel hinv o st' hrun
    rw [hloop] at hrun
    rw [ite_eq_right (by scalar_tac)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
    rw [vecFrom_nil _ _ _ (by omega)]
    exact ⟨_, lst, rfl, hm, hrel, hinv⟩
  | succ k ih =>
    intro st lst m s j hn hm hrel hinv o st' hrun
    rw [hloop] at hrun
    rw [ite_eq_left (by scalar_tac)] at hrun
    have hi : j.val < ds.val.length := by omega
    obtain ⟨d, hd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨_, hdv⟩ := ExprOps.vecIndexAt hd
    obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have H := decl_names_ls hrel hinv d _ _ h1
    rw [vecFrom_cons _ _ _ hi, List.foldlM_cons, hdv, StateT.run_bind, StateT.run_bind]
    cases r with
    | Err e =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hrun)
      exact AErrSim.bind (AErrSim.bind H _) _
    | Ok ns =>
      obtain ⟨ns', lst1, hx1, rfl, hrel1, hinv1⟩ := H
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v := lift_cast_u64_of_usize j i2 hi2
      obtain ⟨m1, hm1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hj : i2.val ≤ Std.Usize.max := by rw [hi2v]; scalar_tac
      have hrel2 := hadd m s ns i2 m1 hj hm hm1
      obtain ⟨j1, hj1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hj1v := ConRon.Refine.Nat.uadd_val hj1
      simp at hj1v
      have := ih (j := j1) (by omega) hrel2 hrel1 hinv1 o st' hrun
      rw [hx1]
      simp only [except_ok_bind, absNIdxList, hi2v] at this ⊢
      rw [hj1v] at this
      exact this

/-- **`first_owner` ⊑ `firstOwner`**: each context name's first record. -/
@[lockstep] theorem first_owner_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers IdxRel (first_owner pers st ds) lst (Modular.firstOwner (absIDeclL ds)) := by
  intro o st' hrun
  rw [first_owner] at hrun
  obtain ⟨m, hm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have H := owner_loop_aux (pers := pers) ds (first_owner_loop pers · ds) first_owner_add
    firstOwnerIns
    (fun m s ns j r hj hm h => by
      simpa using first_owner_add_loop_eq ns j hj _ m s 0#usize rfl hm h)
    (fun st m j => by rw [first_owner_loop]; rfl) _ (j := 0#usize) rfl (IdxRel.empty hm) hrel hinv
    o st' hrun
  have e0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [e0, List.drop_zero] at H
  rw [firstOwner_eq, StateT.run_bind]
  simp only [absIDeclL]
  cases o with
  | Err e => exact AErrSim.bind H _
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h3, h4⟩ := H
    exact ⟨b.1, lst', by rw [hx]; rfl, hR, h3, h4⟩

/-- **`owner_map` ⊑ `ownerMap`**: each context name's last record. -/
@[lockstep] theorem owner_map_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers IdxRel (owner_map pers st ds) lst (Modular.ownerMap (absIDeclL ds)) := by
  intro o st' hrun
  rw [owner_map] at hrun
  obtain ⟨m, hm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have H := owner_loop_aux (pers := pers) ds (owner_map_loop pers · ds) owner_add
    ownerIns
    (fun m s ns j r hj hm h => by
      simpa using owner_add_loop_eq ns j hj _ m s 0#usize rfl hm h)
    (fun st m j => by rw [owner_map_loop]; rfl) _ (j := 0#usize) rfl (IdxRel.empty hm) hrel hinv
    o st' hrun
  have e0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [e0, List.drop_zero] at H
  rw [ownerMap_eq, StateT.run_bind]
  simp only [absIDeclL]
  cases o with
  | Err e => exact AErrSim.bind H _
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h3, h4⟩ := H
    exact ⟨b.1, lst', by rw [hx]; rfl, hR, h3, h4⟩

/-- **`part_pos` is `partPos`.** -/
theorem part_pos_eq {m s} (hm : IdxRel m s) (n : Std.U64) (y : arena.handle.NIdx) {r}
    (h : part_pos m n y = ok r) : r.val = Modular.partPos s n.val (absNIdx y) ∧
      (n.val ≤ Std.Usize.max → r.val ≤ Std.Usize.max) := by
  rw [part_pos] at h
  obtain ⟨o, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, hfit⟩ := hm.get_eq ho
  simp only [Modular.partPos, ← e]
  cases o with
  | none => cases Result.ok_injective h; exact ⟨rfl, id⟩
  | some j => cases Result.ok_injective h; exact ⟨rfl, fun _ => hfit _ rfl⟩


/-! ## The accept of a function whose failures carry twin-only reads

`validate_ctx`, `infer_one`, `infer_flags` and the read order fail with messages the twin
builds from `readName`, which may itself fail at another kind; so these claim their accept
only (`LA`), as the reach's file reads do. -/

/-- **The accept of a state-threading Rust computation**: its `Ok` is a run of the twin, in
related states.  An `Err` claims nothing. -/
def LA {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState))
    (lst : AState) (x : AM β) : Prop :=
  ∀ a st', m = ok (.Ok a, st') →
    ∃ b lst', x.run lst = .ok (b, lst') ∧ R a b ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st'

theorem LS.toLA {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R m lst x) : LA pers R m lst x :=
  fun _ _ hm => h _ _ hm

/-! ## The validation of the context -/

theorem validate_ctx_loop_aux {pers : arena.store.PersTier} (ds : alloc.vec.Vec arena.env.IDeclaration)
    (hs : alloc.vec.Vec arena.handle.NIdx) (n : Nat) :
    ∀ {st lst} {i : Std.Usize}, ds.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun _ _ => True) (validate_ctx_loop pers st ds hs i) lst
        (Modular.validateCtx ((ds.val.drop i.val).map absIDeclaration) (hs.val.map absNIdx).toArray
          i.val) := by
  induction n with
  | zero =>
    intro st lst i hn hrel hinv a st' h
    rw [validate_ctx_loop, ite_eq_right (by scalar_tac)] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    rw [vecFrom_nil _ _ _ (by omega)]
    exact ⟨(), lst, rfl, trivial, hrel, hinv⟩
  | succ k ih =>
    intro st lst i hn hrel hinv a st' h
    rw [validate_ctx_loop, ite_eq_left (by scalar_tac)] at h
    have hi : i.val < ds.val.length := by omega
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hdv⟩ := ExprOps.vecIndexAt hd
    obtain ⟨⟨r, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have H := record_ok_ls hrel hinv d _ _ h1
    rw [vecFrom_cons _ _ _ hi, hdv]
    simp only [Modular.validateCtx]
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok b =>
      obtain ⟨b', lst1, hx1, hbb, hrel1, hinv1⟩ := H
      subst hbb
      cases b' with
      | false =>
        obtain ⟨⟨ce, st2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases Result.ok_injective h
      | true =>
        obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi3v := ConRon.Refine.Nat.uadd_val hi3
        simp at hi3v
        obtain ⟨b2, lst2, hx2, -, hrel2, hinv2⟩ := ih (i := i3) (by omega) hrel1 hinv1 a st' h
        rw [hi3v] at hx2
        refine ⟨b2, lst2, ?_, trivial, hrel2, hinv2⟩
        rw [StateT.run_bind, hx1]
        exact hx2

/-- **`validate_ctx` ⊑ `validateCtx`, accepting**: every context record validated. -/
theorem validate_ctx_la {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ds : alloc.vec.Vec arena.env.IDeclaration)
    (hs : alloc.vec.Vec arena.handle.NIdx) :
    LA pers (fun _ _ => True) (validate_ctx pers st ds hs) lst
      (Modular.validateCtx (absIDeclL ds) (hs.val.map absNIdx).toArray 0) := by
  have := validate_ctx_loop_aux (pers := pers) ds hs _ (i := 0#usize) rfl hrel hinv
  simpa [absIDeclL] using this

/-! ## The inferred flags -/

/-- `type_is_prop_c` ⊑ `typeIsPropC`. -/
@[lockstep] theorem type_is_prop_c_ls {pers st lst} {fe lfe} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI pers fe lfe) (cv : frontend.olean.spec.StmtRec) :
    LS pers (fun a b => b = a) (type_is_prop_c pers st fe cv) lst
      (Modular.typeIsPropC lfe (Frontend.Olean.absStmtRec cv)) := by
  have hctx := IFEnvInv.coreCtx hfe.rel hfe.inv
  rw [type_is_prop_c, Modular.typeIsPropC]
  simp only [Frontend.Olean.absStmtRec]
  lockstep

/-- **`cps_dup` copies.** -/
theorem cps_dup_loop_eq (a : alloc.vec.Vec Std.U32) :
    ∀ (n : Nat) (out : alloc.vec.Vec Std.U32) (i : Std.Usize) {r},
      a.val.length - i.val = n → cps_dup_loop a out i = ok r → r.val = out.val ++ a.val.drop i.val := by
  intro n
  induction n with
  | zero =>
    intro out i r hn h
    rw [cps_dup_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ m ih =>
    intro out i r hn h
    rw [cps_dup_loop, ite_eq_left (by scalar_tac)] at h
    have hi : i.val < a.val.length := by omega
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hxv⟩ := ExprOps.vecIndexAt hx
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hout1v : out1.val = out.val ++ [x] := ConRon.Refine.vec_push_val hout1
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v := ConRon.Refine.Nat.uadd_val hi2
    simp at hi2v
    rw [ih out1 i2 (by omega) h, hout1v, hi2v, List.drop_eq_getElem_cons hi, hxv]
    simp

theorem cps_dup_eq (a : alloc.vec.Vec Std.U32) {r} (h : cps_dup a = ok r) : r.val = a.val := by
  rw [cps_dup] at h
  simpa [alloc.vec.Vec.with_capacity] using cps_dup_loop_eq a _ _ 0#usize rfl h


/-- **`infer_one` ⊑ `inferOne`, accepting**: a recorded statement's names stored before it,
its type a proposition.  The message `what` is not related. -/
theorem infer_one_la {pers st lst fe lfe} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI pers fe lfe) (what : alloc.vec.Vec Std.U32)
    (w : String) (y : arena.handle.NIdx) (cv : frontend.olean.spec.StmtRec) :
    LA pers (fun _ _ => True) (infer_one pers st fe what y cv) lst
      (Modular.inferOne lfe w (absNIdx y) (Frontend.Olean.absStmtRec cv)) := by
  intro a st' h
  rw [infer_one] at h
  obtain ⟨⟨r1, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have H1 := expr_ok_ls hrel hinv cv.level_params 0#u64 cv.ty _ _ h1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok b =>
    obtain ⟨b', lst1, hx1, hbb, hrel1, hinv1⟩ := H1
    subst hbb
    cases b' with
    | false => err_contra h
    | true =>
      obtain ⟨⟨r2, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have H2 := consts_resolve_f_fast_ls (e := cv.ty) hrel1 hinv1 hfe _ _ h2
      cases r2 with
      | Err e => cases Result.ok_injective h
      | Ok b =>
        obtain ⟨b', lst2, hx2, hbb, hrel2, hinv2⟩ := H2
        subst hbb
        cases b' with
        | false => err_contra h
        | true =>
          obtain ⟨⟨r3, st3⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have H3 := type_is_prop_c_ls hrel2 hinv2 hfe cv _ _ h3
          cases r3 with
          | Err e => cases Result.ok_injective h
          | Ok b =>
            obtain ⟨b', lst3, hx3, hbb, hrel3, hinv3⟩ := H3
            subst hbb
            cases b' with
            | false => err_contra h
            | true =>
              obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
              refine ⟨(), lst3, ?_, trivial, hrel3, hinv3⟩
              have e0 : absU (0#u64) = 0 := rfl
              simp only [absNIdxL, e0] at hx1
              simp only [Modular.inferOne, Frontend.Olean.absStmtRec_levelParams,
                Frontend.Olean.absStmtRec_type]
              simp only [StateT.run_bind, hx1, except_ok_bind, ↓reduceIte, hx2, Bool.not_true,
                Bool.false_eq_true]
              rw [show StateT.run (pure PUnit.unit : AM PUnit) lst2 = .ok (PUnit.unit, lst2) from rfl,
                except_ok_bind, hx3]
              rfl


/-- **A recorded statement**, as the twin's: its name and its statement (the message is
not related). -/
def PendRel (r : alloc.vec.Vec Std.U32 × arena.handle.NIdx × frontend.olean.spec.StmtRec)
    (t : String × NIdx × Arena.Frontend.Olean.StmtRec) : Prop :=
  t.2.1 = absNIdx r.2.1 ∧ t.2.2 = Frontend.Olean.absStmtRec r.2.2

/-- **`infer_flags`' loop ⊑ `inferAll`, accepting**, between two idle workers: each recorded
statement inferred in its own bracket, at the view of its part's position. -/
theorem infer_flags_loop_la {tier : arena.store.PersTier} {I : IStreamIndex}
    (htf : tier.frozen = true) (hI : StreamIndexRel tier.env I ∧ FrozenRel tier.env I)
    {owner : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64} {s : _root_.Std.HashMap NIdx Nat}
    (hown : IdxRel owner s) {nU : Std.U64} (hnU : nU.val ≤ Std.Usize.max)
    (pending : alloc.vec.Vec (alloc.vec.Vec Std.U32 × arena.handle.NIdx × frontend.olean.spec.StmtRec)) :
    ∀ (k : Nat) {st lst} {i : Std.Usize} {P : List (String × NIdx × Arena.Frontend.Olean.StmtRec)},
      pending.val.length - i.val = k → List.Forall₂ PendRel (pending.val.drop i.val) P →
      AIdle tier st lst → AStateInv tier st →
      ∀ st', infer_flags_loop tier st pending owner nU i = ok (.Ok (), st') →
        ∃ lst', (Modular.inferAll I s nU.val P).run lst = .ok ((), lst') ∧
          AIdle tier st' lst' ∧ AStateInv tier st' := by
  intro k
  induction k with
  | zero =>
    intro st lst i P hn hP hidle hinv st' h
    rw [infer_flags_loop, ite_eq_right (by scalar_tac)] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    rw [List.drop_eq_nil_of_le (by omega)] at hP
    cases hP
    exact ⟨lst, rfl, hidle, hinv⟩
  | succ k ih =>
    intro st lst i P hn hP hidle hinv st' h
    rw [infer_flags_loop, ite_eq_left (by scalar_tac)] at h
    have hi : i.val < pending.val.length := by omega
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, hxv⟩ := ExprOps.vecIndexAt hx
    rw [List.drop_eq_getElem_cons hi, hxv] at hP
    obtain ⟨⟨w, y, cv⟩, P', ⟨hy, hcv⟩, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp hP
    obtain ⟨v, n1, sr⟩ := x
    dsimp only at hy hcv h
    subst hy hcv
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hpos, hfit⟩ := part_pos_eq hown nU n1 hi2
    obtain ⟨fe, hfe, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hfeR := stream_index_view_rel hI.1 hI.2 (hfit hnU) hfe
    obtain ⟨st1, hst1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (enter_record_sim hidle hinv hst1).apply
    obtain ⟨⟨r, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨st3, hst3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e => cases Result.ok_injective h
    | Ok u =>
      cases u
      obtain ⟨_, lst2, hx2, -, hrel2, hinv2⟩ := infer_one_la hrel1 hinv1 hfeR v w n1 sr () st2 h2
      obtain ⟨lst3, hx3, hidle3, hinv3⟩ := leave_record_rel hrel2 hinv2 htf hst3
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi3v := ConRon.Refine.Nat.uadd_val hi3
      simp at hi3v
      obtain ⟨lst4, hx4, hidle4, hinv4⟩ :=
        ih (i := i3) (P := P') (by omega) (by rw [hi3v]; exact hrest) hidle3 hinv3 st' h
      refine ⟨lst4, ?_, hidle4, hinv4⟩
      have hview : absU i2 = Modular.partPos s nU.val (absNIdx n1) := hpos
      rw [hview] at hx2
      simp only [Modular.inferAll, StateT.run_bind, hx1, except_ok_bind, hx2, hx3, hx4]

end ConRon.Refine2.Modular
