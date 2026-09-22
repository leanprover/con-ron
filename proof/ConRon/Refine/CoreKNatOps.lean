/-
`CORE_PLAN.md` step 4 (task #49): the **`Nat`-operation pinning guards** of
`crates/con-ron-core/src/kernel/core_k.rs` — the eight predicates that license
the arithmetic fast path by pinning the stored declarations of `Nat.add` and
friends (`core_k.rs:1634-1852`).

Cited Lean: `ConLeche/Kernel/Core.lean:656-772` (`natOpGuard`, `natOpCod`,
`natOpTyPinned`, `natOpStoredOk`, `natOpStored`) and the index twins that
actually get stated here — `ConLeche/Kernel/FEnv.lean:133-152`
(`natOpGuardF`, `natOpStoredF`) and `ConLeche/Kernel/DeclCheck.lean:209-238`
(`natOpCodF`, `natOpTyPinnedF`, `natOpStoredOkF`).  `CoreKBase.lean`'s
`FindAgree` is *find*-agreement only, so the `F` twin is what a refinement of an
`FEnv`-reading guard can say; `ConLeche/Verify/CheckerF.lean:74-119`
(`natOpCodF_eq`, `natOpTyPinnedF_eq`, `natOpStoredOkF_eq`, `natOpGuardF_eq`)
turns each back into the `Env` version under `mkFEnv`.

Three things are worth recording.

* **The imported hypotheses.**  Five of these eight functions call something
  another task-#49 agent owns — the pinned names of `core_k.rs`
  (`bool_name`, `bool_true_name`, …, and the `nat_op_deps`/`nat_div_mod_names`
  name *lists*), `lp_empty`, `nat_lit_supported`, `defn_probe` — and
  `bool_stored_ok`/`lp_empty` both go through `env::to_constant_val`, which
  belongs to task #46's `Refine/Env.lean`.  Each is taken as an explicit
  hypothesis, packaged as one of the `*Spec`/`Pinned*` predicates below
  so the statements stay readable; the parent agent discharges them at merge.
  Nothing here proves a pinned name.

* **`nat_op_ty_pinned` is a depth-two node match**, so its proof cases the
  node twice (not an induction — the port's function does not recurse) and
  gets the children's well-formedness from `forall_e_wf_inv`, an inversion of
  the `ExprWF` derivation at a `.forallE` node that belongs in
  `Refine/Expr.lean`.  The Rust's `if dom then (if dom2 then cod else false)
  else false` nesting is the Lean's `&&` chain, and the nine non-`forallE`
  arms are `false` on both sides.

* **`rw` on a con-leche `match` definition generates splitter side goals**
  (`natOpTyPinnedF`, `natOpStoredOkF`): `unfold` is what leaves the matcher in
  place so it can iota-reduce once the node has been cased.  For the two
  guards whose Lean body stays opaque (`natOpGuardF`, `natOpCodF`) there is a
  spelled-out mirror (`natOpGuardL`, `natOpCodL`) with the shared clauses
  named; each mirror is the cited function by `rfl`.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.FEnv
import ConLeche.Kernel.DeclCheck

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK


/-! ## Plumbing -/

/-- `cv.level_params.len() == 0` is `levelParams.isEmpty` — the port counts
where the Lean asks for emptiness, and `absNames` is a `List.map`. -/
theorem absNames_isEmpty (ns : alloc.vec.Vec name.Name) :
    (absNames ns).isEmpty = decide (alloc.vec.Vec.len ns = 0#usize) := by
  have h : (alloc.vec.Vec.len ns).val = ns.val.length := alloc.vec.Vec.len_val ns
  rw [absNames, List.isEmpty_map]
  rcases hl : ns.val with _ | ⟨x, xs⟩
  · rw [hl] at h
    rw [decide_eq_true (show alloc.vec.Vec.len ns = 0#usize by scalar_tac)]; rfl
  · rw [hl] at h
    rw [decide_eq_false (show ¬(alloc.vec.Vec.len ns = 0#usize) by
      intro he; rw [he] at h; simp at h)]; rfl

/-! ## The imported facts, as hypotheses

Every predicate in this section is somebody else's refinement lemma, stated
here so that this file proves none of them (`BRIEF.md` rule 1).  `PinnedName`
and `PinnedNames` are the §3.5 statement of a pinned name and of a pinned
`Vec<Name>`; the `*Spec`s are the statements of `core_k::lp_empty`,
`core_k::nat_lit_supported`, `env::to_constant_val` and (further down, where
its `defnProbeL` is) `core_k::defn_probe`. -/

/-- The cited `match env.find? n with | some ci =>
ci.toConstantVal.levelParams.isEmpty | none => false` predicate
(`Core.lean:660-671`), which `core_k::lp_empty` is. -/
def lpEmptyL (lfe : ConLeche.FEnv) (n : ConLeche.Name) : Bool :=
  match lfe.find? n with
  | some ci => ci.toConstantVal.levelParams.isEmpty
  | none => false

/-- **Imported**: `core_k::lp_empty` refines `lpEmptyL`. -/
def LpEmptySpec (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  ∀ (n : name.Name) (b : Bool), NameWF n →
    core_k.lp_empty fe n = ok b → b = lpEmptyL lfe (absName n)

/-- **Imported**: `core_k::nat_lit_supported` refines `natLitSupportedF`
(`FEnv.lean:117-119`). -/
def NatLitSupportedSpec (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  ∀ b : Bool, core_k.nat_lit_supported fe = ok b → b = ConLeche.natLitSupportedF lfe

/-- **Imported**: `env::to_constant_val` refines `ConstantInfo.toConstantVal`
(`Env.lean:606-609`).  Needed by `bool_stored_ok` here and by `core_k::lp_empty`
elsewhere, so it belongs in `CoreKBase.lean`. -/
def ToConstantValSpec : Prop :=
  ∀ (ci : env.ConstantInfo) (cv : env.ConstantVal), ConstantInfoWF ci →
    env.to_constant_val ci = ok cv →
      absConstantVal cv = (absConstantInfo ci).toConstantVal ∧ ConstantValWF cv

/-! ## `defn_lp_empty` and `deps_all_stored` (`Core.lean:660-662`) -/

/-- The per-dependency clause of `natOpGuard`'s `List.all`
(`Core.lean:660-662`), as its own function — `core_k::defn_lp_empty` is it. -/
def natOpDepStored (lfe : ConLeche.FEnv) : ConLeche.Name → Bool := fun n =>
  match lfe.find? n with
  | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
  | _ => false

/-- **`core_k::defn_lp_empty` refines the per-dependency clause of
`natOpGuardF`** (`ConLeche/Kernel/Core.lean:656-672 natOpGuard`,
`ConLeche/Kernel/FEnv.lean:133-147 natOpGuardF`): the dependency is stored as
a level-monomorphic definition. -/
theorem defn_lp_empty_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} {b : Bool} (hfe : FindAgree fe lfe) (hn : NameWF n)
    (h : core_k.defn_lp_empty fe n = ok b) :
    b = natOpDepStored lfe (absName n) := by
  rw [core_k.defn_lp_empty] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  cases o with
  | none =>
    rw [natOpDepStored, hfe.find_none hn ho]
    simpa using h.symm
  | some ci =>
    rw [natOpDepStored, hfe.find_some hn ho]
    cases ci with
    | DefnInfo cv v hint =>
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact (absNames_isEmpty cv.level_params).symm
    | _ => simp only [Result.ok.injEq] at h; rw [← h]; rfl

/-- The index recursion behind `core_k::deps_all_stored`: from index `i` on it
is the `List.all` of the dropped tail. -/
theorem deps_all_stored_from {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfe : FindAgree fe lfe) {deps : alloc.vec.Vec name.Name} (hdeps : NamesWF deps) :
    ∀ k (i : Std.Usize), deps.val.length - i.val ≤ k → ∀ b : Bool,
      core_k.deps_all_stored fe deps i = ok b →
      b = ((deps.val.drop i.val).map absName).all (natOpDepStored lfe) := by
  intro k
  induction k with
  | zero =>
    intro i hk b h
    rw [core_k.deps_all_stored.eq_def] at h
    simp only [] at h
    rw [if_pos (by have := alloc.vec.Vec.len_val deps; scalar_tac)] at h
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simpa using h.symm
  | succ k ih =>
    intro i hk b h
    rw [core_k.deps_all_stored.eq_def] at h
    simp only [] at h
    split at h
    · rw [List.drop_eq_nil_of_le
        (by have := alloc.vec.Vec.len_val deps; scalar_tac)]
      simpa using h.symm
    · rename_i hlt
      have hb : i.val < deps.val.length := by
        have := alloc.vec.Vec.len_val deps; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hx, b1, hb1, h⟩ := h
      have hxv : deps.val[i.val] = x := by
        have hg := ExprOps.vec_index_getElem? hx
        rw [List.getElem?_eq_getElem hb] at hg
        exact Option.some_injective _ hg
      have hxwf : NameWF x := hdeps x (by rw [← hxv]; exact List.getElem_mem hb)
      have he1 := defn_lp_empty_refines hfe hxwf hb1
      rw [List.drop_eq_getElem_cons hb, hxv]
      simp only [List.map_cons, List.all_cons]
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← he1]; rfl
      | true =>
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨w, hw, h⟩ := h
        have hwv : w.val = i.val + 1 := HashMap.uscalar_add_eq hw
        rw [ih w (by scalar_tac) b h, hwv, ← he1]
        simp

/-- **`core_k::deps_all_stored` refines the `List.all` of `natOpGuardF`'s
dependency clause** (`ConLeche/Kernel/Core.lean:656-672 natOpGuard`,
`ConLeche/Kernel/FEnv.lean:133-147 natOpGuardF`). -/
theorem deps_all_stored_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {deps : alloc.vec.Vec name.Name} {b : Bool} (hfe : FindAgree fe lfe)
    (hdeps : NamesWF deps) (h : core_k.deps_all_stored fe deps 0#usize = ok b) :
    b = (absNames deps).all (natOpDepStored lfe) := by
  have hz : (0#usize : Std.Usize).val = 0 := rfl
  rw [deps_all_stored_from hfe hdeps deps.val.length 0#usize (by scalar_tac) b h, hz,
    List.drop_zero, absNames]

/-! ## `nat_op_guard` (`Core.lean:656-672`, `FEnv.lean:133-147`) -/

/-- `natOpGuardF` with its dependency clause and its two `Bool`-constructor
clauses named (`natOpDepStored`, `lpEmptyL`).  Definitionally the cited
function — the port factors the same three lines out into `defn_lp_empty` and
`lp_empty`. -/
def natOpGuardL (lfe : ConLeche.FEnv) (c : ConLeche.Name) : Bool :=
  ConLeche.natLitSupportedF lfe &&
  (ConLeche.natOpDeps c).all (natOpDepStored lfe) &&
  (if c = ConLeche.natBeqName || c = ConLeche.natBleName ||
      ConLeche.natDivModNames.contains c then
    lpEmptyL lfe ConLeche.boolTrueName && lpEmptyL lfe ConLeche.boolFalseName
   else true)

theorem natOpGuardL_eq (lfe : ConLeche.FEnv) (c : ConLeche.Name) :
    ConLeche.natOpGuardF lfe c = natOpGuardL lfe c := rfl

/-- The `Bool`-constructor half of `nat_op_guard`, which the Rust spells out
once per arm of its three-way name test. -/
theorem bool_ctors_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hlp : LpEmptySpec fe lfe)
    (hbt : PinnedName core_k.bool_true_name ConLeche.boolTrueName)
    (hbf : PinnedName core_k.bool_false_name ConLeche.boolFalseName)
    (h : ∃ n, core_k.bool_true_name = ok n ∧ ∃ x, core_k.lp_empty fe n = ok x ∧
      (if x = true then (do let n2 ← core_k.bool_false_name; core_k.lp_empty fe n2)
       else ok false) = ok b) :
    b = (lpEmptyL lfe ConLeche.boolTrueName && lpEmptyL lfe ConLeche.boolFalseName) := by
  obtain ⟨n, hn, x, hx, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hbt n hn
  have ex := hlp n x hnwf hx
  rw [hnabs] at ex
  cases x
  · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← ex]; rfl
  · simp only [reduceIte, bind_eq_ok_iff] at h
    obtain ⟨n2, hn2, h⟩ := h
    obtain ⟨h2abs, h2wf⟩ := hbf n2 hn2
    have ex2 := hlp n2 b h2wf h
    rw [h2abs] at ex2
    rw [ex2, ← ex]; rfl

/-- **`core_k::nat_op_guard` refines `natOpGuardF`**
(`ConLeche/Kernel/Core.lean:656-672 natOpGuard`,
`ConLeche/Kernel/FEnv.lean:133-147 natOpGuardF`) — the headline guard of this
file: the `Nat` basis, every dependency of `c` stored as a level-monomorphic
definition, and, for the `Bool`-valued ops and the `ble`-guarded `div`/`mod`,
the two `Bool` constructors stored level-monomorphically too.  The Rust's
three-way `beq`/`beq`/`contains` nest is the Lean's one `||` condition, and the
Rust's `if ... then ... else false` nesting is the Lean's `&&` chain.

Imported (`BRIEF.md`, another task-#49 agent): `NatLitSupportedSpec`,
`LpEmptySpec`, and the pinned names `nat_op_deps`, `nat_beq_name`,
`nat_ble_name`, `nat_div_mod_names`, `bool_true_name`, `bool_false_name`. -/
theorem nat_op_guard_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {b : Bool} (hfe : FindAgree fe lfe) (hc : NameWF c)
    (hnls : NatLitSupportedSpec fe lfe) (hlp : LpEmptySpec fe lfe)
    (hnod : PinnedNames (core_k.nat_op_deps c) (ConLeche.natOpDeps (absName c)))
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hdmn : PinnedNames core_k.nat_div_mod_names ConLeche.natDivModNames)
    (hbt : PinnedName core_k.bool_true_name ConLeche.boolTrueName)
    (hbf : PinnedName core_k.bool_false_name ConLeche.boolFalseName)
    (h : core_k.nat_op_guard fe c = ok b) :
    b = ConLeche.natOpGuardF lfe (absName c) := by
  rw [natOpGuardL_eq, natOpGuardL]
  rw [core_k.nat_op_guard] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b0, hb0, h⟩ := h
  rw [← hnls b0 hb0]
  cases b0
  · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]; rfl
  · simp only [reduceIte, bind_eq_ok_iff] at h
    obtain ⟨v, hv, b1, hb1, h⟩ := h
    obtain ⟨hvabs, hvwf⟩ := hnod v hv
    have e1 := deps_all_stored_refines hfe hvwf hb1
    rw [hvabs] at e1
    rw [← e1]
    cases b1
    · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      rw [← h]; rfl
    · simp only [reduceIte, bind_eq_ok_iff] at h
      obtain ⟨n, hn, b2, hb2, h⟩ := h
      obtain ⟨hnabs, hnwf⟩ := hbeq n hn
      have e2 := Name.beq_refines hc hnwf hb2
      rw [hnabs] at e2
      rw [← e2]
      cases b2
      · -- not `Nat.beq`: try `Nat.ble`
        simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, b3, hb3, h⟩ := h
        obtain ⟨h1abs, h1wf⟩ := hble n1 hn1
        have e3 := Name.beq_refines hc h1wf hb3
        rw [h1abs] at e3
        rw [← e3]
        cases b3
        · -- not `Nat.ble` either: the `natDivModNames` membership test
          simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
          obtain ⟨v1, hv1, b4, hb4, h⟩ := h
          obtain ⟨h4abs, h4wf⟩ := hdmn v1 hv1
          have e4 := Name.contains_refines h4wf hc hb4
          rw [h4abs] at e4
          rw [← e4]
          cases b4
          · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
            rw [← h]; rfl
          · simp only [reduceIte, bind_eq_ok_iff] at h
            rw [bool_ctors_refines hlp hbt hbf h]; rfl
        · simp only [reduceIte, bind_eq_ok_iff] at h
          rw [bool_ctors_refines hlp hbt hbf h]; rfl
      · simp only [reduceIte, bind_eq_ok_iff] at h
        rw [bool_ctors_refines hlp hbt hbf h]; rfl

/-! ## `nat_op_cod` and `bool_stored_ok` (`Core.lean:712-722`,
`DeclCheck.lean:209-217`) -/

/-- con-leche's `==` on `Expr` is its `Expr.beq`, which *is* `decide (· = ·)`
(`Expr.lean:976`) — the form `Expr.beq_refines` hands back. -/
theorem expr_beq_decide (a b : ConLeche.Expr) : (a == b) = decide (a = b) := rfl

/-- `expr::sort (level::succ (level::zero))` — the `Sort 1` at which the pinned
`Bool` type is stored. -/
theorem sort_one_step {l l1 : level.Level} {e : expr.Expr}
    (hl : level.zero = ok l) (hl1 : level.succ l = ok l1) (he : expr.sort l1 = ok e) :
    absExpr e = .sort (.succ .zero) ∧ ExprWF e := by
  refine ⟨?_, Expr.sort_wf (Level.succ_wf (Level.zero_wf hl) hl1) he⟩
  rw [Expr.sort_refines he, Level.succ_refines hl1, Level.zero_refines hl]

/-- `expr::mk_const n Vec::new()` at a pinned name: the level-monomorphic
`.const` node these guards compare against. -/
theorem const_no_levels_step {n : name.Name} {e : expr.Expr} {ln : ConLeche.Name}
    (hn : absName n = ln ∧ NameWF n)
    (he : expr.mk_const n (alloc.vec.Vec.new level.Level) = ok e) :
    absExpr e = .const ln [] ∧ ExprWF e := by
  have hlv : LevelsWF (alloc.vec.Vec.new level.Level) := by
    intro u hu; simp [alloc.vec.Vec.new] at hu
  refine ⟨?_, Expr.mk_const_wf hn.2 hlv he⟩
  rw [Expr.mk_const_refines he, hn.1]
  rfl

/-- The `Bool`-is-stored-at-`Sort 1` clause of `natOpCod`
(`Core.lean:716-720`), which `core_k::bool_stored_ok` factors out. -/
def boolStoredL (lfe : ConLeche.FEnv) : Bool :=
  match lfe.find? ConLeche.boolName with
  | some ci => ci.toConstantVal.levelParams.isEmpty &&
      ci.toConstantVal.type == .sort (.succ .zero)
  | none => false

/-- **`core_k::bool_stored_ok` refines the `Bool`-stored clause of `natOpCodF`**
(`ConLeche/Kernel/Core.lean:712-722 natOpCod`,
`ConLeche/Kernel/DeclCheck.lean:209-217 natOpCodF`): `Bool` is stored
level-monomorphically at `Sort 1`.

Imported: the pinned name `bool_name` and `ToConstantValSpec`. -/
theorem bool_stored_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName) (htcv : ToConstantValSpec)
    (h : core_k.bool_stored_ok fe = ok b) : b = boolStoredL lfe := by
  rw [core_k.bool_stored_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hbn n hn
  rw [boolStoredL, ← hnabs]
  cases o with
  | none => rw [hfe.find_none hnwf ho]; simpa using h.symm
  | some ci =>
    rw [hfe.find_some hnwf ho]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := htcv ci cv (hwf n ci hnwf ho) hcv
    show b = ((absConstantInfo ci).toConstantVal.levelParams.isEmpty &&
      ((absConstantInfo ci).toConstantVal.type == ConLeche.Expr.sort (.succ .zero)))
    rw [← hcvabs]
    simp only [absConstantVal]
    split at h
    · rename_i hlen
      simp only [bind_eq_ok_iff] at h
      obtain ⟨l, hl, l1, hl1, e, he, hbeq⟩ := h
      obtain ⟨heabs, hewf⟩ := sort_one_step hl hl1 he
      rw [Expr.beq_refines hcvwf.2.2 hewf hbeq, heabs, absNames_isEmpty, hlen,
        expr_beq_decide]
      rfl
    · rename_i hlen
      rw [absNames_isEmpty, decide_eq_false hlen]
      simpa using h.symm

/-- `natOpCodF` with its `Bool`-stored clause named.  Definitionally the cited
function. -/
def natOpCodL (lfe : ConLeche.FEnv) (c : ConLeche.Name) (e : ConLeche.Expr) : Bool :=
  if c = ConLeche.natBeqName || c = ConLeche.natBleName then
    (e == .const ConLeche.boolName []) && boolStoredL lfe
  else e == .const ConLeche.natName []

theorem natOpCodL_eq (lfe : ConLeche.FEnv) (c : ConLeche.Name) (e : ConLeche.Expr) :
    ConLeche.natOpCodF lfe c e = natOpCodL lfe c e := rfl

/-- The `Bool` codomain arm of `nat_op_cod`, which the Rust spells out once for
`Nat.beq` and once for `Nat.ble`. -/
theorem bool_cod_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {e : expr.Expr}
    {b : Bool} (hfe : FindAgree fe lfe) (hwf : FindWF fe) (he : ExprWF e)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName) (htcv : ToConstantValSpec)
    (h : ∃ n, core_k.bool_name = ok n ∧
      ∃ e1, expr.mk_const n (alloc.vec.Vec.new level.Level) = ok e1 ∧
        ∃ x, expr.beq e e1 = ok x ∧
          (if x = true then core_k.bool_stored_ok fe else ok false) = ok b) :
    b = ((absExpr e == ConLeche.Expr.const ConLeche.boolName []) && boolStoredL lfe) := by
  obtain ⟨n, hn, e1, he1, x, hx, h⟩ := h
  obtain ⟨h1abs, h1wf⟩ := const_no_levels_step (hbn n hn) he1
  have ex := Expr.beq_refines he h1wf hx
  rw [h1abs] at ex
  rw [expr_beq_decide, ← ex]
  cases x
  · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]; rfl
  · simp only [reduceIte] at h
    rw [bool_stored_ok_refines hfe hwf hbn htcv h]; rfl

/-- **`core_k::nat_op_cod` refines `natOpCodF`**
(`ConLeche/Kernel/Core.lean:712-722 natOpCod`,
`ConLeche/Kernel/DeclCheck.lean:209-217 natOpCodF`): the pinned codomain of a
structural-`Nat` operation — `Bool` for the two comparisons, `Nat` otherwise.

Imported: the pinned names `nat_beq_name`, `nat_ble_name`, `bool_name`,
`basis_names::nat_name`, and `ToConstantValSpec`. -/
theorem nat_op_cod_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {c : name.Name}
    {e : expr.Expr} {b : Bool} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (hc : NameWF c) (he : ExprWF e)
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName)
    (hnatn : PinnedName basis_names.nat_name ConLeche.natName)
    (htcv : ToConstantValSpec)
    (h : core_k.nat_op_cod fe c e = ok b) :
    b = ConLeche.natOpCodF lfe (absName c) (absExpr e) := by
  rw [natOpCodL_eq, natOpCodL]
  rw [core_k.nat_op_cod] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, b1, hb1, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hbeq n hn
  have e1 := Name.beq_refines hc hnwf hb1
  rw [hnabs] at e1
  rw [← e1]
  cases b1
  · simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, b2, hb2, h⟩ := h
    obtain ⟨h1abs, h1wf⟩ := hble n1 hn1
    have e2 := Name.beq_refines hc h1wf hb2
    rw [h1abs] at e2
    rw [← e2]
    cases b2
    · -- neither comparison: the codomain is `Nat`
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
      obtain ⟨n2, hn2, e2', he2', hbeq'⟩ := h
      obtain ⟨h2abs, h2wf⟩ := const_no_levels_step (hnatn n2 hn2) he2'
      rw [Expr.beq_refines he h2wf hbeq', h2abs, expr_beq_decide]
      rfl
    · simp only [reduceIte, bind_eq_ok_iff] at h
      rw [bool_cod_refines hfe hwf he hbn htcv h]; rfl
  · simp only [reduceIte, bind_eq_ok_iff] at h
    rw [bool_cod_refines hfe hwf he hbn htcv h]; rfl

/-! ## `nat_op_ty_pinned` (`Core.lean:724-739`, `DeclCheck.lean:219-231`) -/

/-- Inverting `ExprWF` at a `.forallE` node: the two children are well formed
and so is the binder datum.  `nat_op_ty_pinned` is the one guard in this file
that walks *into* a term without recursing, so it needs the children's
well-formedness without an induction; the lemma belongs in `Refine/Expr.lean`
beside the `Expr.*_inv` family. -/
theorem forall_e_wf_inv {d : Std.U64} {a b : expr.Expr} {m : expr.BinderMeta}
    (h : ExprWF (.mk (.mk d (.ForallE a b m)))) :
    ExprWF a ∧ ExprWF b ∧ BinderMetaWF m := by
  cases h with
  | @bvar i e h1 => obtain ⟨d1, he, -, -, -⟩ := Expr.bvar_inv h1; simp at he
  | @fvar idx t e ht h1 => obtain ⟨d1, he, -, -, -⟩ := Expr.fvar_inv h1; simp at he
  | @sort u e hu h1 => obtain ⟨d1, bb, -, he, -, -, -⟩ := Expr.sort_inv h1; simp at he
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, bb, -, he, -, -, -⟩ := Expr.mk_const_inv h1; simp at he
  | @app f a2 e hf ha h1 => obtain ⟨d1, he, -, -, -⟩ := Expr.app_inv h1; simp at he
  | @lam t b2 m2 e ht hb hm h1 => obtain ⟨d1, he, -, -, -⟩ := Expr.lam_inv h1; simp at he
  | @forall_e t b2 m2 e ht hb hm h1 =>
    obtain ⟨d1, he, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq, expr.ExprKind.ForallE.injEq] at he
    obtain ⟨-, rfl, rfl, rfl⟩ := he
    exact ⟨ht, hb, hm⟩
  | @let_e t v b2 e ht hv hb h1 => obtain ⟨d1, he, -, -, -⟩ := Expr.let_e_inv h1; simp at he
  | @lit l e hl h1 => obtain ⟨d1, he, -, -, -⟩ := Expr.lit_inv h1; simp at he
  | @proj s i x e hs hx h1 => obtain ⟨d1, he, -, -, -⟩ := Expr.proj_inv h1; simp at he

/-- **`core_k::nat_op_ty_pinned` refines `natOpTyPinnedF`**
(`ConLeche/Kernel/Core.lean:724-739 natOpTyPinned`,
`ConLeche/Kernel/DeclCheck.lean:219-231 natOpTyPinnedF`): `Nat → Nat` for the
unary `pred`, `Nat → Nat → Nat`/`Nat → Nat → Bool` for the binary ones.  The
depth-two node match is two nested `cases` on the `ExprWF` derivation, the
inner one through `forall_e_wf_inv`.

Imported: the pinned names `nat_pred_name`, `nat_beq_name`, `nat_ble_name`,
`bool_name`, `basis_names::nat_name`, and `ToConstantValSpec`. -/
theorem nat_op_ty_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {ty : expr.Expr} {b : Bool} (hfe : FindAgree fe lfe)
    (hwf : FindWF fe) (hc : NameWF c) (hty : ExprWF ty)
    (hpred : PinnedName core_k.nat_pred_name ConLeche.natPredName)
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName)
    (hnatn : PinnedName basis_names.nat_name ConLeche.natName)
    (htcv : ToConstantValSpec)
    (h : core_k.nat_op_ty_pinned fe c ty = ok b) :
    b = ConLeche.natOpTyPinnedF lfe (absName c) (absExpr ty) := by
  rw [core_k.nat_op_ty_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n0, hn0, natTy, hnatTy, n1, hn1, bp, hbp, h⟩ := h
  obtain ⟨hntabs, hntwf⟩ := const_no_levels_step (hnatn n0 hn0) hnatTy
  obtain ⟨hpabs, hpwf⟩ := hpred n1 hn1
  have ep := Name.beq_refines hc hpwf hbp
  rw [hpabs] at ep
  obtain ⟨⟨d, k⟩⟩ := ty
  unfold ConLeche.natOpTyPinnedF
  cases bp
  · -- not `Nat.pred`: the binary shape `Nat → Nat → cod`
    rw [if_neg (of_decide_eq_false ep.symm)]
    simp only [Bool.false_eq_true, if_false, expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    cases k with
    | ForallE dom inner mb =>
      obtain ⟨hdwf, hiwf, -⟩ := forall_e_wf_inv hty
      obtain ⟨⟨d2, k2⟩⟩ := inner
      simp only [ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
      cases k2 with
      | ForallE dom2 body mb2 =>
        obtain ⟨hd2wf, hbodywf, -⟩ := forall_e_wf_inv hiwf
        simp only [bind_eq_ok_iff] at h
        obtain ⟨b1, hb1, h⟩ := h
        have e1 := Expr.beq_refines hdwf hntwf hb1
        rw [hntabs] at e1
        simp only [absExpr_mk, absExprKind, expr_beq_decide]
        rw [← e1]
        cases b1
        · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          rw [← h]; rfl
        · simp only [reduceIte, bind_eq_ok_iff] at h
          obtain ⟨b2, hb2, h⟩ := h
          have e2 := Expr.beq_refines hd2wf hntwf hb2
          rw [hntabs] at e2
          rw [← e2]
          cases b2
          · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
            rw [← h]; rfl
          · simp only [reduceIte] at h
            rw [nat_op_cod_refines hfe hwf hc hbodywf hbeq hble hbn hnatn htcv h]; rfl
      | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
    | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp
  · -- `Nat.pred`: the unary shape `Nat → cod`
    rw [if_pos (of_decide_eq_true ep.symm)]
    simp only [reduceIte, expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, kernel.expr.ExprView.ofKind] at h
    cases k with
    | ForallE dom body mb =>
      obtain ⟨hdwf, hbodywf, -⟩ := forall_e_wf_inv hty
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b1, hb1, h⟩ := h
      have e1 := Expr.beq_refines hdwf hntwf hb1
      rw [hntabs] at e1
      simp only [absExpr_mk, absExprKind, expr_beq_decide]
      rw [← e1]
      cases b1
      · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h]; rfl
      · simp only [reduceIte] at h
        rw [nat_op_cod_refines hfe hwf hc hbodywf hbeq hble hbn hnatn htcv h]; rfl
    | _ => simp only [Result.ok.injEq] at h; rw [← h]; simp

/-! ## `nat_op_stored_ok` and `nat_op_stored` (`Core.lean:741-772`,
`DeclCheck.lean:233-238`, `FEnv.lean:148-152`) -/

/-- The `some (.defnInfo cv v hint)` destructuring of a lookup, which
`core_k::defn_probe` is. -/
def defnProbeL (lfe : ConLeche.FEnv) (n : ConLeche.Name) :
    Option (ConLeche.ConstantVal × ConLeche.Expr × ConLeche.ReducibilityHint) :=
  match lfe.find? n with
  | some (.defnInfo cv v hint) => some (cv, v, hint)
  | _ => none

/-- **Imported**: `core_k::defn_probe` refines `defnProbeL`, and what it hands
back is well formed (it is read out of the environment). -/
def DefnProbeSpec (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  ∀ (n : name.Name) (o : Option (env.ConstantVal × expr.Expr × env.ReducibilityHint)),
    NameWF n → core_k.defn_probe fe n = ok o →
      o.map (fun t => (absConstantVal t.1, absExpr t.2.1, absHint t.2.2))
          = defnProbeL lfe (absName n) ∧
        ∀ t ∈ o, ConstantValWF t.1 ∧ ExprWF t.2.1

/-- `natOpStoredOkF` read through the probe: one `find?`, cased. -/
theorem natOpStoredOkF_eq_probe (lfe : ConLeche.FEnv) (n : ConLeche.Name) :
    ConLeche.natOpStoredOkF lfe n =
      (match defnProbeL lfe n with
       | some t => t.1.levelParams.isEmpty && ConLeche.natOpTyPinnedF lfe n t.1.type
       | none => false) := by
  unfold ConLeche.natOpStoredOkF defnProbeL
  rcases hf : lfe.find? n with _ | ci
  · rfl
  · cases ci <;> rfl

/-- **`core_k::nat_op_stored_ok` refines `natOpStoredOkF`**
(`ConLeche/Kernel/Core.lean:741-747 natOpStoredOk`,
`ConLeche/Kernel/DeclCheck.lean:233-238 natOpStoredOkF`,
`ConLeche/Kernel/FEnv.lean:148-152 natOpStoredF`): the op is stored as a
level-monomorphic definition at the pinned type.

Imported: `DefnProbeSpec` and everything `nat_op_ty_pinned_refines` imports. -/
theorem nat_op_stored_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} {b : Bool} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (hn : NameWF n) (hdp : DefnProbeSpec fe lfe)
    (hpred : PinnedName core_k.nat_pred_name ConLeche.natPredName)
    (hbeq : PinnedName core_k.nat_beq_name ConLeche.natBeqName)
    (hble : PinnedName core_k.nat_ble_name ConLeche.natBleName)
    (hbn : PinnedName core_k.bool_name ConLeche.boolName)
    (hnatn : PinnedName basis_names.nat_name ConLeche.natName)
    (htcv : ToConstantValSpec)
    (h : core_k.nat_op_stored_ok fe n = ok b) :
    b = ConLeche.natOpStoredOkF lfe (absName n) := by
  rw [natOpStoredOkF_eq_probe]
  rw [core_k.nat_op_stored_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  obtain ⟨hprobe, hprobewf⟩ := hdp n o hn ho
  rw [← hprobe]
  cases o with
  | none =>
    dsimp only at h
    simpa using h.symm
  | some t =>
    obtain ⟨hcvwf, -⟩ := hprobewf t rfl
    obtain ⟨cv, v, hint⟩ := t
    -- the generated `let (cv, _, _) := t` is definitionally this `if`
    replace h : (if alloc.vec.Vec.len cv.level_params = 0#usize then
      core_k.nat_op_ty_pinned fe n cv.ty else ok false) = ok b := h
    show b = ((absNames cv.level_params).isEmpty &&
      ConLeche.natOpTyPinnedF lfe (absName n) (absExpr cv.ty))
    split at h
    · rename_i hlen
      rw [absNames_isEmpty, decide_eq_true hlen,
        nat_op_ty_pinned_refines hfe hwf hn hcvwf.2.2 hpred hbeq hble hbn hnatn htcv h]
      rfl
    · rename_i hlen
      rw [absNames_isEmpty, decide_eq_false hlen]
      simpa using h.symm

/-- **`core_k::nat_op_stored` refines `natOpStoredF`**
(`ConLeche/Kernel/Core.lean:749-772 natOpStored`,
`ConLeche/Kernel/FEnv.lean:148-152 natOpStoredF`) — the reduction-time test: is
`c` stored as a definition at all?  One `find?`, and no imported hypothesis. -/
theorem nat_op_stored_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {b : Bool} (hfe : FindAgree fe lfe) (hc : NameWF c)
    (h : core_k.nat_op_stored fe c = ok b) :
    b = ConLeche.natOpStoredF lfe (absName c) := by
  rw [core_k.nat_op_stored] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  unfold ConLeche.natOpStoredF
  cases o with
  | none => rw [hfe.find_none hc ho]; simpa using h.symm
  | some ci =>
    rw [hfe.find_some hc ho]
    cases ci <;> (simp only [Result.ok.injEq] at h; rw [← h]; rfl)

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`nat_op_guard_refines` is the headline lemma of the file and the one that goes
through everything else here (`defn_lp_empty`, the `deps_all_stored`
recursion, `Refine/Name.lean`'s exactness lemmas). -/

/--
info: 'ConRon.Refine.CoreK.nat_op_guard_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.CoreK.nat_op_guard_refines

end ConRon.Refine.CoreK
