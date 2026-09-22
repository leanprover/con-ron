/-
# `ConRon.Refine2.Checker.Canon` — Theorem 2 for `arena::canon`

**Task #97-P5-Checker**, deliverable 2 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/canon.rs` against
`proof/ConRon/Arena/Canon.lean`: con-leche's canonical-form agreement, decided
in LOCKSTEP on two handles rather than by building two canonical terms.
`canonLevel` and `canonExpr` preserve every node's constructor, so the two
canonical forms are equal iff the originals agree constructor by constructor
down to their leaves — which is what the descent tests, and what makes the
whole module allocation-free except for `canon_names`.

## Three shapes in one file, and the split is the state

* `canon_names{,_go}` and the four `*canon_eq*` entries **intern** the
  numbered parameter names, so they thread the state: `Sim`.
* `canon_level_eq`, `canon_expr_eq` and their companions only `view`:
  `Refine2/Checker/Shape.lean`'s **`SimRE`** — a reader that can decline
  (the fuel arm is `Internal`, one of the three mirrored kinds).
* the ten `*_beq` are **pure**, and each is the twin's derived `DecidableEq`
  at the abstraction — `o = decide (abs a = abs b)`, which is the `Eq2Fwd`
  shape of task #97-P5-0's rule 4 met at the declaration layer instead of at
  a cons key.

## What is Rust-only here

`canon_name_map_from`, `canon_level_eq_at`, `canon_expr_eq_at`,
`canon_expr_eq_two`, `canon_eq_cv_and_rules`, `canon_eq_cv_and_value` and the
ten `*_beq`.  The `_at`/`_two` four are task #97-P6-2's extraction rule 5
(a `view`'s loans dead at the join, and the two-child arms' pair in the twin's
order); the `_beq` ten are DESIGN §3.4's "no `deriving DecidableEq` in code
Aeneas must translate", so they are hand-written comparisons against a derived
instance.  Each is stated against the twin's own arm or its `==`.

## What these lemmas wait on

`Specs.lean`'s `view`, `view_l`, `view_ls` (closed) and `intern_n_node`
(open).  The shape step is the fuel peel at `canon_level_eq` and
`canon_expr_eq`, the `Nat`-count recursion at `canon_names_go` and a
`Vec`-cursor measure induction at the five list walks.
-/
import ConRon.Refine2.Checker.Pins

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The pure comparisons

Ten of them, and every one is the twin's derived `DecidableEq` at the
abstraction.  The five `*_vec_beq` are cursor recursions over two `Vec`s and
are stated at the two lists from the cursor on. -/

/-- `eidx_vec_beq` at the cursor is `==` on the two remaining handle lists. -/
theorem eidx_vec_beq_refines {a b : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.eidx_vec_beq a b i = ok o) :
    o = decide (absEIdxLFrom a i = absEIdxLFrom b i) := by
  sorry

/-- `lidx_vec_beq` at the cursor. -/
theorem lidx_vec_beq_refines {a b : alloc.vec.Vec arena.handle.LIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.lidx_vec_beq a b i = ok o) :
    o = decide (absLIdxLFrom a i = absLIdxLFrom b i) := by
  sorry

/-- `nidx_vec_beq` at the cursor. -/
theorem nidx_vec_beq_refines {a b : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.nidx_vec_beq a b i = ok o) :
    o = decide (absNIdxLFrom a i = absNIdxLFrom b i) := by
  sorry

/-- `i_rec_rule_fire_beq` ⊑ `==` on `IRecRuleFire`. -/
theorem i_rec_rule_fire_beq_refines {a b : arena.env.IRecRuleFire} {o : Bool}
    (hrun : arena.canon.i_rec_rule_fire_beq a b = ok o) :
    o = decide (absIRecRuleFire a = absIRecRuleFire b) := by
  sorry

/-- `i_constant_val_beq` ⊑ `==` on `IConstantVal`. -/
theorem i_constant_val_beq_refines {a b : arena.env.IConstantVal} {o : Bool}
    (hrun : arena.canon.i_constant_val_beq a b = ok o) :
    o = decide (absIConstantVal a = absIConstantVal b) := by
  sorry

/-- `i_rec_rule_beq` ⊑ `==` on `IRecRule`. -/
theorem i_rec_rule_beq_refines {a b : arena.env.IRecRule} {o : Bool}
    (hrun : arena.canon.i_rec_rule_beq a b = ok o) :
    o = decide (absIRecRule a = absIRecRule b) := by
  sorry

/-- `i_rec_rules_beq` at the cursor. -/
theorem i_rec_rules_beq_refines {a b : alloc.vec.Vec arena.env.IRecRule}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.i_rec_rules_beq a b i = ok o) :
    o = decide (absIRecRuleLFrom a i = absIRecRuleLFrom b i) := by
  sorry

/-- `i_ind_caps_beq` ⊑ `==` on `IIndCaps`. -/
theorem i_ind_caps_beq_refines {a b : arena.env.IIndCaps} {o : Bool}
    (hrun : arena.canon.i_ind_caps_beq a b = ok o) :
    o = decide (absIIndCaps a = absIIndCaps b) := by
  sorry

/-- `i_proj_table_beq` ⊑ `==` on `IProjTable`. -/
theorem i_proj_table_beq_refines {t t2 : arena.env.IProjTable} {o : Bool}
    (hrun : arena.canon.i_proj_table_beq t t2 = ok o) :
    o = decide (absIProjTable t = absIProjTable t2) := by
  sorry

/-- `i_constant_info_beq` ⊑ `==` on `IConstantInfo`. -/
theorem i_constant_info_beq_refines {a b : arena.env.IConstantInfo} {o : Bool}
    (hrun : arena.canon.i_constant_info_beq a b = ok o) :
    o = decide (absIConstantInfo a = absIConstantInfo b) := by
  sorry

/-- `i_rec_rule_eq_but_rhs` is the twin's `{ r with rhs := default } == { r'
with rhs := default }` — the record comparison at a common right-hand side,
which is how `canonRulesEq` compares the other fields without interning
anything. -/
theorem i_rec_rule_eq_but_rhs_refines {r r2 : arena.env.IRecRule} {o : Bool}
    (hrun : arena.canon.i_rec_rule_eq_but_rhs r r2 = ok o) :
    o = decide ({ absIRecRule r with rhs := default } =
      { absIRecRule r2 with rhs := default }) := by
  sorry

/-! ## The renaming the parameter list induces -/

/-- `canon_name_map_from` ⊑ `canonNameMap` from the cursor on. -/
theorem canon_name_map_from_refines {ps cs : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} {i : Std.Usize} {o}
    (hrun : arena.canon.canon_name_map_from ps cs n i = ok o) :
    absNIdx o = canonNameMap (absNIdxLFrom ps i)
      (absNIdxLFrom cs i) (absNIdx n) := by
  sorry

/-- `canon_name_map` ⊑ `canonNameMap`: the `i`-th parameter becomes the `i`-th
numbered name, anything else is left alone. -/
theorem canon_name_map_refines {ps cs : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} {o}
    (hrun : arena.canon.canon_name_map ps cs n = ok o) :
    absNIdx o = canonNameMap (absNIdxL ps) (absNIdxL cs) (absNIdx n) := by
  sorry

/-! ## The numbered names

`canon_names_go` counts UP so the list comes out in index order; no fuel,
because it is structural on the count.  It INTERNS, so it is a `Sim`. -/

/-- `canon_names_go` ⊑ `canonNamesGo`, with the Rust's accumulator in front. -/
theorem canon_names_go_refines {pers st lst} {i n : Std.U64}
    {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_names_go pers st i n out = ok o) :
    Sim (fun v => absNIdxL out ++ absNIdxL v) (fun _ => True) pers lst o
      (do pure (absNIdxL out ++ (← canonNamesGo (absU i) (absU n)))) := by
  sorry

/-- `canon_names` ⊑ `canonNames`. -/
theorem canon_names_refines {pers st lst} {n : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_names pers st n = ok o) :
    Sim absNIdxL (fun _ => True) pers lst o (canonNames (absU n)) := by
  sorry

/-! ## The two node transcriptions

`canon_level_eq_at` and `canon_expr_eq_at` are the twin's `match ← view a,
← view b with` bodies past the two `view`s.  Each is transcribed here at the
twin's node views and tied to the twin by an `_unfold` equation — the shape
`Refine2/ExprOps/Read.lean` wrote for `wscopedBGo`, and the shape
`Refine2/Promote/Promote.lean` wrote for the three `promote_*_node`. -/

/-- `canonLevelEq`'s five matching arms and its catch-all. -/
def canonLevelEqAtSpec (ps ps' cs : List NIdx) (fuel : Nat) :
    LNodeView → LNodeView → AM Bool
  | .zero, .zero => pure true
  | .succ a, .succ b => canonLevelEq ps ps' cs fuel a b
  | .max a b, .max a' b' => do
    if ← canonLevelEq ps ps' cs fuel a a' then canonLevelEq ps ps' cs fuel b b'
    else pure false
  | .imax a b, .imax a' b' => do
    if ← canonLevelEq ps ps' cs fuel a a' then canonLevelEq ps ps' cs fuel b b'
    else pure false
  | .param n, .param n' =>
    pure (canonNameMap ps cs n == canonNameMap ps' cs n')
  | _, _ => pure false

/-- `canonExprEq`'s ten matching arms and its catch-all. -/
def canonExprEqAtSpec (ps ps' cs : List NIdx) (fuel : Nat) :
    ENodeView → ENodeView → AM Bool
  | .bvar i, .bvar j => pure (i == j)
  | .fvar i t, .fvar j t' =>
    if i == j then canonExprEq ps ps' cs fuel t t' else pure false
  | .sort u, .sort v => canonLevelEq ps ps' cs fuel u v
  | .const n us, .const n' us' =>
    if n == n' then canonLevelsEq ps ps' cs fuel us us' else pure false
  | .app f x, .app f' x' => do
    if ← canonExprEq ps ps' cs fuel f f' then canonExprEq ps ps' cs fuel x x'
    else pure false
  | .lam t bd _, .lam t' bd' _ => do
    if ← canonExprEq ps ps' cs fuel t t' then canonExprEq ps ps' cs fuel bd bd'
    else pure false
  | .forallE t bd _, .forallE t' bd' _ => do
    if ← canonExprEq ps ps' cs fuel t t' then canonExprEq ps ps' cs fuel bd bd'
    else pure false
  | .letE t v bd, .letE t' v' bd' => do
    if ← canonExprEq ps ps' cs fuel t t' then
      if ← canonExprEq ps ps' cs fuel v v' then canonExprEq ps ps' cs fuel bd bd'
      else pure false
    else pure false
  | .lit l, .lit l' => pure (l == l')
  | .proj s i e, .proj s' i' e' =>
    if s == s' && i == i' then canonExprEq ps ps' cs fuel e e' else pure false
  | _, _ => pure false

/-- `canonLevelEq` in terms of its transcription. -/
theorem canonLevelEq_unfold (ps ps' cs : List NIdx) (fuel : Nat) (u v : LIdx) :
    canonLevelEq ps ps' cs (fuel + 1) u v =
      (do canonLevelEqAtSpec ps ps' cs fuel (← viewL u) (← viewL v)) := by
  sorry

/-- `canonExprEq` in terms of its transcription. -/
theorem canonExprEq_unfold (ps ps' cs : List NIdx) (fuel : Nat) (a b : EIdx) :
    canonExprEq ps ps' cs (fuel + 1) a b =
      (do canonExprEqAtSpec ps ps' cs fuel (← view a) (← view b)) := by
  sorry

/-! ## Levels

Read-only: the twin `view`s and compares, and the only failure is the fuel
arm's `Internal`. -/

/-- `canon_level_eq` ⊑ `canonLevelEq`. -/
theorem canon_level_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {u v : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_level_eq pers st ps ps2 cs fuel u v = ok o) :
    SimRE id lst o
      (canonLevelEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdx u) (absLIdx v)) := by
  sorry

/-- `canon_level_eq_at` is `canon_level_eq`'s arm past the two `view`s
(extraction rule 5), stated against the twin's `match` at the two views. -/
theorem canon_level_eq_at_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a b : arena.store.LNodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_level_eq_at pers st ps ps2 cs fuel a b = ok o) :
    SimRE id lst o
      (canonLevelEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLNodeView a) (absLNodeView b)) := by
  sorry

/-- `canon_level_list_eq` ⊑ `canonLevelListEq` at the cursor. -/
theorem canon_level_list_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {us vs : alloc.vec.Vec arena.handle.LIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_level_list_eq pers st ps ps2 cs fuel us vs i = ok o) :
    SimRE id lst o
      (canonLevelListEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdxLFrom us i) (absLIdxLFrom vs i)) := by
  sorry

/-- `canon_levels_eq` ⊑ `canonLevelsEq`, at two interned universe-argument
LIST handles. -/
theorem canon_levels_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {us vs : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_levels_eq pers st ps ps2 cs fuel us vs = ok o) :
    SimRE id lst o
      (canonLevelsEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLsIdx us) (absLsIdx vs)) := by
  sorry

/-! ## Terms

The binder metadata is NOT compared, exactly as con-leche's clause does not:
`canonExpr` writes `⟨.never⟩` on both sides. -/

/-- `canon_expr_eq` ⊑ `canonExprEq`. -/
theorem canon_expr_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a b : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_expr_eq pers st ps ps2 cs fuel a b = ok o) :
    SimRE id lst o
      (canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absEIdx a) (absEIdx b)) := by
  sorry

/-- `canon_expr_eq_at` is `canon_expr_eq`'s arm past the two `view`s. -/
theorem canon_expr_eq_at_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {va vb : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_expr_eq_at pers st ps ps2 cs fuel va vb = ok o) :
    SimRE id lst o
      (canonExprEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absENodeView va) (absENodeView vb)) := by
  sorry

/-- `canon_expr_eq_two` is the two-child arms' pair of descents, in the twin's
order and with its short-circuit. -/
theorem canon_expr_eq_two_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a a2 b b2 : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_expr_eq_two pers st ps ps2 cs fuel a a2 b b2 = ok o) :
    SimRE id lst o
      (do
        if ← canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx a) (absEIdx b) then
          canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx a2) (absEIdx b2)
        else pure false) := by
  sorry

/-- `canon_rules_eq` ⊑ `canonRulesEq` at the cursor. -/
theorem canon_rules_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_rules_eq pers st ps ps2 cs fuel rs rs2 i = ok o) :
    SimRE id lst o
      (canonRulesEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absIRecRuleLFrom rs i) (absIRecRuleLFrom rs2 i)) := by
  sorry

/-! ## Constants

These four INTERN (`canonNames`), so they thread the state. -/

/-- `i_constant_val_canon_eq` ⊑ `IConstantVal.canonEq`.  The numbered
level-parameter lists are equal exactly when they are equally long, which is
why the length test stands in for comparing them — and why ONE `canonNames`
serves both sides. -/
theorem i_constant_val_canon_eq_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.i_constant_val_canon_eq pers st cv cv2 = ok o) :
    Sim id (fun _ => True) pers lst o
      ((absIConstantVal cv).canonEq (absIConstantVal cv2)) := by
  sorry

/-- `canon_eq_cv_and_rules` is `i_constant_info_canon_eq`'s `.recInfo` arm
past its two scalar tests (extraction rule 5). -/
theorem canon_eq_cv_and_rules_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_cv_and_rules pers st cv cv2 rs rs2 = ok o) :
    Sim id (fun _ => True) pers lst o
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonRulesEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absIRecRuleL rs) (absIRecRuleL rs2)
        else pure false) := by
  sorry

/-- `canon_eq_cv_and_value` is the `.defnInfo` / `.thmInfo` arms' shared tail. -/
theorem canon_eq_cv_and_value_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal} {v v2 : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_cv_and_value pers st cv cv2 v v2 = ok o) :
    Sim id (fun _ => True) pers lst o
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonExprEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absEIdx v) (absEIdx v2)
        else pure false) := by
  sorry

/-- `i_constant_info_canon_eq` ⊑ `IConstantInfo.canonEq`.  `.indInfo`'s
capabilities are not compared (`canon` resets both to `{}`), and a projection
table is compared as it stands. -/
theorem i_constant_info_canon_eq_refines {pers st lst}
    {ci ci2 : arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.i_constant_info_canon_eq pers st ci ci2 = ok o) :
    Sim id (fun _ => True) pers lst o
      ((absIConstantInfo ci).canonEq (absIConstantInfo ci2)) := by
  sorry

/-- `canon_eq_list` ⊑ `canonEqList` at the cursor — two blocks are the same,
member for member, up to the canonical form. -/
theorem canon_eq_list_refines {pers st lst}
    {xs ys : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_list pers st xs ys i = ok o) :
    Sim id (fun _ => True) pers lst o
      (canonEqList (absICILFrom xs i) (absICILFrom ys i)) := by
  sorry

end ConRon.Refine2
