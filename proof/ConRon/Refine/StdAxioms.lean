import ConRon.Refine.CoreKBase
import ConRon.Refine.CoreKSupport
import ConRon.Refine.BasisNames
import ConLeche.Kernel.StdAxioms
import ConLeche.Kernel.DeclCheck

/-! # `kernel::std_axioms` — the two recognized standard axioms (task #56)

`CORE_PLAN.md` step 7.  `crates/con-ron-core/src/kernel/std_axioms.rs` is
`ConLeche/Kernel/StdAxioms.lean`: the pinned names, the *raw* pins written with
`Basis/Builder.lean`'s DSL, the pin comparison (`Expr.erasePw`/
`ConstantVal.matchesPin`, and their executed `@[csimp]` twins
`Expr.erasePwEq`/`ConstantVal.matchesPinFast`), and the install guard
`stdAxiomOk`/`stdAxiomOkF` that consumes all of it.

## The key fact of this module: RAW pins, and the comparison cannot tell

con-leche writes each pin twice — the raw one, hand-written with the builder,
and the annotated one (`iffA`, `iffIntroA`, `iffRecA`, `nonemptyA`,
`nonemptyIntroA`, `nonemptyRecA`, `propextA`, `choiceA`), computed from it at
elaboration time by `#annotate_basis`/`#annotate_pins`.  `stdAxiomOk` compares
against the *annotated* one; the port compares against the *raw* one, which it
can write down (task #24's "`matchesPin` is compared against the RAW pins, and
that is exact").  The bridge is

```text
matchesPin cv (annotate pin) = matchesPin cv pin
```

and **it is proved here, not assumed**: `matchesPin`'s type test is
`a.erasePw == b.erasePw`, so `matchesPin_congr` below reduces the claim to
three closed equations between the annotated and the raw pin — same name, same
level parameters, same `erasePw` of the type — each of which is `rfl` on the
two closed terms (`iffA_matchesPin_raw` … `choiceA_matchesPin_raw`, eight of
them).  So the port's deviation costs the proof nothing at all, and the
annotated pins are cited on the same items the raw ones are.

## What is stated against what

* A **pin builder** gets a closed equality in the style of
  `Refine/BasisTables.lean`: `absConstantInfo <the port's pin> = <the raw
  con-leche pin>`, with the hereditary `ConstantInfoWF` beside it.  Nothing is
  hypothesised; the pins are closed terms on both sides.
* A **pinned name** gets `Refine/BasisNames.lean`'s shape
  (`absName n = ConLeche.iffName ∧ NameWF n`), through `CoreKBase`'s
  `str_lit_step`.
* A **guard** (`iff_pinned`, …, `std_axiom_ok`) is a pure `bool`, so it gets
  exactness: the Rust `Bool` *is* the cited Lean `Bool`, at the con-leche
  spelling with the *annotated* pins, i.e. the guard is literally the cited
  `match` of `stdAxiomOkF`.  The hypotheses are `CoreKBase`'s `FindAgree`/
  `FindWF` rather than the full `FEnv.FEnvRel`/`FEnv.FEnvWF` (the module reads
  the index only through `fenv::find`), with `std_axiom_ok_refines_of_rel` the
  bridge the tier consumes.
* **The environment is the index** (task #18 deviation 3): `stdAxiomOk (env)`
  and `stdAxiomOkF (fe)` are one Rust function, so the statement is against the
  `F`-twin.  `stdAxiomOkF_eq` re-spells that definition's five conjuncts the way
  the six guard lemmas spell them and is `rfl`; it is needed because the *same*
  `match`, written in two modules, elaborates to two `match` auxiliaries, which
  `rw` will not see through.

Two things this file adds that belong elsewhere, each marked in place:
`wf_kind_inv` and its ten wrappers (**to be moved to `Refine/Expr.lean`** beside
`Refine/CoreKGuards.lean`'s three — the lockstep descent cases on the *second*
term's kind, so it needs the inversion at every kind), and the eleven `bb_*`
builder steps below.

## The `Basis/Builder.lean` DSL, locally

`kernel::basis_builder` is not this file's module, and no sibling file may be
imported, so the eleven builder steps this module needs are proved here under
descriptive names (`bb_*`).  **To be unified into `Refine/BasisBuilder.lean`**
when one exists.  They also record task #24's deviation 2: `pi`/`piI`/`piA` are
one Rust function and `lm`/`lmI` another, because `Expr` carries no binder
name, so each `bb_*` step concludes the *node* (`.forallE ty b ⟨.never⟩`) and
`BasisDSL_pi_eq`/`BasisDSL_lm_eq` say that node is every one of the cited
spellings.

## What is not this file's

`kernel::basis_pins::eq_basis_pinned` — the `decide (fe.find? eqName = some
eqA)` conjunct of `stdAxiomOk`'s `propext` arm — is `kernel/basis_pins.rs`, a
different module (task #24's three stubs).  Its refinement is named here as
`EqBasisPinned` and carried as a hypothesis by `std_axiom_ok_refines`, so the
dependency is visible in every downstream lemma and `Refine/BasisPins.lean`
discharges it in one place.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.StdAxioms

/-! ## The builder, refined

`ConLeche/Kernel/Basis/Builder.lean`.  Every helper is "a `def` whose body is a
single `Expr` constructor application", so every step is one smart-constructor
refinement plus its `ExprWF` constructor. -/

/-- Task #24 deviation 2, stated: the three cited `∀`-builders are one node, so
one Rust function refines all three whatever binder name is written. -/
theorem BasisDSL_pi_eq (x : String) (ty b : ConLeche.Expr) :
    ConLeche.BasisDSL.pi x ty b = ConLeche.BasisDSL.piA ty b ∧
      ConLeche.BasisDSL.piI x ty b = ConLeche.BasisDSL.piA ty b ∧
      ConLeche.BasisDSL.piA ty b = .forallE ty b ⟨.never⟩ := ⟨rfl, rfl, rfl⟩

/-- The same for the two cited λ-builders. -/
theorem BasisDSL_lm_eq (x : String) (ty b : ConLeche.Expr) :
    ConLeche.BasisDSL.lm x ty b = .lam ty b ⟨.never⟩ ∧
      ConLeche.BasisDSL.lmI x ty b = .lam ty b ⟨.never⟩ := ⟨rfl, rfl⟩

/-- `Basis/Builder.lean:63-64 BasisDSL.bv` — `basis_builder::bv`. -/
theorem bb_bv {i : Std.U64} {e : expr.Expr} (h : basis_builder.bv i = ok e) :
    absExpr e = .bvar i.val ∧ ExprWF e := by
  rw [basis_builder.bv] at h
  exact ⟨Expr.bvar_refines h, Expr.bvar_wf h⟩

/-- `Basis/Builder.lean:66-67 BasisDSL.srt` — `basis_builder::srt`. -/
theorem bb_srt {u : level.Level} {e : expr.Expr} (hu : LevelWF u)
    (h : basis_builder.srt u = ok e) : absExpr e = .sort (absLevel u) ∧ ExprWF e := by
  rw [basis_builder.srt] at h
  exact ⟨Expr.sort_refines h, Expr.sort_wf hu h⟩

/-- `Basis/Builder.lean:69-70 BasisDSL.prop` — `basis_builder::prop`. -/
theorem bb_prop {e : expr.Expr} (h : basis_builder.prop = ok e) :
    absExpr e = ConLeche.BasisDSL.prop ∧ ExprWF e := by
  rw [basis_builder.prop] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨u, hu, hs⟩ := h
  exact ⟨by rw [Expr.sort_refines hs, Level.zero_refines hu]; rfl,
    Expr.sort_wf (Level.zero_wf hu) hs⟩

/-- `Basis/Builder.lean:75-76 BasisDSL.cnst` — `basis_builder::cnst`.  The
Lean's `us := []` default is spelled at every call site in the port. -/
theorem bb_cnst {n : name.Name} {us : alloc.vec.Vec level.Level} {e : expr.Expr}
    (hn : NameWF n) (hus : LevelsWF us) (h : basis_builder.cnst n us = ok e) :
    absExpr e = .const (absName n) (absLevels us) ∧ ExprWF e := by
  rw [basis_builder.cnst] at h
  exact ⟨Expr.mk_const_refines h, Expr.mk_const_wf hn hus h⟩

/-- The `⟨.never⟩` binder datum every raw-pin binder carries
(`basis_builder::never_meta`; con-leche writes it inline). -/
theorem bb_never_meta {m : expr.BinderMeta} (h : basis_builder.never_meta = ok m) :
    absBinderMeta m = (⟨.never⟩ : ConLeche.BinderMeta) ∧ BinderMetaWF m := by
  rw [basis_builder.never_meta] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pw, hpw, hm⟩ := h
  simp only [expr.binder_meta, ptr_new_eq, bind_tc_ok, Result.ok.injEq] at hm
  subst hm
  exact ⟨by rw [absBinderMeta, PropWhen.never_refines hpw], PropWhen.never_wf hpw⟩

/-- `Basis/Builder.lean:85-97 BasisDSL.pi`/`piI`/`piA` — `basis_builder::pi`
(one Rust function for all three; see `BasisDSL_pi_eq`). -/
theorem bb_pi {ty b e : expr.Expr} (hty : ExprWF ty) (hb : ExprWF b)
    (h : basis_builder.pi ty b = ok e) :
    absExpr e = .forallE (absExpr ty) (absExpr b) ⟨.never⟩ ∧ ExprWF e := by
  rw [basis_builder.pi] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m, hm, hf⟩ := h
  obtain ⟨hmabs, hmwf⟩ := bb_never_meta hm
  exact ⟨by rw [Expr.forall_e_refines hf, hmabs], Expr.forall_e_wf hty hb hmwf hf⟩

/-- `Basis/Builder.lean:99-106 BasisDSL.lm`/`lmI` — `basis_builder::lm`.
Nothing in `StdAxioms.lean` uses it; refined for the family's sake. -/
theorem bb_lm {ty b e : expr.Expr} (hty : ExprWF ty) (hb : ExprWF b)
    (h : basis_builder.lm ty b = ok e) :
    absExpr e = .lam (absExpr ty) (absExpr b) ⟨.never⟩ ∧ ExprWF e := by
  rw [basis_builder.lm] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m, hm, hf⟩ := h
  obtain ⟨hmabs, hmwf⟩ := bb_never_meta hm
  exact ⟨by rw [Expr.lam_refines hf, hmabs], Expr.lam_wf hty hb hmwf hf⟩

/-- `Basis/Builder.lean:108-109 BasisDSL.ap2` — `basis_builder::ap2`. -/
theorem bb_ap2 {f a b e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a) (hb : ExprWF b)
    (h : basis_builder.ap2 f a b = ok e) :
    absExpr e = .app (.app (absExpr f) (absExpr a)) (absExpr b) ∧ ExprWF e := by
  rw [basis_builder.ap2] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨by rw [Expr.app_refines hy, Expr.app_refines hx],
    Expr.app_wf (Expr.app_wf hf ha hx) hb hy⟩

/-- `Basis/Builder.lean:111-112 BasisDSL.ap3` — `basis_builder::ap3`. -/
theorem bb_ap3 {f a b c e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a) (hb : ExprWF b)
    (hc : ExprWF c) (h : basis_builder.ap3 f a b c = ok e) :
    absExpr e = .app (.app (.app (absExpr f) (absExpr a)) (absExpr b)) (absExpr c) ∧
      ExprWF e := by
  rw [basis_builder.ap3] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨x, hx, hy⟩ := h
  obtain ⟨hxa, hxw⟩ := bb_ap2 hf ha hb hx
  exact ⟨by rw [Expr.app_refines hy, hxa], Expr.app_wf hxw hc hy⟩

/-- `Basis/Builder.lean:114-115 BasisDSL.ap4` — `basis_builder::ap4`. -/
theorem bb_ap4 {f a b c d e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a) (hb : ExprWF b)
    (hc : ExprWF c) (hd : ExprWF d) (h : basis_builder.ap4 f a b c d = ok e) :
    absExpr e =
        .app (.app (.app (.app (absExpr f) (absExpr a)) (absExpr b)) (absExpr c))
          (absExpr d) ∧ ExprWF e := by
  rw [basis_builder.ap4] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨x, hx, hy⟩ := h
  obtain ⟨hxa, hxw⟩ := bb_ap3 hf ha hb hc hx
  exact ⟨by rw [Expr.app_refines hy, hxa], Expr.app_wf hxw hd hy⟩

/-- `Basis/Builder.lean:41-42 BasisDSL.bn` — `basis_builder::bn`. -/
theorem bb_bn {s : alloc.vec.Vec Std.U32} {n : name.Name} (hs : StrWF s)
    (h : basis_builder.bn s = ok n) :
    absName n = .str .anonymous (absString s) ∧ NameWF n := by
  rw [basis_builder.bn] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, hmk⟩ := h
  exact ⟨by rw [Name.mk_str_refines hmk, Name.anonymous_refines ha],
    NameWF.str (Name.anonymous_wf ha) hs hmk⟩

/-- `Basis/Builder.lean:44-45 BasisDSL.uN` — `basis_builder::u_n`. -/
theorem bb_u_n {n : name.Name} (h : basis_builder.u_n = ok n) :
    absName n = ConLeche.BasisDSL.uN ∧ NameWF n := by
  rw [basis_builder.u_n] at h
  simp only [basis_builder.bn, bind_eq_ok_iff] at h
  obtain ⟨s, hs, v, hv, a, ha, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [117#u32]) (by simp [basis_builder.u_n.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `Basis/Builder.lean:47-48 BasisDSL.u` — `basis_builder::u`. -/
theorem bb_u {u : level.Level} (h : basis_builder.u = ok u) :
    absLevel u = ConLeche.BasisDSL.u ∧ LevelWF u := by
  rw [basis_builder.u] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, hp⟩ := h
  obtain ⟨h1, h1wf⟩ := bb_u_n hn
  exact ⟨by rw [Level.param_refines hp, h1]; rfl, Level.param_wf h1wf hp⟩

/-! ## The pinned names (`StdAxioms.lean:38-69`)

`Refine/BasisNames.lean`'s shape exactly: unfold, split the two-or-three-bind
`do` chain, hand the pieces to `CoreKBase`'s `str_lit_step`. -/

/-- `ConLeche/Kernel/StdAxioms.lean:38-39 propextName` —
`std_axioms::propext_name` refines `propextName`. -/
theorem propext_name_refines {n : name.Name} (h : std_axioms.propext_name = ok n) :
    absName n = ConLeche.propextName ∧ NameWF n := by
  rw [std_axioms.propext_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [112#u32, 114#u32, 111#u32, 112#u32, 101#u32, 120#u32, 116#u32])
    (by simp [std_axioms.propext_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/StdAxioms.lean:41-42 choiceName` —
`std_axioms::choice_name` refines `choiceName`. -/
theorem choice_name_refines {n : name.Name} (h : std_axioms.choice_name = ok n) :
    absName n = ConLeche.choiceName ∧ NameWF n := by
  rw [std_axioms.choice_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, n1, hn1, s1, hs1, v1, hv1, hmk⟩ := h
  obtain ⟨e1, w1⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hn1
    (L := [67#u32, 108#u32, 97#u32, 115#u32, 115#u32, 105#u32, 99#u32, 97#u32, 108#u32])
    (by simp [std_axioms.choice_name.S]) (by decide)
  obtain ⟨e2, w2⟩ := str_lit_step w1 hs1 hv1 hmk
    (L := [99#u32, 104#u32, 111#u32, 105#u32, 99#u32, 101#u32])
    (by simp [std_axioms.choice_name.S_1]) (by decide)
  exact ⟨by rw [e2, e1, Name.anonymous_refines ha]; rfl, w2⟩

/-- `ConLeche/Kernel/StdAxioms.lean:44-51 toleratedAxiomNames` —
`std_axioms::tolerated_axiom_names` refines `toleratedAxiomNames`: the
one-element list `[sorryAx]`. -/
theorem tolerated_axiom_names_refines {v : alloc.vec.Vec name.Name}
    (h : std_axioms.tolerated_axiom_names = ok v) :
    absNames v = ConLeche.toleratedAxiomNames ∧ NamesWF v := by
  rw [std_axioms.tolerated_axiom_names] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, w, hw, n1, hn1, hpush⟩ := h
  obtain ⟨e1, w1⟩ := str_lit_step (Name.anonymous_wf ha) hs hw hn1
    (L := [115#u32, 111#u32, 114#u32, 114#u32, 121#u32, 65#u32, 120#u32])
    (by simp [std_axioms.tolerated_axiom_names.S]) (by decide)
  have hval : v.val = [n1] := by
    rw [vec_push_val hpush]; simp [alloc.vec.Vec.new]
  refine ⟨?_, ?_⟩
  · rw [absNames, hval]
    simp only [List.map_cons, List.map_nil, e1, Name.anonymous_refines ha]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl
    exact w1

/-- `ConLeche/Kernel/StdAxioms.lean:53-54 iffName` — `std_axioms::iff_name`. -/
theorem iff_name_refines {n : name.Name} (h : std_axioms.iff_name = ok n) :
    absName n = ConLeche.iffName ∧ NameWF n := by
  rw [std_axioms.iff_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [73#u32, 102#u32, 102#u32]) (by simp [std_axioms.iff_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/StdAxioms.lean:56-57 iffIntroName` —
`std_axioms::iff_intro_name`. -/
theorem iff_intro_name_refines {n : name.Name} (h : std_axioms.iff_intro_name = ok n) :
    absName n = ConLeche.iffIntroName ∧ NameWF n := by
  rw [std_axioms.iff_intro_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := iff_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [105#u32, 110#u32, 116#u32, 114#u32, 111#u32])
    (by simp [std_axioms.iff_intro_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/StdAxioms.lean:59-60 iffRecName` —
`std_axioms::iff_rec_name`. -/
theorem iff_rec_name_refines {n : name.Name} (h : std_axioms.iff_rec_name = ok n) :
    absName n = ConLeche.iffRecName ∧ NameWF n := by
  rw [std_axioms.iff_rec_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := iff_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [114#u32, 101#u32, 99#u32]) (by simp [std_axioms.iff_rec_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/StdAxioms.lean:62-63 nonemptyName` —
`std_axioms::nonempty_name`. -/
theorem nonempty_name_refines {n : name.Name} (h : std_axioms.nonempty_name = ok n) :
    absName n = ConLeche.nonemptyName ∧ NameWF n := by
  rw [std_axioms.nonempty_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [78#u32, 111#u32, 110#u32, 101#u32, 109#u32, 112#u32, 116#u32, 121#u32])
    (by simp [std_axioms.nonempty_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/StdAxioms.lean:65-66 nonemptyIntroName` —
`std_axioms::nonempty_intro_name`. -/
theorem nonempty_intro_name_refines {n : name.Name}
    (h : std_axioms.nonempty_intro_name = ok n) :
    absName n = ConLeche.nonemptyIntroName ∧ NameWF n := by
  rw [std_axioms.nonempty_intro_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nonempty_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [105#u32, 110#u32, 116#u32, 114#u32, 111#u32])
    (by simp [std_axioms.nonempty_intro_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/StdAxioms.lean:68-69 nonemptyRecName` —
`std_axioms::nonempty_rec_name`. -/
theorem nonempty_rec_name_refines {n : name.Name}
    (h : std_axioms.nonempty_rec_name = ok n) :
    absName n = ConLeche.nonemptyRecName ∧ NameWF n := by
  rw [std_axioms.nonempty_rec_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nonempty_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [114#u32, 101#u32, 99#u32])
    (by simp [std_axioms.nonempty_rec_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-! ## `Vec` plumbing for the pins

The pins build their `levelParams` and universe-argument lists with a
`Vec::push` onto `Vec::new` (task #18's point 10: the Aeneas subset has no list
literal), and the empty list is `Vec::new` itself. -/

/-- The empty `Vec<Name>` a level-parameter-free pin carries. -/
theorem names_new : absNames (alloc.vec.Vec.new name.Name) = [] ∧
    NamesWF (alloc.vec.Vec.new name.Name) := by
  refine ⟨by simp [absNames, alloc.vec.Vec.new], ?_⟩
  intro x hx; simp [alloc.vec.Vec.new] at hx

/-- The empty `Vec<Level>` a `cnst n []` carries. -/
theorem levels_new : absLevels (alloc.vec.Vec.new level.Level) = [] ∧
    LevelsWF (alloc.vec.Vec.new level.Level) := by
  refine ⟨by simp [absLevels, alloc.vec.Vec.new], ?_⟩
  intro x hx; simp [alloc.vec.Vec.new] at hx

/-- A one-element `Vec<Name>` (`[uN]`, every universe-taking pin's
`levelParams`). -/
theorem names_singleton {v : alloc.vec.Vec name.Name} {n : name.Name} (hn : NameWF n)
    (h : alloc.vec.Vec.push (alloc.vec.Vec.new name.Name) n = ok v) :
    absNames v = [absName n] ∧ NamesWF v := by
  have hval : v.val = [n] := by rw [vec_push_val h]; simp [alloc.vec.Vec.new]
  refine ⟨by rw [absNames, hval]; simp, ?_⟩
  intro x hx
  rw [hval] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  exact hn

/-- A one-element `Vec<Level>` (`[u]`, every universe-taking pin's constant
arguments). -/
theorem levels_singleton {v : alloc.vec.Vec level.Level} {u : level.Level}
    (hu : LevelWF u)
    (h : alloc.vec.Vec.push (alloc.vec.Vec.new level.Level) u = ok v) :
    absLevels v = [absLevel u] ∧ LevelsWF v := by
  have hval : v.val = [u] := by rw [vec_push_val h]; simp [alloc.vec.Vec.new]
  refine ⟨by rw [absLevels, hval]; simp, ?_⟩
  intro x hx
  rw [hval] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  exact hu

/-! ## The raw pins (`StdAxioms.lean:217-298`)

Each is a closed equality in the style of `Refine/BasisTables.lean`: what the
port builds *is* the con-leche pin, with the hereditary `*WF` beside it.  The
`#annotate_basis`/`#annotate_pins` citation on the Rust item is honoured by the
`*_matchesPin_raw` section below, not here: these lemmas are about the raw pin,
which is what the Rust writes. -/

/-- `ConLeche/Kernel/StdAxioms.lean:217-219 iffRaw`
(`:308-314` `#annotate_basis`, computing `iffA`) — `std_axioms::iff_raw`
refines `iffRaw`.  Deviation: `IndCaps`' `{}` is `env::ind_caps_default`. -/
theorem iff_raw_refines {ci : env.ConstantInfo} (h : std_axioms.iff_raw = ok ci) :
    absConstantInfo ci = ConLeche.iffRaw ∧ ConstantInfoWF ci := by
  rw [std_axioms.iff_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, e1, he1, e2, he2, ic, hic, rfl⟩ := h
  obtain ⟨na, nw⟩ := iff_name_refines hn
  obtain ⟨pa, pw⟩ := bb_prop he
  obtain ⟨a1, w1⟩ := bb_pi pw pw he1
  obtain ⟨a2, w2⟩ := bb_pi pw w1 he2
  refine ⟨?_, ⟨nw, names_new.2, w2⟩, Env.ind_caps_default_wf hic⟩
  rw [absConstantInfo, absConstantVal, na, a2, a1, pa, names_new.1,
    Env.ind_caps_default_refines hic]
  rfl

/-- `ConLeche/Kernel/StdAxioms.lean:221-229 iffIntroRaw` —
`std_axioms::iff_intro_raw` refines `iffIntroRaw`, at the pinned arity `2 2`. -/
theorem iff_intro_raw_refines {ci : env.ConstantInfo}
    (h : std_axioms.iff_intro_raw = ok ci) :
    absConstantInfo ci = ConLeche.iffIntroRaw ∧ ConstantInfoWF ci := by
  rw [std_axioms.iff_intro_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, e1, he1, e2, he2, e3, he3, e4, he4, n1, hn1, e5, he5,
    e6, he6, e7, he7, e8, he8, e9, he9, e10, he10, e11, he11, rfl⟩ := h
  obtain ⟨na, nw⟩ := iff_intro_name_refines hn
  obtain ⟨pa, pw⟩ := bb_prop he
  obtain ⟨a1, w1⟩ := bb_bv he1
  obtain ⟨a2, w2⟩ := bb_pi w1 w1 he2
  obtain ⟨a3, w3⟩ := bb_bv he3
  obtain ⟨a4, w4⟩ := bb_pi w1 w3 he4
  obtain ⟨na1, nw1⟩ := iff_name_refines hn1
  obtain ⟨a5, w5⟩ := bb_cnst nw1 levels_new.2 he5
  obtain ⟨a6, w6⟩ := bb_bv he6
  obtain ⟨a7, w7⟩ := bb_ap2 w5 w3 w6 he7
  obtain ⟨a8, w8⟩ := bb_pi w4 w7 he8
  obtain ⟨a9, w9⟩ := bb_pi w2 w8 he9
  obtain ⟨a10, w10⟩ := bb_pi pw w9 he10
  obtain ⟨a11, w11⟩ := bb_pi pw w10 he11
  refine ⟨?_, nw, names_new.2, w11⟩
  rw [absConstantInfo, absConstantVal, na, a11, a10, a9, a8, a7, a6, a5, a4, a3,
    a2, a1, pa, na1, levels_new.1, names_new.1]
  rfl

/-- `ConLeche/Kernel/StdAxioms.lean:231-236 iffRecIntro` —
`std_axioms::iff_rec_intro` refines `iffRecIntro`, `Iff.rec`'s minor premise in
the `a`/`b`/`motive` binder context. -/
theorem iff_rec_intro_refines {e : expr.Expr} (h : std_axioms.iff_rec_intro = ok e) :
    absExpr e = ConLeche.iffRecIntro ∧ ExprWF e := by
  rw [std_axioms.iff_rec_intro] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e0, he0, e1, he1, e2, he2, e3, he3, n, hn, e4, he4, e5, he5, e6, he6,
    e7, he7, e8, he8, e9, he9, e10, he10, hlast⟩ := h
  obtain ⟨a0, w0⟩ := bb_bv he0
  obtain ⟨a1, w1⟩ := bb_pi w0 w0 he1
  obtain ⟨a2, w2⟩ := bb_bv he2
  obtain ⟨a3, w3⟩ := bb_pi w0 w2 he3
  obtain ⟨na, nw⟩ := iff_intro_name_refines hn
  obtain ⟨a4, w4⟩ := bb_cnst nw levels_new.2 he4
  obtain ⟨a5, w5⟩ := bb_bv he5
  obtain ⟨a6, w6⟩ := bb_bv he6
  obtain ⟨a7, w7⟩ := bb_bv he7
  obtain ⟨a8, w8⟩ := bb_ap4 w4 w2 w5 w6 w7 he8
  obtain ⟨a10, w10⟩ := bb_pi w3 (Expr.app_wf w0 w8 he9) he10
  obtain ⟨alast, wlast⟩ := bb_pi w1 w10 hlast
  refine ⟨?_, wlast⟩
  rw [alast, a10, Expr.app_refines he9, a8, a7, a6, a5, a4, a3, a2, a1, a0, na,
    levels_new.1]
  rfl

/-- `ConLeche/Kernel/StdAxioms.lean:238-248 iffRecRaw` —
`std_axioms::iff_rec_raw` refines `iffRecRaw`, at the pinned arity `4 4` and
with no reduction rules. -/
theorem iff_rec_raw_refines {ci : env.ConstantInfo}
    (h : std_axioms.iff_rec_raw = ok ci) :
    absConstantInfo ci = ConLeche.iffRecRaw ∧ ConstantInfoWF ci := by
  rw [std_axioms.iff_rec_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, lps, hlps, n1, hn1, e, he, n2, hn2, e1, he1, e2, he2, e3, he3,
    e4, he4, l, hl, e5, he5, e6, he6, e7, he7, e8, he8, e9, he9, e10, he10,
    e11, he11, e12, he12, e13, he13, e14, he14, e15, he15, e16, he16,
    e17, he17, rfl⟩ := h
  obtain ⟨ua, uw⟩ := bb_u_n hn
  obtain ⟨la, lw⟩ := names_singleton uw hlps
  obtain ⟨na, nw⟩ := iff_rec_name_refines hn1
  obtain ⟨pa, pw⟩ := bb_prop he
  obtain ⟨n2a, n2w⟩ := iff_name_refines hn2
  obtain ⟨a1, w1⟩ := bb_cnst n2w levels_new.2 he1
  obtain ⟨a2, w2⟩ := bb_bv he2
  obtain ⟨a3, w3⟩ := bb_bv he3
  obtain ⟨a4, w4⟩ := bb_ap2 w1 w2 w3 he4
  obtain ⟨lva, lvw⟩ := bb_u hl
  obtain ⟨a5, w5⟩ := bb_srt lvw he5
  obtain ⟨a6, w6⟩ := bb_pi w4 w5 he6
  obtain ⟨a7, w7⟩ := iff_rec_intro_refines he7
  obtain ⟨a8, w8⟩ := bb_cnst n2w levels_new.2 he8
  obtain ⟨a9, w9⟩ := bb_bv he9
  obtain ⟨a10, w10⟩ := bb_bv he10
  obtain ⟨a11, w11⟩ := bb_ap2 w8 w9 w10 he11
  obtain ⟨a13, w13⟩ := bb_pi w11 (Expr.app_wf w10 w3 he12) he13
  obtain ⟨a14, w14⟩ := bb_pi w7 w13 he14
  obtain ⟨a15, w15⟩ := bb_pi w6 w14 he15
  obtain ⟨a16, w16⟩ := bb_pi pw w15 he16
  obtain ⟨a17, w17⟩ := bb_pi pw w16 he17
  refine ⟨?_, ⟨nw, lw, w17⟩, ?_⟩
  · rw [absConstantInfo, absConstantVal, na, la, ua, a17, a16, a15, a14, a13,
      Expr.app_refines he12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, lva,
      pa, n2a, levels_new.1]
    simp only [alloc.vec.Vec.new]
    rfl
  · intro r hr; simp [alloc.vec.Vec.new] at hr

/-- `ConLeche/Kernel/StdAxioms.lean:250-252 iffFamily` —
`std_axioms::iff_family` refines `iffFamily`, the raw `Iff` family in
dependency order. -/
theorem iff_family_refines {v : alloc.vec.Vec env.ConstantInfo}
    (h : std_axioms.iff_family = ok v) :
    absConstantInfos v = ConLeche.iffFamily ∧ ConstantInfosWF v := by
  rw [std_axioms.iff_family] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, fam, hfam, ci1, hci1, fam1, hfam1, ci2, hci2, hlast⟩ := h
  obtain ⟨a0, w0⟩ := iff_raw_refines hci
  obtain ⟨a1, w1⟩ := iff_intro_raw_refines hci1
  obtain ⟨a2, w2⟩ := iff_rec_raw_refines hci2
  have hval : v.val = [ci, ci1, ci2] := by
    rw [vec_push_val hlast, vec_push_val hfam1, vec_push_val hfam]
    simp [alloc.vec.Vec.new]
  refine ⟨?_, ?_⟩
  · rw [absConstantInfos, hval]
    simp only [List.map_cons, List.map_nil, a0, a1, a2]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl
    exacts [w0, w1, w2]

/-- con-leche: none — `std_axioms::one_level` is the level list `[.succ .zero]`
the pinned `Eq` of `propextRaw`'s conclusion carries; Lean writes it inline. -/
theorem one_level_refines {v : alloc.vec.Vec level.Level}
    (h : std_axioms.one_level = ok v) :
    absLevels v = [.succ .zero] ∧ LevelsWF v := by
  rw [std_axioms.one_level] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨l, hl, l1, hl1, hpush⟩ := h
  have hw : LevelWF l1 := Level.succ_wf (Level.zero_wf hl) hl1
  obtain ⟨a, w⟩ := levels_singleton hw hpush
  exact ⟨by rw [a, Level.succ_refines hl1, Level.zero_refines hl], w⟩

/-- `ConLeche/Kernel/StdAxioms.lean:254-261 propextRaw`
(`:316-319` `#annotate_pins`, computing `propextA`) —
`std_axioms::propext_raw` refines `propextRaw`. -/
theorem propext_raw_refines {cv : env.ConstantVal} (h : std_axioms.propext_raw = ok cv) :
    absConstantVal cv = ConLeche.propextRaw ∧ ConstantValWF cv := by
  rw [std_axioms.propext_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, n1, hn1, e1, he1, e2, he2, e3, he3, e4, he4, n2, hn2,
    vs, hvs, e5, he5, e6, he6, e7, he7, e8, he8, e9, he9, e10, he10, rfl⟩ := h
  obtain ⟨na, nw⟩ := propext_name_refines hn
  obtain ⟨pa, pw⟩ := bb_prop he
  obtain ⟨n1a, n1w⟩ := iff_name_refines hn1
  obtain ⟨a1, w1⟩ := bb_cnst n1w levels_new.2 he1
  obtain ⟨a2, w2⟩ := bb_bv he2
  obtain ⟨a3, w3⟩ := bb_bv he3
  obtain ⟨a4, w4⟩ := bb_ap2 w1 w2 w3 he4
  obtain ⟨n2a, n2w⟩ := BasisNames.eq_name_refines hn2
  obtain ⟨vsa, vsw⟩ := one_level_refines hvs
  obtain ⟨a5, w5⟩ := bb_cnst n2w vsw he5
  obtain ⟨a6, w6⟩ := bb_bv he6
  obtain ⟨a7, w7⟩ := bb_ap3 w5 pw w6 w2 he7
  obtain ⟨a8, w8⟩ := bb_pi w4 w7 he8
  obtain ⟨a9, w9⟩ := bb_pi pw w8 he9
  obtain ⟨a10, w10⟩ := bb_pi pw w9 he10
  refine ⟨?_, nw, names_new.2, w10⟩
  rw [absConstantVal, na, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, pa, n1a, n2a,
    vsa, levels_new.1, names_new.1]
  rfl

/-- `ConLeche/Kernel/StdAxioms.lean:263-265 nonemptyRaw` —
`std_axioms::nonempty_raw` refines `nonemptyRaw`. -/
theorem nonempty_raw_refines {ci : env.ConstantInfo}
    (h : std_axioms.nonempty_raw = ok ci) :
    absConstantInfo ci = ConLeche.nonemptyRaw ∧ ConstantInfoWF ci := by
  rw [std_axioms.nonempty_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, lps, hlps, n1, hn1, l, hl, e, he, e1, he1, e2, he2, ic, hic, rfl⟩ := h
  obtain ⟨ua, uw⟩ := bb_u_n hn
  obtain ⟨la, lw⟩ := names_singleton uw hlps
  obtain ⟨na, nw⟩ := nonempty_name_refines hn1
  obtain ⟨lva, lvw⟩ := bb_u hl
  obtain ⟨a, w⟩ := bb_srt lvw he
  obtain ⟨pa, pw⟩ := bb_prop he1
  obtain ⟨a2, w2⟩ := bb_pi w pw he2
  refine ⟨?_, ⟨nw, lw, w2⟩, Env.ind_caps_default_wf hic⟩
  rw [absConstantInfo, absConstantVal, na, la, ua, a2, a, pa, lva,
    Env.ind_caps_default_refines hic]
  rfl

/-- `ConLeche/Kernel/StdAxioms.lean:267-273 nonemptyIntroRaw` —
`std_axioms::nonempty_intro_raw` refines `nonemptyIntroRaw`, at arity `1 1`. -/
theorem nonempty_intro_raw_refines {ci : env.ConstantInfo}
    (h : std_axioms.nonempty_intro_raw = ok ci) :
    absConstantInfo ci = ConLeche.nonemptyIntroRaw ∧ ConstantInfoWF ci := by
  rw [std_axioms.nonempty_intro_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, lps, hlps, l, hl, us, hus, n1, hn1, e, he, e1, he1, n2, hn2,
    e2, he2, e3, he3, e4, he4, e5, he5, e6, he6, rfl⟩ := h
  obtain ⟨ua, uw⟩ := bb_u_n hn
  obtain ⟨la, lw⟩ := names_singleton uw hlps
  obtain ⟨lva, lvw⟩ := bb_u hl
  obtain ⟨usa, usw⟩ := levels_singleton lvw hus
  obtain ⟨na, nw⟩ := nonempty_intro_name_refines hn1
  obtain ⟨a, w⟩ := bb_srt lvw he
  obtain ⟨a1, w1⟩ := bb_bv he1
  obtain ⟨n2a, n2w⟩ := nonempty_name_refines hn2
  obtain ⟨a2, w2⟩ := bb_cnst n2w usw he2
  obtain ⟨a3, w3⟩ := bb_bv he3
  obtain ⟨a5, w5⟩ := bb_pi w1 (Expr.app_wf w2 w3 he4) he5
  obtain ⟨a6, w6⟩ := bb_pi w w5 he6
  refine ⟨?_, nw, lw, w6⟩
  rw [absConstantInfo, absConstantVal, na, la, ua, a6, a5, Expr.app_refines he4,
    a3, a2, a1, a, n2a, usa, lva]
  rfl

/-- `ConLeche/Kernel/StdAxioms.lean:275-287 nonemptyRecRaw` —
`std_axioms::nonempty_rec_raw` refines `nonemptyRecRaw`, at arity `3 3`, with
the motive sort pinned to `Prop` (the cited guidance). -/
theorem nonempty_rec_raw_refines {ci : env.ConstantInfo}
    (h : std_axioms.nonempty_rec_raw = ok ci) :
    absConstantInfo ci = ConLeche.nonemptyRecRaw ∧ ConstantInfoWF ci := by
  rw [std_axioms.nonempty_rec_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, lps, hlps, l, hl, us1, hus1, us2, hus2, us3, hus3, n1, hn1,
    e, he, n2, hn2, e1, he1, e2, he2, e3, he3, e4, he4, e5, he5, e6, he6,
    n3, hn3, e7, he7, e8, he8, e9, he9, e10, he10, e11, he11, e12, he12,
    e13, he13, e14, he14, e15, he15, e16, he16, e17, he17, e18, he18, rfl⟩ := h
  obtain ⟨ua, uw⟩ := bb_u_n hn
  obtain ⟨la, lw⟩ := names_singleton uw hlps
  obtain ⟨lva, lvw⟩ := bb_u hl
  obtain ⟨u1a, u1w⟩ := levels_singleton lvw hus1
  obtain ⟨u2a, u2w⟩ := levels_singleton lvw hus2
  obtain ⟨u3a, u3w⟩ := levels_singleton lvw hus3
  obtain ⟨na, nw⟩ := nonempty_rec_name_refines hn1
  obtain ⟨a, w⟩ := bb_srt lvw he
  obtain ⟨n2a, n2w⟩ := nonempty_name_refines hn2
  obtain ⟨a1, w1⟩ := bb_cnst n2w u1w he1
  obtain ⟨a2, w2⟩ := bb_bv he2
  obtain ⟨pa, pw⟩ := bb_prop he4
  obtain ⟨a5, w5⟩ := bb_pi (Expr.app_wf w1 w2 he3) pw he5
  obtain ⟨a6, w6⟩ := bb_bv he6
  obtain ⟨n3a, n3w⟩ := nonempty_intro_name_refines hn3
  obtain ⟨a7, w7⟩ := bb_cnst n3w u2w he7
  obtain ⟨a8, w8⟩ := bb_bv he8
  obtain ⟨a9, w9⟩ := bb_ap2 w7 w8 w2 he9
  obtain ⟨a11, w11⟩ := bb_pi w6 (Expr.app_wf w6 w9 he10) he11
  obtain ⟨a12, w12⟩ := bb_cnst n2w u3w he12
  obtain ⟨a15, w15⟩ :=
    bb_pi (Expr.app_wf w12 w8 he13) (Expr.app_wf w8 w2 he14) he15
  obtain ⟨a16, w16⟩ := bb_pi w11 w15 he16
  obtain ⟨a17, w17⟩ := bb_pi w5 w16 he17
  obtain ⟨a18, w18⟩ := bb_pi w w17 he18
  refine ⟨?_, ⟨nw, lw, w18⟩, ?_⟩
  · rw [absConstantInfo, absConstantVal, na, la, ua, a18, a17, a16, a15,
      Expr.app_refines he13, Expr.app_refines he14, a12, a11,
      Expr.app_refines he10, a9, a8, a7, a6, a5, Expr.app_refines he3, a2, a1,
      pa, a, n2a, n3a, u1a, u2a, u3a, lva]
    simp only [alloc.vec.Vec.new]
    rfl
  · intro r hr; simp [alloc.vec.Vec.new] at hr

/-- `ConLeche/Kernel/StdAxioms.lean:289-291 nonemptyFamily` —
`std_axioms::nonempty_family` refines `nonemptyFamily`. -/
theorem nonempty_family_refines {v : alloc.vec.Vec env.ConstantInfo}
    (h : std_axioms.nonempty_family = ok v) :
    absConstantInfos v = ConLeche.nonemptyFamily ∧ ConstantInfosWF v := by
  rw [std_axioms.nonempty_family] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, fam, hfam, ci1, hci1, fam1, hfam1, ci2, hci2, hlast⟩ := h
  obtain ⟨a0, w0⟩ := nonempty_raw_refines hci
  obtain ⟨a1, w1⟩ := nonempty_intro_raw_refines hci1
  obtain ⟨a2, w2⟩ := nonempty_rec_raw_refines hci2
  have hval : v.val = [ci, ci1, ci2] := by
    rw [vec_push_val hlast, vec_push_val hfam1, vec_push_val hfam]
    simp [alloc.vec.Vec.new]
  refine ⟨?_, ?_⟩
  · rw [absConstantInfos, hval]
    simp only [List.map_cons, List.map_nil, a0, a1, a2]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl
    exacts [w0, w1, w2]

/-- `ConLeche/Kernel/StdAxioms.lean:293-298 choiceRaw`
(`:316-319` `#annotate_pins`, computing `choiceA`) — `std_axioms::choice_raw`
refines `choiceRaw`. -/
theorem choice_raw_refines {cv : env.ConstantVal} (h : std_axioms.choice_raw = ok cv) :
    absConstantVal cv = ConLeche.choiceRaw ∧ ConstantValWF cv := by
  rw [std_axioms.choice_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, lps, hlps, l, hl, us, hus, n1, hn1, e, he, n2, hn2, e1, he1,
    e2, he2, e3, he3, e4, he4, e5, he5, e6, he6, rfl⟩ := h
  obtain ⟨ua, uw⟩ := bb_u_n hn
  obtain ⟨la, lw⟩ := names_singleton uw hlps
  obtain ⟨lva, lvw⟩ := bb_u hl
  obtain ⟨usa, usw⟩ := levels_singleton lvw hus
  obtain ⟨na, nw⟩ := choice_name_refines hn1
  obtain ⟨a, w⟩ := bb_srt lvw he
  obtain ⟨n2a, n2w⟩ := nonempty_name_refines hn2
  obtain ⟨a1, w1⟩ := bb_cnst n2w usw he1
  obtain ⟨a2, w2⟩ := bb_bv he2
  obtain ⟨a4, w4⟩ := bb_bv he4
  obtain ⟨a5, w5⟩ := bb_pi (Expr.app_wf w1 w2 he3) w4 he5
  obtain ⟨a6, w6⟩ := bb_pi w w5 he6
  refine ⟨?_, nw, lw, w6⟩
  rw [absConstantVal, na, la, ua, a6, a5, a4, Expr.app_refines he3, a2, a1, a,
    n2a, usa, lva]
  rfl


/-! ## The pin comparison (`StdAxioms.lean:71-215`)

`Expr.erasePw`/`ConstantVal.matchesPin` are the **specification** every proof
about a pin hit consumes; `Expr.erasePwEq`/`ConstantVal.matchesPinFast` are the
executed lockstep twins the `@[csimp]` lemma swaps in, and the ones every guard
below calls.  Both pairs are ported (task #13's `@[csimp]` rule) and both are
refined here, exactly; `matches_pin_fast_eq_matches_pin` is the port's copy of
the cited `@[csimp]` equation, transported through the abstraction. -/

/-- The machine-word equality test the `Bvar`/`Proj` arms use: a `U64` equality
decides the `Nat` equality of the abstracted indices. -/
theorem u64_decide_beq (i j : Std.U64) : (decide (i = j)) = (i.val == j.val) := by
  by_cases hij : i = j
  · subst hij; simp
  · have hv : i.val ≠ j.val := fun hc => hij (Std.UScalar.eq_of_val_eq hc)
    simp [hij, hv]

/-- The derived `BEq` is `decide` of the equality — the one shape every
`decide`-valued refinement in `Refine/` differs from the `==` con-leche's
comparisons are written with. -/
theorem decide_eq_beq {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (x y : α) :
    decide (x = y) = (x == y) := by
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy]

/-- `ConLeche/Kernel/StdAxioms.lean:71-122 Expr.erasePw` —
`std_axioms::erase_pw` refines `Expr.erasePw`: the specification of the pin
comparison's type test, which resets every binder's prop-ness datum and leaves
every other field alone.  Ported and uncalled (the executed test is
`erase_pw_eq`), so the provenance gate stays in step with its source. -/
theorem erase_pw_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ r : expr.Expr, std_axioms.erase_pw e = ok r →
      absExpr r = (absExpr e).erasePw ∧ ExprWF r := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    exact ⟨by rw [Expr.bvar_refines h]; rfl, Expr.bvar_wf h⟩
  | @sort u e hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, level_dup_eq] at h
    exact ⟨by rw [Expr.sort_refines h]; rfl, Expr.sort_wf hu h⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, name_dup_eq,
      bind_eq_ok_iff] at h
    obtain ⟨v1, hv1, hmk⟩ := h
    rw [Env.levels_copy_refines hv1] at hmk
    exact ⟨by rw [Expr.mk_const_refines hmk]; rfl, Expr.mk_const_wf hn hus hmk⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨l1, hl1, hlit⟩ := h
    rw [Expr.literal_dup_eq hl1] at hlit
    exact ⟨by rw [Expr.lit_refines hlit]; rfl, Expr.lit_wf hl hlit⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨t, ht, hfv⟩ := h
    obtain ⟨ta, tw⟩ := ih t ht
    exact ⟨by rw [Expr.fvar_refines hfv, ta]; rfl, Expr.fvar_wf tw hfv⟩
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨x, hx, y, hy, hap⟩ := h
    obtain ⟨xa, xw⟩ := ihf x hx
    obtain ⟨ya, yw⟩ := iha y hy
    exact ⟨by rw [Expr.app_refines hap, xa, ya]; rfl, Expr.app_wf xw yw hap⟩
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨x, hx, y, hy, bm, hbm, hlam⟩ := h
    obtain ⟨xa, xw⟩ := ihty x hx
    obtain ⟨ya, yw⟩ := ihbo y hy
    obtain ⟨ba, bw⟩ := bb_never_meta hbm
    exact ⟨by rw [Expr.lam_refines hlam, xa, ya, ba]; rfl,
      Expr.lam_wf xw yw bw hlam⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨x, hx, y, hy, bm, hbm, hall⟩ := h
    obtain ⟨xa, xw⟩ := ihty x hx
    obtain ⟨ya, yw⟩ := ihbo y hy
    obtain ⟨ba, bw⟩ := bb_never_meta hbm
    exact ⟨by rw [Expr.forall_e_refines hall, xa, ya, ba]; rfl,
      Expr.forall_e_wf xw yw bw hall⟩
  | @let_e ty v bo e hty hv hbo h1 ihty ihv ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨x, hx, y, hy, z, hz, hlet⟩ := h
    obtain ⟨xa, xw⟩ := ihty x hx
    obtain ⟨ya, yw⟩ := ihv y hy
    obtain ⟨za, zw⟩ := ihbo z hz
    exact ⟨by rw [Expr.let_e_refines hlet, xa, ya, za]; rfl,
      Expr.let_e_wf xw yw zw hlet⟩
  | @proj sn i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [std_axioms.erase_pw.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, name_dup_eq,
      bind_eq_ok_iff] at h
    obtain ⟨y, hy, hpr⟩ := h
    obtain ⟨ya, yw⟩ := ih y hy
    exact ⟨by rw [Expr.proj_refines hpr, ya]; rfl, Expr.proj_wf hs yw hpr⟩

/-- `ConLeche/Kernel/StdAxioms.lean:124-126 ConstantVal.matchesPin` —
`std_axioms::matches_pin` refines the pin comparison's **specification**,
exactly: exact name, exact level parameters, type up to the `pw` datum. -/
theorem matches_pin_refines {cv pin : env.ConstantVal} {b : Bool}
    (hcv : ConstantValWF cv) (hpin : ConstantValWF pin)
    (h : std_axioms.matches_pin cv pin = ok b) :
    b = ConLeche.ConstantVal.matchesPin (absConstantVal cv) (absConstantVal pin) := by
  rw [std_axioms.matches_pin] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨bn, hbn, h⟩ := h
  rw [Name.beq_refines hcv.1 hpin.1 hbn] at h
  rw [ConLeche.ConstantVal.matchesPin, absConstantVal, absConstantVal]
  by_cases hn : absName cv.name = absName pin.name
  · rw [if_pos (by simpa using hn)] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨bl, hbl, h⟩ := h
    rw [Env.names_beq_refines hcv.2.1 hpin.2.1 hbl] at h
    by_cases hl : absNames cv.level_params = absNames pin.level_params
    · rw [if_pos (by simpa using hl)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨t1, ht1, t2, ht2, hbeq⟩ := h
      obtain ⟨t1a, t1w⟩ := erase_pw_refines hcv.2.2 t1 ht1
      obtain ⟨t2a, t2w⟩ := erase_pw_refines hpin.2.2 t2 ht2
      rw [Expr.beq_refines t1w t2w hbeq, t1a, t2a]
      simp [hn, hl, decide_eq_beq]
    · rw [if_neg (by simpa using hl), Result.ok.injEq] at h
      simp [← h, hl]
  · rw [if_neg (by simpa using hn), Result.ok.injEq] at h
    simp [← h, hn]

/-! ### A `Vec`-free `ExprWF` inversion, all ten kinds at once

**To be moved to `Refine/Expr.lean`** beside the other `*_inv` lemmas, exactly
as `Refine/CoreKGuards.lean`'s note says of the three it needed
(`wf_const_inv`, `wf_sort_inv`, `wf_app_inv`): the lockstep descent cases on the
*other* term's kind, which throws its `ExprWF` derivation away, so it needs the
inversion at every kind rather than at three. -/

/-- The well-formedness of a node's children, read off its kind. -/
def KindWF : expr.ExprKind → Prop
  | .Bvar _ => True
  | .Fvar _ ty => ExprWF ty
  | .«Sort» u => LevelWF u
  | .Const n us => NameWF n ∧ LevelsWF us
  | .App f a => ExprWF f ∧ ExprWF a
  | .Lam ty b m => ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m
  | .ForallE ty b m => ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m
  | .LetE ty v b => ExprWF ty ∧ ExprWF v ∧ ExprWF b
  | .Lit l => LiteralWF l
  | .Proj s _ x => NameWF s ∧ ExprWF x

/-- A well-formed node's children are well formed. -/
theorem wf_kind_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {k : expr.ExprKind} (hk : e = .mk (.mk d k)) : KindWF k := by
  cases he with
  | @bvar i _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact trivial
  | @fvar idx ty _ hty h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact hty
  | @sort u _ hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact hu
  | @mk_const n us _ hn hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hn, hus⟩
  | @app f a _ hf ha h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hf, ha⟩
  | @lam ty bo m _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hty, hbo, hm⟩
  | @forall_e ty bo m _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hty, hbo, hm⟩
  | @let_e ty v bo _ hty hv hbo h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hty, hv, hbo⟩
  | @lit l _ hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact hl
  | @proj sn i x _ hs hx h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hs, hx⟩

theorem wf_fvar_inv {e : expr.Expr} (he : ExprWF e) {d idx : Std.U64}
    {ty : expr.Expr} (hk : e = .mk (.mk d (.Fvar idx ty))) : ExprWF ty :=
  wf_kind_inv he hk

theorem wf_sort_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {u : level.Level} (hk : e = .mk (.mk d (.«Sort» u))) : LevelWF u :=
  wf_kind_inv he hk

theorem wf_const_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {n : name.Name} {us : alloc.vec.Vec level.Level}
    (hk : e = .mk (.mk d (.Const n us))) : NameWF n ∧ LevelsWF us :=
  wf_kind_inv he hk

theorem wf_app_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {f a : expr.Expr} (hk : e = .mk (.mk d (.App f a))) : ExprWF f ∧ ExprWF a :=
  wf_kind_inv he hk

theorem wf_lam_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty b : expr.Expr} {m : expr.BinderMeta} (hk : e = .mk (.mk d (.Lam ty b m))) :
    ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m := wf_kind_inv he hk

theorem wf_forall_e_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty b : expr.Expr} {m : expr.BinderMeta}
    (hk : e = .mk (.mk d (.ForallE ty b m))) :
    ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m := wf_kind_inv he hk

theorem wf_let_e_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty v b : expr.Expr} (hk : e = .mk (.mk d (.LetE ty v b))) :
    ExprWF ty ∧ ExprWF v ∧ ExprWF b := wf_kind_inv he hk

theorem wf_lit_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {l : expr.Literal} (hk : e = .mk (.mk d (.Lit l))) : LiteralWF l :=
  wf_kind_inv he hk

theorem wf_proj_inv {e : expr.Expr} (he : ExprWF e) {d i : Std.U64}
    {sn : name.Name} {x : expr.Expr} (hk : e = .mk (.mk d (.Proj sn i x))) :
    NameWF sn ∧ ExprWF x := wf_kind_inv he hk

/-- `ConLeche/Kernel/StdAxioms.lean:148-162 Expr.erasePwEq` —
`std_axioms::erase_pw_eq` refines the **lockstep descent**: `a.erasePw =
b.erasePw`, decided by descending both terms together and stopping at the first
disagreement, so the walk is bounded by the pin's tree size however large the
stream side is.  The induction is on the `ExprWF` derivation of the *first*
term (which gives the node's shape and the children's well-formedness) and a
case analysis on the second term's stored kind, whose own derivation
`wf_kind_inv` recovers. -/
theorem erase_pw_eq_refines {a : expr.Expr} (ha : ExprWF a) :
    ∀ (b : expr.Expr), ExprWF b → ∀ c : Bool,
      std_axioms.erase_pw_eq a b = ok c →
      c = ConLeche.Expr.erasePwEq (absExpr a) (absExpr b) := by
  induction ha with
  | @bvar i a h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb <;>
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h <;>
      rw [← h] <;> simp [ConLeche.Expr.erasePwEq, u64_decide_beq]
  | @sort u a hu h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case «Sort» v =>
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
      rw [Level.beq_refines hu (wf_sort_inv hb rfl) h]
      simp [ConLeche.Expr.erasePwEq, decide_eq_beq]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @mk_const n us a hn hus h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case Const n2 us2 =>
      obtain ⟨hn2, hus2⟩ := wf_const_inv hb rfl
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
      obtain ⟨bn, hbn, h⟩ := h
      rw [Name.beq_refines hn hn2 hbn] at h
      by_cases hne : absName n = absName n2
      · rw [if_pos (by simpa using hne)] at h
        rw [Expr.levels_beq_refines hus hus2 h]
        simp [ConLeche.Expr.erasePwEq, hne, decide_eq_beq]
      · rw [if_neg (by simpa using hne), Result.ok.injEq] at h
        rw [← h]
        simp [ConLeche.Expr.erasePwEq, hne]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @lit l a hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case Lit l2 =>
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
      rw [Expr.literal_beq_refines hl (wf_lit_inv hb rfl) h]
      simp [ConLeche.Expr.erasePwEq, decide_eq_beq]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @fvar idx ty a hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case Fvar j t2 =>
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
      by_cases hij : idx = j
      · subst hij
        rw [if_pos rfl] at h
        rw [ih t2 (wf_fvar_inv hb rfl) c h]
        simp [ConLeche.Expr.erasePwEq]
      · have hv : idx.val ≠ j.val := fun hc => hij (Std.UScalar.eq_of_val_eq hc)
        rw [if_neg hij, Result.ok.injEq] at h
        rw [← h]
        simp [ConLeche.Expr.erasePwEq, hv]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @app f x a hf hx h1 ihf ihx =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case App f2 x2 =>
      obtain ⟨hf2, hx2⟩ := wf_app_inv hb rfl
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
      obtain ⟨b1, hb1, h⟩ := h
      rw [ihf f2 hf2 b1 hb1] at h
      cases hd : ConLeche.Expr.erasePwEq (absExpr f) (absExpr f2)
      · rw [hd, if_neg (by simp), Result.ok.injEq] at h
        rw [← h]; simp [ConLeche.Expr.erasePwEq, hd]
      · rw [hd, if_pos rfl] at h
        rw [ihx x2 hx2 c h]
        simp [ConLeche.Expr.erasePwEq, hd]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @lam ty bo m a hty hbo hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, -⟩ := wf_lam_inv hb rfl
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
      obtain ⟨b1, hb1, h⟩ := h
      rw [ihty t2 ht2 b1 hb1] at h
      cases hd : ConLeche.Expr.erasePwEq (absExpr ty) (absExpr t2)
      · rw [hd, if_neg (by simp), Result.ok.injEq] at h
        rw [← h]; simp [ConLeche.Expr.erasePwEq, hd]
      · rw [hd, if_pos rfl] at h
        rw [ihbo b2 hb2 c h]
        simp [ConLeche.Expr.erasePwEq, hd]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @forall_e ty bo m a hty hbo hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case ForallE t2 b2 m2 =>
      obtain ⟨ht2, hb2, -⟩ := wf_forall_e_inv hb rfl
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
      obtain ⟨b1, hb1, h⟩ := h
      rw [ihty t2 ht2 b1 hb1] at h
      cases hd : ConLeche.Expr.erasePwEq (absExpr ty) (absExpr t2)
      · rw [hd, if_neg (by simp), Result.ok.injEq] at h
        rw [← h]; simp [ConLeche.Expr.erasePwEq, hd]
      · rw [hd, if_pos rfl] at h
        rw [ihbo b2 hb2 c h]
        simp [ConLeche.Expr.erasePwEq, hd]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @let_e ty v bo a hty hv hbo h1 ihty ihv ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case LetE t2 v2 b2 =>
      obtain ⟨ht2, hv2, hb2⟩ := wf_let_e_inv hb rfl
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
      obtain ⟨b1, hb1, h⟩ := h
      rw [ihty t2 ht2 b1 hb1] at h
      cases hd : ConLeche.Expr.erasePwEq (absExpr ty) (absExpr t2)
      · rw [hd, if_neg (by simp), Result.ok.injEq] at h
        rw [← h]; simp [ConLeche.Expr.erasePwEq, hd]
      · rw [hd, if_pos rfl] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨b3, hb3, h⟩ := h
        rw [ihv v2 hv2 b3 hb3] at h
        cases hd2 : ConLeche.Expr.erasePwEq (absExpr v) (absExpr v2)
        · rw [hd2, if_neg (by simp), Result.ok.injEq] at h
          rw [← h]; simp [ConLeche.Expr.erasePwEq, hd, hd2]
        · rw [hd2, if_pos rfl] at h
          rw [ihbo b2 hb2 c h]
          simp [ConLeche.Expr.erasePwEq, hd, hd2]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]
  | @proj sn i x a hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro b hb c h
    obtain ⟨ndb⟩ := b
    obtain ⟨db, kb⟩ := ndb
    rw [std_axioms.erase_pw_eq.eq_def] at h
    cases kb
    case Proj s2 j e2 =>
      obtain ⟨hs2, he2⟩ := wf_proj_inv hb rfl
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
      obtain ⟨bn, hbn, h⟩ := h
      rw [Name.beq_refines hs hs2 hbn] at h
      by_cases hne : absName sn = absName s2
      · rw [if_pos (by simpa using hne)] at h
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl] at h
          rw [ih e2 he2 c h]
          simp [ConLeche.Expr.erasePwEq, hne]
        · have hv : i.val ≠ j.val := fun hc => hij (Std.UScalar.eq_of_val_eq hc)
          rw [if_neg hij, Result.ok.injEq] at h
          rw [← h]
          simp [ConLeche.Expr.erasePwEq, hne, hv]
      · rw [if_neg (by simpa using hne), Result.ok.injEq] at h
        rw [← h]
        simp [ConLeche.Expr.erasePwEq, hne]
    all_goals
      simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.erasePwEq]

/-- `ConLeche/Kernel/StdAxioms.lean:206-210 ConstantVal.matchesPinFast` —
`std_axioms::matches_pin_fast` refines the **executed** shape test, the one
every pin guard below calls. -/
theorem matches_pin_fast_refines {cv pin : env.ConstantVal} {b : Bool}
    (hcv : ConstantValWF cv) (hpin : ConstantValWF pin)
    (h : std_axioms.matches_pin_fast cv pin = ok b) :
    b = ConLeche.ConstantVal.matchesPinFast (absConstantVal cv)
      (absConstantVal pin) := by
  rw [std_axioms.matches_pin_fast] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨bn, hbn, h⟩ := h
  rw [Name.beq_refines hcv.1 hpin.1 hbn] at h
  rw [ConLeche.ConstantVal.matchesPinFast, absConstantVal, absConstantVal]
  by_cases hn : absName cv.name = absName pin.name
  · rw [if_pos (by simpa using hn)] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨bl, hbl, h⟩ := h
    rw [Env.names_beq_refines hcv.2.1 hpin.2.1 hbl] at h
    by_cases hl : absNames cv.level_params = absNames pin.level_params
    · rw [if_pos (by simpa using hl)] at h
      rw [erase_pw_eq_refines hcv.2.2 pin.ty hpin.2.2 b h]
      simp [hn, hl]
    · rw [if_neg (by simpa using hl), Result.ok.injEq] at h
      simp [← h, hl]
  · rw [if_neg (by simpa using hn), Result.ok.injEq] at h
    simp [← h, hn]

/-- `ConLeche/Kernel/StdAxioms.lean:212-215
ConstantVal.matchesPin_eq_matchesPinFast` — **the agreement**, on the port's
side: the specification and the executed test are the same `Bool`, which is
what the cited `@[csimp]` lemma says.  Every guard below is therefore equally a
statement about `matchesPin`, which is what every proof about a pin hit
consumes. -/
theorem matches_pin_fast_eq_matches_pin {cv pin : env.ConstantVal} {b : Bool}
    (hcv : ConstantValWF cv) (hpin : ConstantValWF pin)
    (h : std_axioms.matches_pin_fast cv pin = ok b) :
    b = ConLeche.ConstantVal.matchesPin (absConstantVal cv) (absConstantVal pin) := by
  rw [matches_pin_fast_refines hcv hpin h,
    ConLeche.ConstantVal.matchesPin_eq_matchesPinFast]

/-- The port's own two comparisons agree, node for node — the `@[csimp]`
equation as the port can state it. -/
theorem matches_pin_eq_fast {cv pin : env.ConstantVal} {b b' : Bool}
    (hcv : ConstantValWF cv) (hpin : ConstantValWF pin)
    (h : std_axioms.matches_pin cv pin = ok b)
    (h' : std_axioms.matches_pin_fast cv pin = ok b') : b = b' := by
  rw [matches_pin_refines hcv hpin h, matches_pin_fast_eq_matches_pin hcv hpin h']


/-! ## The annotated pins, and why comparing against the raw ones is exact

Task #24's key claim for this module, **proved**.  `ConstantVal.matchesPin`
reads three things of the pin — its name, its level parameters and its type *up
to every binder's prop-ness datum* (`Expr.erasePw`) — so two pins that agree on
those three give the same verdict against every stored constant.  The annotated
pin and the raw one do agree on all three, because `annotateBody`
(`Kernel/Core.lean:2746`) rebuilds every node unchanged except a binder's `pw`,
and no pin here has a `letE` (the one arm that changes a shape).  Each of the
eight equations below is therefore `rfl` on two closed terms — Lean checks the
annotation pass's *output*, not an argument about it. -/

/-- Two pins that agree on name, level parameters and `erasePw` of the type are
the same pin as far as `ConstantVal.matchesPin` can tell. -/
theorem matchesPin_congr {p q : ConLeche.ConstantVal} (hn : p.name = q.name)
    (hl : p.levelParams = q.levelParams) (ht : p.type.erasePw = q.type.erasePw)
    (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv p = ConLeche.ConstantVal.matchesPin cv q := by
  simp [ConLeche.ConstantVal.matchesPin, hn, hl, ht]

/-- `ConLeche/Kernel/StdAxioms.lean:308-314` — `iffA` and `iffRaw` give the
same `matchesPin` verdict. -/
theorem iffA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.iffA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.iffRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv

/-- `ConLeche/Kernel/StdAxioms.lean:308-314` — `iffIntroA` and `iffIntroRaw`. -/
theorem iffIntroA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.iffIntroA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.iffIntroRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv

/-- `ConLeche/Kernel/StdAxioms.lean:308-314` — `iffRecA` and `iffRecRaw`. -/
theorem iffRecA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.iffRecA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.iffRecRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv

/-- `ConLeche/Kernel/StdAxioms.lean:308-314` — `nonemptyA` and `nonemptyRaw`. -/
theorem nonemptyA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv

/-- `ConLeche/Kernel/StdAxioms.lean:308-314` — `nonemptyIntroA` and
`nonemptyIntroRaw`. -/
theorem nonemptyIntroA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyIntroA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyIntroRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv

/-- `ConLeche/Kernel/StdAxioms.lean:308-314` — `nonemptyRecA` and
`nonemptyRecRaw`. -/
theorem nonemptyRecA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyRecA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyRecRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv

/-- `ConLeche/Kernel/StdAxioms.lean:316-319` — `propextA` and `propextRaw`. -/
theorem propextA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.propextA
      = ConLeche.ConstantVal.matchesPin cv ConLeche.propextRaw :=
  matchesPin_congr rfl rfl rfl cv

/-- `ConLeche/Kernel/StdAxioms.lean:316-319` — `choiceA` and `choiceRaw`. -/
theorem choiceA_matchesPin_raw (cv : ConLeche.ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.choiceA
      = ConLeche.ConstantVal.matchesPin cv ConLeche.choiceRaw :=
  matchesPin_congr rfl rfl rfl cv

/-! ## The install guard (`StdAxioms.lean:322-373`, `DeclCheck.lean:240-273`)

`stdAxiomOk`'s five (resp. four) conjuncts, one Rust function each — task #24's
pattern 9, so that each `match` on a lookup ends before the next one begins.
Each is refined **exactly**: the Rust `Bool` is the cited Lean conjunct,
verbatim, including the arity patterns, which are part of the pin.

The hypotheses are `CoreKBase`'s find-agreement (`FindAgree`/`FindWF`), the
projection of task #46's `FEnv.FEnvRel`/`FEnv.FEnvWF` that the module reads —
`fenv::find` is the only environment call here. -/

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk`,
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
`std_axioms::iff_pinned` is the stored `Iff` type former against the pin. -/
theorem iff_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    (h : std_axioms.iff_pinned fe = ok b) :
    b = (match lfe.find? ConLeche.iffName with
         | some (.indInfo cvI _) =>
             ConLeche.ConstantVal.matchesPin cvI ConLeche.iffA.toConstantVal
         | _ => false) := by
  rw [std_axioms.iff_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨na, nw⟩ := iff_name_refines hn
  cases o with
  | none =>
    have hg : lfe.find? ConLeche.iffName = none := by
      rw [← na]; exact hrel.find_none nw ho
    rw [hg]
    simp only [Result.ok.injEq] at h
    exact h.symm
  | some ci =>
    have hg : lfe.find? ConLeche.iffName = some (absConstantInfo ci) := by
      rw [← na]; exact hrel.find_some nw ho
    have hciwf := hwf n ci nw ho
    cases ci
    case IndInfo cv caps =>
      rw [hg]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ci1, hci1, cvp, hcvp, hmp⟩ := h
      obtain ⟨r1, w1⟩ := iff_raw_refines hci1
      obtain ⟨r2, w2⟩ := CoreK.to_constant_val_refines w1 hcvp
      show b = ConLeche.ConstantVal.matchesPin (absConstantVal cv)
        ConLeche.iffA.toConstantVal
      rw [iffA_matchesPin_raw, matches_pin_fast_eq_matches_pin hciwf.1 w2 hmp, r2, r1]
    all_goals
      rw [hg]
      simp only [Result.ok.injEq] at h
      exact h.symm

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk`,
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
`std_axioms::iff_intro_pinned`, at the pinned arity `2 2`: the `some (.ctorInfo
cvIi 2 2)` pattern is part of the pin. -/
theorem iff_intro_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    (h : std_axioms.iff_intro_pinned fe = ok b) :
    b = (match lfe.find? ConLeche.iffIntroName with
         | some (.ctorInfo cvIi 2 2) =>
             ConLeche.ConstantVal.matchesPin cvIi ConLeche.iffIntroA.toConstantVal
         | _ => false) := by
  rw [std_axioms.iff_intro_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨na, nw⟩ := iff_intro_name_refines hn
  cases o with
  | none =>
    have hg : lfe.find? ConLeche.iffIntroName = none := by
      rw [← na]; exact hrel.find_none nw ho
    rw [hg]
    simp only [Result.ok.injEq] at h
    exact h.symm
  | some ci =>
    have hg : lfe.find? ConLeche.iffIntroName = some (absConstantInfo ci) := by
      rw [← na]; exact hrel.find_some nw ho
    have hciwf := hwf n ci nw ho
    cases ci
    case CtorInfo cv np nf =>
      rw [hg]
      simp only [] at h
      by_cases hnp : np = 2#u64
      · subst hnp
        by_cases hnf : nf = 2#u64
        · subst hnf
          rw [if_pos rfl, if_pos rfl] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨ci1, hci1, cvp, hcvp, hmp⟩ := h
          obtain ⟨r1, w1⟩ := iff_intro_raw_refines hci1
          obtain ⟨r2, w2⟩ := CoreK.to_constant_val_refines w1 hcvp
          show b = ConLeche.ConstantVal.matchesPin (absConstantVal cv)
            ConLeche.iffIntroA.toConstantVal
          rw [iffIntroA_matchesPin_raw,
            matches_pin_fast_eq_matches_pin hciwf w2 hmp, r2, r1]
        · rw [if_pos rfl, if_neg hnf, Result.ok.injEq] at h
          split
          · rename_i heq
            simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq,
              absConstantInfo] at heq
            exact absurd (Std.UScalar.eq_of_val_eq heq.2.2) hnf
          · exact h.symm
      · rw [if_neg hnp, Result.ok.injEq] at h
        split
        · rename_i heq
          simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq,
            absConstantInfo] at heq
          exact absurd (Std.UScalar.eq_of_val_eq heq.2.1) hnp
        · exact h.symm
    all_goals
      rw [hg]
      simp only [Result.ok.injEq] at h
      exact h.symm

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk`,
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
`std_axioms::iff_rec_pinned`, at the pinned arity `4 4`.  Only the recursor's
*type* is read, never its reduction rules (the cited note). -/
theorem iff_rec_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    (h : std_axioms.iff_rec_pinned fe = ok b) :
    b = (match lfe.find? ConLeche.iffRecName with
         | some (.recInfo cvIr 4 4 _) =>
             ConLeche.ConstantVal.matchesPin cvIr ConLeche.iffRecA.toConstantVal
         | _ => false) := by
  rw [std_axioms.iff_rec_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨na, nw⟩ := iff_rec_name_refines hn
  cases o with
  | none =>
    have hg : lfe.find? ConLeche.iffRecName = none := by
      rw [← na]; exact hrel.find_none nw ho
    rw [hg]
    simp only [Result.ok.injEq] at h
    exact h.symm
  | some ci =>
    have hg : lfe.find? ConLeche.iffRecName = some (absConstantInfo ci) := by
      rw [← na]; exact hrel.find_some nw ho
    have hciwf := hwf n ci nw ho
    cases ci
    case RecInfo cv mi rp rs =>
      rw [hg]
      simp only [] at h
      by_cases hmi : mi = 4#u64
      · subst hmi
        by_cases hrp : rp = 4#u64
        · subst hrp
          rw [if_pos rfl, if_pos rfl] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨ci1, hci1, cvp, hcvp, hmp⟩ := h
          obtain ⟨r1, w1⟩ := iff_rec_raw_refines hci1
          obtain ⟨r2, w2⟩ := CoreK.to_constant_val_refines w1 hcvp
          show b = ConLeche.ConstantVal.matchesPin (absConstantVal cv)
            ConLeche.iffRecA.toConstantVal
          rw [iffRecA_matchesPin_raw,
            matches_pin_fast_eq_matches_pin hciwf.1 w2 hmp, r2, r1]
        · rw [if_pos rfl, if_neg hrp, Result.ok.injEq] at h
          split
          · rename_i heq
            simp only [Option.some.injEq, ConLeche.ConstantInfo.recInfo.injEq,
              absConstantInfo] at heq
            exact absurd (Std.UScalar.eq_of_val_eq heq.2.2.1) hrp
          · exact h.symm
      · rw [if_neg hmi, Result.ok.injEq] at h
        split
        · rename_i heq
          simp only [Option.some.injEq, ConLeche.ConstantInfo.recInfo.injEq,
            absConstantInfo] at heq
          exact absurd (Std.UScalar.eq_of_val_eq heq.2.1) hmi
        · exact h.symm
    all_goals
      rw [hg]
      simp only [Result.ok.injEq] at h
      exact h.symm

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk`,
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
`std_axioms::nonempty_pinned`. -/
theorem nonempty_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    (h : std_axioms.nonempty_pinned fe = ok b) :
    b = (match lfe.find? ConLeche.nonemptyName with
         | some (.indInfo cvN _) =>
             ConLeche.ConstantVal.matchesPin cvN ConLeche.nonemptyA.toConstantVal
         | _ => false) := by
  rw [std_axioms.nonempty_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨na, nw⟩ := nonempty_name_refines hn
  cases o with
  | none =>
    have hg : lfe.find? ConLeche.nonemptyName = none := by
      rw [← na]; exact hrel.find_none nw ho
    rw [hg]
    simp only [Result.ok.injEq] at h
    exact h.symm
  | some ci =>
    have hg : lfe.find? ConLeche.nonemptyName = some (absConstantInfo ci) := by
      rw [← na]; exact hrel.find_some nw ho
    have hciwf := hwf n ci nw ho
    cases ci
    case IndInfo cv caps =>
      rw [hg]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ci1, hci1, cvp, hcvp, hmp⟩ := h
      obtain ⟨r1, w1⟩ := nonempty_raw_refines hci1
      obtain ⟨r2, w2⟩ := CoreK.to_constant_val_refines w1 hcvp
      show b = ConLeche.ConstantVal.matchesPin (absConstantVal cv)
        ConLeche.nonemptyA.toConstantVal
      rw [nonemptyA_matchesPin_raw,
        matches_pin_fast_eq_matches_pin hciwf.1 w2 hmp, r2, r1]
    all_goals
      rw [hg]
      simp only [Result.ok.injEq] at h
      exact h.symm

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk`,
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
`std_axioms::nonempty_intro_pinned`, at the pinned arity `1 1`. -/
theorem nonempty_intro_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    (h : std_axioms.nonempty_intro_pinned fe = ok b) :
    b = (match lfe.find? ConLeche.nonemptyIntroName with
         | some (.ctorInfo cvNi 1 1) =>
             ConLeche.ConstantVal.matchesPin cvNi ConLeche.nonemptyIntroA.toConstantVal
         | _ => false) := by
  rw [std_axioms.nonempty_intro_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨na, nw⟩ := nonempty_intro_name_refines hn
  cases o with
  | none =>
    have hg : lfe.find? ConLeche.nonemptyIntroName = none := by
      rw [← na]; exact hrel.find_none nw ho
    rw [hg]
    simp only [Result.ok.injEq] at h
    exact h.symm
  | some ci =>
    have hg : lfe.find? ConLeche.nonemptyIntroName = some (absConstantInfo ci) := by
      rw [← na]; exact hrel.find_some nw ho
    have hciwf := hwf n ci nw ho
    cases ci
    case CtorInfo cv np nf =>
      rw [hg]
      simp only [] at h
      by_cases hnp : np = 1#u64
      · subst hnp
        by_cases hnf : nf = 1#u64
        · subst hnf
          rw [if_pos rfl, if_pos rfl] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨ci1, hci1, cvp, hcvp, hmp⟩ := h
          obtain ⟨r1, w1⟩ := nonempty_intro_raw_refines hci1
          obtain ⟨r2, w2⟩ := CoreK.to_constant_val_refines w1 hcvp
          show b = ConLeche.ConstantVal.matchesPin (absConstantVal cv)
            ConLeche.nonemptyIntroA.toConstantVal
          rw [nonemptyIntroA_matchesPin_raw,
            matches_pin_fast_eq_matches_pin hciwf w2 hmp, r2, r1]
        · rw [if_pos rfl, if_neg hnf, Result.ok.injEq] at h
          split
          · rename_i heq
            simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq,
              absConstantInfo] at heq
            exact absurd (Std.UScalar.eq_of_val_eq heq.2.2) hnf
          · exact h.symm
      · rw [if_neg hnp, Result.ok.injEq] at h
        split
        · rename_i heq
          simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq,
            absConstantInfo] at heq
          exact absurd (Std.UScalar.eq_of_val_eq heq.2.1) hnp
        · exact h.symm
    all_goals
      rw [hg]
      simp only [Result.ok.injEq] at h
      exact h.symm

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk`,
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
`std_axioms::nonempty_rec_pinned`, at the pinned arity `3 3`. -/
theorem nonempty_rec_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    (h : std_axioms.nonempty_rec_pinned fe = ok b) :
    b = (match lfe.find? ConLeche.nonemptyRecName with
         | some (.recInfo cvNr 3 3 _) =>
             ConLeche.ConstantVal.matchesPin cvNr ConLeche.nonemptyRecA.toConstantVal
         | _ => false) := by
  rw [std_axioms.nonempty_rec_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨na, nw⟩ := nonempty_rec_name_refines hn
  cases o with
  | none =>
    have hg : lfe.find? ConLeche.nonemptyRecName = none := by
      rw [← na]; exact hrel.find_none nw ho
    rw [hg]
    simp only [Result.ok.injEq] at h
    exact h.symm
  | some ci =>
    have hg : lfe.find? ConLeche.nonemptyRecName = some (absConstantInfo ci) := by
      rw [← na]; exact hrel.find_some nw ho
    have hciwf := hwf n ci nw ho
    cases ci
    case RecInfo cv mi rp rs =>
      rw [hg]
      simp only [] at h
      by_cases hmi : mi = 3#u64
      · subst hmi
        by_cases hrp : rp = 3#u64
        · subst hrp
          rw [if_pos rfl, if_pos rfl] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨ci1, hci1, cvp, hcvp, hmp⟩ := h
          obtain ⟨r1, w1⟩ := nonempty_rec_raw_refines hci1
          obtain ⟨r2, w2⟩ := CoreK.to_constant_val_refines w1 hcvp
          show b = ConLeche.ConstantVal.matchesPin (absConstantVal cv)
            ConLeche.nonemptyRecA.toConstantVal
          rw [nonemptyRecA_matchesPin_raw,
            matches_pin_fast_eq_matches_pin hciwf.1 w2 hmp, r2, r1]
        · rw [if_pos rfl, if_neg hrp, Result.ok.injEq] at h
          split
          · rename_i heq
            simp only [Option.some.injEq, ConLeche.ConstantInfo.recInfo.injEq,
              absConstantInfo] at heq
            exact absurd (Std.UScalar.eq_of_val_eq heq.2.2.1) hrp
          · exact h.symm
      · rw [if_neg hmi, Result.ok.injEq] at h
        split
        · rename_i heq
          simp only [Option.some.injEq, ConLeche.ConstantInfo.recInfo.injEq,
            absConstantInfo] at heq
          exact absurd (Std.UScalar.eq_of_val_eq heq.2.1) hmi
        · exact h.symm
    all_goals
      rw [hg]
      simp only [Result.ok.injEq] at h
      exact h.symm

/-! ## The guard, and the one conjunct that is another module's

`stdAxiomOk`'s `propext` arm opens with `decide (env.find? eqName = some eqA)`,
which is **not** a `matchesPin` comparison — it is an exact `ConstantInfo`
equality against the *annotated* basis pin, so the erase-`pw` argument above
does not cover it and the port answers it in `kernel/basis_pins.rs` over task
#22's generated table (`basis_pins::eq_basis_pinned`).  That is a different
module, so its refinement is *named* here and carried as a hypothesis: every
lemma that depends on it says so, and `Refine/BasisPins.lean` discharges it in
one place. -/

/-- **What `Refine/BasisPins.lean` owes this file**: `basis_pins::eq_basis_pinned`
is the cited `decide (fe.find? eqName = some eqA)`. -/
def EqBasisPinned (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  ∀ b : Bool, basis_pins.eq_basis_pinned fe = ok b →
    b = decide (lfe.find? ConLeche.eqName = some ConLeche.eqA)

/-- **`stdAxiomOkF`, with its five conjuncts spelled the way the six guard
lemmas above spell them** — `rfl`, and the one step that makes them rewritable
into it: the same `match` written in two modules elaborates to two `match`
auxiliaries, which are definitionally but not syntactically equal. -/
theorem stdAxiomOkF_eq (lfe : ConLeche.FEnv) (cvA : ConLeche.ConstantVal) :
    ConLeche.stdAxiomOkF lfe cvA =
      (if cvA.name = ConLeche.propextName then
        decide (lfe.find? ConLeche.eqName = some ConLeche.eqA) &&
        (match lfe.find? ConLeche.iffName with
         | some (.indInfo cvI _) =>
             ConLeche.ConstantVal.matchesPin cvI ConLeche.iffA.toConstantVal
         | _ => false) &&
        (match lfe.find? ConLeche.iffIntroName with
         | some (.ctorInfo cvIi 2 2) =>
             ConLeche.ConstantVal.matchesPin cvIi ConLeche.iffIntroA.toConstantVal
         | _ => false) &&
        (match lfe.find? ConLeche.iffRecName with
         | some (.recInfo cvIr 4 4 _) =>
             ConLeche.ConstantVal.matchesPin cvIr ConLeche.iffRecA.toConstantVal
         | _ => false) &&
        ConLeche.ConstantVal.matchesPin cvA ConLeche.propextA
      else if cvA.name = ConLeche.choiceName then
        (match lfe.find? ConLeche.nonemptyName with
         | some (.indInfo cvN _) =>
             ConLeche.ConstantVal.matchesPin cvN ConLeche.nonemptyA.toConstantVal
         | _ => false) &&
        (match lfe.find? ConLeche.nonemptyIntroName with
         | some (.ctorInfo cvNi 1 1) =>
             ConLeche.ConstantVal.matchesPin cvNi ConLeche.nonemptyIntroA.toConstantVal
         | _ => false) &&
        (match lfe.find? ConLeche.nonemptyRecName with
         | some (.recInfo cvNr 3 3 _) =>
             ConLeche.ConstantVal.matchesPin cvNr ConLeche.nonemptyRecA.toConstantVal
         | _ => false) &&
        ConLeche.ConstantVal.matchesPin cvA ConLeche.choiceA
      else false) := rfl

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk`,
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
**`std_axioms::std_axiom_ok` refines `stdAxiomOkF` exactly.**  The port's
nested `if`s are the cited `&&` cascade (both short-circuit, and the port's
conjuncts are the pure guards above); the two pins it compares the checked
axiom against are the *raw* `propextRaw`/`choiceRaw`, which give the annotated
`propextA`/`choiceA`'s verdict by `propextA_matchesPin_raw`/
`choiceA_matchesPin_raw`.

Deviation (task #18's point 3): con-leche's `stdAxiomOk` (over an `Env`) and
`stdAxiomOkF` (over the index) are this one Rust function; the port has one
environment spelling, the index, so the statement is against the `F`-twin. -/
theorem std_axiom_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {cv_a : env.ConstantVal} {b : Bool}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) (heqb : EqBasisPinned fe lfe)
    (hcv : ConstantValWF cv_a)
    (h : std_axioms.std_axiom_ok fe cv_a = ok b) :
    b = ConLeche.stdAxiomOkF lfe (absConstantVal cv_a) := by
  rw [std_axioms.std_axiom_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, bn, hbn, h⟩ := h
  obtain ⟨na, nw⟩ := propext_name_refines hn
  have ebn : bn = decide (absName cv_a.name = ConLeche.propextName) := by
    rw [Name.beq_refines hcv.1 nw hbn, na]
  rw [stdAxiomOkF_eq]
  by_cases hp : absName cv_a.name = ConLeche.propextName
  · rw [show bn = true by rw [ebn, hp]; simp] at h
    rw [if_pos rfl] at h
    rw [if_pos (show (absConstantVal cv_a).name = ConLeche.propextName from hp)]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    rw [← heqb b1 hb1]
    cases b1
    · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      simp [← h]
    · rw [if_pos rfl] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      rw [← iff_pinned_refines hrel hwf hb2]
      cases b2
      · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        simp [← h]
      · rw [if_pos rfl] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨b3, hb3, h⟩ := h
        rw [← iff_intro_pinned_refines hrel hwf hb3]
        cases b3
        · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          simp [← h]
        · rw [if_pos rfl] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨b4, hb4, h⟩ := h
          rw [← iff_rec_pinned_refines hrel hwf hb4]
          cases b4
          · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
            simp [← h]
          · rw [if_pos rfl] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨cvp, hcvp, hmp⟩ := h
            obtain ⟨r1, w1⟩ := propext_raw_refines hcvp
            rw [propextA_matchesPin_raw,
              matches_pin_fast_eq_matches_pin hcv w1 hmp, r1]
            simp
  · rw [show bn = false by rw [ebn]; simp [hp]] at h
    rw [if_neg (by simp)] at h
    rw [if_neg (show ¬ (absConstantVal cv_a).name = ConLeche.propextName from hp)]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, bn1, hbn1, h⟩ := h
    obtain ⟨na1, nw1⟩ := choice_name_refines hn1
    have ebn1 : bn1 = decide (absName cv_a.name = ConLeche.choiceName) := by
      rw [Name.beq_refines hcv.1 nw1 hbn1, na1]
    by_cases hc : absName cv_a.name = ConLeche.choiceName
    · rw [show bn1 = true by rw [ebn1, hc]; simp] at h
      rw [if_pos rfl] at h
      rw [if_pos (show (absConstantVal cv_a).name = ConLeche.choiceName from hc)]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      rw [← nonempty_pinned_refines hrel hwf hb2]
      cases b2
      · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        simp [← h]
      · rw [if_pos rfl] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨b3, hb3, h⟩ := h
        rw [← nonempty_intro_pinned_refines hrel hwf hb3]
        cases b3
        · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          simp [← h]
        · rw [if_pos rfl] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨b4, hb4, h⟩ := h
          rw [← nonempty_rec_pinned_refines hrel hwf hb4]
          cases b4
          · simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
            simp [← h]
          · rw [if_pos rfl] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨cvp, hcvp, hmp⟩ := h
            obtain ⟨r1, w1⟩ := choice_raw_refines hcvp
            rw [choiceA_matchesPin_raw,
              matches_pin_fast_eq_matches_pin hcv w1 hmp, r1]
            simp
    · rw [show bn1 = false by rw [ebn1]; simp [hc]] at h
      rw [if_neg (by simp), Result.ok.injEq] at h
      rw [if_neg (show ¬ (absConstantVal cv_a).name = ConLeche.choiceName from hc)]
      exact h.symm

/-- The same over task #46's full relation, which is what the declaration
checker carries: `FindAgree`/`FindWF` are its find-agreement projection
(`CoreKBase`'s two bridges). -/
theorem std_axiom_ok_refines_of_rel {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {cv_a : env.ConstantVal} {b : Bool}
    (hrel : FEnv.FEnvRel fe lfe) (hwf : FEnv.FEnvWF fe)
    (heqb : EqBasisPinned fe lfe) (hcv : ConstantValWF cv_a)
    (h : std_axioms.std_axiom_ok fe cv_a = ok b) :
    b = ConLeche.stdAxiomOkF lfe (absConstantVal cv_a) :=
  std_axiom_ok_refines (FindAgree.of_rel hrel hwf) (FindWF.of_wf hwf) heqb hcv h

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.StdAxioms.std_axiom_ok_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms std_axiom_ok_refines


end ConRon.Refine.StdAxioms
