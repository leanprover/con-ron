import ConRon.Refine.CoreKBase
import ConRon.Refine.BasisNames
import ConLeche.Kernel.StdAxioms

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
  `F`-twin, and `stdAxiomOk_eq_stdAxiomOkF` records that the two are the same
  `Bool` on a matching pair.

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

end ConRon.Refine.StdAxioms
