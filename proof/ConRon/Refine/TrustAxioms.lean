import ConRon.Refine.CoreKPinned
import ConLeche.Kernel.DeclCheck

/-! # `kernel::trust_axioms` and `kernel::trust_pins` — the compiler-trust
family (task #56)

`CORE_PLAN.md` step 7.  Two Rust modules, one file: `trust_axioms.rs`
(`ConLeche/Kernel/TrustAxioms.lean`, 30 public functions) and `trust_pins.rs`
(`ConLeche/Kernel/TrustPins.lean`, 2) — the pinned names, the pinned shapes of
`Lean.trustCompiler` / `Lean.reduceNat` / `Lean.reduceBool` /
`Lean.ofReduceNat` / `Lean.ofReduceBool`, the guards that check a stream's
declaration against them, and the two hand-pinned identity values the reduce
operations' install compares against.

## The pins are the RAW ones, and that is exact (task #24)

`TrustAxioms.lean` writes its pins twice: the raw ones, hand-written with
`Basis/Builder.lean`'s DSL (`reduceOpRaw`, `ofReduceRaw`), and the annotated
ones (`reduceNatCvA`, `reduceBoolCvA`, `ofReduceNatA`, `ofReduceBoolA`)
computed from them at elaboration time by `#annotate_pins`.  Every consumer
goes through `ConstantVal.matchesPin`, whose type test is
`a.erasePw == b.erasePw`, so `matchesPin cv (annotate pin) = matchesPin cv pin`
and the port compares against the raw pin, which it can write down, with the
annotated twin cited on the same item (DESIGN.md task #24).

Here that argument is not an argument at all but a **closed computation**:
`reduceOpCvA_erasePw` and `ofReducePinA_erasePw` below are `rfl` — the four
annotated pins and the raw ones they came from have the same name, the same
(empty) level parameters and `erasePw`-equal types.  (`reduceNatCvA` is in
fact *literally* `reduceOpRaw reduceNatName`: its one binder's codomain is a
`.const`, so `annotPwPi` answers the parse placeholder `.never` the raw pin
already carries.  The two `ofReduce*` pins differ from their raw forms in
exactly the three binder data `erasePw` erases.)  So each pin builder's lemma
is the closed equality against the **raw** con-leche pin, and each guard's
lemma is exactness against the cited Lean guard *as written* — with the
annotated pin in it.

## The `F`-twins, and what is stated against what

`DeclCheck.lean:272-308` has an `FEnv`-indexed twin of every environment
predicate here (`trustCompilerOkF`, `reduceStoredOkF`, `reduceElemOkF`,
`ofReduceAxOkF`, `reducePinGuardF`), and the port has one environment
spelling, the index (task #18's deviation 3), so every guard below is stated
against the `F`-twin, over `CoreKBase`'s find-agreement projection
(`FindAgree`/`FindWF`).  The two guards the port *factors out* of a `&&`
cascade — `true_pinned` and `true_intro_pinned` (task #3's pattern 9) — have
no Lean twin of their own and are stated against the matching conjunct of
`trustCompilerOkF`, spelled out.

`reduce_pin_guard` is the one guard whose last conjunct the port reaches
through `core_k::consts_resolve`, whose refinement (`Refine/CoreKSupport.lean`)
is against the `Env`-indexed `Expr.constsResolve`; it therefore carries
`CoreKSupport`'s own `henv` hypothesis (`lfe.find? = lenv.find?`), and the
conclusion is the `F`-twin, the two being the same clauses.

## The two hypotheses this file imports

Task #56's files are written in parallel, so — exactly as task #49's eleven
`CoreK*` files did — what a sibling owns travels as an explicit hypothesis of
the lemma that needs it:

* **`MatchesPinSpec`**: `std_axioms::matches_pin_fast` is `ConstantVal.matchesPin`.
  It is `Refine/StdAxioms.lean`'s (`Expr.erasePwEq_eq` is con-leche's own
  agreement between the lockstep descent and the specification).
* **`BasisPinsSpec`**: `basis_pins::eq_basis_pinned` / `nat_basis_pinned` are
  `decide (fe.find? eqName = some eqA)` / `decide (fe.find? natName = some natA)`
  — the two pins compared by exact `ConstantInfo` equality rather than through
  `matchesPin`, which is why they have a module of their own.

Neither is a new claim; both are discharged where the sibling lands.

## Deviations recorded

`lean_ns` has no con-leche declaration to cite: Lean spells
`anonymous |>.str "Lean"` inline at each of the five names below it.  Its lemma
is against that prefix.  `eq_app` is `ofReduceRaw`'s local `eqApp` lambda,
which §3.4 forbids, so it is a named function with the same citation.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel
open ConRon.Refine.CoreK

namespace ConRon.Refine.TrustAxioms

/-! ## The two imported hypotheses -/

/-- **`std_axioms::matches_pin_fast` is `ConstantVal.matchesPin`, exactly.**
Task #56's sibling `Refine/StdAxioms.lean` proves it; `matchesPinFast` is
con-leche's own `@[csimp]` replacement for `matchesPin`, and
`Expr.erasePwEq_eq` (`StdAxioms.lean:206-210`) is the agreement. -/
def MatchesPinSpec : Prop :=
  ∀ (cv pin : env.ConstantVal) (r : Bool), ConstantValWF cv → ConstantValWF pin →
    std_axioms.matches_pin_fast cv pin = ok r →
      r = ConLeche.ConstantVal.matchesPin (absConstantVal cv) (absConstantVal pin)

/-- **The two exactly-compared basis pins**, `Refine/BasisPins.lean`'s
(`kernel/basis_pins.rs` over task #22's generated table): the whole guard
`decide (fe.find? eqName = some eqA)` resp. `… natName = some natA`. -/
structure BasisPinsSpec (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop where
  eqPinned : ∀ r : Bool, basis_pins.eq_basis_pinned fe = ok r →
    r = decide (lfe.find? ConLeche.eqName = some ConLeche.eqA)
  natPinned : ∀ r : Bool, basis_pins.nat_basis_pinned fe = ok r →
    r = decide (lfe.find? ConLeche.natName = some ConLeche.natA)

/-! ## The annotated pins are the raw ones, under `matchesPin`

The four closed computations DESIGN.md task #24's argument predicts.  Nothing
below ever names an annotation pass: `#annotate_pins`' output is a closed term
and `Expr.erasePw` of it is the raw pin's, by `rfl`. -/

/-- `reduceOpCvA c` — the annotated pin — is `matchesPin`-indistinguishable
from the raw `reduceOpRaw` at the same operation, which is what the port
returns (`TrustAxioms.lean:146-148 reduceOpCvA`, `:137-139` the
`#annotate_pins` command). -/
theorem matchesPin_reduceOpCvA (cv : ConLeche.ConstantVal) (c : ConLeche.Name) :
    ConLeche.ConstantVal.matchesPin cv (ConLeche.reduceOpCvA c)
      = ConLeche.ConstantVal.matchesPin cv
          (if c = ConLeche.reduceNatName then ConLeche.reduceOpRaw ConLeche.reduceNatName
           else ConLeche.reduceOpRaw ConLeche.reduceBoolName) := by
  rw [ConLeche.reduceOpCvA]
  split
  · rfl
  · rfl

/-- The same for `ofReducePinA` (`TrustAxioms.lean:150-152 ofReducePinA`,
`:141-144` the `#annotate_pins` command).  Here the annotated pin genuinely
differs from the raw one — its three binders carry `.ifAllZero []` where the
raw pin carries `.never` — and that is exactly what `erasePw` erases. -/
theorem matchesPin_ofReducePinA (cv : ConLeche.ConstantVal) (n : ConLeche.Name) :
    ConLeche.ConstantVal.matchesPin cv (ConLeche.ofReducePinA n)
      = ConLeche.ConstantVal.matchesPin cv
          (if n = ConLeche.ofReduceNatName then ConLeche.ofReduceRaw ConLeche.ofReduceNatName
           else ConLeche.ofReduceRaw ConLeche.ofReduceBoolName) := by
  rw [ConLeche.ofReducePinA]
  split
  · rfl
  · rfl

/-! ## The pinned names (`TrustAxioms.lean:49-75`)

Nine `Name`-valued constants, each the same five lines as `Refine/BasisNames.lean`:
split the `do` chain and hand the pieces to `CoreKBase.str_lit_step`. -/

/-- `ConLeche/Kernel/TrustAxioms.lean:49-50 trueName` — `trust_axioms::true_name`
refines `trueName`. -/
theorem true_name_refines {n : name.Name} (h : trust_axioms.true_name = ok n) :
    absName n = ConLeche.trueName ∧ NameWF n := by
  rw [trust_axioms.true_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [84#u32, 114#u32, 117#u32, 101#u32]) (by simp [trust_axioms.true_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:52-53 trueIntroName` —
`trust_axioms::true_intro_name` refines `trueIntroName`. -/
theorem true_intro_name_refines {n : name.Name}
    (h : trust_axioms.true_intro_name = ok n) :
    absName n = ConLeche.trueIntroName ∧ NameWF n := by
  rw [trust_axioms.true_intro_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := true_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [105#u32, 110#u32, 116#u32, 114#u32, 111#u32])
    (by simp [trust_axioms.true_intro_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- con-leche: none — `trust_axioms::lean_ns` is the `Lean` namespace prefix
the cited module spells inline four times (`anonymous |>.str "Lean"`,
`TrustAxioms.lean:55-68`); it refines exactly that prefix. -/
theorem lean_ns_refines {n : name.Name} (h : trust_axioms.lean_ns = ok n) :
    absName n = ConLeche.Name.anonymous.str "Lean" ∧ NameWF n := by
  rw [trust_axioms.lean_ns] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [76#u32, 101#u32, 97#u32, 110#u32]) (by simp [trust_axioms.lean_ns.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:55-56 trustCompilerName` —
`trust_axioms::trust_compiler_name` refines `trustCompilerName`. -/
theorem trust_compiler_name_refines {n : name.Name}
    (h : trust_axioms.trust_compiler_name = ok n) :
    absName n = ConLeche.trustCompilerName ∧ NameWF n := by
  rw [trust_axioms.trust_compiler_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := lean_ns_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [116#u32, 114#u32, 117#u32, 115#u32, 116#u32, 67#u32, 111#u32, 109#u32, 112#u32,
      105#u32, 108#u32, 101#u32, 114#u32])
    (by simp [trust_axioms.trust_compiler_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:58-59 reduceNatName` —
`trust_axioms::reduce_nat_name` refines `reduceNatName`. -/
theorem reduce_nat_name_refines {n : name.Name}
    (h : trust_axioms.reduce_nat_name = ok n) :
    absName n = ConLeche.reduceNatName ∧ NameWF n := by
  rw [trust_axioms.reduce_nat_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := lean_ns_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [114#u32, 101#u32, 100#u32, 117#u32, 99#u32, 101#u32, 78#u32, 97#u32, 116#u32])
    (by simp [trust_axioms.reduce_nat_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:61-62 reduceBoolName` —
`trust_axioms::reduce_bool_name` refines `reduceBoolName`. -/
theorem reduce_bool_name_refines {n : name.Name}
    (h : trust_axioms.reduce_bool_name = ok n) :
    absName n = ConLeche.reduceBoolName ∧ NameWF n := by
  rw [trust_axioms.reduce_bool_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := lean_ns_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [114#u32, 101#u32, 100#u32, 117#u32, 99#u32, 101#u32, 66#u32, 111#u32, 111#u32,
      108#u32])
    (by simp [trust_axioms.reduce_bool_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:64-65 ofReduceNatName` —
`trust_axioms::of_reduce_nat_name` refines `ofReduceNatName`. -/
theorem of_reduce_nat_name_refines {n : name.Name}
    (h : trust_axioms.of_reduce_nat_name = ok n) :
    absName n = ConLeche.ofReduceNatName ∧ NameWF n := by
  rw [trust_axioms.of_reduce_nat_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := lean_ns_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [111#u32, 102#u32, 82#u32, 101#u32, 100#u32, 117#u32, 99#u32, 101#u32, 78#u32,
      97#u32, 116#u32])
    (by simp [trust_axioms.of_reduce_nat_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:67-68 ofReduceBoolName` —
`trust_axioms::of_reduce_bool_name` refines `ofReduceBoolName`. -/
theorem of_reduce_bool_name_refines {n : name.Name}
    (h : trust_axioms.of_reduce_bool_name = ok n) :
    absName n = ConLeche.ofReduceBoolName ∧ NameWF n := by
  rw [trust_axioms.of_reduce_bool_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := lean_ns_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [111#u32, 102#u32, 82#u32, 101#u32, 100#u32, 117#u32, 99#u32, 101#u32, 66#u32,
      111#u32, 111#u32, 108#u32])
    (by simp [trust_axioms.of_reduce_bool_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:70-71 reduceOpNames` —
`trust_axioms::reduce_op_names` refines `reduceOpNames`, the two operations in
the cited order. -/
theorem reduce_op_names_refines {v : alloc.vec.Vec name.Name}
    (h : trust_axioms.reduce_op_names = ok v) :
    absNames v = ConLeche.reduceOpNames ∧ NamesWF v := by
  rw [trust_axioms.reduce_op_names] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m0, hm0, w0, hw0, m1, hm1, hlast⟩ := h
  obtain ⟨e0, f0⟩ := reduce_nat_name_refines hm0
  obtain ⟨e1, f1⟩ := reduce_bool_name_refines hm1
  have hval : v.val = [m0, m1] := by
    rw [vec_push_val hlast, vec_push_val hw0]; simp
  refine ⟨?_, ?_⟩
  · rw [absNames, hval]
    simp only [List.map_cons, List.map_nil, e0, e1]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl
    exacts [f0, f1]

/-- `ConLeche/Kernel/TrustAxioms.lean:73-75 ofReduceOp` —
`trust_axioms::of_reduce_op` refines `ofReduceOp`: the reduce operation an
`ofReduce*` axiom speaks about. -/
theorem of_reduce_op_refines {n r : name.Name} (hn : NameWF n)
    (h : trust_axioms.of_reduce_op n = ok r) :
    absName r = ConLeche.ofReduceOp (absName n) ∧ NameWF r := by
  rw [trust_axioms.of_reduce_op] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, b, hb, h⟩ := h
  obtain ⟨ea, fa⟩ := of_reduce_nat_name_refines ha
  rw [Name.beq_refines hn fa hb, ea] at h
  rw [ConLeche.ofReduceOp]
  by_cases hc : absName n = ConLeche.ofReduceNatName
  · rw [if_pos hc]
    simp only [hc, decide_true, if_pos] at h
    exact reduce_nat_name_refines h
  · rw [if_neg hc]
    simp only [hc, decide_false, Bool.false_eq_true, if_false] at h
    exact reduce_bool_name_refines h

/-! ## TEMPORARY — the raw-pin builder's steps

`kernel/basis_builder.rs` (`ConLeche/Kernel/Basis/Builder.lean`, the DSL the
raw pins are written with) is another task-#56 file's module, so its six steps
are proved here as *steps* — the shape `str_lit_step` has — rather than as
`<fn>_refines` lemmas that would claim the module.  **To be replaced by
`Refine/BasisBuilder.lean`'s on merge.**  Each is one `Expr` constructor
application (the module's own words), so each is one line.

The empty `Vec`s a pin's `levelParams` and a `.const`'s universe arguments are
built from abstract to `[]`; that is `absNames_new`/`absLevels_new`. -/

@[simp] theorem absNames_new : absNames (alloc.vec.Vec.new name.Name) = [] := by
  simp [absNames, alloc.vec.Vec.new]

@[simp] theorem absLevels_new : absLevels (alloc.vec.Vec.new level.Level) = [] := by
  simp [absLevels, alloc.vec.Vec.new]

theorem namesWF_new : NamesWF (alloc.vec.Vec.new name.Name) := by
  intro n hn; simp [alloc.vec.Vec.new] at hn

theorem levelsWF_new : LevelsWF (alloc.vec.Vec.new level.Level) := by
  intro u hu; simp [alloc.vec.Vec.new] at hu

/-- `Basis/Builder.lean`'s `⟨.never⟩` binder datum, which
`pi`/`piI`/`piA`/`lm`/`lmI` write inline (`basis_builder::never_meta`). -/
theorem never_meta_step {m : expr.BinderMeta} (h : basis_builder.never_meta = ok m) :
    absBinderMeta m = ⟨.never⟩ ∧ BinderMetaWF m := by
  rw [basis_builder.never_meta] at h
  obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
  rw [expr.binder_meta] at h
  simp only [ptr_new_eq, bind_tc_ok, Result.ok.injEq] at h
  subst h
  exact ⟨by simp [PropWhen.never_refines hpw], PropWhenWF.never hpw⟩

/-- `Basis/Builder.lean:85-97 pi`/`piI`/`piA` — `∀ (x : ty), body` at the raw
binder annotation (one Rust function, three citations; the binder name the
three differ in is not carried by `Expr`). -/
theorem pi_step {ty b e : expr.Expr} (hty : ExprWF ty) (hb : ExprWF b)
    (h : basis_builder.pi ty b = ok e) :
    absExpr e = .forallE (absExpr ty) (absExpr b) ⟨.never⟩ ∧ ExprWF e := by
  rw [basis_builder.pi] at h
  obtain ⟨m, hm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hmabs, hmwf⟩ := never_meta_step hm
  exact ⟨by rw [Expr.forall_e_refines h, hmabs], ExprWF.forall_e hty hb hmwf h⟩

/-- `Basis/Builder.lean:99-106 lm`/`lmI` — `fun (x : ty) => body` at the raw
binder annotation. -/
theorem lm_step {ty b e : expr.Expr} (hty : ExprWF ty) (hb : ExprWF b)
    (h : basis_builder.lm ty b = ok e) :
    absExpr e = .lam (absExpr ty) (absExpr b) ⟨.never⟩ ∧ ExprWF e := by
  rw [basis_builder.lm] at h
  obtain ⟨m, hm, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hmabs, hmwf⟩ := never_meta_step hm
  exact ⟨by rw [Expr.lam_refines h, hmabs], ExprWF.lam hty hb hmwf h⟩

/-- `Basis/Builder.lean:75-76 cnst` — a constant at the given universe
arguments. -/
theorem cnst_step {n : name.Name} {us : alloc.vec.Vec level.Level} {e : expr.Expr}
    (hn : NameWF n) (hus : LevelsWF us) (h : basis_builder.cnst n us = ok e) :
    absExpr e = .const (absName n) (absLevels us) ∧ ExprWF e := by
  rw [basis_builder.cnst] at h
  exact ⟨Expr.mk_const_refines h, ExprWF.mk_const hn hus h⟩

/-- `Basis/Builder.lean:63-64 bv` — a bound variable, by de Bruijn index. -/
theorem bv_step {i : Std.U64} {e : expr.Expr} (h : basis_builder.bv i = ok e) :
    absExpr e = .bvar i.val ∧ ExprWF e := by
  rw [basis_builder.bv] at h
  exact ⟨Expr.bvar_refines h, ExprWF.bvar h⟩

/-- `Basis/Builder.lean:108-112 ap2`/`ap3` — binary and ternary application. -/
theorem ap2_step {f a b e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a) (hb : ExprWF b)
    (h : basis_builder.ap2 f a b = ok e) :
    absExpr e = .app (.app (absExpr f) (absExpr a)) (absExpr b) ∧ ExprWF e := by
  rw [basis_builder.ap2] at h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  exact ⟨by rw [Expr.app_refines h, Expr.app_refines hx],
    ExprWF.app (ExprWF.app hf ha hx) hb h⟩

theorem ap3_step {f a b c e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a) (hb : ExprWF b)
    (hc : ExprWF c) (h : basis_builder.ap3 f a b c = ok e) :
    absExpr e = .app (.app (.app (absExpr f) (absExpr a)) (absExpr b)) (absExpr c)
      ∧ ExprWF e := by
  rw [basis_builder.ap3] at h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hxabs, hxwf⟩ := ap2_step hf ha hb hx
  exact ⟨by rw [Expr.app_refines h, hxabs], ExprWF.app hxwf hc h⟩

/-- `std_axioms::one_level` — `[.succ .zero]`, the universe argument every
`Eq` application in this family carries (`StdAxioms.lean:408-412 oneLevel`;
another task-#56 file's, proved here as a step). -/
theorem one_level_step {v : alloc.vec.Vec level.Level}
    (h : std_axioms.one_level = ok v) :
    absLevels v = [.succ .zero] ∧ LevelsWF v := by
  rw [std_axioms.one_level] at h
  obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  have hval : v.val = [s] := by rw [vec_push_val h]; simp
  refine ⟨?_, ?_⟩
  · rw [absLevels, hval]
    simp only [List.map_cons, List.map_nil, Level.succ_refines hs, Level.zero_refines hz]
  · intro u hu
    rw [hval] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl
    exact LevelWF.succ (LevelWF.zero hz) hs

/-! ## The pinned shapes (`TrustAxioms.lean:77-152`) -/

/-- `ConLeche/Kernel/TrustAxioms.lean:86-87 trueCvA` — `trust_axioms::true_cv_a`
refines `trueCvA`, pinned `True`.  Already written annotated in the Lean:
`Sort 0` has no binder. -/
theorem true_cv_a_refines {cv : env.ConstantVal} (h : trust_axioms.true_cv_a = ok cv) :
    absConstantVal cv = ConLeche.trueCvA ∧ ConstantValWF cv := by
  rw [trust_axioms.true_cv_a] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := true_name_refines hn
  replace h := (Result.ok_injective h).symm; subst h
  exact ⟨by simp [absConstantVal, hnabs, Expr.sort_refines hs, Level.zero_refines hz,
      ConLeche.trueCvA],
    ⟨hnwf, namesWF_new, ExprWF.sort (LevelWF.zero hz) hs⟩⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:89-90 trueIntroCvA` —
`trust_axioms::true_intro_cv_a` refines `trueIntroCvA`, pinned `True.intro`. -/
theorem true_intro_cv_a_refines {cv : env.ConstantVal}
    (h : trust_axioms.true_intro_cv_a = ok cv) :
    absConstantVal cv = ConLeche.trueIntroCvA ∧ ConstantValWF cv := by
  rw [trust_axioms.true_intro_cv_a] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := true_intro_name_refines hn
  obtain ⟨htabs, htwf⟩ := true_name_refines ht
  replace h := (Result.ok_injective h).symm; subst h
  exact ⟨by simp [absConstantVal, hnabs, Expr.mk_const_refines he, htabs,
      ConLeche.trueIntroCvA],
    ⟨hnwf, namesWF_new, ExprWF.mk_const htwf levelsWF_new he⟩⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:92-93 trustCompilerA` —
`trust_axioms::trust_compiler_a` refines `trustCompilerA`, pinned
`Lean.trustCompiler : True`. -/
theorem trust_compiler_a_refines {cv : env.ConstantVal}
    (h : trust_axioms.trust_compiler_a = ok cv) :
    absConstantVal cv = ConLeche.trustCompilerA ∧ ConstantValWF cv := by
  rw [trust_axioms.trust_compiler_a] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := trust_compiler_name_refines hn
  obtain ⟨htabs, htwf⟩ := true_name_refines ht
  replace h := (Result.ok_injective h).symm; subst h
  exact ⟨by simp [absConstantVal, hnabs, Expr.mk_const_refines he, htabs,
      ConLeche.trustCompilerA],
    ⟨hnwf, namesWF_new, ExprWF.mk_const htwf levelsWF_new he⟩⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:95-96 boolCvA` — `trust_axioms::bool_cv_a`
refines `boolCvA`, pinned `Bool` (shape only). -/
theorem bool_cv_a_refines {cv : env.ConstantVal} (h : trust_axioms.bool_cv_a = ok cv) :
    absConstantVal cv = ConLeche.boolCvA ∧ ConstantValWF cv := by
  rw [trust_axioms.bool_cv_a] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := CoreK.bool_name_refines hn
  replace h := (Result.ok_injective h).symm; subst h
  exact ⟨by simp [absConstantVal, hnabs, Expr.sort_refines he, Level.succ_refines hs,
      Level.zero_refines hz, ConLeche.boolCvA],
    ⟨hnwf, namesWF_new, ExprWF.sort (LevelWF.succ (LevelWF.zero hz) hs) he⟩⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:98-100 reduceElemName` —
`trust_axioms::reduce_elem_name` refines `reduceElemName`, the element
inductive of a reduce operation. -/
theorem reduce_elem_name_refines {c r : name.Name} (hc : NameWF c)
    (h : trust_axioms.reduce_elem_name c = ok r) :
    absName r = ConLeche.reduceElemName (absName c) ∧ NameWF r := by
  rw [trust_axioms.reduce_elem_name] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ea, fa⟩ := reduce_nat_name_refines ha
  rw [Name.beq_refines hc fa hb, ea] at h
  rw [ConLeche.reduceElemName]
  by_cases hq : absName c = ConLeche.reduceNatName
  · rw [if_pos hq]
    simp only [hq, decide_true, if_pos] at h
    exact BasisNames.nat_name_refines h
  · rw [if_neg hq]
    simp only [hq, decide_false, Bool.false_eq_true, if_false] at h
    exact CoreK.bool_name_refines h

/-- `ConLeche/Kernel/TrustAxioms.lean:102-104 reduceElemTy` —
`trust_axioms::reduce_elem_ty` refines `reduceElemTy`, the element type as the
pinned constant. -/
theorem reduce_elem_ty_refines {c : name.Name} {e : expr.Expr} (hc : NameWF c)
    (h : trust_axioms.reduce_elem_ty c = ok e) :
    absExpr e = ConLeche.reduceElemTy (absName c) ∧ ExprWF e := by
  rw [trust_axioms.reduce_elem_ty] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ea, fa⟩ := reduce_nat_name_refines ha
  rw [Name.beq_refines hc fa hb, ea] at h
  rw [ConLeche.reduceElemTy]
  by_cases hq : absName c = ConLeche.reduceNatName
  · rw [if_pos hq]
    simp only [hq, decide_true, if_pos] at h
    obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hnabs, hnwf⟩ := BasisNames.nat_name_refines hn
    exact ⟨by rw [Expr.mk_const_refines h, hnabs, absLevels_new],
      ExprWF.mk_const hnwf levelsWF_new h⟩
  · rw [if_neg hq]
    simp only [hq, decide_false, Bool.false_eq_true, if_false] at h
    obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hnabs, hnwf⟩ := CoreK.bool_name_refines hn
    exact ⟨by rw [Expr.mk_const_refines h, hnabs, absLevels_new],
      ExprWF.mk_const hnwf levelsWF_new h⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:106-108 reduceOpRaw` —
`trust_axioms::reduce_op_raw` refines `reduceOpRaw`: the raw pinned type
`∀ (n : τ), τ` of `Lean.reduceNat` / `Lean.reduceBool`. -/
theorem reduce_op_raw_refines {c : name.Name} {cv : env.ConstantVal} (hc : NameWF c)
    (h : trust_axioms.reduce_op_raw c = ok cv) :
    absConstantVal cv = ConLeche.reduceOpRaw (absName c) ∧ ConstantValWF cv := by
  rw [trust_axioms.reduce_op_raw] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨htabs, htwf⟩ := reduce_elem_ty_refines hc ht
  obtain ⟨hpabs, hpwf⟩ := pi_step htwf htwf hp
  replace h := (Result.ok_injective h).symm; subst h
  have hnc : absName n = absName c := Name.dup_refines hn
  have hnwf : NameWF n := by
    rw [name_dup_eq] at hn; rw [← Result.ok_injective hn]; exact hc
  refine ⟨?_, ⟨hnwf, namesWF_new, hpwf⟩⟩
  simp only [absConstantVal, hnc, absNames_new, hpabs, htabs,
    ConLeche.reduceOpRaw, ConLeche.BasisDSL.pi]

/-- `ConLeche/Kernel/TrustAxioms.lean:110-120 ofReduceRaw` —
`trust_axioms::eq_app` is `ofReduceRaw`'s local `eqApp` lambda, `Eq.{1} τ x y`
at the operation's element type; §3.4 forbids the closure, so the port has it
as a named function (task #18's point 5) and it refines exactly that body. -/
theorem eq_app_refines {c : name.Name} {x y e : expr.Expr} (hc : NameWF c)
    (hx : ExprWF x) (hy : ExprWF y) (h : trust_axioms.eq_app c x y = ok e) :
    absExpr e = ConLeche.BasisDSL.ap3 (ConLeche.BasisDSL.cnst ConLeche.eqName [.succ .zero])
        (ConLeche.reduceElemTy (absName c)) (absExpr x) (absExpr y) ∧ ExprWF e := by
  rw [trust_axioms.eq_app] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := BasisNames.eq_name_refines hn
  obtain ⟨hvabs, hvwf⟩ := one_level_step hv
  obtain ⟨hfabs, hfwf⟩ := cnst_step hnwf hvwf hf
  obtain ⟨htabs, htwf⟩ := reduce_elem_ty_refines hc ht
  obtain ⟨habs, hwf⟩ := ap3_step hfwf htwf hx hy h
  refine ⟨?_, hwf⟩
  rw [habs, hfabs, hnabs, hvabs, htabs]
  rfl

/-- `ConLeche/Kernel/TrustAxioms.lean:110-120 ofReduceRaw` —
`trust_axioms::of_reduce_raw` refines `ofReduceRaw`: the raw pinned type
`∀ (a b : τ), reduce a = b → a = b`. -/
theorem of_reduce_raw_refines {n : name.Name} {cv : env.ConstantVal} (hn : NameWF n)
    (h : trust_axioms.of_reduce_raw n = ok cv) :
    absConstantVal cv = ConLeche.ofReduceRaw (absName n) ∧ ConstantValWF cv := by
  rw [trust_axioms.of_reduce_raw] at h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e3, he3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e4, he4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e5, he5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e6, he6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e7, he7, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e8, he8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e9, he9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e10, he10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hcabs, hcwf⟩ := of_reduce_op_refines hn hc
  have hn1wf : NameWF n1 := by
    rw [name_dup_eq] at hn1; rw [← Result.ok_injective hn1]; exact hn
  have hn2wf : NameWF n2 := by
    rw [name_dup_eq] at hn2; rw [← Result.ok_injective hn2]; exact hcwf
  obtain ⟨htabs, htwf⟩ := reduce_elem_ty_refines hcwf ht
  obtain ⟨h1abs, h1wf⟩ := cnst_step hn2wf levelsWF_new he1
  obtain ⟨h2abs, h2wf⟩ := bv_step he2
  obtain ⟨h4abs, h4wf⟩ := bv_step he4
  obtain ⟨h6abs, h6wf⟩ := bv_step he6
  have h3abs : absExpr e3 = .app (absExpr e1) (absExpr e2) := Expr.app_refines he3
  have h3wf : ExprWF e3 := ExprWF.app h1wf h2wf he3
  obtain ⟨h5abs, h5wf⟩ := eq_app_refines hcwf h3wf h4wf he5
  obtain ⟨h7abs, h7wf⟩ := eq_app_refines hcwf h6wf h2wf he7
  obtain ⟨h8abs, h8wf⟩ := pi_step h5wf h7wf he8
  obtain ⟨h9abs, h9wf⟩ := pi_step htwf h8wf he9
  obtain ⟨h10abs, h10wf⟩ := pi_step htwf h9wf he10
  replace h := (Result.ok_injective h).symm; subst h
  refine ⟨?_, ⟨hn1wf, namesWF_new, h10wf⟩⟩
  have hn1abs : absName n1 = absName n := Name.dup_refines hn1
  have hn2abs : absName n2 = absName c := Name.dup_refines hn2
  simp only [absConstantVal, hn1abs, absNames_new, h10abs, h9abs, h8abs, h7abs, h5abs,
    h3abs, h1abs, hn2abs, h2abs, h4abs, h6abs, htabs, hcabs, ConLeche.ofReduceRaw,
    ConLeche.BasisDSL.pi, ConLeche.BasisDSL.cnst, ConLeche.BasisDSL.bv,
    ConLeche.BasisDSL.ap3, ConLeche.BasisDSL.ap2, absLevels_new]
  rfl

/-- `ConLeche/Kernel/TrustAxioms.lean:146-148 reduceOpCvA`,
`:137-139` (the `#annotate_pins` command) — `trust_axioms::reduce_op_cv_a`
returns the **raw** pin at the selected operation, which `matchesPin` cannot
tell from the annotated `reduceOpCvA` (`matchesPin_reduceOpCvA`; the module
note has the argument). -/
theorem reduce_op_cv_a_refines {c : name.Name} {cv : env.ConstantVal} (hc : NameWF c)
    (h : trust_axioms.reduce_op_cv_a c = ok cv) :
    absConstantVal cv
        = (if absName c = ConLeche.reduceNatName then
              ConLeche.reduceOpRaw ConLeche.reduceNatName
            else ConLeche.reduceOpRaw ConLeche.reduceBoolName)
      ∧ ConstantValWF cv := by
  rw [trust_axioms.reduce_op_cv_a] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ea, fa⟩ := reduce_nat_name_refines ha
  rw [Name.beq_refines hc fa hb, ea] at h
  by_cases hq : absName c = ConLeche.reduceNatName
  · rw [if_pos hq]
    simp only [hq, decide_true, if_pos] at h
    obtain ⟨habs, hwf⟩ := reduce_op_raw_refines fa h
    exact ⟨by rw [habs, ea], hwf⟩
  · rw [if_neg hq]
    simp only [hq, decide_false, Bool.false_eq_true, if_false] at h
    obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e1, f1⟩ := reduce_bool_name_refines hn1
    obtain ⟨habs, hwf⟩ := reduce_op_raw_refines f1 h
    exact ⟨by rw [habs, e1], hwf⟩

/-- `ConLeche/Kernel/TrustAxioms.lean:150-152 ofReducePinA`, `:141-144` (the
`#annotate_pins` command) — `trust_axioms::of_reduce_pin_a` returns the **raw**
pin an `ofReduce*` axiom is matched against (`matchesPin_ofReducePinA`). -/
theorem of_reduce_pin_a_refines {n : name.Name} {cv : env.ConstantVal} (hn : NameWF n)
    (h : trust_axioms.of_reduce_pin_a n = ok cv) :
    absConstantVal cv
        = (if absName n = ConLeche.ofReduceNatName then
              ConLeche.ofReduceRaw ConLeche.ofReduceNatName
            else ConLeche.ofReduceRaw ConLeche.ofReduceBoolName)
      ∧ ConstantValWF cv := by
  rw [trust_axioms.of_reduce_pin_a] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ea, fa⟩ := of_reduce_nat_name_refines ha
  rw [Name.beq_refines hn fa hb, ea] at h
  by_cases hq : absName n = ConLeche.ofReduceNatName
  · rw [if_pos hq]
    simp only [hq, decide_true, if_pos] at h
    obtain ⟨habs, hwf⟩ := of_reduce_raw_refines fa h
    exact ⟨by rw [habs, ea], hwf⟩
  · rw [if_neg hq]
    simp only [hq, decide_false, Bool.false_eq_true, if_false] at h
    obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e1, f1⟩ := of_reduce_bool_name_refines hn1
    obtain ⟨habs, hwf⟩ := of_reduce_raw_refines f1 h
    exact ⟨by rw [habs, e1], hwf⟩

/-! ## `kernel::trust_pins` — the two hand-pinned identity values

`ConLeche/Kernel/TrustPins.lean` (48 lines, 2 definitions).  Nothing here reads
the compiling environment (con-leche task #273): the pin has been `fun b => b`
on every toolchain that had the opaques, so it is written down once, and these
two lemmas say the port wrote down the same thing. -/

/-- `ConLeche/Kernel/TrustPins.lean:42-43 reduceBoolDeclPin` —
`trust_pins::reduce_bool_decl_pin` refines `reduceBoolDeclPin`,
`fun (b : Bool) => b`. -/
theorem reduce_bool_decl_pin_refines {e : expr.Expr}
    (h : trust_pins.reduce_bool_decl_pin = ok e) :
    absExpr e = ConLeche.reduceBoolDeclPin ∧ ExprWF e := by
  rw [trust_pins.reduce_bool_decl_pin] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rw [basis_builder.bn] at hn
  obtain ⟨a, ha, hmk⟩ := bind_eq_ok_iff.mp hn
  obtain ⟨hnabs, hnwf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [66#u32, 111#u32, 111#u32, 108#u32])
    (by simp [trust_pins.reduce_bool_decl_pin.S]) (by decide)
  obtain ⟨htabs, htwf⟩ := cnst_step hnwf levelsWF_new ht
  obtain ⟨hbabs, hbwf⟩ := bv_step hb
  obtain ⟨habs, hwf⟩ := lm_step htwf hbwf h
  refine ⟨?_, hwf⟩
  rw [habs, htabs, hbabs, hnabs, Name.anonymous_refines ha, absLevels_new]
  rfl

/-- `ConLeche/Kernel/TrustPins.lean:45-46 reduceNatDeclPin` —
`trust_pins::reduce_nat_decl_pin` refines `reduceNatDeclPin`,
`fun (n : Nat) => n`. -/
theorem reduce_nat_decl_pin_refines {e : expr.Expr}
    (h : trust_pins.reduce_nat_decl_pin = ok e) :
    absExpr e = ConLeche.reduceNatDeclPin ∧ ExprWF e := by
  rw [trust_pins.reduce_nat_decl_pin] at h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  rw [basis_builder.bn] at hn
  obtain ⟨a, ha, hmk⟩ := bind_eq_ok_iff.mp hn
  obtain ⟨hnabs, hnwf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [78#u32, 97#u32, 116#u32])
    (by simp [trust_pins.reduce_nat_decl_pin.S]) (by decide)
  obtain ⟨htabs, htwf⟩ := cnst_step hnwf levelsWF_new ht
  obtain ⟨hbabs, hbwf⟩ := bv_step hb
  obtain ⟨habs, hwf⟩ := lm_step htwf hbwf h
  refine ⟨?_, hwf⟩
  rw [habs, htabs, hbabs, hnabs, Name.anonymous_refines ha, absLevels_new]
  rfl

/-! ## The reduce-operation install pin (`TrustAxioms.lean:198-216`) -/

/-- `ConLeche/Kernel/TrustAxioms.lean:200-205 reduceDeclPin` —
`trust_axioms::reduce_decl_pin` refines `reduceDeclPin`: the pinned defining
expression of a reduce operation. -/
theorem reduce_decl_pin_refines {c : name.Name} {e : expr.Expr} (hc : NameWF c)
    (h : trust_axioms.reduce_decl_pin c = ok e) :
    absExpr e = ConLeche.reduceDeclPin (absName c) ∧ ExprWF e := by
  rw [trust_axioms.reduce_decl_pin] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ea, fa⟩ := reduce_nat_name_refines ha
  rw [Name.beq_refines hc fa hb, ea] at h
  rw [ConLeche.reduceDeclPin]
  by_cases hq : absName c = ConLeche.reduceNatName
  · rw [if_pos hq]
    simp only [hq, decide_true, if_pos] at h
    exact reduce_nat_decl_pin_refines h
  · rw [if_neg hq]
    simp only [hq, decide_false, Bool.false_eq_true, if_false] at h
    exact reduce_bool_decl_pin_refines h

/-- `ConLeche/Kernel/TrustAxioms.lean:213-216 reduceCertVar` —
`trust_axioms::reduce_cert_var` refines `reduceCertVar`: the identity
certificate's variable, `fvar 0` at the element type. -/
theorem reduce_cert_var_refines {c : name.Name} {e : expr.Expr} (hc : NameWF c)
    (h : trust_axioms.reduce_cert_var c = ok e) :
    absExpr e = ConLeche.reduceCertVar (absName c) ∧ ExprWF e := by
  rw [trust_axioms.reduce_cert_var] at h
  obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨htabs, htwf⟩ := reduce_elem_ty_refines hc ht
  exact ⟨by rw [Expr.fvar_refines h, htabs]; rfl, ExprWF.fvar htwf h⟩

end ConRon.Refine.TrustAxioms
