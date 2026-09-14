/-
`kernel::basis_pins` and `kernel::nat_op_pins` (task #56, `CORE_PLAN.md`
step 7).

## What is here

`ConLeche/Kernel/BasisA.lean` is the *annotated* basis, computed while the
module elaborates by `#annotate_basis`.  The port cannot run an elaborator, so
the value is carried as generated Rust source
(`kernel::basis_tables`, task #22) and `Refine/BasisTables.lean` proves that
the generated table **is** `ConLeche.BasisKind.declsA` — which is the only
thing this file needs about it.

Seventeen of the nineteen annotated pins are consumed through
`ConstantVal.matchesPin`, whose type test erases every binder's prop-ness
datum, so the port compares them against the *raw* pins and no table is
involved (task #24's `matchesPin` note).  The remaining two are consumed by an
**exact** `ConstantInfo` equality — `env.find? eqName = some eqA`
(`Kernel/StdAxioms.lean:346`, `Kernel/DeclCheck.lean:243,299,313,744`, …) and
`env.find? natName = some natA` (`Kernel/TrustAxioms.lean:180`,
`Kernel/DeclCheck.lean:290`) — and `kernel/basis_pins.rs` is exactly that
consumer layer: the two pins read off the head of their block, the two
predicates, and the two environment guards.

So the refinement of the six functions is the composition of three facts that
already exist:

* `Refine/BasisTables.lean`'s `basis_decls_a_refines` — the table is
  `BasisKind.declsA`, hence `(declsA .eqK)[0] = eqA` and
  `(declsA .natK)[0] = natA`, which is what `eq_a`/`nat_a` read;
* `Refine/Env.lean`'s `constant_info_beq_refines` — the port's derived
  `ConstantInfo` equality is `decide (· = ·)` on the abstracted constants
  (task #27 checked that the derived structural one is what every kernel site
  spells; `ConstantInfo.canonEq` is the frontend's and never the kernel's);
* `Refine/FEnv.lean`'s `find_refines` — the index probe is `FEnv.find?`.

**The stubs task #24 described are gone.**  That entry says `basis_pins.rs`
answers `false` / the empty block and that task #22 should delete the module.
At the current pin they are *not* stubs: task #27 deleted `basis_pins::decls_a`
(`BasisKind.declsA` is `basis_tables::basis_decls_a`, folded by
`checker::check_basis_decl`) and rewrote the two predicates against the
generated table, and `crates/con-ron-core/tests/basis_install.rs` installs all
six blocks end to end.  What is refined below is therefore the real consumer
layer, not a decline.

## `kernel::nat_op_pins`

Task #24's other stub is also gone, and in a way that moves the statement out
of this file.  `nat_op_pins.rs` declares the `NatOpPinSet` record **and
nothing else** — there is no `nat_op_pin_sets()`: task #31 made the variant
list a *parameter* (Charon OOMs on ~26 500 generated nodes) and task #43 then
embedded it as text in the core, `kernel::pins_text::PINS_TEXT` plus the
verified reader `kernel::pins_decode::decode`.  The record's abstraction
(`absNatOpPinSet`) and the decoder's refinement therefore live in
`Refine/Pins.lean`, and nothing about a table is owed here.

Nothing is owed about the *value* of the decoded list either, since **task
#74**.  Task #43's closed computation
`parsePins (absText PINS_TEXT) = .ok ConLeche.natOpPinSets` was out of the
kernel's reach (a `native_decide` axiom already inside Aeneas's `Str` model, a
reference decoder that does not whnf, and quadratic kernel expansion of a
532 KB literal), task #64 took it by `native_decide`, and this file carried the
corollary about the decoded list, `nat_op_pin_sets_refines`.  The vendored
con-leche makes the pin list an argument of the fold (its task #285), so no
statement anywhere needs the decoded list to *be* `natOpPinSets`:
`pins_closed`, `pins_text_decodes` and `nat_op_pin_sets_refines` are all gone,
and what the tower asks of the embedded pins is only `PinsWF`
(`Refine/PinsWF.lean`'s `decode_embedded_wf`).

Task #58 closed the one `sorry` this file had, `basis_decls_a_wf`; the section
below it says how, and why it is not the second `step` tier task #56 expected.

`sorry` count in this file: 0.
-/
import ConRon.Refine.BasisTables
import ConRon.Refine.BasisNames
import ConRon.Refine.FEnv
import ConRon.Refine.Pins

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel
open ConRon.Refine ConRon.Refine.FEnv

namespace ConRon.Refine.BasisPins

/-! ## The one thing task #22 did not prove about its table

`Refine/BasisTables.lean` proves the table's *value* and deliberately forgets
the hash words (`⦃ _ => True ⦄` on every `mix_hash`), because an equation
between abstractions needs nothing else.  The exact `ConstantInfo` comparison
does need more: `Refine/Env.lean`'s `constant_info_beq_refines` is exact only
on well-formed constants, `ConstantInfoWF` being the inductive-predicate
invariant that pins the stored word.  The table's entries satisfy it — every
node of the generated source is a call to the port's own smart constructor —
and the tier below is that second walk, over all 810 generated nodes.

**It is not a second `step` tier**, which is what task #56's note expected.  A
`⦃ ⦄` specification has to prove that the call *succeeds*, and that is why task
#22 needed the whole `mix_hash`/`str_hash`/`levels_hash`/`level_has_param`
totality tier before it could say anything about a node at all.
Well-formedness is asked of a table we are **given** (`h : basis_decls_a k =
ok v`), so the `ok` equation of every node is already in hand, and DESIGN.md
§3.5's rule — a `*WF` predicate is an *inductive* one whose constructors are
the port's own smart constructors — makes each node's clause literally one
constructor applied to that equation.  Those constructors are already
packaged, one per smart constructor, as `Name.mk_str_wf`, `Level.param_wf`,
`Expr.forall_e_wf`, `PropWhen.if_all_zero_wf` and friends, so nothing new is
proved here: the walk is a *loop*.  `wf_peel` splits one bind off the chain
with `bind_eq_ok_iff` and hands the equation to the first `*_wf` lemma that
fits; `repeat` does it 804 times over the six blocks, and the file elaborates
in 30 s (51 s of CPU: the six are independent).

The one thing that has to be said out loud is **`with_reducible`**.  Without
it the `first` alternation is not merely wasteful but catastrophic: matching
`hx : expr.lam ty b m = ok e` against `expr.dup ?e = ok ?r` at default
transparency unfolds *both* generated bodies and reduces a `lam` node's whole
hash computation before failing, at ~100 s for that one step, so the four
blocks that build a `lam` never finish.  At `reducible` transparency a
mismatch is two distinct constants and fails at once, while the branch that
does fit matches syntactically.  With it the largest block (`.QuotK`, 300 of
the 804 binds) takes 26 s and the rest a few seconds each. -/

/-- Every entry of a pushed vector is well formed if every entry of the vector
pushed onto is and the pushed element is.  `StrWF`, `NamesWF`, `LevelsWF`,
`ExprsWF`, `RecRulesWF` and `ConstantInfosWF` are all this shape, so the six
wrappers below are the same proof. -/
theorem vec_all_push {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  intro y hy
  rw [vec_push_val h] at hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · simp only [List.mem_singleton] at hy; subst hy; exact hx

theorem str_push_wf {v w : alloc.vec.Vec Std.U32} {x : Std.U32}
    (hv : StrWF v) (hx : Nat.isValidChar x.val)
    (h : alloc.vec.Vec.push v x = ok w) : StrWF w := vec_all_push hv hx h

theorem names_push_wf {v w : alloc.vec.Vec name.Name} {x : name.Name}
    (hv : NamesWF v) (hx : NameWF x)
    (h : alloc.vec.Vec.push v x = ok w) : NamesWF w := vec_all_push hv hx h

theorem levels_push_wf {v w : alloc.vec.Vec level.Level} {x : level.Level}
    (hv : LevelsWF v) (hx : LevelWF x)
    (h : alloc.vec.Vec.push v x = ok w) : LevelsWF w := vec_all_push hv hx h

theorem exprs_push_wf {v w : alloc.vec.Vec expr.Expr} {x : expr.Expr}
    (hv : ExprsWF v) (hx : ExprWF x)
    (h : alloc.vec.Vec.push v x = ok w) : ExprsWF w := vec_all_push hv hx h

theorem rules_push_wf {v w : alloc.vec.Vec env.RecRule} {x : env.RecRule}
    (hv : RecRulesWF v) (hx : RecRuleWF x)
    (h : alloc.vec.Vec.push v x = ok w) : RecRulesWF w := vec_all_push hv hx h

theorem infos_push_wf {v w : alloc.vec.Vec env.ConstantInfo} {x : env.ConstantInfo}
    (hv : ConstantInfosWF v) (hx : ConstantInfoWF x)
    (h : alloc.vec.Vec.push v x = ok w) : ConstantInfosWF w := vec_all_push hv hx h

/-! The three `dup`s and `expr::binder_meta` are the identity in the model
(DESIGN.md §3.2), so they transport well-formedness rather than build it; the
`*WF` predicates have no constructor for them. -/

theorem name_dup_wf {n r : name.Name} (hn : NameWF n) (h : name.dup n = ok r) :
    NameWF r := by
  simp only [name_dup_eq, Result.ok.injEq] at h; exact h ▸ hn

theorem level_dup_wf {u r : level.Level} (hu : LevelWF u) (h : level.dup u = ok r) :
    LevelWF r := by
  simp only [level_dup_eq, Result.ok.injEq] at h; exact h ▸ hu

theorem expr_dup_wf {e r : expr.Expr} (he : ExprWF e) (h : expr.dup e = ok r) :
    ExprWF r := by rw [Expr.dup_eq h]; exact he

theorem binder_meta_wf {pw : prop_when.PropWhen} {m : expr.BinderMeta}
    (hpw : PropWhenWF pw) (h : expr.binder_meta pw = ok m) : BinderMetaWF m := by
  simp only [expr.binder_meta, Result.ok.injEq] at h
  subst h; exact hpw

/-! The empty vector, at each of the six element types the tables push onto. -/

theorem str_wf_new : StrWF (alloc.vec.Vec.new Std.U32) := by
  simp [StrWF, alloc.vec.Vec.new]

theorem names_wf_new : NamesWF (alloc.vec.Vec.new name.Name) := by
  simp [NamesWF, alloc.vec.Vec.new]

theorem levels_wf_new : LevelsWF (alloc.vec.Vec.new level.Level) := by
  simp [LevelsWF, alloc.vec.Vec.new]

theorem exprs_wf_new : ExprsWF (alloc.vec.Vec.new expr.Expr) := by
  simp [ExprsWF, alloc.vec.Vec.new]

theorem rules_wf_new : RecRulesWF (alloc.vec.Vec.new env.RecRule) := by
  simp [RecRulesWF, alloc.vec.Vec.new]

theorem infos_wf_new : ConstantInfosWF (alloc.vec.Vec.new env.ConstantInfo) := by
  simp [ConstantInfosWF, alloc.vec.Vec.new]

/-! ### The loop

`wf_elem` discharges the *argument* obligations of a `*_wf` lemma: a
well-formedness fact already in context, one of the six empty vectors, a code
point's `Nat.isValidChar` (`decide`), or — for the `RecRule` and
`ConstantInfo` literals the tables push — the record's conjunction, unfolded
and split into facts that are again in context.  `wf_peel` takes the
hypothesis carrying the rest of the generated `do` chain, splits one bind off
it and applies the smart constructor's `*WF` lemma; the branches are ordered
by how often the tables use them. -/

local syntax "wf_elem" : tactic
local macro_rules
  | `(tactic| wf_elem) => `(tactic|
      first
      | assumption
      | exact str_wf_new
      | exact names_wf_new
      | exact levels_wf_new
      | exact exprs_wf_new
      | exact rules_wf_new
      | exact infos_wf_new
      | exact True.intro
      | decide
      | (simp only [ConstantInfoWF, ConstantValWF, IndCapsWF, RecRuleWF,
            RecRuleFireWF, ProjTableWF]
         repeat' first
           | assumption
           | apply And.intro
           | exact True.intro
           | exact str_wf_new
           | exact names_wf_new
           | exact levels_wf_new
           | exact exprs_wf_new
           | exact rules_wf_new))

local syntax "wf_peel" ident : tactic
local macro_rules
  | `(tactic| wf_peel $h:ident) => `(tactic|
      (obtain ⟨_, hx, $h⟩ := bind_eq_ok_iff.mp $h
       first
       | (with_reducible have := expr_dup_wf (by assumption) hx)
       | (with_reducible have := names_push_wf (by wf_elem) (by wf_elem) hx)
       | (with_reducible have := str_push_wf (by wf_elem) (by wf_elem) hx)
       | (with_reducible have := binder_meta_wf (by assumption) hx)
       | (with_reducible have := Expr.forall_e_wf (by assumption) (by assumption) (by assumption) hx)
       | (with_reducible have := Expr.app_wf (by assumption) (by assumption) hx)
       | (with_reducible have := PropWhen.if_all_zero_wf (by wf_elem) hx)
       | (with_reducible have := name_dup_wf (by assumption) hx)
       | (with_reducible have := Name.mk_str_wf (by assumption) (by wf_elem) hx)
       | (with_reducible have := Expr.lam_wf (by assumption) (by assumption) (by assumption) hx)
       | (with_reducible have := Expr.mk_bvar_wf hx)
       | (with_reducible have := level_dup_wf (by assumption) hx)
       | (with_reducible have := Expr.sort_wf (by assumption) hx)
       | (with_reducible have := Expr.mk_const_wf (by assumption) (by wf_elem) hx)
       | (with_reducible have := Level.param_wf (by assumption) hx)
       | (with_reducible have := PropWhen.never_wf hx)
       | (with_reducible have := Name.anonymous_wf hx)
       | (with_reducible have := Level.zero_wf hx)
       | (with_reducible have := Level.succ_wf (by assumption) hx)
       | (with_reducible have := levels_push_wf (by wf_elem) (by wf_elem) hx)
       | (with_reducible have := exprs_push_wf (by wf_elem) (by wf_elem) hx)
       | (with_reducible have := rules_push_wf (by wf_elem) (by wf_elem) hx)
       | (with_reducible have := infos_push_wf (by wf_elem) (by wf_elem) hx)
       clear hx))

/-- A whole block: peel until the chain is one `Vec::push` long, then read the
last push off.  Every generated table ends by pushing its last
`ConstantInfo`. -/
local syntax "basis_wf_block" ident : tactic
local macro_rules
  | `(tactic| basis_wf_block $h:ident) => `(tactic|
      (repeat wf_peel $h
       exact infos_push_wf (by wf_elem) (by wf_elem) $h))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- `ConLeche/Kernel/BasisA.lean` — the `.FalseK` block's entries are well
formed. -/
theorem basis_decls_false_wf {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_false = ok v) : ConstantInfosWF v := by
  rw [basis_tables.basis_decls_false] at h
  basis_wf_block h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- The `.EmptyK` block's entries are well formed. -/
theorem basis_decls_empty_wf {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_empty = ok v) : ConstantInfosWF v := by
  rw [basis_tables.basis_decls_empty] at h
  basis_wf_block h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- The `.PunitK` block's entries are well formed. -/
theorem basis_decls_punit_wf {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_punit = ok v) : ConstantInfosWF v := by
  rw [basis_tables.basis_decls_punit] at h
  basis_wf_block h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- The `.QuotK` block's entries are well formed. -/
theorem basis_decls_quot_wf {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_quot = ok v) : ConstantInfosWF v := by
  rw [basis_tables.basis_decls_quot] at h
  basis_wf_block h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- The `.NatK` block's entries are well formed. -/
theorem basis_decls_nat_wf {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_nat = ok v) : ConstantInfosWF v := by
  rw [basis_tables.basis_decls_nat] at h
  basis_wf_block h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- The `.EqK` block's entries are well formed. -/
theorem basis_decls_eq_wf {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_eq = ok v) : ConstantInfosWF v := by
  rw [basis_tables.basis_decls_eq] at h
  basis_wf_block h

/-- The generated basis table's entries are well formed, at every kind. -/
theorem basis_decls_a_wf {k : env.BasisKind}
    {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_a k = ok v) : ConstantInfosWF v := by
  rw [basis_tables.basis_decls_a.eq_def] at h
  cases k <;> simp only [] at h
  · exact basis_decls_eq_wf h
  · exact basis_decls_nat_wf h
  · exact basis_decls_punit_wf h
  · exact basis_decls_empty_wf h
  · exact basis_decls_false_wf h
  · exact basis_decls_quot_wf h

/-! ## The two pins -/

/-- `Vec::index` at a literal position, as a `getElem?` fact.  (The copy in
`Refine/ExprOps.lean` is `vec_index_getElem?`; that file is not imported
here.) -/
theorem vec_index_get? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- The head of a basis block: `basis_decls_a k` succeeds, and its first entry
abstracts to the head of `BasisKind.declsA (absBasisKind k)` and is well
formed.  This is the shared body of `eq_a_refines`/`nat_a_refines` — the pins
are read off the table rather than spelled a second time, so the install order
`declsA` fixes is what makes them the right constants. -/
theorem block_head {k : env.BasisKind} {block : alloc.vec.Vec env.ConstantInfo}
    {ci : env.ConstantInfo} (hb : basis_tables.basis_decls_a k = ok block)
    (hi : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice env.ConstantInfo)
      block 0#usize = ok ci) :
    (ConLeche.BasisKind.declsA (absBasisKind k))[0]? = some (absConstantInfo ci) ∧
      ConstantInfoWF ci := by
  obtain ⟨v, hv, habs⟩ := WP.spec_imp_exists (basis_decls_a_refines k)
  rw [hb] at hv
  have hvb : v = block := (Result.ok_injective hv).symm
  subst hvb
  have hg : v.val[0]? = some ci := vec_index_get? hi
  refine ⟨?_, basis_decls_a_wf hb ci (List.mem_of_getElem? hg)⟩
  rw [← habs]
  simp only [absConstantInfos, List.getElem?_map, hg, Option.map_some]

/-- `ConLeche/Kernel/BasisA.lean:29-48` — `basis_pins::eq_a` is `eqA`, the
pinned annotated `Eq` type former: the head of the `.eqK` block
(`BasisKind.declsA .eqK = [eqA, eqReflA, eqRecA]`).  `eqA = eqRaw` is a *fact*
and not an assumption (`crates/.../basis_pins.rs`'s note and its
`eq_a_is_annotated` test); nothing below needs it. -/
theorem eq_a_refines {ci : env.ConstantInfo} (h : basis_pins.eq_a = ok ci) :
    absConstantInfo ci = ConLeche.eqA ∧ ConstantInfoWF ci := by
  rw [basis_pins.eq_a] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨block, hb, ci0, hi, hdup⟩ := h
  have hb' : basis_tables.basis_decls_a env.BasisKind.EqK = ok block := hb
  obtain ⟨hhead, hwf⟩ := block_head hb' hi
  rw [Env.constant_info_dup_refines hdup]
  refine ⟨?_, hwf⟩
  simp only [absBasisKind, ConLeche.BasisKind.declsA] at hhead
  exact (Option.some_inj.mp hhead).symm

/-- `ConLeche/Kernel/BasisA.lean:29-48` — `basis_pins::nat_a` is `natA`, the
head of the `.natK` block
(`BasisKind.declsA .natK = [natA, natZeroA, natSuccA, natRecA]`). -/
theorem nat_a_refines {ci : env.ConstantInfo} (h : basis_pins.nat_a = ok ci) :
    absConstantInfo ci = ConLeche.natA ∧ ConstantInfoWF ci := by
  rw [basis_pins.nat_a] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨block, hb, ci0, hi, hdup⟩ := h
  have hb' : basis_tables.basis_decls_a env.BasisKind.NatK = ok block := hb
  obtain ⟨hhead, hwf⟩ := block_head hb' hi
  rw [Env.constant_info_dup_refines hdup]
  refine ⟨?_, hwf⟩
  simp only [absBasisKind, ConLeche.BasisKind.declsA] at hhead
  exact (Option.some_inj.mp hhead).symm

/-! ## The two predicates

`ConstantInfo`'s equality here is the **derived structural one** — task #27
grepped every kernel site and each spells `==` or `decide (… = some eqA)`;
`ConstantInfo.canonEq` (`Frontend/Export.lean:279`), which canonicalises
level-parameter names, belongs to the frontend alone.  `Refine/Env.lean`'s
`constant_info_beq_refines` is that equality, exactly, on well-formed
constants. -/

/-- `ConLeche/Kernel/BasisA.lean:29-48` — `basis_pins::is_pinned_eq_basis` is
the `some ci = some eqA` half of `env.find? eqName = some eqA`: exactly
`decide (ci = eqA)` on the abstracted stored constant. -/
theorem is_pinned_eq_basis_refines {ci : env.ConstantInfo} {b : Bool}
    (hci : ConstantInfoWF ci) (h : basis_pins.is_pinned_eq_basis ci = ok b) :
    b = decide (absConstantInfo ci = ConLeche.eqA) := by
  rw [basis_pins.is_pinned_eq_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pin, hpin, hbeq⟩ := h
  obtain ⟨habs, hwf⟩ := eq_a_refines hpin
  rw [Env.constant_info_beq_refines hci hwf hbeq, habs]

/-- `ConLeche/Kernel/BasisA.lean:29-48` — the same for `Nat`
(`env.find? natName = some natA`, `reduceElemOk`). -/
theorem is_pinned_nat_basis_refines {ci : env.ConstantInfo} {b : Bool}
    (hci : ConstantInfoWF ci) (h : basis_pins.is_pinned_nat_basis ci = ok b) :
    b = decide (absConstantInfo ci = ConLeche.natA) := by
  rw [basis_pins.is_pinned_nat_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pin, hpin, hbeq⟩ := h
  obtain ⟨habs, hwf⟩ := nat_a_refines hpin
  rw [Env.constant_info_beq_refines hci hwf hbeq, habs]

/-! ## The two environment guards

Stated against the `F`-twin, `FEnv.find?` (task #18's deviation 3: the port
has one environment spelling, the index).  The cited Lean writes the guard
over `Env` at the pure sites and over `FEnv` at the executed ones
(`stdAxiomOk` / `stdAxiomOkF`, `reduceElemOk` / `reduceElemOkF`); the two
agree by `FEnvRel`'s first clause, `absEnv fe.env = lfe.env`. -/

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk` /
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
**"the pinned `Eq` basis is installed, unmodified"**:
`basis_pins::eq_basis_pinned` is exactly `decide (find? eqName = some eqA)`.
The `None` arm is exact too: `decide (none = some eqA)` is `false`. -/
theorem eq_basis_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (h : basis_pins.eq_basis_pinned fe = ok b) :
    b = decide (lfe.find? ConLeche.eqName = some ConLeche.eqA) := by
  rw [basis_pins.eq_basis_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, hfind, h⟩ := h
  obtain ⟨hname, hnwf⟩ := BasisNames.eq_name_refines hn
  have hf := find_refines hrel hwf hnwf hfind
  rw [hname] at hf
  cases o with
  | none =>
    simp only [Option.map_none] at hf
    rw [← hf]
    simp only [Result.ok.injEq] at h
    simp [← h]
  | some ci =>
    simp only [Option.map_some] at hf
    rw [← hf, is_pinned_eq_basis_refines (find_wf hwf hnwf hfind ci rfl) h]
    simp

/-- `ConLeche/Kernel/TrustAxioms.lean:177-184 reduceElemOk` /
`ConLeche/Kernel/DeclCheck.lean:288-294 reduceElemOkF` — the same for `Nat`:
the element inductive an `ofReduceNat` axiom needs. -/
theorem nat_basis_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (h : basis_pins.nat_basis_pinned fe = ok b) :
    b = decide (lfe.find? ConLeche.natName = some ConLeche.natA) := by
  rw [basis_pins.nat_basis_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, hfind, h⟩ := h
  obtain ⟨hname, hnwf⟩ := BasisNames.nat_name_refines hn
  have hf := find_refines hrel hwf hnwf hfind
  rw [hname] at hf
  cases o with
  | none =>
    simp only [Option.map_none] at hf
    rw [← hf]
    simp only [Result.ok.injEq] at h
    simp [← h]
  | some ci =>
    simp only [Option.map_some] at hf
    rw [← hf, is_pinned_nat_basis_refines (find_wf hwf hnwf hfind ci rfl) h]
    simp

/-! ## `kernel::nat_op_pins`

The module declares the `NatOpPinSet` record and nothing else (the module
note, and DESIGN.md tasks #31/#43); its abstraction is `Refine/Pins.lean`'s
`absNatOpPinSet`, reused here and not redefined.  Nothing stands where
`nat_op_pin_sets()` would have stood: since **task #74** the tower is stated at
the abstract pin list, so there is no statement to make about the decoded
list's value, and `nat_op_pin_sets_refines` — this file's copy of task #64's
`check_decls_pins_refines`, which read the embedded text through
`pins_text_decodes` — is deleted with it.  `Refine/Pins.lean`'s
`pins_decode_refines` is what remains about the decoder, and
`Refine/PinsWF.lean`'s `decode_embedded_wf` is what the capstones use. -/

end ConRon.Refine.BasisPins
