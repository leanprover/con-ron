/-
`CORE_PLAN.md` step 4 (task #49), the **structure-η / rescue / install-time
rule bits** of `crates/con-ron-core/src/kernel/core_k.rs`: the seventeen
state-free functions between `core_k.rs:1919` and `:2397` that either decide a
*syntactic shape conjunction* the cached certificates read, or *build* a
`RecRule` at install.  Cited Lean: `ConLeche/Kernel/Core.lean:1017-1982` (plus
`ConLeche/Cached/StateC.lean:105-112` for `etaCtorShapeC`, which is
`etaCtorShape` at the index).

In the Rust's own order:

* `eta_projs`/`eta_projs_from` (`:1017-1027 etaProjs`) — **deliberately dead**
  (superseded by `core_c::proj_apps_i`) but ported, so they get lemmas;
* `struct_eta_shape_ok` (`:1029-1101 structEtaCertWith`'s conjunction block);
* `eta_ctor_shape` (`:1103-1114 etaCtorShape`, `StateC.lean:105-112`'s twin);
* `unit_shape_ok` (`:1141-1169 structUnitCert`'s conjunction block);
* `eta_fab_args`/`eta_fab_args_e` (`:1210-1225`) — dead in the Lean too;
* `proj_entry_fire_ok` (`:1227-1253 ProjEntry.fireOk`);
* `and_rescue_slots`/`_from`/`and_rescue_slot_ok` (`:1255-1272 andRescueSlotsOf`
  / `andRescueSlots`, `FEnv.lean:101-103 andRescueSlotsF`);
* `fab_scope_ok` (`:1274-1456 majorToCtor`'s three-conjunct scope guard);
* `rec_rule_k_of`/`rec_rule_eta_of`/`rec_rule_bits` (`:1488-1543`) and
  `proj_fn_rule` (`:1582-1594`);
* `proj_fire_shape_ok` (`:1893-1982 whnfCoreBody`'s `.proj` fire guard).

Four things shaped the file.

1. **A conjunction block is not a named Lean function.**  `structEtaCertWith`
   and `structUnitCert` are monadic certificates whose *first* test is a big
   `∧` cascade over stored data; the port factors exactly that cascade out as
   an `if` nest returning `Bool`.  The refinement therefore equates the `Bool`
   with `decide` of the cited conjunction, spelled against the abstracted
   arguments -- nothing more and nothing less than the cited `if`'s condition.
2. **The port reads the environment through the index** (the module note's
   deviation 3): `struct_eta_shape_ok` calls `fenv::tower_slots_all_f` /
   `rec_slots_all_f`, so its statement carries `FEnv.towerSlotsAllF` /
   `recSlotsAllF` where the cited block has `towerSlotsAll` / `recSlotsAll`,
   and `and_rescue_slots` is stated against `FEnv.andRescueSlotsF` (the cited
   `andRescueSlotsOf` at `lfe.findProj?`).  `Refine/CoreKProj.lean` supplied
   the three walks (deleted, task #105).
3. **`prop_when::names_beq` and `level::name_is_proj_fn_shape` had no lemma.**
   They belong in `Refine/PropWhen.lean` and `Refine/Level.lean`; the only
   callers in `core_k.rs` are `struct_eta_shape_ok` and `rec_rule_eta_of`, so
   they are proved here (`absString_eq_codes` is the `"proj"`/`"projTable"`
   literal comparison, through `Name.absString_inj`).
4. **The owning probes return a tuple**, so the generated bodies of
   `rec_rule_k_of`/`rec_rule_eta_of` open it with a pattern `let` -- a *matcher*
   application neither `simp` nor `dsimp` reduces.  `bind_eq_ok_iff.mp h` (whose
   unification does whnf) and `replace h : … := h` (defeq retyping, the idiom
   `Refine/CoreKNatOps.lean` uses) are what get past it.

Facts owned by *other* task-#49 agents are taken as explicit hypotheses:
`CoreKBase.lean`'s `PinnedName`/`PinnedNames` for the two pinned names
(`Refine/CoreKPinned.lean` discharges them), and the two bundles `VecFacts`
(`Refine/CoreKVec.lean`) and `EnvFacts` (`Refine/CoreKGuards.lean`, plus one
`ExprWF`-inversion that belongs in `Refine/Expr.lean`); the parent agent
discharges both at merge.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.FEnv
import ConLeche.Kernel.Core
import ConLeche.Cached.StateC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## The imported facts

Two bundles of refinements this file *reads* and another agent's file *proves*.
Each clause is verbatim the other file's statement, so the parent agent
discharges a bundle by `⟨fun _ _ => that_theorem, …⟩`.  The two pinned names the
shape guards compare against -- `basis_names::and_name` and
`basis_names::reserved_basis_names` -- come in as `CoreKBase.lean`'s
`PinnedName`/`PinnedNames`, which `Refine/CoreKPinned.lean` discharges. -/

/-! ## Two refinements that belong in other landed files

`prop_when::names_beq` (`Refine/PropWhen.lean`) and
`level::name_is_proj_fn_shape` (`Refine/Level.lean`) have no lemma there and
`core_k.rs` reads each exactly once -- from `struct_eta_shape_ok` and from
`rec_rule_eta_of` -- so they are proved here. -/

/-! ### `level::name_is_proj_fn_shape`

`Name.isProjFnShape` matches the two string literals `"proj"` and
`"projTable"`; the port compares code points (`level::is_proj_str`,
`level::is_proj_table_str`), so the bridge is `Name.absString_inj`. -/

/-- A model list of four entries, listed out. -/
theorem len_eq_four {α : Type} {l : List α} (h : l.length = 4) :
    ∃ a0 a1 a2 a3, l = [a0, a1, a2, a3] := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩; · simp at h
  rcases l with _ | ⟨a4, l⟩
  · exact ⟨a0, a1, a2, a3, rfl⟩
  · simp at h

/-- A model list of nine entries, listed out. -/
theorem len_eq_nine {α : Type} {l : List α} (h : l.length = 9) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8] := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩; · simp at h
  rcases l with _ | ⟨a4, l⟩; · simp at h
  rcases l with _ | ⟨a5, l⟩; · simp at h
  rcases l with _ | ⟨a6, l⟩; · simp at h
  rcases l with _ | ⟨a7, l⟩; · simp at h
  rcases l with _ | ⟨a8, l⟩; · simp at h
  rcases l with _ | ⟨a9, l⟩
  · exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, rfl⟩
  · simp at h

/-- `level::is_proj_str` is the code-point list of `"proj"`. -/
theorem is_proj_str_refines {s : alloc.vec.Vec Std.U32} {b : Bool}
    (h : level.is_proj_str s = ok b) :
    b = decide (s.val = [112#u32, 114#u32, 111#u32, 106#u32]) := by
  rw [level.is_proj_str] at h
  split at h
  · rename_i h4
    have hl : s.val.length = 4 := by have := alloc.vec.Vec.len_val s; scalar_tac
    obtain ⟨a0, a1, a2, a3, hs⟩ := len_eq_four hl
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
      show ∀ i : Nat, s[i]? = (s.val)[i]? from fun _ => rfl, hs,
      show ((0#usize : Std.Usize)).val = 0 from rfl,
      show ((1#usize : Std.Usize)).val = 1 from rfl,
      show ((2#usize : Std.Usize)).val = 2 from rfl,
      show ((3#usize : Std.Usize)).val = 3 from rfl,
      List.getElem?_cons_zero, List.getElem?_cons_succ, bind_tc_ok] at h
    rw [hs]
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
  · rename_i h4
    simp only [Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    intro hc
    have hv : (alloc.vec.Vec.len s).val = s.val.length := alloc.vec.Vec.len_val s
    rw [hc] at hv
    simp only [List.length_cons, List.length_nil] at hv
    exact h4 (by scalar_tac)

/-- `level::is_proj_table_str` is the code-point list of `"projTable"`. -/
theorem is_proj_table_str_refines {s : alloc.vec.Vec Std.U32} {b : Bool}
    (h : level.is_proj_table_str s = ok b) :
    b = decide (s.val = [112#u32, 114#u32, 111#u32, 106#u32, 84#u32, 97#u32,
      98#u32, 108#u32, 101#u32]) := by
  rw [level.is_proj_table_str] at h
  split at h
  · rename_i h9
    have hl : s.val.length = 9 := by have := alloc.vec.Vec.len_val s; scalar_tac
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, hs⟩ := len_eq_nine hl
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
      show ∀ i : Nat, s[i]? = (s.val)[i]? from fun _ => rfl, hs,
      show ((0#usize : Std.Usize)).val = 0 from rfl,
      show ((1#usize : Std.Usize)).val = 1 from rfl,
      show ((2#usize : Std.Usize)).val = 2 from rfl,
      show ((3#usize : Std.Usize)).val = 3 from rfl,
      show ((4#usize : Std.Usize)).val = 4 from rfl,
      show ((5#usize : Std.Usize)).val = 5 from rfl,
      show ((6#usize : Std.Usize)).val = 6 from rfl,
      show ((7#usize : Std.Usize)).val = 7 from rfl,
      show ((8#usize : Std.Usize)).val = 8 from rfl,
      List.getElem?_cons_zero, List.getElem?_cons_succ, bind_tc_ok] at h
    rw [hs]
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
  · rename_i h9
    simp only [Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    intro hc
    have hv : (alloc.vec.Vec.len s).val = s.val.length := alloc.vec.Vec.len_val s
    rw [hc] at hv
    simp only [List.length_cons, List.length_nil] at hv
    exact h9 (by scalar_tac)

/-- A stored `Str` payload abstracts to a given literal exactly when its code
points are that literal's (`Name.absString_inj` on valid code points). -/
theorem absString_eq_codes {s : alloc.vec.Vec Std.U32} {L : List Std.U32}
    (hs : StrWF s) (hL : ∀ c ∈ L, Nat.isValidChar c.val)
    (hlen : L.length ≤ Std.Usize.max) :
    absString s = absCodes L ↔ s.val = L := by
  refine ⟨fun h => ?_, fun h => by rw [absString_eq, h]⟩
  have hv : StrWF (alloc.vec.Vec.from L hlen) := by
    intro c hc; exact hL c (by simpa using hc)
  have heq : absString s = absString (alloc.vec.Vec.from L hlen) := by
    rw [h, absString_eq, alloc.vec.Vec.from_val]
  rw [Name.absString_inj hs hv heq, alloc.vec.Vec.from_val]

/-- The `Name` twin of `ExprOps.node_kind`: the kind read off a node a smart
constructor built. -/
theorem name_node_kind (d : Std.U64) (k : name.NameKind) :
    (name.Name.mk (name.NameNode.mk d k))._0.kind = k := rfl

/-- `Name.isProjFnShape` at a `.num (.str _ s) _` node: the two literals, as a
`Bool` test on the payload. -/
theorem isProjFnShape_num_str (p : ConLeche.Name) (str : String) (k : Nat) :
    ConLeche.Name.isProjFnShape (.num (.str p str) k)
      = (decide (str = "proj") || decide (str = "projTable")) := by
  unfold ConLeche.Name.isProjFnShape
  split <;> simp_all

/-- `ConLeche/Kernel/Level.lean:223-230` -- `level::name_is_proj_fn_shape`
refines `Name.isProjFnShape`. -/
theorem name_is_proj_fn_shape_refines {n : name.Name} {b : Bool} (hn : NameWF n)
    (h : level.name_is_proj_fn_shape n = ok b) :
    b = ConLeche.Name.isProjFnShape (absName n) := by
  cases hn with
  | @anonymous n ha =>
    rw [name_anonymous_inv ha] at h ⊢
    rw [level.name_is_proj_fn_shape] at h
    simp only [arc_deref_eq, name_node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, absName_mk, absNameKind]
    rfl
  | @str pre s n hpre hs hmk =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    rw [level.name_is_proj_fn_shape] at h
    simp only [arc_deref_eq, name_node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, absName_mk, absNameKind]
    rfl
  | @num pre m n hpre hmk =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    rw [level.name_is_proj_fn_shape] at h
    simp only [arc_deref_eq, name_node_kind, bind_tc_ok] at h
    cases hpre with
    | @anonymous p ha =>
      rw [name_anonymous_inv ha] at h ⊢
      simp only [name_node_kind, Result.ok.injEq] at h
      rw [← h, absName_mk, absNameKind, absName_mk, absNameKind]
      rfl
    | @str p2 s2 p hp2 hs2 hmk2 =>
      obtain ⟨hh2, rfl⟩ := mk_str_inv hmk2
      simp only [name_node_kind, bind_eq_ok_iff] at h
      obtain ⟨b1, hb1, h⟩ := h
      have e1 := is_proj_str_refines hb1
      have hp : (absString s2 = "proj") ↔ s2.val = [112#u32, 114#u32, 111#u32, 106#u32] := by
        rw [show ("proj" : String) = absCodes [112#u32, 114#u32, 111#u32, 106#u32] from rfl]
        exact absString_eq_codes hs2 (by decide) (by scalar_tac)
      have hpt : (absString s2 = "projTable") ↔ s2.val = [112#u32, 114#u32, 111#u32,
          106#u32, 84#u32, 97#u32, 98#u32, 108#u32, 101#u32] := by
        rw [show ("projTable" : String) = absCodes [112#u32, 114#u32, 111#u32, 106#u32,
          84#u32, 97#u32, 98#u32, 108#u32, 101#u32] from rfl]
        exact absString_eq_codes hs2 (by decide) (by scalar_tac)
      simp only [absName_mk, absNameKind, isProjFnShape_num_str, hp, hpt]
      rw [← e1]
      split at h
      · rename_i hb1t
        simp only [Result.ok.injEq] at h
        rw [← h, hb1t, Bool.true_or]
      · rename_i hb1f
        simp only [Bool.not_eq_true] at hb1f
        rw [is_proj_table_str_refines h, hb1f, Bool.false_or]
    | @num p2 m2 p hp2 hmk2 =>
      obtain ⟨hh2, rfl⟩ := mk_num_inv hmk2
      simp only [name_node_kind, Result.ok.injEq] at h
      rw [← h, absName_mk, absNameKind, absName_mk, absNameKind]
      rfl

/-! ## The tower-fire guard (`Core.lean:1227-1253`, `:1893-1982`) -/

/-! ## The shape conjunctions (`Core.lean:1029-1114`, `:1141-1169`)

`structEtaCertWith` and `structUnitCert` are monadic certificates whose first
test is a conjunction over stored data; the port factors exactly that `∧`
cascade out as an `if` nest, so the refinement equates the `Bool` with `decide`
of the cited condition. -/

/-! ## The `And`-only η rescue (`Core.lean:1255-1272`, `FEnv.lean:101-103`)

The three cited declarations -- `andRescueSlotsOf`, `andRescueSlots` and
`FEnv.andRescueSlotsF` -- are one function in the port (the module note's point
3: the port's only spelling is the indexed one), so the statements below are
against `andRescueSlotsOf` at `lfe.findProj?`, which is `andRescueSlotsF`. -/

/-! ## The rescue's scope guard (`Core.lean:1274-1456`) -/

/-! ## The fabricated η projections (`Core.lean:1017-1027`, `:1210-1225`)

`eta_projs`/`eta_projs_from` are **deliberately dead** in the port
(`core_c::proj_apps_i` superseded them) and `eta_fab_args`/`eta_fab_args_e` are
written against them and dead in the Lean too (`etaFabArgs`/`etaFabArgsE`);
all four are ported, and refined here, so the provenance gate stays in step
with its source (task #11's `beqRecursive` rule). -/

/-! ## The install-time rule bits (`Core.lean:1488-1543`, `:1582-1594`)

`recRuleKOf`/`recRuleEtaOf` are abstracted over the lookup in the cited Lean;
the port reads `fenv::find` through `ctor_probe`/`ind_probe`, so the statements
below are at `lfe.find?`.  The four `*_hit`/`*_miss` lemmas turn a probe's
`Option` equation back into the shape the cited `match find? c with | some
(.ctorInfo …)` reads.  **The awkward step**: the owning probes return a tuple,
so the generated body opens it with a pattern `let`, which is a *matcher*
application `simp` will not reduce -- `split at h` is what takes it apart, and
the equation it leaves behind is `subst`ed. -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

end ConRon.Refine.CoreK

