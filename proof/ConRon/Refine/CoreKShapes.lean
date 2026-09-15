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
   `andRescueSlotsOf` at `lfe.findProj?`).  `Refine/CoreKProj.lean` supplies
   the three walks.
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
import ConRon.Refine.CoreKProj
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

/-- The three `Vec` helpers of `core_k.rs` the η spine and the scope guard use
(`Refine/CoreKVec.lean`). -/
structure VecFacts : Prop where
  exprSingleton : ∀ {e r}, ExprWF e → core_k.expr_singleton e = ok r →
    absExprs r = [absExpr e] ∧ ExprsWF r
  appendExprs : ∀ {xs ys r}, ExprsWF xs → ExprsWF ys →
    core_k.append_exprs xs ys = ok r → absExprs r = absExprs xs ++ absExprs ys ∧ ExprsWF r
  fvarLeavesSubset : ∀ {xs ys b}, ExprOps.LeavesWF xs → ExprOps.LeavesWF ys →
    core_k.fvar_leaves_subset xs ys = ok b →
    b = (ExprOps.absLeaves xs).all (fun l => (ExprOps.absLeaves ys).contains l)

/-- The two `env` copies and the two owning probes (`Refine/CoreKGuards.lean`,
whose `ctorOf`/`indOf` are re-declared here because the bundle must state them
without importing that file). -/
structure EnvFacts : Prop where
  levelsCopy : ∀ {us r}, env.levels_copy us = ok r → r.val = us.val
  exprsCopy : ∀ {es r}, env.exprs_copy es = ok r → r.val = es.val
  ctorProbe : ∀ {fe lfe n o}, FindAgree fe lfe → FindWF fe → NameWF n →
    core_k.ctor_probe fe n = ok o →
    o.map (fun t => (absConstantVal t.1, t.2.1.val, t.2.2.val))
        = (match lfe.find? (absName n) with
           | some (.ctorInfo cv nP nF) => some (cv, nP, nF) | _ => none) ∧
      ∀ cv nP nF, o = some (cv, nP, nF) → ConstantValWF cv
  indProbe : ∀ {fe lfe n o}, FindAgree fe lfe → FindWF fe → NameWF n →
    core_k.ind_probe fe n = ok o →
    o.map (fun t => (absConstantVal t.1, absIndCaps t.2))
        = (match lfe.find? (absName n) with
           | some (.indInfo cv c) => some (cv, c) | _ => none) ∧
      ∀ cv c, o = some (cv, c) → ConstantValWF cv ∧ IndCapsWF c
  constWF : ∀ {e : expr.Expr}, ExprWF e → ∀ {d : Std.U64} {n : name.Name}
    {us : alloc.vec.Vec level.Level}, e = .mk (.mk d (.Const n us)) →
    NameWF n ∧ LevelsWF us


/-! ## Two refinements that belong in other landed files

`prop_when::names_beq` (`Refine/PropWhen.lean`) and
`level::name_is_proj_fn_shape` (`Refine/Level.lean`) have no lemma there and
`core_k.rs` reads each exactly once -- from `struct_eta_shape_ok` and from
`rec_rule_eta_of` -- so they are proved here. -/

/-- `absNames` is injective on well-formed name vectors: `absName` is
(`Name.absName_injective`) and `List.map` preserves it. -/
theorem map_absName_inj : ∀ (l m : List name.Name),
    (∀ n ∈ l, NameWF n) → (∀ n ∈ m, NameWF n) →
    l.map absName = m.map absName → l = m := by
  intro l
  induction l with
  | nil => intro m _ _ h; cases m with | nil => rfl | cons b m => simp at h
  | cons a l ih =>
    intro m hl hm h
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hab : a = b :=
        Name.absName_injective (hl a (by simp)) (hm b (by simp)) h.1
      rw [hab, ih m (fun n hn => hl n (by simp [hn])) (fun n hn => hm n (by simp [hn])) h.2]

/-- `ConLeche/Kernel/PropWhen.lean:324` -- `prop_when::names_beq` decides
equality of the abstracted level-parameter lists, **exactly** (the cited use is
`cvc.levelParams = cvT.levelParams`). -/
theorem names_beq_refines {ps qs : alloc.vec.Vec name.Name} {b : Bool}
    (hps : NamesWF ps) (hqs : NamesWF qs)
    (h : prop_when.names_beq ps qs = ok b) :
    b = decide (absNames ps = absNames qs) := by
  rw [prop_when.names_beq] at h
  have hc := PropWhen.names_beq_from_refines hps hqs ps.length 0#usize b (by scalar_tac) h
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hc
  have hiff : absNames ps = absNames qs ↔ ps.val = qs.val := by
    refine ⟨fun heq => map_absName_inj _ _ hps hqs heq, fun heq => ?_⟩
    rw [absNames, absNames, heq]
  have : b = true ↔ absNames ps = absNames qs := hc.trans hiff.symm
  cases b <;> simp_all

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
    simp only [expr_view_eq, arc_deref_eq, name_node_kind, ron.node.ExprView.ofKind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, absName_mk, absNameKind]
    rfl
  | @str pre s n hpre hs hmk =>
    obtain ⟨hh, rfl⟩ := mk_str_inv hmk
    rw [level.name_is_proj_fn_shape] at h
    simp only [expr_view_eq, arc_deref_eq, name_node_kind, ron.node.ExprView.ofKind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, absName_mk, absNameKind]
    rfl
  | @num pre m n hpre hmk =>
    obtain ⟨hh, rfl⟩ := mk_num_inv hmk
    rw [level.name_is_proj_fn_shape] at h
    simp only [expr_view_eq, arc_deref_eq, name_node_kind, ron.node.ExprView.ofKind, bind_tc_ok] at h
    cases hpre with
    | @anonymous p ha =>
      rw [name_anonymous_inv ha] at h ⊢
      simp only [name_node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
      rw [← h, absName_mk, absNameKind, absName_mk, absNameKind]
      rfl
    | @str p2 s2 p hp2 hs2 hmk2 =>
      obtain ⟨hh2, rfl⟩ := mk_str_inv hmk2
      simp only [name_node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
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
      simp only [name_node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
      rw [← h, absName_mk, absNameKind, absName_mk, absNameKind]
      rfl

/-! ## The tower-fire guard (`Core.lean:1227-1253`, `:1893-1982`) -/

/-- `ConLeche/Kernel/Core.lean:1227-1253` -- `core_k::proj_entry_fire_ok`
refines `ProjEntry.fireOk`: at a `Prop`-declared structure the field's guard
level must be a proposition at this instantiation, elsewhere the rule fires
unconditionally.  The port's `match … Some true / Some false / None` triple is
the cited `== some true`. -/
theorem proj_entry_fire_ok_refines {entry : env.ProjEntry}
    {us : alloc.vec.Vec level.Level} {b : Bool}
    (he : ProjEntryWF entry) (hus : LevelsWF us)
    (h : core_k.proj_entry_fire_ok entry us = ok b) :
    b = (absProjEntry entry).fireOk (absLevels us) := by
  obtain ⟨-, hlp, -, -, hfs, hss⟩ := he
  rw [core_k.proj_entry_fire_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨l, hl, o, ho, sp, hsp, h⟩ := h
  have hlwf : LevelWF l := LevelWF.zero hl
  have hlz : absLevel l = (.zero : ConLeche.Level) := Level.zero_refines hl
  have hoabs : ConLeche.Level.isEquiv (absLevel entry.struct_sort) .zero = o := by
    rw [← hlz]; exact Level.is_equiv_refines hss hlwf ho
  have hspv : sp = decide (o = some true) := by
    cases o with
    | none => simpa using hsp.symm
    | some c => cases c <;> simpa using hsp.symm
  subst hspv
  have hstruct : (absProjEntry entry).structSort = absLevel entry.struct_sort := rfl
  rw [ConLeche.ProjEntry.fireOk, hstruct, hoabs]
  by_cases ho' : o = some true
  · rw [ho']
    simp only [ho', decide_true, if_true, bind_eq_ok_iff] at h
    obtain ⟨fs, hfsok, o1, ho1, h⟩ := h
    obtain ⟨hfsabs, hfswf⟩ := Level.subst_refines hfs hlp hus hfsok
    have ho1abs : ConLeche.Level.isEquiv
        (ConLeche.Level.subst (absNames entry.level_params) (absLevels us)
          (absLevel entry.field_sort)) .zero = o1 := by
      rw [← hlz, absNames, absLevels, ← hfsabs]
      exact Level.is_equiv_refines hfswf hlwf ho1
    have hfield : (absProjEntry entry).fieldSort = absLevel entry.field_sort := rfl
    have hlps : (absProjEntry entry).levelParams = absNames entry.level_params := rfl
    rw [hfield, hlps, ho1abs]
    cases o1 with
    | none => simp_all
    | some c1 => cases c1 <;> simp_all
  · simp only [ho', decide_false, Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]
    cases o with
    | none => simp
    | some c =>
      cases c with
      | false => simp
      | true => exact absurd rfl ho'

/-- `ConLeche/Kernel/Core.lean:1893-1982` -- `core_k::proj_fire_shape_ok`
refines the five-conjunct fire guard of `whnfCoreBody`'s `.proj` arm (the head
is the entry's constructor, the index is in range, the spine is parameters plus
fields, the level count matches, the possibly-`Prop` guard passes). -/
theorem proj_fire_shape_ok_refines {entry : env.ProjEntry} {c : name.Name} {i : Std.U64}
    {us : alloc.vec.Vec level.Level} {args : alloc.vec.Vec expr.Expr} {b : Bool}
    (he : ProjEntryWF entry) (hc : NameWF c) (hus : LevelsWF us)
    (h : core_k.proj_fire_shape_ok entry c i us args = ok b) :
    b = decide (absName c = (absProjEntry entry).ctor ∧
      i.val < (absProjEntry entry).numFields ∧
      (absExprs args).length
        = (absProjEntry entry).numParams + (absProjEntry entry).numFields ∧
      (absLevels us).length = (absProjEntry entry).levelParams.length ∧
      (absProjEntry entry).fireOk (absLevels us) = true) := by
  have hargs : (absExprs args).length = args.val.length := by simp [absExprs]
  have husl : (absLevels us).length = us.val.length := by simp [absLevels]
  have e1 : (absProjEntry entry).ctor = absName entry.ctor := rfl
  have e2 : (absProjEntry entry).numFields = entry.num_fields.val := rfl
  have e3 : (absProjEntry entry).numParams = entry.num_params.val := rfl
  have e4 : (absProjEntry entry).levelParams.length = entry.level_params.val.length := by
    simp [absProjEntry, absNames]
  simp only [e1, e2, e3, e4, hargs, husl]
  rw [core_k.proj_fire_shape_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨bc, hbc, h⟩ := h
  have hbcabs := Name.beq_refines hc he.2.2.1 hbc
  split at h
  · rename_i hbct
    rw [hbct] at hbcabs
    have hce : absName c = absName entry.ctor := by simpa using hbcabs.symm
    split at h
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine (decide_eq_false ?_).symm
      rintro ⟨-, hlt, -, -, -⟩
      exact absurd hlt (by scalar_tac)
    · rename_i hge
      have hlt : i.val < entry.num_fields.val := by scalar_tac
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨n3, hn3, h⟩ := h
      have hn3v : n3.val = entry.num_params.val + entry.num_fields.val :=
        HashMap.uscalar_add_eq hn3
      have hcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len args) : Std.U64).val
          = args.val.length := by
        rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      split at h
      · rename_i hne
        simp only [bne_iff_ne, ne_eq] at hne
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine (decide_eq_false ?_).symm
        rintro ⟨-, -, hlen, -, -⟩
        exact hne (by scalar_tac)
      · rename_i hne
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
        have hlen : args.val.length = entry.num_params.val + entry.num_fields.val := by
          rw [← hcast, hne, hn3v]
        split at h
        · rename_i hne2
          simp only [bne_iff_ne, ne_eq] at hne2
          simp only [Result.ok.injEq] at h
          rw [← h]
          refine (decide_eq_false ?_).symm
          rintro ⟨-, -, -, hlen2, -⟩
          refine hne2 ?_
          have h1 := alloc.vec.Vec.len_val us
          have h2 := alloc.vec.Vec.len_val entry.level_params
          scalar_tac
        · rename_i hne2
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne2
          have hlen2 : us.val.length = entry.level_params.val.length := by
            have h1 := alloc.vec.Vec.len_val us
            have h2 := alloc.vec.Vec.len_val entry.level_params
            scalar_tac
          rw [proj_entry_fire_ok_refines he hus h]
          simp [hce, hlt, hlen, hlen2]
  · rename_i hbct
    simp only [Bool.not_eq_true] at hbct
    rw [hbct] at hbcabs
    simp only [Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    rintro ⟨hce, -, -, -, -⟩
    exact absurd hce (by simpa using hbcabs.symm)

/-! ## The shape conjunctions (`Core.lean:1029-1114`, `:1141-1169`)

`structEtaCertWith` and `structUnitCert` are monadic certificates whose first
test is a conjunction over stored data; the port factors exactly that `∧`
cascade out as an `if` nest, so the refinement equates the `Bool` with `decide`
of the cited condition. -/

/-- A node is its own `data`/`kind` pair -- what `EnvFacts.constWF` is stated
against, from a `split`'s kind equation. -/
theorem expr_node_eta (e : expr.Expr) : e = .mk (.mk e._0.data e._0.kind) := by
  cases e with | mk nd => cases nd with | mk d k => rfl

/-- `absExpr` read off the observed kind -- the direction a `split` on a port
`match` needs (`Refine/CoreKSupport.lean` has the same fact as `absExpr_kind`;
this copy carries a name that cannot clash with it at merge). -/
theorem absExpr_node_kind (e : expr.Expr) : absExpr e = absExprKind e._0.kind := by
  cases e with | mk nd => cases nd with | mk d k => rfl

/-- `ConLeche/Cached/StateC.lean:105-112` -- `core_k::eta_ctor_shape` refines
`etaCtorShapeC`, which is `Core.lean:1103-1114 etaCtorShape` at the index (the
module note's deviation 3): the candidate's head is a stored constructor
applied to exactly its parameters and fields. -/
theorem eta_ctor_shape_refines (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) {a : expr.Expr} {b : Bool} (ha : ExprWF a)
    (h : core_k.eta_ctor_shape fe a = ok b) :
    b = ConLeche.Cached.etaCtorShapeC lfe (absExpr a) := by
  rw [core_k.eta_ctor_shape] at h
  simp only [bind_eq_ok_iff, expr_view_eq, arc_deref_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨f, hf, h⟩ := h
  obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines ha hf
  rw [ConLeche.Cached.etaCtorShapeC, ← hfabs, absExpr_node_kind f]
  split at h
  all_goals rename_i hk
  all_goals of_kind_inv hk
  all_goals rw [hk]
  all_goals simp only [absExprKind]
  case h_4 cn cus =>
    have hfeq : f = .mk (.mk f._0.data (.Const cn cus)) := by
      rw [← hk]; exact expr_node_eta f
    obtain ⟨hcnwf, -⟩ := henv.constWF hfwf hfeq
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    cases o with
    | none =>
      rw [hrel.find_none hcnwf ho]
      simp only [Result.ok.injEq] at h
      rw [← h]
    | some ci =>
      rw [hrel.find_some hcnwf ho]
      cases ci with
      | CtorInfo cv cn_p cn_f =>
        simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
        obtain ⟨v, hv, n2, hn2, h⟩ := h
        obtain ⟨hvabs, -⟩ := ExprOps.get_app_args_refines ha hv
        have hn2v : n2.val = cn_p.val + cn_f.val := HashMap.uscalar_add_eq hn2
        have hcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len v) : Std.U64).val
            = v.val.length := by
          rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
        rw [← h, ← hvabs]
        simp only [absConstantInfo, absExprs, List.length_map]
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq, beq_iff_eq]
        constructor
        · intro hx; rw [← hcast, hx, hn2v]
        · intro hx
          refine Std.UScalar.val_eq_imp_iff.mpr ?_
          rw [hcast, hn2v]; exact hx
      | AxiomInfo _ | DefnInfo _ _ _ | ThmInfo _ _ | IndInfo _ _ | RecInfo _ _ _ _
      | ProjInfo _ =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        simp only [absConstantInfo]
  all_goals (simp only [Result.ok.injEq] at h; rw [← h])

/-- `ConLeche/Kernel/Core.lean:1141-1169` -- `core_k::unit_shape_ok` refines
`structUnitCert`'s conjunction block: the unit-like capability, the name not
reserved, the parameter count and the level count. -/
theorem unit_shape_ok_refines
    (hres : PinnedNames basis_names.reserved_basis_names ConLeche.reservedBasisNames)
    {t : name.Name} {us2 : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {cvt : env.ConstantVal} {caps : env.IndCaps} {b : Bool}
    (ht : NameWF t) (h : core_k.unit_shape_ok t us2 targs cvt caps = ok b) :
    b = decide ((absIndCaps caps).unitlike = true ∧
      ConLeche.reservedBasisNames.contains (absName t) = false ∧
      (absExprs targs).length = (absIndCaps caps).unitParams ∧
      (absLevels us2).length = (absConstantVal cvt).levelParams.length) := by
  rw [core_k.unit_shape_ok] at h
  split at h
  · rename_i hu
    simp only [bind_eq_ok_iff] at h
    obtain ⟨v, hv, cb, hcb, h⟩ := h
    obtain ⟨hvabs, hvwf⟩ := hres v hv
    have hcbabs : cb = ConLeche.reservedBasisNames.contains (absName t) := by
      rw [Name.contains_refines hvwf ht hcb, hvabs]
    split at h
    · rename_i hct
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine (decide_eq_false ?_).symm
      rintro ⟨-, hB, -, -⟩
      rw [← hcbabs, hct] at hB
      exact absurd hB (by simp)
    · rename_i hct
      simp only [Bool.not_eq_true] at hct
      have hB : ConLeche.reservedBasisNames.contains (absName t) = false := by
        rw [← hcbabs]; exact hct
      have hcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len targs) : Std.U64).val
          = targs.val.length := by
        rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
      split at h
      · rename_i hne
        simp only [bne_iff_ne, ne_eq] at hne
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine (decide_eq_false ?_).symm
        rintro ⟨-, -, hC, -⟩
        have hC' : (absExprs targs).length = caps.unit_params.val := hC
        simp only [absExprs, List.length_map] at hC'
        exact hne (by scalar_tac)
      · rename_i hne
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
        have hC : (absExprs targs).length = (absIndCaps caps).unitParams := by
          show (absExprs targs).length = caps.unit_params.val
          simp only [absExprs, List.length_map]
          rw [← hcast, hne]
        simp only [Result.ok.injEq] at h
        rw [← h, decide_eq_decide]
        have h1 := alloc.vec.Vec.len_val us2
        have h2 := alloc.vec.Vec.len_val cvt.level_params
        constructor
        · intro hx
          refine ⟨hu, hB, hC, ?_⟩
          show (absLevels us2).length = (absNames cvt.level_params).length
          simp only [absLevels, absNames, List.length_map]
          scalar_tac
        · rintro ⟨-, -, -, hD⟩
          have hD' : (absLevels us2).length = (absNames cvt.level_params).length := hD
          simp only [absLevels, absNames, List.length_map] at hD'
          scalar_tac
  · rename_i hu
    simp only [Bool.not_eq_true] at hu
    simp only [Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    rintro ⟨hA, -, -, -⟩
    have hA' : caps.unitlike = true := hA
    rw [hu] at hA'
    exact absurd hA' (by simp)

/-- `ConLeche/Kernel/Core.lean:1029-1101` -- `core_k::struct_eta_shape_ok`
refines `structEtaCertWith`'s conjunction block: the η capability and its
constructor, neither name reserved, the parameter count, the level count, the
constructor's own level parameters, and the one-kind slot discipline.  The port
reads the slot discipline through the index (`FEnv.towerSlotsAllF` /
`recSlotsAllF`, `Refine/CoreKProj.lean`) where the cited block has
`towerSlotsAll` / `recSlotsAll`. -/
theorem struct_eta_shape_ok_refines
    (hres : PinnedNames basis_names.reserved_basis_names ConLeche.reservedBasisNames)
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    {c t : name.Name} {us2 : alloc.vec.Vec level.Level}
    {targs : alloc.vec.Vec expr.Expr} {cvc cvt : env.ConstantVal}
    {caps : env.IndCaps} {b : Bool}
    (hc : NameWF c) (ht : NameWF t) (hcvc : ConstantValWF cvc) (hcvt : ConstantValWF cvt)
    (hcaps : IndCapsWF caps)
    (h : core_k.struct_eta_shape_ok fe c us2 targs cvc cvt caps t = ok b) :
    b = decide ((absIndCaps caps).eta = true ∧
      (absIndCaps caps).etaCtor = absName c ∧
      ConLeche.reservedBasisNames.contains (absName t) = false ∧
      ConLeche.reservedBasisNames.contains (absName c) = false ∧
      (absExprs targs).length = (absIndCaps caps).etaParams ∧
      (absLevels us2).length = (absConstantVal cvt).levelParams.length ∧
      (absConstantVal cvc).levelParams = (absConstantVal cvt).levelParams ∧
      (lfe.towerSlotsAllF (absName t) (absIndCaps caps).etaFields ||
        lfe.recSlotsAllF (absName t) (absIndCaps caps).etaFields) = true) := by
  rw [core_k.struct_eta_shape_ok] at h
  split at h
  case isFalse hu =>
    simp only [Bool.not_eq_true] at hu
    simp only [Result.ok.injEq] at h
    rw [← h]
    refine (decide_eq_false ?_).symm
    rintro ⟨hA, -, -, -, -, -, -, -⟩
    have hA' : caps.eta = true := hA
    rw [hu] at hA'
    exact absurd hA' (by simp)
  case isTrue hu =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨bc, hbc, h⟩ := h
    have hbcabs := Name.beq_refines hcaps.1 hc hbc
    split at h
    case isFalse hbct =>
      simp only [Bool.not_eq_true] at hbct
      rw [hbct] at hbcabs
      simp only [Result.ok.injEq] at h
      rw [← h]
      refine (decide_eq_false ?_).symm
      rintro ⟨-, hB, -, -, -, -, -, -⟩
      have hB' : absName caps.eta_ctor = absName c := hB
      exact absurd hB' (by simpa using hbcabs.symm)
    case isTrue hbct =>
      rw [hbct] at hbcabs
      have hB : absName caps.eta_ctor = absName c := by simpa using hbcabs.symm
      simp only [bind_eq_ok_iff] at h
      obtain ⟨v, hv, cbt, hcbt, h⟩ := h
      obtain ⟨hvabs, hvwf⟩ := hres v hv
      have hcbtabs : cbt = ConLeche.reservedBasisNames.contains (absName t) := by
        rw [Name.contains_refines hvwf ht hcbt, hvabs]
      split at h
      case isTrue hct =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine (decide_eq_false ?_).symm
        rintro ⟨-, -, hC, -, -, -, -, -⟩
        rw [← hcbtabs, hct] at hC
        exact absurd hC (by simp)
      case isFalse hct =>
        simp only [Bool.not_eq_true] at hct
        have hC : ConLeche.reservedBasisNames.contains (absName t) = false := by
          rw [← hcbtabs]; exact hct
        simp only [bind_eq_ok_iff] at h
        obtain ⟨cbc, hcbc, h⟩ := h
        have hcbcabs : cbc = ConLeche.reservedBasisNames.contains (absName c) := by
          rw [Name.contains_refines hvwf hc hcbc, hvabs]
        split at h
        case isTrue hcc =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          refine (decide_eq_false ?_).symm
          rintro ⟨-, -, -, hD, -, -, -, -⟩
          rw [← hcbcabs, hcc] at hD
          exact absurd hD (by simp)
        case isFalse hcc =>
          simp only [Bool.not_eq_true] at hcc
          have hD : ConLeche.reservedBasisNames.contains (absName c) = false := by
            rw [← hcbcabs]; exact hcc
          have hcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len targs) : Std.U64).val
              = targs.val.length := by
            rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
          simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
          split at h
          case isTrue hne =>
            simp only [bne_iff_ne, ne_eq] at hne
            simp only [Result.ok.injEq] at h
            rw [← h]
            refine (decide_eq_false ?_).symm
            rintro ⟨-, -, -, -, hE, -, -, -⟩
            have hE' : (absExprs targs).length = caps.eta_params.val := hE
            simp only [absExprs, List.length_map] at hE'
            exact hne (by scalar_tac)
          case isFalse hne =>
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
            have hE : (absExprs targs).length = (absIndCaps caps).etaParams := by
              show (absExprs targs).length = caps.eta_params.val
              simp only [absExprs, List.length_map]
              rw [← hcast, hne]
            have h1 := alloc.vec.Vec.len_val us2
            have h2 := alloc.vec.Vec.len_val cvt.level_params
            split at h
            case isTrue hne2 =>
              simp only [bne_iff_ne, ne_eq] at hne2
              simp only [Result.ok.injEq] at h
              rw [← h]
              refine (decide_eq_false ?_).symm
              rintro ⟨-, -, -, -, -, hF, -, -⟩
              have hF' : (absLevels us2).length
                  = (absNames cvt.level_params).length := hF
              simp only [absLevels, absNames, List.length_map] at hF'
              exact hne2 (by scalar_tac)
            case isFalse hne2 =>
              simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne2
              have hF : (absLevels us2).length
                  = (absConstantVal cvt).levelParams.length := by
                show (absLevels us2).length = (absNames cvt.level_params).length
                simp only [absLevels, absNames, List.length_map]
                scalar_tac
              simp only [bind_eq_ok_iff] at h
              obtain ⟨bl, hbl, h⟩ := h
              have hblabs := names_beq_refines hcvc.2.1 hcvt.2.1 hbl
              split at h
              case isFalse hblt =>
                simp only [Bool.not_eq_true] at hblt
                rw [hblt] at hblabs
                simp only [Result.ok.injEq] at h
                rw [← h]
                refine (decide_eq_false ?_).symm
                rintro ⟨-, -, -, -, -, -, hG, -⟩
                have hG' : absNames cvc.level_params = absNames cvt.level_params := hG
                exact absurd hG' (by simpa using hblabs.symm)
              case isTrue hblt =>
                rw [hblt] at hblabs
                have hG : (absConstantVal cvc).levelParams
                    = (absConstantVal cvt).levelParams := by
                  show absNames cvc.level_params = absNames cvt.level_params
                  simpa using hblabs.symm
                simp only [bind_eq_ok_iff] at h
                obtain ⟨bt, hbt, h⟩ := h
                have hbtabs := tower_slots_all_f_refines hrel hwf ht hbt
                have htow : lfe.towerSlotsAllF (absName t) caps.eta_fields.val = bt :=
                  hbtabs.symm
                split at h
                case isTrue hbtt =>
                  simp only [Result.ok.injEq] at h
                  rw [← h]
                  refine (decide_eq_true ?_).symm
                  refine ⟨hu, hB, hC, hD, hE, hF, hG, ?_⟩
                  show (lfe.towerSlotsAllF (absName t) caps.eta_fields.val ||
                    lfe.recSlotsAllF (absName t) caps.eta_fields.val) = true
                  rw [htow, hbtt, Bool.true_or]
                case isFalse hbtt =>
                  simp only [Bool.not_eq_true] at hbtt
                  rw [rec_slots_all_f_refines hrel ht h]
                  by_cases hr : lfe.recSlotsAllF (absName t) caps.eta_fields.val = true
                  · rw [hr]
                    refine (decide_eq_true ?_).symm
                    refine ⟨hu, hB, hC, hD, hE, hF, hG, ?_⟩
                    show (lfe.towerSlotsAllF (absName t) caps.eta_fields.val ||
                      lfe.recSlotsAllF (absName t) caps.eta_fields.val) = true
                    rw [hr, Bool.or_true]
                  · simp only [Bool.not_eq_true] at hr
                    rw [hr]
                    refine (decide_eq_false ?_).symm
                    rintro ⟨-, -, -, -, -, -, -, hx⟩
                    have hx' : (lfe.towerSlotsAllF (absName t) caps.eta_fields.val ||
                        lfe.recSlotsAllF (absName t) caps.eta_fields.val) = true := hx
                    rw [htow, hbtt, hr] at hx'
                    simp at hx'

/-! ## The `And`-only η rescue (`Core.lean:1255-1272`, `FEnv.lean:101-103`)

The three cited declarations -- `andRescueSlotsOf`, `andRescueSlots` and
`FEnv.andRescueSlotsF` -- are one function in the port (the module note's point
3: the port's only spelling is the indexed one), so the statements below are
against `andRescueSlotsOf` at `lfe.findProj?`, which is `andRescueSlotsF`. -/

/-- The cited per-slot body of `andRescueSlotsOf`, as a function of the
lookup. -/
def andSlotOk (findProj? : ConLeche.Name → Nat → Option ConLeche.ProjEntry)
    (ctor : ConLeche.Name) (nP : Nat) (ust : List ConLeche.Level) (j : Nat) : Bool :=
  match findProj? ConLeche.andName j with
  | some e => e.ctor == ctor && e.numParams == nP && e.numFields == 2 && e.fireOk ust
  | none => false

/-- `ConLeche/Kernel/Core.lean:1255-1268` -- `core_k::and_rescue_slot_ok`
refines the per-slot test of `andRescueSlotsOf` (task #14's per-element rule:
the entry's borrow dies inside the callee). -/
theorem and_rescue_slot_ok_refines
    (hand : PinnedName basis_names.and_name ConLeche.andName)
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    {ctor : name.Name} {n_p j : Std.U64} {ust : alloc.vec.Vec level.Level} {b : Bool}
    (hctor : NameWF ctor) (hust : LevelsWF ust)
    (h : core_k.and_rescue_slot_ok fe ctor n_p ust j = ok b) :
    b = andSlotOk lfe.findProj? (absName ctor) n_p.val (absLevels ust) j.val := by
  rw [core_k.and_rescue_slot_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨an, han, o, ho, h⟩ := h
  obtain ⟨hanabs, hanwf⟩ := hand an han
  obtain ⟨hoabs, howf⟩ := find_proj_refines hrel hwf hanwf ho
  rw [andSlotOk, ← hanabs, ← hoabs]
  cases o with
  | none =>
    simp only [Option.map_none]
    simp only [Result.ok.injEq] at h
    rw [← h]
  | some pe =>
    have hpewf := howf pe rfl
    simp only [Option.map_some]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨bc, hbc, h⟩ := h
    have hbcabs := Name.beq_refines hpewf.2.2.1 hctor hbc
    split at h
    case isTrue hbct =>
      rw [hbct] at hbcabs
      have hq1 : ((absProjEntry pe).ctor == absName ctor) = true := by
        show ((absName pe.ctor : ConLeche.Name) == absName ctor) = true
        simpa using hbcabs.symm
      split at h
      case isTrue hne =>
        simp only [bne_iff_ne, ne_eq] at hne
        simp only [Result.ok.injEq] at h
        rw [← h]
        have hq2 : ((absProjEntry pe).numParams == n_p.val) = false := by
          show ((pe.num_params.val : Nat) == n_p.val) = false
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro hc
          exact hne (Std.UScalar.val_eq_imp_iff.mpr hc)
        rw [hq2]
        simp
      case isFalse hne =>
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
        have hq2 : ((absProjEntry pe).numParams == n_p.val) = true := by
          show ((pe.num_params.val : Nat) == n_p.val) = true
          simp only [beq_iff_eq]
          rw [hne]
        split at h
        case isTrue hnf =>
          simp only [bne_iff_ne, ne_eq] at hnf
          simp only [Result.ok.injEq] at h
          rw [← h]
          have hq3 : ((absProjEntry pe).numFields == 2) = false := by
            show ((pe.num_fields.val : Nat) == 2) = false
            simp only [beq_eq_false_iff_ne, ne_eq]
            intro hc
            exact hnf (Std.UScalar.val_eq_imp_iff.mpr (by rw [hc]; rfl))
          rw [hq3]
          simp
        case isFalse hnf =>
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hnf
          have hq3 : ((absProjEntry pe).numFields == 2) = true := by
            show ((pe.num_fields.val : Nat) == 2) = true
            simp only [beq_iff_eq]
            rw [hnf]; rfl
          rw [proj_entry_fire_ok_refines hpewf hust h, hq1, hq2, hq3]
          simp
    case isFalse hbct =>
      simp only [Bool.not_eq_true] at hbct
      rw [hbct] at hbcabs
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hq1 : ((absProjEntry pe).ctor == absName ctor) = false := by
        show ((absName pe.ctor : ConLeche.Name) == absName ctor) = false
        simpa using hbcabs.symm
      rw [hq1]
      simp

/-- `ConLeche/Kernel/Core.lean:1255-1268` -- the index recursion behind
`and_rescue_slots`, the cited `(List.range 2).all`. -/
theorem and_rescue_slots_from_refines
    (hand : PinnedName basis_names.and_name ConLeche.andName)
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    {ctor : name.Name} {n_p : Std.U64} {ust : alloc.vec.Vec level.Level}
    (hctor : NameWF ctor) (hust : LevelsWF ust) (N : Nat) :
    ∀ (j : Std.U64) (b : Bool), 2 - j.val = N →
      core_k.and_rescue_slots_from fe ctor n_p ust j = ok b →
      b = ((List.range' j.val (2 - j.val)).all
            (andSlotOk lfe.findProj? (absName ctor) n_p.val (absLevels ust))) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro j b hN h
    rw [core_k.and_rescue_slots_from.eq_def] at h
    split at h
    · rename_i hge
      have : 2 - j.val = 0 := by scalar_tac
      rw [this]
      simp only [List.range'_zero, List.all_nil]
      exact (Result.ok_injective h).symm
    · rename_i hge
      have hlt : j.val < 2 := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hc, h⟩ := h
      have hcabs := and_rescue_slot_ok_refines hand hrel hwf hctor hust hc
      have hcons : 2 - j.val = (2 - (j.val + 1)) + 1 := by omega
      rw [hcons, List.range'_succ, List.all_cons, ← hcabs]
      split at h
      · rename_i hbt
        simp only [bind_eq_ok_iff] at h
        obtain ⟨j2, hj2, hrec⟩ := h
        have hj2v : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
        rw [ih (2 - j2.val) (by omega) j2 b (by omega) hrec, hj2v]
        simp only [hbt, Bool.true_and]
      · rename_i hbt
        simp only [Bool.not_eq_true] at hbt
        rw [hbt]
        simp only [Bool.false_and]
        exact (Result.ok_injective h).symm

/-- `ConLeche/Kernel/FEnv.lean:101-103` -- `core_k::and_rescue_slots` refines
`FEnv.andRescueSlotsF`, i.e. `Core.lean:1255-1272 andRescueSlotsOf` /
`andRescueSlots` at the index: the two tower entries of the pinned `And` are
stored, name the rule's constructor at the major's parameter count, and their
`Prop` guards pass at `ust`. -/
theorem and_rescue_slots_refines
    (hand : PinnedName basis_names.and_name ConLeche.andName)
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    {ctor : name.Name} {n_p : Std.U64} {ust : alloc.vec.Vec level.Level} {b : Bool}
    (hctor : NameWF ctor) (hust : LevelsWF ust)
    (h : core_k.and_rescue_slots fe ctor n_p ust = ok b) :
    b = lfe.andRescueSlotsF (absName ctor) n_p.val (absLevels ust) := by
  rw [core_k.and_rescue_slots] at h
  rw [and_rescue_slots_from_refines hand hrel hwf hctor hust _ 0#u64 b rfl h]
  simp only [ConLeche.FEnv.andRescueSlotsF, ConLeche.andRescueSlotsOf,
    List.range_eq_range', show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero]
  rfl

/-! ## The rescue's scope guard (`Core.lean:1274-1456`) -/

/-- `ConLeche/Kernel/Core.lean:1274-1456` -- `core_k::fab_scope_ok` refines the
three-conjunct scope guard all three `majorToCtor` branches run on their
fabrication: well-scoped at the ambient depth, closed under loose `bvar`s, and
introducing no free variable the major does not already have. -/
theorem fab_scope_ok_refines (hvec : VecFacts) {fab major : expr.Expr}
    {depth : Std.U64} {b : Bool} (hfab : ExprWF fab) (hmajor : ExprWF major)
    (h : core_k.fab_scope_ok fab major depth = ok b) :
    b = ((absExpr fab).wscopedB depth.val && (absExpr fab).looseBVarsBounded 0 &&
      (absExpr fab).fvarLeaves.all (fun l => (absExpr major).fvarLeaves.contains l)) := by
  rw [core_k.fab_scope_ok] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b1, hb1, h⟩ := h
  have hb1abs := ExprOps.wscoped_b_refines hfab hb1
  split at h
  case isFalse hb1f =>
    simp only [Bool.not_eq_true] at hb1f
    rw [hb1f] at hb1abs
    simp only [Result.ok.injEq] at h
    rw [← h, ← hb1abs]
    simp
  case isTrue hb1t =>
    rw [hb1t] at hb1abs
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b2, hb2, h⟩ := h
    have hb2abs := ExprOps.loose_bvars_bounded_refines hfab hb2
    simp only [show ((0#u64 : Std.U64)).val = 0 from rfl] at hb2abs
    split at h
    case isFalse hb2f =>
      simp only [Bool.not_eq_true] at hb2f
      rw [hb2f] at hb2abs
      simp only [Result.ok.injEq] at h
      rw [← h, ← hb1abs, ← hb2abs]
      simp
    case isTrue hb2t =>
      rw [hb2t] at hb2abs
      simp only [bind_eq_ok_iff] at h
      obtain ⟨xs, hxs, ys, hys, h⟩ := h
      obtain ⟨hxsabs, hxswf⟩ := ExprOps.fvar_leaves_refines hfab hxs
      obtain ⟨hysabs, hyswf⟩ := ExprOps.fvar_leaves_refines hmajor hys
      rw [hvec.fvarLeavesSubset hxswf hyswf h, hxsabs, hysabs,
        ← hb1abs, ← hb2abs]
      simp

/-! ## The fabricated η projections (`Core.lean:1017-1027`, `:1210-1225`)

`eta_projs`/`eta_projs_from` are **deliberately dead** in the port
(`core_c::proj_apps_i` superseded them) and `eta_fab_args`/`eta_fab_args_e` are
written against them and dead in the Lean too (`etaFabArgs`/`etaFabArgsE`);
all four are ported, and refined here, so the provenance gate stays in step
with its source (task #11's `beqRecursive` rule). -/

/-- The cited `etaProjs` body's per-slot expression, at a slot kind the caller
has already decided (the port's `eta_projs_from` takes the `Bool`). -/
def etaProjAt (tower : Bool) (T : ConLeche.Name) (us : List ConLeche.Level)
    (targs : List ConLeche.Expr) (b : ConLeche.Expr) (j : Nat) : ConLeche.Expr :=
  if tower then .proj T j b
  else ConLeche.Expr.mkAppN (.const (ConLeche.projFnName T j) us) (targs ++ [b])

/-- `ConLeche/Kernel/Core.lean:1017-1027` -- the index recursion behind
`eta_projs`, i.e. the cited `(List.range nF).map` at a decided slot kind. -/
theorem eta_projs_from_refines (hvec : VecFacts) (henv : EnvFacts)
    {t : name.Name} {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {b : expr.Expr} (ht : NameWF t) (hus : LevelsWF us) (htargs : ExprsWF targs)
    (hb : ExprWF b) (tower : Bool) (N : Nat) :
    ∀ (n_f j : Std.U64) (out r : alloc.vec.Vec expr.Expr), n_f.val - j.val = N →
      ExprsWF out →
      core_k.eta_projs_from tower t us targs b n_f j out = ok r →
      absExprs r = absExprs out ++ (List.range' j.val (n_f.val - j.val)).map
          (etaProjAt tower (absName t) (absLevels us) (absExprs targs) (absExpr b))
        ∧ ExprsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n_f j out r hN hout h
    rw [core_k.eta_projs_from.eq_def] at h
    split at h
    · rename_i hge
      have hz : n_f.val - j.val = 0 := by scalar_tac
      rw [hz, ← Result.ok_injective h]
      exact ⟨by simp, hout⟩
    · rename_i hge
      have hlt : j.val < n_f.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨out1, hout1, i2, hi2, hrec⟩ := h
      have hi2v : i2.val = j.val + 1 := HashMap.uscalar_add_eq hi2
      have key : absExprs out1 = absExprs out ++
          [etaProjAt tower (absName t) (absLevels us) (absExprs targs) (absExpr b) j.val]
          ∧ ExprsWF out1 := by
        split at hout1
        · rename_i htw
          simp only [bind_eq_ok_iff, name_dup_eq, expr_dup_eq, Result.ok.injEq,
            exists_eq_left'] at hout1
          obtain ⟨e1, he1, hpush⟩ := hout1
          refine ⟨?_, ExprOps.exprsWF_push hout (Expr.proj_wf ht hb he1) hpush⟩
          rw [ExprOps.absExprs_push hpush, Expr.proj_refines he1, etaProjAt, if_pos htw]
        · rename_i htw
          simp only [Bool.not_eq_true] at htw
          simp only [bind_eq_ok_iff] at hout1
          obtain ⟨v, hv, v1, hv1, spine, hspine, n, hn, v2, hv2, e, he, e1, he1, hpush⟩ :=
            hout1
          have hvv : v.val = targs.val := henv.exprsCopy hv
          have hvwf : ExprsWF v := fun x hx => htargs x (by rw [← hvv]; exact hx)
          have hvabs : absExprs v = absExprs targs := by rw [absExprs, absExprs, hvv]
          obtain ⟨hv1abs, hv1wf⟩ := hvec.exprSingleton hb hv1
          obtain ⟨hspabs, hspwf⟩ := hvec.appendExprs hvwf hv1wf hspine
          obtain ⟨hnabs, hnwf⟩ := proj_fn_name_refines ht hn
          have hv2v : v2.val = us.val := henv.levelsCopy hv2
          have hv2wf : LevelsWF v2 := fun x hx => hus x (by rw [← hv2v]; exact hx)
          have hv2abs : absLevels v2 = absLevels us := by rw [absLevels, absLevels, hv2v]
          have hewf : ExprWF e := Expr.mk_const_wf hnwf hv2wf he
          obtain ⟨he1abs, he1wf⟩ := ExprOps.mk_app_n_refines hewf hspwf he1
          refine ⟨?_, ExprOps.exprsWF_push hout he1wf hpush⟩
          rw [ExprOps.absExprs_push hpush, he1abs, Expr.mk_const_refines he, hnabs,
            hv2abs, hspabs, hvabs, hv1abs, etaProjAt, if_neg (by simp [htw])]
      obtain ⟨habs, hrwf⟩ :=
        ih (n_f.val - i2.val) (by omega) n_f i2 out1 r rfl key.2 hrec
      refine ⟨?_, hrwf⟩
      rw [habs, key.1, hi2v]
      have hcons : n_f.val - j.val = (n_f.val - (j.val + 1)) + 1 := by omega
      rw [hcons, List.range'_succ, List.map_cons]
      simp

/-- `ConLeche/Kernel/Core.lean:1017-1027` -- `core_k::eta_projs` refines
`etaProjs`: `.proj T j b` nodes at an all-tower slot family, the modeled path's
projection-function applications otherwise.  The cited `towerSlotsAll env` is
read through the index (`FEnv.towerSlotsAllF`). -/
theorem eta_projs_refines (hvec : VecFacts) (henv : EnvFacts) {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    {t : name.Name} {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {b : expr.Expr} {n_f : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (ht : NameWF t) (hus : LevelsWF us) (htargs : ExprsWF targs) (hb : ExprWF b)
    (h : core_k.eta_projs fe t us targs b n_f = ok r) :
    absExprs r = (if lfe.towerSlotsAllF (absName t) n_f.val then
        (List.range n_f.val).map fun j => ConLeche.Expr.proj (absName t) j (absExpr b)
      else
        (List.range n_f.val).map fun j =>
          ConLeche.Expr.mkAppN (.const (ConLeche.projFnName (absName t) j) (absLevels us))
            (absExprs targs ++ [absExpr b])) ∧ ExprsWF r := by
  rw [core_k.eta_projs] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨tower, htow, h⟩ := h
  have htowabs := tower_slots_all_f_refines hrel hwf ht htow
  obtain ⟨habs, hrwf⟩ := eta_projs_from_refines hvec henv ht hus htargs hb tower _
    n_f 0#u64 _ r rfl ExprOps.exprsWF_new h
  refine ⟨?_, hrwf⟩
  rw [habs, ← htowabs]
  simp only [ExprOps.absExprs_new, List.nil_append,
    show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero, List.range_eq_range']
  cases tower <;> simp [etaProjAt]

/-- `ConLeche/Kernel/Core.lean:1210-1218` -- `core_k::eta_fab_args` refines
`etaFabArgs` (dead in both: `etaFabArgsE` is what `majorToCtor` uses). -/
theorem eta_fab_args_refines (hvec : VecFacts) (henv : EnvFacts)
    {t : name.Name} {ust : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {major : expr.Expr} {n_f : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (ht : NameWF t) (hust : LevelsWF ust) (htargs : ExprsWF targs) (hmajor : ExprWF major)
    (h : core_k.eta_fab_args t ust targs major n_f = ok r) :
    absExprs r = absExprs targs ++ (List.range n_f.val).map (fun j =>
        ConLeche.Expr.mkAppN (.const (ConLeche.projFnName (absName t) j) (absLevels ust))
          (absExprs targs ++ [absExpr major])) ∧ ExprsWF r := by
  rw [core_k.eta_fab_args] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨projs, hprojs, v, hv, happ⟩ := h
  obtain ⟨hpabs, hpwf⟩ := eta_projs_from_refines hvec henv ht hust htargs hmajor false _
    n_f 0#u64 _ projs rfl ExprOps.exprsWF_new hprojs
  have hvv : v.val = targs.val := henv.exprsCopy hv
  have hvwf : ExprsWF v := fun x hx => htargs x (by rw [← hvv]; exact hx)
  have hvabs : absExprs v = absExprs targs := by rw [absExprs, absExprs, hvv]
  obtain ⟨hrabs, hrwf⟩ := hvec.appendExprs hvwf hpwf happ
  refine ⟨?_, hrwf⟩
  rw [hrabs, hvabs, hpabs]
  simp only [ExprOps.absExprs_new, List.nil_append,
    show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero, List.range_eq_range']
  simp [etaProjAt]

/-- `ConLeche/Kernel/Core.lean:1220-1225` -- `core_k::eta_fab_args_e` refines
`etaFabArgsE`: `eta_fab_args` at the entry kind. -/
theorem eta_fab_args_e_refines (hvec : VecFacts) (henv : EnvFacts) {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} (hrel : FindAgree fe lfe) (hwf : FindWF fe)
    {t : name.Name} {ust : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {major : expr.Expr} {n_f : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (ht : NameWF t) (hust : LevelsWF ust) (htargs : ExprsWF targs) (hmajor : ExprWF major)
    (h : core_k.eta_fab_args_e fe t ust targs major n_f = ok r) :
    absExprs r = absExprs targs ++
        (if lfe.towerSlotsAllF (absName t) n_f.val then
          (List.range n_f.val).map fun j => ConLeche.Expr.proj (absName t) j (absExpr major)
        else
          (List.range n_f.val).map fun j =>
            ConLeche.Expr.mkAppN (.const (ConLeche.projFnName (absName t) j) (absLevels ust))
              (absExprs targs ++ [absExpr major])) ∧ ExprsWF r := by
  rw [core_k.eta_fab_args_e] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨projs, hprojs, v, hv, happ⟩ := h
  obtain ⟨hpabs, hpwf⟩ :=
    eta_projs_refines hvec henv hrel hwf ht hust htargs hmajor hprojs
  have hvv : v.val = targs.val := henv.exprsCopy hv
  have hvwf : ExprsWF v := fun x hx => htargs x (by rw [← hvv]; exact hx)
  have hvabs : absExprs v = absExprs targs := by rw [absExprs, absExprs, hvv]
  obtain ⟨hrabs, hrwf⟩ := hvec.appendExprs hvwf hpwf happ
  exact ⟨by rw [hrabs, hvabs, hpabs], hrwf⟩

/-! ## The install-time rule bits (`Core.lean:1488-1543`, `:1582-1594`)

`recRuleKOf`/`recRuleEtaOf` are abstracted over the lookup in the cited Lean;
the port reads `fenv::find` through `ctor_probe`/`ind_probe`, so the statements
below are at `lfe.find?`.  The four `*_hit`/`*_miss` lemmas turn a probe's
`Option` equation back into the shape the cited `match find? c with | some
(.ctorInfo …)` reads.  **The awkward step**: the owning probes return a tuple,
so the generated body opens it with a pattern `let`, which is a *matcher*
application `simp` will not reduce -- `split at h` is what takes it apart, and
the equation it leaves behind is `subst`ed. -/

/-- `ctor_probe` hit: the cited `some (.ctorInfo cvj _ cnF)` arm is the one the
lookup takes. -/
theorem ctor_probe_hit (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} {cv : env.ConstantVal} {nP nF : Std.U64}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.ctor_probe fe n = ok (some (cv, nP, nF))) :
    lfe.find? (absName n) = some (.ctorInfo (absConstantVal cv) nP.val nF.val)
      ∧ ConstantValWF cv := by
  obtain ⟨habs, hcvwf⟩ := henv.ctorProbe hrel hwf hn h
  refine ⟨?_, hcvwf cv nP nF rfl⟩
  simp only [Option.map_some] at habs
  cases hl : lfe.find? (absName n) with
  | none => rw [hl] at habs; simp at habs
  | some ci =>
    rw [hl] at habs
    cases ci with
    | ctorInfo cv1 p1 f1 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at habs
      obtain ⟨h1, h2, h3⟩ := habs
      rw [h1, h2, h3]
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | recInfo _ _ _ _
    | projInfo _ => simp at habs

/-- `ctor_probe` miss: no stored constructor of that name. -/
theorem ctor_probe_miss (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} (hrel : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.ctor_probe fe n = ok none) :
    ∀ cv nP nF, lfe.find? (absName n) ≠ some (.ctorInfo cv nP nF) := by
  obtain ⟨habs, -⟩ := henv.ctorProbe hrel hwf hn h
  simp only [Option.map_none] at habs
  intro cv nP nF hc
  rw [hc] at habs
  simp at habs

/-- `ind_probe` hit. -/
theorem ind_probe_hit (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} {cv : env.ConstantVal} {caps : env.IndCaps}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.ind_probe fe n = ok (some (cv, caps))) :
    lfe.find? (absName n) = some (.indInfo (absConstantVal cv) (absIndCaps caps))
      ∧ ConstantValWF cv ∧ IndCapsWF caps := by
  obtain ⟨habs, hcwf⟩ := henv.indProbe hrel hwf hn h
  refine ⟨?_, (hcwf cv caps rfl).1, (hcwf cv caps rfl).2⟩
  simp only [Option.map_some] at habs
  cases hl : lfe.find? (absName n) with
  | none => rw [hl] at habs; simp at habs
  | some ci =>
    rw [hl] at habs
    cases ci with
    | indInfo cv1 c1 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at habs
      obtain ⟨h1, h2⟩ := habs
      rw [h1, h2]
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
    | projInfo _ => simp at habs

/-- `ind_probe` miss. -/
theorem ind_probe_miss (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} (hrel : FindAgree fe lfe) (hwf : FindWF fe) (hn : NameWF n)
    (h : core_k.ind_probe fe n = ok none) :
    ∀ cv caps, lfe.find? (absName n) ≠ some (.indInfo cv caps) := by
  obtain ⟨habs, -⟩ := henv.indProbe hrel hwf hn h
  simp only [Option.map_none] at habs
  intro cv caps hc
  rw [hc] at habs
  simp at habs

/-- `ConLeche/Kernel/Core.lean:1488-1503` -- `core_k::rec_rule_k_of` refines
`recRuleKOf` at `lfe.find?`: **the K bit at install** -- the rule's constructor
has no fields and belongs to an inductive stored with the K capability. -/
theorem rec_rule_k_of_refines (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) {ctor : name.Name} {b : Bool}
    (hctor : NameWF ctor) (h : core_k.rec_rule_k_of fe ctor = ok b) :
    b = ConLeche.recRuleKOf lfe.find? (absName ctor) := by
  rw [core_k.rec_rule_k_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  rw [ConLeche.recRuleKOf]
  cases o with
  | none =>
    have hnot := ctor_probe_miss henv hrel hwf hctor ho
    simp only [Result.ok.injEq] at h
    rw [← h]
    cases hl : lfe.find? (absName ctor) with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo cv1 p1 f1 => exact absurd hl (hnot cv1 p1 f1)
      | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | recInfo _ _ _ _
      | projInfo _ => rfl
  | some p =>
    obtain ⟨cv, nP, nF⟩ := p
    obtain ⟨hfind, hcvwf⟩ := ctor_probe_hit henv hrel hwf hctor ho
    rw [hfind]
    dsimp only
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    simp only [bind_eq_ok_iff, expr_view_eq, arc_deref_eq, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨f, hf, h⟩ := h
    obtain ⟨hresabs, hreswf⟩ := ExprOps.pi_result_refines hcvwf.2.2 hres
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines hreswf hf
    rw [show (absConstantVal cv).type = absExpr cv.ty from rfl, ← hresabs, ← hfabs,
      absExpr_node_kind f]
    split at h
    all_goals rename_i hk
    all_goals of_kind_inv hk
    all_goals rw [hk]
    all_goals simp only [absExprKind]
    case h_4 tn tus =>
      have hfeq : f = .mk (.mk f._0.data (.Const tn tus)) := by
        rw [← hk]; exact expr_node_eta f
      obtain ⟨htnwf, -⟩ := henv.constWF hfwf hfeq
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o2, ho2, h⟩ := h
      cases o2 with
      | none =>
        have hnot2 := ind_probe_miss henv hrel hwf htnwf ho2
        simp only [Result.ok.injEq] at h
        rw [← h]
        cases hl : lfe.find? (absName tn) with
        | none => rfl
        | some ci =>
          cases ci with
          | indInfo cv1 c1 => exact absurd hl (hnot2 cv1 c1)
          | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | ctorInfo _ _ _
          | recInfo _ _ _ _ | projInfo _ => rfl
      | some p2 =>
        obtain ⟨cvt, caps⟩ := p2
        obtain ⟨hfind2, -, -⟩ := ind_probe_hit henv hrel hwf htnwf ho2
        rw [hfind2]
        dsimp only
        replace h : (if caps.rule_k = true then ok (decide (nF = 0#u64)) else ok false)
            = ok b := h
        split at h
        · rename_i hrk
          simp only [Result.ok.injEq] at h
          rw [← h]
          show decide (nF = 0#u64) = (caps.rule_k && (nF.val == 0))
          rw [hrk, Bool.true_and, Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, beq_iff_eq]
          constructor
          · intro hx; rw [hx]; rfl
          · intro hx; exact Std.UScalar.val_eq_imp_iff.mpr (by rw [hx]; rfl)
        · rename_i hrk
          simp only [Bool.not_eq_true] at hrk
          simp only [Result.ok.injEq] at h
          rw [← h]
          show false = (caps.rule_k && (nF.val == 0))
          rw [hrk, Bool.false_and]
    all_goals (simp only [Result.ok.injEq] at h; rw [← h])

/-- `ConLeche/Kernel/Core.lean:1505-1531` -- `core_k::rec_rule_eta_of` refines
`recRuleEtaOf` at `lfe.find?`: **the η-rescue bit at install** -- the rule's
constructor is the η constructor of a stored η-capable inductive, carries that
inductive's own level parameters, and the recursor is not itself a projection
function. -/
theorem rec_rule_eta_of_refines (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) {rec_name ctor : name.Name} {b : Bool}
    (hrec : NameWF rec_name) (hctor : NameWF ctor)
    (h : core_k.rec_rule_eta_of fe rec_name ctor = ok b) :
    b = ConLeche.recRuleEtaOf lfe.find? (absName rec_name) (absName ctor) := by
  rw [core_k.rec_rule_eta_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  rw [ConLeche.recRuleEtaOf]
  cases o with
  | none =>
    have hnot := ctor_probe_miss henv hrel hwf hctor ho
    simp only [Result.ok.injEq] at h
    rw [← h]
    cases hl : lfe.find? (absName ctor) with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo cv1 p1 f1 => exact absurd hl (hnot cv1 p1 f1)
      | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | recInfo _ _ _ _
      | projInfo _ => rfl
  | some p =>
    obtain ⟨cv, nP, nF⟩ := p
    obtain ⟨hfind, hcvwf⟩ := ctor_probe_hit henv hrel hwf hctor ho
    rw [hfind]
    dsimp only
    obtain ⟨res, hres, h⟩ := bind_eq_ok_iff.mp h
    simp only [bind_eq_ok_iff, expr_view_eq, arc_deref_eq, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨f, hf, h⟩ := h
    obtain ⟨hresabs, hreswf⟩ := ExprOps.pi_result_refines hcvwf.2.2 hres
    obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines hreswf hf
    rw [show (absConstantVal cv).type = absExpr cv.ty from rfl, ← hresabs, ← hfabs,
      absExpr_node_kind f]
    split at h
    all_goals rename_i hk
    all_goals of_kind_inv hk
    all_goals rw [hk]
    all_goals simp only [absExprKind]
    case h_4 tn tus =>
      have hfeq : f = .mk (.mk f._0.data (.Const tn tus)) := by
        rw [← hk]; exact expr_node_eta f
      obtain ⟨htnwf, -⟩ := henv.constWF hfwf hfeq
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o2, ho2, h⟩ := h
      cases o2 with
      | none =>
        have hnot2 := ind_probe_miss henv hrel hwf htnwf ho2
        simp only [Result.ok.injEq] at h
        rw [← h]
        cases hl : lfe.find? (absName tn) with
        | none => rfl
        | some ci =>
          cases ci with
          | indInfo cv1 c1 => exact absurd hl (hnot2 cv1 c1)
          | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | ctorInfo _ _ _
          | recInfo _ _ _ _ | projInfo _ => rfl
      | some p2 =>
        obtain ⟨cvt, caps⟩ := p2
        obtain ⟨hfind2, hcvtwf, hcapswf⟩ := ind_probe_hit henv hrel hwf htnwf ho2
        rw [hfind2]
        dsimp only
        show b = (caps.eta && ((absName caps.eta_ctor : ConLeche.Name) == absName ctor) &&
          !(absName rec_name).isProjFnShape &&
          ((absNames cv.level_params : List ConLeche.Name) == absNames cvt.level_params))
        replace h : (if caps.eta = true then
            (do let bc ← name.beq caps.eta_ctor ctor
                if bc = true then
                  (do let bp ← level.name_is_proj_fn_shape rec_name
                      if bp = true then ok false
                      else prop_when.names_beq cv.level_params cvt.level_params)
                else ok false)
          else ok false) = ok b := h
        split at h
        · rename_i heta
          rw [heta, Bool.true_and]
          simp only [bind_eq_ok_iff] at h
          obtain ⟨bc, hbc, h⟩ := h
          have hbcabs := Name.beq_refines hcapswf.1 hctor hbc
          split at h
          · rename_i hbct
            rw [hbct] at hbcabs
            have hq : ((absName caps.eta_ctor : ConLeche.Name) == absName ctor) = true := by
              simpa using hbcabs.symm
            rw [hq, Bool.true_and]
            simp only [bind_eq_ok_iff] at h
            obtain ⟨bp, hbp, h⟩ := h
            have hbpabs := name_is_proj_fn_shape_refines hrec hbp
            split at h
            · rename_i hbpt
              rw [hbpt] at hbpabs
              simp only [Result.ok.injEq] at h
              rw [← h, ← hbpabs]
              simp
            · rename_i hbpt
              simp only [Bool.not_eq_true] at hbpt
              rw [hbpt] at hbpabs
              rw [← hbpabs, Bool.not_false, Bool.true_and,
                names_beq_refines hcvwf.2.1 hcvtwf.2.1 h]
              cases hcc : (absNames cv.level_params == absNames cvt.level_params) with
              | true => exact decide_eq_true (eq_of_beq hcc)
              | false => exact decide_eq_false (ne_of_beq_false hcc)
          · rename_i hbct
            simp only [Bool.not_eq_true] at hbct
            rw [hbct] at hbcabs
            simp only [Result.ok.injEq] at h
            rw [← h]
            have hq : ((absName caps.eta_ctor : ConLeche.Name) == absName ctor) = false := by
              simpa using hbcabs.symm
            rw [hq]
            simp
        · rename_i heta
          simp only [Bool.not_eq_true] at heta
          simp only [Result.ok.injEq] at h
          rw [← h, heta]
          simp
    all_goals (simp only [Result.ok.injEq] at h; rw [← h])

/-- `ConLeche/Kernel/Core.lean:1533-1543` -- `core_k::rec_rule_bits` refines
`recRuleBits`: the one place the K and η-rescue conditions are decided.  This
one *builds* a `RecRule`, so it carries a `RecRuleWF` conclusion. -/
theorem rec_rule_bits_refines (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) {rec_name : name.Name}
    {rl r : env.RecRule} (hrec : NameWF rec_name) (hrl : RecRuleWF rl)
    (h : core_k.rec_rule_bits fe rec_name rl = ok r) :
    absRecRule r = ConLeche.recRuleBits lfe.find? (absName rec_name) (absRecRule rl)
      ∧ RecRuleWF r := by
  rw [core_k.rec_rule_bits] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨k, hk, eta, heta, rfl⟩ := h
  have hkabs := rec_rule_k_of_refines henv hrel hwf hrl.1 hk
  have hetaabs := rec_rule_eta_of_refines henv hrel hwf hrec hrl.1 heta
  refine ⟨?_, hrl.1, hrl.2.1, hrl.2.2⟩
  rw [ConLeche.recRuleBits, absRecRule, absRecRule]
  simp only [hkabs, hetaabs]

/-- `ConLeche/Kernel/Core.lean:1582-1594` -- `core_k::proj_fn_rule` refines
`projFnRule`: the stored rule of an installed projection function, with its two
bits stamped by `rec_rule_bits`.  The cited record literal leaves `k`/`eta` at
their `false` defaults, which the stamping then overwrites. -/
theorem proj_fn_rule_refines (henv : EnvFacts) {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FindAgree fe lfe) (hwf : FindWF fe) {t ctor_name : name.Name}
    {pty rhs_a : expr.Expr} {n_p n_f i : Std.U64} {r : env.RecRule}
    (ht : NameWF t) (hctor : NameWF ctor_name) (hpty : ExprWF pty) (hrhs : ExprWF rhs_a)
    (h : core_k.proj_fn_rule fe t ctor_name pty n_p n_f i rhs_a = ok r) :
    absRecRule r = ConLeche.projFnRule lfe.find? (absName t) (absName ctor_name)
        (absExpr pty) n_p.val n_f.val i.val (absExpr rhs_a) ∧ RecRuleWF r := by
  rw [core_k.proj_fn_rule] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨bp, hbp, fire, hfire, n1, hn1, hbits⟩ := h
  have hbpabs := ExprOps.rec_rule_plain_refines hpty hbp
  obtain ⟨hn1abs, hn1wf⟩ := proj_fn_name_refines ht hn1
  have hfirev : fire
      = (if bp = true then env.RecRuleFire.Plain else env.RecRuleFire.Inert) := by
    split at hfire
    · rename_i hb; rw [if_pos hb]; exact (Result.ok_injective hfire).symm
    · rename_i hb; rw [if_neg hb]; exact (Result.ok_injective hfire).symm
  subst hfirev
  have hfwf : RecRuleFireWF (if bp = true then env.RecRuleFire.Plain
      else env.RecRuleFire.Inert) := by
    cases bp <;> exact trivial
  have hrlwf : RecRuleWF ⟨ctor_name, n_f, n_p,
      (if bp = true then env.RecRuleFire.Plain else env.RecRuleFire.Inert),
      rhs_a, false, false, false⟩ := ⟨hctor, hfwf, hrhs⟩
  obtain ⟨habs, hrwf⟩ := rec_rule_bits_refines henv hrel hwf hn1wf hrlwf hbits
  refine ⟨?_, hrwf⟩
  rw [habs, ConLeche.projFnRule, hn1abs]
  congr 1
  rw [absRecRule, ← hbpabs]
  cases bp <;> rfl

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.CoreK.and_rescue_slots_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms and_rescue_slots_refines

end ConRon.Refine.CoreK

