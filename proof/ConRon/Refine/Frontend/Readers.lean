/-
The parser's **readers and value builders**, well formed by construction (task
#85, phase 1).

This file owns `frontend::export_c`'s reading half — the three index tables
(`scan_types::id_table_*`), the six state readers, the five value builders and
the six state steps that write a term back — together with the one arithmetic
leaf the parse needs and the checker does not (`nat_decimal::from_decimal`).

The argument is DESIGN.md §3.5's, and it is one line: the `*WF` predicates of
`Refine/Abs.lean` are **inductives whose constructors are the port's own smart
constructors** (`name::mk_str`, `level::succ`, `expr::app`, …), and the parse
reaches every node it stores through exactly one of them.  So each lemma below
is a forward walk through the generated body that applies one `NameWF`/
`LevelWF`/`ExprWF` constructor per arm, with `Refine/Frontend/Base.lean`'s
`StateDWF`/`IdTableWF`/`MapValsWF` carrying the invariant across a table write.

`Refine/Frontend/ScanWF.lean` supplies the one hypothesis that is *not* by
construction, `NameRecWF`/`ExprRecWF`: a `Vec<u32>` the scanner produced as a
string payload holds valid code points.

**The task-#71 idiom** (`Refine/README.md` §"Writing a new refinement lemma")
closes every arm-per-constructor lemma here — the two value builders it was
landed for (`parse_level_rec_d_wf`, `parse_expr_rec_d_wf`), the two record
builders and all three table entries — as `rust_norm h ; all_goals rust_grind`
after one shape line.  What each needed beyond the registered sets is a handful
of equation-first `use` lemmas (the `*_wf'` family below) and four local
`rust_reduce` equations for the wrappers the generated body calls but the
plumbing set does not know (`expr::literal_nat`, `expr::literal_str`,
`expr::mk_bvar`, `export_c::merr`).  The loops and the table plumbing are hand
proofs, as the idiom's scope says they must be: a `*_loop` is a
`partial_fixpoint` with no induction principle, so it is strong induction on
`n - i`.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Plumbing

The four `Vec` facts every table write needs.  `Refine/PinsWF.lean` keeps
private copies of the first two; they are four lines each. -/

/-- What a `Vec` read hands back is one of the `Vec`'s entries: how a
well-formed table makes a well-formed reading. -/
private theorem vec_index_mem {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    x ∈ v.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? h)

/-- A push extends a "every entry satisfies `P`" invariant by the pushed
element: the step the dense half of a table and every accumulator takes. -/
private theorem push_wf {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  rw [vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- The write-back of a `Vec::index_mut` is `Vec.set`.  (`Refine/HashMap.lean`'s
`vec_index_mut_eq` says more but asks for `Inhabited α`, which the port's three
term types do not have.) -/
private theorem index_mut_back {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {a : α} {f : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (a, f)) :
    f = alloc.vec.Vec.set v i := by
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨y, -, h⟩ := h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- An overwrite of one slot keeps the invariant: `id_table_insert`'s rebinding
arm below the dense frontier. -/
private theorem set_wf {α : Type} {P : α → Prop} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x) : ∀ y ∈ (alloc.vec.Vec.set v i x).val, P y := by
  intro y hy
  rw [alloc.vec.Vec.set_val_eq] at hy
  rcases List.mem_or_eq_of_mem_set hy with hy | hy
  · exact hv y hy
  · exact hy ▸ hx

/-! ## The parse's index tables

`scan_types::id_table_*` (`ConLeche/Frontend/Scan/Types.lean:341-361 IdTable`):
the dense prefix and the sparse overflow map, both halves. -/

/-- `scan_types::id_table_get` (`Scan/Types.lean:346-348 IdTable.get?`): a hit
returns a recorded value, from the dense `Vec` or from the overflow map. -/
theorem id_table_get_wf {T : Type} {P : T → Prop} {t : frontend.scan_types.IdTable T}
    {i : Std.U64} {x : T} (ht : IdTableWF P t)
    (h : frontend.scan_types.id_table_get t i = ok (some x)) : P x := by
  rw [frontend.scan_types.id_table_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨k, -, i1, -, h⟩ := h
  split at h
  · split at h
    · simp only [bind_eq_ok_iff, Result.ok.injEq, Option.some.injEq] at h
      obtain ⟨y, hy, rfl⟩ := h
      exact ht.1 _ (vec_index_mem hy)
    · exact map_get_wf ht.2 h
  · exact map_get_wf ht.2 h

/-- `scan_types::id_table_insert` (`Scan/Types.lean:350-357 IdTable.insert`):
the three arms — a push at the frontier, an overwrite below it, an overflow
insert above it — each record the inserted value and disturb nothing else. -/
theorem id_table_insert_wf {T : Type} {P : T → Prop} {t t' : frontend.scan_types.IdTable T}
    {i : Std.U64} {x : T} (ht : IdTableWF P t) (hx : P x)
    (h : frontend.scan_types.id_table_insert t i x = ok t') : IdTableWF P t' := by
  rw [frontend.scan_types.id_table_insert] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, -, h⟩ := h
  split at h
  · simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨push_wf ht.1 hx hv, ht.2⟩
  · split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨i2, -, p, hp, h⟩ := h
      obtain ⟨a, f⟩ := p
      cases Result.ok_injective h
      rw [index_mut_back hp]
      exact ⟨set_wf ht.1 hx, ht.2⟩
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨p, hp, h⟩ := h
      obtain ⟨old, hm⟩ := p
      cases Result.ok_injective h
      exact ⟨ht.1, map_insert_wf ht.2 hx hp⟩

/-- `scan_types::id_table_singleton` (`Scan/Types.lean:359-361
IdTable.singleton`): index 0 bound, and nothing else. -/
theorem id_table_singleton_wf {T : Type} {P : T → Prop} {x : T}
    {t : frontend.scan_types.IdTable T} (hx : P x)
    (h : frontend.scan_types.id_table_singleton x = ok t) : IdTableWF P t := by
  rw [frontend.scan_types.id_table_singleton] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨dense, hd, m, hm, rfl⟩ := h
  exact ⟨push_wf (by simp [alloc.vec.Vec.new]) hx hd, map_new_wf hm⟩

/-- `scan_types::id_table_empty` (`Scan/Types.lean:341-344 IdTable`'s field
defaults): an empty table holds nothing, at any predicate. -/
theorem id_table_empty_wf {T : Type} {P : T → Prop} {t : frontend.scan_types.IdTable T}
    (h : frontend.scan_types.id_table_empty T = ok t) : IdTableWF P t := by
  rw [frontend.scan_types.id_table_empty] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨by simp [alloc.vec.Vec.new], map_new_wf hm⟩

/-! ## The state readers

`export_c::st_name`/`st_level`/`st_expr` and the two list forms.  Each is one
`id_table_get` and one `*::dup`, and `dup` is the identity in the model
(`Refine/Abs.lean`'s `name_dup_eq`/`level_dup_eq`, `Refine/Expr.lean`'s
`Expr.dup_eq`), so what comes out is literally the recorded entry.  The
`st_fresh_name`/`st_fresh_level`/`st_fresh_expr` guards need no lemma: they
return `()` and write nothing. -/

/-- `export_c::st_name` (`ConLeche/Frontend/ExportC.lean:164-167 StateD.name`). -/
theorem st_name_wf {st : frontend.export_c.StateD} {i : Std.U64} {n : name.Name}
    (hst : StateDWF st) (h : frontend.export_c.st_name st i = ok (.Ok n)) : NameWF n := by
  rw [frontend.export_c.st_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  split at h
  · simp only [bind_eq_ok_iff, frontend.export_c.merr, Result.ok.injEq, reduceCtorEq,
      and_false, exists_false] at h
  · rename_i _ v
    simp only [name_dup_eq, bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    exact id_table_get_wf hst.names ho

/-- `export_c::st_level` (`ConLeche/Frontend/ExportC.lean:169-172 StateD.level`). -/
theorem st_level_wf {st : frontend.export_c.StateD} {i : Std.U64} {u : level.Level}
    (hst : StateDWF st) (h : frontend.export_c.st_level st i = ok (.Ok u)) : LevelWF u := by
  rw [frontend.export_c.st_level] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  split at h
  · simp only [bind_eq_ok_iff, frontend.export_c.merr, Result.ok.injEq, reduceCtorEq,
      and_false, exists_false] at h
  · rename_i _ v
    simp only [level_dup_eq, bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    exact id_table_get_wf hst.levels ho

/-- `export_c::st_expr` (`ConLeche/Frontend/ExportC.lean:174-177 StateD.expr`). -/
theorem st_expr_wf {st : frontend.export_c.StateD} {i : Std.U64} {e : expr.Expr}
    (hst : StateDWF st) (h : frontend.export_c.st_expr st i = ok (.Ok e)) : ExprWF e := by
  rw [frontend.export_c.st_expr] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  split at h
  · simp only [bind_eq_ok_iff, frontend.export_c.merr, Result.ok.injEq, reduceCtorEq,
      and_false, exists_false] at h
  · rename_i _ v
    simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨c, hc, rfl⟩ := h
    rw [Expr.dup_eq hc]
    exact id_table_get_wf hst.exprs ho

/-- The accumulator of `export_c::st_names`' index loop.  A `*_loop` is a
`partial_fixpoint` with no induction principle, so this is strong induction on
the measure `n - i` of the `while i < n` shape. -/
private theorem st_names_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (is : alloc.vec.Vec Std.U64)
      (out : alloc.vec.Vec name.Name) (n i : Std.Usize) (r : alloc.vec.Vec name.Name),
      StateDWF st → NamesWF out → n.val - i.val = N →
      frontend.export_c.st_names_loop st is out n i = ok (.Ok r) → NamesWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st is out n i r hst hout hN h
    rw [frontend.export_c.st_names_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, -, r1, hr1, h⟩ := h
      split at h
      · rename_i _ v
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        exact ih (n.val - i2.val) (by scalar_tac) st is out1 n i2 r hst
          (push_wf hout (st_name_wf hst hr1) hpush) rfl h
      · simp only [Result.ok.injEq, reduceCtorEq] at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::st_names` (con-leche's `is.mapM st.name`, which §3.4 forbids as
an iterator adapter). -/
theorem st_names_wf {st : frontend.export_c.StateD} {is : alloc.vec.Vec Std.U64}
    {ns : alloc.vec.Vec name.Name} (hst : StateDWF st)
    (h : frontend.export_c.st_names st is = ok (.Ok ns)) : NamesWF ns := by
  rw [frontend.export_c.st_names] at h
  exact st_names_loop_wf _ st is _ _ _ ns hst (by simp [NamesWF]) rfl h

/-- The accumulator of `export_c::st_levels`' index loop (see
`st_names_loop_wf`). -/
private theorem st_levels_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (is : alloc.vec.Vec Std.U64)
      (out : alloc.vec.Vec level.Level) (n i : Std.Usize) (r : alloc.vec.Vec level.Level),
      StateDWF st → LevelsWF out → n.val - i.val = N →
      frontend.export_c.st_levels_loop st is out n i = ok (.Ok r) → LevelsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st is out n i r hst hout hN h
    rw [frontend.export_c.st_levels_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, -, r1, hr1, h⟩ := h
      split at h
      · rename_i _ v
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        exact ih (n.val - i2.val) (by scalar_tac) st is out1 n i2 r hst
          (push_wf hout (st_level_wf hst hr1) hpush) rfl h
      · simp only [Result.ok.injEq, reduceCtorEq] at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::st_levels` (con-leche's `us.mapM st.level`). -/
theorem st_levels_wf {st : frontend.export_c.StateD} {is : alloc.vec.Vec Std.U64}
    {us : alloc.vec.Vec level.Level} (hst : StateDWF st)
    (h : frontend.export_c.st_levels st is = ok (.Ok us)) : LevelsWF us := by
  rw [frontend.export_c.st_levels] at h
  exact st_levels_loop_wf _ st is _ _ _ us hst (by simp [LevelsWF]) rfl h

/-- `export_c::get_decl_d` (`ConLeche/Frontend/ExportC.lean:179-189 getDeclD`):
the declaration-level expression lookup, which is `st_expr`. -/
theorem get_decl_d_wf {st : frontend.export_c.StateD} {i : Std.U64} {e : expr.Expr}
    (hst : StateDWF st) (h : frontend.export_c.get_decl_d st i = ok (.Ok e)) : ExprWF e := by
  rw [frontend.export_c.get_decl_d] at h
  exact st_expr_wf hst h

/-- `export_c::parse_pw_d` (`ConLeche/Frontend/ExportC.lean:191-194 parsePwD`):
both arms are a `PropWhenWF` constructor — `prop_when::never` and
`prop_when::if_all_zero`, two of the type's four public producers. -/
theorem parse_pw_d_wf {st : frontend.export_c.StateD} {r : frontend.scan_types.PwRec}
    {pw : prop_when.PropWhen} (hst : StateDWF st)
    (h : frontend.export_c.parse_pw_d st r = ok (.Ok pw)) : PropWhenWF pw := by
  rw [frontend.export_c.parse_pw_d.eq_def] at h
  split at h
  · simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨c, hc, rfl⟩ := h
    exact PropWhenWF.never hc
  · rename_i ns
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r1, hr1, h⟩ := h
    split at h
    · rename_i _ out
      simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨c, hc, rfl⟩ := h
      exact PropWhenWF.if_all_zero (st_names_wf hst hr1) hc
    · simp only [Result.ok.injEq, reduceCtorEq] at h

/-! ## The readers, keyed on the Rust equation

`Refine/README.md`'s first keying rule: a `grind [→ …]` lemma takes its
E-matching patterns from its propositional hypotheses **in order**, so a reader
whose first hypothesis is `StateDWF st` would fire at every well-formed state
rather than on the node the inverted bind produced.  These are the same seven
lemmas with the equation first, and they are what the idiom below runs on. -/

private theorem st_name_wf' {st : frontend.export_c.StateD} {i : Std.U64} {n : name.Name}
    (h : frontend.export_c.st_name st i = ok (.Ok n)) (hst : StateDWF st) : NameWF n :=
  st_name_wf hst h

private theorem st_level_wf' {st : frontend.export_c.StateD} {i : Std.U64} {u : level.Level}
    (h : frontend.export_c.st_level st i = ok (.Ok u)) (hst : StateDWF st) : LevelWF u :=
  st_level_wf hst h

private theorem st_expr_wf' {st : frontend.export_c.StateD} {i : Std.U64} {e : expr.Expr}
    (h : frontend.export_c.st_expr st i = ok (.Ok e)) (hst : StateDWF st) : ExprWF e :=
  st_expr_wf hst h

private theorem st_names_wf' {st : frontend.export_c.StateD} {is : alloc.vec.Vec Std.U64}
    {ns : alloc.vec.Vec name.Name} (h : frontend.export_c.st_names st is = ok (.Ok ns))
    (hst : StateDWF st) : NamesWF ns := st_names_wf hst h

private theorem st_levels_wf' {st : frontend.export_c.StateD} {is : alloc.vec.Vec Std.U64}
    {us : alloc.vec.Vec level.Level} (h : frontend.export_c.st_levels st is = ok (.Ok us))
    (hst : StateDWF st) : LevelsWF us := st_levels_wf hst h

private theorem get_decl_d_wf' {st : frontend.export_c.StateD} {i : Std.U64} {e : expr.Expr}
    (h : frontend.export_c.get_decl_d st i = ok (.Ok e)) (hst : StateDWF st) : ExprWF e :=
  get_decl_d_wf hst h

private theorem parse_pw_d_wf' {st : frontend.export_c.StateD} {r : frontend.scan_types.PwRec}
    {pw : prop_when.PropWhen} (h : frontend.export_c.parse_pw_d st r = ok (.Ok pw))
    (hst : StateDWF st) : PropWhenWF pw := parse_pw_d_wf hst h

attribute [local grind →] st_name_wf' st_level_wf' st_expr_wf' st_names_wf' st_levels_wf'
  get_decl_d_wf' parse_pw_d_wf' Level.zero_wf' Level.succ_wf' Level.max_wf' Level.imax_wf'
  Level.param_wf'

/-- `export_c::parse_level_rec_d` (`ConLeche/Frontend/ExportC.lean:239-247
parseLevelEntryD`): four arms, one `LevelWF` constructor each.  The first
lemma of the group written with the task-#71 idiom, and exactly its shape. -/
theorem parse_level_rec_d_wf {st : frontend.export_c.StateD} {r : frontend.scan_types.LevelRec}
    {u : level.Level} (hst : StateDWF st)
    (h : frontend.export_c.parse_level_rec_d st r = ok (.Ok u)) : LevelWF u := by
  rw [frontend.export_c.parse_level_rec_d.eq_def] at h
  rust_norm h
  all_goals rust_grind

/-! ## The two `Expr` leaves

`ExprRec::NatVal` and `ExprRec::StrVal` are the only arms of the expression
parse whose payload is not already a table entry, so they are the only two that
need a lemma of their own. -/

/-- `nat_decimal::from_decimal` (no cited Lean: `Scan/Fast.lean`'s `readNat`
produces a Lean `Nat` straight from the digits, and the port has its own
bignum) returns `ron::nat`'s own normal form — because its last step is
`nat::norm`, whatever the nineteen-digit chunk loop accumulated. -/
theorem from_decimal_wf {s : Slice Std.U8} {n : ron.nat.Nat}
    (h : frontend.nat_decimal.from_decimal s = ok (some n)) : Nat.NatWF n := by
  rw [frontend.nat_decimal.from_decimal] at h
  split at h
  · simp only [Result.ok.injEq, reduceCtorEq] at h
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨b, -, h⟩ := h
    split at h
    · simp only [bind_eq_ok_iff, Result.ok.injEq, Option.some.injEq] at h
      obtain ⟨v, -, m, hm, rfl⟩ := h
      exact (Nat.norm_refines hm).2
    · simp only [Result.ok.injEq, reduceCtorEq] at h

/-- `core_types::code_points` copies the slice, so `StrWF` transfers from the
scanner's record to the `Vec<u32>` the literal (or the `Str` name) stores. -/
private theorem code_points_wf {s v : alloc.vec.Vec Std.U32} (hs : StrWF s)
    (h : core_types.code_points (alloc.vec.Vec.deref s) = ok v) : StrWF v := by
  intro c hc
  rw [Env.code_points_val h,
    show (alloc.vec.Vec.deref s).val = s.val from Slice.from_val _ _] at hc
  exact hs c hc

/-- `Refine/README.md`'s second keying rule: an optional clause is keyed on the
Rust equation *with the constructor in it*, so that it fires on the literal the
inverted bind produced rather than on every `Literal` in sight. -/
private theorem lit_nat_wf' {n : ron.nat.Nat} {e : expr.Expr}
    (h : expr.lit (.NatVal n) = ok e) (hn : Nat.NatWF n) : ExprWF e := Expr.lit_wf' h hn

private theorem lit_str_wf' {s : alloc.vec.Vec Std.U32} {e : expr.Expr}
    (h : expr.lit (.StrVal s) = ok e) (hs : StrWF s) : ExprWF e := Expr.lit_wf' h hs

/-- The four wrappers the generated body calls that `Refine/Abs.lean`'s
plumbing set does not know: two literal constructors (each one `ron::ptr::new`,
the identity), the `bvar` pool stub of task #11, and the parse's `throw`. -/
private theorem literal_nat_eq (n : ron.nat.Nat) : expr.literal_nat n = ok (.NatVal n) := by
  simp [expr.literal_nat]

private theorem literal_str_eq (s : alloc.vec.Vec Std.U32) :
    expr.literal_str s = ok (.StrVal s) := by simp [expr.literal_str]

private theorem mk_bvar_eq (i : Std.U64) : expr.mk_bvar i = expr.bvar i := by
  simp [expr.mk_bvar]

private theorem merr_eq (T : Type) (msg : alloc.vec.Vec Std.U32) :
    frontend.export_c.merr T msg = ok (.Err (.Msg msg)) := rfl

/-- `expr::binder_meta` is the pointer wrapper (`ExprOps.binder_meta_eq`), so
the two binder arms meet the node `⟨p⟩` rather than a variable: the `use`
lemmas are stated at it, `BinderMetaWF ⟨p⟩` being `PropWhenWF p` by
definition. -/
private theorem lam_pw_wf' {ty bo e : expr.Expr} {p : prop_when.PropWhen}
    (h : expr.lam ty bo ⟨p⟩ = ok e) (hty : ExprWF ty) (hbo : ExprWF bo)
    (hp : PropWhenWF p) : ExprWF e := Expr.lam_wf' h hty hbo hp

private theorem forall_e_pw_wf' {ty bo e : expr.Expr} {p : prop_when.PropWhen}
    (h : expr.forall_e ty bo ⟨p⟩ = ok e) (hty : ExprWF ty) (hbo : ExprWF bo)
    (hp : PropWhenWF p) : ExprWF e := Expr.forall_e_wf' h hty hbo hp

attribute [local rust_reduce, local rust_invert] literal_nat_eq literal_str_eq mk_bvar_eq
  merr_eq

attribute [local grind →] Expr.bvar_wf Expr.sort_wf' Expr.mk_const_wf' Expr.app_wf'
  lam_pw_wf' forall_e_pw_wf' Expr.let_e_wf' Expr.proj_wf' lit_nat_wf' lit_str_wf'
  from_decimal_wf code_points_wf

/-- `export_c::parse_expr_rec_d` (`ConLeche/Frontend/ExportC.lean:249-279
parseExprEntryD`): **ten arms, one `ExprWF` constructor each** — the group's
central lemma and the largest use of the task-#71 idiom so far.  The shape step
is `cases r`; everything after it is the idiom's two lines. -/
theorem parse_expr_rec_d_wf {st : frontend.export_c.StateD} {r : frontend.scan_types.ExprRec}
    {e : expr.Expr} (hst : StateDWF st) (hr : ExprRecWF r)
    (h : frontend.export_c.parse_expr_rec_d st r = ok (.Ok e)) : ExprWF e := by
  rw [frontend.export_c.parse_expr_rec_d.eq_def] at h
  cases r
  all_goals simp only [ExprRecWF] at hr
  all_goals rust_norm h
  all_goals rust_grind

/-! ## The record builders -/

/-- `export_c::parse_cv_d` (`ConLeche/Frontend/ExportC.lean:283-289 parseCVD`):
a declaration's common data — three readings, no constructor of its own
(`ConstantValWF` is hereditary, `env`'s records carrying no derived data). -/
theorem parse_cv_d_wf {st : frontend.export_c.StateD} {cv : frontend.scan_types.CVRec}
    {v : env.ConstantVal} (hst : StateDWF st)
    (h : frontend.export_c.parse_cv_d st cv = ok (.Ok v)) : ConstantValWF v := by
  rw [frontend.export_c.parse_cv_d.eq_def] at h
  rust_norm h
  all_goals (simp only [ConstantValWF]; rust_grind)

private theorem rec_rule_parsed_wf' {ctor : name.Name} {nfields : Std.U64} {rhs : expr.Expr}
    {r : env.RecRule} (h : env.rec_rule_parsed ctor nfields rhs = ok r) (hc : NameWF ctor)
    (hr : ExprWF rhs) : RecRuleWF r := Env.rec_rule_parsed_wf hc hr h

attribute [local grind →] rec_rule_parsed_wf'

/-- `export_c::parse_rule_d` (`ConLeche/Frontend/ExportC.lean:346-349
parseRuleD`): one recursor rule, at `env::rec_rule_parsed`'s field defaults. -/
theorem parse_rule_d_wf {st : frontend.export_c.StateD} {ru : frontend.scan_types.RuleRec}
    {r : env.RecRule} (hst : StateDWF st)
    (h : frontend.export_c.parse_rule_d st ru = ok (.Ok r)) : RecRuleWF r := by
  rw [frontend.export_c.parse_rule_d.eq_def] at h
  rust_norm h
  all_goals rust_grind

/-- The accumulator of `export_c::parse_rules_d`' index loop (see
`st_names_loop_wf`). -/
private theorem parse_rules_d_loop_wf (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (rus : alloc.vec.Vec frontend.scan_types.RuleRec)
      (out : alloc.vec.Vec env.RecRule) (n i : Std.Usize) (r : alloc.vec.Vec env.RecRule),
      StateDWF st → RecRulesWF out → n.val - i.val = N →
      frontend.export_c.parse_rules_d_loop st rus out n i = ok (.Ok r) → RecRulesWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st rus out n i r hst hout hN h
    rw [frontend.export_c.parse_rules_d_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨rr, -, r1, hr1, h⟩ := h
      split at h
      · rename_i _ v
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        exact ih (n.val - i1.val) (by scalar_tac) st rus out1 n i1 r hst
          (push_wf hout (parse_rule_d_wf hst hr1) hpush) rfl h
      · simp only [Result.ok.injEq, reduceCtorEq] at h
    · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
      exact h ▸ hout

/-- `export_c::parse_rules_d` (`ConLeche/Frontend/ExportC.lean:346-349
parseRuleD`'s `r.rules.mapM`). -/
theorem parse_rules_d_wf {st : frontend.export_c.StateD}
    {rus : alloc.vec.Vec frontend.scan_types.RuleRec} {rs : alloc.vec.Vec env.RecRule}
    (hst : StateDWF st) (h : frontend.export_c.parse_rules_d st rus = ok (.Ok rs)) :
    RecRulesWF rs := by
  rw [frontend.export_c.parse_rules_d] at h
  exact parse_rules_d_loop_wf _ st rus _ _ _ rs hst (by simp [RecRulesWF]) rfl h

/-! ## The state steps

`note_decl_entries`, `note_one` and `note_block` need no lemma of their own:
they build the entry `Vec` and never touch the state.  What the state steps
below have to show is that `note_entries`' two writes — `heights` and
`const_types`, the modeller's tables, which `StateDWF` has no clause for —
leave the six tracked fields where they were. -/

/-- `export_c::state_d_init` (`ConLeche/Frontend/ExportC.lean:755-758
StateD.init`): the two singleton tables hold `name::anonymous` and
`level::zero`, which are `NameWF`/`LevelWF` constructors; everything else is
empty. -/
theorem state_d_init_wf {im ce : Bool} {st : frontend.export_c.StateD}
    (h : frontend.export_c.state_d_init im ce = ok st) : StateDWF st := by
  rw [frontend.export_c.state_d_init] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, it, hit, l, hl, it1, hit1, it2, hit2, hm, hhm, hm1, hhm1,
    hm2, -, hm3, -, hm4, -, hm5, -, rfl⟩ := h
  exact ⟨id_table_singleton_wf (NameWF.anonymous hn) hit,
    id_table_singleton_wf (LevelWF.zero hl) hit1, id_table_empty_wf hit2,
    by simp [alloc.vec.Vec.new], map_new_wf hhm, map_new_wf hhm1⟩

/-- The step of `export_c::note_entries`' index loop (see `st_names_loop_wf`
for the induction).  Both writes land in untracked fields, so every clause is
carried across by the record update. -/
private theorem note_entries_loop_wf (N : Nat) :
    ∀ (st st' : frontend.export_c.StateD)
      (es : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr × (Option Std.U64)))
      (n i : Std.Usize),
      StateDWF st → n.val - i.val = N →
      frontend.export_c.note_entries_loop st es n i = ok st' → StateDWF st' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st st' es n i hst hN h
    rw [frontend.export_c.note_entries_loop.eq_def] at h
    split at h
    · rename_i hlt
      -- `Prod.exists` first: the entry is a four-tuple, and the
      -- `let (n1, v, e, o) := …` its pattern produces is a one-alternative `match`
      -- that neither `split` nor a plain `simp only [bind_eq_ok_iff]` opens
      -- (`Refine/Abs.lean`'s `rust_pairs` note).
      simp only [bind_eq_ok_iff, Prod.exists] at h
      obtain ⟨n1, v, e, o, -, h⟩ := h
      simp only [rust_invert] at h
      obtain ⟨st1, hst1, v1, -, e1, -, old, hm, -, i1, hi1, h⟩ := h
      have hst1' : StateDWF st1 := by
        split at hst1
        · exact (Result.ok_injective hst1) ▸ hst
        · simp only [rust_invert] at hst1
          obtain ⟨old1, hm1, -, hst1⟩ := hst1
          exact hst1 ▸
            ⟨hst.names, hst.levels, hst.exprs, hst.decls, hst.proj_owners, hst.proj_levels⟩
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      refine ih (n.val - i1.val) (by scalar_tac) _ st' es n i1 ?_ rfl h
      exact ⟨hst1'.names, hst1'.levels, hst1'.exprs, hst1'.decls, hst1'.proj_owners,
        hst1'.proj_levels⟩
    · exact (Result.ok_injective h) ▸ hst

/-- `export_c::note_entries` (`ConLeche/Frontend/ExportC.lean:135-153
noteDecl`): it writes only `heights` and `const_types`, which the invariant
does not track. -/
theorem note_entries_wf {st st' : frontend.export_c.StateD}
    {es : alloc.vec.Vec (name.Name × (alloc.vec.Vec name.Name) × expr.Expr × (Option Std.U64))}
    (hst : StateDWF st) (h : frontend.export_c.note_entries st es = ok st') : StateDWF st' := by
  rw [frontend.export_c.note_entries] at h
  exact note_entries_loop_wf _ st st' es _ _ hst rfl h

/-- `export_c::note_decl` (`ConLeche/Frontend/ExportC.lean:135-153
noteDecl`). -/
theorem note_decl_wf {st st' : frontend.export_c.StateD} {d : env.Declaration}
    (hst : StateDWF st) (h : frontend.export_c.note_decl st d = ok st') : StateDWF st' := by
  rw [frontend.export_c.note_decl] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨es, -, h⟩ := h
  exact note_entries_wf hst h

/-- `export_c::push_decl` (`ConLeche/Frontend/ExportC.lean:155-162 pushDecl`):
**the one step that extends `StateDWF.decls`**, and the only one that asks its
caller for anything — the declaration it appends must itself be well formed. -/
theorem push_decl_wf {st st' : frontend.export_c.StateD} {d : env.Declaration}
    (hst : StateDWF st) (hd : DeclarationWF d)
    (h : frontend.export_c.push_decl st d = ok st') : StateDWF st' := by
  rw [frontend.export_c.push_decl] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨st1, hst1, v, hv, rfl⟩ := h
  have h1 := note_decl_wf hst hst1
  exact ⟨h1.names, h1.levels, h1.exprs, push_wf h1.decls hd hv, h1.proj_owners, h1.proj_levels⟩

/-! ## The three table entries

Each binds one stream index: the value half above, then `id_table_insert` into
the matching table.  The three `*_insert_wf'` lemmas are the state update read
as a `StateDWF` step, keyed on the Rust equation like every other `use` lemma
here. -/

private theorem names_insert_wf' {st : frontend.export_c.StateD} {i : Std.U64} {n : name.Name}
    {it : frontend.scan_types.IdTable name.Name}
    (h : frontend.scan_types.id_table_insert st.names i n = ok it)
    (hst : StateDWF st) (hn : NameWF n) : StateDWF { st with names := it } :=
  ⟨id_table_insert_wf hst.names hn h, hst.levels, hst.exprs, hst.decls, hst.proj_owners,
    hst.proj_levels⟩

private theorem levels_insert_wf' {st : frontend.export_c.StateD} {i : Std.U64} {u : level.Level}
    {it : frontend.scan_types.IdTable level.Level}
    (h : frontend.scan_types.id_table_insert st.levels i u = ok it)
    (hst : StateDWF st) (hu : LevelWF u) : StateDWF { st with levels := it } :=
  ⟨hst.names, id_table_insert_wf hst.levels hu h, hst.exprs, hst.decls, hst.proj_owners,
    hst.proj_levels⟩

private theorem exprs_insert_wf' {st : frontend.export_c.StateD} {i : Std.U64} {e : expr.Expr}
    {it : frontend.scan_types.IdTable expr.Expr}
    (h : frontend.scan_types.id_table_insert st.exprs i e = ok it)
    (hst : StateDWF st) (he : ExprWF e) : StateDWF { st with exprs := it } :=
  ⟨hst.names, hst.levels, id_table_insert_wf hst.exprs he h, hst.decls, hst.proj_owners,
    hst.proj_levels⟩

private theorem mk_str_wf' {pre s n} (h : name.mk_str pre s = ok n) (hpre : NameWF pre)
    (hs : StrWF s) : NameWF n := NameWF.str hpre hs h

private theorem mk_num_wf' {pre m n} (h : name.mk_num pre m = ok n) (hpre : NameWF pre) :
    NameWF n := NameWF.num hpre h

private theorem parse_level_rec_d_wf' {st : frontend.export_c.StateD}
    {r : frontend.scan_types.LevelRec} {u : level.Level}
    (h : frontend.export_c.parse_level_rec_d st r = ok (.Ok u)) (hst : StateDWF st) :
    LevelWF u := parse_level_rec_d_wf hst h

private theorem parse_expr_rec_d_wf' {st : frontend.export_c.StateD}
    {r : frontend.scan_types.ExprRec} {e : expr.Expr}
    (h : frontend.export_c.parse_expr_rec_d st r = ok (.Ok e)) (hst : StateDWF st)
    (hr : ExprRecWF r) : ExprWF e := parse_expr_rec_d_wf hst hr h

attribute [local grind →] names_insert_wf' levels_insert_wf' exprs_insert_wf' mk_str_wf'
  mk_num_wf' code_points_wf parse_level_rec_d_wf' parse_expr_rec_d_wf'

/-- `export_c::parse_name_entry_d` (`ConLeche/Frontend/ExportC.lean:228-237
parseNameEntryD`): the name value is built directly, by `name::mk_str` or
`name::mk_num` — the two `NameWF` constructors that are not `anonymous`.  The
`Str` arm is where `NameRecWF`'s `StrWF` is spent. -/
theorem parse_name_entry_d_wf {st st' : frontend.export_c.StateD} {i : Std.U64}
    {r : frontend.scan_types.NameRec} (hst : StateDWF st) (hr : NameRecWF r)
    (h : frontend.export_c.parse_name_entry_d st i r = ok (.Ok (), st')) : StateDWF st' := by
  rw [frontend.export_c.parse_name_entry_d.eq_def] at h
  cases r
  all_goals simp only [NameRecWF] at hr
  all_goals rust_norm h
  all_goals rust_grind

/-- `export_c::parse_level_entry_d` (`ConLeche/Frontend/ExportC.lean:239-247
parseLevelEntryD`). -/
theorem parse_level_entry_d_wf {st st' : frontend.export_c.StateD} {i : Std.U64}
    {r : frontend.scan_types.LevelRec} (hst : StateDWF st)
    (h : frontend.export_c.parse_level_entry_d st i r = ok (.Ok (), st')) : StateDWF st' := by
  rw [frontend.export_c.parse_level_entry_d.eq_def] at h
  rust_norm h
  all_goals rust_grind

/-- `export_c::parse_expr_entry_d` (`ConLeche/Frontend/ExportC.lean:249-279
parseExprEntryD`). -/
theorem parse_expr_entry_d_wf {st st' : frontend.export_c.StateD} {i : Std.U64}
    {r : frontend.scan_types.ExprRec} (hst : StateDWF st) (hr : ExprRecWF r)
    (h : frontend.export_c.parse_expr_entry_d st i r = ok (.Ok (), st')) : StateDWF st' := by
  rw [frontend.export_c.parse_expr_entry_d.eq_def] at h
  rust_norm h
  all_goals rust_grind

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.Frontend.parse_expr_rec_d_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parse_expr_rec_d_wf

/--
info: 'ConRon.Refine.Frontend.parse_cv_d_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parse_cv_d_wf

end ConRon.Refine.Frontend
