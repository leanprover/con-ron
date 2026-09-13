/-
Step 5 of `ConRon/Refine/CORE_PLAN.md`: the **operation** half of
`cached::state_c`'s refinement — the `*M` wrappers of
`crates/con-ron-core/src/cached/state_c.rs` against con-leche's
`ConLeche/Cached/StateC.lean`.

`Refine/State.lean` (task #46) built the *relation*: `StateRel`/`StateWF` over
the fourteen memo tables, and one probe/insert lemma per table.  This file
runs the wrappers on top of it, in the `CORE_PLAN` shape

```
f st … = ok (r, st') → ∀ lst, StateRel st lst → ∃ lst',
  (ConLeche.Cached.f' …).run lst = .ok (abs r, lst') ∧ StateRel st' lst' ∧ StateWF st' ∧ WF r
```

— exact result on success, nothing claimed on failure (DESIGN.md §3.5).  Note
what is *not* claimed: a memo **hit** is not claimed to be *correct*.  Neither
`StateRel` nor `StateWF` says a stored entry is the value the operation would
have computed, and none is needed: con-leche probes the same table at the same
key and gets the same entry, so the two programs agree whatever the entry is.
The memo tables are a refinement obligation, not a soundness one.

## What is here

| group | wrappers |
|---|---|
| the pure wrappers | `bvar_bound_m`, `subst_level_trees`, `peel_fuel`, `inst_c_cap_c`, `cconst_e_new`, and the eight that *are* their `cached::expr_ops_c` twin |
| the level memos | `simplify_l_m` (`lsimpC`), `is_non_zero_l_m` (`lnzC`), `is_equiv_l_m` and `is_equiv_list_l_m` (`eqvC` over `lsimpC`) |
| the bulk-instantiation memo | `inst_list_m`, with the `instC` entry cap `inst_c_cap_c` and its clear-on-cap |
| the lazy stored-constant conversions | `stored_ty_idx_m`, `stored_val_idx_m` (`ienv`, the §3.2 pointer-identity sites) |
| the level-instantiated readers | `const_decl_probe`/`defn_decl_probe`/`rule_rhs_probe(_from)` and `const_ty_at_m`/`const_val_at_m`/`rule_rhs_at_m` |
| the flush and the record | `flush_c`, `record_c_const` |

`consts_resolve_fc` — the memoized `ExprC` DAG walk of the parsed-index
driver — is the sibling file `Refine/StateCResolve.lean`.

## The two ingredients this file does not own

* **`cached::expr_ops_c`.**  Eight of the wrappers, `inst_list_m` and
  `inst_level_params_m` among them, run an `ExprOpsC` twin, whose refinement is
  task #51's `Refine/ExprOpsC.lean`.  Rather than duplicate it, the two facts
  needed here are *named* (`InstantiateListRefines`,
  `InstLevelParamsRefines`) and taken as hypotheses; the eight thin wrappers
  get, in addition, the unconditional identity that says the wrapper *is* its
  twin (`inst1_m_eq`, …), which is the whole of their content.  Nothing is
  weakened: the conclusions below are the exact-result ones, under an explicit
  ingredient.
* **`InstCSize`** is the `instC` entry-count clause the cap needs
  (`StateC.lean:188-197` drops the map when `size ≥ instCCapC`,
  `inst_list_m_reset_at` when `len() ≥ inst_c_cap_c`).  Task #61 folded it
  into `State.lean`'s `StateRel` (the field `StateRel.instCSize`), so it is
  *derivable* here and the abbreviation below is only a name; it still travels
  as an explicit hypothesis and an explicit conclusion of the `inst_list_m`
  lemmas, so the memo policies line up probe by probe.
-/
import ConRon.Refine.State
import ConRon.Refine.FEnv
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsCAbs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.StateC

open ConRon.Refine.State

/-! ## Plumbing

`CheckCM = StateT CState (Except CheckError)`, so a con-leche wrapper's `run`
is an `Except` and `pure` is `Except.ok`.  The lemma and the `local simp`
attributes below are the whole of the monad plumbing: with them in place, every
"run" lemma in this file is `simp [<the con-leche definition>, <the lookups>]`.

What they do *not* do is push a state argument through an `if` or a `match`:
`(if c then f else g) lst` is opaque to `simp`.  That is why the run lemmas come
one per *branch* of the con-leche definition, and why `eqvStep` and (in
`StateCResolve.lean`) `nodeL` name the subterms con-leche writes inline — each a
`rfl`-identity against the cited definition, so nothing is assumed. -/

/-- `pure` in `Except` is `ok`. -/
@[local simp] theorem except_pure {E A : Type} (a : A) :
    (pure a : Except E A) = .ok a := rfl

-- The `simp` set that unfolds a `CheckCM` action's `run` down to its `Option`
-- lookups.
attribute [local simp] StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-- The `instC` table's entry count agrees with con-leche's
`Std.HashMap.size`: what makes the port's `inst_c.len() < inst_c_cap_c` and
con-leche's `mp.size < instCCapC` the same test.  Only `inst_list_m` reads it.

Task #61 folded it into `State.lean`'s `StateRel` (as the field
`StateRel.instCSize`, with `State.insert_size_step` as its insert lemma), so
this abbreviation is now *derivable* — `hrel.instCSize` — rather than an extra
hypothesis a caller has to find from somewhere.  The lemmas below keep it as
an explicit argument and an explicit conclusion, which is what makes the memo
policies line up probe by probe; `State.lean` is where it is established. -/
abbrev InstCSize (st : cached.state_c.CState) (lst : ConLeche.Cached.CState) : Prop :=
  (HashMap.al_v st.inst_c).length = lst.instC.size

/-! ## The pure wrappers

Nine of the ten `*M` syntactic wrappers are `pure (<a syntactic operation>)`,
so the port drops the state argument (task #14's rule 9) and the wrapper *is*
the operation.  Eight of them run a `cached::expr_ops_c` twin, whose
refinement is task #51's; the identity below is this file's whole share of
them, and composing it with `Refine/ExprOpsC.lean`'s lemma is the wrapper's
refinement.  `bvar_bound_m` and `subst_level_trees` run `kernel::` operations
that are already refined, so they get their full lemma here. -/

/-- `ConLeche/Cached/StateC.lean:181-184` — `inst1_m` *is*
`expr_ops_c::instantiate1` (the cited `ExprC.instantiate1`). -/
theorem inst1_m_eq (e v : expr.Expr) (d : Std.U64) :
    cached.state_c.inst1_m e v d = cached.expr_ops_c.instantiate1 e v d := rfl

/-- `ConLeche/Cached/StateC.lean:201-205` — `inst_list_rev_m` *is*
`expr_ops_c::instantiate_rev`. -/
theorem inst_list_rev_m_eq (e : expr.Expr) (vs : alloc.vec.Vec expr.Expr)
    (d : Std.U64) :
    cached.state_c.inst_list_rev_m e vs d
      = cached.expr_ops_c.instantiate_rev e vs d := rfl

/-- `ConLeche/Cached/StateC.lean:207-208` — `abstract1_m` *is*
`expr_ops_c::abstract1` at cursor `0`. -/
theorem abstract1_m_eq (e : expr.Expr) (d : Std.U64) :
    cached.state_c.abstract1_m e d = cached.expr_ops_c.abstract1 e d 0#u64 := rfl

/-- `ConLeche/Cached/StateC.lean:210-211` — `abstract_range_m` *is*
`expr_ops_c::abstract_range` at cursor `0`. -/
theorem abstract_range_m_eq (e : expr.Expr) (d k : Std.U64) :
    cached.state_c.abstract_range_m e d k
      = cached.expr_ops_c.abstract_range e d k 0#u64 := rfl

/-- `ConLeche/Cached/StateC.lean:213-214` — `mk_app_n_m` *is*
`expr_ops_c::mk_app_n`. -/
theorem mk_app_n_m_eq (f : expr.Expr) (args : alloc.vec.Vec expr.Expr) :
    cached.state_c.mk_app_n_m f args = cached.expr_ops_c.mk_app_n f args := rfl

/-- `ConLeche/Cached/StateC.lean:216-218` — `inst_spine_m` *is*
`expr_ops_c::inst_spine`. -/
theorem inst_spine_m_eq (args : alloc.vec.Vec expr.Expr) (t : Std.U64)
    (e : expr.Expr) :
    cached.state_c.inst_spine_m args t e
      = cached.expr_ops_c.inst_spine args t e := rfl

/-- `ConLeche/Cached/StateC.lean:224-226` — `inst_level_params_m` *is*
`expr_ops_c::inst_level_params` (the cited `ExprC.instLevelParams`). -/
theorem inst_level_params_m_eq (ks : alloc.vec.Vec name.Name)
    (us : alloc.vec.Vec level.Level) (e : expr.Expr) :
    cached.state_c.inst_level_params_m ks us e
      = cached.expr_ops_c.inst_level_params ks us e := rfl

/-- `ConLeche/Cached/StateC.lean:172-174` — `peel_fuel` is con-leche's
`peelFuel` (and `peelFuelM`, whose body is `pure peelFuel`). -/
theorem peel_fuel_refines {r : Std.U64} (h : cached.state_c.peel_fuel = ok r) :
    r.val = ConLeche.Cached.peelFuel := by
  rw [cached.state_c.peel_fuel] at h; rw [← Result.ok_injective h]; rfl

/-- `ConLeche/Cached/StateC.lean:162` — `inst_c_cap_c` is con-leche's
`instCCapC`. -/
theorem inst_c_cap_c_refines {r : Std.Usize}
    (h : cached.state_c.inst_c_cap_c = ok r) :
    r.val = ConLeche.Cached.instCCapC := by
  rw [cached.state_c.inst_c_cap_c] at h; rw [← Result.ok_injective h]; rfl

/-- `ConLeche/Cached/StateC.lean:176-177` — `bvar_bound_m` is the cited
`pure e.bvarB`, an `O(1)` field read. -/
theorem bvar_bound_m_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : cached.state_c.bvar_bound_m e = ok r) : r.val = (absExpr e).bvarB := by
  rw [cached.state_c.bvar_bound_m] at h; exact ConRon.Refine.ExprOps.bvar_b_refines he h

/-- `ConLeche/Cached/StateC.lean:122-126` — `cconst_e_new` is the cited
`CConstE` at its one field default, `val := none`. -/
theorem cconst_e_new_refines {ty_e ty : expr.Expr} {c : cached.state_c.CConstE}
    (h : cached.state_c.cconst_e_new ty_e ty = ok c) :
    absCConstE c = { tyE := absExpr ty_e, ty := absExpr ty, val := none } := by
  rw [cached.state_c.cconst_e_new] at h; rw [← Result.ok_injective h]; rfl

/-- `cconst_e_new` is well formed when its two terms are. -/
theorem cconst_e_new_wf {ty_e ty : expr.Expr} {c : cached.state_c.CConstE}
    (hty_e : ExprWF ty_e) (hty : ExprWF ty)
    (h : cached.state_c.cconst_e_new ty_e ty = ok c) : CConstEWF c := by
  rw [cached.state_c.cconst_e_new] at h
  rw [← Result.ok_injective h]
  exact ⟨hty_e, hty, by simp⟩

/-! ## The level memos

Three persistent result caches (`lsimpC`, `lnzC`, `eqvC`) keyed structurally on
`Level` — con-leche's one place a non-`O(1)` hash is paid.  Each wrapper is a
probe and, on a miss, the operation followed by an insert; the memo policies
line up probe by probe. -/

/-- `ConLeche/Kernel/Level.lean:178-183` — `level::is_non_zero` refines
`Level.isNonZero`.  **To be unified into `Refine/Level.lean`**, whose task-#5
cascade covers everything else this file reads off that module; `isNonZeroLM`
is the only caller and it lives here. -/
theorem is_non_zero_refines (u : level.Level) :
    ∀ b, level.is_non_zero u = ok b → b = (absLevel u).isNonZero := by
  induction u using Level.ind' with
  | zero h =>
    intro b hb; rw [level.is_non_zero.eq_def] at hb; simp at hb
    simp [← hb, ConLeche.Level.isNonZero]
  | param h n =>
    intro b hb; rw [level.is_non_zero.eq_def] at hb; simp at hb
    simp [← hb, ConLeche.Level.isNonZero]
  | succ h x _ih =>
    intro b hb; rw [level.is_non_zero.eq_def] at hb; simp at hb
    simp [← hb, ConLeche.Level.isNonZero]
  | imax h x y _ih1 ih2 =>
    intro b hb; rw [level.is_non_zero.eq_def] at hb; simp at hb
    simp [ConLeche.Level.isNonZero, ih2 b hb]
  | max h x y ih1 ih2 =>
    intro b hb; rw [level.is_non_zero.eq_def] at hb; simp at hb
    obtain ⟨b1, h1, hb⟩ := bind_eq_ok_iff.mp hb
    have hx := ih1 b1 h1
    cases b1 with
    | true =>
      simp only [if_true] at hb
      simp [ConLeche.Level.isNonZero, ← Result.ok_injective hb, ← hx]
    | false =>
      simp only [Bool.false_eq_true, if_false] at hb
      simp [ConLeche.Level.isNonZero, ← hx, ih2 b hb]

/-! ### `simplify_l_m`

The two branches separately, because `is_equiv_l_m` runs this wrapper twice and
needs the resulting state *by name*, not under an existential. -/

/-- `ConLeche/Cached/StateC.lean:240-248` — `simplify_l_m` on an `lsimpC`
**hit**: the stored entry, the state untouched. -/
theorem simplify_l_m_hit {st st' : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {u r x : level.Level}
    (hrel : StateRel st lst) (hwf : StateWF st) (hu : LevelWF u)
    (hhit : lst.lsimpC[absLevel u]? = some (absLevel x))
    (h : cached.state_c.simplify_l_m st u = ok (r, st')) :
    absLevel r = absLevel x ∧ LevelWF r ∧ st' = st := by
  rw [cached.state_c.simplify_l_m] at h
  obtain ⟨o, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlk, hv⟩ := lsimp_probe_refines hrel hwf hu hp
  cases o with
  | none => rw [hhit] at hlk; simp at hlk
  | some r0 =>
    rw [hhit] at hlk
    simp only [Option.map_some, Option.some.injEq] at hlk
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hlk, hv r0 rfl, rfl⟩

/-- `ConLeche/Cached/StateC.lean:240-248` — `simplify_l_m` on an `lsimpC`
**miss**: `level::simplify`, then the insert. -/
theorem simplify_l_m_miss {st st' : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {u r : level.Level}
    (hrel : StateRel st lst) (hwf : StateWF st) (hu : LevelWF u)
    (hmiss : lst.lsimpC[absLevel u]? = none)
    (h : cached.state_c.simplify_l_m st u = ok (r, st')) :
    absLevel r = ConLeche.Level.simplify (absLevel u) ∧ LevelWF r ∧
      StateRel st'
        { lst with lsimpC := lst.lsimpC.insert (absLevel u) (absLevel r) } ∧
      StateWF st' := by
  rw [cached.state_c.simplify_l_m] at h
  obtain ⟨o, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlk, -⟩ := lsimp_probe_refines hrel hwf hu hp
  cases o with
  | some r0 => rw [hmiss] at hlk; simp at hlk
  | none =>
    simp only [level_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨r0, hsimp, p, hins, h⟩ := h
    obtain ⟨hr0, hwfr0⟩ := Level.simplify_refines hu hsimp
    obtain ⟨old, m'⟩ := p
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hrel', hwf'⟩ := lsimp_c_insert_refines hrel hwf hu hwfr0 hins
    exact ⟨hr0, hwfr0, hrel', hwf'⟩

/-- `ConLeche/Cached/StateC.lean:240-248` — **`simplify_l_m` refines
`simplifyLM`**: `Level.simplify`, persistently memoized in `lsimpC`. -/
theorem simplify_l_m_refines {st st' : cached.state_c.CState}
    {u r : level.Level} (hwf : StateWF st) (hu : LevelWF u)
    (h : cached.state_c.simplify_l_m st u = ok (r, st')) :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.simplifyLM (absLevel u)).run lst
          = .ok (absLevel r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ LevelWF r := by
  intro lst hrel
  cases hlk : lst.lsimpC[absLevel u]? with
  | some x =>
    -- the hit: `simplifyLM` answers the stored entry and writes nothing
    rw [cached.state_c.simplify_l_m] at h
    obtain ⟨o, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hlk', hv⟩ := lsimp_probe_refines hrel hwf hu hp
    cases o with
    | none => rw [hlk] at hlk'; simp at hlk'
    | some r0 =>
      rw [hlk] at hlk'
      simp only [Option.map_some, Option.some.injEq] at hlk'
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hwf, hv r0 rfl⟩
      rw [hlk']
      simp [ConLeche.Cached.simplifyLM, hlk]
  | none =>
    obtain ⟨hr, hwfr, hrel', hwf'⟩ := simplify_l_m_miss hrel hwf hu hlk h
    refine ⟨_, ?_, hrel', hwf', hwfr⟩
    rw [hr]
    simp [ConLeche.Cached.simplifyLM, hlk]

/-- `ConLeche/Cached/StateC.lean:251-259` — **`is_non_zero_l_m` refines
`isNonZeroLM`**: `Level.isNonZero`, persistently memoized in `lnzC`. -/
theorem is_non_zero_l_m_refines {st st' : cached.state_c.CState}
    {u : level.Level} {b : Bool} (hwf : StateWF st) (hu : LevelWF u)
    (h : cached.state_c.is_non_zero_l_m st u = ok (b, st')) :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.isNonZeroLM (absLevel u)).run lst = .ok (b, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst hrel
  rw [cached.state_c.is_non_zero_l_m] at h
  obtain ⟨o, hp, h⟩ := bind_eq_ok_iff.mp h
  have hlk := lnz_probe_refines hrel hwf hu hp
  cases o with
  | some b0 =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lst, ?_, hrel, hwf⟩
    simp [ConLeche.Cached.isNonZeroLM, ← hlk]
  | none =>
    simp only [level_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨b0, hnz, p, hins, h⟩ := h
    have hb0 : b0 = (absLevel u).isNonZero := is_non_zero_refines u b0 hnz
    obtain ⟨old, m'⟩ := p
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hrel', hwf'⟩ :=
      lnz_c_insert_refines hrel hwf hu hins
    refine ⟨_, ?_, hrel', hwf'⟩
    rw [hb0]
    simp [ConLeche.Cached.isNonZeroLM, ← hlk]

/-! ### `is_equiv_l_m`

Level equivalence with a persistent result cache: the `l == r` head test (which
writes nothing), the `eqvC` probe, then *two* `lsimpC` steps and the `leqCore`
cascade both ways.  con-leche writes the whole miss branch as one `modifyGet`
with the two `lsimpC` probes inlined; the port calls `simplify_l_m` twice.  The
three "run" lemmas below are that decomposition — `isEquivLM`'s own `run`,
branch by branch — and `eqvStep` names the tail after the two steps, so the
port's five outcomes each meet a plain value. -/

/-- The tail of `isEquivLM`'s miss branch (`StateC.lean:281-298`), after the two
inline `lsimpC` steps: the `ls == rs` test and the `leqCore` cascade both ways,
with `eqvC` written exactly where the cited function writes it (and left alone
in the two `none` outcomes). -/
def eqvStep (l r ls rs : ConLeche.Level) (s : ConLeche.Cached.CState) :
    Option Bool × ConLeche.Cached.CState :=
  if ls == rs then (some true, { s with eqvC := s.eqvC.insert (l, r) true })
  else
    match ConLeche.Level.leqCore ConLeche.Level.defaultFuel ls rs 0 with
    | some false => (some false, { s with eqvC := s.eqvC.insert (l, r) false })
    | some true =>
      match ConLeche.Level.leqCore ConLeche.Level.defaultFuel rs ls 0 with
      | some b => (some b, { s with eqvC := s.eqvC.insert (l, r) b })
      | none => (none, s)
    | none => (none, s)

/-- `ConLeche/Cached/StateC.lean:271` — the head test: equal levels are
equivalent, and no cache entry is written. -/
theorem isEquivLM_same {lst : ConLeche.Cached.CState} {l r : ConLeche.Level}
    (heq : l = r) :
    (ConLeche.Cached.isEquivLM l r).run lst = .ok (some true, lst) := by
  simp [ConLeche.Cached.isEquivLM, heq]

/-- `ConLeche/Cached/StateC.lean:273-275` — an `eqvC` hit: the stored verdict,
the state untouched. -/
theorem isEquivLM_hit {lst : ConLeche.Cached.CState} {l r : ConLeche.Level}
    {b : Bool} (hne : (l == r) = false) (hhit : lst.eqvC[(l, r)]? = some b) :
    (ConLeche.Cached.isEquivLM l r).run lst = .ok (some b, lst) := by
  simp [ConLeche.Cached.isEquivLM, hne, hhit]

/-- `ConLeche/Cached/StateC.lean:276-298` — the miss branch, its two inline
`lsimpC` probes spelled as the two `simplifyLM` steps the port makes. -/
theorem isEquivLM_miss {lst : ConLeche.Cached.CState} {l r : ConLeche.Level}
    (hne : (l == r) = false) (hmiss : lst.eqvC[(l, r)]? = none) :
    (ConLeche.Cached.isEquivLM l r).run lst
      = ((ConLeche.Cached.simplifyLM l).run lst).bind fun p =>
          ((ConLeche.Cached.simplifyLM r).run p.2).bind fun q =>
            .ok (eqvStep l r p.1 q.1 q.2) := by
  cases hl : lst.lsimpC[l]? with
  | some x =>
    cases hr : lst.lsimpC[r]? with
    | some y =>
      simp [ConLeche.Cached.isEquivLM, ConLeche.Cached.simplifyLM, eqvStep,
        hne, hmiss, hl, hr]; rfl
    | none =>
      simp [ConLeche.Cached.isEquivLM, ConLeche.Cached.simplifyLM, eqvStep,
        hne, hmiss, hl, hr]; rfl
  | none =>
    cases hr : (lst.lsimpC.insert l (ConLeche.Level.simplify l))[r]? with
    | some y =>
      simp [ConLeche.Cached.isEquivLM, ConLeche.Cached.simplifyLM, eqvStep,
        hne, hmiss, hl, hr]; rfl
    | none =>
      simp [ConLeche.Cached.isEquivLM, ConLeche.Cached.simplifyLM, eqvStep,
        hne, hmiss, hl, hr]; rfl

/-- `ConLeche/Cached/StateC.lean:270-298` — **`is_equiv_l_m` refines
`isEquivLM`**. -/
theorem is_equiv_l_m_refines {st st' : cached.state_c.CState}
    {l r : level.Level} {o : Option Bool} (hwf : StateWF st) (hl : LevelWF l)
    (hr : LevelWF r) (h : cached.state_c.is_equiv_l_m st l r = ok (o, st')) :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.isEquivLM (absLevel l) (absLevel r)).run lst
          = .ok (o, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst hrel
  rw [cached.state_c.is_equiv_l_m] at h
  obtain ⟨b, hbeq, h⟩ := bind_eq_ok_iff.mp h
  have hb := Level.beq_refines hl hr hbeq
  cases b with
  | true =>
    -- the head test: `official`'s `is_equivalent` disjunct, no cache entry
    have heq : absLevel l = absLevel r := of_decide_eq_true hb.symm
    simp only [if_true] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, isEquivLM_same heq, hrel, hwf⟩
  | false =>
    have hne : ¬ (absLevel l = absLevel r) := of_decide_eq_false hb.symm
    have hnb : (absLevel l == absLevel r) = false := by simp [hne]
    simp only [Bool.false_eq_true, if_false, level_dup_eq, bind_tc_ok] at h
    obtain ⟨oe, hprobe, h⟩ := bind_eq_ok_iff.mp h
    have hlk := eqv_probe_refines hrel hwf ⟨hl, hr⟩ hprobe
    rw [absLevelPair] at hlk
    cases oe with
    | some b0 =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lst, isEquivLM_hit hnb hlk.symm, hrel, hwf⟩
    | none =>
      -- the miss: two `lsimpC` steps, then `eqvStep`
      obtain ⟨p1, hs1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ls, st1⟩ := p1
      obtain ⟨p2, hs2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨rs, st2⟩ := p2
      obtain ⟨lst1, hrun1, hrel1, hwf1, hwfls⟩ :=
        simplify_l_m_refines hwf hl hs1 lst hrel
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwfrs⟩ :=
        simplify_l_m_refines hwf1 hr hs2 lst1 hrel1
      rw [isEquivLM_miss hnb hlk.symm, hrun1]
      simp only [Except.bind, hrun2]
      -- the five outcomes of the cascade
      obtain ⟨b1, hbeq1, h⟩ := bind_eq_ok_iff.mp h
      have hb1 := Level.beq_refines hwfls hwfrs hbeq1
      cases b1 with
      | true =>
        have heq1 : absLevel ls = absLevel rs := of_decide_eq_true hb1.symm
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨q, hins, h⟩ := h
        obtain ⟨old, m'⟩ := q
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hrel', hwf'⟩ := eqv_c_insert_refines hrel2 hwf2 ⟨hl, hr⟩ hins
        refine ⟨_, ?_, hrel', hwf'⟩
        simp only [eqvStep, beq_iff_eq, if_pos heq1]
        rfl
      | false =>
        have hne1 : ¬ (absLevel ls = absLevel rs) := of_decide_eq_false hb1.symm
        simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
        obtain ⟨fuel, hfuel, h⟩ := h
        have hfv : fuel.val = ConLeche.Level.defaultFuel := by
          rw [level.default_fuel] at hfuel; rw [← Result.ok_injective hfuel]; rfl
        obtain ⟨o1, hlc1, h⟩ := h
        have hlc1' : ConLeche.Level.leqCore ConLeche.Level.defaultFuel
            (absLevel ls) (absLevel rs) 0 = o1 := by
          have hx := Level.leq_core_refines hwfls hwfrs hlc1
          rw [hfv] at hx; simpa using hx
        cases o1 with
        | none =>
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨lst2, ?_, hrel2, hwf2⟩
          simp only [eqvStep, beq_iff_eq, if_neg hne1, hlc1']
        | some b2 =>
          cases b2 with
          | false =>
            simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
            obtain ⟨q, hins, h⟩ := h
            obtain ⟨old, m'⟩ := q
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hrel', hwf'⟩ :=
              eqv_c_insert_refines hrel2 hwf2 ⟨hl, hr⟩ hins
            refine ⟨_, ?_, hrel', hwf'⟩
            simp only [eqvStep, beq_iff_eq, if_neg hne1, hlc1']
            rfl
          | true =>
            simp only [if_true, bind_eq_ok_iff] at h
            obtain ⟨o2, hlc2, h⟩ := h
            have hlc2' : ConLeche.Level.leqCore ConLeche.Level.defaultFuel
                (absLevel rs) (absLevel ls) 0 = o2 := by
              have hx := Level.leq_core_refines hwfrs hwfls hlc2
              rw [hfv] at hx; simpa using hx
            cases o2 with
            | none =>
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨lst2, ?_, hrel2, hwf2⟩
              simp only [eqvStep, beq_iff_eq, if_neg hne1, hlc1', hlc2']
            | some b3 =>
              simp only [bind_eq_ok_iff] at h
              obtain ⟨q, hins, h⟩ := h
              obtain ⟨old, m'⟩ := q
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hrel', hwf'⟩ :=
                eqv_c_insert_refines hrel2 hwf2 ⟨hl, hr⟩ hins
              refine ⟨_, ?_, hrel', hwf'⟩
              simp only [eqvStep, beq_iff_eq, if_neg hne1, hlc1', hlc2']
              rfl

/-! ### `is_equiv_list_l_m`

Pointwise `isEquivLM`.  con-leche recurses on the two `List`s; the port recurses
on an index into the two `Vec`s, so the statement is the task-#5 index-loop one
— the conclusion on `List.drop i`, which at `i = 0` collapses to the whole list.
The arm order matters and is kept: a length mismatch answers `some false` only
*after* the common prefix has been walked, so a `none` from an earlier pair
still wins. -/

/-- `ConLeche/Cached/StateC.lean:301-302` — the empty case. -/
theorem isEquivListLM_nil {lst : ConLeche.Cached.CState} :
    (ConLeche.Cached.isEquivListLM [] []).run lst = .ok (some true, lst) := by
  simp [ConLeche.Cached.isEquivListLM]

/-- `ConLeche/Cached/StateC.lean:307` — a length mismatch, the left list
longer. -/
theorem isEquivListLM_left {lst : ConLeche.Cached.CState}
    {a : ConLeche.Level} {xs : List ConLeche.Level} :
    (ConLeche.Cached.isEquivListLM (a :: xs) []).run lst
      = .ok (some false, lst) := by
  simp [ConLeche.Cached.isEquivListLM]

/-- `ConLeche/Cached/StateC.lean:307` — a length mismatch, the right list
longer. -/
theorem isEquivListLM_right {lst : ConLeche.Cached.CState}
    {b : ConLeche.Level} {ys : List ConLeche.Level} :
    (ConLeche.Cached.isEquivListLM [] (b :: ys)).run lst
      = .ok (some false, lst) := by
  simp [ConLeche.Cached.isEquivListLM]

/-- `ConLeche/Cached/StateC.lean:303-306` — one step of the pointwise walk. -/
theorem isEquivListLM_cons {lst : ConLeche.Cached.CState}
    {a b : ConLeche.Level} {xs ys : List ConLeche.Level} :
    (ConLeche.Cached.isEquivListLM (a :: xs) (b :: ys)).run lst
      = ((ConLeche.Cached.isEquivLM a b).run lst).bind fun p =>
          match p.1 with
          | none => .ok (none, p.2)
          | some false => .ok (some false, p.2)
          | some true => (ConLeche.Cached.isEquivListLM xs ys).run p.2 := by
  simp only [ConLeche.Cached.isEquivListLM, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  cases (ConLeche.Cached.isEquivLM a b) lst with
  | error e => rfl
  | ok p => obtain ⟨o, s⟩ := p; cases o with
            | none => rfl
            | some c => cases c <;> rfl

/-- `ConLeche/Cached/StateC.lean:301-308` — **`is_equiv_list_l_m_from` refines
`isEquivListLM`** on the two suffixes at the cursor. -/
theorem is_equiv_list_l_m_from_refines {ls rs : alloc.vec.Vec level.Level}
    (hls : LevelsWF ls) (hrs : LevelsWF rs) :
    ∀ k : Nat, ∀ (i : Std.Usize) (st st' : cached.state_c.CState)
      (o : Option Bool),
      ls.val.length - i.val ≤ k → StateWF st →
      cached.state_c.is_equiv_list_l_m_from st ls rs i = ok (o, st') →
      ∀ lst, StateRel st lst → ∃ lst',
        (ConLeche.Cached.isEquivListLM ((ls.val.drop i.val).map absLevel)
            ((rs.val.drop i.val).map absLevel)).run lst = .ok (o, lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro k
  induction k with
  | zero =>
    intro i st st' o hk hwf h lst hrel
    rw [cached.state_c.is_equiv_list_l_m_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac)] at h
    by_cases hir : i.val ≥ rs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len rs by scalar_tac)] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hwf⟩
      rw [List.drop_eq_nil_of_le (show ls.val.length ≤ i.val by scalar_tac),
        List.drop_eq_nil_of_le (show rs.val.length ≤ i.val by scalar_tac)]
      exact isEquivListLM_nil
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len rs by scalar_tac),
        if_neg (show ¬ i < alloc.vec.Vec.len ls by scalar_tac)] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hwf⟩
      rw [List.drop_eq_nil_of_le (show ls.val.length ≤ i.val by scalar_tac),
        List.drop_eq_getElem_cons (show i.val < rs.val.length by scalar_tac)]
      exact isEquivListLM_right
  | succ k ih =>
    intro i st st' o hk hwf h lst hrel
    rw [cached.state_c.is_equiv_list_l_m_from.eq_def] at h; simp only [] at h
    by_cases hil : i.val ≥ ls.val.length
    · -- the left list is exhausted; the answer does not look at the state
      rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac)] at h
      by_cases hir : i.val ≥ rs.val.length
      · rw [if_pos (show i >= alloc.vec.Vec.len rs by scalar_tac)] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨lst, ?_, hrel, hwf⟩
        rw [List.drop_eq_nil_of_le (show ls.val.length ≤ i.val by scalar_tac),
          List.drop_eq_nil_of_le (show rs.val.length ≤ i.val by scalar_tac)]
        exact isEquivListLM_nil
      · rw [if_neg (show ¬ i >= alloc.vec.Vec.len rs by scalar_tac),
          if_neg (show ¬ i < alloc.vec.Vec.len ls by scalar_tac)] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨lst, ?_, hrel, hwf⟩
        rw [List.drop_eq_nil_of_le (show ls.val.length ≤ i.val by scalar_tac),
          List.drop_eq_getElem_cons (show i.val < rs.val.length by scalar_tac)]
        exact isEquivListLM_right
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len ls by scalar_tac),
        if_pos (show i < alloc.vec.Vec.len ls by scalar_tac)] at h
      have hltl : i.val < ls.val.length := by scalar_tac
      by_cases hir : i.val < rs.val.length
      · -- the common step
        rw [if_pos (show i < alloc.vec.Vec.len rs by scalar_tac)] at h
        have hmax : i.val + 1 ≤ Std.Usize.max := by
          have := ls.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        obtain ⟨y, hy, hyv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ls i hltl)
        subst hyv
        obtain ⟨z, hz, hzv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rs i hir)
        subst hzv
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hz,
          Result.ok.injEq, exists_eq_left'] at h
        obtain ⟨p, hstep, h⟩ := h
        obtain ⟨oo, st1⟩ := p
        obtain ⟨lst1, hrun, hrel1, hwf1⟩ :=
          is_equiv_l_m_refines hwf (hls _ (List.getElem_mem hltl))
            (hrs _ (List.getElem_mem hir)) hstep lst hrel
        rw [List.drop_eq_getElem_cons hltl, List.drop_eq_getElem_cons hir,
          List.map_cons, List.map_cons, isEquivListLM_cons, hrun]
        simp only [Except.bind]
        cases oo with
        | none =>
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨lst1, rfl, hrel1, hwf1⟩
        | some c =>
          cases c with
          | false =>
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨lst1, rfl, hrel1, hwf1⟩
          | true =>
            simp only [hw, bind_tc_ok] at h
            obtain ⟨lst', hrun', hrel', hwf'⟩ :=
              ih w st1 st' o (by scalar_tac) hwf1 h lst1 hrel1
            refine ⟨lst', ?_, hrel', hwf'⟩
            rw [hwv] at hrun'
            exact hrun'
      · -- the right list is exhausted first
        rw [if_neg (show ¬ i < alloc.vec.Vec.len rs by scalar_tac)] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨lst, ?_, hrel, hwf⟩
        rw [List.drop_eq_getElem_cons hltl,
          List.drop_eq_nil_of_le (show rs.val.length ≤ i.val by scalar_tac),
          List.map_cons]
        exact isEquivListLM_left

/-- `ConLeche/Cached/StateC.lean:301-308` — **`is_equiv_list_l_m` refines
`isEquivListLM`**. -/
theorem is_equiv_list_l_m_refines {st st' : cached.state_c.CState}
    {ls rs : alloc.vec.Vec level.Level} {o : Option Bool} (hwf : StateWF st)
    (hls : LevelsWF ls) (hrs : LevelsWF rs)
    (h : cached.state_c.is_equiv_list_l_m st ls rs = ok (o, st')) :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.isEquivListLM (absLevels ls) (absLevels rs)).run lst
          = .ok (o, lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst hrel
  rw [cached.state_c.is_equiv_list_l_m] at h
  have hx := is_equiv_list_l_m_from_refines hls hrs ls.val.length 0#usize st st'
    o (by scalar_tac) hwf h lst hrel
  simpa [absLevels] using hx

/-! ## `inst_list_m` and the `instC` entry cap

Bulk instantiation with the persistent result memo, keyed by the whole argument
tuple.  Three steps, in the cited order: the `bvarB ≤ d` identity (no key is
built and nothing is cached), the probe, and on a miss the **entry-bound reset**
followed by the insert.  The cap is the one place the two programs compare a
*size*: `StateC.lean:194` drops the whole map when `mp.size ≥ instCCapC` and
`inst_list_m_reset_at` when `s.inst_c.len() ≥ inst_c_cap_c`, so the two tests
must be the same test — which is what `InstCSize` supplies. -/

attribute [local simp] ConRon.Refine.State.expr_dup_eq

/-- The one `cached::expr_ops_c` fact `inst_list_m` needs: the memoised
`instantiate_list` walk refines `ExprC.instantiateList`.  **Task #51's
`Refine/ExprOpsC.lean` owns it**; it travels here as a named hypothesis so that
nothing below is weakened and nothing is duplicated. -/
def InstantiateListRefines : Prop :=
  ∀ (e : expr.Expr) (vs : alloc.vec.Vec expr.Expr) (d : Std.U64) (r : expr.Expr),
    ExprWF e → ExprsWF vs →
    cached.expr_ops_c.instantiate_list e vs d = ok r →
    absExpr r
        = ConLeche.Cached.ExprC.instantiateList (absExpr e) (absExprs vs) d.val
      ∧ ExprWF r

/-- The one `cached::expr_ops_c` fact the three level-instantiated readers need:
the memoised `inst_level_params` walk refines `ExprC.instLevelParams`.  **Task
#51's `Refine/ExprOpsC.lean` owns it** (`Refine/ExprOps.lean`'s
`instantiate_level_params_refines` is the *unmemoised* `kernel::expr_ops` twin,
the same value at a different memo policy). -/
def InstLevelParamsRefines : Prop :=
  ∀ (ks : alloc.vec.Vec name.Name) (us : alloc.vec.Vec level.Level)
    (e r : expr.Expr), NamesWF ks → LevelsWF us → ExprWF e →
    cached.expr_ops_c.inst_level_params ks us e = ok r →
    absExpr r
        = ConLeche.Cached.ExprC.instLevelParams (absNames ks) (absLevels us)
            (absExpr e)
      ∧ ExprWF r

/-- `ConLeche/Cached/StateC.lean:188-189` — the `bvarB ≤ d` identity: the same
node, by reference, and no key is built. -/
theorem instListM_id {lst : ConLeche.Cached.CState} {e : ConLeche.Expr}
    {vs : List ConLeche.Expr} {d : Nat} (hle : e.bvarB ≤ d) :
    (ConLeche.Cached.instListM e vs d).run lst = .ok (e, lst) := by
  simp [ConLeche.Cached.instListM, hle]

/-- `ConLeche/Cached/StateC.lean:190-192` — an `instC` hit. -/
theorem instListM_hit {lst : ConLeche.Cached.CState} {e r : ConLeche.Expr}
    {vs : List ConLeche.Expr} {d : Nat} (hgt : ¬ e.bvarB ≤ d)
    (hhit : lst.instC[(e, vs, d)]? = some r) :
    (ConLeche.Cached.instListM e vs d).run lst = .ok (r, lst) := by
  simp [ConLeche.Cached.instListM, hgt, hhit]

/-- `ConLeche/Cached/StateC.lean:193-197` — an `instC` miss **below** the entry
bound: the map survives and gains the new entry. -/
theorem instListM_miss_under {lst : ConLeche.Cached.CState} {e : ConLeche.Expr}
    {vs : List ConLeche.Expr} {d : Nat} (hgt : ¬ e.bvarB ≤ d)
    (hmiss : lst.instC[(e, vs, d)]? = none)
    (hcap : lst.instC.size < ConLeche.Cached.instCCapC) :
    (ConLeche.Cached.instListM e vs d).run lst
      = .ok (ConLeche.Cached.ExprC.instantiateList e vs d,
          { lst with
            instC := lst.instC.insert (e, vs, d)
              (ConLeche.Cached.ExprC.instantiateList e vs d) }) := by
  simp [ConLeche.Cached.instListM, hgt, hmiss, hcap]

/-- `ConLeche/Cached/StateC.lean:193-197` — an `instC` miss **at** the entry
bound: the map is dropped whole, so the freshly computed result is the reset
map's single entry. -/
theorem instListM_miss_over {lst : ConLeche.Cached.CState} {e : ConLeche.Expr}
    {vs : List ConLeche.Expr} {d : Nat} (hgt : ¬ e.bvarB ≤ d)
    (hmiss : lst.instC[(e, vs, d)]? = none)
    (hcap : ¬ lst.instC.size < ConLeche.Cached.instCCapC) :
    (ConLeche.Cached.instListM e vs d).run lst
      = .ok (ConLeche.Cached.ExprC.instantiateList e vs d,
          { lst with
            instC := (∅ : _root_.Std.HashMap
                (ConLeche.Expr × List ConLeche.Expr × Nat) ConLeche.Expr).insert
              (e, vs, d) (ConLeche.Cached.ExprC.instantiateList e vs d) }) := by
  simp [ConLeche.Cached.instListM, hgt, hmiss, hcap]

/-- `ConLeche/Cached/StateC.lean:194` — **the entry bound, below it**: the port
leaves the state alone exactly where con-leche keeps `mp`. -/
theorem inst_list_m_reset_under {st st' : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} (hwf : StateWF st) (hsz : InstCSize st lst)
    (hcap : lst.instC.size < ConLeche.Cached.instCCapC)
    (h : cached.state_c.inst_list_m_reset st = ok st') : st' = st := by
  rw [cached.state_c.inst_list_m_reset, cached.state_c.inst_c_cap_c] at h
  simp only [bind_tc_ok, cached.state_c.inst_list_m_reset_at,
    bind_eq_ok_iff] at h
  obtain ⟨n, hn, h⟩ := h
  have hnv := (HashMap.len_refines hwf.instCInv hn).1
  rw [if_pos (show n < 32000000#usize by
    rw [InstCSize] at hsz
    have : n.val = lst.instC.size := by rw [hnv, hsz]
    rw [ConLeche.Cached.instCCapC] at hcap
    scalar_tac)] at h
  exact (Result.ok_injective h).symm

/-- `ConLeche/Cached/StateC.lean:194` — **the entry bound, at it**: the port's
fresh table is con-leche's `{}`, and the count agrees again. -/
theorem inst_list_m_reset_over {st st' : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} (hrel : StateRel st lst) (hwf : StateWF st)
    (hsz : InstCSize st lst)
    (hcap : ¬ lst.instC.size < ConLeche.Cached.instCCapC)
    (h : cached.state_c.inst_list_m_reset st = ok st') :
    StateRel st' { lst with instC := ∅ } ∧ StateWF st' ∧
      InstCSize st' { lst with instC := ∅ } := by
  rw [cached.state_c.inst_list_m_reset, cached.state_c.inst_c_cap_c] at h
  simp only [bind_tc_ok, cached.state_c.inst_list_m_reset_at,
    bind_eq_ok_iff] at h
  obtain ⟨n, hn, h⟩ := h
  have hnv := (HashMap.len_refines hwf.instCInv hn).1
  rw [if_neg (show ¬ n < 32000000#usize by
    rw [InstCSize] at hsz
    have : n.val = lst.instC.size := by rw [hnv, hsz]
    rw [ConLeche.Cached.instCCapC] at hcap
    scalar_tac)] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m, hm, h⟩ := h
  rw [← Result.ok_injective h]
  have hsz' : (HashMap.al_v m).length
      = ({ lst with instC := ∅ } : ConLeche.Cached.CState).instC.size := by
    rw [new_alv hm]; simp
  refine ⟨{ hrel with instC := new_rel hm, instCSize := hsz' },
    { hwf with
      instCInv := new_inv hm, instCKeys := new_keys hm,
      instCVals := new_vals hm }, ?_⟩
  exact hsz'

/-- `ConLeche/Cached/StateC.lean:186-199` — **`inst_list_m` refines
`instListM`**: the head cutoff, the probe, and on a miss the entry-bound reset
followed by the insert, with the two sides' entry counts in step. -/
theorem inst_list_m_refines (hwalk : InstantiateListRefines)
    {st st' : cached.state_c.CState} {e r : expr.Expr}
    {vs : alloc.vec.Vec expr.Expr} {d : Std.U64} (hwf : StateWF st)
    (he : ExprWF e) (hvs : ExprsWF vs)
    (h : cached.state_c.inst_list_m st e vs d = ok (r, st')) :
    ∀ lst, StateRel st lst → InstCSize st lst → ∃ lst',
      (ConLeche.Cached.instListM (absExpr e) (absExprs vs) d.val).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ InstCSize st' lst' ∧ ExprWF r := by
  intro lst hrel hsz
  rw [cached.state_c.inst_list_m] at h
  obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
  have hbbv := ConRon.Refine.ExprOps.bvar_b_refines he hbb
  by_cases hle : (absExpr e).bvarB ≤ d.val
  · rw [if_pos (show bb <= d by scalar_tac)] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, instListM_id hle, hrel, hwf, hsz, he⟩
  · rw [if_neg (show ¬ bb <= d by scalar_tac)] at h
    simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok,
      bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hvv : v = vs := Env.exprs_copy_refines hv
    rw [hvv] at h
    obtain ⟨o, hprobe, h⟩ := h
    obtain ⟨hlk, hov⟩ := inst_c_probe_refines hrel hwf ⟨he, hvs⟩ hprobe
    rw [absInstKey] at hlk
    cases o with
    | some r0 =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Option.map_some] at hlk
      exact ⟨lst, instListM_hit hle hlk.symm, hrel, hwf, hsz, hov r0 rfl⟩
    | none =>
      simp only [Option.map_none] at hlk
      obtain ⟨st1, hres, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨rw1, hwalkr, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hrwv, hrww⟩ := hwalk e vs d rw1 he hvs hwalkr
      simp only [bind_eq_ok_iff] at h
      obtain ⟨q, hins, h⟩ := h
      obtain ⟨old, m'⟩ := q
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hcap : lst.instC.size < ConLeche.Cached.instCCapC
      · have hst1 : st1 = st := inst_list_m_reset_under hwf hsz hcap hres
        subst hst1
        obtain ⟨hrel', hwf'⟩ := inst_c_insert_refines hrel hwf ⟨he, hvs⟩ hrww hins
        rw [absInstKey] at hrel'
        refine ⟨{ lst with
            instC := lst.instC.insert (absExpr e, absExprs vs, d.val)
              (absExpr rw1) }, ?_, hrel', hwf', ?_, hrww⟩
        · rw [hrwv]; exact instListM_miss_under hle hlk.symm hcap
        · show (HashMap.al_v m').length = _
          exact insert_size_step instKeyKey hwf.instCInv hwf.instCKeys hrel.instC
            ⟨he, hvs⟩ hins hsz
      · obtain ⟨hrel1, hwf1, hsz1⟩ :=
          inst_list_m_reset_over hrel hwf hsz hcap hres
        obtain ⟨hrel', hwf'⟩ :=
          inst_c_insert_refines hrel1 hwf1 ⟨he, hvs⟩ hrww hins
        rw [absInstKey] at hrel'
        refine ⟨{ lst with
            instC := (∅ : _root_.Std.HashMap
                (ConLeche.Expr × List ConLeche.Expr × Nat) ConLeche.Expr).insert
              (absExpr e, absExprs vs, d.val) (absExpr rw1) },
          ?_, hrel', hwf', ?_, hrww⟩
        · rw [hrwv]; exact instListM_miss_over hle hlk.symm hcap
        · show (HashMap.al_v m').length = _
          exact insert_size_step instKeyKey hwf1.instCInv hwf1.instCKeys
            hrel1.instC ⟨he, hvs⟩ hins hsz1

/-! ## The lazy stored-constant conversions

The `ExprC` of a stored constant's type (resp. value): the cached `ienv` entry
when its `Expr` tag validates by pointer equality, else the `Expr` itself.

**The two §3.2 pointer-identity sites of this module.**  con-leche validates the
tag with `Expr.exprPtrBEq`, which is *structural* equality with a
physical-equality shortcut; `expr_ops::expr_ptr_beq` is that composition with
the shortcut modeled `false` (task #23's standing treatment, discharged by
`Refine/ExprOpsMeta.lean`'s `expr_ptr_beq_refines`).  So the model takes the
`beq` branch and answers exactly what the program answers — and the branch it
picks is unobservable anyway: `ent.ty` is by construction the conversion of
`ent.tyE`, `ExprC = Expr`, so both arms return the same value. -/

/-- `ConLeche/Cached/StateC.lean:312-320` — `storedTyIdxM` on an `ienv` **hit**,
against the type half of the entry, in exactly the shape
`state_c::ienv_ty_probe`'s refinement hands over. -/
theorem storedTyIdxM_run {lst : ConLeche.Cached.CState} {n : ConLeche.Name}
    {ty tyE tyC : ConLeche.Expr}
    (h : (lst.ienv[n]?).map (fun c => (c.tyE, c.ty)) = some (tyE, tyC)) :
    (ConLeche.Cached.storedTyIdxM n ty).run lst
      = .ok (if ConLeche.Expr.exprPtrBEq tyE ty then tyC else ty, lst) := by
  cases hx : lst.ienv[n]? with
  | none => rw [hx] at h; simp at h
  | some c =>
    obtain ⟨a, b, cv⟩ := c
    rw [hx] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [ConLeche.Cached.storedTyIdxM, hx]
    split <;> rfl

/-- `ConLeche/Cached/StateC.lean:312-320` — `storedTyIdxM` on an `ienv`
**miss**: the `Expr` itself. -/
theorem storedTyIdxM_none {lst : ConLeche.Cached.CState} {n : ConLeche.Name}
    {ty : ConLeche.Expr}
    (h : (lst.ienv[n]?).map (fun c => (c.tyE, c.ty)) = none) :
    (ConLeche.Cached.storedTyIdxM n ty).run lst = .ok (ty, lst) := by
  cases hx : lst.ienv[n]? with
  | none => simp [ConLeche.Cached.storedTyIdxM, hx]
  | some c => rw [hx] at h; simp at h

/-- `ConLeche/Cached/StateC.lean:322-330` — `storedValIdxM` where the entry
carries a value, in the shape `state_c::ienv_val_probe`'s refinement hands
over. -/
theorem storedValIdxM_run {lst : ConLeche.Cached.CState} {n : ConLeche.Name}
    {v vE vi : ConLeche.Expr}
    (h : (lst.ienv[n]?).bind (fun c => c.val) = some (vE, vi)) :
    (ConLeche.Cached.storedValIdxM n v).run lst
      = .ok (if ConLeche.Expr.exprPtrBEq vE v then vi else v, lst) := by
  cases hx : lst.ienv[n]? with
  | none => rw [hx] at h; simp at h
  | some c =>
    obtain ⟨a, b, cv⟩ := c
    cases cv with
    | none => rw [hx] at h; simp at h
    | some p =>
      obtain ⟨p1, p2⟩ := p
      rw [hx] at h
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ConLeche.Cached.storedValIdxM, hx]
      split <;> rfl

/-- `ConLeche/Cached/StateC.lean:322-330` — `storedValIdxM` where there is no
stored value (no entry, or an entry without one): the `Expr` itself. -/
theorem storedValIdxM_none {lst : ConLeche.Cached.CState} {n : ConLeche.Name}
    {v : ConLeche.Expr} (h : (lst.ienv[n]?).bind (fun c => c.val) = none) :
    (ConLeche.Cached.storedValIdxM n v).run lst = .ok (v, lst) := by
  cases hx : lst.ienv[n]? with
  | none => simp [ConLeche.Cached.storedValIdxM, hx]
  | some c =>
    obtain ⟨a, b, cv⟩ := c
    cases cv with
    | none => simp [ConLeche.Cached.storedValIdxM, hx]
    | some p => rw [hx] at h; simp at h

/-- `ConLeche/Cached/StateC.lean:312-320` — **`stored_ty_idx_m` refines
`storedTyIdxM`**.  The state is untouched, both sides. -/
theorem stored_ty_idx_m_refines {st st' : cached.state_c.CState}
    {n : name.Name} {ty r : expr.Expr} (hwf : StateWF st) (hn : NameWF n)
    (hty : ExprWF ty)
    (h : cached.state_c.stored_ty_idx_m st n ty = ok (r, st')) :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.storedTyIdxM (absName n) (absExpr ty)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst hrel
  rw [cached.state_c.stored_ty_idx_m] at h
  obtain ⟨o, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlk, hov⟩ := ienv_ty_probe_refines hrel hwf hn hp
  cases o with
  | none =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, storedTyIdxM_none (by simpa using hlk.symm), hrel, hwf, hty⟩
  | some ent =>
    obtain ⟨a, b0⟩ := ent
    obtain ⟨hwa, hwb⟩ := hov (a, b0) rfl
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv := ConRon.Refine.ExprOps.expr_ptr_beq_refines hwa hty hbb
    simp only [Option.map_some] at hlk
    cases bb with
    | true =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hwf, hwb⟩
      rw [storedTyIdxM_run hlk.symm, if_pos hbbv.symm]
    | false =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hwf, hty⟩
      rw [storedTyIdxM_run hlk.symm,
        if_neg (by simp [← hbbv] : ¬ ConLeche.Expr.exprPtrBEq (absExpr a) (absExpr ty) = true)]

/-- `ConLeche/Cached/StateC.lean:322-330` — **`stored_val_idx_m` refines
`storedValIdxM`**. -/
theorem stored_val_idx_m_refines {st st' : cached.state_c.CState}
    {n : name.Name} {v r : expr.Expr} (hwf : StateWF st) (hn : NameWF n)
    (hv : ExprWF v)
    (h : cached.state_c.stored_val_idx_m st n v = ok (r, st')) :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.storedValIdxM (absName n) (absExpr v)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst hrel
  rw [cached.state_c.stored_val_idx_m] at h
  obtain ⟨o, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hlk, hov⟩ := ienv_val_probe_refines hrel hwf hn hp
  cases o with
  | none =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, storedValIdxM_none (by simpa using hlk.symm), hrel, hwf, hv⟩
  | some ent =>
    obtain ⟨a, b0⟩ := ent
    obtain ⟨hwa, hwb⟩ := hov (a, b0) rfl
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    have hbbv := ConRon.Refine.ExprOps.expr_ptr_beq_refines hwa hv hbb
    simp only [Option.map_some] at hlk
    cases bb with
    | true =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hwf, hwb⟩
      rw [storedValIdxM_run hlk.symm, if_pos hbbv.symm]
    | false =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hwf, hv⟩
      rw [storedValIdxM_run hlk.symm,
        if_neg (by simp [← hbbv] : ¬ ConLeche.Expr.exprPtrBEq (absExpr a) (absExpr v) = true)]

/-! ## The environment reads behind the three level-instantiated readers

`const_decl_probe`, `defn_decl_probe` and `rule_rhs_probe(_from)` are the
`fe.find? …` destructurings of `constTyAtM`/`constValAtM`/`ruleRhsAtM`, factored
out as owning probes so that the index's borrow ends before the caller writes to
the state (task #14's rule).  Each answers exactly what con-leche's `match`
binds, and answers it well formed. -/

/-- `env::to_constant_val` answers a **well-formed** `ConstantVal`.  **To be
unified into `Refine/Env.lean`** beside `to_constant_val_refines`, which is the
value half; the readers below need the invariant half too. -/
theorem to_constant_val_wf {c : env.ConstantInfo} {r : env.ConstantVal}
    (hc : ConstantInfoWF c) (h : env.to_constant_val c = ok r) :
    ConstantValWF r := by
  cases c with
  | AxiomInfo v =>
    rw [env.to_constant_val] at h; rw [Env.constant_val_dup_refines h]; exact hc
  | DefnInfo v val hint =>
    rw [env.to_constant_val] at h
    rw [Env.constant_val_dup_refines h]; exact hc.1
  | ThmInfo v val =>
    rw [env.to_constant_val] at h
    rw [Env.constant_val_dup_refines h]; exact hc.1
  | IndInfo v caps =>
    rw [env.to_constant_val] at h
    rw [Env.constant_val_dup_refines h]; exact hc.1
  | CtorInfo v np nf =>
    rw [env.to_constant_val] at h
    rw [Env.constant_val_dup_refines h]; exact hc
  | RecInfo v mi rp rs =>
    rw [env.to_constant_val] at h
    rw [Env.constant_val_dup_refines h]; exact hc.1
  | ProjInfo tbl =>
    simp only [env.to_constant_val, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, v, hv, l, hl, l1, hl1, e, he, rfl⟩ := h
    refine ⟨Env.proj_table_name_wf hc.1 hn, ?_,
      ExprWF.sort (LevelWF.succ (LevelWF.zero hl) hl1) he⟩
    intro q hq
    rw [PropWhen.names_copy_val hv] at hq
    exact hc.2.1 q hq

/-- `ConLeche/Cached/StateC.lean:337-338` — **`const_decl_probe` refines the
cited `fe.find? n` followed by `ci.toConstantVal`**, at the two components the
`match` destructures. -/
theorem const_decl_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name}
    {o : Option (alloc.vec.Vec name.Name × expr.Expr)}
    (hrel : FEnv.FEnvRel fe lfe) (hwf : FEnv.FEnvWF fe) (hn : NameWF n)
    (h : cached.state_c.const_decl_probe fe n = ok o) :
    o.map (fun p => (absNames p.1, absExpr p.2))
        = (lfe.find? (absName n)).map
            (fun ci => (ci.toConstantVal.levelParams, ci.toConstantVal.type))
      ∧ ∀ p, o = some p → NamesWF p.1 ∧ ExprWF p.2 := by
  rw [cached.state_c.const_decl_probe] at h
  obtain ⟨oc, hfind, h⟩ := bind_eq_ok_iff.mp h
  have hlk := FEnv.find_refines hrel hwf hn hfind
  have hvw := FEnv.find_wf hwf hn hfind
  cases oc with
  | none =>
    simp only [Option.map_none] at hlk
    simp only [Result.ok.injEq] at h
    subst h
    exact ⟨by rw [← hlk]; rfl, by simp⟩
  | some ci =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    have hcvv := Env.to_constant_val_refines hcv
    have hcvw := to_constant_val_wf (hvw ci rfl) hcv
    refine ⟨?_, ?_⟩
    · rw [← hlk]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      rw [← hcvv]
      exact ⟨rfl, rfl⟩
    · intro p hp
      simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨hcvw.2.1, hcvw.2.2⟩

/-- `ConLeche/Cached/StateC.lean:355-356` — **`defn_decl_probe` refines the
cited `some (.defnInfo cv v _)` destructuring**. -/
theorem defn_decl_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} {o : Option (alloc.vec.Vec name.Name × expr.Expr)}
    (hrel : FEnv.FEnvRel fe lfe) (hwf : FEnv.FEnvWF fe) (hn : NameWF n)
    (h : cached.state_c.defn_decl_probe fe n = ok o) :
    o.map (fun p => (absNames p.1, absExpr p.2))
        = (lfe.find? (absName n)).bind
            (fun ci => match ci with
              | .defnInfo cv v _ => some (cv.levelParams, v)
              | _ => none)
      ∧ ∀ p, o = some p → NamesWF p.1 ∧ ExprWF p.2 := by
  rw [cached.state_c.defn_decl_probe] at h
  obtain ⟨oc, hfind, h⟩ := bind_eq_ok_iff.mp h
  have hlk := FEnv.find_refines hrel hwf hn hfind
  have hvw := FEnv.find_wf hwf hn hfind
  cases oc with
  | none =>
    simp only [Option.map_none] at hlk
    simp only [Result.ok.injEq] at h
    subst h
    exact ⟨by rw [← hlk]; rfl, by simp⟩
  | some ci =>
    have hciw := hvw ci rfl
    cases ci with
    | DefnInfo cv val hint =>
      simp only [bind_eq_ok_iff, ConRon.Refine.State.expr_dup_eq,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨ks, hks, rfl⟩ := h
      have hkv : absNames ks = absNames cv.level_params := by
        simp only [absNames]; rw [PropWhen.names_copy_val hks]
      refine ⟨?_, ?_⟩
      · rw [← hlk]
        simp [absConstantInfo, absConstantVal, hkv]
      · intro p hp
        simp only [Option.some.injEq] at hp
        subst hp
        refine ⟨?_, hciw.2⟩
        intro q hq
        rw [PropWhen.names_copy_val hks] at hq
        exact hciw.1.2.1 q hq
    | AxiomInfo cv =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | ThmInfo cv val =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | IndInfo cv caps =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | CtorInfo cv np nf =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | RecInfo cv mi rp rs =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | ProjInfo tbl =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩

/-- `ConLeche/Cached/StateC.lean:375` — **`rule_rhs_probe_from` refines the
cited `rules.find? (fun r' => r'.ctor == j)`** at its right-hand side, on the
suffix at the cursor (the task-#5 index-loop shape). -/
theorem rule_rhs_probe_from_refines {rules : alloc.vec.Vec env.RecRule}
    {j : name.Name} (hrs : RecRulesWF rules) (hj : NameWF j) :
    ∀ k : Nat, ∀ (i : Std.Usize) (o : Option expr.Expr),
      rules.val.length - i.val ≤ k →
      cached.state_c.rule_rhs_probe_from rules j i = ok o →
      o.map absExpr
          = (((rules.val.drop i.val).map absRecRule).find?
              (fun r' => r'.ctor == absName j)).map (fun rl => rl.rhs)
        ∧ ∀ r, o = some r → ExprWF r := by
  intro k
  induction k with
  | zero =>
    intro i o hk h
    rw [cached.state_c.rule_rhs_probe_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len rules by scalar_tac),
      Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (show rules.val.length ≤ i.val by scalar_tac)]
    exact ⟨rfl, by simp⟩
  | succ k ih =>
    intro i o hk h
    rw [cached.state_c.rule_rhs_probe_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ rules.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len rules by scalar_tac),
        Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (show rules.val.length ≤ i.val by scalar_tac)]
      exact ⟨rfl, by simp⟩
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len rules by scalar_tac)] at h
      have hlt : i.val < rules.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := rules.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rules i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b, hb, h⟩ := h
      have hrw := hrs _ (List.getElem_mem hlt)
      have hbv := Level.name_beq_exact hrw.1 hj hb
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.find?_cons]
      cases b with
      | true =>
        have hcond : ((absRecRule rules.val[i.val]).ctor == absName j) = true := by
          simpa [absRecRule] using hbv.symm
        simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok, if_true,
          Result.ok.injEq] at h
        subst h
        rw [hcond]
        exact ⟨rfl, fun r hr => by
          simp only [Option.some.injEq] at hr; subst hr; exact hrw.2.2⟩
      | false =>
        have hcond : ((absRecRule rules.val[i.val]).ctor == absName j) = false := by
          simpa [absRecRule] using hbv.symm
        simp only [Bool.false_eq_true, if_false, hw, bind_tc_ok] at h
        rw [hcond]
        have hrec := ih w o (by scalar_tac) h
        rw [hwv] at hrec
        exact hrec

/-- `ConLeche/Cached/StateC.lean:373-378` — **`rule_rhs_probe` refines the cited
`some (.recInfo cv _ _ rules)` destructuring followed by `rules.find?`**. -/
theorem rule_rhs_probe_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c j : name.Name} {o : Option (alloc.vec.Vec name.Name × expr.Expr)}
    (hrel : FEnv.FEnvRel fe lfe) (hwf : FEnv.FEnvWF fe) (hc : NameWF c)
    (hj : NameWF j) (h : cached.state_c.rule_rhs_probe fe c j = ok o) :
    o.map (fun p => (absNames p.1, absExpr p.2))
        = (lfe.find? (absName c)).bind
            (fun ci => match ci with
              | .recInfo cv _ _ rules =>
                (rules.find? (fun r' => r'.ctor == absName j)).map
                  (fun rl => (cv.levelParams, rl.rhs))
              | _ => none)
      ∧ ∀ p, o = some p → NamesWF p.1 ∧ ExprWF p.2 := by
  rw [cached.state_c.rule_rhs_probe] at h
  obtain ⟨oc, hfind, h⟩ := bind_eq_ok_iff.mp h
  have hlk := FEnv.find_refines hrel hwf hc hfind
  have hvw := FEnv.find_wf hwf hc hfind
  cases oc with
  | none =>
    simp only [Option.map_none] at hlk
    simp only [Result.ok.injEq] at h
    subst h
    exact ⟨by rw [← hlk]; rfl, by simp⟩
  | some ci =>
    have hciw := hvw ci rfl
    cases ci with
    | RecInfo cv mi rp rs =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨orhs, hprobe, h⟩ := h
      obtain ⟨hpv, hpw⟩ :=
        rule_rhs_probe_from_refines hciw.2 hj rs.val.length 0#usize orhs
          (by scalar_tac) hprobe
      have hpv' : orhs.map absExpr
          = ((absRecRules rs).find? (fun r' => r'.ctor == absName j)).map
              (fun rl => rl.rhs) := by
        simpa [absRecRules] using hpv
      cases hx : (absRecRules rs).find? (fun r' => r'.ctor == absName j) with
      | none =>
        rw [hx] at hpv'
        rw [absRecRules] at hx
        cases orhs with
        | some r0 => simp at hpv'
        | none =>
          simp only [Result.ok.injEq] at h
          subst h
          refine ⟨?_, by simp⟩
          rw [← hlk]
          simp only [Option.map_some, absConstantInfo, Option.bind_some, hx,
            Option.map_none]
      | some rl =>
        rw [hx] at hpv'
        rw [absRecRules] at hx
        cases orhs with
        | none => simp at hpv'
        | some rhs =>
          simp only [Option.map_some, Option.some.injEq] at hpv'
          simp only [bind_eq_ok_iff, Result.ok.injEq] at h
          obtain ⟨ks, hks, rfl⟩ := h
          have hkv : absNames ks = absNames cv.level_params := by
            simp only [absNames]; rw [PropWhen.names_copy_val hks]
          refine ⟨?_, ?_⟩
          · rw [← hlk]
            simp only [Option.map_some, absConstantInfo, Option.bind_some, hx,
              absConstantVal, hkv, hpv']
          · intro p hp
            simp only [Option.some.injEq] at hp
            subst hp
            refine ⟨?_, hpw rhs rfl⟩
            intro q hq
            rw [PropWhen.names_copy_val hks] at hq
            exact hciw.1.2.1 q hq
    | AxiomInfo cv =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | DefnInfo cv val hint =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | ThmInfo cv val =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | IndInfo cv caps =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | CtorInfo cv np nf =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩
    | ProjInfo tbl =>
      simp only [Result.ok.injEq] at h; subst h
      exact ⟨by rw [← hlk]; rfl, by simp⟩

/-! ## The three level-instantiated readers

`constTyAt`/`constValAt`/`ruleRhsAt`: the level-instantiated type, value and
recursor-rule right-hand side of a stored constant, each memoized under its own
key.  The port drops the cited `_nI`/`_cI _jI` parameters — the interned twins
the retired arena needed, already underscored in con-leche — so the statements
quantify over them. -/

/-- `ConLeche/Cached/StateC.lean:333-334` — a `constTyAt` hit. -/
theorem constTyAtM_hit {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {nI n : ConLeche.Name} {us : List ConLeche.Level} {i : ConLeche.Expr}
    (hhit : lst.constTyAt[(n, us)]? = some i) :
    (ConLeche.Cached.constTyAtM lfe nI n us).run lst = .ok (i, lst) := by
  simp [ConLeche.Cached.constTyAtM, hhit]

/-- `ConLeche/Cached/StateC.lean:335-347` — a `constTyAt` miss on a stored
constant: the lazy conversion, the level instantiation, the insert. -/
theorem constTyAtM_bind {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {nI n : ConLeche.Name} {us : List ConLeche.Level}
    {ci : ConLeche.ConstantInfo}
    (hmiss : lst.constTyAt[(n, us)]? = none) (hfind : lfe.find? n = some ci) :
    (ConLeche.Cached.constTyAtM lfe nI n us).run lst
      = ((ConLeche.Cached.storedTyIdxM n ci.toConstantVal.type).run lst).bind
          fun p =>
            .ok (ConLeche.Cached.ExprC.instLevelParams
                   ci.toConstantVal.levelParams us p.1,
                 { p.2 with
                   constTyAt := p.2.constTyAt.insert (n, us)
                     (ConLeche.Cached.ExprC.instLevelParams
                       ci.toConstantVal.levelParams us p.1) }) := by
  simp [ConLeche.Cached.constTyAtM, hmiss, hfind, ConLeche.Cached.storedTyIdxM]
  split <;> rfl

/-- `ConLeche/Cached/StateC.lean:349` — a `constTyAt` miss on a name the
environment does not know: the cited `throw (.internal …)`. -/
theorem constTyAtM_throw {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {nI n : ConLeche.Name} {us : List ConLeche.Level}
    (hmiss : lst.constTyAt[(n, us)]? = none) (hfind : lfe.find? n = none) :
    (ConLeche.Cached.constTyAtM lfe nI n us).run lst
      = .error (.internal "constTyAtM: unknown constant") := by
  simp [ConLeche.Cached.constTyAtM, hmiss, hfind]
  rfl

/-- `ConLeche/Cached/StateC.lean:352-353` — a `constValAt` hit. -/
theorem constValAtM_hit {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {nI n : ConLeche.Name} {us : List ConLeche.Level} {i : ConLeche.Expr}
    (hhit : lst.constValAt[(n, us)]? = some i) :
    (ConLeche.Cached.constValAtM lfe nI n us).run lst = .ok (i, lst) := by
  simp [ConLeche.Cached.constValAtM, hhit]

/-- `ConLeche/Cached/StateC.lean:354-365` — a `constValAt` miss on a stored
definition. -/
theorem constValAtM_bind {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {nI n : ConLeche.Name} {us : List ConLeche.Level}
    {cv : ConLeche.ConstantVal} {v : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint}
    (hmiss : lst.constValAt[(n, us)]? = none)
    (hfind : lfe.find? n = some (.defnInfo cv v hint)) :
    (ConLeche.Cached.constValAtM lfe nI n us).run lst
      = ((ConLeche.Cached.storedValIdxM n v).run lst).bind fun p =>
          .ok (ConLeche.Cached.ExprC.instLevelParams cv.levelParams us p.1,
               { p.2 with
                 constValAt := p.2.constValAt.insert (n, us)
                   (ConLeche.Cached.ExprC.instLevelParams cv.levelParams us
                     p.1) }) := by
  simp [ConLeche.Cached.constValAtM, hmiss, hfind,
    ConLeche.Cached.storedValIdxM]
  split <;> rfl

/-- `ConLeche/Cached/StateC.lean:366` — a `constValAt` miss on a name that is
not a stored definition (unknown, or known at another constructor): the cited
`| _ => throw (.internal …)`, one arm for both. -/
theorem constValAtM_throw {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {nI n : ConLeche.Name} {us : List ConLeche.Level}
    (hmiss : lst.constValAt[(n, us)]? = none)
    (hfind : (lfe.find? n).bind
        (fun ci => match ci with
          | .defnInfo cv v _ => some (cv.levelParams, v)
          | _ => none) = none) :
    (ConLeche.Cached.constValAtM lfe nI n us).run lst
      = .error (.internal "constValAtM: not a stored definition") := by
  cases hx : lfe.find? n with
  | none => simp [ConLeche.Cached.constValAtM, hmiss, hx]; rfl
  | some ci =>
    cases ci with
    | defnInfo cv v hint => rw [hx] at hfind; simp at hfind
    | _ => simp [ConLeche.Cached.constValAtM, hmiss, hx]; rfl

/-- `ConLeche/Cached/StateC.lean:370-371` — a `ruleRhsAt` hit. -/
theorem ruleRhsAtM_hit {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {cI jI c j : ConLeche.Name} {us : List ConLeche.Level} {i : ConLeche.Expr}
    (hhit : lst.ruleRhsAt[(c, j, us)]? = some i) :
    (ConLeche.Cached.ruleRhsAtM lfe cI jI c j us).run lst = .ok (i, lst) := by
  simp [ConLeche.Cached.ruleRhsAtM, hhit]

/-- `ConLeche/Cached/StateC.lean:372-386` — a `ruleRhsAt` miss on a stored
recursor with a rule for the constructor. -/
theorem ruleRhsAtM_miss {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {cI jI c j : ConLeche.Name} {us : List ConLeche.Level}
    {cv : ConLeche.ConstantVal} {mi rp : Nat}
    {rules : List ConLeche.RecRule} {rl : ConLeche.RecRule}
    (hmiss : lst.ruleRhsAt[(c, j, us)]? = none)
    (hfind : lfe.find? c = some (.recInfo cv mi rp rules))
    (hrule : rules.find? (fun r' => r'.ctor == j) = some rl) :
    (ConLeche.Cached.ruleRhsAtM lfe cI jI c j us).run lst
      = .ok (ConLeche.Cached.ExprC.instLevelParams cv.levelParams us rl.rhs,
             { lst with
               ruleRhsAt := lst.ruleRhsAt.insert (c, j, us)
                 (ConLeche.Cached.ExprC.instLevelParams cv.levelParams us
                   rl.rhs) }) := by
  simp [ConLeche.Cached.ruleRhsAtM, ConLeche.Cached.instLevelParamsM, modify,
    MonadStateOf.modifyGet, hmiss, hfind, hrule]

/-- `ConLeche/Cached/StateC.lean:387-388` — the *two* `ruleRhsAt` throws, which
the port merges into one arm (`state_c.rs:945`): `c` is not a stored recursor,
or it is one but has no rule for the constructor `j`.  Both are `.internal`,
and a refinement lemma compares only the kind, so one existential covers the
merge. -/
theorem ruleRhsAtM_throw {lst : ConLeche.Cached.CState} {lfe : ConLeche.FEnv}
    {cI jI c j : ConLeche.Name} {us : List ConLeche.Level}
    (hmiss : lst.ruleRhsAt[(c, j, us)]? = none)
    (hfind : (lfe.find? c).bind
        (fun ci => match ci with
          | .recInfo cv _ _ rules =>
            (rules.find? (fun r' => r'.ctor == j)).map
              (fun rl => (cv.levelParams, rl.rhs))
          | _ => none) = none) :
    ∃ s, (ConLeche.Cached.ruleRhsAtM lfe cI jI c j us).run lst
      = .error (.internal s) := by
  cases hx : lfe.find? c with
  | none =>
    exact ⟨"ruleRhsAtM: not a stored recursor", by
      simp [ConLeche.Cached.ruleRhsAtM, hmiss, hx]; rfl⟩
  | some ci =>
    cases ci with
    | recInfo cv mi rp rules =>
      rw [hx] at hfind
      simp only [Option.bind_some] at hfind
      cases hr : rules.find? (fun r' => r'.ctor == j) with
      | none =>
        exact ⟨"ruleRhsAtM: no rule for constructor", by
          simp [ConLeche.Cached.ruleRhsAtM, hmiss, hx, hr]; rfl⟩
      | some rl => rw [hr] at hfind; simp at hfind
    | _ =>
      exact ⟨"ruleRhsAtM: not a stored recursor", by
        simp [ConLeche.Cached.ruleRhsAtM, hmiss, hx]; rfl⟩

/-- `crates/con-ron-core/src/cached/state_c.rs:891` — **the failure half of
`const_ty_at_m`** (task #67).  The port has exactly one `Err` site here, the
unknown-constant arm, and it mirrors con-leche's one `throw` at
`ConLeche/Cached/StateC.lean:349`: both are `.internal`, and only the kind is
compared. -/
theorem const_ty_at_m_err {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {n : name.Name} {us : alloc.vec.Vec level.Level}
    {ce : core_types.CheckError} (hwf : StateWF st)
    (hfwf : FEnv.FEnvWF fe) (hn : NameWF n) (hus : LevelsWF us)
    (h : cached.state_c.const_ty_at_m st fe n us = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnv.FEnvRel fe lfe → ∀ nI,
      ErrSim ce
        ((ConLeche.Cached.constTyAtM lfe nI (absName n) (absLevels us)).run lst) := by
  intro lst lfe hrel hfrel nI
  rw [cached.state_c.const_ty_at_m] at h
  simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvv : v = us := Env.levels_copy_refines hv
  rw [hvv] at h
  obtain ⟨o, hprobe, h⟩ := h
  obtain ⟨hlk, -⟩ := const_ty_at_probe_refines hrel hwf ⟨hn, hus⟩ hprobe
  rw [absNameLevels] at hlk
  cases o with
  | some i =>
    -- the memo hit returns `.Ok`, never `.Err`
    simp at h
  | none =>
    simp only [Option.map_none] at hlk
    obtain ⟨o1, hdecl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hdv, -⟩ := const_decl_probe_refines hfrel hfwf hn hdecl
    cases o1 with
    | none =>
      -- the throwing arm: the constant is unknown on both sides
      have hfind : lfe.find? (absName n) = none := by
        cases hx : lfe.find? (absName n) with
        | none => rfl
        | some ci => rw [hx] at hdv; simp at hdv
      obtain ⟨s1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce1, hce, h⟩ := bind_eq_ok_iff.mp h
      simp only [core_types.internal, Result.ok.injEq] at hce
      subst hce
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Err.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ErrSim.internal (constTyAtM_throw hlk.symm hfind)
    | some cvp =>
      -- the stored constant is found: the arm returns `.Ok`
      exfalso
      obtain ⟨ks, ty⟩ := cvp
      obtain ⟨p, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨raw, st1⟩ := p
      obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok,
        bind_eq_ok_iff] at h
      obtain ⟨q, -, h⟩ := h
      obtain ⟨old, m'⟩ := q
      simp at h

/-- `ConLeche/Cached/StateC.lean:332-349` — **`const_ty_at_m` refines
`constTyAtM`** over its whole outcome (task #67): at `.Ok` the accept
direction, unchanged; at `.Err` the companion `const_ty_at_m_err` above, which
is where that half is proved (it does not need `hinst`, and its own call sites
do not have one).  The `match` reduces definitionally at `.Ok r`, so a call
site that knows its callee succeeded reads exactly as it did before. -/
theorem const_ty_at_m_refines (hinst : InstLevelParamsRefines)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {n : name.Name}
    {us : alloc.vec.Vec level.Level}
    {out : core.result.Result expr.Expr core_types.CheckError} (hwf : StateWF st)
    (hfwf : FEnv.FEnvWF fe) (hn : NameWF n) (hus : LevelsWF us)
    (h : cached.state_c.const_ty_at_m st fe n us = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnv.FEnvRel fe lfe → ∀ nI,
      match out with
      | .Ok r => ∃ lst',
        (ConLeche.Cached.constTyAtM lfe nI (absName n) (absLevels us)).run lst
            = .ok (absExpr r, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r
      | .Err ce =>
        ErrSim ce
          ((ConLeche.Cached.constTyAtM lfe nI (absName n) (absLevels us)).run lst) := by
  cases out with
  | Err ce =>
    exact fun lst lfe hrel hfrel nI =>
      const_ty_at_m_err hwf hfwf hn hus h lst lfe hrel hfrel nI
  | Ok r =>
    intro lst lfe hrel hfrel nI
    rw [cached.state_c.const_ty_at_m] at h
    simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hvv : v = us := Env.levels_copy_refines hv
    rw [hvv] at h
    obtain ⟨o, hprobe, h⟩ := h
    obtain ⟨hlk, hov⟩ := const_ty_at_probe_refines hrel hwf ⟨hn, hus⟩ hprobe
    rw [absNameLevels] at hlk
    cases o with
    | some i =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Option.map_some] at hlk
      exact ⟨lst, constTyAtM_hit hlk.symm, hrel, hwf, hov i rfl⟩
    | none =>
      simp only [Option.map_none] at hlk
      obtain ⟨o1, hdecl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdv, hdw⟩ := const_decl_probe_refines hfrel hfwf hn hdecl
      cases o1 with
      | none =>
        -- the port throws; nothing is claimed on failure (§3.5)
        exfalso
        obtain ⟨s1, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, -, h⟩ := bind_eq_ok_iff.mp h
        simp at h
      | some cvp =>
        obtain ⟨ks, ty⟩ := cvp
        obtain ⟨hksw, htyw⟩ := hdw (ks, ty) rfl
        -- the index read agrees
        cases hfind : lfe.find? (absName n) with
        | none => rw [hfind] at hdv; simp at hdv
        | some ci =>
          rw [hfind] at hdv
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdv
          obtain ⟨hkse, htye⟩ := hdv
          obtain ⟨p, hraw, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨raw, st1⟩ := p
          obtain ⟨lst1, hrun, hrel1, hwf1, hraww⟩ :=
            stored_ty_idx_m_refines hwf hn htyw hraw lst hrel
          obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hiv, hiw⟩ :=
            hinst ks us raw i hksw hus hraww (by rw [← inst_level_params_m_eq]; exact hi)
          simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok,
            bind_eq_ok_iff] at h
          obtain ⟨q, hins, h⟩ := h
          obtain ⟨old, m'⟩ := q
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hrel', hwf'⟩ :=
            const_ty_at_insert_refines hrel1 hwf1 ⟨hn, hus⟩ hiw hins
          rw [absNameLevels] at hrel'
          refine ⟨{ lst1 with
              constTyAt := lst1.constTyAt.insert (absName n, absLevels us)
                (absExpr i) }, ?_, hrel', hwf', hiw⟩
          rw [constTyAtM_bind hlk.symm hfind, ← htye, hrun]
          simp only [Except.bind]
          rw [hiv, ← hkse]

/-- `crates/con-ron-core/src/cached/state_c.rs:915` — **the failure half of
`const_val_at_m`** (task #67): the port's one `Err` site, the
not-a-stored-definition arm, against con-leche's one `throw` at
`ConLeche/Cached/StateC.lean:366`. -/
theorem const_val_at_m_err {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {n : name.Name} {us : alloc.vec.Vec level.Level}
    {ce : core_types.CheckError} (hwf : StateWF st)
    (hfwf : FEnv.FEnvWF fe) (hn : NameWF n) (hus : LevelsWF us)
    (h : cached.state_c.const_val_at_m st fe n us = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnv.FEnvRel fe lfe → ∀ nI,
      ErrSim ce
        ((ConLeche.Cached.constValAtM lfe nI (absName n) (absLevels us)).run lst) := by
  intro lst lfe hrel hfrel nI
  rw [cached.state_c.const_val_at_m] at h
  simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvv : v = us := Env.levels_copy_refines hv
  rw [hvv] at h
  obtain ⟨o, hprobe, h⟩ := h
  obtain ⟨hlk, -⟩ := const_val_at_probe_refines hrel hwf ⟨hn, hus⟩ hprobe
  rw [absNameLevels] at hlk
  cases o with
  | some i => simp at h
  | none =>
    simp only [Option.map_none] at hlk
    obtain ⟨o1, hdecl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hdv, -⟩ := defn_decl_probe_refines hfrel hfwf hn hdecl
    cases o1 with
    | none =>
      obtain ⟨s1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce1, hce, h⟩ := bind_eq_ok_iff.mp h
      simp only [core_types.internal, Result.ok.injEq] at hce
      subst hce
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Err.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Option.map_none] at hdv
      exact ErrSim.internal (constValAtM_throw hlk.symm hdv.symm)
    | some cvp =>
      exfalso
      obtain ⟨ks, val⟩ := cvp
      obtain ⟨p, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨raw, st1⟩ := p
      obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok,
        bind_eq_ok_iff] at h
      obtain ⟨q, -, h⟩ := h
      obtain ⟨old, m'⟩ := q
      simp at h

/-- `ConLeche/Cached/StateC.lean:351-367` — **`const_val_at_m` refines
`constValAtM`** over its whole outcome (task #67): at `.Ok` the accept
direction, unchanged; at `.Err` the companion `const_val_at_m_err` above,
which is where that half is proved (it does not need `hinst`, and its own call
sites do not have one).  The `match` reduces definitionally at `.Ok r`, so a
call site that knows its callee succeeded reads exactly as it did before. -/
theorem const_val_at_m_refines (hinst : InstLevelParamsRefines)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {n : name.Name}
    {us : alloc.vec.Vec level.Level}
    {out : core.result.Result expr.Expr core_types.CheckError} (hwf : StateWF st)
    (hfwf : FEnv.FEnvWF fe) (hn : NameWF n) (hus : LevelsWF us)
    (h : cached.state_c.const_val_at_m st fe n us = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnv.FEnvRel fe lfe → ∀ nI,
      match out with
      | .Ok r => ∃ lst',
        (ConLeche.Cached.constValAtM lfe nI (absName n) (absLevels us)).run lst
            = .ok (absExpr r, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r
      | .Err ce =>
        ErrSim ce
          ((ConLeche.Cached.constValAtM lfe nI (absName n) (absLevels us)).run lst) := by
  cases out with
  | Err ce =>
    exact fun lst lfe hrel hfrel nI =>
      const_val_at_m_err hwf hfwf hn hus h lst lfe hrel hfrel nI
  | Ok r =>
    intro lst lfe hrel hfrel nI
    rw [cached.state_c.const_val_at_m] at h
    simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hvv : v = us := Env.levels_copy_refines hv
    rw [hvv] at h
    obtain ⟨o, hprobe, h⟩ := h
    obtain ⟨hlk, hov⟩ := const_val_at_probe_refines hrel hwf ⟨hn, hus⟩ hprobe
    rw [absNameLevels] at hlk
    cases o with
    | some i =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Option.map_some] at hlk
      exact ⟨lst, constValAtM_hit hlk.symm, hrel, hwf, hov i rfl⟩
    | none =>
      simp only [Option.map_none] at hlk
      obtain ⟨o1, hdecl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdv, hdw⟩ := defn_decl_probe_refines hfrel hfwf hn hdecl
      cases o1 with
      | none =>
        exfalso
        obtain ⟨s1, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, -, h⟩ := bind_eq_ok_iff.mp h
        simp at h
      | some cvp =>
        obtain ⟨ks, val⟩ := cvp
        obtain ⟨hksw, hvalw⟩ := hdw (ks, val) rfl
        cases hfind : lfe.find? (absName n) with
        | none => rw [hfind] at hdv; simp at hdv
        | some ci =>
          rw [hfind] at hdv
          cases ci with
          | defnInfo cv v0 hint =>
            simp only [Option.map_some, Option.bind_some, Option.some.injEq,
              Prod.mk.injEq] at hdv
            obtain ⟨hkse, hvale⟩ := hdv
            obtain ⟨p, hraw, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨raw, st1⟩ := p
            obtain ⟨lst1, hrun, hrel1, hwf1, hraww⟩ :=
              stored_val_idx_m_refines hwf hn hvalw hraw lst hrel
            obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hiv, hiw⟩ :=
              hinst ks us raw i hksw hus hraww
                (by rw [← inst_level_params_m_eq]; exact hi)
            simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok,
              bind_eq_ok_iff] at h
            obtain ⟨q, hins, h⟩ := h
            obtain ⟨old, m'⟩ := q
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hrel', hwf'⟩ :=
              const_val_at_insert_refines hrel1 hwf1 ⟨hn, hus⟩ hiw hins
            rw [absNameLevels] at hrel'
            refine ⟨{ lst1 with
                constValAt := lst1.constValAt.insert (absName n, absLevels us)
                  (absExpr i) }, ?_, hrel', hwf', hiw⟩
            rw [constValAtM_bind hlk.symm hfind, ← hvale, hrun]
            simp only [Except.bind]
            rw [hiv, ← hkse]
          | axiomInfo cv0 => simp at hdv
          | thmInfo cv0 v0 => simp at hdv
          | indInfo cv0 caps => simp at hdv
          | ctorInfo cv0 np nf => simp at hdv
          | recInfo cv0 mi rp rules => simp at hdv
          | projInfo tbl => simp at hdv

/-- `ConLeche/Cached/StateC.lean:369-388` — **`rule_rhs_at_m` refines
`ruleRhsAtM`** on success. -/
theorem rule_rhs_at_m_refines (hinst : InstLevelParamsRefines)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {c j : name.Name}
    {us : alloc.vec.Vec level.Level} {r : expr.Expr} (hwf : StateWF st)
    (hfwf : FEnv.FEnvWF fe) (hc : NameWF c) (hj : NameWF j) (hus : LevelsWF us)
    (h : cached.state_c.rule_rhs_at_m st fe c j us = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnv.FEnvRel fe lfe → ∀ cI jI, ∃ lst',
      (ConLeche.Cached.ruleRhsAtM lfe cI jI (absName c) (absName j)
            (absLevels us)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst lfe hrel hfrel cI jI
  rw [cached.state_c.rule_rhs_at_m] at h
  simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvv : v = us := Env.levels_copy_refines hv
  rw [hvv] at h
  obtain ⟨o, hprobe, h⟩ := h
  obtain ⟨hlk, hov⟩ :=
    rule_rhs_at_probe_refines hrel hwf ⟨hc, hj, hus⟩ hprobe
  rw [absNameNameLevels] at hlk
  cases o with
  | some i =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Option.map_some] at hlk
    exact ⟨lst, ruleRhsAtM_hit hlk.symm, hrel, hwf, hov i rfl⟩
  | none =>
    simp only [Option.map_none] at hlk
    obtain ⟨o1, hdecl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hdv, hdw⟩ := rule_rhs_probe_refines hfrel hfwf hc hj hdecl
    cases o1 with
    | none =>
      exfalso
      obtain ⟨s1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, -, h⟩ := bind_eq_ok_iff.mp h
      simp at h
    | some cvp =>
      obtain ⟨ks, rhs⟩ := cvp
      obtain ⟨hksw, hrhsw⟩ := hdw (ks, rhs) rfl
      cases hfind : lfe.find? (absName c) with
      | none => rw [hfind] at hdv; simp at hdv
      | some ci =>
        rw [hfind] at hdv
        cases ci with
        | recInfo cv mi rp rules =>
          simp only [Option.map_some, Option.bind_some] at hdv
          cases hrule : rules.find? (fun r' => r'.ctor == absName j) with
          | none =>
            rw [hrule] at hdv
            simp at hdv
          | some rl =>
            rw [hrule] at hdv
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdv
            obtain ⟨hkse, hrhse⟩ := hdv
            obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hiv, hiw⟩ :=
              hinst ks us rhs i hksw hus hrhsw
                (by rw [← inst_level_params_m_eq]; exact hi)
            simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok,
              bind_eq_ok_iff] at h
            obtain ⟨q, hins, h⟩ := h
            obtain ⟨old, m'⟩ := q
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hrel', hwf'⟩ :=
              rule_rhs_at_insert_refines hrel hwf ⟨hc, hj, hus⟩ hiw hins
            rw [absNameNameLevels] at hrel'
            refine ⟨{ lst with
                ruleRhsAt := lst.ruleRhsAt.insert
                  (absName c, absName j, absLevels us) (absExpr i) },
              ?_, hrel', hwf', hiw⟩
            rw [ruleRhsAtM_miss hlk.symm hfind hrule, hiv, ← hkse, ← hrhse]
        | axiomInfo cv0 => simp at hdv
        | defnInfo cv0 v0 hint => simp at hdv
        | thmInfo cv0 v0 => simp at hdv
        | indInfo cv0 caps => simp at hdv
        | ctorInfo cv0 np nf => simp at hdv
        | projInfo tbl => simp at hdv

/-- `crates/con-ron-core/src/cached/state_c.rs:945` — **the failure half of
`rule_rhs_at_m`** (task #67).  The port's one `Err` site merges con-leche's
*two* `throw`s, `ConLeche/Cached/StateC.lean:387` ("no rule for constructor")
and `:388` ("not a stored recursor"); both are `.internal`, so the merge is
invisible to a statement that compares only the kind. -/
theorem rule_rhs_at_m_err {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {c j : name.Name} {us : alloc.vec.Vec level.Level}
    {ce : core_types.CheckError} (hwf : StateWF st)
    (hfwf : FEnv.FEnvWF fe) (hc : NameWF c) (hj : NameWF j) (hus : LevelsWF us)
    (h : cached.state_c.rule_rhs_at_m st fe c j us = ok (.Err ce, st')) :
    ∀ lst lfe, StateRel st lst → FEnv.FEnvRel fe lfe → ∀ cI jI,
      ErrSim ce
        ((ConLeche.Cached.ruleRhsAtM lfe cI jI (absName c) (absName j)
          (absLevels us)).run lst) := by
  intro lst lfe hrel hfrel cI jI
  rw [cached.state_c.rule_rhs_at_m] at h
  simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvv : v = us := Env.levels_copy_refines hv
  rw [hvv] at h
  obtain ⟨o, hprobe, h⟩ := h
  obtain ⟨hlk, -⟩ :=
    rule_rhs_at_probe_refines hrel hwf ⟨hc, hj, hus⟩ hprobe
  rw [absNameNameLevels] at hlk
  cases o with
  | some i => simp at h
  | none =>
    simp only [Option.map_none] at hlk
    obtain ⟨o1, hdecl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hdv, -⟩ := rule_rhs_probe_refines hfrel hfwf hc hj hdecl
    cases o1 with
    | none =>
      obtain ⟨s1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce1, hce, h⟩ := bind_eq_ok_iff.mp h
      simp only [core_types.internal, Result.ok.injEq] at hce
      subst hce
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Err.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Option.map_none] at hdv
      obtain ⟨s, hs⟩ := ruleRhsAtM_throw hlk.symm hdv.symm
      exact ErrSim.internal hs
    | some cvp =>
      exfalso
      obtain ⟨ks, rhs⟩ := cvp
      obtain ⟨i, -, h⟩ := bind_eq_ok_iff.mp h
      simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok,
        bind_eq_ok_iff] at h
      obtain ⟨q, -, h⟩ := h
      obtain ⟨old, m'⟩ := q
      simp at h

/-! ## The flush and the converted-constant record -/

/-- `ConLeche/Cached/StateC.lean:400` — `flushC` is `modify (·.flushed)`. -/
theorem flushC_run {lst : ConLeche.Cached.CState} :
    (ConLeche.Cached.flushC).run lst = .ok ((), lst.flushed) := by
  simp [ConLeche.Cached.flushC, modify, MonadStateOf.modifyGet]

/-- `ConLeche/Cached/StateC.lean:400` — **`flush_c` refines `flushC`**: the ten
environment-dependent tables become fresh, the four environment-independent ones
(`ienv` and the three level memos) survive, and the `instC` count is again in
step (both sides are empty). -/
theorem flush_c_refines {st st' : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} (hrel : StateRel st lst) (hwf : StateWF st)
    (h : cached.state_c.flush_c st = ok st') :
    (ConLeche.Cached.flushC).run lst = .ok ((), lst.flushed) ∧
      StateRel st' lst.flushed ∧ StateWF st' ∧ InstCSize st' lst.flushed := by
  rw [cached.state_c.flush_c] at h
  obtain ⟨hrel', hwf'⟩ := flushed_refines hrel hwf h
  refine ⟨flushC_run, hrel', hwf', ?_⟩
  -- the count: `flushed` gives `instC` a fresh table on both sides
  rw [cached.state_c.flushed] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨m0, h0, m1, h1, m2, h2, m3, h3, m4, h4, hst⟩ := h
  subst hst
  show (HashMap.al_v m4).length = _
  rw [new_alv h4]
  simp [ConLeche.Cached.CState.flushed]

/-- The fresh state's `instC` count agrees with con-leche's (both empty).  The
relation and the invariant are `State.lean`'s `cstate_new_refines`; this is the
`InstCSize` clause that file does not carry. -/
theorem cstate_new_size {st : cached.state_c.CState}
    (h : cached.state_c.cstate_new = ok st) :
    InstCSize st ({} : ConLeche.Cached.CState) := by
  rw [cached.state_c.cstate_new] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨m0, h0, m1, h1, m2, h2, m3, h3, m4, h4, m5, h5, m6, h6, m7, h7,
    m8, h8, hst⟩ := h
  subst hst
  show (HashMap.al_v m8).length = _
  rw [new_alv h8]
  simp

/-- `ConLeche/Cached/StateC.lean:455-460` — `recordCConst` is
`modify (ienv := … .insert …)`. -/
theorem recordCConst_run {lst : ConLeche.Cached.CState} {n : ConLeche.Name}
    {tyE ty : ConLeche.Expr}
    {val : Option (ConLeche.Expr × ConLeche.Cached.ExprC)} :
    (ConLeche.Cached.recordCConst n tyE ty val).run lst
      = .ok ((), { lst with ienv := lst.ienv.insert n ⟨tyE, ty, val⟩ }) := by
  simp [ConLeche.Cached.recordCConst, modify, MonadStateOf.modifyGet]

/-- `ConLeche/Cached/StateC.lean:455-460` — **`record_c_const` refines
`recordCConst`**: the accepted constant's converted type/value, tagged with the
very `Expr` objects pushed into the environment. -/
theorem record_c_const_refines {st st' : cached.state_c.CState}
    {n : name.Name} {ty_e ty : expr.Expr}
    {val : Option (expr.Expr × expr.Expr)} (hwf : StateWF st) (hn : NameWF n)
    (hty_e : ExprWF ty_e) (hty : ExprWF ty)
    (hval : ∀ p, val = some p → ExprWF p.1 ∧ ExprWF p.2)
    (h : cached.state_c.record_c_const st n ty_e ty val = ok st') :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.recordCConst (absName n) (absExpr ty_e) (absExpr ty)
            (val.map (fun p => (absExpr p.1, absExpr p.2)))).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst hrel
  rw [cached.state_c.record_c_const] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨q, hins, h⟩ := h
  obtain ⟨old, m'⟩ := q
  simp at h
  subst h
  obtain ⟨hrel', hwf'⟩ :=
    ienv_insert_refines hrel hwf hn ⟨hty_e, hty, hval⟩ hins
  exact ⟨_, recordCConst_run, hrel', hwf'⟩

/-! ## `subst_level_trees`

`substLevelTreesM`'s body is `pure (ls.map (Level.subst ks us))`, so the port is
the plain function; it builds the result `Vec` with an index loop, so the
statement is again the task-#5 one on `List.drop i` with the accumulator in
front. -/

/-- `ConLeche/Cached/StateC.lean:233-236` — the index loop of
`subst_level_trees`: the accumulator followed by `Level.subst` on the suffix at
the cursor. -/
theorem subst_level_trees_from_val {ks : alloc.vec.Vec name.Name}
    {us ls : alloc.vec.Vec level.Level} (hks : NamesWF ks) (hus : LevelsWF us)
    (hls : LevelsWF ls) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec level.Level),
      ls.val.length - i.val ≤ k → LevelsWF out →
      cached.state_c.subst_level_trees_from ks us ls i out = ok v →
      absLevels v = absLevels out ++ (ls.val.drop i.val).map
          (fun l => ConLeche.Level.subst (absNames ks) (absLevels us)
            (absLevel l))
        ∧ LevelsWF v := by
  intro k
  induction k with
  | zero =>
    intro i out v hk hout h
    rw [cached.state_c.subst_level_trees_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac),
      Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (show ls.val.length ≤ i.val by scalar_tac)]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out v hk hout h
    rw [cached.state_c.subst_level_trees_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ ls.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ls by scalar_tac),
        Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (show ls.val.length ≤ i.val by scalar_tac)]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len ls by scalar_tac)] at h
      have hlt : i.val < ls.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := ls.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ls i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨l1, hl1, out1, hout1, h⟩ := h
      obtain ⟨hl1v, hl1w⟩ :=
        Level.subst_refines (hls _ (List.getElem_mem hlt)) hks hus hl1
      have hout1w : LevelsWF out1 := by
        intro x hx
        rw [vec_push_val hout1] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hout x hx'
        · simp only [List.mem_singleton] at hx'; rw [hx']; exact hl1w
      obtain ⟨hv, hvw⟩ := ih w out1 v (by scalar_tac) hout1w h
      refine ⟨?_, hvw⟩
      rw [hv, hwv, absLevels, absLevels, vec_push_val hout1,
        List.drop_eq_getElem_cons hlt]
      simp only [hl1v, absLevels, absNames, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- `ConLeche/Cached/StateC.lean:233-236` — `substLevelTreesM`'s body is
`pure (…)`, so its `run` writes nothing. -/
theorem substLevelTreesM_run {lst : ConLeche.Cached.CState}
    {ks : List ConLeche.Name} {us ls : List ConLeche.Level} :
    (ConLeche.Cached.substLevelTreesM ks us ls).run lst
      = .ok (ls.map (ConLeche.Level.subst ks us), lst) := by
  simp [ConLeche.Cached.substLevelTreesM]

/-- `ConLeche/Cached/StateC.lean:233-236` — **`subst_level_trees` refines
`substLevelTreesM`**. -/
theorem subst_level_trees_refines {ks : alloc.vec.Vec name.Name}
    {us ls v : alloc.vec.Vec level.Level} (hks : NamesWF ks) (hus : LevelsWF us)
    (hls : LevelsWF ls)
    (h : cached.state_c.subst_level_trees ks us ls = ok v) :
    ∀ lst, (ConLeche.Cached.substLevelTreesM (absNames ks) (absLevels us)
          (absLevels ls)).run lst
        = .ok (absLevels v, lst)
      ∧ LevelsWF v := by
  intro lst
  rw [cached.state_c.subst_level_trees] at h
  obtain ⟨hv, hvw⟩ :=
    subst_level_trees_from_val hks hus hls ls.val.length 0#usize _ v
      (by scalar_tac) (by intro x hx; simp [alloc.vec.Vec.new] at hx) h
  refine ⟨?_, hvw⟩
  rw [substLevelTreesM_run, hv]
  simp [absLevels, alloc.vec.Vec.new]

/-! ## One ingredient discharged

Task #51 landed while this file was being written, so one of the two named
`cached::expr_ops_c` ingredients can be closed here and now:
`Refine/ExprOpsCAbs.lean`'s `inst_level_params_refines` *is*
`InstLevelParamsRefines`.  `InstantiateListRefines` stays a hypothesis: task
#51's `instantiate_list_refines` is one of that task's open `sorry`s, and
nothing here should depend on it. -/

/-- `Refine/ExprOpsCAbs.lean` discharges `InstLevelParamsRefines`, so the three
level-instantiated readers can be applied unconditionally. -/
theorem instLevelParamsRefines : InstLevelParamsRefines :=
  fun _ks _us _e _r hks hus he h =>
    ExprOpsC.inst_level_params_refines hks hus he h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Lean's own three and nothing else: no `sorry`, nothing from Aeneas's library,
nothing from the `Arc` models, nothing from `native_decide`.
`Classical.choice` comes in through `DecidableEq` on the generated key types,
which every `decide (a = b)` inside `Eq2Fwd`, `toFun` and `RelOn` goes
through (`Refine/State.lean`'s census says the same). -/

/-- info: 'ConRon.Refine.StateC.instLevelParamsRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms instLevelParamsRefines

/-- info: 'ConRon.Refine.StateC.is_equiv_l_m_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_equiv_l_m_refines

/-- info: 'ConRon.Refine.StateC.inst_list_m_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inst_list_m_refines

/-- info: 'ConRon.Refine.StateC.const_ty_at_m_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms const_ty_at_m_refines

/-- info: 'ConRon.Refine.StateC.rule_rhs_at_m_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_rhs_at_m_err

end ConRon.Refine.StateC
