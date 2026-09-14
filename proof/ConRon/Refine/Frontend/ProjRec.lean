import ConRon.Refine.Frontend.Base
import ConRon.Refine.ExprOpsCSubst
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.IndStructParts
import ConRon.Refine.CoreKNames

/-! # The projection rewrite, well formed (task #85, phase 1)

`frontend::proj_rec` is one of the two places on the parse path that *builds* a
term instead of reading one.  The elaborator spells a structure's projection
function as `fun p⃗ self => .proj T i self`; this checker serves `.proj` only on
the class its direct install recognises, so for a *mutual* (non-direct)
structure-like owner the parse rewrites the value into the owner's recursor
applied to a motive vector, a minor vector and the subject:

    fun p⃗ self => T.rec.{ℓ, u⃗} p⃗ motives minors self

`proj_rec_value` is that rewrite and its answer is stored in a
`DefnDecl`/`ThmDecl`, so `Refine/Main.lean`'s `hds` needs it well formed.  This
file proves it, in the DESIGN.md §3.5 shape: every node the rewrite builds goes
through `expr::lam`/`expr::mk_const`/`expr::mk_bvar`/`level::param`, which
*are* the constructors of `ExprWF`/`LevelWF`, so the proof is bookkeeping — the
binder lists, the accumulators and the two `MkBinder` dictionaries — and never
names a hash formula.

`proj_rec_owners` is the census that produces the `ProjRecOwner` records the
rewrite reads; its lemma is what `export_c::register_proj_owners` needs to
establish `Frontend/Base.lean`'s `ProjRecOwnerWF` for `StateDWF.proj_owners`.

## What carries no clause

The module's recognisers — `cps_starts_with`, `is_proj_iota_name`,
`occurs_const_fast`/`occurs_const_go`/`occurs_const_node`, `any_name_mentions`,
`any_dom_mentions`, `any_ctor_mentions`, `any_is_rec`, `head_is`, `find_ctor`,
`find_rec`, `type_names` — return a `bool`, an index or a list of names *copied
out of their input*.  None of them builds a term, so none of them owes a
well-formedness lemma.  `find_ctor`/`find_rec` hand back an *index*, and the
one thing their caller needs of it — that `recs[j]` is one of `recs` — is
`slice_index_mem` below, not a lemma about `find_rec`.

The four machine-word fields of `ProjRecOwner` (`n_p`, `n_f`, `num_motives`,
`num_minors`) and of the three census records carry no clause for the same
reason: a `u64` has no invariant.

## How these were proved

The task-#71 idiom (`Refine/README.md`) fits this file almost everywhere: the
shape step is `ExprWF.ind_node` for the two walks on a term (`strip_pis_all`,
`lam_body`) and a strong induction on the `while` shape's `Nat` measure for the
eight index recursions, and `rw [f.eq_def] at h; rust_norm h` does the rest —
`rust_norm` alone disposes of the nine dead `match` arms of every node
dispatch, and of the `Option`/`Result` plumbing of the two `MkBinder`
implementations.  What it does *not* do is name the witnesses it introduces, so
most proofs here are a `rename_i` followed by three or four forward steps;
`rust_grind` is not used, the goals after `rust_norm` being single
constructor applications rather than simulation statements.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## The census records -/

/-- `proj_rec::ProjTypeRec`: the export's own shape data for one block member
(`ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners`).  `n_p`, `n_i` and
`is_rec` are a machine word and a flag. -/
def ProjTypeRecWF (t : frontend.proj_rec.ProjTypeRec) : Prop :=
  NameWF t.name ∧ NamesWF t.lps ∧ ExprWF t.ty ∧ NamesWF t.ctors

/-- `proj_rec::ProjCtorRec` (`ProjRec.lean:332-370`). -/
def ProjCtorRecWF (c : frontend.proj_rec.ProjCtorRec) : Prop :=
  NameWF c.name ∧ ExprWF c.ty

/-- `proj_rec::ProjRecRec` (`ProjRec.lean:332-370`). -/
def ProjRecRecWF (r : frontend.proj_rec.ProjRecRec) : Prop :=
  NameWF r.name ∧ NamesWF r.lps ∧ ExprWF r.ty

/-! ## Indexing helpers

`Refine/ExprOps.lean`'s `vec_index_expr` and `Refine/CoreKVec.lean`'s
`vec_index_leaf` both carry an abstraction clause this file has no use for, so
the membership half is restated once, generically, for a `Vec` and for a
`Slice`. -/

/-- `Vec::index` when it succeeds: the element is one of the vector's. -/
theorem vec_index_mem {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length ∧ x ∈ v.val := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < v.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  refine ⟨hlt, ?_⟩
  have hx : v.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  rw [← hx]; exact List.getElem_mem hlt

/-- `Slice::index_usize` when it succeeds: the element is one of the slice's. -/
theorem slice_index_mem {α : Type} {s : Slice α} {i : Std.Usize} {x : α}
    (h : Slice.index_usize s i = ok x) : i.val < s.val.length ∧ x ∈ s.val := by
  have hg := slice_index_getElem? h
  have hlt : i.val < s.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  refine ⟨hlt, ?_⟩
  have hx : s.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  rw [← hx]; exact List.getElem_mem hlt


/-! ## The accumulators and the small builders

Four index recursions that only ever copy or build: `partial_fixpoint` gives no
induction principle, so each is a strong induction on the `Nat` measure the
`while` shape supplies (`n - i` upward, `i` downward). -/

/-- `proj_rec::one_level` — Lean's `[ℓ]`, a one-element level list. -/
theorem one_level_wf {l : level.Level} {us : alloc.vec.Vec level.Level}
    (hl : LevelWF l) (h : frontend.proj_rec.one_level l = ok us) : LevelsWF us := by
  rw [frontend.proj_rec.one_level] at h
  simp only [level_dup_eq, bind_tc_ok] at h
  have hv : us.val = [l] := by rw [vec_push_val h]; simp
  intro u hu
  rw [hv] at hu; simp only [List.mem_singleton] at hu; rw [hu]; exact hl

/-- The index recursion behind `proj_rec::append_levels`. -/
theorem append_levels_loop_wf (N : Nat) :
    ∀ (us out r : alloc.vec.Vec level.Level) (n i : Std.Usize),
      us.val.length - i.val = N → LevelsWF us → LevelsWF out →
      frontend.proj_rec.append_levels_loop us out n i = ok r → LevelsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro us out r n i hN hus hout h
    rw [frontend.proj_rec.append_levels_loop.eq_def] at h
    split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨l, hidx, l1, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      obtain ⟨hlt, hmem⟩ := vec_index_mem hidx
      rw [level_dup_eq] at hdup
      have hl1 : l1 = l := (Result.ok_injective hdup).symm
      have hout1 : LevelsWF out1 := by
        intro u hu
        rw [vec_push_val hpush] at hu
        rcases List.mem_append.1 hu with h1 | h1
        · exact hout u h1
        · simp only [List.mem_singleton] at h1; rw [h1, hl1]; exact hus l hmem
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      exact ih (us.val.length - i2.val) (by omega) us out1 r n i2 rfl hus hout1 hrec
    · rw [← Result.ok_injective h]; exact hout

/-- `proj_rec::append_levels` — Lean's `ℓ :: us` as an accumulator append. -/
theorem append_levels_wf {out us r : alloc.vec.Vec level.Level}
    (hout : LevelsWF out) (hus : LevelsWF us)
    (h : frontend.proj_rec.append_levels out us = ok r) : LevelsWF r := by
  rw [frontend.proj_rec.append_levels] at h
  exact append_levels_loop_wf _ us out r _ 0#usize rfl hus hout h

/-- The index recursion behind `proj_rec::append_exprs`. -/
theorem append_exprs_loop_wf (N : Nat) :
    ∀ (xs out r : alloc.vec.Vec expr.Expr) (n i : Std.Usize),
      xs.val.length - i.val = N → ExprsWF xs → ExprsWF out →
      frontend.proj_rec.append_exprs_loop xs out n i = ok r → ExprsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs out r n i hN hxs hout h
    rw [frontend.proj_rec.append_exprs_loop.eq_def] at h
    split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨e, hidx, e1, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      obtain ⟨hlt, hmem⟩ := vec_index_mem hidx
      have he1 : e1 = e := Expr.dup_eq hdup
      have hout1 : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hpush] at hx
        rcases List.mem_append.1 hx with h1 | h1
        · exact hout x h1
        · simp only [List.mem_singleton] at h1; rw [h1, he1]; exact hxs e hmem
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      exact ih (xs.val.length - i2.val) (by omega) xs out1 r n i2 rfl hxs hout1 hrec
    · rw [← Result.ok_injective h]; exact hout

/-- `proj_rec::append_exprs` — Lean's `xs ++ ys` on the recursor's spine. -/
theorem append_exprs_wf {out xs r : alloc.vec.Vec expr.Expr}
    (hout : ExprsWF out) (hxs : ExprsWF xs)
    (h : frontend.proj_rec.append_exprs out xs = ok r) : ExprsWF r := by
  rw [frontend.proj_rec.append_exprs] at h
  exact append_exprs_loop_wf _ xs out r _ 0#usize rfl hxs hout h

/-- The countdown behind `proj_rec::bvar_params`. -/
theorem bvar_params_loop_wf (N : Nat) :
    ∀ (n_p : Std.U64) (out r : alloc.vec.Vec expr.Expr) (k : Std.U64),
      n_p.val - k.val = N → ExprsWF out →
      frontend.proj_rec.bvar_params_loop n_p out k = ok r → ExprsWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n_p out r k hN hout h
    rw [frontend.proj_rec.bvar_params_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : k.val < n_p.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, e, he, out1, hpush, k1, hk1, hrec⟩ := h
      have hout1 : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hpush] at hx
        rcases List.mem_append.1 hx with h1 | h1
        · exact hout x h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact Expr.mk_bvar_wf he
      have hk1v : k1.val = k.val + 1 := HashMap.uscalar_add_eq hk1
      exact ih (n_p.val - k1.val) (by omega) n_p out1 r k1 rfl hout1 hrec
    · rw [← Result.ok_injective h]; exact hout

/-- `proj_rec::bvar_params` — the cited `(List.range o.nP).map fun k =>
Expr.bvar (o.nP - k)` (`ConLeche/Frontend/ProjRec.lean:279-330 projRecValue`).
Every entry is an `expr::mk_bvar`, which is `ExprWF`'s `bvar` constructor. -/
theorem bvar_params_wf {n_p : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (h : frontend.proj_rec.bvar_params n_p = ok r) : ExprsWF r := by
  rw [frontend.proj_rec.bvar_params] at h
  simp only [lift_eq, bind_tc_ok] at h
  refine bvar_params_loop_wf _ n_p _ r 0#u64 rfl (fun x hx => ?_) h
  simp at hx

/-- The countdown behind `proj_rec::mk_lams`. -/
theorem mk_lams_loop_wf (N : Nat) :
    ∀ (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (acc r : expr.Expr)
      (i : Std.Usize),
      i.val = N → ExprOps.BindersWF bs → ExprWF acc →
      frontend.proj_rec.mk_lams_loop bs acc i = ok r → ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bs acc r i hN hbs hacc h
    rw [frontend.proj_rec.mk_lams_loop.eq_def] at h
    split at h
    · rename_i hgt
      have hgtv : 0 < i.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, p, hidx, h⟩ := h
      obtain ⟨-, hmem⟩ := vec_index_mem hidx
      obtain ⟨hp1, hp2⟩ := hbs p hmem
      obtain ⟨e, bm⟩ := p
      -- `cases` on the pair leaves the matcher unreduced, so the last three
      -- binds are inverted by hand rather than by `simp`.
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bm1, hbm, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨acc1, hlam, hrec⟩ := bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val - 1 := HashMap.uscalar_sub_eq hi1
      refine ih i1.val (by omega) bs acc1 r i1 rfl hbs ?_ hrec
      rw [Expr.dup_eq hdup] at hlam
      rw [Expr.binder_meta_dup_eq hbm] at hlam
      exact Expr.lam_wf hp1 hacc hp2 hlam
    · rw [← Result.ok_injective h]; exact hacc

/-- `proj_rec::mk_lams` (`ConLeche/Frontend/ProjRec.lean:247-249 mkLams`):
rebuild a `λ`-telescope over a binder list. -/
theorem mk_lams_wf {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {body r : expr.Expr}
    (hbs : ExprOps.BindersWF bs) (hbody : ExprWF body)
    (h : frontend.proj_rec.mk_lams bs body = ok r) : ExprWF r := by
  rw [frontend.proj_rec.mk_lams] at h
  exact mk_lams_loop_wf _ bs body r _ rfl hbs hbody h

/-! ## The telescope walkers

`strip_pis_all` recurses on the *subterm*, so its lemma is an induction on the
`ExprWF` derivation (`ExprWF.ind_node`, the task-#71 shape step);
`inst_pis_open` and `build_binders` count down a `u64`, so theirs is a strong
induction on a `Nat` measure.  All three loops carry a `bool` that turns the
`while` into its own exit, and each gets a one-line "the exit really is the
exit" lemma so that the measure need not track the flag. -/

/-- `strip_pis_all`'s loop at `more = false` is its own exit. -/
theorem strip_pis_all_loop_false {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {cur : expr.Expr} {r : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr}
    (h : frontend.proj_rec.strip_pis_all_loop bs cur false = ok r) : r = (bs, cur) := by
  rw [frontend.proj_rec.strip_pis_all_loop.eq_def] at h
  split at h
  · rename_i hc; simp at hc
  · exact (Result.ok_injective h).symm

/-- The spine walk behind `proj_rec::strip_pis_all`. -/
theorem strip_pis_all_loop_wf (cur : expr.Expr) (hcur : ExprWF cur) :
    ∀ (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (more : Bool)
      (r : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr),
      ExprOps.BindersWF bs →
      frontend.proj_rec.strip_pis_all_loop bs cur more = ok r →
      ExprOps.BindersWF r.1 ∧ ExprWF r.2 := by
  induction cur, hcur using ExprWF.ind_node with
  | forall_e d ty b m hwf ihty ihb =>
    intro bs more r hbs h
    rw [frontend.proj_rec.strip_pis_all_loop.eq_def] at h
    rust_norm h
    · rename_i _ bs2 bm hand _ _
      obtain ⟨hbm, hpush⟩ := hand
      obtain ⟨hty, hb, hm⟩ := ExprWF.forall_e_kids hwf
      rw [Expr.binder_meta_dup_eq hbm] at hpush
      exact ihb hb bs2 true _ (ExprOps.bindersWF_push hbs hty hm hpush) h
    · exact ⟨hbs, hwf⟩
  | _ =>
    intro bs more r hbs h
    rw [frontend.proj_rec.strip_pis_all_loop.eq_def] at h
    rust_norm h
    · rw [strip_pis_all_loop_false h]; exact ⟨hbs, ‹ExprWF _›⟩
    · exact ⟨hbs, ‹ExprWF _›⟩

/-- `proj_rec::strip_pis_all` (`ConLeche/Frontend/ProjRec.lean:239-245
stripPisAll`): every leading `∀`'s domain and datum, and the body. -/
theorem strip_pis_all_wf {e : expr.Expr}
    {r : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr} (he : ExprWF e)
    (h : frontend.proj_rec.strip_pis_all e = ok r) :
    ExprOps.BindersWF r.1 ∧ ExprWF r.2 := by
  rw [frontend.proj_rec.strip_pis_all] at h
  simp only [expr_dup_eq, bind_tc_ok] at h
  exact strip_pis_all_loop_wf e he _ true r ExprOps.bindersWF_new h

/-- `inst_pis_open`'s loop at `ok = false` is its own exit. -/
theorem inst_pis_open_loop_false {args : alloc.vec.Vec expr.Expr} {cur : expr.Expr}
    {n i : Std.Usize} {r : expr.Expr × Bool}
    (h : frontend.proj_rec.inst_pis_open_loop args cur n i false = ok r) :
    r = (cur, false) := by
  rw [frontend.proj_rec.inst_pis_open_loop.eq_def] at h
  split at h
  · split at h
    · rename_i hc; simp at hc
    · exact (Result.ok_injective h).symm
  · exact (Result.ok_injective h).symm

/-- The index recursion behind `proj_rec::inst_pis_open`: one
`expr_ops_c::instantiate1_lift` per argument, so the residual telescope stays
well formed as long as the arguments are. -/
theorem inst_pis_open_loop_wf (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (cur : expr.Expr) (n i : Std.Usize) (ok1 : Bool)
      (r : expr.Expr × Bool),
      n.val - i.val = N → ExprsWF args → ExprWF cur →
      frontend.proj_rec.inst_pis_open_loop args cur n i ok1 = ok r → ExprWF r.1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args cur n i ok1 r hN hargs hcur h
    obtain ⟨⟨d, kind⟩⟩ := cur
    rw [frontend.proj_rec.inst_pis_open_loop.eq_def] at h
    rust_norm h
    case h_7 =>
      rename_i ea e1 hand i1 hi1 _ _
      obtain ⟨hidx, hinst⟩ := hand
      obtain ⟨-, hbo, -⟩ := ExprWF.forall_e_kids hcur
      obtain ⟨-, hmem⟩ := vec_index_mem hidx
      have hwfe1 : ExprWF e1 :=
        (ExprOpsC.instantiate1_lift_refines hbo (hargs ea hmem) hinst).2
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hlt : i.val < n.val := by scalar_tac
      exact ih (n.val - i1.val) (by omega) args e1 n i1 true _ rfl hargs hwfe1 h
    all_goals first
      | exact hcur
      | (rw [inst_pis_open_loop_false h]; exact hcur)

/-- `proj_rec::inst_pis_open` (`ConLeche/Frontend/ProjRec.lean:251-257
instPisOpen`): instantiate the leading `∀`-binders at *open* arguments. -/
theorem inst_pis_open_wf {e : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {r : Option expr.Expr} (he : ExprWF e) (hargs : ExprsWF args)
    (h : frontend.proj_rec.inst_pis_open e args = ok r) :
    ∀ x, r = some x → ExprWF x := by
  rw [frontend.proj_rec.inst_pis_open] at h
  simp only [expr_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨p, hloop, hdone⟩ := h
  obtain ⟨cur1, ok1⟩ := p
  have hwf : ExprWF cur1 :=
    inst_pis_open_loop_wf _ args e _ 0#usize true (cur1, ok1) rfl hargs he hloop
  -- the destructuring `let` the tuple bind leaves is an iota step, by definition
  replace hdone : frontend.proj_rec.inst_pis_open_done ok1 cur1 = ok r := hdone
  rw [frontend.proj_rec.inst_pis_open_done.eq_def] at hdone
  intro x hx
  split at hdone <;> rw [← Result.ok_injective hdone] at hx
  · simp only [Option.some.injEq] at hx; rw [← hx]; exact hwf
  · simp at hx

/-! ## The two pinned constants of the rewrite -/

/-- `proj_rec::punit_at` — `.const punitName [ℓ]`, the constant every motive
but the owner's answers. -/
theorem punit_at_wf {l : level.Level} {e : expr.Expr} (hl : LevelWF l)
    (h : frontend.proj_rec.punit_at l = ok e) : ExprWF e := by
  rw [frontend.proj_rec.punit_at] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, hmk⟩ := h
  exact Expr.mk_const_wf (BasisNames.punit_name_refines hn).2 (one_level_wf hl hv) hmk

/-- `proj_rec::punit_unit_at` — `.const punitUnitName [ℓ]`, the value every
minor but the owner constructor's returns. -/
theorem punit_unit_at_wf {l : level.Level} {e : expr.Expr} (hl : LevelWF l)
    (h : frontend.proj_rec.punit_unit_at l = ok e) : ExprWF e := by
  rw [frontend.proj_rec.punit_unit_at] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, hmk⟩ := h
  exact Expr.mk_const_wf (BasisNames.punit_unit_name_refines hn).2 (one_level_wf hl hv) hmk

/-! ## `build_binders`, parametric in its dictionary

`build_binders` is a `MkBinder`-generic telescope peeler (`§3.4` has no
closures, so con-leche's `Expr → Option Expr` argument became a one-method
trait).  What the rewrite needs of that argument is one line, in the shape
`PropWhenWF`'s `bind_z` constructor uses for `prop_when::bind_z`'s dictionary:
the binder it makes out of a well-formed domain is well formed. -/

/-- The dictionary's obligation. -/
def MkBinderWF {M : Type} (inst : frontend.proj_rec.MkBinder M) (mk : M) : Prop :=
  ∀ dom, ExprWF dom → ∀ t, inst.binder mk dom = ok (some t) → ExprWF t

/-- `proj_rec::build_binders_step_at` — the cited `do let t ← mk dom; …`
(`ConLeche/Frontend/ProjRec.lean:259-269 buildBinders`). -/
theorem build_binders_step_at_wf {M : Type} {inst : frontend.proj_rec.MkBinder M} {mk : M}
    {dom body : expr.Expr} {o : Option (expr.Expr × expr.Expr)}
    (hmk : MkBinderWF inst mk) (hdom : ExprWF dom) (hbody : ExprWF body)
    (h : frontend.proj_rec.build_binders_step_at inst mk dom body = ok o) :
    ∀ t b, o = some (t, b) → ExprWF t ∧ ExprWF b := by
  rw [frontend.proj_rec.build_binders_step_at] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, hb, h⟩ := h
  cases o1 with
  | none => intro t b hx; rw [← Result.ok_injective h] at hx; simp at hx
  | some t0 =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b0, hinst, h⟩ := h
    have ht : ExprWF t0 := hmk dom hdom t0 hb
    have hb0 : ExprWF b0 := (ExprOpsC.instantiate1_lift_refines hbody ht hinst).2
    intro t b hx
    rw [← Result.ok_injective h] at hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨ht, hb0⟩

/-- `proj_rec::build_binders_step` — one binder's term and the telescope
instantiated at it (`ProjRec.lean:259-269 buildBinders`). -/
theorem build_binders_step_wf {M : Type} {inst : frontend.proj_rec.MkBinder M} {mk : M}
    {cur : expr.Expr} {o : Option (expr.Expr × expr.Expr)}
    (hmk : MkBinderWF inst mk) (hcur : ExprWF cur)
    (h : frontend.proj_rec.build_binders_step inst mk cur = ok o) :
    ∀ t b, o = some (t, b) → ExprWF t ∧ ExprWF b := by
  obtain ⟨⟨d, kind⟩⟩ := cur
  rw [frontend.proj_rec.build_binders_step.eq_def] at h
  rust_norm h
  case h_7 =>
    exact build_binders_step_at_wf hmk (ExprWF.forall_e_kids hcur).1
      (ExprWF.forall_e_kids hcur).2.1 h
  -- the nine arms that are not a `∀` answer `none`, which `rust_norm`'s
  -- `reduceCtorEq` has already turned into the contradiction
  all_goals (intro t b hx; simp at hx)

/-- `build_binders`' loop at `ok = false` is its own exit. -/
theorem build_binders_loop_false {M : Type} {inst : frontend.proj_rec.MkBinder M} {mk : M}
    {k : Std.U64} {out : alloc.vec.Vec expr.Expr} {cur : expr.Expr} {i : Std.U64}
    {r : (alloc.vec.Vec expr.Expr) × expr.Expr × Bool}
    (h : frontend.proj_rec.build_binders_loop inst mk k out cur i false = ok r) :
    r = (out, cur, false) := by
  rw [frontend.proj_rec.build_binders_loop.eq_def] at h
  split at h
  · split at h
    · rename_i hc; simp at hc
    · exact (Result.ok_injective h).symm
  · exact (Result.ok_injective h).symm

/-- The countdown behind `proj_rec::build_binders`. -/
theorem build_binders_loop_wf {M : Type} {inst : frontend.proj_rec.MkBinder M} {mk : M}
    (hmk : MkBinderWF inst mk) (N : Nat) :
    ∀ (k : Std.U64) (out : alloc.vec.Vec expr.Expr) (cur : expr.Expr) (i : Std.U64)
      (ok1 : Bool) (r : (alloc.vec.Vec expr.Expr) × expr.Expr × Bool),
      k.val - i.val = N → ExprsWF out → ExprWF cur →
      frontend.proj_rec.build_binders_loop inst mk k out cur i ok1 = ok r →
      ExprsWF r.1 ∧ ExprWF r.2.1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k out cur i ok1 r hN hout hcur h
    rw [frontend.proj_rec.build_binders_loop.eq_def] at h
    rust_norm h
    case h_2 =>
      rename_i _ t b hstep out1 hpush i1 hi1 _ _
      obtain ⟨ht, hb⟩ := build_binders_step_wf hmk hcur hstep t b rfl
      have hout1 : ExprsWF out1 := by
        intro x hx
        rw [vec_push_val hpush] at hx
        rcases List.mem_append.1 hx with h1 | h1
        · exact hout x h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact ht
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hlt : i.val < k.val := by scalar_tac
      exact ih (k.val - i1.val) (by omega) k out1 b i1 true _ rfl hout1 hb h
    all_goals first
      | exact ⟨hout, hcur⟩
      | (rw [build_binders_loop_false h]; exact ⟨hout, hcur⟩)

/-- `proj_rec::build_binders` (`ConLeche/Frontend/ProjRec.lean:259-269
buildBinders`): peel `k` binders, building one term per binder out of its
domain.  The dictionary's obligation is the hypothesis. -/
theorem build_binders_wf {M : Type} {inst : frontend.proj_rec.MkBinder M} {mk : M}
    {k : Std.U64} {e : expr.Expr} {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hmk : MkBinderWF inst mk) (he : ExprWF e)
    (h : frontend.proj_rec.build_binders inst mk k e = ok r) :
    ∀ out cur, r = some (out, cur) → ExprsWF out ∧ ExprWF cur := by
  rw [frontend.proj_rec.build_binders] at h
  simp only [expr_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨p, hloop, hdone⟩ := h
  obtain ⟨out0, cur0, ok0⟩ := p
  obtain ⟨hout0, hcur0⟩ :=
    build_binders_loop_wf hmk _ k _ e 0#u64 true (out0, cur0, ok0) rfl
      (fun x hx => by simp at hx) he hloop
  replace hdone : frontend.proj_rec.build_binders_done ok0 out0 cur0 = ok r := hdone
  rw [frontend.proj_rec.build_binders_done.eq_def] at hdone
  intro out cur hx
  split at hdone <;> rw [← Result.ok_injective hdone] at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx; exact ⟨hout0, hcur0⟩
  · simp at hx

/-! ## The two dictionaries

`MkMotive` and `MkMinor` are the rewrite's two `MkBinder` implementations
(`ConLeche/Frontend/ProjRec.lean:279-330 projRecValue`'s `mkMotive` and
`mkMinor`).  Each discharges `MkBinderWF`: whatever it makes out of a
well-formed domain is an `expr::lam` over `strip_pis_all`'s own binders with a
well-formed body — the lifted subject `R`, the constant `PUnit.{ℓ}`, a bound
variable of the minor's own telescope, or `PUnit.unit.{ℓ}`. -/

/-- The owner's motive is `fun (t : T p⃗) => R`, every other one the constant
`PUnit.{ℓ}` over its telescope.  The owner name `t` carries no hypothesis: it
is only ever `head_is`' *comparison* argument. -/
theorem mk_motive_wf {t : name.Name} {rr : expr.Expr} {l : level.Level}
    (hr : ExprWF rr) (hl : LevelWF l) :
    MkBinderWF frontend.proj_rec.MkMotive.Insts.Con_ron_coreFrontendProj_recMkBinder
      { t := t, r := rr, l := l } := by
  intro dom hdom x h
  replace h : frontend.proj_rec.MkMotive.Insts.Con_ron_coreFrontendProj_recMkBinder.binder
      { t := t, r := rr, l := l } dom = ok (some x) := h
  rw [frontend.proj_rec.MkMotive.Insts.Con_ron_coreFrontendProj_recMkBinder.binder] at h
  rust_norm h
  case h_3.isTrue.isTrue =>
    rename_i v e hsp _ _ _ _ e1 bm hidx _ _ _ e3 hlift bm1 hbmdup
    obtain ⟨hv, -⟩ := strip_pis_all_wf hdom hsp
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    obtain ⟨he1, hbm⟩ := hv _ hmem
    rw [Expr.binder_meta_dup_eq hbmdup] at h
    exact Expr.lam_wf he1 (ExprOps.lift_loose_bvars_refines hr hlift).2 hbm h
  case h_3.isTrue.isFalse =>
    rename_i v e hsp _ _ _ _ e1 bm hidx _ _ _ e3 hpu bm1 hbmdup
    obtain ⟨hv, -⟩ := strip_pis_all_wf hdom hsp
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    obtain ⟨he1, hbm⟩ := hv _ hmem
    rw [Expr.binder_meta_dup_eq hbmdup] at h
    exact Expr.lam_wf he1 (punit_at_wf hl hpu) hbm h
  case h_3.isFalse =>
    rename_i v e hsp _ _ _ _ e2 hpu
    obtain ⟨hv, -⟩ := strip_pis_all_wf hdom hsp
    exact mk_lams_wf hv (punit_at_wf hl hpu) h

/-- The owner constructor's minor returns field `i` of its telescope (fields
first, then the inductive hypotheses); every other one returns
`PUnit.unit.{ℓ}`.  As for `mk_motive_wf`, the constructor name `c` is only
`head_is`' comparison argument and carries no hypothesis. -/
theorem mk_minor_wf {c : name.Name} {i : Std.U64} {l : level.Level} (hl : LevelWF l) :
    MkBinderWF frontend.proj_rec.MkMinor.Insts.Con_ron_coreFrontendProj_recMkBinder
      { ctor := c, i := i, l := l } := by
  intro dom hdom x h
  replace h : frontend.proj_rec.MkMinor.Insts.Con_ron_coreFrontendProj_recMkBinder.binder
      { ctor := c, i := i, l := l } dom = ok (some x) := h
  rw [frontend.proj_rec.MkMinor.Insts.Con_ron_coreFrontendProj_recMkBinder.binder] at h
  rust_norm h
  case isFalse.isTrue.isTrue =>
    rename_i v e hsp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2 hbv
    obtain ⟨hv, -⟩ := strip_pis_all_wf hdom hsp
    exact mk_lams_wf hv (Expr.mk_bvar_wf hbv) h
  all_goals (
    rename_i v e hsp _ _ _ _ _ _ _ _ _ _ _ e2 hpu
    obtain ⟨hv, -⟩ := strip_pis_all_wf hdom hsp
    exact mk_lams_wf hv (punit_unit_at_wf hl hpu) h)

/-! ## The rewrite -/

/-- `proj_rec::proj_rec_value_major` — the cited final `match rty with |
.forallE majDom _ _ => …` (`ConLeche/Frontend/ProjRec.lean:279-330
projRecValue`): the owner has no indices, so the next binder is the subject
itself and the value is `T.rec.{ℓ, u⃗} p⃗ motives minors (bvar 0)` under the
definition's own binders.  `rty` needs no hypothesis — only its `majDom` is
read, and only by `head_is`. -/
theorem proj_rec_value_major_wf {o : frontend.proj_rec.ProjRecOwner}
    {lus : alloc.vec.Vec level.Level} {params motives minors : alloc.vec.Vec expr.Expr}
    {lbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {rty e : expr.Expr}
    (ho : ProjRecOwnerWF o) (hlus : LevelsWF lus) (hparams : ExprsWF params)
    (hmotives : ExprsWF motives) (hminors : ExprsWF minors)
    (hlbs : ExprOps.BindersWF lbs)
    (h : frontend.proj_rec.proj_rec_value_major o lus params motives minors lbs rty
      = ok (some e)) : ExprWF e := by
  obtain ⟨⟨d, kind⟩⟩ := rty
  rw [frontend.proj_rec.proj_rec_value_major.eq_def] at h
  rust_norm h
  rename_i a1 ha1 a2 ha2 a3 ha3 bv hbv args3 hpush lus2 hlc cn hcn app happ
  have hnew : ExprsWF (alloc.vec.Vec.new expr.Expr) := fun y hy => by simp at hy
  have h1 : ExprsWF a1 := append_exprs_wf hnew hparams ha1
  have h2 : ExprsWF a2 := append_exprs_wf h1 hmotives ha2
  have h3 : ExprsWF a3 := append_exprs_wf h2 hminors ha3
  have h4 : ExprsWF args3 := by
    intro y hy
    rw [vec_push_val hpush] at hy
    rcases List.mem_append.1 hy with hy1 | hy1
    · exact h3 y hy1
    · simp only [List.mem_singleton] at hy1; rw [hy1]; exact Expr.mk_bvar_wf hbv
  have h5 : LevelsWF lus2 := fun u hu => hlus u (by rw [← ExprOps.levels_copy_val hlc]; exact hu)
  have h6 : ExprWF cn := Expr.mk_const_wf ho.2.2.2.1 h5 hcn
  exact mk_lams_wf hlbs (ExprOps.mk_app_n_refines h6 h4 happ).2 h

/-- `proj_rec::proj_rec_value_at` — the cited block from `let us := o.lps.map
Level.param` to the last `buildBinders` (`ProjRec.lean:279-330 projRecValue`):
the recursor's type at the chosen elimination level, its parameters
instantiated at the body frame, then the motives and the minors. -/
theorem proj_rec_value_at_wf {o : frontend.proj_rec.ProjRecOwner} {l : level.Level}
    {r : expr.Expr} {lbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.U64}
    {e : expr.Expr} (ho : ProjRecOwnerWF o) (hl : LevelWF l) (hr : ExprWF r)
    (hlbs : ExprOps.BindersWF lbs)
    (h : frontend.proj_rec.proj_rec_value_at o l r lbs i = ok (some e)) : ExprWF e := by
  rw [frontend.proj_rec.proj_rec_value_at] at h
  rust_norm h
  rename_i us hus1 v1 hv1 lus hlus1 rty0 hrty0 pars hpars _ rty1 hipo _ mots mrt hmot _ mins nrt hmin
  have hUS : LevelsWF us := (StructParts.params_of_refines ho.2.1 hus1).2
  have hLUS : LevelsWF lus := append_levels_wf (one_level_wf hl hv1) hUS hlus1
  have hRTY0 : ExprWF rty0 :=
    (ExprOps.instantiate_level_params_refines ho.2.2.2.2.1 hLUS ho.2.2.2.2.2 hrty0).2
  have hPARS : ExprsWF pars := bvar_params_wf hpars
  have hRTY1 : ExprWF rty1 := inst_pis_open_wf hRTY0 hPARS hipo rty1 rfl
  obtain ⟨hMOTS, hMRT⟩ := build_binders_wf (mk_motive_wf hr hl) hRTY1 hmot mots mrt rfl
  obtain ⟨hMINS, -⟩ := build_binders_wf (mk_minor_wf hl) hMRT hmin mins nrt rfl
  exact proj_rec_value_major_wf ho hLUS hPARS hMOTS hMINS hlbs h

/-- **The rewrite** (`ConLeche/Frontend/ProjRec.lean:279-330 projRecValue`).
`ty`/`val` are the definition's declared type and value, `i` the projected
field, `l` the field's sort (from the artifact); the answer is what
`export_c::proj_rewrite_d` stores in place of the parsed value. -/
theorem proj_rec_value_wf {o : frontend.proj_rec.ProjRecOwner} {l : level.Level}
    {ty val e : expr.Expr} {i : Std.U64} (ho : ProjRecOwnerWF o) (hl : LevelWF l)
    (hty : ExprWF ty) (hval : ExprWF val)
    (h : frontend.proj_rec.proj_rec_value o l ty val i = ok (some e)) : ExprWF e := by
  rw [frontend.proj_rec.proj_rec_value] at h
  rust_norm h
  rename_i _ k hk _ _ _ _ _ lv lb hsl _ _ _ _ pb tb hsp
  obtain ⟨hlv, -⟩ := (ExprOps.strip_lams_refines hval hsl).2 (lv, lb) rfl
  obtain ⟨-, htb⟩ := (ExprOps.strip_pis_refines hty hsp).2 (pb, tb) rfl
  exact proj_rec_value_at_wf ho hl htb hlv h

/-! ## The readers -/

/-- `proj_rec::lam_body` (`ConLeche/Frontend/ProjRec.lean:233-237 lamBody`):
the node under the value's leading `λ`s. -/
theorem lam_body_wf (e : expr.Expr) (he : ExprWF e) :
    ∀ b, frontend.proj_rec.lam_body e = ok b → ExprWF b := by
  induction e, he using ExprWF.ind_node with
  | lam d ty bo m hwf ihty ihb =>
    intro b h
    rw [frontend.proj_rec.lam_body.eq_def] at h
    rust_norm h
    exact ihb (ExprWF.lam_kids hwf).2.1 b h
  | _ =>
    intro b h
    rw [frontend.proj_rec.lam_body.eq_def] at h
    -- `expr::dup` is the identity in the model, so `rust_norm` has already
    -- identified `b` with the node itself
    rust_norm h
    exact ‹ExprWF _›

/-- `proj_rec::proj_iota_level` (`ConLeche/Frontend/ProjRec.lean:120-125
projIotaLevel`): the `Eq` level of an artifact iota statement.  It is read out
of the `.const` node's own level list, so the clause follows from `ExprWF`'s
`mk_const` constructor. -/
theorem proj_iota_level_wf {ty : expr.Expr} {l : level.Level} (hty : ExprWF ty)
    (h : frontend.proj_rec.proj_iota_level ty = ok (some l)) : LevelWF l := by
  rw [frontend.proj_rec.proj_iota_level] at h
  rust_norm h
  rename_i pr hpr hd hhd _ n us heq _ _ _ _ _ _
  have hHD : ExprWF hd := (ExprOps.get_app_fn_refines (ExprOps.pi_result_refines hty hpr).2 hhd).2
  have hk := ExprWF.kids hHD
  rw [heq] at hk
  exact hk.2 l (vec_index_mem h).2

/-! ## The artifact's name

`proj_iota_name` spells `T._model.proj_i.iota`.  Its `proj_i` component is
`text::cat` of a literal with `text::u64_str`, so the three code-point helpers
of `frontend::text` owe a `StrWF` clause here — the one place on the parse path
where a `Name` payload is *computed* rather than copied from the input.  (The
name itself is only ever a map *key* in `export_c`, whose `MapValsWF` is
key-blind; the lemma is stated because a reader of the owner census may want
it.) -/

/-- The index recursion behind `text::cat`. -/
theorem cat_loop_wf (N : Nat) :
    ∀ (b out r : alloc.vec.Vec Std.U32) (n i : Std.Usize),
      b.val.length - i.val = N → StrWF b → StrWF out →
      frontend.text.cat_loop b out n i = ok r → StrWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro b out r n i hN hb hout h
    rw [frontend.text.cat_loop.eq_def] at h
    split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hidx, out1, hpush, i2, hi2, hrec⟩ := h
      obtain ⟨hlt, hmem⟩ := vec_index_mem hidx
      have hout1 : StrWF out1 := by
        intro y hy
        rw [vec_push_val hpush] at hy
        rcases List.mem_append.1 hy with h1 | h1
        · exact hout y h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact hb c hmem
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      exact ih (b.val.length - i2.val) (by omega) b out1 r n i2 rfl hb hout1 hrec
    · rw [← Result.ok_injective h]; exact hout

/-- `text::cat` concatenates two code-point strings. -/
theorem cat_wf {a b r : alloc.vec.Vec Std.U32} (ha : StrWF a) (hb : StrWF b)
    (h : frontend.text.cat a b = ok r) : StrWF r := by
  rw [frontend.text.cat] at h
  exact cat_loop_wf _ b a r _ 0#usize rfl hb ha h

/-- `text::u64_str`'s first loop: the decimal digits, least significant first.
Each pushed code point is `48 + k % 10`, i.e. an ASCII digit. -/
theorem u64_str_loop0_wf (N : Nat) :
    ∀ (rev r : alloc.vec.Vec Std.U32) (k : Std.U64),
      k.val = N → StrWF rev → frontend.text.u64_str_loop0 rev k = ok r → StrWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro rev r k hN hrev h
    rw [frontend.text.u64_str_loop0.eq_def] at h
    split at h
    · rename_i hgt
      have hkv : 0 < k.val := by scalar_tac
      simp only [lift_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨dg, hdg, c, hadd, rev1, hpush, k1, hk1, hrec⟩ := h
      have hdgv : dg.val = k.val % 10 := CoreK.uscalar_rem_eq (by scalar_tac) hdg
      have hcast : (Std.UScalar.cast .U32 dg).val = dg.val :=
        CoreK.u64_cast_u32_val_of_lt_ten (by omega)
      have hcv : c.val = 48 + (Std.UScalar.cast .U32 dg).val := HashMap.uscalar_add_eq hadd
      have hvalid : Nat.isValidChar c.val := by
        unfold Nat.isValidChar
        have : c.val < 58 := by omega
        omega
      have hrev1 : StrWF rev1 := by
        intro y hy
        rw [vec_push_val hpush] at hy
        rcases List.mem_append.1 hy with h1 | h1
        · exact hrev y h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact hvalid
      have hk1v : k1.val = k.val / 10 := HashMap.uscalar_div_eq hk1
      exact ih k1.val (by rw [hk1v, ← hN]; exact Nat.div_lt_self hkv (by omega))
        rev1 r k1 rfl hrev1 hrec
    · rw [← Result.ok_injective h]; exact hrev

/-- `text::u64_str`'s second loop: the digits read back to front. -/
theorem u64_str_loop1_wf (N : Nat) :
    ∀ (rev out r : alloc.vec.Vec Std.U32) (i : Std.Usize),
      i.val = N → StrWF rev → StrWF out →
      frontend.text.u64_str_loop1 rev out i = ok r → StrWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro rev out r i hN hrev hout h
    rw [frontend.text.u64_str_loop1.eq_def] at h
    split at h
    · rename_i hgt
      have hiv : 0 < i.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, c, hidx, out1, hpush, hrec⟩ := h
      obtain ⟨-, hmem⟩ := vec_index_mem hidx
      have hi1v : i1.val = i.val - 1 := HashMap.uscalar_sub_eq hi1
      have hout1 : StrWF out1 := by
        intro y hy
        rw [vec_push_val hpush] at hy
        rcases List.mem_append.1 hy with h1 | h1
        · exact hout y h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact hrev c hmem
      exact ih i1.val (by omega) rev out1 r i1 rfl hrev hout1 hrec
    · rw [← Result.ok_injective h]; exact hout

/-- `text::u64_str` is a string of ASCII digits. -/
theorem u64_str_wf {i : Std.U64} {s : alloc.vec.Vec Std.U32}
    (h : frontend.text.u64_str i = ok s) : StrWF s := by
  have hnew : StrWF (alloc.vec.Vec.new Std.U32) := by intro y hy; simp at hy
  rw [frontend.text.u64_str] at h
  split at h
  · intro y hy
    rw [vec_push_val h] at hy
    rw [show (alloc.vec.Vec.new Std.U32).val = [] by simp [alloc.vec.Vec.new],
      List.nil_append, List.mem_singleton] at hy
    have h48 : (48#u32 : Std.U32).val = 48 := by scalar_tac
    rw [hy]; unfold Nat.isValidChar; omega
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨rev, hrev, hloop⟩ := h
    exact u64_str_loop1_wf _ rev _ s _ rfl (u64_str_loop0_wf _ _ rev i rfl hnew hrev)
      (by intro y hy; simp at hy) hloop

/-- The `StrWF` half of `CoreKBase`'s `str_lit_step`, for a literal that does
not immediately become a `Name`. -/
theorem code_points_strwf {k : Std.Usize} {S : Array Std.U32 k} {L : List Std.U32}
    {w : alloc.vec.Vec Std.U32} (hw : core_types.code_points (Array.to_slice S) = ok w)
    (hSL : S.val = L) (hvalid : ∀ c ∈ L, Nat.isValidChar c.val) : StrWF w := by
  intro c hc
  rw [code_points_val hw, Array.val_to_slice, hSL] at hc
  exact hvalid c hc

/-- `proj_rec::proj_iota_name` (`ConLeche/Frontend/ProjRec.lean:106-111
projIotaName`): `T._model.proj_i.iota`. -/
theorem proj_iota_name_wf {t : name.Name} {i : Std.U64} {n : name.Name} (ht : NameWF t)
    (h : frontend.proj_rec.proj_iota_name t i = ok n) : NameWF n := by
  rw [frontend.proj_rec.proj_iota_name] at h
  simp only [name_dup_eq, lift_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨v, hv, a, ha, v1, hv1, v2, hv2, v3, hv3, b, hb, v4, hv4, hmk⟩ := h
  have hawf : NameWF a := (str_lit_step ht (lift_eq _) hv ha
    (L := [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32])
    (by simp [frontend.proj_rec.proj_iota_name.MODEL]) (by decide)).2
  have hv1s : StrWF v1 := code_points_strwf hv1
    (L := [112#u32, 114#u32, 111#u32, 106#u32, 95#u32])
    (by simp [frontend.proj_rec.proj_iota_name.PROJ]) (by decide)
  have hbwf : NameWF b := Name.mk_str_wf hawf (cat_wf hv1s (u64_str_wf hv2) hv3) hb
  exact (str_lit_step hbwf (lift_eq _) hv4 hmk
    (L := [105#u32, 111#u32, 116#u32, 97#u32])
    (by simp [frontend.proj_rec.proj_iota_name.IOTA]) (by decide)).2

/-- `proj_rec::info_name` — `env::constant_info_name`, spelled here so that
`export_c`'s owner registration reads like the Lean. -/
theorem info_name_wf {ci : env.ConstantInfo} {n : name.Name} (hci : ConstantInfoWF ci)
    (h : frontend.proj_rec.info_name ci = ok n) : NameWF n := by
  rw [frontend.proj_rec.info_name] at h
  cases ci with
  | AxiomInfo v =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; exact hci.1
  | DefnInfo v _ _ | ThmInfo v _ | IndInfo v _ | RecInfo v _ _ _ =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; exact hci.1.1
  | CtorInfo v _ _ =>
    simp only [env.constant_info_name, name_dup_eq, Result.ok.injEq] at h
    rw [← h]; exact hci.1
  | ProjInfo t =>
    simp only [env.constant_info_name] at h
    exact Env.proj_table_name_wf hci.1 h

/-! ## The owner census

`proj_rec_owners` answers which block members the rewrite serves.  What it
*builds* is a record whose six term fields all come from the export's own
records: `t`/`ctor` from the type record's name and its single constructor,
`lps`/`rec_lps` through `prop_when::names_copy`, `rec_name`/`rec_type` from the
recursor record.  Everything else it does — `struct_parts_core`,
`native_parts`, `any_is_rec`, `any_ctor_mentions`, `find_ctor`, `find_rec`,
`level::is_equiv` — is a decision, so `block` and `ctors` carry no term into
the answer. -/

/-- `proj_rec::proj_rec_owner_at` (`ConLeche/Frontend/ProjRec.lean:332-370
projRecOwners`): the `types.filterMap` body on one type record. -/
theorem proj_rec_owner_at_wf {t : frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec} {recs : Slice frontend.proj_rec.ProjRecRec}
    {o : frontend.proj_rec.ProjRecOwner} (ht : ProjTypeRecWF t)
    (hr : ∀ x ∈ recs.val, ProjRecRecWF x)
    (h : frontend.proj_rec.proj_rec_owner_at t ctors recs = ok (some o)) :
    ProjRecOwnerWF o := by
  obtain ⟨htn, htlps, -, htctors⟩ := ht
  rw [frontend.proj_rec.proj_rec_owner_at] at h
  rust_norm h
  all_goals (
    rename_i cn hcn _ _ _ _ _ _ _ _ _ _ prr hprr _ _ _ lps1 hlps1 _ _ rlps hrlps
    obtain ⟨-, hcnmem⟩ := vec_index_mem hcn
    obtain ⟨-, hprrmem⟩ := slice_index_mem hprr
    obtain ⟨hrn, hrlpsw, hrty⟩ := hr _ hprrmem
    refine ⟨htn, ?_, htctors _ hcnmem, hrn, ?_, hrty⟩
    · intro x hx; rw [PropWhen.names_copy_val hlps1] at hx; exact htlps x hx
    · intro x hx; rw [PropWhen.names_copy_val hrlps] at hx; exact hrlpsw x hx)

/-- The loop behind `proj_rec::proj_rec_owners_go`. -/
theorem proj_rec_owners_go_loop_wf (N : Nat) :
    ∀ (types : Slice frontend.proj_rec.ProjTypeRec)
      (ctors : Slice frontend.proj_rec.ProjCtorRec)
      (recs : Slice frontend.proj_rec.ProjRecRec) (n : Std.Usize)
      (out r : alloc.vec.Vec frontend.proj_rec.ProjRecOwner) (i : Std.Usize),
      types.val.length - i.val = N →
      (∀ x ∈ types.val, ProjTypeRecWF x) → (∀ x ∈ recs.val, ProjRecRecWF x) →
      (∀ x ∈ out.val, ProjRecOwnerWF x) →
      frontend.proj_rec.proj_rec_owners_go_loop types ctors recs n out i = ok r →
      ∀ x ∈ r.val, ProjRecOwnerWF x := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro types ctors recs n out r i hN htypes hrecs hout h
    rw [frontend.proj_rec.proj_rec_owners_go_loop.eq_def] at h
    split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨ptr, hptr, o, ho, out1, heq, i1, hi1, hrec⟩ := h
      obtain ⟨hlt, hmem⟩ := slice_index_mem hptr
      have hout1 : ∀ x ∈ out1.val, ProjRecOwnerWF x := by
        cases o with
        | none => rw [← Result.ok_injective heq]; exact hout
        | some o1 =>
          intro x hx
          rw [vec_push_val heq] at hx
          rcases List.mem_append.1 hx with h1 | h1
          · exact hout x h1
          · simp only [List.mem_singleton] at h1
            rw [h1]; exact proj_rec_owner_at_wf (htypes ptr hmem) hrecs ho
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      exact ih (types.val.length - i1.val) (by omega) types ctors recs n out1 r i1 rfl
        htypes hrecs hout1 hrec
    · rw [← Result.ok_injective h]; exact hout

/-- `proj_rec::proj_rec_owners_go` — the cited `types.filterMap`. -/
theorem proj_rec_owners_go_wf {types : Slice frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec} {recs : Slice frontend.proj_rec.ProjRecRec}
    {os : alloc.vec.Vec frontend.proj_rec.ProjRecOwner}
    (ht : ∀ x ∈ types.val, ProjTypeRecWF x) (hr : ∀ x ∈ recs.val, ProjRecRecWF x)
    (h : frontend.proj_rec.proj_rec_owners_go types ctors recs = ok os) :
    ∀ x ∈ os.val, ProjRecOwnerWF x := by
  rw [frontend.proj_rec.proj_rec_owners_go] at h
  exact proj_rec_owners_go_loop_wf _ types ctors recs _ _ os 0#usize rfl ht hr
    (fun x hx => by simp at hx) h

set_option linter.unusedVariables false in
/-- **The owner census** (`ConLeche/Frontend/ProjRec.lean:332-370
projRecOwners`).  `hb` is not used: the parsed block reaches the answer through
`struct_parts_core` and `native_parts`, both of which only *decide* whether the
census runs at all, and `hc` is not used either — a `ProjCtorRec` contributes
only its field count `n_f`, a machine word.  Both are kept in the statement
because they are what `export_c::register_proj_owners` has to hand. -/
theorem proj_rec_owners_wf {block : alloc.vec.Vec env.ConstantInfo}
    {types : Slice frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec} {recs : Slice frontend.proj_rec.ProjRecRec}
    {os : alloc.vec.Vec frontend.proj_rec.ProjRecOwner} (hb : ConstantInfosWF block)
    (ht : ∀ t ∈ types.val, ProjTypeRecWF t) (hc : ∀ c ∈ ctors.val, ProjCtorRecWF c)
    (hr : ∀ r ∈ recs.val, ProjRecRecWF r)
    (h : frontend.proj_rec.proj_rec_owners block types ctors recs = ok os) :
    ∀ o ∈ os.val, ProjRecOwnerWF o := by
  rw [frontend.proj_rec.proj_rec_owners] at h
  rust_norm h
  all_goals first
    | exact proj_rec_owners_go_wf ht hr h
    | (intro x hx; simp at hx)

/-! ## The axiom census

`Refine/Main.lean`'s three: the tier adds none of its own. -/

/-- info: 'ConRon.Refine.Frontend.proj_rec_value_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proj_rec_value_wf

/-- info: 'ConRon.Refine.Frontend.proj_rec_owners_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proj_rec_owners_wf

end ConRon.Refine.Frontend
