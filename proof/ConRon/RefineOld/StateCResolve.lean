/-
`Refine/StateC.lean`'s last wrapper, in its own file because it is a *walk*:
`cached::state_c::consts_resolve_fc`, the parsed-index driver's syntactic guard
— `Expr.constsResolveF fe` as one **memoized `Expr` DAG pass**
(`ConLeche/Cached/StateC.lean:409-519`).

Two things are different from the `*M` wrappers next door:

* the memo is **local to the call** (the result depends on the environment), so
  it is a `&mut HashMap` accumulator and not `CState` state: no §3.1 memo-policy
  obligation attaches to it, only the invariant, which is `MemoBOk` below —
  `Refine/ExprOps.lean`'s `MemoInv` at the `Expr`-keyed dictionary with `Bool`
  values: *every recorded answer is the real one*;
* the recursion is on the term, so the proof is an induction on the `ExprWF`
  derivation (task #17's style), one case per constructor, and `go`'s memo
  prologue is shared by all ten.

## The memo discipline (task #98, con-leche's #317/#319)

Since con-leche's #319 the cited walk no longer threads a structural
`Std.HashMap` that records EVERY node: it is `constsResolveFXP`, a walk
verified against the plain descent `constsResolveFP`, which decides `bvar`,
`sort`, `lit` and `const` on the spot and probes only a compound node
(`fvar` included: its annotation is descended) that `withExclusive` reports
shared.  There is therefore no longer a con-leche *table* for this port's
table to denote — only an answer to agree with — so what `MemoBOk` carries is
`ExprOps.MemoInv`'s "every entry is the plain descent's value at its key"
rather than `Refine/State.lean`'s three table facts.

That shape is what makes `go_of_node` below **one** prologue for every node
kind: correctness does not depend on the gate's verdict at all.  A skipped
node is not probed (`memo_b_probe_true`) and not recorded
(`memo_b_record_true`), so its table comes out of the arm untouched; a probed
node's hit is `MemoInv.hit` and its record is `MemoInv.set`.
`Refine/Excl.lean` holds the model of the gate itself.

## The ingredient this file does not own

The two `.lit` arms read `core_k::nat_trio_stored` and
`core_k::str_support_stored` — con-leche spells the same ten `FEnv.find?`
tests inline.  Their refinement is **task #49's `Refine/CoreK*.lean`** (and
through them `kernel::basis_names`', which no task has yet), so the two facts
travel here as one named hypothesis, `LitGuardsRefine`.  Nothing below is
weakened: the conclusion is the exact-result one, under an explicit ingredient.
-/
import ConRon.RefineOld.StateC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.StateC

open ConRon.Refine.State

/-! ## The call-local memo -/

/-- `ConLeche/Cached/StateC.lean:449` — con-leche's `Expr.MemoB0
(constsResolveFP fe)`, as the `Q` of `ExprOps.MemoInv`: a recorded answer is
the plain descent's answer at the key.  The value is a `Bool`, so there is no
well-formedness half. -/
def ResolveQ (lfe : ConLeche.FEnv) : ConLeche.Expr → Bool → Prop :=
  fun k r => r = ConLeche.Cached.constsResolveFP lfe k

/-- `ConLeche/Cached/StateC.lean:449` — the `ron::HashMap Expr Bool` the cited
walk threads: a well-formed table holding only well-formed keys, each mapped to
`constsResolveFP lfe` of the key's erasure. -/
abbrev MemoBOk (lfe : ConLeche.FEnv)
    (memo : ron.hashmap.HashMap expr.Expr Bool) : Prop :=
  ExprOps.MemoInv ExprWF absExpr (ResolveQ lfe) memo

/-- A fresh memo records nothing, so it records nothing wrong. -/
theorem memo_b_new {lfe : ConLeche.FEnv}
    {memo : ron.hashmap.HashMap expr.Expr Bool}
    (h : ron.hashmap.HashMap.new expr.Expr Bool = ok memo) : MemoBOk lfe memo :=
  ExprOps.MemoInv.empty (new_alv h)

/-- `ConLeche/Cached/StateC.lean:455` — `expr_ops::memo_b_get` is the cited
probe, and a hit is a correct answer. -/
theorem memo_b_get_refines {lfe : ConLeche.FEnv}
    {memo : ron.hashmap.HashMap expr.Expr Bool} {e : expr.Expr} {r : Bool}
    (hm : MemoBOk lfe memo) (he : ExprWF e)
    (h : expr_ops.memo_b_get memo e = ok (some r)) :
    r = ConLeche.Cached.constsResolveFP lfe (absExpr e) :=
  ExprOps.MemoInv.hit ExprOps.expr_key_exact hm he (ExprOps.memo_b_get_hit h)

/-- `ConLeche/Cached/StateC.lean:455` — the walk's `memo.shared e`: recording a
correct answer keeps the invariant. -/
theorem memo_b_insert {lfe : ConLeche.FEnv}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {e : expr.Expr} {b : Bool}
    {old : Option Bool} (hm : MemoBOk lfe memo) (he : ExprWF e)
    (hb : b = ConLeche.Cached.constsResolveFP lfe (absExpr e))
    (h : ron.hashmap.HashMap.insert hExpr eExpr memo e b = ok (old, memo')) :
    MemoBOk lfe memo' :=
  ExprOps.MemoInv.set ExprOps.expr_key_exact hm he hb h

/-! ## The two `.lit` guards

The ingredient task #49's `Refine/CoreK*.lean` owes this file: the two
`core_k` readers behind the `.lit` arms, each against the cited chain of
`FEnv.find?` tests. -/

/-- `ConLeche/Kernel/Core.lean:307-332` — `core_k::nat_trio_stored` and
`core_k::str_support_stored` against the cited `isSome` chains. -/
structure LitGuardsRefine : Prop where
  nat : ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (b : Bool),
    FEnv.FEnvRel fe lfe → FEnv.FEnvWF fe →
    core_k.nat_trio_stored fe = ok b →
    b = ((lfe.find? ConLeche.natName).isSome &&
          (lfe.find? ConLeche.natZeroName).isSome &&
          (lfe.find? ConLeche.natSuccName).isSome)
  str : ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (b : Bool),
    FEnv.FEnvRel fe lfe → FEnv.FEnvWF fe →
    core_k.str_support_stored fe = ok b →
    b = ((lfe.find? ConLeche.stringName).isSome &&
          (lfe.find? ConLeche.stringOfListName).isSome &&
          (lfe.find? ConLeche.listName).isSome &&
          (lfe.find? ConLeche.listNilName).isSome &&
          (lfe.find? ConLeche.listConsName).isSome &&
          (lfe.find? ConLeche.charName).isSome &&
          (lfe.find? ConLeche.charOfNatName).isSome)

/-! ## The walk -/

/-- `ConLeche/Cached/StateC.lean:449-515` — **the memo prologue, once**: given
that the port's `consts_resolve_fc_node` answers the plain descent at this
memo, `consts_resolve_fc_go` does too.  One proof for both verdicts of the
gate: a skipped node is neither probed nor recorded and hands its table
straight on, a probed node's hit is `MemoInv.hit` and its record is
`MemoInv.set`.  The ten `ExprWF` cases below supply the node obligation and
nothing else. -/
theorem go_of_node {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {e : expr.Expr} {b : Bool}
    (hm : MemoBOk lfe memo) (he : ExprWF e)
    (hnode : ∀ (b' : Bool) (m' : ron.hashmap.HashMap expr.Expr Bool),
      cached.state_c.consts_resolve_fc_node fe memo e = ok (b', m') →
      b' = ConLeche.Cached.constsResolveFP lfe (absExpr e) ∧ MemoBOk lfe m')
    (h : cached.state_c.consts_resolve_fc_go fe memo e = ok (b, memo')) :
    b = ConLeche.Cached.constsResolveFP lfe (absExpr e) ∧ MemoBOk lfe memo' := by
  rw [cached.state_c.consts_resolve_fc_go.eq_def] at h
  obtain ⟨skip, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  cases skip with
  | true =>
    rw [memo_b_probe_true] at ho
    cases o with
    | some r => simp at ho
    | none =>
      simp only [memo_b_record_true, bind_tc_ok] at h
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, memo1⟩ := p
      obtain ⟨hb, hm1⟩ := hnode r0 memo1 hnd
      have e0 := Result.ok_injective (α := Bool × _) h
      have e1 : r0 = b := congrArg Prod.fst e0
      have e2 : memo1 = memo' := congrArg Prod.snd e0
      subst e1; subst e2
      exact ⟨hb, hm1⟩
  | false =>
    rw [memo_b_probe_false] at ho
    cases o with
    | some r =>
      have e0 := Result.ok_injective (α := Bool × _) h
      have e1 : r = b := congrArg Prod.fst e0
      have e2 : memo = memo' := congrArg Prod.snd e0
      subst e1; subst e2
      exact ⟨memo_b_get_refines hm he ho, hm⟩
    | none =>
      obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, memo1⟩ := p
      obtain ⟨hb, hm1⟩ := hnode r0 memo1 hnd
      obtain ⟨memo2, hrec, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, hdup, old, hins⟩ := memo_b_record_inv hrec
      rw [Expr.dup_eq hdup] at hins
      have e0 := Result.ok_injective (α := Bool × _) h
      have ea : r0 = b := congrArg Prod.fst e0
      have eb : memo2 = memo' := congrArg Prod.snd e0
      subst ea; subst eb
      exact ⟨hb, memo_b_insert hm1 he hb hins⟩

/-- `ConLeche/Cached/StateC.lean:449-515` — **`consts_resolve_fc_go` refines
`constsResolveFP`**: one induction on the `ExprWF` derivation, one node
obligation per constructor. -/
theorem consts_resolve_fc_go_refines (hg : LitGuardsRefine) {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} (hfrel : FEnv.FEnvRel fe lfe) (hfwf : FEnv.FEnvWF fe)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (b : Bool),
      MemoBOk lfe memo →
      cached.state_c.consts_resolve_fc_go fe memo e = ok (b, memo') →
      b = ConLeche.Cached.constsResolveFP lfe (absExpr e) ∧ MemoBOk lfe memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, Result.ok.injEq, Prod.mk.injEq] at hnd
    obtain ⟨rfl, rfl⟩ := hnd
    exact ⟨by simp [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind], hm⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, Result.ok.injEq, Prod.mk.injEq] at hnd
    obtain ⟨rfl, rfl⟩ := hnd
    exact ⟨by simp [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind], hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, bind_eq_ok_iff] at hnd
    obtain ⟨o, hfind, hnd⟩ := hnd
    have hlf := FEnv.find_refines hfrel hfwf hn hfind
    simp only [Result.ok.injEq, Prod.mk.injEq] at hnd
    obtain ⟨rfl, rfl⟩ := hnd
    refine ⟨?_, hm⟩
    simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hlf,
      core.option.Option.is_some]
    cases o <;> simp
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind] at hnd
    cases l with
    | NatVal k =>
      simp only [bind_eq_ok_iff] at hnd
      obtain ⟨bn, hbn, hnd⟩ := hnd
      have hbnv := hg.nat fe lfe bn hfrel hfwf hbn
      simp only [Result.ok.injEq, Prod.mk.injEq] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      refine ⟨?_, hm⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, absLiteral,
        hbnv]
    | StrVal s =>
      simp only [bind_eq_ok_iff] at hnd
      obtain ⟨bn, hbn, hnd⟩ := hnd
      have hbnv := hg.nat fe lfe bn hfrel hfwf hbn
      cases bn with
      | true =>
        simp only [if_true, bind_eq_ok_iff] at hnd
        obtain ⟨bs, hbs, hnd⟩ := hnd
        have hbsv := hg.str fe lfe bs hfrel hfwf hbs
        simp only [Result.ok.injEq, Prod.mk.injEq] at hnd
        obtain ⟨rfl, rfl⟩ := hnd
        refine ⟨?_, hm⟩
        simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, absLiteral]
        rw [hbsv]
        simp_all
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq,
          Prod.mk.injEq] at hnd
        obtain ⟨rfl, rfl⟩ := hnd
        refine ⟨?_, hm⟩
        simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, absLiteral]
        simp_all
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind] at hnd
    obtain ⟨hb1, hm1⟩ := ih memo m' b' hm hnd
    refine ⟨?_, hm1⟩
    simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind]
    exact hb1
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1f, hnd⟩ := hnd
    obtain ⟨bf, m1⟩ := p
    obtain ⟨hb1, hm1⟩ := ihf memo m1 bf hm h1f
    cases bf with
    | true =>
      obtain ⟨hb2, hm2⟩ := iha m1 m' b' hm1 hnd
      refine ⟨?_, hm2⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
        Bool.true_and]
      exact hb2
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      refine ⟨?_, hm1⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
        Bool.false_and]
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1t, hnd⟩ := hnd
    obtain ⟨bt, m1⟩ := p
    obtain ⟨hb1, hm1⟩ := ihty memo m1 bt hm h1t
    cases bt with
    | true =>
      obtain ⟨hb2, hm2⟩ := ihbo m1 m' b' hm1 hnd
      refine ⟨?_, hm2⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
        Bool.true_and]
      exact hb2
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      refine ⟨?_, hm1⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
        Bool.false_and]
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1t, hnd⟩ := hnd
    obtain ⟨bt, m1⟩ := p
    obtain ⟨hb1, hm1⟩ := ihty memo m1 bt hm h1t
    cases bt with
    | true =>
      obtain ⟨hb2, hm2⟩ := ihbo m1 m' b' hm1 hnd
      refine ⟨?_, hm2⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
        Bool.true_and]
      exact hb2
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      refine ⟨?_, hm1⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
        Bool.false_and]
  | @let_e ty v bo e hty hv hbo h1 ihty ihv ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hv hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1t, hnd⟩ := hnd
    obtain ⟨bt, m1⟩ := p
    obtain ⟨hb1, hm1⟩ := ihty memo m1 bt hm h1t
    cases bt with
    | true =>
      obtain ⟨q, h1v, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨bv, m2⟩ := q
      obtain ⟨hb2, hm2⟩ := ihv m1 m2 bv hm1 h1v
      cases bv with
      | true =>
        obtain ⟨hb3, hm3⟩ := ihbo m2 m' b' hm2 hnd
        refine ⟨?_, hm3⟩
        simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
          ← hb2, Bool.true_and]
        exact hb3
      | false =>
        simp at hnd
        obtain ⟨rfl, rfl⟩ := hnd
        refine ⟨?_, hm2⟩
        simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
          ← hb2, Bool.true_and, Bool.false_and]
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      refine ⟨?_, hm1⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hb1,
        Bool.false_and]
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind,
      ron.node.ExprView.ofKind, bind_eq_ok_iff] at hnd
    obtain ⟨o, hfind, hnd⟩ := hnd
    have hlf := FEnv.find_refines hfrel hfwf hs hfind
    cases o with
    | none =>
      simp only [core.option.Option.is_some, Option.isSome_none,
        Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      refine ⟨?_, hm⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hlf]
      simp
    | some ci =>
      simp only [core.option.Option.is_some, Option.isSome_some,
        if_true] at hnd
      obtain ⟨hb1, hm1⟩ := ih memo m' b' hm hnd
      refine ⟨?_, hm1⟩
      simp only [ConLeche.Cached.constsResolveFP, absExpr_mk, absExprKind, ← hlf,
        Option.map_some, Option.isSome_some, Bool.true_and]
      exact hb1

/-- `ConLeche/Cached/StateC.lean:517-519` — **`consts_resolve_fc` refines
`constsResolveFC`**: one memoized DAG walk from a fresh memo. -/
theorem consts_resolve_fc_refines (hg : LitGuardsRefine) {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} {e : expr.Expr} {b : Bool}
    (hfrel : FEnv.FEnvRel fe lfe) (hfwf : FEnv.FEnvWF fe) (he : ExprWF e)
    (h : cached.state_c.consts_resolve_fc fe e = ok b) :
    b = ConLeche.Cached.constsResolveFC lfe (absExpr e) := by
  rw [cached.state_c.consts_resolve_fc] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, memo'⟩ := p
  simp at h
  subst h
  obtain ⟨hb, -⟩ :=
    consts_resolve_fc_go_refines hg hfrel hfwf he memo memo' b0 (memo_b_new hnew) hgo
  rw [ConLeche.Cached.constsResolveFC, ConLeche.Expr.resBool_eq]
  exact hb

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/-- info: 'ConRon.Refine.StateC.consts_resolve_fc_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consts_resolve_fc_refines

end ConRon.Refine.StateC
