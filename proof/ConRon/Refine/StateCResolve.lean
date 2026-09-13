/-
`Refine/StateC.lean`'s last wrapper, in its own file because it is a *walk*:
`cached::state_c::consts_resolve_fc`, the parsed-index driver's syntactic guard
— `Expr.constsResolveF fe` as one **memoized `ExprC` DAG pass**
(`ConLeche/Cached/StateC.lean:409-450`).

Two things are different from the `*M` wrappers next door:

* the memo is **local to the call** (the result depends on the environment), so
  it is a `&mut HashMap` accumulator and not `CState` state: no §3.1 memo-policy
  obligation attaches to it, only the relation, which is `MemoBOk` below —
  `Refine/State.lean`'s three table facts (`Inv`, `KeysOk`, `RelOn`) at the
  `Expr`-keyed dictionary with `Bool` values;
* the recursion is on the term, so the proof is an induction on the `ExprWF`
  derivation (task #17's style), one case per constructor, and `go`'s memo
  prologue is shared by all ten.

## The ingredient this file does not own

The two `.lit` arms read `core_k::nat_trio_stored` and
`core_k::str_support_stored` — con-leche spells the same ten `FEnv.find?`
tests inline.  Their refinement is **task #49's `Refine/CoreK*.lean`** (and
through them `kernel::basis_names`', which no task has yet), so the two facts
travel here as one named hypothesis, `LitGuardsRefine`.  Nothing below is
weakened: the conclusion is the exact-result one, under an explicit ingredient.
-/
import ConRon.Refine.StateC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.StateC

open ConRon.Refine.State

/-! ## The call-local memo -/

/-- `ConLeche/Cached/StateC.lean:409` — the `Std.HashMap ExprC Bool` the cited
walk threads: a well-formed `ron::HashMap` holding only well-formed keys, whose
lookups agree with con-leche's under `absExpr`. -/
structure MemoBOk (memo : ron.hashmap.HashMap expr.Expr Bool)
    (lmemo : _root_.Std.HashMap ConLeche.Expr Bool) : Prop where
  inv : HashMap.Inv hExpr memo
  keys : HashMap.KeysOk ExprWF memo
  rel : HashMap.RelOn ExprWF memo lmemo absExpr id

/-- A fresh memo relates to con-leche's `{}`. -/
theorem memo_b_new {memo : ron.hashmap.HashMap expr.Expr Bool}
    (h : ron.hashmap.HashMap.new expr.Expr Bool = ok memo) :
    MemoBOk memo (∅ : _root_.Std.HashMap ConLeche.Expr Bool) :=
  ⟨new_inv h, new_keys h, new_rel h⟩

/-- `ConLeche/Cached/StateC.lean:410` — `state_c::memo_b_get` is the cited
`memo[e]?`. -/
theorem memo_b_get_refines {memo : ron.hashmap.HashMap expr.Expr Bool}
    {lmemo : _root_.Std.HashMap ConLeche.Expr Bool} {e : expr.Expr}
    {o : Option Bool} (hm : MemoBOk memo lmemo) (he : ExprWF e)
    (h : cached.state_c.memo_b_get memo e = ok o) : o = lmemo[absExpr e]? := by
  rw [cached.state_c.memo_b_get] at h
  obtain ⟨o', hget, h⟩ := bind_eq_ok_iff.mp h
  have hr := (get_step (Q := fun _ => True) exprKey hm.inv hm.keys
    (fun _ _ => trivial) hm.rel he hget).1
  cases o' with
  | none => simp only [Result.ok.injEq] at h; subst h; simpa using hr
  | some b => simp only [Result.ok.injEq] at h; subst h; simpa using hr

/-- `ConLeche/Cached/StateC.lean:446` — the walk's `memo.insert e r`. -/
theorem memo_b_insert {memo memo' : ron.hashmap.HashMap expr.Expr Bool}
    {lmemo : _root_.Std.HashMap ConLeche.Expr Bool} {e : expr.Expr} {b : Bool}
    {old : Option Bool} (hm : MemoBOk memo lmemo) (he : ExprWF e)
    (h : ron.hashmap.HashMap.insert hExpr eExpr memo e b = ok (old, memo')) :
    MemoBOk memo' (lmemo.insert (absExpr e) b) := by
  obtain ⟨h1, h2, -, h4⟩ := insert_step (Q := fun _ => True) exprKey hm.inv
    hm.keys (fun _ _ => trivial) hm.rel he trivial h
  exact ⟨h1, h2, h4⟩

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

/-! ## The walk

`nodeL` names the inner `match e with …` of `constsResolveFCGo`
(`StateC.lean:413-445`) so that the memo prologue can be proved once; the
identity `constsResolveFCGo_eq` is `rfl`. -/

/-- The inner `match e with …` of `ConLeche.Cached.constsResolveFCGo`, named. -/
def nodeL (fe : ConLeche.FEnv) (memo : _root_.Std.HashMap ConLeche.Expr Bool)
    (e : ConLeche.Expr) : Bool × _root_.Std.HashMap ConLeche.Expr Bool :=
  match e with
  | .bvar .. | .sort .. => (true, memo)
  | .lit (.natVal _) .. =>
    ((fe.find? ConLeche.natName).isSome &&
      (fe.find? ConLeche.natZeroName).isSome &&
      (fe.find? ConLeche.natSuccName).isSome, memo)
  | .lit (.strVal _) .. =>
    ((fe.find? ConLeche.natName).isSome &&
      (fe.find? ConLeche.natZeroName).isSome &&
      (fe.find? ConLeche.natSuccName).isSome &&
      (fe.find? ConLeche.stringName).isSome &&
      (fe.find? ConLeche.stringOfListName).isSome &&
      (fe.find? ConLeche.listName).isSome &&
      (fe.find? ConLeche.listNilName).isSome &&
      (fe.find? ConLeche.listConsName).isSome &&
      (fe.find? ConLeche.charName).isSome &&
      (fe.find? ConLeche.charOfNatName).isSome, memo)
  | .const nm _ .. => ((fe.find? nm).isSome, memo)
  | .fvar _ ty .. => ConLeche.Cached.constsResolveFCGo fe memo ty
  | .app f a .. =>
    let (rf, memo) := ConLeche.Cached.constsResolveFCGo fe memo f
    if rf then ConLeche.Cached.constsResolveFCGo fe memo a else (false, memo)
  | .lam ty body _ .. | .forallE ty body _ .. =>
    let (rt, memo) := ConLeche.Cached.constsResolveFCGo fe memo ty
    if rt then ConLeche.Cached.constsResolveFCGo fe memo body else (false, memo)
  | .letE ty val body .. =>
    let (rt, memo) := ConLeche.Cached.constsResolveFCGo fe memo ty
    if rt then
      let (rv, memo) := ConLeche.Cached.constsResolveFCGo fe memo val
      if rv then ConLeche.Cached.constsResolveFCGo fe memo body
      else (false, memo)
    else (false, memo)
  | .proj sn _ sub .. =>
    if (fe.find? sn).isSome then ConLeche.Cached.constsResolveFCGo fe memo sub
    else (false, memo)

/-- `ConLeche/Cached/StateC.lean:409-446` — the cited walk is its memo prologue
around `nodeL`. -/
theorem constsResolveFCGo_eq (fe : ConLeche.FEnv)
    (memo : _root_.Std.HashMap ConLeche.Expr Bool) (e : ConLeche.Expr) :
    ConLeche.Cached.constsResolveFCGo fe memo e
      = match memo[e]? with
        | some r => (r, memo)
        | none => let (r, m) := nodeL fe memo e; (r, m.insert e r) := by
  rw [ConLeche.Cached.constsResolveFCGo.eq_def]
  rfl

/-- `ConLeche/Cached/StateC.lean:409-446` — **the memo prologue, once**: given
that the port's `consts_resolve_fc_node` refines `nodeL` at this memo,
`consts_resolve_fc_go` refines `constsResolveFCGo`.  The ten `ExprWF` cases
below supply the `nodeL` obligation and nothing else. -/
theorem go_of_node {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool}
    {lmemo : _root_.Std.HashMap ConLeche.Expr Bool} {e : expr.Expr} {b : Bool}
    (hm : MemoBOk memo lmemo) (he : ExprWF e)
    (hnode : ∀ (b' : Bool) (m' : ron.hashmap.HashMap expr.Expr Bool),
      cached.state_c.consts_resolve_fc_node fe memo e = ok (b', m') →
      ∃ lm', nodeL lfe lmemo (absExpr e) = (b', lm') ∧ MemoBOk m' lm')
    (h : cached.state_c.consts_resolve_fc_go fe memo e = ok (b, memo')) :
    ∃ lmemo', ConLeche.Cached.constsResolveFCGo lfe lmemo (absExpr e)
        = (b, lmemo') ∧ MemoBOk memo' lmemo' := by
  rw [cached.state_c.consts_resolve_fc_go.eq_def] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hlk := memo_b_get_refines hm he ho
  rw [constsResolveFCGo_eq, ← hlk]
  cases o with
  | some r =>
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lmemo, rfl, hm⟩
  | none =>
    obtain ⟨p, hnd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r0, memo1⟩ := p
    obtain ⟨lm1, hlnd, hm1⟩ := hnode r0 memo1 hnd
    simp only [ConRon.Refine.State.expr_dup_eq, bind_tc_ok] at h
    obtain ⟨q, hins, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨old, memo2⟩ := q
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lm1.insert (absExpr e) r0, ?_, memo_b_insert hm1 he hins⟩
    rw [hlnd]

/-- `ConLeche/Cached/StateC.lean:409-446` — **`consts_resolve_fc_go` refines
`constsResolveFCGo`**: one induction on the `ExprWF` derivation, one `nodeL`
obligation per constructor. -/
theorem consts_resolve_fc_go_refines (hg : LitGuardsRefine) {fe : fenv.FEnv}
    {lfe : ConLeche.FEnv} (hfrel : FEnv.FEnvRel fe lfe) (hfwf : FEnv.FEnvWF fe)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool)
      (lmemo : _root_.Std.HashMap ConLeche.Expr Bool) (b : Bool),
      MemoBOk memo lmemo →
      cached.state_c.consts_resolve_fc_go fe memo e = ok (b, memo') →
      ∃ lmemo', ConLeche.Cached.constsResolveFCGo lfe lmemo (absExpr e)
          = (b, lmemo') ∧ MemoBOk memo' lmemo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, Result.ok.injEq,
      Prod.mk.injEq] at hnd
    obtain ⟨rfl, rfl⟩ := hnd
    exact ⟨lmemo, by simp [nodeL], hm⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, Result.ok.injEq,
      Prod.mk.injEq] at hnd
    obtain ⟨rfl, rfl⟩ := hnd
    exact ⟨lmemo, by simp [nodeL], hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, bind_eq_ok_iff] at hnd
    obtain ⟨o, hfind, hnd⟩ := hnd
    have hlf := FEnv.find_refines hfrel hfwf hn hfind
    simp only [Result.ok.injEq, Prod.mk.injEq] at hnd
    obtain ⟨rfl, rfl⟩ := hnd
    refine ⟨lmemo, ?_, hm⟩
    simp only [nodeL, absExpr_mk, absExprKind, ← hlf,
      core.option.Option.is_some]
    cases o <;> simp
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind] at hnd
    cases l with
    | NatVal k =>
      simp only [bind_eq_ok_iff] at hnd
      obtain ⟨bn, hbn, hnd⟩ := hnd
      have hbnv := hg.nat fe lfe bn hfrel hfwf hbn
      simp only [Result.ok.injEq, Prod.mk.injEq] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      refine ⟨lmemo, ?_, hm⟩
      simp only [nodeL, absExpr_mk, absExprKind, absLiteral, hbnv]
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
        refine ⟨lmemo, ?_, hm⟩
        simp only [nodeL, absExpr_mk, absExprKind, absLiteral]
        rw [hbsv]
        simp only [Prod.mk.injEq, and_true]
        simp_all
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq,
          Prod.mk.injEq] at hnd
        obtain ⟨rfl, rfl⟩ := hnd
        refine ⟨lmemo, ?_, hm⟩
        simp only [nodeL, absExpr_mk, absExprKind, absLiteral]
        simp_all
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind] at hnd
    obtain ⟨lm1, hl1, hm1⟩ := ih memo m' lmemo b' hm hnd
    refine ⟨lm1, ?_, hm1⟩
    simp only [nodeL, absExpr_mk, absExprKind]
    exact hl1
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1f, hnd⟩ := hnd
    obtain ⟨bf, m1⟩ := p
    obtain ⟨lm1, hl1, hm1⟩ := ihf memo m1 lmemo bf hm h1f
    simp only [nodeL, absExpr_mk, absExprKind, hl1]
    cases bf with
    | true =>
      obtain ⟨lm2, hl2, hm2⟩ := iha m1 m' lm1 b' hm1 hnd
      exact ⟨lm2, hl2, hm2⟩
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      exact ⟨lm1, rfl, hm1⟩
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1t, hnd⟩ := hnd
    obtain ⟨bt, m1⟩ := p
    obtain ⟨lm1, hl1, hm1⟩ := ihty memo m1 lmemo bt hm h1t
    simp only [nodeL, absExpr_mk, absExprKind, hl1]
    cases bt with
    | true =>
      obtain ⟨lm2, hl2, hm2⟩ := ihbo m1 m' lm1 b' hm1 hnd
      exact ⟨lm2, hl2, hm2⟩
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      exact ⟨lm1, rfl, hm1⟩
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1t, hnd⟩ := hnd
    obtain ⟨bt, m1⟩ := p
    obtain ⟨lm1, hl1, hm1⟩ := ihty memo m1 lmemo bt hm h1t
    simp only [nodeL, absExpr_mk, absExprKind, hl1]
    cases bt with
    | true =>
      obtain ⟨lm2, hl2, hm2⟩ := ihbo m1 m' lm1 b' hm1 hnd
      exact ⟨lm2, hl2, hm2⟩
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      exact ⟨lm1, rfl, hm1⟩
  | @let_e ty v bo e hty hv hbo h1 ihty ihv ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hv hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, bind_eq_ok_iff] at hnd
    obtain ⟨p, h1t, hnd⟩ := hnd
    obtain ⟨bt, m1⟩ := p
    obtain ⟨lm1, hl1, hm1⟩ := ihty memo m1 lmemo bt hm h1t
    simp only [nodeL, absExpr_mk, absExprKind, hl1]
    cases bt with
    | true =>
      obtain ⟨q, h1v, hnd⟩ := bind_eq_ok_iff.mp hnd
      obtain ⟨bv, m2⟩ := q
      obtain ⟨lm2, hl2, hm2⟩ := ihv m1 m2 lm1 bv hm1 h1v
      simp only [hl2]
      cases bv with
      | true =>
        obtain ⟨lm3, hl3, hm3⟩ := ihbo m2 m' lm2 b' hm2 hnd
        exact ⟨lm3, hl3, hm3⟩
      | false =>
        simp at hnd
        obtain ⟨rfl, rfl⟩ := hnd
        exact ⟨lm2, rfl, hm2⟩
    | false =>
      simp at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      exact ⟨lm1, rfl, hm1⟩
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' lmemo b hm h
    refine go_of_node hm hwfe ?_ h
    intro b' m' hnd
    rw [cached.state_c.consts_resolve_fc_node.eq_def] at hnd
    simp only [arc_deref_eq, bind_tc_ok, ConRon.Refine.ExprOps.node_kind, bind_eq_ok_iff] at hnd
    obtain ⟨o, hfind, hnd⟩ := hnd
    have hlf := FEnv.find_refines hfrel hfwf hs hfind
    simp only [nodeL, absExpr_mk, absExprKind, ← hlf]
    cases o with
    | none =>
      simp only [core.option.Option.is_some, Option.isSome_none,
        Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hnd
      obtain ⟨rfl, rfl⟩ := hnd
      exact ⟨lmemo, rfl, hm⟩
    | some ci =>
      simp only [core.option.Option.is_some, Option.isSome_some,
        if_true] at hnd
      obtain ⟨lm1, hl1, hm1⟩ := ih memo m' lmemo b' hm hnd
      refine ⟨lm1, ?_, hm1⟩
      simp only [Option.map_some, Option.isSome_some, if_true]
      exact hl1

/-- `ConLeche/Cached/StateC.lean:448-450` — **`consts_resolve_fc` refines
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
  obtain ⟨lmemo', hl, -⟩ :=
    consts_resolve_fc_go_refines hg hfrel hfwf he memo memo' ∅ b0
      (memo_b_new hnew) hgo
  rw [ConLeche.Cached.constsResolveFC, hl]

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/-- info: 'ConRon.Refine.StateC.consts_resolve_fc_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consts_resolve_fc_refines

end ConRon.Refine.StateC
