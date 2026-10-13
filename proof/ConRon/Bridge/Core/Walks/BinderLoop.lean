/-
# `ConRon.Bridge.Core.Walks.BinderLoop` — the two binder-telescope loops

Task #97-P3-Core round 6, lane `binders`; task #119 (con-leche's task #342:
no binder datum, so no threaded PropWhen and no leaf check).  The twin's
`inferBody` binder clauses are con-leche's CACHED-tier telescope loops
(`Arena/Core.lean`'s `inferLams`/`inferPis`), not the pure tier's per-binder
chain.  con-leche proves the loops sound against the chain in two layers, and
this module is the bridge's copy of the upper one:

1. **the carry** (here): the twin's handle-level loop denotes con-leche's
   `Expr`-level PURE MIRROR (`ConLeche/Verify/BinderLoop.lean`'s
   `inferLams`, `inferPis`) — the analogue of con-leche's own
   `Verify/Cached/BinderLoopC.lean` `…C_sim`, one bind at a time;
2. **the identification** (con-leche's): `inferLams_sound`,
   `inferPis_sound` — a successful mirror run is reproduced by the chained
   body at some fuel.

The stacks are push-order `Array`s on the twin side and cons-order `List`s
on the mirror side (`BinderLoopC.lean`'s `toListRev_push`); the rebuild
phase reads `stk[n-1]` counting down, which is the mirror's head, so the
out-phase invariant is about `(stk.toList.take n).reverse`.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.ExprOps.Owed
import ConRon.Bridge.ExprOps.Subst
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.ExprOps.Walks
import ConRon.Bridge.Core.Walks.FvarB
import ConLeche.Verify.BinderLoop

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Stack relations -/

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:98 RelILStk — two
stacks related entry by entry. -/
def StkRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ StkRel R as bs
  | _, _ => False

/-- con-leche: none — `StkRel` is monotone in the entry relation. -/
theorem StkRel.imp {α β : Type} {R R' : α → β → Prop}
    (h : ∀ a b, R a b → R' a b) :
    ∀ {as : List α} {bs : List β}, StkRel R as bs → StkRel R' as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h _ _ h1, StkRel.imp h h2⟩
  | [], _ :: _, hr => hr.elim
  | _ :: _, [], hr => hr.elim

/-- con-leche: none — related stacks have the same length. -/
theorem StkRel.length {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, StkRel R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h2⟩ => by simp [StkRel.length h2]
  | [], _ :: _, hr => hr.elim
  | _ :: _, [], hr => hr.elim

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:94 RelILE — a λ
stack entry: the opened domain handle denotes the mirror's opened domain. -/
def LamR (st : EStore) (e : EIdx) (x : Expr) : Prop :=
  denoteE st e = some x

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:351 RelLStk — a ∀
stack entry: the domain sort's level handle denotes the mirror's level. -/
def PiR (st : EStore) (e : LIdx) (x : Level) : Prop :=
  denoteL st.ls e = some x

theorem LamR.ext {st st' : EStore} (hx : Ext st st') :
    ∀ e x, LamR st e x → LamR st' e x :=
  fun _ _ h => denote_ext h hx

theorem PiR.ext {st st' : EStore} (hx : Ext st st') :
    ∀ e x, PiR st e x → PiR st' e x :=
  fun _ _ h => denoteL_ext h hx

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:77 toListRev_push —
pushing on the twin's stack conses on the mirror's. -/
theorem StkRel.push {α β : Type} {R : α → β → Prop} {stk : Array α}
    {stkx : List β} {a : α} {b : β} (h : StkRel R stk.toList.reverse stkx)
    (hab : R a b) : StkRel R (stk.push a).toList.reverse (b :: stkx) := by
  simp only [Array.toList_push, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  exact ⟨hab, h⟩

/-- con-leche: none — the out phase's step: the prefix of length `j + 1`,
reversed, is the entry at `j` over the prefix of length `j`. -/
theorem StkRel.take_succ {α β : Type} {R : α → β → Prop} {stk : Array α}
    [Inhabited α] {j : Nat} {stkx : List β} (hj : j < stk.size)
    (h : StkRel R (stk.toList.take (j + 1)).reverse stkx) :
    ∃ b rest, stkx = b :: rest ∧ R stk[j]! b ∧
      StkRel R (stk.toList.take j).reverse rest := by
  have hj' : j < stk.toList.length := by simpa using hj
  rw [List.take_add_one, List.getElem?_eq_getElem hj'] at h
  simp only [Option.toList_some, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append] at h
  cases stkx with
  | nil => exact h.elim
  | cons b rest =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨b, rest, rfl, ?_, h2⟩
    have : stk[j]! = stk.toList[j] := by
      simp [getElem!_pos, hj]
    rw [this]; exact h1

/-- con-leche: none — the whole stack is the prefix of its own length. -/
theorem StkRel.take_size {α β : Type} {R : α → β → Prop} {stk : Array α}
    {stkx : List β} (h : StkRel R stk.toList.reverse stkx) :
    StkRel R (stk.toList.take stk.size).reverse stkx := by
  rw [show stk.size = stk.toList.length by simp, List.take_length]; exact h

/-! ## 2. The λ-inference loop

### 2.1 The outward rebuild -/

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:117 inferLamsOutC_sim
— **the λ loop's rebuild carries**: the twin's count-down over the pushed
stack denotes the mirror's fold over the consed one. -/
theorem inferLamsOut_carry (d : Nat) (stk : Array EIdx) :
    ∀ (n : Nat) (s₀ : AState) (cur : EIdx) (curx : Expr) (stkx : List Expr),
      CheckOK mode env fe s₀ → denoteE s₀.store cur = some curx →
      n ≤ stk.size → StkRel (LamR s₀.store) (stk.toList.take n).reverse stkx →
      ⦃fun s => s = s₀⦄ ConRon.Arena.inferLamsOut d stk n cur
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ConLeche.inferLamsOut (m := CheckM) d stkx (n - 1) curx
            = .ok v; ⊤⦄
  | 0, s₀, cur, curx, stkx, hok, hcur, _, hstk => by
    cases stkx with
    | cons _ _ => exact hstk.elim
    | nil =>
      rw [ConRon.Arena.inferLamsOut]
      vcgen +internalize
      bridge_peel; subst_vars
      exact ⟨hok, Ext.refl _, rfl, curx, hcur, rfl⟩
  | j + 1, s₀, cur, curx, stkx, hok, hcur, hle, hstk => by
    obtain ⟨tyox, rest, rfl, hty, hrest⟩ :=
      StkRel.take_succ (Nat.lt_of_succ_le hle) hstk
    rw [ConRon.Arena.inferLamsOut]
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    refine triple_seq (ExprOps.abstractRangeFast_spec fvarBSpec
      coreWalkFuel s₀ stk[j]! d j 0 hok.state (by rw [hty]; rfl)) ?_
    rintro tyAbs s1 ⟨hs1, hx1, hc1, hp1, -, hrel1⟩
    have hok1 := hok.mono hs1 hx1 hc1 hp1
    have hta : denoteE s1.store tyAbs = some (tyox.abstractRange d j) :=
      hrel1 _ hty
    refine triple_seq (internForallEE_spec s1 tyAbs cur hs1.wf
      (by rw [hta]; rfl) (by rw [denote_ext hcur hx1]; rfl)) ?_
    rintro nd s2 ⟨hwf2, hx2, -, -, -, hc2, hp2, -, hd2⟩
    have hok2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
    have hnd : denoteE s2.store nd =
        some (.forallE (tyox.abstractRange d j) curx) := by
      rw [hd2]
      simp [denoteEView, denote_ext hta hx2, denote_ext hcur (hx1.trans hx2)]
    have hx02 : Ext s₀.store s2.store := hx1.trans hx2
    refine triple_mono (inferLamsOut_carry d stk j s2 nd _ rest hok2 hnd
      (Nat.le_of_succ_le hle)
      (StkRel.imp (LamR.ext hx02) hrest)) ?_
    rintro r s' ⟨hok', hx', hp', v, hv, hrun⟩
    exact ⟨hok', hx02.trans hx', hp'.trans (hp2.trans hp1), v, hv, hrun⟩

/-! ### 2.2 Shape facts the loops read off a handle -/

/-- con-leche: none — a handle whose tag is not `lam` denotes no λ. -/
theorem denote_not_lam_of_tag {st : EStore} (hwf : StoreWF st) {t : EIdx}
    {tx : Expr} (hd : denoteE st t = some tx) (hne : t.tag ≠ ETag.lam) :
    ∀ p q, tx ≠ .lam p q := by
  rintro p q rfl
  exact hne (ExprOps.tag_lam_of_denote hwf hd)

/-- con-leche: none — a handle whose tag is not `forallE` denotes no ∀. -/
theorem denote_not_forallE_of_tag {st : EStore} (hwf : StoreWF st) {t : EIdx}
    {tx : Expr} (hd : denoteE st t = some tx) (hne : t.tag ≠ ETag.forallE) :
    ∀ p q, tx ≠ .forallE p q := by
  rintro p q rfl
  have h := ExprOps.isForallE_rel hwf hd
  simp only [ConRon.Arena.isForallE, Expr.isForallE, beq_iff_eq] at h
  exact hne h

/-- con-leche: none — a `sort`-tagged handle denotes a sort. -/
theorem denote_sort_of_tag {st : EStore} (hwf : StoreWF st) {w : EIdx}
    {wx : Expr} (hd : denoteE st w = some wx)
    (ht : (w.tag == ETag.sort) = true) : ∃ l, wx = .sort l := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  have htg := EStore.tagOf_of_view hv
  have ht' : w.tag = ETag.sort := by simpa using ht
  cases v
  case sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hd
    exact ⟨l, rfl⟩
  all_goals
    exfalso
    rw [ht'] at htg
    simp [ENodeView.tagOf, ETag.proj, ETag.app, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit] at htg

/-- con-leche: ConLeche/Kernel/Core.lean:1049-1055 ensureSort — **the twin's
`ensureSort` at the knot record**: one `whnf` slot call and a sort view. -/
theorem ensureSortK_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.ensureSort (coreKnot mode fe id fuel) fe d i
    ⦃fun u s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ l, denoteL s'.store.ls u = some l ∧
        ∃ F, ConLeche.whnf mode env F d e = .ok (.sort l); ⊤⦄ := by
  unfold ConRon.Arena.ensureSort
  refine triple_seq (hsim.whnf s₀ d i e hok hden hw) ?_
  rintro w s1 ⟨hok1, hx1, hp1, wx, hwx, -, F, hF⟩
  obtain ⟨v, hv⟩ := denoteE_view hwx
  refine tag_view_bind_triple hv ?_
    (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
  cases v
  case sort u =>
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv hok1.state.wf hv hwx
    dsimp only
    vcgen
    bridge_peel; subst_vars
    exact ⟨hok1, hx1, hp1, l, hl, F, hF⟩
  all_goals (dsimp only; exact triple_fail)

/-! ### 2.3 The λ leaf -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:60-65 inferLamsLeaf — the
mirror's leaf, from its two facts. -/
theorem mInferLamsLeaf {F d k : Nat} {tx bt v : Expr} {ws : List Expr}
    {stkx : List Expr}
    (hb : ConLeche.inferTypeCore mode env F (d + k) (tx.instantiateList ws)
      = .ok bt)
    (hout : ConLeche.inferLamsOut (m := CheckM) d stkx (k - 1)
      (bt.abstractRange d k) = .ok v) :
    ConLeche.inferLamsLeaf (ConLeche.pureFns mode env F) d tx k ws stkx
      = .ok v := by
  unfold ConLeche.inferLamsLeaf
  rw [infer_def, hb, ConLeche.okB_bind]
  exact hout

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:168 inferLamsLeafC_sim
— **the λ loop's leaf carries**: bulk open, infer, the leaf's
`abstractRange`, and the rebuild. -/
theorem inferLamsLeaf_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (t : EIdx) (k : Nat) (fvs : Array EIdx)
    (stk : Array EIdx) (tx : Expr) (ws : List Expr) (stkx : List Expr)
    (hok : CheckOK mode env fe s₀) (ht : denoteE s₀.store t = some tx)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hstk : StkRel (LamR s₀.store) stk.toList.reverse stkx)
    (hk : stk.size = k)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.inferLamsLeaf (coreKnot mode fe id fuel) d t k fvs stk
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
        ∃ F, ConLeche.inferLamsLeaf (ConLeche.pureFns mode env F) d tx k
          ws stkx = .ok v; ⊤⦄ := by
  unfold ConRon.Arena.inferLamsLeaf
  -- stage 1: the residual, opened in bulk
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ t fvs 0 ws
    hok.state hvec (by rw [ht]; rfl)) ?_
  rintro ob s1 ⟨hs1, hx1, hc1, hp1, -, hrel1⟩
  have hok1 := hok.mono hs1 hx1 hc1 hp1
  have hob : denoteE s1.store ob = some (tx.instantiateList ws) := hrel1 _ ht
  -- stage 2: its type
  refine triple_seq (hsim.infer s1 (d + k) ob _ hok1 hob hw) ?_
  rintro bt s2 ⟨hok2, hx2, hp2, btx, hbtx, -, F1, hF1⟩
  have hx02 := hx1.trans hx2
  -- stage 3: closed over the opened variables
  refine triple_seq (ExprOps.abstractRangeFast_spec fvarBSpec coreWalkFuel s2 bt
    d k 0 hok2.state (by rw [hbtx]; rfl)) ?_
  rintro cur s3 ⟨hs3, hx3, hc3, hp3, -, hrel3⟩
  have hok3 := hok2.mono hs3 hx3 hc3 hp3
  have hcur : denoteE s3.store cur = some (btx.abstractRange d k) :=
    hrel3 _ hbtx
  have hx03 := hx02.trans hx3
  -- stage 4: the rebuild
  refine triple_mono (inferLamsOut_carry d stk stk.size s3 cur _ stkx
    hok3 hcur (Nat.le_refl _)
    (StkRel.take_size (StkRel.imp (LamR.ext hx03) hstk))) ?_
  rintro r s' ⟨hok', hx', hp', v, hv, hrun⟩
  refine ⟨hok', hx03.trans hx', hp'.trans (hp3.trans (hp2.trans hp1)), v, hv,
    F1, ?_⟩
  rw [hk] at hrun
  exact mInferLamsLeaf hF1 hrun

/-! ### 2.4 The peel -/

/-- con-leche: none — the mirror is fuel-monotone (it is a `FueledM` run,
`inferLams_atF`). -/
theorem mInferLams_mono {d peel k : Nat} {t v : Expr} {ws : List Expr}
    {stkx : List Expr} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.inferLams (ConLeche.pureFns mode env F) d peel t k ws stkx
      = .ok v) :
    ConLeche.inferLams (ConLeche.pureFns mode env F') d peel t k ws stkx
      = .ok v := by
  rw [← ConLeche.inferLams_atF] at h ⊢
  exact (ConLeche.inferLams (ConLeche.fueledFns mode env) d peel t k ws
    stkx).property hle h

/-- con-leche: none — opening a binder's body at the next free variable
keeps it scoped one level deeper (con-leche's `hwopen`, BinderLoopC.lean). -/
theorem wscoped_open_cons {D : Nat} {ty body : Expr} {ws : List Expr}
    (hty : Expr.WScoped D (ty.instantiateList ws))
    (hbody : Expr.WScoped D (body.instantiateList ws 1)) :
    Expr.WScoped (D + 1)
      (body.instantiateList (Expr.fvar D (ty.instantiateList ws) :: ws)) := by
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1 hty 0 hbody

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:264 inferLamsC_sim —
**THE λ-TELESCOPE LOOP CARRIES**: the twin's `inferLams` at a residual `t`,
a push-order free-variable vector and a push-order stack denotes the
mirror's `inferLams` at the same peel budget. -/
theorem inferLams_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) :
    ∀ (peel : Nat) (s₀ : AState) (t : EIdx) (k : Nat) (fvs : Array EIdx)
      (stk : Array EIdx) (tx : Expr) (ws : List Expr) (stkx : List Expr),
      CheckOK mode env fe s₀ → denoteE s₀.store t = some tx →
      ExprOps.InstLVec s₀.store fvs ws →
      StkRel (LamR s₀.store) stk.toList.reverse stkx → stk.size = k →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.inferLams (coreKnot mode fe id fuel) d peel t k
          fvs stk
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ∃ F, ConLeche.inferLams (ConLeche.pureFns mode env F) d peel tx
            k ws stkx = .ok v; ⊤⦄
  | 0, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hk, hw => by
    rw [ConRon.Arena.inferLams]
    refine triple_mono (inferLamsLeaf_carry hsim s₀ d t k fvs stk tx ws stkx hok
      ht hvec hstk hk hw) ?_
    rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
    exact ⟨h1, h2, h3, v, hv, F, by rw [ConLeche.inferLams_zero]; exact hF⟩
  | peel + 1, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hk, hw => by
    have hwf := hok.state.wf
    rw [ConRon.Arena.inferLams]
    split
    next htg =>
      have hne : t.tag ≠ ETag.lam := by simpa using htg
      have hnl := denote_not_lam_of_tag hwf ht hne
      refine triple_mono (inferLamsLeaf_carry hsim s₀ d t k fvs stk tx ws stkx
        hok ht hvec hstk hk hw) ?_
      rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
      exact ⟨h1, h2, h3, v, hv, F,
        by rw [ConLeche.inferLams_succ_ne_lam _ hnl]; exact hF⟩
    next htg =>
      have htl : t.tag = ETag.lam := by simpa using htg
      refine triple_seq (viewBind_spec s₀ t) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1
      cases ob with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨ty, body⟩ := p
        dsimp only
        have hv := view_of_viewBind_lam htl hob.symm
        obtain ⟨tyx, bodyx, rfl, hty, hbody⟩ := denote_lam_inv hwf hv ht
        have hlamL : (Expr.lam tyx bodyx).instantiateList ws
            = .lam (tyx.instantiateList ws) (bodyx.instantiateList ws 1) := by
          simp [Expr.instantiateList]
        have hwc : Expr.WScoped (d + k) (tyx.instantiateList ws) ∧
            Expr.WScoped (d + k) (bodyx.instantiateList ws 1) := by
          rw [hlamL] at hw; simpa only [Expr.WScoped] using hw
        -- stage 1: the domain, opened in bulk
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty fvs
          0 ws hok.state hvec (by rw [hty]; rfl)) ?_
        rintro tyo s1 ⟨hs1, hx1, hc1, hp1, -, hrel1⟩
        have hok1 := hok.mono hs1 hx1 hc1 hp1
        have htyo : denoteE s1.store tyo = some (tyx.instantiateList ws) :=
          hrel1 _ hty
        -- stage 2: its type
        refine triple_seq (hsim.infer s1 (d + k) tyo _ hok1 htyo hwc.1) ?_
        rintro tty s2 ⟨hok2, hx2, hp2, ttyx, httyx, hwttyx, F1, hF1⟩
        -- stage 3: reduced
        refine triple_seq (hsim.whnf s2 (d + k) tty ttyx hok2 httyx hwttyx) ?_
        rintro w s3 ⟨hok3, hx3, hp3, wx, hwx, -, F2, hF2⟩
        split
        next hsort =>
          obtain ⟨l, rfl⟩ := denote_sort_of_tag hok3.state.wf hwx hsort
          have hx03 := hx1.trans (hx2.trans hx3)
          have htyo3 := denote_ext htyo (hx2.trans hx3)
          -- stage 4: the free variable
          refine triple_seq (internFVarE_spec s3 (d + k) tyo hok3.state.wf
            (by rw [htyo3]; rfl)) ?_
          rintro fv s4 ⟨hwf4, hx4, -, -, -, hc4, hp4, -, hd4⟩
          have hok4 := hok3.mono ⟨hwf4⟩ hx4 hc4 hp4
          have hfv : denoteE s4.store fv =
              some (.fvar (d + k) (tyx.instantiateList ws)) := by
            rw [hd4]; simp [denoteEView, denote_ext htyo3 hx4]
          have hx04 := hx03.trans hx4
          -- stage 5: the rest of the chain
          refine triple_mono (inferLams_carry hsim d peel s4 body (k + 1)
            (fvs.push fv) (stk.push tyo) bodyx
            (Expr.fvar (d + k) (tyx.instantiateList ws) :: ws)
            (tyx.instantiateList ws :: stkx) hok4
            (denote_ext hbody hx04)
            (InstLVec.push (hvec.ext hx04) hfv)
            (StkRel.push (StkRel.imp (LamR.ext hx04) hstk)
              (denote_ext htyo (hx2.trans (hx3.trans hx4))))
            (by simp [hk])
            (by rw [show d + (k + 1) = d + k + 1 by omega]
                exact wscoped_open_cons hwc.1 hwc.2)) ?_
          rintro r s' ⟨hok', hx', hp', v, hv', F3, hF3⟩
          refine ⟨hok', hx04.trans hx', hp'.trans (hp4.trans (hp3.trans
            (hp2.trans hp1))), v, hv', max (max F1 F2) F3, ?_⟩
          rw [ConLeche.inferLams_succ_lam, infer_def,
            ConLeche.inferTypeCore_mono (Nat.le_trans (Nat.le_max_left F1 F2)
              (Nat.le_max_left _ F3)) hF1, ConLeche.okB_bind, whnf_def,
            ConLeche.whnf_mono (Nat.le_trans (Nat.le_max_right F1 F2)
              (Nat.le_max_left _ F3)) hF2, ConLeche.okB_bind]
          exact mInferLams_mono (Nat.le_max_right _ _) hF3
        next => exact triple_fail

/-! ### 2.5 The `.lam` clause -/

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:595 inferLamsC_tail_sim
(its `himp` half) — **the pure side of the `.lam` clause**: a mirror run of
the loop at the one-binder start is the chained `inferBody` λ clause at a
larger fuel, by con-leche's `inferLams_sound`. -/
theorem inferTypeCore_lam_of_loop {d F1 F2 F3 : Nat} {tyx bodyx ttyx : Expr}
    {u : Level} {v : Expr} {peel : Nat}
    (hF1 : ConLeche.inferTypeCore mode env F1 d tyx = .ok ttyx)
    (hF2 : ConLeche.whnf mode env F2 d ttyx = .ok (.sort u))
    (hF3 : ConLeche.inferLams (ConLeche.pureFns mode env F3) d peel bodyx 1
      [Expr.fvar d tyx] [tyx] = .ok v) :
    ∃ F, ConLeche.inferTypeCore mode env F d (.lam tyx bodyx) = .ok v := by
  obtain ⟨F', hchain⟩ := ConLeche.inferLams_sound (env := env) peel bodyx 1
    [Expr.fvar d tyx] [tyx] F3 v rfl hF3
  obtain ⟨bt, hbt, htail⟩ := ConLeche.bind_okB hchain
  let G := max (max F1 F2) F'
  have hle1 : F1 ≤ G := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hle2 : F2 ≤ G := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hle3 : F' ≤ G := Nat.le_max_right _ _
  refine ⟨G + 1, ?_⟩
  rw [ConLeche.inferTypeCore_lam_eq, ConLeche.inferTypeCore_mono hle1 hF1,
    ConLeche.okB_bind, ConLeche.whnf_mono hle2 hF2, ConLeche.okB_bind]
  dsimp only
  have hbt' : ConLeche.inferTypeCore mode env G (d + 1)
      (bodyx.instantiate1 (.fvar d tyx)) = .ok bt := by
    rw [← ConLeche.instList_single bodyx (Expr.fvar d tyx)]
    exact ConLeche.inferTypeCore_mono hle3 hbt
  rw [hbt', ConLeche.okB_bind]
  simpa [ConLeche.inferLamsWrap] using htail

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:595 inferLamsC_tail_sim
— **THE `.lam` CLAUSE CARRIES**: the twin's `inferLam` (domain type, its
sort, the first free variable, then `inferLams` from `k = 1`) against
con-leche's chained `inferBody` λ clause. -/
theorem inferLam_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty body : EIdx)
    (tyx bodyx : Expr) (hok : CheckOK mode env fe s₀)
    (hty : denoteE s₀.store ty = some tyx)
    (hbody : denoteE s₀.store body = some bodyx)
    (hw : Expr.WScoped d (.lam tyx bodyx)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.inferLam (coreKnot mode fe id fuel) d ty body
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d (.lam tyx bodyx)
          s'.store r; ⊤⦄ := by
  have hwty : Expr.WScoped d tyx := by unfold Expr.WScoped at hw; exact hw.1
  have hwbody : Expr.WScoped d bodyx := by unfold Expr.WScoped at hw; exact hw.2
  unfold ConRon.Arena.inferLam
  refine triple_seq (hsim.infer s₀ d ty tyx hok hty hwty) ?_
  rintro tty s1 ⟨hok1, hx1, hp1, ttyx, httyx, hwttyx, F1, hF1⟩
  refine triple_seq (hsim.whnf s1 d tty ttyx hok1 httyx hwttyx) ?_
  rintro w s2 ⟨hok2, hx2, hp2, wx, hwx, -, F2, hF2⟩
  split
  next hsort =>
    obtain ⟨u, rfl⟩ := denote_sort_of_tag hok2.state.wf hwx hsort
    have hx02 := hx1.trans hx2
    have hty2 := denote_ext hty hx02
    refine triple_seq (internFVarE_spec s2 d ty hok2.state.wf
      (by rw [hty2]; rfl)) ?_
    rintro fv s3 ⟨hwf3, hx3, -, -, -, hc3, hp3, -, hd3⟩
    have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
    have hfv : denoteE s3.store fv = some (.fvar d tyx) := by
      rw [hd3]; simp [denoteEView, denote_ext hty2 hx3]
    have hx03 := hx02.trans hx3
    have hvec : ExprOps.InstLVec s3.store #[fv] [Expr.fvar d tyx] :=
      InstLVec.push (InstLVec.empty _) hfv
    have hstk : StkRel (LamR s3.store) (#[ty] : Array _).toList.reverse
        [tyx] :=
      StkRel.push (stk := #[]) (stkx := []) trivial (denote_ext hty hx03)
    have hwopen : Expr.WScoped (d + 1)
        (bodyx.instantiateList [Expr.fvar d tyx]) := by
      rw [ConLeche.instList_single]
      exact Expr.WScoped.instantiate1 hwty 0 hwbody
    refine triple_mono (inferLams_carry hsim d peelFuel s3 body 1 #[fv]
      #[ty] bodyx [Expr.fvar d tyx] [tyx] hok3
      (denote_ext hbody hx03) hvec hstk rfl hwopen) ?_
    rintro r s' ⟨hok', hx', hp', v, hv, F3, hF3⟩
    obtain ⟨F, hF⟩ := inferTypeCore_lam_of_loop hF1 hF2 hF3
    exact ⟨hok', hx03.trans hx', hp'.trans (hp3.trans (hp2.trans hp1)), v, hv,
      ConLeche.inferTypeCore_WScoped henv F hF hw, F, hF⟩
  next => exact triple_fail

/-! ## 3. The ∀-inference loop

### 3.1 The outward `imax` fold -/

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:359 inferPisOutC_sim
— **the ∀ loop's fold carries** (con-leche's task #272: the fold reads no
per-node datum). -/
theorem inferPisOut_carry (stk : Array LIdx) :
    ∀ (n : Nat) (s₀ : AState) (v : LIdx) (vx : Level) (stkx : List Level),
      CheckOK mode env fe s₀ → denoteL s₀.store.ls v = some vx →
      n ≤ stk.size → StkRel (PiR s₀.store) (stk.toList.take n).reverse stkx →
      ⦃fun s => s = s₀⦄ ConRon.Arena.inferPisOut stk n v
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ lx, denoteL s'.store.ls r = some lx ∧
          ConLeche.inferPisOut (m := CheckM) stkx vx = .ok lx; ⊤⦄
  | 0, s₀, v, vx, stkx, hok, hv, _, hstk => by
    cases stkx with
    | cons _ _ => exact hstk.elim
    | nil =>
      rw [ConRon.Arena.inferPisOut]
      vcgen +internalize
      bridge_peel; subst_vars
      exact ⟨hok, Ext.refl _, rfl, vx, hv, rfl⟩
  | j + 1, s₀, v, vx, stkx, hok, hv, hle, hstk => by
    obtain ⟨ux, rest, rfl, hu, hrest⟩ :=
      StkRel.take_succ (Nat.lt_of_succ_le hle) hstk
    rw [ConRon.Arena.inferPisOut]
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have hvo : s₀.store.ls.ViewOK (.imax stk[j]! v) := by
      constructor
      · intro c hc
        simp only [LNodeView.lchildren, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact lview_isSome_of_denote hu
        · exact lview_isSome_of_denote hv
      · intro c hc; simp [LNodeView.nchildren] at hc
    refine triple_seq (internLNode_spec s₀ (.imax stk[j]! v) hok.state.wf hvo) ?_
    rintro v2 s1 ⟨hwf1, hx1, -, -, -, -, hc1, hp1, -, hd1⟩
    have hok1 := hok.mono ⟨hwf1⟩ hx1 hc1 hp1
    have hv2 : denoteL s1.store.ls v2 = some (.imax ux vx) := by
      rw [hd1]
      simp [denoteLView, opt2, denoteL_ext hu hx1, denoteL_ext hv hx1]
    refine triple_mono (inferPisOut_carry stk j s1 v2 _ rest hok1 hv2
      (Nat.le_of_succ_le hle) (StkRel.imp (PiR.ext hx1) hrest)) ?_
    rintro r s' ⟨hok', hx', hp', lx, hl, hrun⟩
    exact ⟨hok', hx1.trans hx', hp'.trans hp1, lx, hl, hrun⟩

/-! ### 3.2 The ∀ leaf -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:88-96 inferPisLeaf — the
mirror's leaf, from its three facts. -/
theorem mInferPisLeaf {F d k : Nat} {tx bt : Expr} {vx lx : Level}
    {ws : List Expr} {stkx : List Level}
    (hb : ConLeche.inferTypeCore mode env F (d + k) (tx.instantiateList ws)
      = .ok bt)
    (hw : ConLeche.whnf mode env F (d + k) bt = .ok (.sort vx))
    (hout : ConLeche.inferPisOut (m := CheckM) stkx vx = .ok lx) :
    ConLeche.inferPisLeaf (ConLeche.pureFns mode env F) d tx k ws stkx
      = .ok (.sort lx) := by
  unfold ConLeche.inferPisLeaf
  rw [infer_def, hb, ConLeche.okB_bind, whnf_def, hw, ConLeche.okB_bind]
  dsimp only
  rw [hout, ConLeche.okB_bind]
  rfl

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:405 inferPisLeafC_sim
— **the ∀ loop's leaf carries**: bulk open, infer, the sort, the fold, the
sort node. -/
theorem inferPisLeaf_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (t : EIdx) (k : Nat) (fvs : Array EIdx)
    (stk : Array LIdx) (tx : Expr) (ws : List Expr) (stkx : List Level)
    (hok : CheckOK mode env fe s₀) (ht : denoteE s₀.store t = some tx)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hstk : StkRel (PiR s₀.store) stk.toList.reverse stkx)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.inferPisLeaf (coreKnot mode fe id fuel) fe d t k fvs stk
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
        ∃ F, ConLeche.inferPisLeaf (ConLeche.pureFns mode env F) d tx k
          ws stkx = .ok v; ⊤⦄ := by
  unfold ConRon.Arena.inferPisLeaf
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ t fvs 0 ws
    hok.state hvec (by rw [ht]; rfl)) ?_
  rintro ob s1 ⟨hs1, hx1, hc1, hp1, -, hrel1⟩
  have hok1 := hok.mono hs1 hx1 hc1 hp1
  have hob : denoteE s1.store ob = some (tx.instantiateList ws) := hrel1 _ ht
  refine triple_seq (hsim.infer s1 (d + k) ob _ hok1 hob hw) ?_
  rintro bt s2 ⟨hok2, hx2, hp2, btx, hbtx, hwbtx, F1, hF1⟩
  refine triple_seq (ensureSortK_spec hsim s2 (d + k) bt btx hok2 hbtx hwbtx) ?_
  rintro v s3 ⟨hok3, hx3, hp3, vx, hvx, F2, hF2⟩
  have hx03 := hx1.trans (hx2.trans hx3)
  refine triple_seq (inferPisOut_carry stk stk.size s3 v vx stkx hok3 hvx
    (Nat.le_refl _) (StkRel.take_size (StkRel.imp (PiR.ext hx03) hstk))) ?_
  rintro iv s5 ⟨hok5, hx5, hp5, lx, hlx, hrun⟩
  refine triple_mono (internSortE_spec s5 iv hok5.state.wf
    (lview_isSome_of_denote hlx)) ?_
  rintro r s6 ⟨hwf6, hx6, -, -, -, hc6, hp6, -, hd6⟩
  have hok6 := hok5.mono ⟨hwf6⟩ hx6 hc6 hp6
  refine ⟨hok6, hx03.trans (hx5.trans hx6),
    hp6.trans (hp5.trans (hp3.trans (hp2.trans hp1))),
    .sort lx, by rw [hd6]; simp [denoteEView, denoteL_ext hlx hx6],
    max F1 F2, ?_⟩
  exact mInferPisLeaf (ConLeche.inferTypeCore_mono (Nat.le_max_left _ _) hF1)
    (ConLeche.whnf_mono (Nat.le_max_right _ _) hF2) hrun

/-! ### 3.3 The ∀ peel -/

/-- con-leche: none — the ∀ mirror is fuel-monotone (`inferPis_atF`). -/
theorem mInferPis_mono {d peel k : Nat} {t v : Expr} {ws : List Expr}
    {stkx : List Level} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.inferPis (ConLeche.pureFns mode env F) d peel t k ws stkx
      = .ok v) :
    ConLeche.inferPis (ConLeche.pureFns mode env F') d peel t k ws stkx
      = .ok v := by
  rw [← ConLeche.inferPis_atF] at h ⊢
  exact (ConLeche.inferPis (ConLeche.fueledFns mode env) d peel t k ws
    stkx).property hle h

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:436 inferPisC_sim —
**THE ∀-TELESCOPE LOOP CARRIES**. -/
theorem inferPis_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) :
    ∀ (peel : Nat) (s₀ : AState) (t : EIdx) (k : Nat) (fvs : Array EIdx)
      (stk : Array LIdx) (tx : Expr) (ws : List Expr) (stkx : List Level),
      CheckOK mode env fe s₀ → denoteE s₀.store t = some tx →
      ExprOps.InstLVec s₀.store fvs ws →
      StkRel (PiR s₀.store) stk.toList.reverse stkx →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.inferPis (coreKnot mode fe id fuel) fe d peel t k
          fvs stk
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ∃ F, ConLeche.inferPis (ConLeche.pureFns mode env F) d peel tx
            k ws stkx = .ok v; ⊤⦄
  | 0, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hw => by
    rw [ConRon.Arena.inferPis]
    refine triple_mono (inferPisLeaf_carry hsim s₀ d t k fvs stk tx ws stkx hok
      ht hvec hstk hw) ?_
    rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
    exact ⟨h1, h2, h3, v, hv, F, by rw [ConLeche.inferPis_zero]; exact hF⟩
  | peel + 1, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hw => by
    have hwf := hok.state.wf
    rw [ConRon.Arena.inferPis]
    split
    next htg =>
      have hne : t.tag ≠ ETag.forallE := by simpa using htg
      have hnp := denote_not_forallE_of_tag hwf ht hne
      refine triple_mono (inferPisLeaf_carry hsim s₀ d t k fvs stk tx ws stkx
        hok ht hvec hstk hw) ?_
      rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
      exact ⟨h1, h2, h3, v, hv, F,
        by rw [ConLeche.inferPis_succ_ne_pi _ hnp]; exact hF⟩
    next htg =>
      have htp : t.tag = ETag.forallE := by simpa using htg
      refine triple_seq (viewBind_spec s₀ t) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1
      cases ob with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨ty, body⟩ := p
        dsimp only
        have hv := view_of_viewBind_forallE htp hob.symm
        obtain ⟨tyx, bodyx, rfl, hty, hbody⟩ := denote_forallE_inv hwf hv ht
        have hpiL : (Expr.forallE tyx bodyx).instantiateList ws
            = .forallE (tyx.instantiateList ws)
              (bodyx.instantiateList ws 1) := by
          simp [Expr.instantiateList]
        have hwc : Expr.WScoped (d + k) (tyx.instantiateList ws) ∧
            Expr.WScoped (d + k) (bodyx.instantiateList ws 1) := by
          rw [hpiL] at hw; simpa only [Expr.WScoped] using hw
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty fvs
          0 ws hok.state hvec (by rw [hty]; rfl)) ?_
        rintro tyo s1 ⟨hs1, hx1, hc1, hp1, -, hrel1⟩
        have hok1 := hok.mono hs1 hx1 hc1 hp1
        have htyo : denoteE s1.store tyo = some (tyx.instantiateList ws) :=
          hrel1 _ hty
        refine triple_seq (hsim.infer s1 (d + k) tyo _ hok1 htyo hwc.1) ?_
        rintro tty s2 ⟨hok2, hx2, hp2, ttyx, httyx, hwttyx, F1, hF1⟩
        refine triple_seq (hsim.whnf s2 (d + k) tty ttyx hok2 httyx hwttyx) ?_
        rintro w s3 ⟨hok3, hx3, hp3, wx, hwx, -, F2, hF2⟩
        split
        next hsort =>
          refine triple_seq (viewSort_spec s3 w) ?_
          rintro ou s3' ⟨hs3', hou⟩
          subst s3'
          cases ou with
          | none => exact triple_failDanglingE
          | some u =>
            dsimp only
            have hvw := view_of_viewSort_tag hsort hou.symm
            obtain ⟨ux, rfl, hux⟩ := denote_sort_inv hok3.state.wf hvw hwx
            have hx03 := hx1.trans (hx2.trans hx3)
            have htyo3 := denote_ext htyo (hx2.trans hx3)
            refine triple_seq (internFVarE_spec s3 (d + k) tyo hok3.state.wf
              (by rw [htyo3]; rfl)) ?_
            rintro fv s4 ⟨hwf4, hx4, -, -, -, hc4, hp4, -, hd4⟩
            have hok4 := hok3.mono ⟨hwf4⟩ hx4 hc4 hp4
            have hfv : denoteE s4.store fv =
                some (.fvar (d + k) (tyx.instantiateList ws)) := by
              rw [hd4]; simp [denoteEView, denote_ext htyo3 hx4]
            have hx04 := hx03.trans hx4
            refine triple_mono (inferPis_carry hsim d peel s4 body (k + 1)
              (fvs.push fv) (stk.push u) bodyx
              (Expr.fvar (d + k) (tyx.instantiateList ws) :: ws)
              (ux :: stkx) hok4
              (denote_ext hbody hx04)
              (InstLVec.push (hvec.ext hx04) hfv)
              (StkRel.push (StkRel.imp (PiR.ext hx04) hstk)
                (denoteL_ext hux hx4))
              (by rw [show d + (k + 1) = d + k + 1 by omega]
                  exact wscoped_open_cons hwc.1 hwc.2)) ?_
            rintro r s' ⟨hok', hx', hp', v, hv', F3, hF3⟩
            refine ⟨hok', hx04.trans hx', hp'.trans (hp4.trans (hp3.trans
              (hp2.trans hp1))), v, hv', max (max F1 F2) F3, ?_⟩
            rw [ConLeche.inferPis_succ_pi, infer_def,
              ConLeche.inferTypeCore_mono (Nat.le_trans (Nat.le_max_left F1 F2)
                (Nat.le_max_left _ F3)) hF1, ConLeche.okB_bind, whnf_def,
              ConLeche.whnf_mono (Nat.le_trans (Nat.le_max_right F1 F2)
                (Nat.le_max_left _ F3)) hF2, ConLeche.okB_bind]
            exact mInferPis_mono (Nat.le_max_right _ _) hF3
        next => exact triple_fail

/-! ### 3.4 The `.forallE` clause -/

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:790 inferPisC_tail_sim
(its `himp` half) — **the pure side of the `.forallE` clause**, by
con-leche's `inferPis_sound`. -/
theorem inferTypeCore_forallE_of_loop {d F1 F2 F3 : Nat} {tyx bodyx ttyx : Expr}
    {ux : Level} {v : Expr} {peel : Nat}
    (hF1 : ConLeche.inferTypeCore mode env F1 d tyx = .ok ttyx)
    (hF2 : ConLeche.whnf mode env F2 d ttyx = .ok (.sort ux))
    (hF3 : ConLeche.inferPis (ConLeche.pureFns mode env F3) d peel bodyx 1
      [Expr.fvar d tyx] [ux] = .ok v) :
    ∃ F, ConLeche.inferTypeCore mode env F d (.forallE tyx bodyx) = .ok v := by
  obtain ⟨F', hchain⟩ := ConLeche.inferPis_sound (env := env) peel bodyx 1
    [Expr.fvar d tyx] [ux] F3 v rfl (Nat.le_refl 1) hF3
  obtain ⟨bt, hbt, hwrap⟩ := ConLeche.bind_okB hchain
  let G := max (max F1 F2) F'
  have hle1 : F1 ≤ G := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hle2 : F2 ≤ G := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hle3 : F' ≤ G := Nat.le_max_right _ _
  refine ⟨G + 1, ?_⟩
  rw [ConLeche.inferTypeCore_forallE_eq, ConLeche.inferTypeCore_mono hle1 hF1,
    ConLeche.okB_bind, ConLeche.whnf_mono hle2 hF2, ConLeche.okB_bind]
  dsimp only
  have hbt' : ConLeche.inferTypeCore mode env G (d + 1)
      (bodyx.instantiate1 (.fvar d tyx)) = .ok bt := by
    rw [← ConLeche.instList_single bodyx (Expr.fvar d tyx)]
    exact ConLeche.inferTypeCore_mono hle3 hbt
  rw [hbt', ConLeche.okB_bind]
  unfold ConLeche.inferPisWrap at hwrap
  obtain ⟨w, hw, hwrap⟩ := ConLeche.bind_okB hwrap
  rw [ConLeche.ensureSort_def] at hw
  have hw' : ConLeche.ensureSortCore mode env G (d + 1) bt = .ok w :=
    ConLeche.ensureSortCore_mono hle3 hw
  rw [hw', ConLeche.okB_bind]
  unfold ConLeche.inferPisWrap at hwrap
  exact hwrap

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:790 inferPisC_tail_sim
— **THE `.forallE` CLAUSE CARRIES**. -/
theorem inferForall_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty body : EIdx)
    (tyx bodyx : Expr) (hok : CheckOK mode env fe s₀)
    (hty : denoteE s₀.store ty = some tyx)
    (hbody : denoteE s₀.store body = some bodyx)
    (hw : Expr.WScoped d (.forallE tyx bodyx)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.inferForall (coreKnot mode fe id fuel) fe d ty body
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d (.forallE tyx bodyx)
          s'.store r; ⊤⦄ := by
  have hwty : Expr.WScoped d tyx := by unfold Expr.WScoped at hw; exact hw.1
  have hwbody : Expr.WScoped d bodyx := by unfold Expr.WScoped at hw; exact hw.2
  unfold ConRon.Arena.inferForall
  refine triple_seq (hsim.infer s₀ d ty tyx hok hty hwty) ?_
  rintro tty s1 ⟨hok1, hx1, hp1, ttyx, httyx, hwttyx, F1, hF1⟩
  refine triple_seq (hsim.whnf s1 d tty ttyx hok1 httyx hwttyx) ?_
  rintro w s2 ⟨hok2, hx2, hp2, wx, hwx, -, F2, hF2⟩
  split
  next hsort =>
    refine triple_seq (viewSort_spec s2 w) ?_
    rintro ou s2' ⟨hs2', hou⟩
    subst s2'
    cases ou with
    | none => exact triple_failDanglingE
    | some u =>
      dsimp only
      have hvw := view_of_viewSort_tag hsort hou.symm
      obtain ⟨ux, rfl, hux⟩ := denote_sort_inv hok2.state.wf hvw hwx
      have hx02 := hx1.trans hx2
      have hty2 := denote_ext hty hx02
      refine triple_seq (internFVarE_spec s2 d ty hok2.state.wf
        (by rw [hty2]; rfl)) ?_
      rintro fv s3 ⟨hwf3, hx3, -, -, -, hc3, hp3, -, hd3⟩
      have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
      have hfv : denoteE s3.store fv = some (.fvar d tyx) := by
        rw [hd3]; simp [denoteEView, denote_ext hty2 hx3]
      have hx03 := hx02.trans hx3
      have hvec : ExprOps.InstLVec s3.store #[fv] [Expr.fvar d tyx] :=
        InstLVec.push (InstLVec.empty _) hfv
      have hstk : StkRel (PiR s3.store) (#[u] : Array _).toList.reverse
          [ux] :=
        StkRel.push (stk := #[]) (stkx := []) trivial (denoteL_ext hux hx3)
      have hwopen : Expr.WScoped (d + 1)
          (bodyx.instantiateList [Expr.fvar d tyx]) := by
        rw [ConLeche.instList_single]
        exact Expr.WScoped.instantiate1 hwty 0 hwbody
      refine triple_mono (inferPis_carry hsim d peelFuel s3 body 1 #[fv]
        #[u] bodyx [Expr.fvar d tyx] [ux] hok3
        (denote_ext hbody hx03) hvec hstk hwopen) ?_
      rintro r s' ⟨hok', hx', hp', v, hv, F3, hF3⟩
      obtain ⟨F, hF⟩ := inferTypeCore_forallE_of_loop hF1 hF2 hF3
      exact ⟨hok', hx03.trans hx', hp'.trans (hp3.trans (hp2.trans hp1)), v, hv,
        ConLeche.inferTypeCore_WScoped henv F hF hw, F, hF⟩
  next => exact triple_fail

/-! ## 4. The axiom census -/

#print axioms inferLamsOut_carry
#print axioms inferLamsLeaf_carry
#print axioms inferLams_carry
#print axioms inferTypeCore_lam_of_loop
#print axioms inferLam_spec
#print axioms inferPisOut_carry
#print axioms inferPisLeaf_carry
#print axioms inferPis_carry
#print axioms inferTypeCore_forallE_of_loop
#print axioms inferForall_spec

end ConRon.Bridge.Core
