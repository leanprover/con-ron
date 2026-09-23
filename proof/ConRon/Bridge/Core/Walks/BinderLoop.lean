/-
# `ConRon.Bridge.Core.Walks.BinderLoop` — the four binder-telescope loops

Task #97-P3-Core round 6, lane `binders`.  The twin's `inferBody` and
`annotateBody` binder clauses are con-leche's CACHED-tier telescope loops
(`Arena/Core.lean`'s `inferLams`/`inferPis`/`annotatePis`/`annotateLams`,
task #97-P6-11/12), not the pure tier's per-binder chain.  con-leche proves
the loops sound against the chain in two layers, and this module is the
bridge's copy of the upper one:

1. **the carry** (here): the twin's handle-level loop denotes con-leche's
   `Expr`-level PURE MIRROR (`ConLeche/Verify/BinderLoop.lean`'s
   `inferLams`, `inferPis`, `annotatePis`, `annotateLams`) — the analogue of
   con-leche's own `Verify/Cached/BinderLoopC.lean` `…C_sim`, one bind at a
   time;
2. **the identification** (con-leche's): `inferLams_sound`,
   `inferPis_sound`, `annotatePis_sound`, `annotateLams_sound` — a
   successful mirror run is reproduced by the chained body at some fuel.

The stacks are push-order `Array`s on the twin side and cons-order `List`s
on the mirror side (`BinderLoopC.lean`'s `toListRev_push`); the rebuild
phase reads `stk[n-1]` counting down, which is the mirror's head, so the
out-phase invariant is about `(stk.toList.take n).reverse`.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.ExprOps.Owed
import ConRon.Bridge.ExprOps.Walks
import ConRon.Bridge.Core.Walks.FvarB
import ConLeche.Verify.BinderLoop

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

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

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:94 RelILE — a λ (or
annotation) stack entry: the domain handle denotes the mirror's domain, the
binder meta is the mirror's. -/
def LamR (st : EStore) (e : EIdx × BinderMeta) (x : Expr × BinderMeta) : Prop :=
  denoteE st e.1 = some x.1 ∧ e.2 = x.2

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:351 RelLStk — a ∀
stack entry: the domain sort's level handle denotes the mirror's level. -/
def PiR (st : EStore) (e : LIdx × PropWhen) (x : Level × PropWhen) : Prop :=
  denoteL st.ls e.1 = some x.1 ∧ e.2 = x.2

theorem LamR.ext {st st' : EStore} (hx : Ext st st') :
    ∀ e x, LamR st e x → LamR st' e x :=
  fun _ _ h => ⟨denote_ext h.1 hx, h.2⟩

theorem PiR.ext {st st' : EStore} (hx : Ext st st') :
    ∀ e x, PiR st e x → PiR st' e x :=
  fun _ _ h => ⟨denoteL_ext h.1 hx, h.2⟩

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

/-- con-leche: ConLeche/Verify/BinderLoop.lean:67 inferLamsOut — one step of
the mirror's rebuild fold, at a passing chain check. -/
theorem mInferLamsOut_cons {d j : Nat} {tyo cur : Expr} {mb : BinderMeta}
    {prevPw : PropWhen} {rest : List (Expr × BinderMeta)}
    (hc : (mode.verifiedChecks && !(mb.pw == prevPw)) = false) :
    ConLeche.inferLamsOut (m := CheckM) mode d ((tyo, mb) :: rest) j cur prevPw
      = ConLeche.inferLamsOut (m := CheckM) mode d rest (j - 1)
          (.forallE (tyo.abstractRange d j) cur mb) mb.pw := by
  conv => lhs; unfold ConLeche.inferLamsOut
  simp only [hc, Bool.false_eq_true, if_false]

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:117 inferLamsOutC_sim
— **the λ loop's rebuild carries**: the twin's count-down over the pushed
stack denotes the mirror's fold over the consed one. -/
theorem inferLamsOut_carry (d : Nat) (stk : Array (EIdx × BinderMeta)) :
    ∀ (n : Nat) (s₀ : AState) (cur : EIdx) (curx : Expr) (prevPw : PropWhen)
      (stkx : List (Expr × BinderMeta)),
      CheckOK mode env fe s₀ → denoteE s₀.store cur = some curx →
      n ≤ stk.size → StkRel (LamR s₀.store) (stk.toList.take n).reverse stkx →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.inferLamsOut mode d stk n cur prevPw
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ConLeche.inferLamsOut (m := CheckM) mode d stkx (n - 1) curx prevPw
            = .ok v⌝⦄
  | 0, s₀, cur, curx, prevPw, stkx, hok, hcur, _, hstk => by
    cases stkx with
    | cons _ _ => exact hstk.elim
    | nil =>
      rw [ConRon.Arena.inferLamsOut]
      simp only [if_true]
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok, Ext.refl _, rfl, curx, hcur, rfl⟩
  | j + 1, s₀, cur, curx, prevPw, stkx, hok, hcur, hle, hstk => by
    obtain ⟨⟨tyox, mbx⟩, rest, rfl, ⟨hty, hmb⟩, hrest⟩ :=
      StkRel.take_succ (Nat.lt_of_succ_le hle) hstk
    rw [ConRon.Arena.inferLamsOut]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    dsimp only at hmb
    split
    next => exact triple_fail
    next hc =>
      have hc' : (mode.verifiedChecks && !(mbx.pw == prevPw)) = false := by
        rw [← hmb]; simpa using hc
      rw [mInferLamsOut_cons hc']
      refine triple_seq (ExprOps.abstractRangeFast_spec fvarBSpec
        coreWalkFuel s₀ stk[j]!.1 d j 0 hok.state (by rw [hty]; rfl)) ?_
      rintro tyAbs s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
      have hok1 := hok.mono hs1 hx1 hc1 hp1
      have hta : denoteE s1.store tyAbs = some (tyox.abstractRange d j) :=
        hrel1 _ hty
      refine triple_seq (internForallEE_spec s1 tyAbs cur stk[j]!.2 hs1.wf
        (by rw [hta]; rfl) (by rw [denote_ext hcur hx1]; rfl)) ?_
      rintro nd s2 ⟨hwf2, hx2, -, -, -, -, hc2, hp2, -, hd2⟩
      have hok2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
      have hnd : denoteE s2.store nd =
          some (.forallE (tyox.abstractRange d j) curx mbx) := by
        rw [hd2]
        simp [denoteEView, denote_ext hta hx2, denote_ext hcur (hx1.trans hx2),
          hmb]
      have hx02 : Ext s₀.store s2.store := hx1.trans hx2
      refine triple_mono (inferLamsOut_carry d stk j s2 nd _ stk[j]!.2.pw rest hok2 hnd
        (Nat.le_of_succ_le hle)
        (StkRel.imp (LamR.ext hx02) hrest)) ?_
      rintro r s' ⟨hok', hx', hp', v, hv, hrun⟩
      refine ⟨hok', hx02.trans hx', hp'.trans (hp2.trans hp1), v, hv, ?_⟩
      rw [hmb] at hrun
      exact hrun

/-! ### 2.2 Shape facts the loops read off a handle -/

/-- con-leche: none — a handle whose tag is not `lam` denotes no λ. -/
theorem denote_not_lam_of_tag {st : EStore} (hwf : StoreWF st) {t : EIdx}
    {tx : Expr} (hd : denoteE st t = some tx) (hne : t.tag ≠ ETag.lam) :
    ∀ p q m, tx ≠ .lam p q m := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  exact denote_not_lam hwf hv hd
    (fun ty b m h => hne (by rw [EStore.tagOf_of_view hv, h]; rfl))

/-- con-leche: none — a handle whose tag is not `forallE` denotes no ∀. -/
theorem denote_not_forallE_of_tag {st : EStore} (hwf : StoreWF st) {t : EIdx}
    {tx : Expr} (hd : denoteE st t = some tx) (hne : t.tag ≠ ETag.forallE) :
    ∀ p q m, tx ≠ .forallE p q m := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  exact denote_not_forallE hwf hv hd
    (fun ty b m h => hne (by rw [EStore.tagOf_of_view hv, h]; rfl))

/-- con-leche: none — `viewBind` at a λ-tagged handle is its `view`. -/
theorem view_lam_of_viewBind {st : EStore} {t ty b : EIdx} {mb : BinderMeta}
    (htg : t.tag = ETag.lam) (h : st.viewBind t = some (ty, b, mb)) :
    st.view t = some (.lam ty b mb) := by
  unfold EStore.viewBind at h
  cases h1 : st.viewBindI t with
  | none => rw [h1] at h; cases h
  | some p =>
    obtain ⟨ty', b', mi⟩ := p
    rw [h1] at h
    dsimp only at h
    cases h2 : st.viewBM mi with
    | none => rw [h2] at h; cases h
    | some m =>
      rw [h2] at h
      cases h
      exact view_of_viewBindI_lam htg h1 h2

/-- con-leche: none — `viewBind` at a ∀-tagged handle is its `view`. -/
theorem view_forallE_of_viewBind {st : EStore} {t ty b : EIdx}
    {mb : BinderMeta} (htg : t.tag = ETag.forallE)
    (h : st.viewBind t = some (ty, b, mb)) :
    st.view t = some (.forallE ty b mb) := by
  unfold EStore.viewBind at h
  cases h1 : st.viewBindI t with
  | none => rw [h1] at h; cases h
  | some p =>
    obtain ⟨ty', b', mi⟩ := p
    rw [h1] at h
    dsimp only at h
    cases h2 : st.viewBM mi with
    | none => rw [h2] at h; cases h
    | some m =>
      rw [h2] at h
      cases h
      exact view_of_viewBindI_forallE htg h1 h2

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

/-- con-leche: ConLeche/Kernel/Core.lean:1101-1107 ensureSort — **the twin's
`ensureSort` at the knot record**: one `whnf` slot call and a sort view. -/
theorem ensureSortK_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.ensureSort (coreKnot mode fe id fuel) fe d i
    ⦃⇓? u s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ l, denoteL s'.store.ls u = some l ∧
        ∃ F, ConLeche.whnf mode env F d e = .ok (.sort l)⌝⦄ := by
  unfold ConRon.Arena.ensureSort
  refine triple_seq (hsim.whnf s₀ d i e hok hden hw) ?_
  rintro w s1 ⟨hok1, hx1, hp1, wx, hwx, -, F, hF⟩
  obtain ⟨v, hv⟩ := denoteE_view hwx
  refine view_bind_triple hv ?_
  cases v
  case sort u =>
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv hok1.state.wf hv hwx
    dsimp only
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok1, hx1, hp1, l, hl, F, hF⟩
  all_goals (dsimp only; exact triple_fail)

/-- con-leche: none — the stack head, when there is one. -/
theorem StkRel.last {α β : Type} {R : α → β → Prop} {stk : Array α}
    [Inhabited α] {stkx : List β} (h : StkRel R stk.toList.reverse stkx)
    (hn : stk.size ≠ 0) :
    ∃ b rest, stkx = b :: rest ∧ R stk[stk.size - 1]! b := by
  obtain ⟨b, rest, h1, h2, -⟩ := StkRel.take_succ (stk := stk) (j := stk.size - 1)
    (by omega) (by rw [show stk.size - 1 + 1 = stk.size by omega]
                   exact StkRel.take_size h)
  exact ⟨b, rest, h1, h2⟩

/-- con-leche: none — an empty twin stack is an empty mirror stack. -/
theorem StkRel.nil_of_size {α β : Type} {R : α → β → Prop} {stk : Array α}
    {stkx : List β} (h : StkRel R stk.toList.reverse stkx)
    (hn : stk.size = 0) : stkx = [] := by
  have := StkRel.length h
  simp only [List.length_reverse, Array.length_toList, hn] at this
  exact List.eq_nil_of_length_eq_zero this.symm

/-! ### 2.3 The λ leaf's codomain check -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:108-122 inferLamsLeaf — the
leaf's codomain-sort check (task #152), as FACTS at a fuel: at the verified
modes the io-grade type of the leaf's type reduces to a sort whose zero-ness
is the innermost binder's datum. -/
def LamLeafOK (mode : CheckMode) (env : Env) (d k : Nat) (btx : Expr)
    (stkx : List (Expr × BinderMeta)) (F : Nat) : Prop :=
  mode.verifiedChecks = true → ∃ btt vb,
    ConLeche.inferTypeIO mode env F (d + k) btx = .ok btt ∧
    ConLeche.whnf mode env F (d + k) btt = .ok (.sort vb) ∧
    ∀ x mb0 rest, stkx = (x, mb0) :: rest → (Level.zeronessOf vb == mb0.pw) = true

theorem LamLeafOK.mono {d k : Nat} {btx : Expr}
    {stkx : List (Expr × BinderMeta)} {F F' : Nat} (hle : F ≤ F')
    (h : LamLeafOK mode env d k btx stkx F) : LamLeafOK mode env d k btx stkx F' := by
  intro hv
  obtain ⟨btt, vb, h1, h2, h3⟩ := h hv
  exact ⟨btt, vb, ConLeche.inferTypeIO_mono hle h1, ConLeche.whnf_mono hle h2, h3⟩

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:168 inferLamsLeafC_sim
(its check half) — **the twin's `inferLamsLeafCheck`** establishes
`LamLeafOK`. -/
theorem inferLamsLeafCheck_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d k : Nat) (stk : Array (EIdx × BinderMeta))
    (stkx : List (Expr × BinderMeta)) (bt : EIdx) (btx : Expr)
    (hok : CheckOK mode env fe s₀) (hbt : denoteE s₀.store bt = some btx)
    (hwbt : Expr.WScoped (d + k) btx)
    (hstk : StkRel (LamR s₀.store) stk.toList.reverse stkx) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.inferLamsLeafCheck mode (coreKnot mode fe id fuel) fe d k
        stk bt
    ⦃⇓? _u s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ F, LamLeafOK mode env d k btx stkx F⌝⦄ := by
  unfold ConRon.Arena.inferLamsLeafCheck
  split
  next hnv =>
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok, Ext.refl _, rfl, 0, fun hv => ?_⟩
    simp [hv] at hnv
  next hv0 =>
    have hv : mode.verifiedChecks = true := by simpa using hv0
    refine triple_seq (hsim.inferIO s₀ (d + k) bt btx hok hbt hwbt) ?_
    rintro btt s1 ⟨hok1, hx1, hp1, bttx, hbttx, hwbttx, F1, hF1⟩
    refine triple_seq (ensureSortK_spec hsim s1 (d + k) btt bttx hok1 hbttx
      hwbttx) ?_
    rintro vb s2 ⟨hok2, hx2, hp2, l, hl, F2, hF2⟩
    have hx02 := hx1.trans hx2
    have hp02 := hp2.trans hp1
    have hA : ConLeche.inferTypeIO mode env (max F1 F2) (d + k) btx = .ok bttx :=
      ConLeche.inferTypeIO_mono (Nat.le_max_left _ _) hF1
    have hB : ConLeche.whnf mode env (max F1 F2) (d + k) bttx = .ok (.sort l) :=
      ConLeche.whnf_mono (Nat.le_max_right _ _) hF2
    dsimp only
    split
    next hn =>
      mvcgen
      bridge_peel; subst_vars
      have hnil := StkRel.nil_of_size hstk hn
      refine ⟨hok2, hx02, hp02, max F1 F2, fun _ => ⟨bttx, l, hA, hB, ?_⟩⟩
      intro x mb0 rest h; rw [hnil] at h; cases h
    next hn =>
      obtain ⟨⟨x0, mb0⟩, rest0, hcons, _, hmb⟩ := StkRel.last hstk hn
      subst hcons
      refine triple_seq (readLevelM_spec s2 vb hok2.caches.readL) ?_
      rintro lvb s3 ⟨hst3, hm3, hp3, hc3, hl3, hL3⟩
      have hok3 := CheckOK.ofReadbackFrame hok2
        (ReadbackFrame.ofReadL hst3 hm3 hp3 hc3 hL3)
      rw [hl] at hl3
      obtain rfl : lvb = l := (Option.some.inj hl3).symm
      split
      next hz =>
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok3, by rw [hst3]; exact hx02, hp3.trans hp02, max F1 F2,
          fun _ => ⟨bttx, lvb, hA, hB, ?_⟩⟩
        intro x mb1 rest h
        cases h
        exact hz
      next => exact triple_fail

/-! ### 2.4 The λ leaf -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:123-129 inferLamsLeaf — the
datum the rebuild starts from: the residual's own λ datum, else the
innermost peeled binder's, else `never`. -/
def mPrev (o : Option PropWhen) (stkx : List (Expr × BinderMeta)) : PropWhen :=
  match o with
  | some p => p
  | none =>
    match stkx with
    | (_, mb0) :: _ => mb0.pw
    | [] => .never

/-- con-leche: ConLeche/Verify/BinderLoop.lean:108-129 inferLamsLeaf — the
mirror's leaf, from its three facts. -/
theorem mInferLamsLeaf {F d k : Nat} {tx bt v : Expr} {ws : List Expr}
    {stkx : List (Expr × BinderMeta)}
    (hb : ConLeche.inferTypeCore mode env F (d + k) (tx.instantiateList ws)
      = .ok bt)
    (hchk : tx.lamPw = none → LamLeafOK mode env d k bt stkx F)
    (hout : ConLeche.inferLamsOut (m := CheckM) mode d stkx (k - 1)
      (bt.abstractRange d k) (mPrev tx.lamPw stkx) = .ok v) :
    ConLeche.inferLamsLeaf mode (ConLeche.pureFns mode env F) d tx k ws stkx
      = .ok v := by
  unfold ConLeche.inferLamsLeaf
  rw [infer_def, hb, ConLeche.okB_bind]
  cases tx
  case lam =>
    simpa [mPrev, Expr.lamPw] using hout
  all_goals
    by_cases hv : mode.verifiedChecks = true
    · obtain ⟨btt, vb, h1, h2, h3⟩ := hchk rfl hv
      dsimp only
      rw [if_pos hv, inferTypeIO_def, h1, ConLeche.okB_bind, whnf_def, h2,
        ConLeche.okB_bind]
      dsimp only
      cases stkx with
      | nil => exact hout
      | cons e rest =>
        obtain ⟨x, mb0⟩ := e
        dsimp only
        rw [if_pos (h3 _ _ _ rfl)]
        exact hout
    · dsimp only
      rw [if_neg hv]
      exact hout

/-- con-leche: none — the twin's rebuild datum is the mirror's. -/
theorem prevPw_none {stk : Array (EIdx × BinderMeta)} {st : EStore}
    {stkx : List (Expr × BinderMeta)}
    (hstk : StkRel (LamR st) stk.toList.reverse stkx) :
    (if stk.size = 0 then PropWhen.never else stk[stk.size - 1]!.2.pw)
      = mPrev none stkx := by
  split
  next hn => rw [StkRel.nil_of_size hstk hn]; rfl
  next hn =>
    obtain ⟨⟨x0, mb0⟩, rest0, rfl, _, hmb⟩ := StkRel.last hstk hn
    simp only [mPrev]
    rw [hmb]

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:168 inferLamsLeafC_sim
— **the λ loop's leaf carries**: bulk open, infer, the codomain check at a
datum-free residual, the leaf's `abstractRange`, and the rebuild. -/
theorem inferLamsLeaf_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (t : EIdx) (k : Nat) (fvs : Array EIdx)
    (stk : Array (EIdx × BinderMeta)) (tx : Expr) (ws : List Expr)
    (stkx : List (Expr × BinderMeta))
    (hok : CheckOK mode env fe s₀) (ht : denoteE s₀.store t = some tx)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hstk : StkRel (LamR s₀.store) stk.toList.reverse stkx)
    (hk : stk.size = k)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.inferLamsLeaf mode (coreKnot mode fe id fuel) fe d t k fvs stk
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
        ∃ F, ConLeche.inferLamsLeaf mode (ConLeche.pureFns mode env F) d tx k
          ws stkx = .ok v⌝⦄ := by
  unfold ConRon.Arena.inferLamsLeaf
  -- stage 1: the residual, opened in bulk
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ t fvs 0 ws
    hok.state hvec (by rw [ht]; rfl)) ?_
  rintro ob s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
  have hok1 := hok.mono hs1 hx1 hc1 hp1
  have hob : denoteE s1.store ob = some (tx.instantiateList ws) := hrel1 _ ht
  -- stage 2: its type
  refine triple_seq (hsim.infer s1 (d + k) ob _ hok1 hob hw) ?_
  rintro bt s2 ⟨hok2, hx2, hp2, btx, hbtx, hwbtx, F1, hF1⟩
  have hx02 := hx1.trans hx2
  have ht2 := denote_ext ht hx02
  -- stage 3: the residual's own datum
  refine triple_seq (ExprOps.lamPw_spec s2 t hok2.state (by rw [ht2]; rfl)) ?_
  rintro lpw s3' ⟨hs3', hlpw⟩
  subst s3'
  have hlpw' : lpw = tx.lamPw := hlpw tx ht2
  have hstk2 := StkRel.imp (LamR.ext hx02) hstk
  -- the rest, from a state and the leaf-check facts
  have hrest : ∀ (s3 : AState) (F2 : Nat), CheckOK mode env fe s3 →
      Ext s2.store s3.store → s3.pins = s2.pins →
      (tx.lamPw = none → LamLeafOK mode env d k btx stkx F2) →
      ∀ (prevPw : PropWhen), prevPw = mPrev tx.lamPw stkx →
      ⦃fun s => ⌜s = s3⌝⦄ (do
        let cur ← abstractRangeFast coreWalkFuel bt d k 0
        ConRon.Arena.inferLamsOut mode d stk stk.size cur prevPw)
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ∃ F, ConLeche.inferLamsLeaf mode (ConLeche.pureFns mode env F) d tx
            k ws stkx = .ok v⌝⦄ := by
    intro s3 F2 hok3 hx3 hp3 hchk prevPw hprev
    have hbt3 := denote_ext hbtx hx3
    refine triple_seq (ExprOps.abstractRangeFast_spec fvarBSpec coreWalkFuel s3 bt
      d k 0 hok3.state (by rw [hbt3]; rfl)) ?_
    rintro cur s4 ⟨hs4, hx4, -, hc4, hp4, -, hrel4⟩
    have hok4 := hok3.mono hs4 hx4 hc4 hp4
    have hcur : denoteE s4.store cur = some (btx.abstractRange d k) :=
      hrel4 _ hbt3
    have hx24 := hx3.trans hx4
    refine triple_mono (inferLamsOut_carry d stk stk.size s4 cur _ prevPw stkx
      hok4 hcur (Nat.le_refl _)
      (StkRel.take_size (StkRel.imp (LamR.ext hx24) hstk2))) ?_
    rintro r s' ⟨hok', hx', hp', v, hv, hrun⟩
    refine ⟨hok', hx02.trans (hx24.trans hx'), hp'.trans (hp4.trans (hp3.trans
      (hp2.trans hp1))), v, hv, max F1 F2, ?_⟩
    rw [hk, hprev] at hrun
    exact mInferLamsLeaf (ConLeche.inferTypeCore_mono (Nat.le_max_left _ _) hF1)
      (fun hn => (hchk hn).mono (Nat.le_max_right _ _)) hrun
  cases lpw with
  | some p =>
    dsimp only
    rw [pure_bind]
    exact hrest s2 0 hok2 (Ext.refl _) rfl
      (fun hn => by rw [← hlpw'] at hn; cases hn) p (by rw [← hlpw']; rfl)
  | none =>
    dsimp only
    refine triple_seq (inferLamsLeafCheck_carry hsim s2 d k stk stkx bt btx hok2
      hbtx hwbtx hstk2) ?_
    rintro _ s3 ⟨hok3, hx3, hp3, F2, hchk⟩
    exact hrest s3 F2 hok3 hx3 hp3 (fun _ => hchk) _
      (by rw [← hlpw', prevPw_none hstk2])

/-! ### 2.5 The peel -/

/-- con-leche: none — the mirror is fuel-monotone (it is a `FueledM` run,
`inferLams_atF`). -/
theorem mInferLams_mono {d peel k : Nat} {t v : Expr} {ws : List Expr}
    {stkx : List (Expr × BinderMeta)} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.inferLams mode (ConLeche.pureFns mode env F) d peel t k ws stkx
      = .ok v) :
    ConLeche.inferLams mode (ConLeche.pureFns mode env F') d peel t k ws stkx
      = .ok v := by
  rw [← ConLeche.inferLams_atF] at h ⊢
  exact (ConLeche.inferLams mode (ConLeche.fueledFns mode env) d peel t k ws
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
      (stk : Array (EIdx × BinderMeta)) (tx : Expr) (ws : List Expr)
      (stkx : List (Expr × BinderMeta)),
      CheckOK mode env fe s₀ → denoteE s₀.store t = some tx →
      ExprOps.InstLVec s₀.store fvs ws →
      StkRel (LamR s₀.store) stk.toList.reverse stkx → stk.size = k →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.inferLams mode (coreKnot mode fe id fuel) fe d peel t k
          fvs stk
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ∃ F, ConLeche.inferLams mode (ConLeche.pureFns mode env F) d peel tx
            k ws stkx = .ok v⌝⦄
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
        obtain ⟨ty, body, mb⟩ := p
        dsimp only
        have hv := view_lam_of_viewBind htl hob.symm
        obtain ⟨tyx, bodyx, rfl, hty, hbody⟩ := denote_lam_inv hwf hv ht
        have hlamL : (Expr.lam tyx bodyx mb).instantiateList ws
            = .lam (tyx.instantiateList ws) (bodyx.instantiateList ws 1) mb := by
          simp [Expr.instantiateList]
        have hwc : Expr.WScoped (d + k) (tyx.instantiateList ws) ∧
            Expr.WScoped (d + k) (bodyx.instantiateList ws 1) := by
          rw [hlamL] at hw; simpa only [Expr.WScoped] using hw
        -- stage 1: the domain, opened in bulk
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty fvs
          0 ws hok.state hvec (by rw [hty]; rfl)) ?_
        rintro tyo s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
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
          rintro fv s4 ⟨hwf4, hx4, -, -, -, -, hc4, hp4, -, hd4⟩
          have hok4 := hok3.mono ⟨hwf4⟩ hx4 hc4 hp4
          have hfv : denoteE s4.store fv =
              some (.fvar (d + k) (tyx.instantiateList ws)) := by
            rw [hd4]; simp [denoteEView, denote_ext htyo3 hx4]
          have hx04 := hx03.trans hx4
          -- stage 5: the rest of the chain
          refine triple_mono (inferLams_carry hsim d peel s4 body (k + 1)
            (fvs.push fv) (stk.push (tyo, mb)) bodyx
            (Expr.fvar (d + k) (tyx.instantiateList ws) :: ws)
            ((tyx.instantiateList ws, mb) :: stkx) hok4
            (denote_ext hbody hx04)
            (InstLVec.push (hvec.ext hx04) hfv)
            (StkRel.push (StkRel.imp (LamR.ext hx04) hstk)
              ⟨denote_ext htyo (hx2.trans (hx3.trans hx4)), rfl⟩)
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

/-! ### 2.6 The `.lam` clause -/

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:595 inferLamsC_tail_sim
(its `himp` half) — **the pure side of the `.lam` clause**: a mirror run of
the loop at the one-binder start is the chained `inferBody` λ clause at a
larger fuel, by con-leche's `inferLams_sound`. -/
theorem inferTypeCore_lam_of_loop {d F1 F2 F3 : Nat} {tyx bodyx ttyx : Expr}
    {u : Level} {mb : BinderMeta} {v : Expr} {peel : Nat}
    (hF1 : ConLeche.inferTypeCore mode env F1 d tyx = .ok ttyx)
    (hF2 : ConLeche.whnf mode env F2 d ttyx = .ok (.sort u))
    (hF3 : ConLeche.inferLams mode (ConLeche.pureFns mode env F3) d peel bodyx 1
      [Expr.fvar d tyx] [(tyx, mb)] = .ok v) :
    ∃ F, ConLeche.inferTypeCore mode env F d (.lam tyx bodyx mb) = .ok v := by
  obtain ⟨F', hchain⟩ := ConLeche.inferLams_sound (env := env) peel bodyx 1
    [Expr.fvar d tyx] [(tyx, mb)] F3 v rfl
    (by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact ⟨_, _, rfl⟩) hF3
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
  unfold ConLeche.inferLamsTail at htail
  revert htail
  cases hbp : bodyx.lamPw with
  | some pwI =>
    intro htail
    have hbl : bodyx.isLam = true := by
      cases bodyx <;> first | rfl | exact nomatch hbp
    simp only [hbl, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte] at htail
    unfold ConLeche.inferLamsWrap at htail
    dsimp only
    by_cases hg : (mode.verifiedChecks && !(mb.pw == pwI)) = true
    · rw [if_pos hg] at htail
      exact nomatch htail
    rw [if_neg hg] at htail
    by_cases hv : mode.verifiedChecks = true
    · rw [if_pos hv]
      have hpw : (mb.pw == pwI) = true := by
        by_cases hc : (mb.pw == pwI) = true
        · exact hc
        · exact absurd (by simp [hv, hc]) hg
      rw [if_pos hpw]
      exact htail
    · rw [if_neg hv]
      exact htail
  | none =>
    intro htail
    have hbl : bodyx.isLam = false := by
      cases bodyx <;> first | rfl | exact nomatch hbp
    simp only [hbl, Bool.not_false, Bool.and_true] at htail
    dsimp only
    by_cases hv : mode.verifiedChecks = true
    case neg =>
      rw [if_neg hv] at htail ⊢
      unfold ConLeche.inferLamsWrap at htail
      rw [if_neg (by simp [hv])] at htail
      exact htail
    rw [if_pos hv] at htail ⊢
    rw [ConLeche.inferTypeIO_def] at htail
    obtain ⟨btt, hbtt, htail⟩ := ConLeche.bind_okB htail
    rw [ConLeche.inferTypeIO_mono hle3 hbtt, ConLeche.okB_bind]
    rw [ConLeche.ensureSort_def] at htail
    obtain ⟨w, hww, htail⟩ := ConLeche.bind_okB htail
    rw [ConLeche.ensureSortCore_mono hle3 hww, ConLeche.okB_bind]
    try dsimp only at htail ⊢
    by_cases hz : (Level.zeronessOf w == mb.pw) = true
    case neg =>
      rw [if_neg hz] at htail
      exact nomatch htail
    rw [if_pos hz] at htail
    rw [if_pos hz]
    unfold ConLeche.inferLamsWrap at htail
    rw [if_neg (by simp)] at htail
    exact htail

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:595 inferLamsC_tail_sim
— **THE `.lam` CLAUSE CARRIES**: the twin's `inferLam` (domain type, its
sort, the first free variable, then `inferLams` from `k = 1`) against
con-leche's chained `inferBody` λ clause. -/
theorem inferLam_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty body : EIdx) (mb : BinderMeta)
    (tyx bodyx : Expr) (hok : CheckOK mode env fe s₀)
    (hty : denoteE s₀.store ty = some tyx)
    (hbody : denoteE s₀.store body = some bodyx)
    (hw : Expr.WScoped d (.lam tyx bodyx mb)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.inferLam mode (coreKnot mode fe id fuel) fe d ty body mb
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d (.lam tyx bodyx mb)
          s'.store r⌝⦄ := by
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
    rintro fv s3 ⟨hwf3, hx3, -, -, -, -, hc3, hp3, -, hd3⟩
    have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
    have hfv : denoteE s3.store fv = some (.fvar d tyx) := by
      rw [hd3]; simp [denoteEView, denote_ext hty2 hx3]
    have hx03 := hx02.trans hx3
    have hvec : ExprOps.InstLVec s3.store #[fv] [Expr.fvar d tyx] :=
      InstLVec.push (InstLVec.empty _) hfv
    have hstk : StkRel (LamR s3.store) (#[(ty, mb)] : Array _).toList.reverse
        [(tyx, mb)] :=
      StkRel.push (stk := #[]) (stkx := []) trivial ⟨denote_ext hty hx03, rfl⟩
    have hwopen : Expr.WScoped (d + 1)
        (bodyx.instantiateList [Expr.fvar d tyx]) := by
      rw [ConLeche.instList_single]
      exact Expr.WScoped.instantiate1 hwty 0 hwbody
    refine triple_mono (inferLams_carry hsim d peelFuel s3 body 1 #[fv]
      #[(ty, mb)] bodyx [Expr.fvar d tyx] [(tyx, mb)] hok3
      (denote_ext hbody hx03) hvec hstk rfl hwopen) ?_
    rintro r s' ⟨hok', hx', hp', v, hv, F3, hF3⟩
    obtain ⟨F, hF⟩ := inferTypeCore_lam_of_loop hF1 hF2 hF3
    exact ⟨hok', hx03.trans hx', hp'.trans (hp3.trans (hp2.trans hp1)), v, hv,
      ConLeche.inferTypeCore_WScoped henv F hF hw, F, hF⟩
  next => exact triple_fail

end ConRon.Bridge.Core
