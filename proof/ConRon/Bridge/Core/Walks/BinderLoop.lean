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
  refine tag_view_bind_triple hv ?_
    (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
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
          refine triple_seq (viewSort_spec s3 w) ?_
          rintro ou s3' ⟨hs3', hou⟩
          subst s3'
          cases ou with
          | none => exact triple_failDanglingE
          | some u =>
            dsimp only
            have hvw := view_of_viewSort_tag hsort hou.symm
            obtain ⟨l, rfl, -⟩ := denote_sort_inv hok3.state.wf hvw hwx
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

/-! ## 3. The ∀-inference loop

### 3.1 The outward `imax` fold, with the threaded datum -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:151 inferPisOut — one step of
the mirror's fold, at a passing datum check. -/
theorem mInferPisOut_cons {u vx : Level} {pw : PropWhen}
    {rest : List (Level × PropWhen)}
    (hc : (mode.verifiedChecks && !(Level.zeronessOf vx == pw)) = false) :
    ConLeche.inferPisOut (m := CheckM) mode ((u, pw) :: rest) vx
      = ConLeche.inferPisOut (m := CheckM) mode rest (.imax u vx) := by
  conv => lhs; unfold ConLeche.inferPisOut
  simp only [hc, Bool.false_eq_true, if_false]

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:359 inferPisOutC_sim
— **the ∀ loop's fold carries**, and the THREADED datum is sound: the twin
checks every binder against the leaf sort's zero-ness `pv`, read once; the
mirror checks it against the zero-ness of the sort built so far, which is
the same datum because `Level.zeronessOf (.imax u v) = Level.zeronessOf v`
(con-leche's task #272, definitionally). -/
theorem inferPisOut_carry (stk : Array (LIdx × PropWhen)) (pv : PropWhen) :
    ∀ (n : Nat) (s₀ : AState) (v : LIdx) (vx : Level)
      (stkx : List (Level × PropWhen)),
      CheckOK mode env fe s₀ → denoteL s₀.store.ls v = some vx →
      Level.zeronessOf vx = pv →
      n ≤ stk.size → StkRel (PiR s₀.store) (stk.toList.take n).reverse stkx →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.inferPisOut mode stk n v pv
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ lx, denoteL s'.store.ls r = some lx ∧
          ConLeche.inferPisOut (m := CheckM) mode stkx vx = .ok lx⌝⦄
  | 0, s₀, v, vx, stkx, hok, hv, _, _, hstk => by
    cases stkx with
    | cons _ _ => exact hstk.elim
    | nil =>
      rw [ConRon.Arena.inferPisOut]
      simp only [if_true]
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok, Ext.refl _, rfl, vx, hv, rfl⟩
  | j + 1, s₀, v, vx, stkx, hok, hv, hz, hle, hstk => by
    obtain ⟨⟨ux, pwx⟩, rest, rfl, ⟨hu, hpw⟩, hrest⟩ :=
      StkRel.take_succ (Nat.lt_of_succ_le hle) hstk
    rw [ConRon.Arena.inferPisOut]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    dsimp only at hpw
    split
    next => exact triple_fail
    next hc =>
      have hc' : (mode.verifiedChecks && !(Level.zeronessOf vx == pwx)) = false := by
        rw [hz, ← hpw]; simpa using hc
      rw [mInferPisOut_cons hc']
      have hvo : s₀.store.ls.ViewOK (.imax stk[j]!.1 v) := by
        constructor
        · intro c hc
          simp only [LNodeView.lchildren, List.mem_cons,
            List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact lview_isSome_of_denote hu
          · exact lview_isSome_of_denote hv
        · intro c hc; simp [LNodeView.nchildren] at hc
      refine triple_seq (internLNode_spec s₀ (.imax stk[j]!.1 v) hok.state.wf hvo) ?_
      rintro v2 s1 ⟨hwf1, hx1, -, -, -, -, hc1, hp1, -, hd1⟩
      have hok1 := hok.mono ⟨hwf1⟩ hx1 hc1 hp1
      have hv2 : denoteL s1.store.ls v2 = some (.imax ux vx) := by
        rw [hd1]
        simp [denoteLView, opt2, denoteL_ext hu hx1, denoteL_ext hv hx1]
      refine triple_mono (inferPisOut_carry stk pv j s1 v2 _ rest hok1 hv2
        (by simpa [Level.zeronessOf] using hz) (Nat.le_of_succ_le hle)
        (StkRel.imp (PiR.ext hx1) hrest)) ?_
      rintro r s' ⟨hok', hx', hp', lx, hl, hrun⟩
      exact ⟨hok', hx1.trans hx', hp'.trans hp1, lx, hl, hrun⟩

/-! ### 3.2 The ∀ leaf -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:160-169 inferPisLeaf — the
mirror's leaf, from its three facts. -/
theorem mInferPisLeaf {F d k : Nat} {tx bt : Expr} {vx lx : Level}
    {ws : List Expr} {stkx : List (Level × PropWhen)}
    (hb : ConLeche.inferTypeCore mode env F (d + k) (tx.instantiateList ws)
      = .ok bt)
    (hw : ConLeche.whnf mode env F (d + k) bt = .ok (.sort vx))
    (hout : ConLeche.inferPisOut (m := CheckM) mode stkx vx = .ok lx) :
    ConLeche.inferPisLeaf mode (ConLeche.pureFns mode env F) d tx k ws stkx
      = .ok (.sort lx) := by
  unfold ConLeche.inferPisLeaf
  rw [infer_def, hb, ConLeche.okB_bind, whnf_def, hw, ConLeche.okB_bind]
  dsimp only
  rw [hout, ConLeche.okB_bind]
  rfl

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:405 inferPisLeafC_sim
— **the ∀ loop's leaf carries**: bulk open, infer, the sort (read back ONCE
for the threaded datum), the fold, the sort node. -/
theorem inferPisLeaf_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (t : EIdx) (k : Nat) (fvs : Array EIdx)
    (stk : Array (LIdx × PropWhen)) (tx : Expr) (ws : List Expr)
    (stkx : List (Level × PropWhen))
    (hok : CheckOK mode env fe s₀) (ht : denoteE s₀.store t = some tx)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hstk : StkRel (PiR s₀.store) stk.toList.reverse stkx)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.inferPisLeaf mode (coreKnot mode fe id fuel) fe d t k fvs stk
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
        ∃ F, ConLeche.inferPisLeaf mode (ConLeche.pureFns mode env F) d tx k
          ws stkx = .ok v⌝⦄ := by
  unfold ConRon.Arena.inferPisLeaf
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ t fvs 0 ws
    hok.state hvec (by rw [ht]; rfl)) ?_
  rintro ob s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
  have hok1 := hok.mono hs1 hx1 hc1 hp1
  have hob : denoteE s1.store ob = some (tx.instantiateList ws) := hrel1 _ ht
  refine triple_seq (hsim.infer s1 (d + k) ob _ hok1 hob hw) ?_
  rintro bt s2 ⟨hok2, hx2, hp2, btx, hbtx, hwbtx, F1, hF1⟩
  refine triple_seq (ensureSortK_spec hsim s2 (d + k) bt btx hok2 hbtx hwbtx) ?_
  rintro v s3 ⟨hok3, hx3, hp3, vx, hvx, F2, hF2⟩
  refine triple_seq (readLevelM_spec s3 v hok3.caches.readL) ?_
  rintro lv s4 ⟨hst4, hm4, hp4, hc4, hl4, hL4⟩
  have hok4 := CheckOK.ofReadbackFrame hok3
    (ReadbackFrame.ofReadL hst4 hm4 hp4 hc4 hL4)
  rw [hvx] at hl4
  obtain rfl : lv = vx := (Option.some.inj hl4).symm
  have hx34 : Ext s3.store s4.store := by rw [hst4]; exact Ext.refl _
  have hx04 := hx1.trans (hx2.trans (hx3.trans hx34))
  refine triple_seq (inferPisOut_carry stk (Level.zeronessOf lv) stk.size s4 v lv
    stkx hok4 (by rw [hst4]; exact hvx) rfl (Nat.le_refl _)
    (StkRel.take_size (StkRel.imp (PiR.ext hx04) hstk))) ?_
  rintro iv s5 ⟨hok5, hx5, hp5, lx, hlx, hrun⟩
  refine triple_mono (internSortE_spec s5 iv hok5.state.wf
    (lview_isSome_of_denote hlx)) ?_
  rintro r s6 ⟨hwf6, hx6, -, -, -, -, hc6, hp6, -, hd6⟩
  have hok6 := hok5.mono ⟨hwf6⟩ hx6 hc6 hp6
  refine ⟨hok6, hx04.trans (hx5.trans hx6),
    hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1)))),
    .sort lx, by rw [hd6]; simp [denoteEView, denoteL_ext hlx hx6],
    max F1 F2, ?_⟩
  exact mInferPisLeaf (ConLeche.inferTypeCore_mono (Nat.le_max_left _ _) hF1)
    (ConLeche.whnf_mono (Nat.le_max_right _ _) hF2) hrun

/-! ### 3.3 The ∀ peel -/

/-- con-leche: none — the ∀ mirror is fuel-monotone (`inferPis_atF`). -/
theorem mInferPis_mono {d peel k : Nat} {t v : Expr} {ws : List Expr}
    {stkx : List (Level × PropWhen)} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.inferPis mode (ConLeche.pureFns mode env F) d peel t k ws stkx
      = .ok v) :
    ConLeche.inferPis mode (ConLeche.pureFns mode env F') d peel t k ws stkx
      = .ok v := by
  rw [← ConLeche.inferPis_atF] at h ⊢
  exact (ConLeche.inferPis mode (ConLeche.fueledFns mode env) d peel t k ws
    stkx).property hle h

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:436 inferPisC_sim —
**THE ∀-TELESCOPE LOOP CARRIES**. -/
theorem inferPis_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) :
    ∀ (peel : Nat) (s₀ : AState) (t : EIdx) (k : Nat) (fvs : Array EIdx)
      (stk : Array (LIdx × PropWhen)) (tx : Expr) (ws : List Expr)
      (stkx : List (Level × PropWhen)),
      CheckOK mode env fe s₀ → denoteE s₀.store t = some tx →
      ExprOps.InstLVec s₀.store fvs ws →
      StkRel (PiR s₀.store) stk.toList.reverse stkx →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.inferPis mode (coreKnot mode fe id fuel) fe d peel t k
          fvs stk
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ∃ F, ConLeche.inferPis mode (ConLeche.pureFns mode env F) d peel tx
            k ws stkx = .ok v⌝⦄
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
        obtain ⟨ty, body, mb⟩ := p
        dsimp only
        have hv := view_forallE_of_viewBind htp hob.symm
        obtain ⟨tyx, bodyx, rfl, hty, hbody⟩ := denote_forallE_inv hwf hv ht
        have hpiL : (Expr.forallE tyx bodyx mb).instantiateList ws
            = .forallE (tyx.instantiateList ws) (bodyx.instantiateList ws 1)
              mb := by
          simp [Expr.instantiateList]
        have hwc : Expr.WScoped (d + k) (tyx.instantiateList ws) ∧
            Expr.WScoped (d + k) (bodyx.instantiateList ws 1) := by
          rw [hpiL] at hw; simpa only [Expr.WScoped] using hw
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty fvs
          0 ws hok.state hvec (by rw [hty]; rfl)) ?_
        rintro tyo s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
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
            rintro fv s4 ⟨hwf4, hx4, -, -, -, -, hc4, hp4, -, hd4⟩
            have hok4 := hok3.mono ⟨hwf4⟩ hx4 hc4 hp4
            have hfv : denoteE s4.store fv =
                some (.fvar (d + k) (tyx.instantiateList ws)) := by
              rw [hd4]; simp [denoteEView, denote_ext htyo3 hx4]
            have hx04 := hx03.trans hx4
            refine triple_mono (inferPis_carry hsim d peel s4 body (k + 1)
              (fvs.push fv) (stk.push (u, mb.pw)) bodyx
              (Expr.fvar (d + k) (tyx.instantiateList ws) :: ws)
              ((ux, mb.pw) :: stkx) hok4
              (denote_ext hbody hx04)
              (InstLVec.push (hvec.ext hx04) hfv)
              (StkRel.push (StkRel.imp (PiR.ext hx04) hstk)
                ⟨denoteL_ext hux hx4, rfl⟩)
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
    {ux : Level} {mb : BinderMeta} {v : Expr} {peel : Nat}
    (hF1 : ConLeche.inferTypeCore mode env F1 d tyx = .ok ttyx)
    (hF2 : ConLeche.whnf mode env F2 d ttyx = .ok (.sort ux))
    (hF3 : ConLeche.inferPis mode (ConLeche.pureFns mode env F3) d peel bodyx 1
      [Expr.fvar d tyx] [(ux, mb.pw)] = .ok v) :
    ∃ F, ConLeche.inferTypeCore mode env F d (.forallE tyx bodyx mb) = .ok v := by
  obtain ⟨F', hchain⟩ := ConLeche.inferPis_sound (env := env) peel bodyx 1
    [Expr.fvar d tyx] [(ux, mb.pw)] F3 v rfl (Nat.le_refl 1) hF3
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
  dsimp only at hwrap ⊢
  by_cases hver : mode.verifiedChecks = true
  case neg =>
    rw [if_neg hver] at hwrap ⊢
    unfold ConLeche.inferPisWrap at hwrap
    exact hwrap
  rw [if_pos hver] at hwrap ⊢
  by_cases hz : (Level.zeronessOf w == mb.pw) = true
  case neg =>
    rw [if_neg hz] at hwrap
    exact nomatch hwrap
  rw [if_pos hz] at hwrap ⊢
  unfold ConLeche.inferPisWrap at hwrap
  exact hwrap

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:790 inferPisC_tail_sim
— **THE `.forallE` CLAUSE CARRIES**. -/
theorem inferForall_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty body : EIdx) (mb : BinderMeta)
    (tyx bodyx : Expr) (hok : CheckOK mode env fe s₀)
    (hty : denoteE s₀.store ty = some tyx)
    (hbody : denoteE s₀.store body = some bodyx)
    (hw : Expr.WScoped d (.forallE tyx bodyx mb)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.inferForall mode (coreKnot mode fe id fuel) fe d ty body mb
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d (.forallE tyx bodyx mb)
          s'.store r⌝⦄ := by
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
      rintro fv s3 ⟨hwf3, hx3, -, -, -, -, hc3, hp3, -, hd3⟩
      have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
      have hfv : denoteE s3.store fv = some (.fvar d tyx) := by
        rw [hd3]; simp [denoteEView, denote_ext hty2 hx3]
      have hx03 := hx02.trans hx3
      have hvec : ExprOps.InstLVec s3.store #[fv] [Expr.fvar d tyx] :=
        InstLVec.push (InstLVec.empty _) hfv
      have hstk : StkRel (PiR s3.store) (#[(u, mb.pw)] : Array _).toList.reverse
          [(ux, mb.pw)] :=
        StkRel.push (stk := #[]) (stkx := []) trivial ⟨denoteL_ext hux hx3, rfl⟩
      have hwopen : Expr.WScoped (d + 1)
          (bodyx.instantiateList [Expr.fvar d tyx]) := by
        rw [ConLeche.instList_single]
        exact Expr.WScoped.instantiate1 hwty 0 hwbody
      refine triple_mono (inferPis_carry hsim d peelFuel s3 body 1 #[fv]
        #[(u, mb.pw)] bodyx [Expr.fvar d tyx] [(ux, mb.pw)] hok3
        (denote_ext hbody hx03) hvec hstk hwopen) ?_
      rintro r s' ⟨hok', hx', hp', v, hv, F3, hF3⟩
      obtain ⟨F, hF⟩ := inferTypeCore_forallE_of_loop hF1 hF2 hF3
      exact ⟨hok', hx03.trans hx', hp'.trans (hp3.trans (hp2.trans hp1)), v, hv,
        ConLeche.inferTypeCore_WScoped henv F hF hw, F, hF⟩
  next => exact triple_fail

/-! ## 4. The annotation loops

### 4.1 The shared outward rebuild -/

/-- con-leche: none — the node a rebuild interns, by the loop's kind. -/
def mkB (isLam : Bool) (ty b : Expr) (m : BinderMeta) : Expr :=
  if isLam then .lam ty b m else .forallE ty b m

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1018-1024 annotBinderMeta — the
twin's copy is the same function. -/
theorem annotBinderMeta_eq (pw? : Option PropWhen) (mb : BinderMeta) :
    ConRon.Arena.annotBinderMeta pw? mb = ConLeche.annotBinderMeta pw? mb := by
  cases pw? <;> rfl

/-- con-leche: none — `internLamE`/`internForallEE` by the loop's kind. -/
theorem internBinderE_spec (isLam : Bool) (s₀ : AState) (ty b : EIdx)
    (m : BinderMeta) (tx bx : Expr) (hwf : StoreWF s₀.store)
    (hty : denoteE s₀.store ty = some tx) (hb : denoteE s₀.store b = some bx) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (if isLam then internLamE ty b m else internForallEE ty b m)
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteE s'.store h = some (mkB isLam tx bx m)⌝⦄ := by
  cases isLam
  · simp only [Bool.false_eq_true, if_false]
    refine triple_mono (internForallEE_spec s₀ ty b m hwf (by rw [hty]; rfl)
      (by rw [hb]; rfl)) ?_
    rintro h s' ⟨h1, h2, -, -, -, -, h3, h4, -, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [h5]; simp [denoteEView, denote_ext hty h2, denote_ext hb h2, mkB]
  · simp only [if_true]
    refine triple_mono (internLamE_spec s₀ ty b m hwf (by rw [hty]; rfl)
      (by rw [hb]; rfl)) ?_
    rintro h s' ⟨h1, h2, -, -, -, -, h3, h4, -, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [h5]; simp [denoteEView, denote_ext hty h2, denote_ext hb h2, mkB]

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:890
annotateBindersOutC_sim — **the annotation loops' rebuild carries**, with
task #161's datum threading. -/
theorem annotateBindersOut_carry (isLam : Bool) (d : Nat)
    (stk : Array (EIdx × BinderMeta)) :
    ∀ (n : Nat) (s₀ : AState) (pw? : Option PropWhen) (cur : EIdx)
      (curx : Expr) (stkx : List (Expr × BinderMeta)),
      CheckOK mode env fe s₀ → denoteE s₀.store cur = some curx →
      n ≤ stk.size → StkRel (LamR s₀.store) (stk.toList.take n).reverse stkx →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.annotateBindersOut isLam d pw? stk n cur
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ConLeche.annotateBindersOut (m := CheckM) (mkB isLam) d pw? stkx
            (n - 1) curx = .ok v⌝⦄
  | 0, s₀, pw?, cur, curx, stkx, hok, hcur, _, hstk => by
    cases stkx with
    | cons _ _ => exact hstk.elim
    | nil =>
      rw [ConRon.Arena.annotateBindersOut]
      simp only [if_true]
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok, Ext.refl _, rfl, curx, hcur, rfl⟩
  | j + 1, s₀, pw?, cur, curx, stkx, hok, hcur, hle, hstk => by
    obtain ⟨⟨tyx, mbx⟩, rest, rfl, ⟨hty, hmb⟩, hrest⟩ :=
      StkRel.take_succ (Nat.lt_of_succ_le hle) hstk
    rw [ConRon.Arena.annotateBindersOut]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    dsimp only at hmb
    refine triple_seq (ExprOps.abstractRangeFast_spec fvarBSpec
      coreWalkFuel s₀ stk[j]!.1 d j 0 hok.state (by rw [hty]; rfl)) ?_
    rintro tyAbs s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
    have hok1 := hok.mono hs1 hx1 hc1 hp1
    have hta : denoteE s1.store tyAbs = some (tyx.abstractRange d j) :=
      hrel1 _ hty
    have hk : ∀ (nd : EIdx) (s2 : AState), (StoreWF s2.store ∧
        Ext s1.store s2.store ∧ s2.caches = s1.caches ∧ s2.pins = s1.pins ∧
        denoteE s2.store nd = some (mkB isLam (tyx.abstractRange d j) curx
          (ConRon.Arena.annotBinderMeta pw? stk[j]!.2))) →
        ⦃fun s => ⌜s = s2⌝⦄
          ConRon.Arena.annotateBindersOut isLam d
            (if pw?.isSome = true then
              some (ConRon.Arena.annotBinderMeta pw? stk[j]!.2).pw else none)
            stk j nd
        ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
            s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
            ConLeche.annotateBindersOut (m := CheckM) (mkB isLam) d pw?
              ((tyx, mbx) :: rest) j curx = .ok v⌝⦄ := by
      rintro nd s2 ⟨hwf2, hx2, hc2, hp2, hnd⟩
      have hok2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
      have hx02 : Ext s₀.store s2.store := hx1.trans hx2
      refine triple_mono (annotateBindersOut_carry isLam d stk j s2 _ nd _ rest
        hok2 hnd (Nat.le_of_succ_le hle) (StkRel.imp (LamR.ext hx02) hrest)) ?_
      rintro r s' ⟨hok', hx', hp', v, hv, hrun⟩
      refine ⟨hok', hx02.trans hx', hp'.trans (hp2.trans hp1), v, hv, ?_⟩
      rw [hmb, annotBinderMeta_eq] at hrun
      have hpw2 : (if pw?.isSome = true then
            some (ConLeche.annotBinderMeta pw? mbx).pw else none)
          = pw?.map (fun _ => (ConLeche.annotBinderMeta pw? mbx).pw) := by
        cases pw? <;> rfl
      rw [hpw2] at hrun
      exact hrun
    have hint := internBinderE_spec isLam s1 tyAbs cur
      (ConRon.Arena.annotBinderMeta pw? stk[j]!.2) _ _ hs1.wf hta
      (denote_ext hcur hx1)
    cases isLam
    · simp only [Bool.false_eq_true, if_false] at hint ⊢
      exact triple_seq hint hk
    · simp only [if_true] at hint ⊢
      exact triple_seq hint hk

/-! ### 4.2 The ∀-annotation loop -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:217-230 annotatePisLeaf — the
mirror's leaf, from its three facts. -/
theorem mAnnotatePisLeaf {F d k : Nat} {tx leaf' v : Expr} {p : PropWhen}
    {ws : List Expr} {stkx : List (Expr × BinderMeta)}
    (ha : ConLeche.annotateCore mode env F (d + k) (tx.instantiateList ws)
      = .ok leaf')
    (hp : ConLeche.annotPwPi (ConLeche.pureFns mode env F) env (d + k) leaf'
      = .ok p)
    (hout : ConLeche.annotateBindersOut (m := CheckM) (mkB false) d (some p) stkx
      (k - 1) (leaf'.abstractRange d k) = .ok v) :
    ConLeche.annotatePisLeaf (ConLeche.pureFns mode env F) env d tx k ws stkx
      = .ok v := by
  unfold ConLeche.annotatePisLeaf ConLeche.annotatePisPw
  rw [annotate_def, ha, ConLeche.okB_bind]
  simp only [hp, bind, Except.bind, pure, Except.pure]
  exact hout

/-- con-leche: none — the ∀-annotation mirror is fuel-monotone
(`annotatePis_atF`). -/
theorem mAnnotatePis_mono {d peel k : Nat} {t v : Expr} {ws : List Expr}
    {stkx : List (Expr × BinderMeta)} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.annotatePis (ConLeche.pureFns mode env F) env d peel t k ws
      stkx = .ok v) :
    ConLeche.annotatePis (ConLeche.pureFns mode env F') env d peel t k ws stkx
      = .ok v := by
  rw [← ConLeche.annotatePis_atF] at h ⊢
  exact (ConLeche.annotatePis (ConLeche.fueledFns mode env) env d peel t k ws
    stkx).property hle h

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1037
annotatePisLeafC_sim — **the ∀-annotation leaf carries**. -/
theorem annotatePisLeaf_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (t : EIdx) (k : Nat) (fvs : Array EIdx)
    (stk : Array (EIdx × BinderMeta)) (tx : Expr) (ws : List Expr)
    (stkx : List (Expr × BinderMeta))
    (hok : CheckOK mode env fe s₀) (ht : denoteE s₀.store t = some tx)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hstk : StkRel (LamR s₀.store) stk.toList.reverse stkx)
    (hk : stk.size = k)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotatePisLeaf (coreKnot mode fe id fuel) fe d t k fvs stk
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
        ∃ F, ConLeche.annotatePisLeaf (ConLeche.pureFns mode env F) env d tx k
          ws stkx = .ok v⌝⦄ := by
  unfold ConRon.Arena.annotatePisLeaf
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ t fvs 0 ws
    hok.state hvec (by rw [ht]; rfl)) ?_
  rintro ob s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
  have hok1 := hok.mono hs1 hx1 hc1 hp1
  have hob : denoteE s1.store ob = some (tx.instantiateList ws) := hrel1 _ ht
  refine triple_seq (hsim.annotate s1 (d + k) ob _ hok1 hob hw) ?_
  rintro lp s2 ⟨hok2, hx2, hp2, lx, hlx, hwlx, F1, hF1⟩
  refine triple_seq (annotPwPi_spec hsim s2 (d + k) lp lx hok2 hlx hwlx) ?_
  rintro p s3 ⟨hok3, hx3, hp3, F2, hF2⟩
  have hlx3 := denote_ext hlx hx3
  refine triple_seq (ExprOps.abstractRangeFast_spec fvarBSpec coreWalkFuel s3 lp
    d k 0 hok3.state (by rw [hlx3]; rfl)) ?_
  rintro cur s4 ⟨hs4, hx4, -, hc4, hp4, -, hrel4⟩
  have hok4 := hok3.mono hs4 hx4 hc4 hp4
  have hcur : denoteE s4.store cur = some (lx.abstractRange d k) := hrel4 _ hlx3
  have hx04 := hx1.trans (hx2.trans (hx3.trans hx4))
  refine triple_mono (annotateBindersOut_carry false d stk stk.size s4 (some p)
    cur _ stkx hok4 hcur (Nat.le_refl _)
    (StkRel.take_size (StkRel.imp (LamR.ext hx04) hstk))) ?_
  rintro r s' ⟨hok', hx', hp', v, hv, hrun⟩
  refine ⟨hok', hx04.trans hx', hp'.trans (hp4.trans (hp3.trans (hp2.trans hp1))),
    v, hv, max F1 F2, ?_⟩
  rw [hk] at hrun
  exact mAnnotatePisLeaf (ConLeche.annotateCore_mono (Nat.le_max_left _ _) hF1)
    (ConLeche.annotPwPi_mono (Nat.le_max_right _ _) hF2) hrun

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1064 annotatePisC_sim
— **THE ∀-ANNOTATION LOOP CARRIES**. -/
theorem annotatePis_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) :
    ∀ (peel : Nat) (s₀ : AState) (t : EIdx) (k : Nat) (fvs : Array EIdx)
      (stk : Array (EIdx × BinderMeta)) (tx : Expr) (ws : List Expr)
      (stkx : List (Expr × BinderMeta)),
      CheckOK mode env fe s₀ → denoteE s₀.store t = some tx →
      ExprOps.InstLVec s₀.store fvs ws →
      StkRel (LamR s₀.store) stk.toList.reverse stkx → stk.size = k →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.annotatePis (coreKnot mode fe id fuel) fe d peel t k fvs stk
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ∃ F, ConLeche.annotatePis (ConLeche.pureFns mode env F) env d peel tx
            k ws stkx = .ok v⌝⦄
  | 0, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hk, hw => by
    rw [ConRon.Arena.annotatePis]
    refine triple_mono (annotatePisLeaf_carry hsim s₀ d t k fvs stk tx ws stkx
      hok ht hvec hstk hk hw) ?_
    rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
    exact ⟨h1, h2, h3, v, hv, F, by rw [ConLeche.annotatePis_zero]; exact hF⟩
  | peel + 1, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hk, hw => by
    have hwf := hok.state.wf
    rw [ConRon.Arena.annotatePis]
    split
    next htg =>
      have htp : t.tag = ETag.forallE := by simpa using htg
      refine triple_seq (viewBind_spec s₀ t) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1
      cases ob with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨ty, body, mb⟩ := p
        dsimp only
        have hv := view_forallE_of_viewBind htp hob.symm
        obtain ⟨tyx, bodyx, rfl, hty, hbody⟩ := denote_forallE_inv hwf hv ht
        have hpiL : (Expr.forallE tyx bodyx mb).instantiateList ws
            = .forallE (tyx.instantiateList ws) (bodyx.instantiateList ws 1)
              mb := by
          simp [Expr.instantiateList]
        have hwc : Expr.WScoped (d + k) (tyx.instantiateList ws) ∧
            Expr.WScoped (d + k) (bodyx.instantiateList ws 1) := by
          rw [hpiL] at hw; simpa only [Expr.WScoped] using hw
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty fvs
          0 ws hok.state hvec (by rw [hty]; rfl)) ?_
        rintro tyo s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
        have hok1 := hok.mono hs1 hx1 hc1 hp1
        have htyo : denoteE s1.store tyo = some (tyx.instantiateList ws) :=
          hrel1 _ hty
        refine triple_seq (hsim.annotate s1 (d + k) tyo _ hok1 htyo hwc.1) ?_
        rintro typ s2 ⟨hok2, hx2, hp2, typx, htypx, hwtypx, F1, hF1⟩
        refine triple_seq (internFVarE_spec s2 (d + k) typ hok2.state.wf
          (by rw [htypx]; rfl)) ?_
        rintro fv s3 ⟨hwf3, hx3, -, -, -, -, hc3, hp3, -, hd3⟩
        have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
        have hfv : denoteE s3.store fv = some (.fvar (d + k) typx) := by
          rw [hd3]; simp [denoteEView, denote_ext htypx hx3]
        have hx03 := hx1.trans (hx2.trans hx3)
        refine triple_mono (annotatePis_carry hsim d peel s3 body (k + 1)
          (fvs.push fv) (stk.push (typ, mb)) bodyx
          (Expr.fvar (d + k) typx :: ws) ((typx, mb) :: stkx) hok3
          (denote_ext hbody hx03)
          (InstLVec.push (hvec.ext hx03) hfv)
          (StkRel.push (StkRel.imp (LamR.ext hx03) hstk)
            ⟨denote_ext htypx hx3, rfl⟩)
          (by simp [hk])
          (by rw [show d + (k + 1) = d + k + 1 by omega, Expr.instantiateList_cons]
              exact Expr.WScoped.instantiate1 hwtypx 0 hwc.2)) ?_
        rintro r s' ⟨hok', hx', hp', v, hv', F2, hF2⟩
        refine ⟨hok', hx03.trans hx', hp'.trans (hp3.trans (hp2.trans hp1)), v,
          hv', max F1 F2, ?_⟩
        rw [ConLeche.annotatePis_succ_pi, annotate_def,
          ConLeche.annotateCore_mono (Nat.le_max_left _ _) hF1, ConLeche.okB_bind]
        exact mAnnotatePis_mono (Nat.le_max_right _ _) hF2
    next htg =>
      have hne : t.tag ≠ ETag.forallE := by simpa using htg
      have hnp := denote_not_forallE_of_tag hwf ht hne
      refine triple_mono (annotatePisLeaf_carry hsim s₀ d t k fvs stk tx ws stkx
        hok ht hvec hstk hk hw) ?_
      rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
      exact ⟨h1, h2, h3, v, hv, F,
        by rw [ConLeche.annotatePis_succ_ne_pi _ hnp]; exact hF⟩

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1272
annotatePisC_tail_sim (its `himp` half) — **the pure side of the `.forallE`
annotation clause**, by con-leche's `annotatePis_sound`. -/
theorem annotateCore_forallE_of_loop {d F1 F3 : Nat} {tyx bodyx typx : Expr}
    {mb : BinderMeta} {v : Expr} {peel : Nat}
    (hF1 : ConLeche.annotateCore mode env F1 d tyx = .ok typx)
    (hF3 : ConLeche.annotatePis (ConLeche.pureFns mode env F3) env d peel bodyx 1
      [Expr.fvar d typx] [(typx, mb)] = .ok v) :
    ∃ F, ConLeche.annotateCore mode env F d (.forallE tyx bodyx mb) = .ok v := by
  obtain ⟨F', hchain⟩ := ConLeche.annotatePis_sound (env := env) peel bodyx 1
    [Expr.fvar d typx] [(typx, mb)] F3 v rfl hF3
  obtain ⟨body', hbody', hwrap⟩ := ConLeche.bind_okB hchain
  let G := max F1 F'
  have hle1 : F1 ≤ G := Nat.le_max_left _ _
  have hle3 : F' ≤ G := Nat.le_max_right _ _
  refine ⟨G + 1, ?_⟩
  rw [ConLeche.annotateCore_forallE_eq, ConLeche.annotateCore_mono hle1 hF1,
    ConLeche.okB_bind]
  have hb' : ConLeche.annotateCore mode env G (d + 1)
      (bodyx.instantiate1 (.fvar d typx)) = .ok body' := by
    rw [← ConLeche.instList_single bodyx (Expr.fvar d typx)]
    exact ConLeche.annotateCore_mono hle3 hbody'
  rw [hb', ConLeche.okB_bind]
  rw [ConLeche.annotatePisWrap_cons] at hwrap
  simp only [ConLeche.annotatePisWrap_nil, show (1 : Nat) - 1 = 0 from rfl,
    Nat.add_zero] at hwrap
  revert hwrap
  split
  · intro hwrap
    obtain ⟨pw, hpw, hwrap⟩ := ConLeche.bind_okB hwrap
    rw [ConLeche.annotPwPi_mono hle3 hpw, ConLeche.okB_bind]
    exact hwrap
  · exact id

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1272
annotatePisC_tail_sim — **THE `.forallE` ANNOTATION CLAUSE CARRIES**: the
domain annotated, the first free variable, `annotatePis` from `k = 1`. -/
theorem annotateForall_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty body : EIdx) (mb : BinderMeta)
    (tyx bodyx : Expr) (hok : CheckOK mode env fe s₀)
    (hty : denoteE s₀.store ty = some tyx)
    (hbody : denoteE s₀.store body = some bodyx)
    (hw : Expr.WScoped d (.forallE tyx bodyx mb)) :
    ⦃fun s => ⌜s = s₀⌝⦄ (do
      let typ ← (coreKnot mode fe id fuel).annotate d ty
      let fv ← internFVarE d typ
      ConRon.Arena.annotatePis (coreKnot mode fe id fuel) fe d peelFuel body 1
        #[fv] #[(typ, mb)])
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d (.forallE tyx bodyx mb)
          s'.store r⌝⦄ := by
  have hwty : Expr.WScoped d tyx := by unfold Expr.WScoped at hw; exact hw.1
  have hwbody : Expr.WScoped d bodyx := by unfold Expr.WScoped at hw; exact hw.2
  refine triple_seq (hsim.annotate s₀ d ty tyx hok hty hwty) ?_
  rintro typ s1 ⟨hok1, hx1, hp1, typx, htypx, hwtypx, F1, hF1⟩
  refine triple_seq (internFVarE_spec s1 d typ hok1.state.wf
    (by rw [htypx]; rfl)) ?_
  rintro fv s2 ⟨hwf2, hx2, -, -, -, -, hc2, hp2, -, hd2⟩
  have hok2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
  have hfv : denoteE s2.store fv = some (.fvar d typx) := by
    rw [hd2]; simp [denoteEView, denote_ext htypx hx2]
  have hx02 := hx1.trans hx2
  have hvec : ExprOps.InstLVec s2.store #[fv] [Expr.fvar d typx] :=
    InstLVec.push (InstLVec.empty _) hfv
  have hstk : StkRel (LamR s2.store) (#[(typ, mb)] : Array _).toList.reverse
      [(typx, mb)] :=
    StkRel.push (stk := #[]) (stkx := []) trivial ⟨denote_ext htypx hx2, rfl⟩
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d typx]) := by
    rw [ConLeche.instList_single]
    exact Expr.WScoped.instantiate1 hwtypx 0 hwbody
  refine triple_mono (annotatePis_carry hsim d peelFuel s2 body 1 #[fv]
    #[(typ, mb)] bodyx [Expr.fvar d typx] [(typx, mb)] hok2
    (denote_ext hbody hx02) hvec hstk rfl hwopen) ?_
  rintro r s' ⟨hok', hx', hp', v, hv, F3, hF3⟩
  obtain ⟨F, hF⟩ := annotateCore_forallE_of_loop hF1 hF3
  exact ⟨hok', hx02.trans hx', hp'.trans (hp2.trans hp1), v, hv,
    ConLeche.annotateCore_WScoped F _ hF hw, F, hF⟩

/-! ### 4.3 The λ-annotation loop -/

/-- con-leche: ConLeche/Verify/BinderLoop.lean:245-258 annotateLamsLeaf — the
mirror's leaf, from its three facts. -/
theorem mAnnotateLamsLeaf {F d k : Nat} {tx leaf' v : Expr} {p : PropWhen}
    {ws : List Expr} {stkx : List (Expr × BinderMeta)}
    (ha : ConLeche.annotateCore mode env F (d + k) (tx.instantiateList ws)
      = .ok leaf')
    (hp : ConLeche.annotPwLam (ConLeche.pureFns mode env F) env (d + k) leaf'
      = .ok p)
    (hout : ConLeche.annotateBindersOut (m := CheckM) (mkB true) d (some p) stkx
      (k - 1) (leaf'.abstractRange d k) = .ok v) :
    ConLeche.annotateLamsLeaf (ConLeche.pureFns mode env F) env d tx k ws stkx
      = .ok v := by
  unfold ConLeche.annotateLamsLeaf ConLeche.annotateLamsPw
  rw [annotate_def, ha, ConLeche.okB_bind]
  simp only [hp, bind, Except.bind, pure, Except.pure]
  exact hout

/-- con-leche: none — the λ-annotation mirror is fuel-monotone
(`annotateLams_atF`). -/
theorem mAnnotateLams_mono {d peel k : Nat} {t v : Expr} {ws : List Expr}
    {stkx : List (Expr × BinderMeta)} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.annotateLams (ConLeche.pureFns mode env F) env d peel t k ws
      stkx = .ok v) :
    ConLeche.annotateLams (ConLeche.pureFns mode env F') env d peel t k ws stkx
      = .ok v := by
  rw [← ConLeche.annotateLams_atF] at h ⊢
  exact (ConLeche.annotateLams (ConLeche.fueledFns mode env) env d peel t k ws
    stkx).property hle h

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1138
annotateLamsLeafC_sim — **the λ-annotation leaf carries**. -/
theorem annotateLamsLeaf_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (t : EIdx) (k : Nat) (fvs : Array EIdx)
    (stk : Array (EIdx × BinderMeta)) (tx : Expr) (ws : List Expr)
    (stkx : List (Expr × BinderMeta))
    (hok : CheckOK mode env fe s₀) (ht : denoteE s₀.store t = some tx)
    (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (hstk : StkRel (LamR s₀.store) stk.toList.reverse stkx)
    (hk : stk.size = k)
    (hw : Expr.WScoped (d + k) (tx.instantiateList ws)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotateLamsLeaf (coreKnot mode fe id fuel) fe d t k fvs stk
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
        ∃ F, ConLeche.annotateLamsLeaf (ConLeche.pureFns mode env F) env d tx k
          ws stkx = .ok v⌝⦄ := by
  unfold ConRon.Arena.annotateLamsLeaf
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ t fvs 0 ws
    hok.state hvec (by rw [ht]; rfl)) ?_
  rintro ob s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
  have hok1 := hok.mono hs1 hx1 hc1 hp1
  have hob : denoteE s1.store ob = some (tx.instantiateList ws) := hrel1 _ ht
  refine triple_seq (hsim.annotate s1 (d + k) ob _ hok1 hob hw) ?_
  rintro lp s2 ⟨hok2, hx2, hp2, lx, hlx, hwlx, F1, hF1⟩
  refine triple_seq (annotPwLam_spec hsim s2 (d + k) lp lx hok2 hlx hwlx) ?_
  rintro p s3 ⟨hok3, hx3, hp3, F2, hF2⟩
  have hlx3 := denote_ext hlx hx3
  refine triple_seq (ExprOps.abstractRangeFast_spec fvarBSpec coreWalkFuel s3 lp
    d k 0 hok3.state (by rw [hlx3]; rfl)) ?_
  rintro cur s4 ⟨hs4, hx4, -, hc4, hp4, -, hrel4⟩
  have hok4 := hok3.mono hs4 hx4 hc4 hp4
  have hcur : denoteE s4.store cur = some (lx.abstractRange d k) := hrel4 _ hlx3
  have hx04 := hx1.trans (hx2.trans (hx3.trans hx4))
  refine triple_mono (annotateBindersOut_carry true d stk stk.size s4 (some p)
    cur _ stkx hok4 hcur (Nat.le_refl _)
    (StkRel.take_size (StkRel.imp (LamR.ext hx04) hstk))) ?_
  rintro r s' ⟨hok', hx', hp', v, hv, hrun⟩
  refine ⟨hok', hx04.trans hx', hp'.trans (hp4.trans (hp3.trans (hp2.trans hp1))),
    v, hv, max F1 F2, ?_⟩
  rw [hk] at hrun
  exact mAnnotateLamsLeaf (ConLeche.annotateCore_mono (Nat.le_max_left _ _) hF1)
    (ConLeche.annotPwLam_mono (Nat.le_max_right _ _) hF2) hrun

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1165 annotateLamsC_sim
— **THE ∀-ANNOTATION LOOP CARRIES**. -/
theorem annotateLams_carry {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) :
    ∀ (peel : Nat) (s₀ : AState) (t : EIdx) (k : Nat) (fvs : Array EIdx)
      (stk : Array (EIdx × BinderMeta)) (tx : Expr) (ws : List Expr)
      (stkx : List (Expr × BinderMeta)),
      CheckOK mode env fe s₀ → denoteE s₀.store t = some tx →
      ExprOps.InstLVec s₀.store fvs ws →
      StkRel (LamR s₀.store) stk.toList.reverse stkx → stk.size = k →
      Expr.WScoped (d + k) (tx.instantiateList ws) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.annotateLams (coreKnot mode fe id fuel) fe d peel t k fvs stk
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ ∃ v, denoteE s'.store r = some v ∧
          ∃ F, ConLeche.annotateLams (ConLeche.pureFns mode env F) env d peel tx
            k ws stkx = .ok v⌝⦄
  | 0, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hk, hw => by
    rw [ConRon.Arena.annotateLams]
    refine triple_mono (annotateLamsLeaf_carry hsim s₀ d t k fvs stk tx ws stkx
      hok ht hvec hstk hk hw) ?_
    rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
    exact ⟨h1, h2, h3, v, hv, F, by rw [ConLeche.annotateLams_zero]; exact hF⟩
  | peel + 1, s₀, t, k, fvs, stk, tx, ws, stkx, hok, ht, hvec, hstk, hk, hw => by
    have hwf := hok.state.wf
    rw [ConRon.Arena.annotateLams]
    split
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
            = .lam (tyx.instantiateList ws) (bodyx.instantiateList ws 1)
              mb := by
          simp [Expr.instantiateList]
        have hwc : Expr.WScoped (d + k) (tyx.instantiateList ws) ∧
            Expr.WScoped (d + k) (bodyx.instantiateList ws 1) := by
          rw [hlamL] at hw; simpa only [Expr.WScoped] using hw
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty fvs
          0 ws hok.state hvec (by rw [hty]; rfl)) ?_
        rintro tyo s1 ⟨hs1, hx1, -, hc1, hp1, -, hrel1⟩
        have hok1 := hok.mono hs1 hx1 hc1 hp1
        have htyo : denoteE s1.store tyo = some (tyx.instantiateList ws) :=
          hrel1 _ hty
        refine triple_seq (hsim.annotate s1 (d + k) tyo _ hok1 htyo hwc.1) ?_
        rintro typ s2 ⟨hok2, hx2, hp2, typx, htypx, hwtypx, F1, hF1⟩
        refine triple_seq (internFVarE_spec s2 (d + k) typ hok2.state.wf
          (by rw [htypx]; rfl)) ?_
        rintro fv s3 ⟨hwf3, hx3, -, -, -, -, hc3, hp3, -, hd3⟩
        have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
        have hfv : denoteE s3.store fv = some (.fvar (d + k) typx) := by
          rw [hd3]; simp [denoteEView, denote_ext htypx hx3]
        have hx03 := hx1.trans (hx2.trans hx3)
        refine triple_mono (annotateLams_carry hsim d peel s3 body (k + 1)
          (fvs.push fv) (stk.push (typ, mb)) bodyx
          (Expr.fvar (d + k) typx :: ws) ((typx, mb) :: stkx) hok3
          (denote_ext hbody hx03)
          (InstLVec.push (hvec.ext hx03) hfv)
          (StkRel.push (StkRel.imp (LamR.ext hx03) hstk)
            ⟨denote_ext htypx hx3, rfl⟩)
          (by simp [hk])
          (by rw [show d + (k + 1) = d + k + 1 by omega, Expr.instantiateList_cons]
              exact Expr.WScoped.instantiate1 hwtypx 0 hwc.2)) ?_
        rintro r s' ⟨hok', hx', hp', v, hv', F2, hF2⟩
        refine ⟨hok', hx03.trans hx', hp'.trans (hp3.trans (hp2.trans hp1)), v,
          hv', max F1 F2, ?_⟩
        rw [ConLeche.annotateLams_succ_lam, annotate_def,
          ConLeche.annotateCore_mono (Nat.le_max_left _ _) hF1, ConLeche.okB_bind]
        exact mAnnotateLams_mono (Nat.le_max_right _ _) hF2
    next htg =>
      have hne : t.tag ≠ ETag.lam := by simpa using htg
      have hnl := denote_not_lam_of_tag hwf ht hne
      refine triple_mono (annotateLamsLeaf_carry hsim s₀ d t k fvs stk tx ws stkx
        hok ht hvec hstk hk hw) ?_
      rintro r s' ⟨h1, h2, h3, v, hv, F, hF⟩
      exact ⟨h1, h2, h3, v, hv, F,
        by rw [ConLeche.annotateLams_succ_ne_lam _ hnl]; exact hF⟩

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1376
annotateLamsC_tail_sim (its `himp` half) — **the pure side of the `.lam`
annotation clause**, by con-leche's `annotateLams_sound`. -/
theorem annotateCore_lam_of_loop {d F1 F3 : Nat} {tyx bodyx typx : Expr}
    {mb : BinderMeta} {v : Expr} {peel : Nat}
    (hF1 : ConLeche.annotateCore mode env F1 d tyx = .ok typx)
    (hF3 : ConLeche.annotateLams (ConLeche.pureFns mode env F3) env d peel bodyx 1
      [Expr.fvar d typx] [(typx, mb)] = .ok v) :
    ∃ F, ConLeche.annotateCore mode env F d (.lam tyx bodyx mb) = .ok v := by
  obtain ⟨F', hchain⟩ := ConLeche.annotateLams_sound (env := env) peel bodyx 1
    [Expr.fvar d typx] [(typx, mb)] F3 v rfl hF3
  obtain ⟨body', hbody', hwrap⟩ := ConLeche.bind_okB hchain
  let G := max F1 F'
  have hle1 : F1 ≤ G := Nat.le_max_left _ _
  have hle3 : F' ≤ G := Nat.le_max_right _ _
  refine ⟨G + 1, ?_⟩
  rw [ConLeche.annotateCore_lam_eq, ConLeche.annotateCore_mono hle1 hF1,
    ConLeche.okB_bind]
  have hb' : ConLeche.annotateCore mode env G (d + 1)
      (bodyx.instantiate1 (.fvar d typx)) = .ok body' := by
    rw [← ConLeche.instList_single bodyx (Expr.fvar d typx)]
    exact ConLeche.annotateCore_mono hle3 hbody'
  rw [hb', ConLeche.okB_bind]
  rw [ConLeche.annotateLamsWrap_cons] at hwrap
  simp only [ConLeche.annotateLamsWrap_nil, show (1 : Nat) - 1 = 0 from rfl,
    Nat.add_zero] at hwrap
  revert hwrap
  split
  · intro hwrap
    obtain ⟨pw, hpw, hwrap⟩ := ConLeche.bind_okB hwrap
    rw [ConLeche.annotPwLam_mono hle3 hpw, ConLeche.okB_bind]
    exact hwrap
  · exact id

/-- con-leche: ConLeche/Verify/Cached/BinderLoopC.lean:1376
annotateLamsC_tail_sim — **THE `.lam` ANNOTATION (bvar-closed branch) CLAUSE CARRIES**: the
domain annotated, the first free variable, `annotateLams` from `k = 1`. -/
theorem annotateLamLoop_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty body : EIdx) (mb : BinderMeta)
    (tyx bodyx : Expr) (hok : CheckOK mode env fe s₀)
    (hty : denoteE s₀.store ty = some tyx)
    (hbody : denoteE s₀.store body = some bodyx)
    (hw : Expr.WScoped d (.lam tyx bodyx mb)) :
    ⦃fun s => ⌜s = s₀⌝⦄ (do
      let typ ← (coreKnot mode fe id fuel).annotate d ty
      let fv ← internFVarE d typ
      ConRon.Arena.annotateLams (coreKnot mode fe id fuel) fe d peelFuel body 1
        #[fv] #[(typ, mb)])
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d (.lam tyx bodyx mb)
          s'.store r⌝⦄ := by
  have hwty : Expr.WScoped d tyx := by unfold Expr.WScoped at hw; exact hw.1
  have hwbody : Expr.WScoped d bodyx := by unfold Expr.WScoped at hw; exact hw.2
  refine triple_seq (hsim.annotate s₀ d ty tyx hok hty hwty) ?_
  rintro typ s1 ⟨hok1, hx1, hp1, typx, htypx, hwtypx, F1, hF1⟩
  refine triple_seq (internFVarE_spec s1 d typ hok1.state.wf
    (by rw [htypx]; rfl)) ?_
  rintro fv s2 ⟨hwf2, hx2, -, -, -, -, hc2, hp2, -, hd2⟩
  have hok2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
  have hfv : denoteE s2.store fv = some (.fvar d typx) := by
    rw [hd2]; simp [denoteEView, denote_ext htypx hx2]
  have hx02 := hx1.trans hx2
  have hvec : ExprOps.InstLVec s2.store #[fv] [Expr.fvar d typx] :=
    InstLVec.push (InstLVec.empty _) hfv
  have hstk : StkRel (LamR s2.store) (#[(typ, mb)] : Array _).toList.reverse
      [(typx, mb)] :=
    StkRel.push (stk := #[]) (stkx := []) trivial ⟨denote_ext htypx hx2, rfl⟩
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d typx]) := by
    rw [ConLeche.instList_single]
    exact Expr.WScoped.instantiate1 hwtypx 0 hwbody
  refine triple_mono (annotateLams_carry hsim d peelFuel s2 body 1 #[fv]
    #[(typ, mb)] bodyx [Expr.fvar d typx] [(typx, mb)] hok2
    (denote_ext hbody hx02) hvec hstk rfl hwopen) ?_
  rintro r s' ⟨hok', hx', hp', v, hv, F3, hF3⟩
  obtain ⟨F, hF⟩ := annotateCore_lam_of_loop hF1 hF3
  exact ⟨hok', hx02.trans hx', hp'.trans (hp2.trans hp1), v, hv,
    ConLeche.annotateCore_WScoped F _ hF hw, F, hF⟩

/-! ### 4.4 The λ residual: the per-binder clause -/

/-- con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody — **the
per-binder `.lam` clause carries** (`annotateBinder … true`, the residual
con-leche's cached tier keeps for a λ that is not `bvar`-closed): the
domain annotated, one `instantiate1`, the body annotated, the datum written
unless one is, one `abstract1`, the node. -/
theorem annotateBinderLam_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty body : EIdx) (mb : BinderMeta)
    (tyx bodyx : Expr) (hok : CheckOK mode env fe s₀)
    (hty : denoteE s₀.store ty = some tyx)
    (hbody : denoteE s₀.store body = some bodyx)
    (hw : Expr.WScoped d (.lam tyx bodyx mb)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotateBinder (coreKnot mode fe id fuel) fe d ty body mb true
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d (.lam tyx bodyx mb)
          s'.store r⌝⦄ := by
  have hwty : Expr.WScoped d tyx := by unfold Expr.WScoped at hw; exact hw.1
  have hwbody : Expr.WScoped d bodyx := by unfold Expr.WScoped at hw; exact hw.2
  unfold ConRon.Arena.annotateBinder
  -- stage 1: the domain
  refine triple_seq (hsim.annotate s₀ d ty tyx hok hty hwty) ?_
  rintro typ s1 ⟨hok1, hx1, hp1, typx, htypx, hwtypx, F1, hF1⟩
  -- stage 2: the free variable
  refine triple_seq (internFVarE_spec s1 d typ hok1.state.wf
    (by rw [htypx]; rfl)) ?_
  rintro fv s2 ⟨hwf2, hx2, -, -, -, -, hc2, hp2, -, hd2⟩
  have hok2 := hok1.mono ⟨hwf2⟩ hx2 hc2 hp2
  have hfv : denoteE s2.store fv = some (.fvar d typx) := by
    rw [hd2]; simp [denoteEView, denote_ext htypx hx2]
  have hx02 := hx1.trans hx2
  have hbody2 := denote_ext hbody hx02
  -- stage 3: the body, opened
  refine triple_seq (instantiate1Fast_specE coreWalkFuel s2 body fv 0 hok2.state
    (by rw [hfv]; rfl) (by rw [hbody2]; rfl)) ?_
  rintro ob s3 ⟨hs3, hx3, hc3, hp3, -, hrel3⟩
  have hok3 := hok2.mono hs3 hx3 hc3 hp3
  have hob : denoteE s3.store ob = some (bodyx.instantiate1 (.fvar d typx)) :=
    hrel3 _ hfv _ hbody2
  have hwob : Expr.WScoped (d + 1) (bodyx.instantiate1 (.fvar d typx)) :=
    Expr.WScoped.instantiate1 hwtypx 0 hwbody
  -- stage 4: the body, annotated
  refine triple_seq (hsim.annotate s3 (d + 1) ob _ hok3 hob hwob) ?_
  rintro bp s4 ⟨hok4, hx4, hp4, bpx, hbpx, hwbpx, F2, hF2⟩
  have hx04 := hx02.trans (hx3.trans hx4)
  have htypx4 := denote_ext htypx (hx2.trans (hx3.trans hx4))
  -- the tail, from the datum and a fuel at which the pure datum is it
  have hk : ∀ (pw : PropWhen) (s5 : AState) (F3 : Nat),
      CheckOK mode env fe s5 → Ext s4.store s5.store → s5.pins = s4.pins →
      (ConLeche.annotateCore mode env (max (max F1 F2) F3 + 1) d
        (.lam tyx bodyx mb) = .ok (.lam typx (bpx.abstract1 d) ⟨pw⟩)) →
      ⦃fun s => ⌜s = s5⌝⦄ (do
        let ab ← abstract1Fast coreWalkFuel bp d 0
        if true = true then internLamE typ ab ⟨pw⟩
        else internForallEE typ ab ⟨pw⟩)
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimE (ConLeche.annotateCore mode env) d (.lam tyx bodyx mb)
            s'.store r⌝⦄ := by
    intro pw s5 F3 hok5 hx5 hp5 hpure
    have hbp5 := denote_ext hbpx hx5
    refine triple_seq (ExprOps.abstract1Fast_spec fvarBSpec coreWalkFuel s5 bp d
      0 hok5.state (by rw [hbp5]; rfl)) ?_
    rintro ab s6 ⟨hs6, hx6, -, hc6, hp6, -, hrel6⟩
    have hok6 := hok5.mono hs6 hx6 hc6 hp6
    have hab : denoteE s6.store ab = some (bpx.abstract1 d) := hrel6 _ hbp5
    simp only [if_true]
    refine triple_mono (internLamE_spec s6 typ ab ⟨pw⟩ hok6.state.wf
      (by rw [denote_ext htypx4 (hx5.trans hx6)]; rfl) (by rw [hab]; rfl)) ?_
    rintro r s7 ⟨hwf7, hx7, -, -, -, -, hc7, hp7, -, hd7⟩
    have hok7 := hok6.mono ⟨hwf7⟩ hx7 hc7 hp7
    refine ⟨hok7, hx04.trans (hx5.trans (hx6.trans hx7)),
      hp7.trans (hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1))))),
      _, ?_, ConLeche.annotateCore_WScoped _ _ hpure hw, _, hpure⟩
    rw [hd7]
    simp [denoteEView, denote_ext htypx4 (hx5.trans (hx6.trans hx7)),
      denote_ext hab hx7]
  have hA : ∀ G, max F1 F2 ≤ G →
      ConLeche.annotateCore mode env G d tyx = .ok typx ∧
      ConLeche.annotateCore mode env G (d + 1)
        (bodyx.instantiate1 (.fvar d typx)) = .ok bpx := fun G hle =>
    ⟨ConLeche.annotateCore_mono (Nat.le_trans (Nat.le_max_left _ _) hle) hF1,
     ConLeche.annotateCore_mono (Nat.le_trans (Nat.le_max_right _ _) hle) hF2⟩
  by_cases hwr : (!ConRon.Arena.pwWritten mb.pw) = true
  · rw [if_pos hwr]
    simp only [if_true]
    refine triple_seq (annotPwLam_spec hsim s4 (d + 1) bp bpx hok4 hbpx hwbpx) ?_
    rintro pw s5 ⟨hok5, hx5, hp5, F3, hF3⟩
    refine hk pw s5 F3 hok5 hx5 hp5 ?_
    obtain ⟨h1, h2⟩ := hA (max (max F1 F2) F3) (Nat.le_max_left _ _)
    have hwr' : (!ConLeche.pwWritten mb.pw) = true := hwr
    rw [ConLeche.annotateCore_lam_eq, h1, ConLeche.okB_bind, h2,
      ConLeche.okB_bind, if_pos hwr',
      ConLeche.annotPwLam_mono (Nat.le_max_right _ _) hF3, ConLeche.okB_bind]
    rfl
  · rw [if_neg hwr, pure_bind]
    refine hk mb.pw s4 0 hok4 (Ext.refl _) rfl ?_
    obtain ⟨h1, h2⟩ := hA (max (max F1 F2) 0) (Nat.le_max_left _ _)
    have hwr' : ¬ (!ConLeche.pwWritten mb.pw) = true := hwr
    rw [ConLeche.annotateCore_lam_eq, h1, ConLeche.okB_bind, h2,
      ConLeche.okB_bind, if_neg hwr']
    rfl

/-! ## 5. The axiom census -/

#print axioms inferLamsOut_carry
#print axioms inferLamsLeafCheck_carry
#print axioms inferLamsLeaf_carry
#print axioms inferLams_carry
#print axioms inferTypeCore_lam_of_loop
#print axioms inferLam_spec
#print axioms inferPisOut_carry
#print axioms inferPisLeaf_carry
#print axioms inferPis_carry
#print axioms inferTypeCore_forallE_of_loop
#print axioms inferForall_spec
#print axioms annotateBindersOut_carry
#print axioms annotatePisLeaf_carry
#print axioms annotatePis_carry
#print axioms annotateCore_forallE_of_loop
#print axioms annotateForall_spec
#print axioms annotateLamsLeaf_carry
#print axioms annotateLams_carry
#print axioms annotateCore_lam_of_loop
#print axioms annotateLamLoop_spec
#print axioms annotateBinderLam_spec

end ConRon.Bridge.Core
