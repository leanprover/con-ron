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

end ConRon.Bridge.Core
