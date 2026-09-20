/-
# Experiment C2's layer: the mini store's `@[spec]` theorems

`Specs.lean` is this layer at the real `EStore`; this is the same eight
groups at the mini arena, so that experiment C2 is *literally* experiment A's
recipe with ten constructors cut to three.  Nothing here mentions `Vec` or
`u32`: the denotation half of Theorem 2 is representation-free.

Two deliberate deviations from `Specs.lean`, both measured in the round-2
report:

* **the denotation is a relation, not a function.**  `denoteE` is a *function*
  because `StoreWF` supplies a rank witness that bounds its fuel; the mini
  arena carries no rank, so `DenotesM s h e` is `∃ n, denoteMAux s n h = some e`
  and functionality (`DenotesM.uniq`) replaces `Option.some.inj`.  That costs
  one lemma group and buys the whole rank machinery.
* **the capacity invariant `MWF` is needed here too.**  `mFindApp` returns
  `mMk mTagApp j`, and `mTagOf (mMk mTagApp j) = mTagApp` only for
  `j < mIdxCap`.  The same invariant C1 needs for Rust's truncating `as u32`
  is needed on the twin's side for the tag arithmetic — both halves of
  Theorem 2 carry a capacity invariant, which round 1 did not predict.
-/
import ConRon.Arena.Spike.MiniRun

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option maxHeartbeats 1000000
set_option mvcgen.warning false

/-! ## The capacity invariant and the extension order -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the mini arena's capacity
invariant: no constructor array longer than `IDX_CAP`, so that a handle's tag
and index round-trip. -/
structure MWF (s : MState) : Prop where
  bvars : s.bvars.length ≤ mIdxCap
  apps : s.apps.length ≤ mIdxCap
  lams : s.lams.length ≤ mIdxCap

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt (the `Ext` conjunct) — the
arena only grows, and only at the end of each array. -/
structure MExt (s s' : MState) : Prop where
  bvars : ∃ l, s'.bvars = s.bvars ++ l
  apps : ∃ l, s'.apps = s.apps ++ l
  lams : ∃ l, s'.lams = s.lams ++ l

theorem MExt.refl (s : MState) : MExt s s := ⟨⟨[], by simp⟩, ⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem MExt.trans {a b c : MState} (h1 : MExt a b) (h2 : MExt b c) : MExt a c := by
  obtain ⟨⟨l1, e1⟩, ⟨m1, f1⟩, ⟨n1, g1⟩⟩ := h1
  obtain ⟨⟨l2, e2⟩, ⟨m2, f2⟩, ⟨n2, g2⟩⟩ := h2
  exact ⟨⟨l1 ++ l2, by rw [e2, e1, List.append_assoc]⟩,
         ⟨m1 ++ m2, by rw [f2, f1, List.append_assoc]⟩,
         ⟨n1 ++ n2, by rw [g2, g1, List.append_assoc]⟩⟩

/-- con-leche: none — a lookup that succeeded still succeeds after an append. -/
theorem prefix_getElem {α : Type} {l l' m : List α} {i : Nat} {x : α}
    (hl : l' = l ++ m) (h : l[i]? = some x) : l'[i]? = some x := by
  subst hl
  have hi : i < l.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
    exact hlt
  rw [List.getElem?_append_left hi]; exact h

theorem MExt.viewBvar {s s' : MState} (hx : MExt s s') {h i : Nat}
    (hv : s.viewBvar h = some i) : s'.viewBvar h = some i := by
  obtain ⟨l, hl⟩ := hx.bvars
  simp only [MState.viewBvar] at hv ⊢
  split at hv
  · rename_i ht; rw [if_pos ht]; exact prefix_getElem hl hv
  · simp at hv

theorem MExt.viewApp {s s' : MState} (hx : MExt s s') {h : Nat} {p : Nat × Nat}
    (hv : s.viewApp h = some p) : s'.viewApp h = some p := by
  obtain ⟨l, hl⟩ := hx.apps
  simp only [MState.viewApp] at hv ⊢
  split at hv
  · rename_i ht; rw [if_pos ht]; exact prefix_getElem hl hv
  · simp at hv

theorem MExt.viewLam {s s' : MState} (hx : MExt s s') {h : Nat} {p : Nat × Nat}
    (hv : s.viewLam h = some p) : s'.viewLam h = some p := by
  obtain ⟨l, hl⟩ := hx.lams
  simp only [MState.viewLam] at hv ⊢
  split at hv
  · rename_i ht; rw [if_pos ht]; exact prefix_getElem hl hv
  · simp at hv


/-! ## The denotation, as a relation

`denoteE` is a function because `StoreWF` supplies a rank; the mini arena has
no rank, so "h reads back as e" is "some fuel suffices".  Monotonicity in the
fuel makes that single-valued (`DenotesM.uniq`), and it makes both the
introduction and the elimination of a node available — which a fixed fuel does
not.

Four unfolding lemmas first: the *only* place `denoteMAux` is unfolded. -/

theorem tag_bvar_ne_app : ¬ (mTagApp = mTagBvar) := by decide
theorem tag_bvar_ne_lam : ¬ (mTagLam = mTagBvar) := by decide
theorem tag_app_ne_lam : ¬ (mTagLam = mTagApp) := by decide

theorem viewBvar_tag {s : MState} {h i : Nat} (hv : s.viewBvar h = some i) :
    mTagOf h = mTagBvar := by
  simp only [MState.viewBvar] at hv; split at hv
  · assumption
  · simp at hv

theorem viewApp_tag {s : MState} {h : Nat} {p : Nat × Nat} (hv : s.viewApp h = some p) :
    mTagOf h = mTagApp := by
  simp only [MState.viewApp] at hv; split at hv
  · assumption
  · simp at hv

theorem viewLam_tag {s : MState} {h : Nat} {p : Nat × Nat} (hv : s.viewLam h = some p) :
    mTagOf h = mTagLam := by
  simp only [MState.viewLam] at hv; split at hv
  · assumption
  · simp at hv

theorem dm_bvar {s : MState} {h i : Nat} (n : Nat) (hv : s.viewBvar h = some i) :
    denoteMAux s (n + 1) h = some (.bvar i) := by
  simp only [denoteMAux, if_pos (viewBvar_tag hv), hv, Option.map_some]

theorem dm_app {s : MState} {h a b : Nat} (n : Nat) (hv : s.viewApp h = some (a, b)) :
    denoteMAux s (n + 1) h = opt2 Expr.app (denoteMAux s n a) (denoteMAux s n b) := by
  have ht := viewApp_tag hv
  have hb : ¬ (mTagOf h = mTagBvar) := by rw [ht]; exact tag_bvar_ne_app
  simp only [denoteMAux, if_neg hb, if_pos ht, hv]

theorem dm_lam {s : MState} {h a b : Nat} (n : Nat) (hv : s.viewLam h = some (a, b)) :
    denoteMAux s (n + 1) h
      = opt2 (fun x y => Expr.lam x y default) (denoteMAux s n a) (denoteMAux s n b) := by
  have ht := viewLam_tag hv
  have hb : ¬ (mTagOf h = mTagBvar) := by rw [ht]; exact tag_bvar_ne_lam
  have ha : ¬ (mTagOf h = mTagApp) := by rw [ht]; exact tag_app_ne_lam
  simp only [denoteMAux, if_neg hb, if_neg ha, if_pos ht, hv]

/-- con-leche: none — every `some` answer comes from one of the three shapes.
This is the mini arena's `Verify/Disc.lean`, in one lemma because there are
three constructors rather than ten. -/
theorem dm_inv {s : MState} {h : Nat} {e : Expr} :
    ∀ (n : Nat), denoteMAux s n h = some e →
      (∃ m i, n = m + 1 ∧ s.viewBvar h = some i ∧ e = .bvar i) ∨
      (∃ m a b ea eb, n = m + 1 ∧ s.viewApp h = some (a, b) ∧ e = .app ea eb ∧
        denoteMAux s m a = some ea ∧ denoteMAux s m b = some eb) ∨
      (∃ m a b ea eb, n = m + 1 ∧ s.viewLam h = some (a, b) ∧ e = .lam ea eb default ∧
        denoteMAux s m a = some ea ∧ denoteMAux s m b = some eb) := by
  intro n hd
  cases n with
  | zero => simp [denoteMAux] at hd
  | succ m =>
    by_cases hb : mTagOf h = mTagBvar
    · simp only [denoteMAux, if_pos hb, Option.map_eq_some_iff] at hd
      obtain ⟨i, hi, he⟩ := hd
      exact Or.inl ⟨m, i, rfl, hi, he.symm⟩
    · by_cases ha : mTagOf h = mTagApp
      · cases hv : s.viewApp h with
        | none => simp only [denoteMAux, if_neg hb, if_pos ha, hv] at hd; simp at hd
        | some p =>
          obtain ⟨a, b⟩ := p
          rw [dm_app m hv, opt2_eq_some_iff] at hd
          obtain ⟨x, y, hx, hy, he⟩ := hd
          exact Or.inr (Or.inl ⟨m, a, b, x, y, rfl, rfl, he.symm, hx, hy⟩)
      · by_cases hl : mTagOf h = mTagLam
        · cases hv : s.viewLam h with
          | none => simp only [denoteMAux, if_neg hb, if_neg ha, if_pos hl, hv] at hd; simp at hd
          | some p =>
            obtain ⟨a, b⟩ := p
            rw [dm_lam m hv, opt2_eq_some_iff] at hd
            obtain ⟨x, y, hx, hy, he⟩ := hd
            exact Or.inr (Or.inr ⟨m, a, b, x, y, rfl, rfl, he.symm, hx, hy⟩)
        · simp only [denoteMAux, if_neg hb, if_neg ha, if_neg hl] at hd; simp at hd

/-- con-leche: ConLeche/Kernel/Expr.lean:344 Expr — more fuel never loses an
answer. -/
theorem denoteMAux_mono (s : MState) :
    ∀ (n m h : Nat) (e : Expr), denoteMAux s n h = some e → n ≤ m →
      denoteMAux s m h = some e := by
  intro n
  induction n with
  | zero => intro m h e hd _; simp [denoteMAux] at hd
  | succ n ih =>
    intro m h e hd hnm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hnm' : n ≤ m' := by omega
    rcases dm_inv (n + 1) hd with ⟨k, i, hk, hv, he⟩ | ⟨k, a, b, ea, eb, hk, hv, he, hx, hy⟩ |
      ⟨k, a, b, ea, eb, hk, hv, he, hx, hy⟩
    · rw [dm_bvar m' hv, he]
    · cases hk
      rw [dm_app m' hv, opt2_eq_some_iff]
      exact ⟨ea, eb, ih m' a ea hx hnm', ih m' b eb hy hnm', he.symm⟩
    · cases hk
      rw [dm_lam m' hv, opt2_eq_some_iff]
      exact ⟨ea, eb, ih m' a ea hx hnm', ih m' b eb hy hnm', he.symm⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:344 Expr — **the readback
relation**. -/
def DenotesM (s : MState) (h : Nat) (e : Expr) : Prop := ∃ n, denoteMAux s n h = some e

/-- con-leche: none — the readback is single-valued.  This replaces
`Option.some.inj` everywhere `Specs.lean` uses it. -/
theorem DenotesM.uniq {s : MState} {h : Nat} {e e' : Expr}
    (h1 : DenotesM s h e) (h2 : DenotesM s h e') : e = e' := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have a1 := denoteMAux_mono s n (max n m) h e hn (Nat.le_max_left _ _)
  have a2 := denoteMAux_mono s m (max n m) h e' hm (Nat.le_max_right _ _)
  rw [a1] at a2
  exact Option.some.inj a2

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — a denotation survives
every arena extension. -/
theorem DenotesM.ext {s s' : MState} {h : Nat} {e : Expr}
    (hd : DenotesM s h e) (hx : MExt s s') : DenotesM s' h e := by
  obtain ⟨n, hn⟩ := hd
  refine ⟨n, ?_⟩
  induction n generalizing h e with
  | zero => simp [denoteMAux] at hn
  | succ n ih =>
    rcases dm_inv (n + 1) hn with ⟨k, i, hk, hv, he⟩ | ⟨k, a, b, ea, eb, hk, hv, he, hxx, hyy⟩ |
      ⟨k, a, b, ea, eb, hk, hv, he, hxx, hyy⟩
    · rw [dm_bvar n (hx.viewBvar hv), he]
    · cases hk
      rw [dm_app n (hx.viewApp hv), opt2_eq_some_iff]
      exact ⟨ea, eb, ih hxx, ih hyy, he.symm⟩
    · cases hk
      rw [dm_lam n (hx.viewLam hv), opt2_eq_some_iff]
      exact ⟨ea, eb, ih hxx, ih hyy, he.symm⟩

/-! ## The three introductions and the three inversions

`Specs.lean`'s groups 3 and 5 at three constructors.  The relational
denotation gives both directions from one `dm_inv`. -/

theorem DenotesM.bvar {s : MState} {h i : Nat} (hv : s.viewBvar h = some i) :
    DenotesM s h (.bvar i) := ⟨1, dm_bvar 0 hv⟩

theorem DenotesM.app {s : MState} {h a b : Nat} {ea eb : Expr}
    (hv : s.viewApp h = some (a, b)) (ha : DenotesM s a ea) (hb : DenotesM s b eb) :
    DenotesM s h (.app ea eb) := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨max n m + 1, ?_⟩
  rw [dm_app _ hv, opt2_eq_some_iff]
  exact ⟨ea, eb, denoteMAux_mono s n _ a ea hn (Nat.le_max_left _ _),
    denoteMAux_mono s m _ b eb hm (Nat.le_max_right _ _), rfl⟩

theorem DenotesM.lam {s : MState} {h a b : Nat} {ea eb : Expr}
    (hv : s.viewLam h = some (a, b)) (ha : DenotesM s a ea) (hb : DenotesM s b eb) :
    DenotesM s h (.lam ea eb default) := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨max n m + 1, ?_⟩
  rw [dm_lam _ hv, opt2_eq_some_iff]
  exact ⟨ea, eb, denoteMAux_mono s n _ a ea hn (Nat.le_max_left _ _),
    denoteMAux_mono s m _ b eb hm (Nat.le_max_right _ _), rfl⟩

theorem DenotesM.bvar_inv {s : MState} {h i : Nat} {e : Expr}
    (hv : s.viewBvar h = some i) (hd : DenotesM s h e) : e = .bvar i :=
  hd.uniq (DenotesM.bvar hv)

theorem DenotesM.app_inv {s : MState} {h a b : Nat} {e : Expr}
    (hv : s.viewApp h = some (a, b)) (hd : DenotesM s h e) :
    ∃ ea eb, e = .app ea eb ∧ DenotesM s a ea ∧ DenotesM s b eb := by
  obtain ⟨n, hn⟩ := hd
  rcases dm_inv n hn with ⟨k, i, hk, hv2, _⟩ | ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩ |
    ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩
  · exact absurd ((viewApp_tag hv).symm.trans (viewBvar_tag hv2)) tag_bvar_ne_app
  · rw [hv] at hv2
    have hp := Option.some.inj hv2
    have h1 : a = a' := congrArg Prod.fst hp
    have h2 : b = b' := congrArg Prod.snd hp
    subst h1; subst h2
    exact ⟨ea, eb, he, ⟨k, hx⟩, ⟨k, hy⟩⟩
  · exact absurd ((viewLam_tag hv2).symm.trans (viewApp_tag hv)) tag_app_ne_lam

theorem DenotesM.lam_inv {s : MState} {h a b : Nat} {e : Expr}
    (hv : s.viewLam h = some (a, b)) (hd : DenotesM s h e) :
    ∃ ea eb, e = .lam ea eb default ∧ DenotesM s a ea ∧ DenotesM s b eb := by
  obtain ⟨n, hn⟩ := hd
  rcases dm_inv n hn with ⟨k, i, hk, hv2, _⟩ | ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩ |
    ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩
  · exact absurd ((viewLam_tag hv).symm.trans (viewBvar_tag hv2)) tag_bvar_ne_lam
  · exact absurd ((viewLam_tag hv).symm.trans (viewApp_tag hv2)) tag_app_ne_lam
  · rw [hv] at hv2
    have hp := Option.some.inj hv2
    have h1 : a = a' := congrArg Prod.fst hp
    have h2 : b = b' := congrArg Prod.snd hp
    subst h1; subst h2
    exact ⟨ea, eb, he, ⟨k, hx⟩, ⟨k, hy⟩⟩

/-! ## The handle arithmetic, and the cons tables

`mFindApp` returns `mMk mTagApp j`, and `mTagOf (mMk mTagApp j) = mTagApp`
only below `mIdxCap` — which is why the denotation half needs `MWF` too. -/

theorem mk_tag (t j : Nat) (hj : j < mIdxCap) : mTagOf (mMk t j) = t := by
  simp only [mTagOf, mMk, mIdxCap] at hj ⊢
  omega

theorem mk_idx (t j : Nat) (hj : j < mIdxCap) : mIdxOf (mMk t j) = j := by
  simp only [mIdxOf, mMk, mIdxCap] at hj ⊢
  omega

theorem listFindIdx_spec {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (k : α) (i j : Nat), listFindIdx l k i = some j →
      i ≤ j ∧ l[j - i]? = some k := by
  intro l
  induction l with
  | nil => intro k i j h; simp [listFindIdx] at h
  | cons x rest ih =>
    intro k i j h
    simp only [listFindIdx] at h
    split at h
    · rename_i hb
      have : j = i := by simpa using h.symm
      subst this
      exact ⟨Nat.le_refl _, by simp [eq_of_beq hb]⟩
    · obtain ⟨h1, h2⟩ := ih k (i + 1) j h
      refine ⟨by omega, ?_⟩
      have : j - i = (j - (i + 1)) + 1 := by omega
      rw [this]
      simpa using h2

theorem mFindBvar_view {s : MState} (hwf : MWF s) {k r : Nat}
    (h : mFindBvar s k = some r) : s.viewBvar r = some k := by
  simp only [mFindBvar, Option.map_eq_some_iff] at h
  obtain ⟨j, hj, rfl⟩ := h
  obtain ⟨_, h2⟩ := listFindIdx_spec s.bvars k 0 j hj
  simp only [Nat.sub_zero] at h2
  have hjl : j < s.bvars.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h2; exact hlt
  have hjc : j < mIdxCap := by have := hwf.bvars; omega
  simp only [MState.viewBvar, mk_tag _ _ hjc, mk_idx _ _ hjc]
  exact h2

theorem mFindApp_view {s : MState} (hwf : MWF s) {f a r : Nat}
    (h : mFindApp s f a = some r) : s.viewApp r = some (f, a) := by
  simp only [mFindApp, Option.map_eq_some_iff] at h
  obtain ⟨j, hj, rfl⟩ := h
  obtain ⟨_, h2⟩ := listFindIdx_spec s.apps (f, a) 0 j hj
  simp only [Nat.sub_zero] at h2
  have hjl : j < s.apps.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h2; exact hlt
  have hjc : j < mIdxCap := by have := hwf.apps; omega
  simp only [MState.viewApp, mk_tag _ _ hjc, mk_idx _ _ hjc]
  exact h2

theorem mFindLam_view {s : MState} (hwf : MWF s) {ty b r : Nat}
    (h : mFindLam s ty b = some r) : s.viewLam r = some (ty, b) := by
  simp only [mFindLam, Option.map_eq_some_iff] at h
  obtain ⟨j, hj, rfl⟩ := h
  obtain ⟨_, h2⟩ := listFindIdx_spec s.lams (ty, b) 0 j hj
  simp only [Nat.sub_zero] at h2
  have hjl : j < s.lams.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h2; exact hlt
  have hjc : j < mIdxCap := by have := hwf.lams; omega
  simp only [MState.viewLam, mk_tag _ _ hjc, mk_idx _ _ hjc]
  exact h2

/-! ## The `@[spec]` layer

DESIGN §8.6's template, verbatim: the precondition is `s = s₀` and nothing
else, the postcondition is `⇓?`, and it names `s₀`. -/

/-- con-leche: ConLeche/Kernel/Core.lean:62 CheckError — a `mfail` never
returns, so under `⇓?` its success barrel is `False`. -/
@[spec] theorem mfail_spec {α : Type} (e : CheckError) :
    ⦃fun _ => ⌜True⌝⦄ (mfail e : MM α) ⦃⇓? _r _s' => ⌜False⌝⦄ := by
  intro _ _; trivial

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — **the one spec that
carries the arena**: a handle whose view is the node, the capacity invariant
kept, the arena only grown, the memo untouched. -/
@[spec] theorem mInternBvar_spec (s₀ : MState) (hwf : MWF s₀) (k : Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ mInternBvar k
    ⦃⇓? r s' => ⌜MWF s' ∧ MExt s₀ s' ∧ s'.memo = s₀.memo ∧ s'.viewBvar r = some k⌝⦄ := by
  mvcgen [mInternBvar]
  case vc1.h_1 =>
    rename_i s hs r hf; subst hs
    exact ⟨hwf, MExt.refl _, rfl, mFindBvar_view hwf hf⟩
  case vc2.h_2.isTrue =>
    rename_i s hs hf hc _ _; subst hs
    simp +zetaDelta only []
    refine ⟨⟨by simp; omega, hwf.apps, hwf.lams⟩,
      ⟨⟨[k], rfl⟩, ⟨[], by simp⟩, ⟨[], by simp⟩⟩, trivial, ?_⟩
    simp only [MState.viewBvar, mk_tag _ _ hc, mk_idx _ _ hc, if_pos]
    simp
  case vc3.h_2.isFalse.success => intro hf; exact hf.elim

@[spec] theorem mInternApp_spec (s₀ : MState) (hwf : MWF s₀) (f a : Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ mInternApp f a
    ⦃⇓? r s' => ⌜MWF s' ∧ MExt s₀ s' ∧ s'.memo = s₀.memo ∧ s'.viewApp r = some (f, a)⌝⦄ := by
  mvcgen [mInternApp]
  case vc1.h_1 =>
    rename_i s hs r hf; subst hs
    exact ⟨hwf, MExt.refl _, rfl, mFindApp_view hwf hf⟩
  case vc2.h_2.isTrue =>
    rename_i s hs hf hc _ _; subst hs
    simp +zetaDelta only []
    refine ⟨⟨hwf.bvars, by simp; omega, hwf.lams⟩,
      ⟨⟨[], by simp⟩, ⟨[(f, a)], rfl⟩, ⟨[], by simp⟩⟩, trivial, ?_⟩
    simp only [MState.viewApp, mk_tag _ _ hc, mk_idx _ _ hc, if_pos]
    simp
  case vc3.h_2.isFalse.success => intro hf; exact hf.elim

@[spec] theorem mInternLam_spec (s₀ : MState) (hwf : MWF s₀) (ty b : Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ mInternLam ty b
    ⦃⇓? r s' => ⌜MWF s' ∧ MExt s₀ s' ∧ s'.memo = s₀.memo ∧ s'.viewLam r = some (ty, b)⌝⦄ := by
  mvcgen [mInternLam]
  case vc1.h_1 =>
    rename_i s hs r hf; subst hs
    exact ⟨hwf, MExt.refl _, rfl, mFindLam_view hwf hf⟩
  case vc2.h_2.isTrue =>
    rename_i s hs hf hc _ _; subst hs
    simp +zetaDelta only []
    refine ⟨⟨hwf.bvars, hwf.apps, by simp; omega⟩,
      ⟨⟨[], by simp⟩, ⟨[], by simp⟩, ⟨[(ty, b)], rfl⟩⟩, trivial, ?_⟩
    simp only [MState.viewLam, mk_tag _ _ hc, mk_idx _ _ hc, if_pos]
    simp
  case vc3.h_2.isFalse.success => intro hf; exact hf.elim


/-! ## The answer relation and the memo invariant

`Specs.lean`'s groups 6, 7 and 8, at three constructors.  The precondition
"this handle denotes" is `DenotesSome` — `Specs.lean` spells it
`(denoteE st c).isSome = true`, and the point (round 1's rule 4) is the same:
no metavariable in a recursive call's side goal. -/

/-- con-leche: none — "this handle reads back as something". -/
def DenotesSome (s : MState) (c : Nat) : Prop := ∃ e, DenotesM s c e

@[grind →] theorem DenotesSome.ext {s s' : MState} {c : Nat}
    (hd : DenotesSome s c) (hx : MExt s s') : DenotesSome s' c :=
  ⟨hd.choose, hd.choose_spec.ext hx⟩

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — "`r` in `s'` is what
`instantiate1` makes of `c` in `s`, at cursor `d`". -/
def Inst1AtM (ve : Expr) (d : Nat) (s : MState) (c : Nat) (s' : MState) (r : Nat) : Prop :=
  ∀ e, DenotesM s c e → DenotesM s' r (e.instantiate1 ve d)

@[grind →] theorem Inst1AtM.apply {ve : Expr} {d : Nat} {s s' : MState} {c r : Nat}
    {e : Expr} (h : Inst1AtM ve d s c s' r) (he : DenotesM s c e) :
    DenotesM s' r (e.instantiate1 ve d) := h e he

@[grind →] theorem Inst1AtM.denotes {ve : Expr} {d : Nat} {s s' : MState} {c r : Nat}
    (h : Inst1AtM ve d s c s' r) (hs : DenotesSome s c) : DenotesSome s' r :=
  ⟨_, h hs.choose hs.choose_spec⟩

/-- con-leche: none — the answer travels forward with the arena. -/
@[grind →] theorem Inst1AtM.ext {ve : Expr} {d : Nat} {s s' s'' : MState} {c r : Nat}
    (h : Inst1AtM ve d s c s' r) (hx : MExt s' s'') : Inst1AtM ve d s c s'' r :=
  fun e he => (h e he).ext hx

/-- con-leche: none — and backward along an extension of the *source*. -/
@[grind →] theorem Inst1AtM.of_ext {ve : Expr} {d : Nat} {s s0 s' : MState} {c r : Nat}
    (h : Inst1AtM ve d s c s' r) (hx : MExt s0 s) : Inst1AtM ve d s0 c s' r :=
  fun e he => h e (he.ext hx)

/-- con-leche: none — **retarget the source store**: the answer relation was
established against the store the call started in, and the memo records it
against the store the call ended in.  `Specs.lean`'s `Inst1At.retarget`. -/
@[grind →] theorem Inst1AtM.retarget {ve : Expr} {d : Nat} {s s0 s' : MState} {c r : Nat}
    (h : Inst1AtM ve d s c s' r) (hx : MExt s s0) (hs : DenotesSome s c) :
    Inst1AtM ve d s0 c s' r := by
  intro e he
  obtain ⟨e0, he0⟩ := hs
  have heq := (he0.ext hx).uniq he
  subst heq
  exact h e0 he0

/-! ## The per-site step lemmas

One per constructor that recurses, with the hypotheses in the shape `mvcgen`
actually produces — the children's answers against the store each call
started in, the extension chain spelled out.  Round 1's §4.1 group 7. -/

theorem Inst1AtM.app_step {ve : Expr} {d : Nat} {s s1 s2 s3 : MState}
    {h f a rf ra r : Nat} (hview : s.viewApp h = some (f, a))
    (hx1 : MExt s s1) (hf : Inst1AtM ve d s f s1 rf)
    (hx2 : MExt s1 s2) (ha : Inst1AtM ve d s1 a s2 ra)
    (hx3 : MExt s2 s3) (hr : s3.viewApp r = some (rf, ra)) :
    Inst1AtM ve d s h s3 r := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := DenotesM.app_inv hview he
  have h1 : DenotesM s3 rf (ef.instantiate1 ve d) := ((hf ef hdf).ext hx2).ext hx3
  have h2 : DenotesM s3 ra (ea.instantiate1 ve d) := ((ha ea (hda.ext hx1)).ext hx3)
  have hd3 := DenotesM.app hr h1 h2
  exact hd3

theorem Inst1AtM.lam_step {ve : Expr} {d : Nat} {s s1 s2 s3 : MState}
    {h ty b rt rb r : Nat} (hview : s.viewLam h = some (ty, b))
    (hx1 : MExt s s1) (ht : Inst1AtM ve d s ty s1 rt)
    (hx2 : MExt s1 s2) (hb : Inst1AtM ve (d + 1) s1 b s2 rb)
    (hx3 : MExt s2 s3) (hr : s3.viewLam r = some (rt, rb)) :
    Inst1AtM ve d s h s3 r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := DenotesM.lam_inv hview he
  have h1 : DenotesM s3 rt (et.instantiate1 ve d) := ((ht et hdt).ext hx2).ext hx3
  have h2 : DenotesM s3 rb (eb.instantiate1 ve (d + 1)) := ((hb eb (hdb.ext hx1)).ext hx3)
  have hd3 := DenotesM.lam hr h1 h2
  exact hd3

/-! ## The memo

Round 1's rule 6: **a memo insert's spec states that the invariant is
preserved, not that the table grew.**  The invariant is over *membership*
rather than over `mMemoGet`, which makes the insert case `List.mem_append`
instead of a `listFindIdx`-on-append lemma — one of round 2's small
simplifications over `Specs.lean`'s `Std.HashMap` version. -/

/-- con-leche: none — the denotation does not look at the memo. -/
theorem denoteMAux_congr {s s' : MState} (h1 : s'.bvars = s.bvars) (h2 : s'.apps = s.apps)
    (h3 : s'.lams = s.lams) : ∀ (n h : Nat), denoteMAux s' n h = denoteMAux s n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [denoteMAux, MState.viewBvar, MState.viewApp, MState.viewLam, h1, h2, h3, ih]

theorem DenotesM.congr {s s' : MState} (h1 : s'.bvars = s.bvars) (h2 : s'.apps = s.apps)
    (h3 : s'.lams = s.lams) {h : Nat} {e : Expr} (hd : DenotesM s h e) : DenotesM s' h e := by
  obtain ⟨n, hn⟩ := hd
  exact ⟨n, by rw [denoteMAux_congr h1 h2 h3]; exact hn⟩

/-- con-leche: none — the probe returns a recorded entry. -/
theorem mMemoGet_mem {s : MState} {h d r : Nat} (hg : mMemoGet s h d = some r) :
    (h, d, r) ∈ s.memo := by
  simp only [mMemoGet] at hg
  split at hg
  · simp at hg
  · rename_i j hj
    obtain ⟨_, h2⟩ :=
      listFindIdx_spec (s.memo.map (fun e => (e.1, e.2.1))) (h, d) 0 j hj
    simp only [Nat.sub_zero, List.getElem?_map, Option.map_eq_some_iff] at h2
    obtain ⟨x, hx, hkey⟩ := h2
    rw [hx] at hg
    simp only [Option.map_some, Option.some.injEq] at hg
    obtain ⟨a, b, c⟩ := x
    simp only [Prod.mk.injEq] at hkey hg
    subst hg
    obtain ⟨e1, e2⟩ := hkey
    subst e1; subst e2
    exact List.mem_of_getElem? hx

/-- con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — the memo's
invariant, transported through the readback relation. -/
def Inst1MemoM (ve : Expr) (s : MState) : Prop :=
  ∀ h d r, (h, d, r) ∈ s.memo → ∃ e, DenotesM s h e ∧ DenotesM s r (e.instantiate1 ve d)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — **the memo
hit**: a recorded entry *is* the answer. -/
@[grind →] theorem Inst1MemoM.get {ve : Expr} {s : MState} {h d r : Nat}
    (hm : Inst1MemoM ve s) (hg : mMemoGet s h d = some r) : Inst1AtM ve d s h s r := by
  intro e he
  obtain ⟨e', h1, h2⟩ := hm h d r (mMemoGet_mem hg)
  have heq := h1.uniq he
  subst heq
  exact h2

/-- con-leche: none — the memo survives an arena extension that leaves the
table alone. -/
theorem Inst1MemoM.mono {ve : Expr} {s s' : MState} (hm : Inst1MemoM ve s)
    (hx : MExt s s') (hc : s'.memo = s.memo) : Inst1MemoM ve s' := by
  intro h d r hmem
  rw [hc] at hmem
  obtain ⟨e, h1, h2⟩ := hm h d r hmem
  exact ⟨e, h1.ext hx, h2.ext hx⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:69 Inst1MemoInv.insert — the
insert, in the invariant-carrying shape. -/
theorem Inst1MemoM.insert {ve : Expr} {s : MState} {h d r : Nat}
    (hm : Inst1MemoM ve s) (hk : DenotesSome s h) (hr : Inst1AtM ve d s h s r) :
    Inst1MemoM ve { s with memo := s.memo ++ [(h, d, r)] } := by
  intro h' d' r' hmem
  have hc1 : ({ s with memo := s.memo ++ [(h, d, r)] } : MState).bvars = s.bvars := rfl
  have hc2 : ({ s with memo := s.memo ++ [(h, d, r)] } : MState).apps = s.apps := rfl
  have hc3 : ({ s with memo := s.memo ++ [(h, d, r)] } : MState).lams = s.lams := rfl
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | heq
  · obtain ⟨e, h1, h2⟩ := hm h' d' r' hmem
    exact ⟨e, h1.congr hc1 hc2 hc3, h2.congr hc1 hc2 hc3⟩
  · obtain ⟨rfl, rfl, rfl⟩ : h' = h ∧ d' = d ∧ r' = r := by
      simp only [Prod.mk.injEq] at heq; exact ⟨heq.1, heq.2.1, heq.2.2⟩
    obtain ⟨e, he⟩ := hk
    exact ⟨e, he.congr hc1 hc2 hc3, (hr e he).congr hc1 hc2 hc3⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go — **the memo
insert's spec**: the invariant is preserved, and the caller's obligations
(the key denotes, the value is the answer) are side goals the caller has. -/
@[spec] theorem mMemoSet_spec (s₀ : MState) (ve : Expr) (hwf : MWF s₀)
    (hm : Inst1MemoM ve s₀) (h d r : Nat) (hk : DenotesSome s₀ h)
    (hr : Inst1AtM ve d s₀ h s₀ r) :
    ⦃fun s => ⌜s = s₀⌝⦄ mMemoSet h d r
    ⦃⇓? _u s' => ⌜MWF s' ∧ MExt s₀ s' ∧ Inst1MemoM ve s'⌝⦄ := by
  mvcgen [mMemoSet]
  rename_i s hs _ _
  subst hs
  simp +zetaDelta only []
  exact ⟨⟨hwf.bvars, hwf.apps, hwf.lams⟩,
    ⟨⟨[], by simp⟩, ⟨[], by simp⟩, ⟨[], by simp⟩⟩,
    Inst1MemoM.insert hm hk hr⟩

/-! ## The three `bvar` sites

`Specs.lean` has ten per-site step lemmas because the real store has ten
constructors; the mini arena's `bvar` arm has three *sites* (hit, shift,
below the cursor) and they are the only place `Expr.instantiate1` is
unfolded.  Keeping them out of `grind`'s hint list and behind a named lemma
is round 1's rule 5 and round 2's elaboration finding in one. -/

theorem Inst1AtM.bvar_hit {ve : Expr} {s : MState} {h d v : Nat}
    (hv : s.viewBvar h = some d) (hvd : DenotesM s v ve) : Inst1AtM ve d s h s v := by
  intro e he
  rw [DenotesM.bvar_inv hv he]
  have hb : (Expr.bvar d).instantiate1 ve d = ve := by simp [Expr.instantiate1]
  rw [hb]
  exact hvd

theorem Inst1AtM.bvar_gt {ve : Expr} {s s' : MState} {h d i r : Nat}
    (hv : s.viewBvar h = some i) (hgt : d < i) (hr : s'.viewBvar r = some (i - 1)) :
    Inst1AtM ve d s h s' r := by
  intro e he
  rw [DenotesM.bvar_inv hv he]
  have hb : (Expr.bvar i).instantiate1 ve d = Expr.bvar (i - 1) := by
    simp only [Expr.instantiate1, if_neg (show ¬ i = d by omega), if_pos (show i > d by omega)]
  rw [hb]
  exact DenotesM.bvar hr

theorem Inst1AtM.bvar_le {ve : Expr} {s : MState} {h d i : Nat}
    (hv : s.viewBvar h = some i) (hne : ¬ i = d) (hle : ¬ d < i) :
    Inst1AtM ve d s h s h := by
  intro e he
  rw [DenotesM.bvar_inv hv he]
  have hb : (Expr.bvar i).instantiate1 ve d = Expr.bvar i := by
    simp only [Expr.instantiate1, if_neg hne, if_neg (show ¬ i > d by omega)]
  rw [hb]
  exact DenotesM.bvar hv

/-! ## The `DenotesSome` calculus

`Specs.lean`'s group 4 (`isSome_app`, `isSome_lam`, …) at three
constructors: push "this handle denotes" down a node, so that a recursive
call's precondition is discharged without a metavariable. -/

@[grind →] theorem DenotesSome.of_app {s : MState} {h a b : Nat}
    (hv : s.viewApp h = some (a, b)) (hs : DenotesSome s h) :
    DenotesSome s a ∧ DenotesSome s b := by
  obtain ⟨e, he⟩ := hs
  obtain ⟨ea, eb, _, ha, hb⟩ := DenotesM.app_inv hv he
  exact ⟨⟨ea, ha⟩, ⟨eb, hb⟩⟩

@[grind →] theorem DenotesSome.of_lam {s : MState} {h a b : Nat}
    (hv : s.viewLam h = some (a, b)) (hs : DenotesSome s h) :
    DenotesSome s a ∧ DenotesSome s b := by
  obtain ⟨e, he⟩ := hs
  obtain ⟨ea, eb, _, ha, hb⟩ := DenotesM.lam_inv hv he
  exact ⟨⟨ea, ha⟩, ⟨eb, hb⟩⟩
