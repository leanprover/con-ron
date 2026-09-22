/-
# `ConRon.Bridge.Promote.Pers` — the PERSISTENT extension, and what survives a drop

DESIGN.md §8.2 states Theorem 1's second conjunct as `Ext st st'`.  **At the
per-declaration STEP that conjunct is false as written**, and this module is
the correction (task #97-P3-Checker, finding 1).

`Ext st st'` (`Arena/Denote.lean:274`) is TOTAL: *every* handle of `st`
denotes the same in `st'`.  `Arena/Checker.lean`'s `checkDeclStep` ends in
`dropScratch`, which takes the scratch tier away, and `Arena/WFProofs.lean`'s
own `dropScratch_spec` says exactly what then happens to a scratch handle:
`denoteE st.dropScratch i = none`.  So a bracketed step CANNOT deliver `Ext`,
and the conjunct it does deliver — the one the fold actually needs, and the
one that is the tier discipline in a line — is

    PExt st st' :  every PERSISTENT handle that denotes in `st`
                   denotes the same in `st'`

`Ext` implies it, `PExt` composes, and `dropScratch` preserves it.  Everything
the fold carries across a step boundary — the environment, the pending
records, the pin table — is persistent by construction (that is what
`Arena/Promote.lean` exists for), so `PExt` transports all of it.

The second half of the module is the vocabulary for "by construction":
`PersE` and its siblings at the four handle kinds, lifted to the declaration
layer (`PersCV`, `PersCI`, `PersDecl`, `PersVG`, `PersIFEnv`, `PersPins`).  A
`Pers…` predicate is decided by the handles' tier bits alone — it says nothing
about any store — which is what lets `Arena/Promote.lean`'s theorems establish
it and the fold consume it without either mentioning the other's store.
-/
import ConRon.Bridge.StateOK

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## Running an `AM` do-block

The bind's inversion, at the bottom of the tier: every run-form proof of
`Bridge/Checker/**` and `Bridge/Promote/**` starts with it, and after it no
proof in either directory mentions `StateT`. -/

/-- con-leche: none — the `AM` bind, applied. -/
theorem AM.bind_apply {α β : Type} (x : AM α) (f : α → AM β) (s : AState) :
    (x >>= f) s = (x s) >>= (fun p => f p.1 p.2) := rfl

/-- con-leche: none — the `AM` bind's inversion: an accepting composite is two
accepting halves. -/
theorem AM.bind_ok {α β : Type} {x : AM α} {f : α → AM β} {s s' : AState}
    {b : β} (h : (x >>= f) s = .ok (b, s')) :
    ∃ a s₁, x s = .ok (a, s₁) ∧ f a s₁ = .ok (b, s') := by
  rw [AM.bind_apply] at h
  revert h
  cases hx : x s with
  | error e => intro h; exact nomatch h
  | ok p =>
    obtain ⟨a, s₁⟩ := p
    intro h
    exact ⟨a, s₁, rfl, h⟩

/-- con-leche: none — `fail` as an equation: the error arm of `AM` carries no
state, so a `fail` is the error and nothing else. -/
theorem fail_apply {α : Type} (e : Arena.CheckError) (s : AState) :
    (fail e : AM α) s = .error e := rfl

/-- con-leche: none — **a program that cannot succeed**.  Every guard body of
a `checkConstantVal`-shaped front door is one: the error message is computed
from a readback (`s!"… {← readName n}"`), so the body is a chain of binds
ending in `fail`, and what the bridge needs to know about it is exactly this.

Reading a front door backwards is then one lemma per guard: an accepting run
took the branch that is not `Never`. -/
def AM.Never {α : Type} (x : AM α) : Prop :=
  ∀ (s : AState) (a : α) (s' : AState), x s ≠ .ok (a, s')

theorem AM.Never.fail {α : Type} (e : Arena.CheckError) :
    AM.Never (fail e : AM α) := by
  intro s a s' h; rw [fail_apply] at h; exact nomatch h

theorem AM.Never.bind {α β : Type} {x : AM α} {g : α → AM β}
    (h : ∀ a, AM.Never (g a)) : AM.Never (x >>= g) := by
  intro s b s' hb
  obtain ⟨a, s₁, _, h2⟩ := AM.bind_ok hb
  exact h a s₁ b s' h2

/-- con-leche: none — the guard bodies of the declaration checker, as a
non-equation: `readName n >>= fun x => fail (… x)` cannot succeed.  It is what
every `absurd` in `Bridge/Checker/Arms.lean` takes. -/
theorem AM.readFail_ne {α β : Type} {x : AM α} {f : α → Arena.CheckError}
    {s s' : AState} {b : β} :
    (x >>= fun a => (Arena.fail (f a) : AM β)) s ≠ .ok (b, s') :=
  (AM.Never.bind fun _ => AM.Never.fail _) s b s'

/-- con-leche: none — an `if` in `AM`, inverted. -/
theorem AM.ite_ok {α : Type} {c : Prop} [Decidable c] {X Y : AM α}
    {s s' : AState} {a : α} (h : (if c then X else Y) s = .ok (a, s')) :
    (c ∧ X s = .ok (a, s')) ∨ (¬ c ∧ Y s = .ok (a, s')) := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h; exact Or.inr ⟨hc, h⟩

/-- con-leche: none — `pure` in `AM`, inverted. -/
theorem AM.pure_ok {α : Type} {a b : α} {s s' : AState}
    (h : (pure a : AM α) s = .ok (b, s')) : b = a ∧ s' = s := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- con-leche: none — a bind whose FIRST half cannot succeed cannot succeed. -/
theorem AM.Never.of_bind_left {α β : Type} {x : AM α} {g : α → AM β}
    (h : AM.Never x) : AM.Never (x >>= g) := by
  intro s b s' hb
  obtain ⟨a, s1, h1, _⟩ := AM.bind_ok hb
  exact h s a s1 h1

/-- con-leche: none — a block that starts with `fail` cannot succeed, whatever
follows it.  This is the shape every guard body of a do-block has, because
Lean's `do` elaborator copies the CONTINUATION into both arms of an
`if`/`unless` that does not return. -/
theorem AM.Never.fail_any {α β : Type} {e : Arena.CheckError} {g : α → AM β} :
    AM.Never ((Arena.fail e : AM α) >>= g) :=
  AM.Never.of_bind_left (AM.Never.fail e)

/-- con-leche: none — **`if c then <a failing block>` (a do-block guard with
no `else`), inverted.**  Lean's `do` elaborator copies the continuation into
both arms, so the `then` arm is "the failure, then the rest" and the `else`
arm is "`pure ()`, then the rest": an accepting run means the guard was false,
and what is left to read is the `else` arm. -/
theorem AM.dguard_ok {α : Type} {c : Prop} [Decidable c] {X Y : AM α}
    {s s' : AState} {a : α} (hX : AM.Never X)
    (h : (if c then X else Y) s = .ok (a, s')) : ¬ c ∧ Y s = .ok (a, s') := by
  rcases AM.ite_ok h with ⟨_, hbad⟩ | ⟨hc, hgood⟩
  · exact absurd hbad (hX s a s')
  · exact ⟨hc, hgood⟩

/-- con-leche: none — **`unless c do <a failing block>`, inverted**: the same
at the other arm. -/
theorem AM.dunless_ok {α : Type} {c : Prop} [Decidable c] {X Y : AM α}
    {s s' : AState} {a : α} (hX : AM.Never X)
    (h : (if c then Y else X) s = .ok (a, s')) : c ∧ Y s = .ok (a, s') := by
  rcases AM.ite_ok h with ⟨hc, hgood⟩ | ⟨_, hbad⟩
  · exact ⟨hc, hgood⟩
  · exact absurd hbad (hX s a s')

/-- con-leche: none — a leading `pure` in a do-block is transparent. -/
theorem AM.pure_bind_ok {α β : Type} {a : α} {g : α → AM β} {s s' : AState}
    {b : β} (h : ((pure a : AM α) >>= g) s = .ok (b, s')) :
    g a s = .ok (b, s') := h

/-! ## The persistent extension -/

/-- con-leche: none — `NExt` restricted to persistent handles. -/
def PNExt (st st' : NStore) : Prop :=
  ∀ i n, i.isPersistent = true → denoteN st i = some n → denoteN st' i = some n

/-- con-leche: none — `LExt` restricted to persistent handles. -/
structure PLExt (st st' : LStore) : Prop where
  ns : PNExt st.ns st'.ns
  lvl : ∀ i u, i.isPersistent = true → denoteL st i = some u → denoteL st' i = some u

/-- con-leche: none — `LsExt` restricted to persistent handles. -/
structure PLsExt (st st' : LsStore) : Prop where
  ls : PLExt st.ls st'.ls
  lst : ∀ i us, i.isPersistent = true → denoteLs st i = some us →
    denoteLs st' i = some us

/-- con-leche: none — **the tier discipline in one relation** (DESIGN §8.2,
corrected): every PERSISTENT handle of `st` denotes the same in `st'`.  This
is what a bracketed fold step delivers where §8.2 writes `Ext`; `Ext` is an
unbracketed call's conjunct and implies this one. -/
structure PExt (st st' : EStore) : Prop where
  lss : PLsExt st.lss st'.lss
  expr : ∀ i e, i.isPersistent = true → denoteE st i = some e →
    denoteE st' i = some e

theorem PNExt.refl (st : NStore) : PNExt st st := fun _ _ _ h => h
theorem PLExt.refl (st : LStore) : PLExt st st := ⟨PNExt.refl _, fun _ _ _ h => h⟩
theorem PLsExt.refl (st : LsStore) : PLsExt st st :=
  ⟨PLExt.refl _, fun _ _ _ h => h⟩
theorem PExt.refl (st : EStore) : PExt st st := ⟨PLsExt.refl _, fun _ _ _ h => h⟩

theorem PNExt.trans {a b c : NStore} (h₁ : PNExt a b) (h₂ : PNExt b c) :
    PNExt a c := fun i n hp h => h₂ i n hp (h₁ i n hp h)

theorem PLExt.trans {a b c : LStore} (h₁ : PLExt a b) (h₂ : PLExt b c) :
    PLExt a c :=
  ⟨h₁.ns.trans h₂.ns, fun i u hp h => h₂.lvl i u hp (h₁.lvl i u hp h)⟩

theorem PLsExt.trans {a b c : LsStore} (h₁ : PLsExt a b) (h₂ : PLsExt b c) :
    PLsExt a c :=
  ⟨h₁.ls.trans h₂.ls, fun i us hp h => h₂.lst i us hp (h₁.lst i us hp h)⟩

theorem PExt.trans {a b c : EStore} (h₁ : PExt a b) (h₂ : PExt b c) : PExt a c :=
  ⟨h₁.lss.trans h₂.lss, fun i e hp h => h₂.expr i e hp (h₁.expr i e hp h)⟩

/-! ### `Ext` implies it

The unbracketed direction: an `intern`, a walk, a whole `checkDecl` — none of
them drops a tier, so each delivers the total `Ext`, and every consumer below
takes the restricted one. -/

theorem PNExt.of_ext {a b : NStore} (h : NExt a b) : PNExt a b :=
  fun i n _ hd => h i n hd

theorem PLExt.of_ext {a b : LStore} (h : LExt a b) : PLExt a b :=
  ⟨PNExt.of_ext h.ns, fun i u _ hd => h.lvl i u hd⟩

theorem PLsExt.of_ext {a b : LsStore} (h : LsExt a b) : PLsExt a b :=
  ⟨PLExt.of_ext h.ls, fun i us _ hd => h.lst i us hd⟩

/-- con-leche: none — the total extension implies the restricted one. -/
theorem PExt.of_ext {a b : EStore} (h : Ext a b) : PExt a b :=
  ⟨PLsExt.of_ext h.lss, fun i e _ hd => h.expr i e hd⟩

/-! ### The two ends of the bracket see the same store

`enableScratch` and `dropScratch` differ **only** in the `scratchOn` flag they
leave behind — both replace the scratch tier by `empty` — and a store's `view`
cannot tell the difference at ANY handle, persistent or not: a persistent
handle reads the untouched `pers` arrays in both, and a scratch handle reads
`none` in both (`ETables.empty`'s getter on the `enableScratch` side, the flag
being `false` on the `dropScratch` side).  So the two stores' readbacks are
equal FUNCTIONS, which is what `PExt.enterScratch` below stands on.

This is task #97-P3-Checker's item 21, paid here rather than in
`Arena/WFProofs.lean` and paid cheaper than it was priced: **none of the eight
lemmas mentions the well-formedness invariant**, because `view` equality is
decided by the two stores' fields alone and no rank is involved. -/

/-- con-leche: none — the name store's view is the same at both ends of the
bracket. -/
theorem NStore.view_bracket (st : NStore) (i : NIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  simp only [NStore.view, NStore.enableScratch, NStore.dropScratch]
  by_cases hp : i.isPersistent = true
  · simp [hp]
  · simp [hp, NTables.get_empty]

/-- con-leche: none — the level store's view is the same at both ends. -/
theorem LStore.view_bracket (st : LStore) (i : LIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  simp only [LStore.view, LStore.enableScratch, LStore.dropScratch]
  by_cases hp : i.isPersistent = true
  · simp [hp]
  · simp [hp, LTables.get_empty]

/-- con-leche: none — the level-list store's view is the same at both ends. -/
theorem LsStore.view_bracket (st : LsStore) (i : LsIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  simp only [LsStore.view, LsStore.enableScratch, LsStore.dropScratch]
  by_cases hp : i.isPersistent = true
  · simp [hp]
  · simp [hp, LsTables.get_empty]

/-- con-leche: none — the binder datum reads the same at both ends. -/
theorem EStore.viewBM_bracket (st : EStore) (i : BMIdx) :
    st.enableScratch.viewBM i = st.dropScratch.viewBM i := by
  simp only [EStore.viewBM, EStore.enableScratch, EStore.dropScratch,
    EStore.persGetBM]
  by_cases hp : i.isPersistent = true
  · simp [hp]
  · simp [hp, ETables.getBM_empty]

/-- con-leche: none — the expression store's view is the same at both ends;
the two binder tags go through `viewBind`, whose two reads are the lemma above
and `viewBindI`'s own tier select. -/
theorem EStore.view_bracket (st : EStore) (i : EIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  have hbi : st.enableScratch.viewBindI i = st.dropScratch.viewBindI i := by
    simp only [EStore.viewBindI, EStore.enableScratch, EStore.dropScratch,
      EStore.persGetBind]
    by_cases hp : i.isPersistent = true
    · simp [hp]
    · simp [hp, ETables.getBind_empty]
  simp only [EStore.view, EStore.viewBind, hbi, EStore.viewBM_bracket]
  by_cases hb : ETag.isBind i.tag = true
  · simp [hb]
  · simp only [hb, Bool.false_eq_true, if_false]
    simp only [EStore.enableScratch, EStore.dropScratch]
    by_cases hp : i.isPersistent = true
    · simp [hp]
    · simp [hp, ETables.get_empty]

/-- con-leche: none — a name's readback depends on the store only through its
`view`. -/
theorem denoteNAux_store_congr {st st' : NStore}
    (hv : ∀ i, st'.view i = st.view i) :
    ∀ (f : Nat) (i : NIdx), denoteNAux st' f i = denoteNAux st f i := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ k ih => intro i; simp only [denoteNAux, hv i, ih]

/-- con-leche: none — a name reads back the same at both ends of the bracket
(the node counts agree: both tiers' scratch arrays are `empty`). -/
theorem denoteN_bracket (st : NStore) (i : NIdx) :
    denoteN st.enableScratch i = denoteN st.dropScratch i :=
  denoteNAux_store_congr (NStore.view_bracket st) _ i

/-- con-leche: none — a level's readback depends on the store through its
`view` and the name store underneath it. -/
theorem denoteLAux_store_congr {st st' : LStore}
    (hv : ∀ i, st'.view i = st.view i)
    (hn : ∀ i, denoteN st'.ns i = denoteN st.ns i) :
    ∀ (f : Nat) (i : LIdx), denoteLAux st' f i = denoteLAux st f i := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ k ih => intro i; simp only [denoteLAux, hv i, hn, ih]

/-- con-leche: none — a level reads back the same at both ends. -/
theorem denoteL_bracket (st : LStore) (i : LIdx) :
    denoteL st.enableScratch i = denoteL st.dropScratch i :=
  denoteLAux_store_congr (LStore.view_bracket st) (denoteN_bracket st.ns) _ i

/-- con-leche: none — the level-list fold follows its element readback. -/
theorem denoteLList_store_congr {st st' : LStore}
    (hl : ∀ i, denoteL st' i = denoteL st i) :
    ∀ us : List LIdx, denoteLList st' us = denoteLList st us := by
  intro us
  induction us with
  | nil => rfl
  | cons a as ih => simp only [denoteLList, hl a, ih]

/-- con-leche: none — a universe-argument list reads back the same at both
ends. -/
theorem denoteLs_bracket (st : LsStore) (i : LsIdx) :
    denoteLs st.enableScratch i = denoteLs st.dropScratch i := by
  simp only [denoteLs, LsStore.view_bracket st i]
  cases st.dropScratch.view i with
  | none => rfl
  | some us => exact denoteLList_store_congr (denoteL_bracket st.ls) us

/-- con-leche: none — an expression's readback depends on the store through
its `view` and the three stores underneath it. -/
theorem denoteEAux_store_congr {st st' : EStore}
    (hv : ∀ i, st'.view i = st.view i)
    (hn : ∀ i, denoteN st'.ns i = denoteN st.ns i)
    (hl : ∀ i, denoteL st'.ls i = denoteL st.ls i)
    (hls : ∀ i, denoteLs st'.lss i = denoteLs st.lss i) :
    ∀ (f : Nat) (i : EIdx), denoteEAux st' f i = denoteEAux st f i := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ k ih => intro i; simp only [denoteEAux, hv i, hn, hl, hls, ih]

/-- con-leche: none — **an expression reads back the same at both ends of the
bracket**, which is what turns `PExt.dropScratch` into `PExt.enterScratch`. -/
theorem denoteE_bracket (st : EStore) (i : EIdx) :
    denoteE st.enableScratch i = denoteE st.dropScratch i :=
  denoteEAux_store_congr (EStore.view_bracket st) (denoteN_bracket st.ns)
    (denoteL_bracket st.ls) (denoteLs_bracket st.lss) _ i

/-! ### The bracket preserves it

`Arena/WFProofs.lean`'s four `dropScratch_spec`s, assembled. -/

theorem PExt.dropScratch {st : EStore} (h : StoreWF st) :
    PExt st st.dropScratch := by
  have hw : StoreWF st := h
  obtain ⟨rk, hwa⟩ := h
  have hlss : LsStoreWF st.lss := hwa.lss
  have hls : LStoreWF st.lss.ls := hlss.ls
  have hns : NStoreWF st.lss.ls.ns := by
    obtain ⟨rkl, hl⟩ := hls; exact hl.ns
  exact ⟨⟨⟨fun i n hp hd => (NStore.dropScratch_spec hns).2.2 i n hp hd,
      fun i u hp hd => (LStore.dropScratch_spec hls).2.2 i u hp hd⟩,
    fun i us hp hd => (LsStore.dropScratch_spec hlss).2.2 i us hp hd⟩,
    fun i e hp hd => EStore.dropScratch_denote_pers hw hp hd⟩

/-- con-leche: none — **the bracket's OPENING step, and the one-lemma gap in
`Arena/WFProofs.lean`** (task #97-P3-Checker, finding 4).

`enterScratch` turns the scratch tier on.  It changes nothing persistent —
`enableScratch` and `dropScratch` "differ only in the flag they leave behind"
(`WFProofs.lean`'s own section note), both replacing the scratch tier by
`empty` — so a persistent handle keeps its denotation across it, exactly as it
does across a drop.

**But `WFProofs.lean` states that only for `dropScratch`.**  For
`enableScratch` it states the `view` half (`EStore.view_enableScratch_pers`,
`NStore.view_enableScratch_pers`, …) and the scratch half
(`denoteE_enableScratch_scr`) and stops; there is no
`denoteE_enableScratch_pers` to match `denoteE_dropScratch_pers`, and
`EStore.enableScratch_spec`'s three conjuncts are `StoreWF`, `view` and the
scratch handles' `none`.  So the persistent DENOTATION across an
`enterScratch` cannot be assembled from the store layer as it stands, and
`Arena.checkDeclStep_bridge` — whose first two operations are `flushCaches`
and `enterScratch` — stops here.

**CLOSED (task #97-P3-Checker-2), and not the way item 21 expected.**  The
lemma that was asked for — `denote*_enableScratch_pers` beside
`denote*_dropScratch_pers`, i.e. the `dropScratch` argument re-run — is not
needed at all: `enableScratch` and `dropScratch` produce stores whose `view`
agrees at EVERY handle, persistent or not (a persistent handle reads the same
untouched `pers` arrays; a scratch handle reads `none` on both sides, from
`ETables.empty`'s getter on one and from the flag on the other), so the two
readbacks are equal FUNCTIONS and this is `PExt.dropScratch` transported
across that equality.  The eight congruences are the section just above and none
of them mentions the well-formedness invariant, which is why this costs a
tenth of what the item priced. -/
theorem PExt.enterScratch {st : EStore} (h : StoreWF st) :
    PExt st st.enableScratch := by
  have hd := PExt.dropScratch h
  exact
    ⟨⟨⟨fun i n hp hden => (denoteN_bracket st.ns i).trans (hd.lss.ls.ns i n hp hden),
        fun i u hp hden => (denoteL_bracket st.ls i).trans (hd.lss.ls.lvl i u hp hden)⟩,
      fun i us hp hden => (denoteLs_bracket st.lss i).trans (hd.lss.lst i us hp hden)⟩,
    fun i e hp hden => (denoteE_bracket st i).trans (hd.expr i e hp hden)⟩

/-! ## Persistence of a handle, and of everything built out of handles

A `Pers…` predicate looks only at the tier bits, so it is a fact about the
VALUE and not about any store — which is what makes it survive a
`dropScratch` for free and what lets `Arena/Promote.lean` establish it. -/

/-- con-leche: none — a name handle lives in the persistent tier. -/
abbrev PersN (n : NIdx) : Prop := n.isPersistent = true
/-- con-leche: none — a level handle lives in the persistent tier. -/
abbrev PersL (l : LIdx) : Prop := l.isPersistent = true
/-- con-leche: none — a universe-argument list handle is persistent. -/
abbrev PersLs (l : LsIdx) : Prop := l.isPersistent = true
/-- con-leche: none — an expression handle lives in the persistent tier. -/
abbrev PersE (e : EIdx) : Prop := e.isPersistent = true

/-- con-leche: none — every handle of a name list is persistent. -/
def PersNList (ns : List NIdx) : Prop := ∀ n ∈ ns, PersN n
/-- con-leche: none — every handle of an expression list is persistent. -/
def PersEList (es : List EIdx) : Prop := ∀ e ∈ es, PersE e
/-- con-leche: none — every handle of a level list is persistent. -/
def PersLList (us : List LIdx) : Prop := ∀ u ∈ us, PersL u

/-- con-leche: none — a stored constant's header is persistent, field by
field (`Arena/Env.lean`'s `IConstantVal`). -/
structure PersCV (cv : IConstantVal) : Prop where
  name : PersN cv.name
  levelParams : PersNList cv.levelParams
  type : PersE cv.type

/-- con-leche: none — a recursor rule's firing mode is persistent. -/
def PersFire : IRecRuleFire → Prop
  | .inert => True
  | .plain => True
  | .nested lvls pins => PersLList lvls ∧ PersEList pins

/-- con-leche: none — a recursor rule is persistent. -/
structure PersRule (rl : IRecRule) : Prop where
  ctor : PersN rl.ctor
  fire : PersFire rl.fire
  rhs : PersE rl.rhs

/-- con-leche: none — every rule of the list is persistent. -/
def PersRules (rs : List IRecRule) : Prop := ∀ r ∈ rs, PersRule r

/-- con-leche: none — an inductive's capabilities record is persistent (its
one handle field is the eta constructor's name). -/
def PersCaps (c : IIndCaps) : Prop := PersN c.etaCtor

/-- con-leche: none — a projection table is persistent, field by field. -/
structure PersProjTable (t : IProjTable) : Prop where
  structName : PersN t.structName
  tableName : PersN t.tableName
  levelParams : PersNList t.levelParams
  ctor : PersN t.ctor
  structSort : PersL t.structSort
  bodies : PersEList t.bodies.toList
  guards : PersLList t.guards

/-- con-leche: none — **a stored constant is persistent**: the clause
`dropScratch` needs of the environment, and what `Arena/Promote.lean`'s
`promoteCI` delivers. -/
def PersCI : IConstantInfo → Prop
  | .axiomInfo v => PersCV v
  | .defnInfo v e _ => PersCV v ∧ PersE e
  | .thmInfo v e => PersCV v ∧ PersE e
  | .indInfo v c => PersCV v ∧ PersCaps c
  | .ctorInfo v _ _ => PersCV v
  | .recInfo v _ _ rs => PersCV v ∧ PersRules rs
  | .projInfo t => PersProjTable t

/-- con-leche: none — every member of a block is persistent. -/
def PersCIList (cs : List IConstantInfo) : Prop := ∀ c ∈ cs, PersCI c

/-- con-leche: none — every constant of the environment is persistent. -/
def PersIEnv (e : IEnv) : Prop := PersCIList e.consts

/-- con-leche: none — **the environment index is persistent**: both its list
and its rows.  The rows matter as much as the list — `Arena/Promote.lean`'s
`eraseInstalled`/`indexPromoted` exist because a stale row under a SCRATCH key
would answer a different constant once `dropScratch` hands that word back. -/
structure PersIFEnv (fe : IFEnv) : Prop where
  env : PersIEnv fe.env
  idx : ∀ n p, fe.idx[n]? = some p → PersN n ∧ PersCI p.2

/-- con-leche: none — arena infrastructure; **what a lookup in a persistent
index answers is persistent**: `IFEnv.find?` reads the index and nothing else,
so `PersIFEnv`'s row clause covers both the key and the constant.  This is
what makes `IFEnvOK` survive a `dropScratch` (`Bridge/Checker/Inv.lean`'s
`IFEnvOK.pmono`) without a re-derivation from the denotation. -/
theorem PersIFEnv.find {fe : IFEnv} (hp : PersIFEnv fe) {n : NIdx}
    {ci : IConstantInfo} (hf : fe.find? n = some ci) : PersN n ∧ PersCI ci := by
  rw [IFEnv.find?] at hf
  cases hidx : fe.idx[n]? with
  | none => rw [hidx] at hf; exact absurd hf (by simp)
  | some p =>
    rw [hidx] at hf
    obtain ⟨c, cj⟩ := p
    simp only at hf
    by_cases hlt : c < fe.visibleBelow
    · rw [if_pos hlt] at hf
      obtain rfl := Option.some.inj hf
      exact hp.idx n (c, cj) hidx
    · rw [if_neg hlt] at hf; exact absurd hf (by simp)

/-- con-leche: none — a declaration record is persistent (the parse builds
them in the persistent tier, so this is the frontend tier's postcondition). -/
def PersDecl : IDeclaration → Prop
  | .axiomDecl v => PersCV v
  | .defnDecl v e _ => PersCV v ∧ PersE e
  | .thmDecl v e => PersCV v ∧ PersE e
  | .opaqueDecl v e => PersCV v ∧ PersE e
  | .basisDecl _ => True
  | .indDecl block _ => PersCIList block
  | .quotDecl _ v => PersCV v

/-- con-leche: none — the datum that crosses the install/check seam is
persistent: `Arena/Promote.lean`'s `promoteVG` is what makes it so, and it is
what lets phase B run after phase A's `dropScratch`. -/
structure PersVG (g : Arena.ValueGroup) : Prop where
  cvA : PersCV g.cvA
  jv : PersE g.jv

/-- con-leche: none — a `Nat`-operation pin variant is persistent
(`internAllPins` runs before the parse, with the scratch tier closed). -/
structure PersPinSet (p : INatOpPinSet) : Prop where
  pins : PersEList [p.divPin, p.modPin, p.gcdPin, p.landPin, p.lorPin,
    p.xorPin, p.shiftLeftPin, p.shiftRightPin]
  proofs : PersEList (p.divProofs ++ p.modProofs ++ p.gcdProofs ++
    p.landProofs ++ p.lorProofs ++ p.xorProofs ++ p.shiftLeftProofs ++
    p.shiftRightProofs)

/-- con-leche: none — every pin variant is persistent. -/
def PersPinSets (ps : List INatOpPinSet) : Prop := ∀ p ∈ ps, PersPinSet p

/-- con-leche: none — **the pin TABLE is persistent** — task #97-P3-0 §7's
"one more clause: the pin handles are persistent", which is what makes
`PinsOK` survive `dropScratch`.  It is free: the driver runs
`internReservedPins` before the prelude with the scratch tier closed. -/
structure PersPins (s : AState) : Prop where
  names : ∀ n ∈ s.pins.names, PersN n
  reserved : PersNList s.pins.reserved
  emptyLevels : PersLs s.pins.emptyLevels
  zeroLevel : PersL s.pins.zeroLevel
  sortOne : PersE s.pins.sortOne

end ConRon.Bridge
