/-
# The denotation (DESIGN.md §8.3, task #97 P2a)

`denoteN`/`denoteL`/`denoteLs`/`denoteE` read a handle back as the con-leche
value it stands for.  They are the *only* bridge between (B) and (A): every
statement of Theorem 1 is written with `denote st` where con-ron's Rust proof
writes `absExpr` today.

## Fuel, not a stored rank — and why

DESIGN §8.3 offers two shapes: well-founded recursion on a rank carried by
`StoreWF`, or a fuel that `StoreWF` proves sufficient.  This module takes the
fuel, with the store's own node count as the fuel, for three reasons:

1. **`denote` is total and hypothesis-free.**  A rank that lives inside
   `StoreWF` is existentially quantified, so a `denote` defined by recursion on
   it would have to take the well-formedness proof as an argument — and
   `intern_spec` relates `denote` *before* and *after* an append, i.e. on a
   store whose `StoreWF` is the thing being established.  With fuel, `denoteE`
   is a plain `EStore → EIdx → Option Expr` that every statement can mention.
2. **With per-constructor arrays there is no handle order to recurse on.**
   con-leche's arena could recurse on the index itself (`ArenaWF.lean:477`,
   "forward references denote `none`, which makes the recursion well-founded
   on the index") because it had one array.  Ten arrays have no common order,
   so *some* extra measure is needed either way; fuel is the one that does not
   have to be threaded.
3. **The equations are definitional.**  `denoteEAux st (f+1) i` unfolds by
   `rfl`; the only lemma the tier above needs is `denoteE_unfold`
   (`WFProofs.lean`), which trades the fuel for `StoreWF`'s rank once.

The rank still exists — it is `StoreWF`'s `rank` field, with children below
parents and every rank below the tier's node count — and it is what proves the
fuel sufficient.
-/
import ConRon.Arena.Store
import ConLeche.Kernel.Expr

namespace ConRon.Arena

open ConLeche

/-! ## Two small option combinators

Spelled as matches (not `bind`) so the generated code is a branch, and given
their `= some` characterisations so the `denote` proofs are `simp`. -/

/-- con-leche: none — a two-argument `Option.map`. -/
@[inline] def opt2 {α β γ : Type} (f : α → β → γ) (a : Option α) (b : Option β) :
    Option γ :=
  match a, b with
  | some x, some y => some (f x y)
  | _, _ => none

/-- con-leche: none — a three-argument `Option.map`. -/
@[inline] def opt3 {α β γ δ : Type} (f : α → β → γ → δ) (a : Option α)
    (b : Option β) (c : Option γ) : Option δ :=
  match a, b, c with
  | some x, some y, some z => some (f x y z)
  | _, _, _ => none

@[simp] theorem opt2_eq_some_iff {α β γ : Type} {f : α → β → γ} {a : Option α}
    {b : Option β} {c : γ} :
    opt2 f a b = some c ↔ ∃ x y, a = some x ∧ b = some y ∧ f x y = c := by
  cases a <;> cases b <;> simp [opt2, eq_comm]

@[simp] theorem opt3_eq_some_iff {α β γ δ : Type} {f : α → β → γ → δ}
    {a : Option α} {b : Option β} {c : Option γ} {d : δ} :
    opt3 f a b c = some d ↔
      ∃ x y z, a = some x ∧ b = some y ∧ c = some z ∧ f x y z = d := by
  cases a <;> cases b <;> cases c <;> simp [opt3, eq_comm]

/-! ## Names -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the fuel-indexed
readback of a name handle. -/
def denoteNAux (st : NStore) : Nat → NIdx → Option ConLeche.Name
  | 0, _ => none
  | f + 1, i =>
    (st.view i).bind fun v =>
      match v with
      | .anonymous => some .anonymous
      | .str p s => (denoteNAux st f p).map fun q => .str q s
      | .num p n => (denoteNAux st f p).map fun q => .num q n

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the readback of a name
handle, at the store's own node count as fuel. -/
def denoteN (st : NStore) (i : NIdx) : Option ConLeche.Name :=
  denoteNAux st (st.nodeCount + 1) i

theorem denoteNAux_mono (st : NStore) :
    ∀ (f f' : Nat) (i : NIdx) (n : ConLeche.Name), f ≤ f' →
      denoteNAux st f i = some n → denoteNAux st f' i = some n := by
  intro f
  induction f with
  | zero => intro f' i n _ h; simp [denoteNAux] at h
  | succ k ih =>
    intro f' i n hle h
    obtain ⟨k', rfl⟩ : ∃ k', f' = k' + 1 := ⟨f' - 1, by omega⟩
    have hk : k ≤ k' := by omega
    simp only [denoteNAux, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨v, hv, h⟩ := h
    refine ⟨v, hv, ?_⟩
    cases v with
    | anonymous => exact h
    | str p s =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨q, hq, rfl⟩ := h
      exact ⟨q, ih k' p q hk hq, rfl⟩
    | num p m =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨q, hq, rfl⟩ := h
      exact ⟨q, ih k' p q hk hq, rfl⟩

/-! ## Levels -/

/-- con-leche: ConLeche/Kernel/Expr.lean:40-45 Level — the fuel-indexed
readback of a level handle. -/
def denoteLAux (st : LStore) : Nat → LIdx → Option Level
  | 0, _ => none
  | f + 1, i =>
    (st.view i).bind fun v =>
      match v with
      | .zero => some .zero
      | .succ u => (denoteLAux st f u).map Level.succ
      | .max u v => opt2 Level.max (denoteLAux st f u) (denoteLAux st f v)
      | .imax u v => opt2 Level.imax (denoteLAux st f u) (denoteLAux st f v)
      | .param n => (denoteN st.ns n).map Level.param

/-- con-leche: ConLeche/Kernel/Expr.lean:40-45 Level — the readback of a level
handle. -/
def denoteL (st : LStore) (i : LIdx) : Option Level :=
  denoteLAux st (st.nodeCount + 1) i

theorem denoteLAux_mono (st : LStore) :
    ∀ (f f' : Nat) (i : LIdx) (u : Level), f ≤ f' →
      denoteLAux st f i = some u → denoteLAux st f' i = some u := by
  intro f
  induction f with
  | zero => intro f' i u _ h; simp [denoteLAux] at h
  | succ k ih =>
    intro f' i u hle h
    obtain ⟨k', rfl⟩ : ∃ k', f' = k' + 1 := ⟨f' - 1, by omega⟩
    have hk : k ≤ k' := by omega
    simp only [denoteLAux, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨v, hv, h⟩ := h
    refine ⟨v, hv, ?_⟩
    cases v with
    | zero => exact h
    | succ a =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨q, hq, rfl⟩ := h
      exact ⟨q, ih k' a q hk hq, rfl⟩
    | max a b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      exact ⟨x, y, ih k' a x hk hx, ih k' b y hk hy, rfl⟩
    | imax a b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      exact ⟨x, y, ih k' a x hk hx, ih k' b y hk hy, rfl⟩
    | param n => exact h

/-! ## Level lists

A list node's children are level handles only, so there is no recursion
through `LsIdx` and no fuel: the readback is a plain fold. -/

/-- con-leche: none — `denoteL` mapped over a level-handle list. -/
def denoteLList (st : LStore) : List LIdx → Option (List Level)
  | [] => some []
  | u :: us => opt2 List.cons (denoteL st u) (denoteLList st us)

/-- con-leche: none — the readback of an interned universe-argument list. -/
def denoteLs (st : LsStore) (i : LsIdx) : Option (List Level) :=
  match st.view i with
  | none => none
  | some us => denoteLList st.ls us

/-! ## Expressions -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the fuel-indexed
readback of an expression handle. -/
def denoteEAux (st : EStore) : Nat → EIdx → Option Expr
  | 0, _ => none
  | f + 1, i =>
    (st.view i).bind fun v =>
      match v with
      | .bvar k => some (.bvar k)
      | .fvar k ty => (denoteEAux st f ty).map (Expr.fvar k)
      | .sort u => (denoteL st.ls u).map Expr.sort
      | .const n us => opt2 Expr.const (denoteN st.ns n) (denoteLs st.lss us)
      | .app g a => opt2 Expr.app (denoteEAux st f g) (denoteEAux st f a)
      | .lam ty b m =>
        opt2 (fun x y => Expr.lam x y m) (denoteEAux st f ty) (denoteEAux st f b)
      | .forallE ty b m =>
        opt2 (fun x y => Expr.forallE x y m) (denoteEAux st f ty) (denoteEAux st f b)
      | .letE ty w b =>
        opt3 Expr.letE (denoteEAux st f ty) (denoteEAux st f w) (denoteEAux st f b)
      | .lit l => some (.lit l)
      | .proj n k e =>
        opt2 (fun nm x => Expr.proj nm k x) (denoteN st.ns n) (denoteEAux st f e)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the readback of an
expression handle, at the store's own node count as fuel. -/
def denoteE (st : EStore) (i : EIdx) : Option Expr :=
  denoteEAux st (st.nodeCount + 1) i

theorem denoteEAux_mono (st : EStore) :
    ∀ (f f' : Nat) (i : EIdx) (e : Expr), f ≤ f' →
      denoteEAux st f i = some e → denoteEAux st f' i = some e := by
  intro f
  induction f with
  | zero => intro f' i e _ h; simp [denoteEAux] at h
  | succ k ih =>
    intro f' i e hle h
    obtain ⟨k', rfl⟩ : ∃ k', f' = k' + 1 := ⟨f' - 1, by omega⟩
    have hk : k ≤ k' := by omega
    simp only [denoteEAux, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨v, hv, h⟩ := h
    refine ⟨v, hv, ?_⟩
    cases v with
    | bvar _ => exact h
    | fvar j ty =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨q, hq, rfl⟩ := h
      exact ⟨q, ih k' ty q hk hq, rfl⟩
    | sort _ => exact h
    | const _ _ => exact h
    | app g a =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      exact ⟨x, y, ih k' g x hk hx, ih k' a y hk hy, rfl⟩
    | lam ty b m =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      exact ⟨x, y, ih k' ty x hk hx, ih k' b y hk hy, rfl⟩
    | forallE ty b m =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      exact ⟨x, y, ih k' ty x hk hx, ih k' b y hk hy, rfl⟩
    | letE ty w b =>
      simp only [opt3_eq_some_iff] at h ⊢
      obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := h
      exact ⟨x, y, z, ih k' ty x hk hx, ih k' w y hk hy, ih k' b z hk hz, rfl⟩
    | lit _ => exact h
    | proj n j e' =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      exact ⟨x, y, hx, ih k' e' y hk hy, rfl⟩

/-! ## Extension

`Ext st st'` is DESIGN §8.3's "every handle of `st` denotes the same in
`st'`".  It is one of the three conjuncts of `intern_spec`, and it is what
carries a fact proved before an intern past it; `dropScratch` preserves it on
*persistent* handles only, which is the tier discipline in one line. -/

/-- con-leche: none — extension of the name store. -/
def NExt (st st' : NStore) : Prop :=
  ∀ i n, denoteN st i = some n → denoteN st' i = some n

/-- con-leche: none — extension of the level store (the name store with it). -/
structure LExt (st st' : LStore) : Prop where
  ns : NExt st.ns st'.ns
  lvl : ∀ i u, denoteL st i = some u → denoteL st' i = some u

/-- con-leche: none — extension of the level-list store. -/
structure LsExt (st st' : LsStore) : Prop where
  ls : LExt st.ls st'.ls
  lst : ∀ i us, denoteLs st i = some us → denoteLs st' i = some us

/-- con-leche: none — extension of the whole arena (DESIGN §8.3; con-leche's
`Ext`, `Verify/SimI.lean:244`, is the same conjunct of `SimAt`). -/
structure Ext (st st' : EStore) : Prop where
  lss : LsExt st.lss st'.lss
  expr : ∀ i e, denoteE st i = some e → denoteE st' i = some e

theorem NExt.refl (st : NStore) : NExt st st := fun _ _ h => h
theorem LExt.refl (st : LStore) : LExt st st := ⟨NExt.refl _, fun _ _ h => h⟩
theorem LsExt.refl (st : LsStore) : LsExt st st := ⟨LExt.refl _, fun _ _ h => h⟩
theorem Ext.refl (st : EStore) : Ext st st := ⟨LsExt.refl _, fun _ _ h => h⟩

theorem NExt.trans {a b c : NStore} (h₁ : NExt a b) (h₂ : NExt b c) : NExt a c :=
  fun i n h => h₂ i n (h₁ i n h)

theorem LExt.trans {a b c : LStore} (h₁ : LExt a b) (h₂ : LExt b c) : LExt a c :=
  ⟨h₁.ns.trans h₂.ns, fun i u h => h₂.lvl i u (h₁.lvl i u h)⟩

theorem LsExt.trans {a b c : LsStore} (h₁ : LsExt a b) (h₂ : LsExt b c) :
    LsExt a c :=
  ⟨h₁.ls.trans h₂.ls, fun i us h => h₂.lst i us (h₁.lst i us h)⟩

theorem Ext.trans {a b c : EStore} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c :=
  ⟨h₁.lss.trans h₂.lss, fun i e h => h₂.expr i e (h₁.expr i e h)⟩

end ConRon.Arena
