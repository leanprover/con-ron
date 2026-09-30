/-
# `ConRon.Bridge.Inductives.Records` — the uniform route's records, denoted

DESIGN §8.2's **Theorem 1** at the uniform inductive route (task #105).
The twin's records (`Arena/Inductives/{BlockParts, Positivity, ClassRead,
RecCheck, GenRec, BlockTail}.lean`) hold handles where con-leche's hold terms;
this module gives each an `Option`-valued DENOTATION (`d…`), so that every
relation the tier states between a twin record and con-leche's is one
equation `dX st x = some y`, with ONE `ext` transport per record.

It also holds the pure side's **fuel calculus** (`FOk`): the route's
con-leche functions are written over a `CheckerOps m`, and at
`m := FueledM` (`ConLeche/Verify/BridgeDecl.lean`'s `fueledOpsM`) every
computation is a MONOTONE family, so "the pure side succeeds with `v` at
some fuel" composes through `bind` with no per-function monotonicity lemma.
`checkDecl_datF` turns the final `FOk` into the statement `IndSpec` asks for.

Nothing here reads an `AState`: the module imports the representation half
of the foundation only (`Bridge/Rel.lean`).
-/
import ConRon.Bridge.Rel
import ConRon.Arena.Inductives.BlockTail
import ConLeche.Verify.BridgeDecl

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The fuel calculus -/

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:39 bridgeRel — **the pure side
succeeds with `v` at some fuel**.  At a `FueledM` computation this is
monotone in the fuel, which is what makes it compose. -/
def FOk {α : Type} (p : FueledM α) (v : α) : Prop := ∃ F, p.val F = .ok v

theorem FOk.pure {α : Type} (a : α) : FOk (Pure.pure a : FueledM α) a := ⟨0, rfl⟩

theorem FOk.bind {α β : Type} {x : FueledM α} {f : α → FueledM β} {a : α} {b : β}
    (hx : FOk x a) (hf : FOk (f a) b) : FOk (x >>= f) b := by
  obtain ⟨F₁, h₁⟩ := hx
  obtain ⟨F₂, h₂⟩ := hf
  refine ⟨max F₁ F₂, ?_⟩
  rw [FueledM.atF_bind, x.property (Nat.le_max_left F₁ F₂) h₁]
  exact (f a).property (Nat.le_max_right F₁ F₂) h₂

theorem FOk.seq {β : Type} {x : FueledM Unit} {y : FueledM β} {b : β}
    (hx : FOk x ()) (hy : FOk y b) : FOk (x >>= fun _ => y) b :=
  FOk.bind hx hy

/-- con-leche: none — `unless`/`if` with the test known to pass. -/
theorem FOk.ite_pos {α : Type} {c : Prop} [Decidable c] {x y : FueledM α} {v : α}
    (hc : c) (h : FOk x v) : FOk (if c then x else y) v := by
  rw [if_pos hc]; exact h

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:201-204 unwrapOr — at `some`,
the pure side's `unwrapOr` is `pure`. -/
theorem FOk.unwrapOr {α : Type} {a : α} {e : ConLeche.CheckError} :
    FOk (ConLeche.unwrapOr (m := FueledM) (some a) e) a := FOk.pure a

/-- con-leche: ConLeche/Kernel/Core.lean:197-199 liftFueled — the same. -/
theorem FOk.liftFueled {α : Type} {a : α} {w : String} :
    FOk (ConLeche.liftFueled (m := FueledM) w (some a)) a := FOk.pure a

/-- con-leche: ConLeche/Verify/BridgeDecl.lean fueledOpsM — a knot call's
answer, as the Core tier's `SimE` states it, IS an `FOk` of the fueled
operation. -/
theorem FOk.whnf {μ : CheckMode} {env : Env} {d : Nat} {e v : Expr}
    (h : ∃ F, ConLeche.whnf μ env F d e = .ok v) :
    FOk ((fueledOpsM μ).whnf env d e) v := h

theorem FOk.inferType {μ : CheckMode} {env : Env} {d : Nat} {e v : Expr}
    (h : ∃ F, ConLeche.inferTypeCore μ env F d e = .ok v) :
    FOk ((fueledOpsM μ).inferType env d e) v := h

theorem FOk.isDefEq {μ : CheckMode} {env : Env} {d : Nat} {a b : Expr} {v : Bool}
    (h : ∃ F, ConLeche.isDefEqCore μ env F d a b = .ok v) :
    FOk ((fueledOpsM μ).isDefEq env d a b) v := h

theorem FOk.ensureSort {μ : CheckMode} {env : Env} {d : Nat} {e : Expr} {v : Level}
    (h : ∃ F, ConLeche.ensureSortCore μ env F d e = .ok v) :
    FOk ((fueledOpsM μ).ensureSort env d e) v := h

theorem FOk.annotate {μ : CheckMode} {env : Env} {d : Nat} {e v : Expr}
    (h : ∃ F, ConLeche.annotateCore μ env F d e = .ok v) :
    FOk ((fueledOpsM μ).annotate env d e) v := h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:1201 checkDecl_datF — the
tier's conclusion in the shape `IndSpec` states. -/
theorem FOk.checkDecl {μ : CheckMode} {pins : List NatOpPinSet} {env env' : Env}
    {d : Declaration} (h : FOk (ConLeche.checkDecl μ (fueledOpsM μ) pins env d) env') :
    ∃ F, ConLeche.checkDecl μ (fueledOps μ F) pins env d = .ok env' := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, by rw [← checkDecl_datF]; exact hF⟩

/-! ## A generic list denotation, and its transport -/

/-- con-leche: none — `List.mapM` at `Option`, for the record lists. -/
theorem mapM_option_ext {α β : Type} {f g : α → Option β}
    (h : ∀ x y, f x = some y → g x = some y) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.mapM g = some ys
  | [], ys, hm => hm
  | x :: xs, ys, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hm ⊢
    cases hx : f x with
    | none => rw [hx] at hm; simp at hm
    | some y =>
      rw [hx] at hm
      cases hxs : xs.mapM f with
      | none => rw [hxs] at hm; simp at hm
      | some zs =>
        rw [hxs] at hm
        simp only [Option.bind_some] at hm
        rw [h x y hx, mapM_option_ext h xs zs hxs]
        exact hm

/-- con-leche: none — `Option`'s `mapM` at a cons, inverted. -/
theorem mapM_option_cons_inv {α β : Type} {f : α → Option β} {x : α} {xs : List α}
    {ys : List β} (h : (x :: xs).mapM f = some ys) :
    ∃ y ys', ys = y :: ys' ∧ f x = some y ∧ xs.mapM f = some ys' := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
  cases hx : f x with
  | none => rw [hx] at h; simp at h
  | some y =>
    rw [hx] at h
    cases hxs : xs.mapM f with
    | none => rw [hxs] at h; simp at h
    | some zs =>
      rw [hxs] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      exact ⟨y, zs, h.symm, rfl, rfl⟩

/-- con-leche: none — and built back up. -/
theorem mapM_option_cons {α β : Type} {f : α → Option β} {x : α} {xs : List α}
    {y : β} {ys : List β} (hx : f x = some y) (hxs : xs.mapM f = some ys) :
    (x :: xs).mapM f = some (y :: ys) := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, hx, hxs,
    Option.bind_some]

/-- con-leche: none — `Option`'s `mapM` at an index. -/
theorem mapM_option_getElem?_bind {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ (j : Nat),
      ys[j]? = xs[j]?.bind f := by
  intro xs
  induction xs with
  | nil =>
    intro ys h j
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons x xs ih =>
    intro ys h j
    obtain ⟨y, ys', rfl, hx, hxs⟩ := mapM_option_cons_inv h
    cases j with
    | zero => simp [hx]
    | succ j => simpa using ih hxs j

/-- con-leche: none — `Option`'s `mapM` of a reversed list. -/
theorem mapM_option_reverse {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.reverse.mapM f = some ys.reverse := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
           subst h; rfl
  | cons x xs ih =>
    intro ys h
    obtain ⟨y, ys', rfl, hx, hxs⟩ := mapM_option_cons_inv h
    simp only [List.reverse_cons, List.mapM_append, ih hxs, List.mapM_cons, List.mapM_nil, hx,
      Option.bind_eq_bind, Option.pure_def, Option.bind_some]

/-- con-leche: none — `Option`'s `mapM` keeps the length. -/
theorem mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.mapM_nil] at h; cases h; rfl
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => rw [hx] at h; simp at h
    | some y =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | none => rw [hxs] at h; simp at h
      | some zs =>
        rw [hxs] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp [ih hxs]

/-- con-leche: none — `Option`'s `mapM` over a snoc. -/
theorem mapM_option_snoc {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {x : α} {ys : List β}, (xs ++ [x]).mapM f = some ys →
      ∃ zs y, ys = zs ++ [y] ∧ xs.mapM f = some zs ∧ f x = some y := by
  intro xs
  induction xs with
  | nil =>
    intro x ys h
    simp only [List.nil_append, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def] at h
    cases hx : f x with
    | none => rw [hx] at h; simp at h
    | some y =>
      rw [hx] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      subst h
      exact ⟨[], y, rfl, rfl, rfl⟩
  | cons a as ih =>
    intro x ys h
    simp only [List.cons_append, List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def] at h
    cases ha : f a with
    | none => rw [ha] at h; simp at h
    | some b =>
      rw [ha] at h
      cases hr : (as ++ [x]).mapM f with
      | none => rw [hr] at h; simp at h
      | some rs =>
        rw [hr] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨zs, y, rfl, hz, hy⟩ := ih hr
        refine ⟨b :: zs, y, rfl, ?_, hy⟩
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, ha, hz,
          Option.bind_some]

/-- con-leche: none — `Option`'s `mapM` distributes over `++`. -/
theorem mapM_option_append {α β : Type} {f : α → Option β} :
    ∀ {xs ys : List α} {a b : List β}, xs.mapM f = some a → ys.mapM f = some b →
      (xs ++ ys).mapM f = some (a ++ b) := by
  intro xs
  induction xs with
  | nil =>
    intro ys a b ha hb
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at ha
    subst ha; simpa using hb
  | cons x xs ih =>
    intro ys a b ha hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at ha
    cases hx : f x with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : xs.mapM f with
      | none => rw [hx, hxs] at ha; simp at ha
      | some zs =>
        rw [hx, hxs] at ha
        simp only [Option.bind_some, Option.some.injEq] at ha
        subst ha
        simp only [List.cons_append, List.mapM_cons, Option.bind_eq_bind, Option.pure_def, hx,
          ih hxs hb, Option.bind_some]

/-- con-leche: none — `Option`'s `mapM` under a pointwise-equal function. -/
theorem mapM_option_congr {α β : Type} {f g : α → Option β} (h : ∀ x, f x = g x)
    (xs : List α) : xs.mapM f = xs.mapM g := by
  rw [show f = g from funext h]

/-- con-leche: none — a member of a denoting list has a denoted partner. -/
theorem mapM_option_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], _, _, _, hx => nomatch hx
  | a :: as, _, h, x, hx => by
    obtain ⟨b, bs, rfl, hb, hbs⟩ := mapM_option_cons_inv h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_option_mem hbs x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- con-leche: none — `Option`'s `mapM` at the empty list, inverted. -/
theorem mapM_option_nil_inv {α β : Type} {f : α → Option β} {ys : List β}
    (h : ([] : List α).mapM f = some ys) : ys = [] := by
  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; exact h.symm

/-- con-leche: none — a denotation is TRANSPORTED along `Ext` when every
answer it gives at the smaller store it gives at the larger. -/
def DExt {α β : Type} (d : EStore → α → Option β) : Prop :=
  ∀ {st st' : EStore}, Ext st st' → ∀ x y, d st x = some y → d st' x = some y

theorem DExt.list {α β : Type} {d : EStore → α → Option β} (h : DExt d) :
    DExt (fun st (xs : List α) => xs.mapM (d st)) :=
  fun hx xs ys hm => mapM_option_ext (fun x y => h hx x y) xs ys hm

theorem dExt_denoteE : DExt denoteE := fun hx _ _ h => denote_ext h hx
theorem dExt_denoteCV : DExt Frontend.denoteCV := fun hx _ _ h => denoteCV_ext h hx
theorem dExt_denoteEList : DExt Frontend.denoteEList :=
  fun hx xs ys h => denoteEList_ext hx xs ys h
/-- con-leche: none — the do-notation form every record denotation below is
written in: two transported pieces give a transported pair. -/
theorem option_bind_ext {α β : Type} {o o' : Option α} {f : α → Option β} {y : β}
    (ho : ∀ a, o = some a → o' = some a) (h : o >>= f = some y) : o' >>= f = some y := by
  cases hc : o with
  | none => rw [hc] at h; exact nomatch h
  | some a => rw [hc] at h; rw [ho a hc]; exact h

/-! ## The block's shape (`Arena/Inductives/BlockParts.lean`) -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:66 MemberShape
(`ctors`) — a constructor with its field count. -/
def dCtor (st : EStore) (c : IConstantVal × Nat) : Option (ConstantVal × Nat) :=
  (Frontend.denoteCV st c.1).map (·, c.2)

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:66 MemberShape. -/
def dCtors (st : EStore) (cs : List (IConstantVal × Nat)) :
    Option (List (ConstantVal × Nat)) := cs.mapM (dCtor st)

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:58-69 MemberShape. -/
def dMember (st : EStore) (m : Arena.MemberShape) : Option ConLeche.MemberShape := do
  let cvT ← Frontend.denoteCV st m.cvT
  let cs ← dCtors st m.ctors
  pure ⟨cvT, m.nIdx, cs⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:71-96 RecShape. -/
def dRec (st : EStore) (r : Arena.RecShape) : Option ConLeche.RecShape := do
  let cvR ← Frontend.denoteCV st r.cvR
  let rhss ← Frontend.denoteEList st r.rhss
  pure ⟨cvR, r.rP, r.mI, r.tgt, rhss⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:98-121 BlockShape. -/
def dShape (st : EStore) (p : Arena.BlockShape) : Option ConLeche.BlockShape := do
  let members ← p.members.mapM (dMember st)
  let recs ← p.recs.mapM (dRec st)
  let elim ← denoteN st.ns p.elim
  let s ← denoteL st.ls p.resSort
  pure ⟨members, recs, p.nP, elim, s, p.large, p.isProp⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:198-201 BlockParts. -/
def dParts (st : EStore) (p : Arena.BlockParts) : Option ConLeche.BlockParts :=
  (dShape st p.shape).map fun q => ⟨q⟩

theorem dCtor_ext : DExt dCtor := by
  intro st st' hx c y h
  simp only [dCtor, Option.map_eq_some_iff] at h ⊢
  obtain ⟨cv, hcv, rfl⟩ := h
  exact ⟨cv, denoteCV_ext hcv hx, rfl⟩

theorem dCtors_ext : DExt dCtors := dCtor_ext.list

theorem dMember_ext : DExt dMember := by
  intro st st' hx m y h
  simp only [dMember] at h ⊢
  refine option_bind_ext (fun a ha => denoteCV_ext ha hx) ?_
  cases hcv : Frontend.denoteCV st m.cvT with
  | none => rw [hcv] at h; exact nomatch h
  | some cv =>
    rw [hcv] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    exact option_bind_ext (fun a ha => dCtors_ext hx _ a ha) h

theorem dRec_ext : DExt dRec := by
  intro st st' hx r y h
  simp only [dRec] at h ⊢
  refine option_bind_ext (fun a ha => denoteCV_ext ha hx) ?_
  cases hcv : Frontend.denoteCV st r.cvR with
  | none => rw [hcv] at h; exact nomatch h
  | some cv =>
    rw [hcv] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    exact option_bind_ext (fun a ha => denoteEList_ext hx _ a ha) h

theorem dShape_ext : DExt dShape := by
  intro st st' hx p y h
  simp only [dShape] at h ⊢
  cases h1 : p.members.mapM (dMember st) with
  | none => rw [h1] at h; exact nomatch h
  | some ms =>
  cases h2 : p.recs.mapM (dRec st) with
  | none => rw [h1, h2] at h; exact nomatch h
  | some rs =>
  cases h3 : denoteN st.ns p.elim with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some el =>
  cases h4 : denoteL st.ls p.resSort with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some s =>
  rw [h1, h2, h3, h4] at h
  rw [show p.members.mapM (dMember st') = some ms from dMember_ext.list hx _ _ h1,
    show p.recs.mapM (dRec st') = some rs from dRec_ext.list hx _ _ h2, denoteN_ext h3 hx,
    denoteL_ext h4 hx]
  exact h

theorem dParts_ext : DExt dParts := by
  intro st st' hx p y h
  simp only [dParts, Option.map_eq_some_iff] at h ⊢
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q, dShape_ext hx _ _ hq, rfl⟩

/-! ## The positivity walk's records (`Arena/Inductives/Positivity.lean`) -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:598-608 NestFieldKind
— the twin's copy of the inductive, read as con-leche's. -/
def kindOf : Arena.NestFieldKind → ConLeche.NestFieldKind
  | .ordinary => .ordinary
  | .recursive t => .recursive t
  | .reflexive t => .reflexive t
  | .inProgress => .inProgress
  | .nested r => .nested r

theorem kindOf_flat (k : Arena.NestFieldKind) :
    (kindOf k).flat = k.flat := by
  cases k <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey. -/
def dKey (st : EStore) (k : Arena.NestKey) : Option ConLeche.NestKey := do
  let c ← denoteN st.ns k.cname
  let us ← denoteLs st.lss k.lvls
  let ds ← Frontend.denoteEList st k.ds
  pure ⟨c, us, ds⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:530-536 NestHole. -/
def dHole (st : EStore) (h : Arena.NestHole) : Option ConLeche.NestHole :=
  (dKey st h.key).map fun k => ⟨k, h.base⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:621-641 NestCtorNf. -/
def dCtorNf (st : EStore) (n : Arena.NestCtorNf) : Option ConLeche.NestCtorNf := do
  let c ← denoteN st.ns n.ctor
  let us ← denoteLs st.lss n.lvls
  let ds ← Frontend.denoteEList st n.ds
  let ty ← denoteE st n.ty
  pure ⟨c, us, ds, ty⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:656-668 NestState. -/
def dState (st : EStore) (ns : Arena.NestState) : Option ConLeche.NestState := do
  let keys ← ns.keys.toList.mapM (dKey st)
  let active ← ns.active.mapM (dKey st)
  let nfs ← ns.ctorNfs.toList.mapM (dCtorNf st)
  pure ⟨keys.toArray, active, nfs.toArray⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1442-1496 nestPos
(`prog`) — **the frame stack, reversed**: the twin's is outermost first,
con-leche's innermost first (`Arena/Inductives/Positivity.lean`'s module
note). -/
def dProg (st : EStore) (prog : List Arena.NestHole) : Option (List ConLeche.NestHole) :=
  (prog.mapM (dHole st)).map List.reverse

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:643-654 NestCtx — the
twin's record at the lookup `find?` (the environment every reader takes beside
it), its interned level list denoting `lps.map .param`. -/
def dCtx (st : EStore) (find? : ConLeche.Name → Option ConstantInfo)
    (c : Arena.NestCtx) : Option ConLeche.NestCtx := do
  let names ← Frontend.denoteNList st.ns c.names
  let lps ← Frontend.denoteNList st.ns c.lps
  let params ← Frontend.denoteEList st c.params
  let sort ← denoteL st.ls c.sort
  let lvls ← denoteLs st.lss c.lvls
  if lvls = lps.map .param then pure ⟨names, lps, c.nP, c.nIdxs, params, sort, find?⟩
  else none

theorem dKey_ext : DExt dKey := by
  intro st st' hx k y h
  simp only [dKey] at h ⊢
  cases h1 : denoteN st.ns k.cname with
  | none => rw [h1] at h; exact nomatch h
  | some c =>
  cases h2 : denoteLs st.lss k.lvls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some us =>
  cases h3 : Frontend.denoteEList st k.ds with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some ds =>
  rw [h1, h2, h3] at h
  rw [denoteN_ext h1 hx, denoteLs_ext h2 hx, denoteEList_ext hx _ _ h3]
  exact h

theorem dHole_ext : DExt dHole := by
  intro st st' hx k y h
  simp only [dHole, Option.map_eq_some_iff] at h ⊢
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q, dKey_ext hx _ _ hq, rfl⟩

theorem dCtorNf_ext : DExt dCtorNf := by
  intro st st' hx k y h
  simp only [dCtorNf] at h ⊢
  cases h1 : denoteN st.ns k.ctor with
  | none => rw [h1] at h; exact nomatch h
  | some c =>
  cases h2 : denoteLs st.lss k.lvls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some us =>
  cases h3 : Frontend.denoteEList st k.ds with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some ds =>
  cases h4 : denoteE st k.ty with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some ty =>
  rw [h1, h2, h3, h4] at h
  rw [denoteN_ext h1 hx, denoteLs_ext h2 hx, denoteEList_ext hx _ _ h3, denote_ext h4 hx]
  exact h

theorem dState_ext : DExt dState := by
  intro st st' hx k y h
  simp only [dState] at h ⊢
  cases h1 : k.keys.toList.mapM (dKey st) with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : k.active.mapM (dKey st) with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : k.ctorNfs.toList.mapM (dCtorNf st) with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some c =>
  rw [h1, h2, h3] at h
  rw [show k.keys.toList.mapM (dKey st') = some a from dKey_ext.list hx _ _ h1,
    show k.active.mapM (dKey st') = some b from dKey_ext.list hx _ _ h2,
    show k.ctorNfs.toList.mapM (dCtorNf st') = some c from dCtorNf_ext.list hx _ _ h3]
  exact h

theorem dProg_ext : DExt dProg := by
  intro st st' hx k y h
  simp only [dProg, Option.map_eq_some_iff] at h ⊢
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q, dHole_ext.list hx _ _ hq, rfl⟩

theorem dCtx_ext (find? : ConLeche.Name → Option ConstantInfo) :
    DExt (fun st c => dCtx st find? c) := by
  intro st st' hx k y h
  simp only [dCtx] at h ⊢
  cases h1 : Frontend.denoteNList st.ns k.names with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : Frontend.denoteNList st.ns k.lps with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : Frontend.denoteEList st k.params with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some c =>
  cases h4 : denoteL st.ls k.sort with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some s =>
  cases h5 : denoteLs st.lss k.lvls with
  | none => rw [h1, h2, h3, h4, h5] at h; exact nomatch h
  | some l =>
  rw [h1, h2, h3, h4, h5] at h
  rw [denoteNListE_ext hx _ _ h1, denoteNListE_ext hx _ _ h2, denoteEList_ext hx _ _ h3,
    denoteL_ext h4 hx, denoteLs_ext h5 hx]
  exact h

/-! ## The shape records, inverted -/

/-- con-leche: none — a denoted shape, field by field. -/
theorem dShape_inv {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) :
    p.members.mapM (dMember st) = some pP.members ∧ p.recs.mapM (dRec st) = some pP.recs ∧
      p.nP = pP.nP ∧ denoteN st.ns p.elim = some pP.elim ∧
      denoteL st.ls p.resSort = some pP.resSort ∧ p.large = pP.large ∧
      p.isProp = pP.isProp := by
  simp only [dShape] at h
  cases h1 : p.members.mapM (dMember st) with
  | none => rw [h1] at h; exact nomatch h
  | some ms =>
  cases h2 : p.recs.mapM (dRec st) with
  | none => rw [h1, h2] at h; exact nomatch h
  | some rs =>
  cases h3 : denoteN st.ns p.elim with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some el =>
  cases h4 : denoteL st.ls p.resSort with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some so =>
  rw [h1, h2, h3, h4] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- con-leche: none — a denoted member, field by field. -/
theorem dMember_inv {st : EStore} {m : Arena.MemberShape} {mP : ConLeche.MemberShape}
    (h : dMember st m = some mP) :
    Frontend.denoteCV st m.cvT = some mP.cvT ∧ m.nIdx = mP.nIdx ∧
      dCtors st m.ctors = some mP.ctors := by
  simp only [dMember] at h
  cases h1 : Frontend.denoteCV st m.cvT with
  | none => rw [h1] at h; exact nomatch h
  | some cv =>
  cases h2 : dCtors st m.ctors with
  | none => rw [h1, h2] at h; exact nomatch h
  | some cs =>
  rw [h1, h2] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl⟩

/-- con-leche: none — a denoted recursor record, field by field. -/
theorem dRec_inv {st : EStore} {r : Arena.RecShape} {rP : ConLeche.RecShape}
    (h : dRec st r = some rP) :
    Frontend.denoteCV st r.cvR = some rP.cvR ∧ r.rP = rP.rP ∧ r.mI = rP.mI ∧
      r.tgt = rP.tgt ∧ Frontend.denoteEList st r.rhss = some rP.rhss := by
  simp only [dRec] at h
  cases h1 : Frontend.denoteCV st r.cvR with
  | none => rw [h1] at h; exact nomatch h
  | some cv =>
  cases h2 : Frontend.denoteEList st r.rhss with
  | none => rw [h1, h2] at h; exact nomatch h
  | some rh =>
  rw [h1, h2] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end ConRon.Bridge.Inductives
