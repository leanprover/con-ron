/-
# `ConRon.Bridge.Frontend.Olean.Read` — a module's value, off the memo

The memo answers a pointer without touching the state, so reading a skeleton through it
is a pure function of the skeleton (`PR`, a run that returns its state), the same function
as upstream's `ModSkel.read`.  Denotations (`denoteEntry`, `denoteMod`) are upstream's own
`mapM`s, in `Option`, so that one lemma about `mapM` (`entry_sim`) relates a read skeleton
to its specification.
-/
module

public import ConRon.Bridge.Frontend.Olean.Fast

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Sub DS PtrRead entryMap)
open ConLeche.Frontend.Olean (Region CEntryF CKindF ImportF ImportRec ModSkel nameAt nameP exprP
  bind_some_left constSkel moduleSkel)

/-! ## Denotations -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:403-404 ImportRec — an import's name read
back. -/
@[expose] def denoteImport (st : EStore) (i : ImportF NIdx) : Option ImportRec :=
  i.mapM (denoteN st.ns)

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:262-266 CEntryF — a constant's names and
expressions read back. -/
@[expose] def denoteEntry (st : EStore) (c : CEntryF NIdx EIdx) : Option (CEntryF ConLeche.Name Expr) :=
  c.mapM (denoteN st.ns) (denoteE st)

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:437-440 ModDecoded — a module read back. -/
@[expose] def denoteMod (st : EStore) (d : ConRon.Arena.Frontend.Olean.ModDecoded) :
    Option ConLeche.Frontend.Olean.ModDecoded := do
  let imports ← d.imports.toList.mapM (denoteImport st)
  let constants ← d.constants.toList.mapM (denoteEntry st)
  pure ⟨d.isModule, imports.toArray, constants.toArray⟩

/-! ## Options: one list, one constant -/

/-- A `mapM` in `Option` related to another through a denotation. -/
theorem list_sim {α β γ : Type} {f : α → Option β} {g : α → Option γ} {d : β → Option γ} :
    ∀ (l : List α) {ys : List β}, l.mapM f = some ys →
      (∀ x ∈ l, ∀ y, f x = some y → ∃ z, g x = some z ∧ d y = some z) →
      ∃ zs, l.mapM g = some zs ∧ ys.mapM d = some zs
  | [], ys, h, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | x :: l, ys, h, hk => by
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_some_left h
    obtain ⟨ys', hys, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    obtain ⟨z, hz, hd⟩ := hk x (by simp) y hy
    obtain ⟨zs, hzs, hds⟩ := list_sim l hys (fun w hw => hk w (List.mem_cons_of_mem _ hw))
    refine ⟨z :: zs, ?_, ?_⟩
    · simp only [List.mapM_cons, hz, hzs]; rfl
    · simp only [List.mapM_cons, hd, hds]; rfl

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:299-305 CEntryF.mapM — **a constant read by
`fn`, `fe`** is one read by `fnC`, `feC`, through the denotations `dn`, `de`. -/
theorem entry_sim {N E N' E' N'' E'' : Type} {fn : N → Option N'} {fe : E → Option E'}
    {fnC : N → Option N''} {feC : E → Option E''} {dn : N' → Option N''} {de : E' → Option E''}
    (c : CEntryF N E) {e : CEntryF N' E'} (h : c.mapM fn fe = some e)
    (hn : ∀ x ∈ c.names, ∀ y, fn x = some y → ∃ z, fnC x = some z ∧ dn y = some z)
    (he : ∀ x ∈ c.exprs, ∀ y, fe x = some y → ∃ z, feC x = some z ∧ de y = some z) :
    ∃ z, c.mapM fnC feC = some z ∧ e.mapM dn de = some z := by
  rcases c with ⟨name, lps, type, kind⟩
  simp only [CEntryF.mapM] at h ⊢
  obtain ⟨n', hn', h⟩ := bind_some_left h
  obtain ⟨lps', hl', h⟩ := bind_some_left h
  obtain ⟨t', ht', h⟩ := bind_some_left h
  obtain ⟨k', hk', h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  obtain ⟨zn, h1, h1'⟩ := hn name (by simp [ConLeche.Frontend.Olean.CEntryF.names]) _ hn'
  obtain ⟨zl, h2, h2'⟩ := list_sim lps hl'
    (fun x hx => hn x (by simp [ConLeche.Frontend.Olean.CEntryF.names, hx]))
  obtain ⟨zt, h3, h3'⟩ := he type (by simp [ConLeche.Frontend.Olean.CEntryF.exprs]) _ ht'
  have hkk : ∃ zk, kind.mapM fnC feC = some zk ∧ k'.mapM dn de = some zk := by
    cases kind with
    | ax u =>
      simp only [CKindF.mapM, pure, Option.some.injEq] at hk'
      subst hk'
      exact ⟨.ax u, rfl, rfl⟩
    | quot u =>
      simp only [CKindF.mapM, pure, Option.some.injEq] at hk'
      subst hk'
      exact ⟨.quot u, rfl, rfl⟩
    | defn v hs sf =>
      simp only [CKindF.mapM] at hk'
      obtain ⟨v', hv', hk'⟩ := bind_some_left hk'
      simp only [pure, Option.some.injEq] at hk'
      subst hk'
      obtain ⟨z, a, b⟩ := he v (by simp [ConLeche.Frontend.Olean.CEntryF.exprs]) _ hv'
      refine ⟨.defn z hs sf, ?_, ?_⟩
      · simp only [CKindF.mapM, a]; rfl
      · simp only [CKindF.mapM, b]; rfl
    | opaq v u =>
      simp only [CKindF.mapM] at hk'
      obtain ⟨v', hv', hk'⟩ := bind_some_left hk'
      simp only [pure, Option.some.injEq] at hk'
      subst hk'
      obtain ⟨z, a, b⟩ := he v (by simp [ConLeche.Frontend.Olean.CEntryF.exprs]) _ hv'
      refine ⟨.opaq z u, ?_, ?_⟩
      · simp only [CKindF.mapM, a]; rfl
      · simp only [CKindF.mapM, b]; rfl
    | thm v all =>
      simp only [CKindF.mapM] at hk'
      obtain ⟨v', hv', hk'⟩ := bind_some_left hk'
      obtain ⟨all', ha', hk'⟩ := bind_some_left hk'
      simp only [pure, Option.some.injEq] at hk'
      subst hk'
      obtain ⟨z, a, b⟩ := he v (by simp [ConLeche.Frontend.Olean.CEntryF.exprs]) _ hv'
      obtain ⟨zs, c, d⟩ := list_sim all ha'
        (fun x hx => hn x (by simp [ConLeche.Frontend.Olean.CEntryF.names, hx]))
      refine ⟨.thm z zs, ?_, ?_⟩
      · simp only [CKindF.mapM, a, c]; rfl
      · simp only [CKindF.mapM, b, d]; rfl
    | induct np ni all cs nn ir iu irf =>
      simp only [CKindF.mapM] at hk'
      obtain ⟨all', ha', hk'⟩ := bind_some_left hk'
      obtain ⟨cs', hc', hk'⟩ := bind_some_left hk'
      simp only [pure, Option.some.injEq] at hk'
      subst hk'
      obtain ⟨zs, a, b⟩ := list_sim all ha'
        (fun x hx => hn x (by simp [ConLeche.Frontend.Olean.CEntryF.names, hx]))
      obtain ⟨zc, c, d⟩ := list_sim cs hc'
        (fun x hx => hn x (by simp [ConLeche.Frontend.Olean.CEntryF.names, hx]))
      refine ⟨.induct np ni zs zc nn ir iu irf, ?_, ?_⟩
      · simp only [CKindF.mapM, a, c]; rfl
      · simp only [CKindF.mapM, b, d]; rfl
    | ctor ind ci np nf iu =>
      simp only [CKindF.mapM] at hk'
      obtain ⟨i', hi', hk'⟩ := bind_some_left hk'
      simp only [pure, Option.some.injEq] at hk'
      subst hk'
      obtain ⟨z, a, b⟩ := hn ind (by simp [ConLeche.Frontend.Olean.CEntryF.names]) _ hi'
      refine ⟨.ctor z ci np nf iu, ?_, ?_⟩
      · simp only [CKindF.mapM, a]; rfl
      · simp only [CKindF.mapM, b]; rfl
    | recur all np ni nmo nmi rules kk iu =>
      simp only [CKindF.mapM] at hk'
      obtain ⟨all', ha', hk'⟩ := bind_some_left hk'
      obtain ⟨rs', hr', hk'⟩ := bind_some_left hk'
      simp only [pure, Option.some.injEq] at hk'
      subst hk'
      obtain ⟨zs, a, b⟩ := list_sim all ha'
        (fun x hx => hn x (by simp [ConLeche.Frontend.Olean.CEntryF.names, hx]))
      obtain ⟨zr, c, d⟩ := list_sim
        (g := fun (x : N × Nat × E) => do
          let c ← fnC x.1
          let e ← feC x.2.2
          pure (c, x.2.1, e))
        (d := fun (x : N' × Nat × E') => do
          let c ← dn x.1
          let e ← de x.2.2
          pure (c, x.2.1, e)) rules hr' (by
          rintro ⟨cn, nf, ex⟩ hx ⟨cn', nf', ex'⟩ hy
          obtain ⟨y1, h1, hy⟩ := bind_some_left hy
          obtain ⟨y2, h2, hy⟩ := bind_some_left hy
          simp only [pure, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨rfl, rfl, rfl⟩ := hy
          obtain ⟨z1, a1, b1⟩ := hn cn (List.mem_append_right _ (List.mem_append_right _
            (List.mem_map_of_mem (f := fun x : N × Nat × E => x.1) hx))) _ h1
          obtain ⟨z2, a2, b2⟩ := he ex (List.mem_cons_of_mem _
            (List.mem_map_of_mem (f := fun x : N × Nat × E => x.2.2) hx)) _ h2
          refine ⟨(z1, nf, z2), ?_, ?_⟩
          · simp only [a1, a2]; rfl
          · simp only [b1, b2]; rfl)
      refine ⟨.recur zs np ni nmo nmi zr kk iu, ?_, ?_⟩
      · simp only [CKindF.mapM, a]
        exact congrArg (fun o => Option.bind o fun rules => pure (CKindF.recur zs np ni nmo nmi rules kk iu)) c
      · simp only [CKindF.mapM, b]
        exact congrArg (fun o => Option.bind o fun rules => pure (CKindF.recur zs np ni nmo nmi rules kk iu)) d
  obtain ⟨zk, h4, h4'⟩ := hkk
  refine ⟨⟨zn, zl, zt, zk⟩, ?_, ?_⟩
  · simp only [h1, h2, h3, h4]; rfl
  · simp only [h1', h2', h3', h4']; rfl

/-- A `mapM` that asks only for what it answered asks the same of a larger function. -/
theorem list_mono {α β : Type} {f g : α → Option β} (hm : ∀ x y, f x = some y → g x = some y) :
    ∀ (l : List α) {ys : List β}, l.mapM f = some ys → l.mapM g = some ys := by
  intro l ys h
  obtain ⟨zs, h1, h2⟩ := list_sim (g := g) (d := some) l h
    (fun x _ y hy => ⟨y, hm x y hy, rfl⟩)
  have : ys.mapM (some : β → Option β) = some ys := by
    clear h h2
    induction ys with
    | nil => rfl
    | cons a as ih => simp only [List.mapM_cons, ih]; rfl
  rw [this] at h2
  cases h2
  exact h1

/-- A constant read back in a larger store. -/
theorem denoteEntry_ext {st st' : EStore} (hx : Ext st st') {c : CEntryF NIdx EIdx}
    {e : CEntryF ConLeche.Name Expr} (h : denoteEntry st c = some e) : denoteEntry st' c = some e := by
  obtain ⟨hs1, hs2⟩ := ConLeche.Frontend.Olean.CEntryF.mapM_some c h
  have hc := ConLeche.Frontend.Olean.CEntryF.mapM_congr (fn := denoteN st.ns) (fn' := denoteN st'.ns)
    (fe := denoteE st) (fe' := denoteE st') c
    (fun x hm => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hs1 x hm)
      rw [hy, denoteN_ext hy hx])
    (fun x hm => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hs2 x hm)
      rw [hy, denote_ext hy hx])
  unfold denoteEntry at h ⊢
  rw [← hc]
  exact h

/-- An import read back in a larger store. -/
theorem denoteImport_ext {st st' : EStore} (hx : Ext st st') {i : ImportF NIdx} {z : ImportRec}
    (h : denoteImport st i = some z) : denoteImport st' i = some z := by
  unfold denoteImport ImportF.mapM at h ⊢
  obtain ⟨y, hy, h⟩ := bind_some_left h
  simp only [denoteN_ext hy hx]
  simpa [hy] using h

/-- A module read back in a larger store. -/
theorem denoteMod_ext {st st' : EStore} (hx : Ext st st')
    {d : ConRon.Arena.Frontend.Olean.ModDecoded} {z : ConLeche.Frontend.Olean.ModDecoded}
    (h : denoteMod st d = some z) : denoteMod st' d = some z := by
  unfold denoteMod at h ⊢
  obtain ⟨is, h1, h⟩ := bind_some_left h
  obtain ⟨cs, h2, h⟩ := bind_some_left h
  simp only [list_mono (fun _ _ hy => denoteImport_ext hx hy) _ h1,
    list_mono (fun _ _ hy => denoteEntry_ext hx hy) _ h2]
  exact h

/-! ## Runs that return their state -/

/-- con-leche: none — an `OptionT AM` action that leaves the state alone and answers `o`. -/
@[expose] def PR {α : Type} (x : OptionT AM α) (o : Option α) : Prop := ∀ s, x s = .ok (o, s)

theorem PR.pure {α : Type} (a : α) : PR (Pure.pure a : OptionT AM α) (some a) := fun _ => rfl

theorem PR.bind {α β : Type} {x : OptionT AM α} {o : Option α} {f : α → OptionT AM β}
    {g : α → Option β} (hx : PR x o) (hf : ∀ a, PR (f a) (g a)) :
    PR (x >>= f) (o >>= g) := by
  intro s
  have hx' := hx s
  show (OptionT.bind x f) s = _
  simp only [OptionT.bind, OptionT.mk, Bind.bind, StateT.bind, hx']
  cases o with
  | none => rfl
  | some a => exact hf a s

theorem PR.mapM {α β : Type} {f : α → OptionT AM β} {g : α → Option β} (h : ∀ a, PR (f a) (g a)) :
    ∀ (l : List α), PR (l.mapM f) (l.mapM g)
  | [] => PR.pure _
  | x :: l => by
    simp only [List.mapM_cons]
    exact (h x).bind fun a => (PR.mapM h l).bind fun b => PR.pure _

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:407-409 ImportF.mapM -/
theorem PR.importMap {N N' : Type} {f : N → OptionT AM N'} {g : N → Option N'}
    (h : ∀ a, PR (f a) (g a)) (i : ImportF N) : PR (i.mapM f) (i.mapM g) :=
  (h i.module).bind fun _ => PR.pure _

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:275-296 CKindF.mapM -/
theorem PR.kindMap {N E N' E' : Type} {fn : N → OptionT AM N'} {fe : E → OptionT AM E'}
    {gn : N → Option N'} {ge : E → Option E'} (hn : ∀ a, PR (fn a) (gn a))
    (he : ∀ a, PR (fe a) (ge a)) (k : CKindF N E) : PR (k.mapM fn fe) (k.mapM gn ge) := by
  cases k with
  | ax u => exact PR.pure _
  | quot u => exact PR.pure _
  | defn v h s => exact (he v).bind fun _ => PR.pure _
  | opaq v u => exact (he v).bind fun _ => PR.pure _
  | thm v all => exact (he v).bind fun _ => (PR.mapM hn all).bind fun _ => PR.pure _
  | induct np ni all cs nn ir iu irf =>
    exact (PR.mapM hn all).bind fun _ => (PR.mapM hn cs).bind fun _ => PR.pure _
  | ctor ind ci np nf iu => exact (hn ind).bind fun _ => PR.pure _
  | recur all np ni nmo nmi rules kk iu =>
    refine (PR.mapM hn all).bind fun _ => (PR.mapM ?_ rules).bind fun _ => PR.pure _
    rintro ⟨c, n, e⟩
    exact (hn c).bind fun _ => (he e).bind fun _ => PR.pure _

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:299-305 CEntryF.mapM -/
theorem PR.entryMap {N E N' E' : Type} {fn : N → OptionT AM N'} {fe : E → OptionT AM E'}
    {gn : N → Option N'} {ge : E → Option E'} (hn : ∀ a, PR (fn a) (gn a))
    (he : ∀ a, PR (fe a) (ge a)) (c : CEntryF N E) : PR (c.mapM fn fe) (c.mapM gn ge) :=
  (hn c.name).bind fun _ => (PR.mapM hn c.levelParams).bind fun _ => (he c.type).bind fun _ =>
    (PR.kindMap hn he c.kind).bind fun _ => PR.pure _

/-! ## A module off the memo -/

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:311-316 ModSkel.read — the twin's read off a
memo, as a function. -/
@[expose] def readOf (nm : UInt64 → Option NIdx) (ex : UInt64 → Option EIdx) (sk : ModSkel)
    (cs : List (CEntryF UInt64 UInt64)) : Option ConRon.Arena.Frontend.Olean.ModDecoded := do
  let imports ← sk.imports.mapM (ImportF.mapM nm)
  let constants ← cs.mapM (CEntryF.mapM nm ex)
  pure ⟨sk.isModule, imports.toArray, constants.toArray⟩

theorem modSkelRead_pr {rd : PtrRead} {nm : UInt64 → Option NIdx} {ex : UInt64 → Option EIdx}
    (hn : ∀ v, rd.rdName v = pure (nm v)) (he : ∀ v, rd.rdExpr v = pure (ex v)) (sk : ModSkel)
    (cs : List (CEntryF UInt64 UInt64)) :
    PR (ConRon.Arena.Frontend.Olean.ModSkel.read rd sk cs) (readOf nm ex sk cs) := by
  have h1 : ∀ v, PR (OptionT.mk (rd.rdName v)) (nm v) := fun v s => by
    show rd.rdName v s = _
    rw [hn]; rfl
  have h2 : ∀ v, PR (OptionT.mk (rd.rdExpr v)) (ex v) := fun v s => by
    show rd.rdExpr v s = _
    rw [he]; rfl
  exact (PR.mapM (PR.importMap h1) sk.imports).bind fun _ =>
    (PR.mapM (fun c s => PR.entryMap h1 h2 c s) cs).bind fun _ => PR.pure _

/-- con-leche: ConLeche/Verify/Frontend/Olean/Equiv.lean:299 ModSkel.read_some — **the read off
a memo that answers the roots is the specification's**. -/
theorem readOf_spec {st : EStore} {r : Region} {nm : UInt64 → Option NIdx} {ex : UInt64 → Option EIdx}
    {sk : ModSkel} {cs : List (CEntryF UInt64 UInt64)}
    {d : ConRon.Arena.Frontend.Olean.ModDecoded} (hr : readOf nm ex sk cs = some d)
    (hi : ∀ i ∈ sk.imports, ∀ y, nm i.module = some y →
      ∃ z, nameP r i.module = some z ∧ denoteN st.ns y = some z)
    (hn : ∀ c ∈ cs, ∀ v ∈ c.names, ∀ y, nm v = some y →
      ∃ z, nameP r v = some z ∧ denoteN st.ns y = some z)
    (he : ∀ c ∈ cs, ∀ v ∈ c.exprs, ∀ y, ex v = some y →
      ∃ z, exprP r v = some z ∧ denoteE st y = some z) :
    ∃ z, sk.read (nameP r) (exprP r) cs = some z ∧ denoteMod st d = some z := by
  unfold readOf at hr
  obtain ⟨is, h1, hr⟩ := bind_some_left hr
  obtain ⟨es, h2, hr⟩ := bind_some_left hr
  simp only [pure, Option.some.injEq] at hr
  subst hr
  obtain ⟨zis, a1, b1⟩ := list_sim (g := ImportF.mapM (nameP r)) (d := denoteImport st) _ h1
    (fun i hm y hy => by
      obtain ⟨w, hw, hy⟩ := bind_some_left hy
      simp only [pure, Option.some.injEq] at hy
      subst hy
      obtain ⟨z, a, b⟩ := hi i hm _ hw
      exact ⟨{ i with module := z }, by simp only [ImportF.mapM, a]; rfl,
        by simp only [denoteImport, ImportF.mapM, b]; rfl⟩)
  obtain ⟨zes, a2, b2⟩ := list_sim (g := CEntryF.mapM (nameP r) (exprP r)) (d := denoteEntry st) _ h2
    (fun c hm y hy => entry_sim (fnC := nameP r) (feC := exprP r) (dn := denoteN st.ns)
      (de := denoteE st) c hy (hn c hm) (he c hm))
  refine ⟨⟨sk.isModule, zis.toArray, zes.toArray⟩, ?_, ?_⟩
  · simp only [ConLeche.Frontend.Olean.ModSkel.read, a1, a2]; rfl
  · simp only [denoteMod, b1, b2]; rfl

end ConRon.Bridge.Frontend.Olean
