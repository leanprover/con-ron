/-
# `ConRon.Bridge.Modular.Home` — the worker's home, Theorem 1 (task #166)

**The twin's home of a module is upstream's `WorkerFacts.home`** (`homeHyp_holds`): the private
part's files read off the snapshot (`readFiles`), the private view's load a load by the
specification (`LoadOf 0 mC f lC`, `loadView_run` over `loadAt_runOf`), and the views' check over
the load upstream's accept (`checkViews_run`: each part's flag, the server part's imports, the name
tables, and the exported level of each private constant, `expoOfParts_run`, a theorem's value read
off the file where the check compares one, `entryAt_run`).

Run style (simulations over `AM.bind_ok`), as `Bridge/Frontend/Olean/Closure.lean`.
-/
module

public import ConRon.Bridge.Modular.Rel
public import ConRon.Bridge.Frontend.Olean.Sparse
public import ConRon.Bridge.Modular.ReadsParts
public import ConRon.Bridge.Modular.Accepted
public import ConRon.Bridge.Frontend.Olean.Parse
public import ConRon.Bridge.Frontend.Olean.Closure
public import ConRon.Bridge.Frontend.Olean.MergeAll
public import ConLeche.Verify.Driver.Loads
public import ConLeche.Frontend.Olean.Module
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.OleanInput

public section

namespace ConRon.Bridge.Modular.Home

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins DS)
open ConLeche.Frontend.Olean (Region CEntryF CKindF ImportF ImportRec Roots OLeanLevel ModFiles
  ModSkel constSkel moduleSkel nameP exprP decodeAt constSpec bind_some_left)

/-! ## Imports read back -/

/-- Two arrays read back off one array of import handles are one. -/
theorem imports_den_eq {st : EStore} {a : Array (ImportF NIdx)} {zs ws : Array ImportRec}
    (h1 : a.toList.mapM (denoteImport st) = some zs.toList)
    (h2 : a.toList.mapM (denoteImport st) = some ws.toList) : zs = ws := by
  rw [h1] at h2
  exact Array.toList_inj.mp (Option.some.inj h2)

/-! ## A constant compared, read back -/

/-- A `mapM` of an injective partial function is injective. -/
theorem mapM_inj {α β : Type} {f : α → Option β}
    (hf : ∀ a b z, f a = some z → f b = some z → a = b) :
    ∀ {l l' : List α} {zs : List β}, l.mapM f = some zs → l'.mapM f = some zs → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: l', zs, h1, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h1
    subst h1
    simp only [List.mapM_cons] at h2
    obtain ⟨_, _, g⟩ := bind_some_left h2
    obtain ⟨_, _, g'⟩ := bind_some_left g
    cases g'
  | a :: l, [], zs, h1, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h2
    subst h2
    simp only [List.mapM_cons] at h1
    obtain ⟨_, _, g⟩ := bind_some_left h1
    obtain ⟨_, _, g'⟩ := bind_some_left g
    cases g'
  | a :: l, b :: l', zs, h1, h2 => by
    simp only [List.mapM_cons] at h1 h2
    obtain ⟨x, hx, g1⟩ := bind_some_left h1
    obtain ⟨xs, hxs, g2⟩ := bind_some_left g1
    obtain ⟨y, hy, g3⟩ := bind_some_left h2
    obtain ⟨ys, hys, g4⟩ := bind_some_left g3
    simp only [pure, Option.some.injEq] at g2 g4
    subst g2
    simp only [List.cons.injEq] at g4
    obtain ⟨rfl, rfl⟩ := g4
    rw [hf a b _ hx hy, mapM_inj hf hxs hys]

/-- `denoteN` at a well-formed store, as `mapM_inj` asks. -/
theorem denN_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (a b : NIdx) (z : ConLeche.Name), denoteN st.ns a = some z → denoteN st.ns b = some z → a = b := by
  intro a b z ha hb
  obtain ⟨rk, hrk⟩ := hwf
  exact ConRon.Arena.denoteN_inj hrk.nsWF ha hb

/-- `denoteE` at a well-formed store, as `mapM_inj` asks. -/
theorem denE_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (a b : EIdx) (z : Expr), denoteE st a = some z → denoteE st b = some z → a = b :=
  fun _ _ _ ha hb => ConRon.Arena.denoteE_inj hwf ha hb

/-- A kind's denotation keeps its constructor. -/
theorem kind_tag {st : EStore} {k : CKindF NIdx EIdx} {z : CKindF Name Expr}
    (h : k.mapM (denoteN st.ns) (denoteE st) = some z) : z.tag = k.tag := by
  cases k <;> simp only [CKindF.mapM] at h
  all_goals first
    | (simp only [pure, Option.some.injEq] at h; subst h; rfl)
    | (obtain ⟨_, _, g⟩ := bind_some_left h
       first
         | (simp only [pure, Option.some.injEq] at g; subst g; rfl)
         | (obtain ⟨_, _, g'⟩ := bind_some_left g
            simp only [pure, Option.some.injEq] at g'; subst g'; rfl))

/-- A recursor rule's denotation is injective. -/
theorem rule_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (a b : NIdx × Nat × EIdx) (z : Name × Nat × Expr),
      (do let c ← denoteN st.ns a.1; let e ← denoteE st a.2.2; pure (c, a.2.1, e)) = some z →
      (do let c ← denoteN st.ns b.1; let e ← denoteE st b.2.2; pure (c, b.2.1, e)) = some z →
      a = b := by
  rintro ⟨c, m, e⟩ ⟨c', m', e'⟩ z ha hb
  obtain ⟨x1, g1, ha⟩ := bind_some_left ha
  obtain ⟨x2, g2, ha⟩ := bind_some_left ha
  obtain ⟨y1, g1', hb⟩ := bind_some_left hb
  obtain ⟨y2, g2', hb⟩ := bind_some_left hb
  simp only [pure, Option.some.injEq] at ha hb
  subst ha
  simp only [Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl, rfl⟩ := hb
  rw [denN_inj hwf c c' _ g1 g1', denE_inj hwf e e' _ g2 g2']

/-- **A kind's denotation is injective** at a well-formed store. -/
theorem kind_inj {st : EStore} (hwf : StoreWF st) {k k' : CKindF NIdx EIdx} {z : CKindF Name Expr}
    (h : k.mapM (denoteN st.ns) (denoteE st) = some z)
    (h' : k'.mapM (denoteN st.ns) (denoteE st) = some z) : k = k' := by
  have hN := denN_inj hwf
  have hE := denE_inj hwf
  have ht : k.tag = k'.tag := (kind_tag h).symm.trans (kind_tag h')
  cases k <;> cases k' <;> (try simp [CKindF.tag] at ht) <;>
    simp only [CKindF.mapM] at h h'
  case ax.ax u u' =>
    simp only [pure, Option.some.injEq] at h h'; subst h; cases h'; rfl
  case quot.quot u u' =>
    simp only [pure, Option.some.injEq] at h h'; subst h; cases h'; rfl
  case defn.defn v hs sf v' hs' sf' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    simp only [pure, Option.some.injEq] at g g'; subst g; cases g'
    rw [hE v v' _ hx hy]
  case opaq.opaq v u v' u' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    simp only [pure, Option.some.injEq] at g g'; subst g; cases g'
    rw [hE v v' _ hx hy]
  case thm.thm v all v' all' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨xs, hxs, g1⟩ := bind_some_left g
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    obtain ⟨ys, hys, g1'⟩ := bind_some_left g'
    simp only [pure, Option.some.injEq] at g1 g1'; subst g1; cases g1'
    rw [hE v v' _ hx hy, mapM_inj hN hxs hys]
  case induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨xs, hxs, g1⟩ := bind_some_left g
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    obtain ⟨ys, hys, g1'⟩ := bind_some_left g'
    simp only [pure, Option.some.injEq] at g1 g1'; subst g1; cases g1'
    rw [mapM_inj hN hx hy, mapM_inj hN hxs hys]
  case ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    simp only [pure, Option.some.injEq] at g g'; subst g; cases g'
    rw [hN ind ind' _ hx hy]
  case recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
    obtain ⟨x, hx, g⟩ := bind_some_left h
    obtain ⟨xs, hxs, g1⟩ := bind_some_left g
    obtain ⟨y, hy, g'⟩ := bind_some_left h'
    obtain ⟨ys, hys, g1'⟩ := bind_some_left g'
    simp only [pure, Option.some.injEq] at g1 g1'; subst g1; cases g1'
    rw [mapM_inj hN hx hy, mapM_inj (rule_inj hwf) hxs hys]

/-- **A constant's denotation is injective** at a well-formed store. -/
theorem denoteEntry_inj {st : EStore} (hwf : StoreWF st) {a b : CEntryF NIdx EIdx}
    {z : CEntryF Name Expr} (ha : denoteEntry st a = some z) (hb : denoteEntry st b = some z) :
    a = b := by
  rcases a with ⟨n, l, t, k⟩
  rcases b with ⟨n', l', t', k'⟩
  simp only [denoteEntry, CEntryF.mapM] at ha hb
  obtain ⟨zn, h1, ga⟩ := bind_some_left ha
  obtain ⟨zl, h2, ga⟩ := bind_some_left ga
  obtain ⟨zt, h3, ga⟩ := bind_some_left ga
  obtain ⟨zk, h4, ga⟩ := bind_some_left ga
  obtain ⟨zn', h1', gb⟩ := bind_some_left hb
  obtain ⟨zl', h2', gb⟩ := bind_some_left gb
  obtain ⟨zt', h3', gb⟩ := bind_some_left gb
  obtain ⟨zk', h4', gb⟩ := bind_some_left gb
  simp only [pure, Option.some.injEq] at ga gb
  subst ga
  simp only [CEntryF.mk.injEq] at gb
  obtain ⟨rfl, rfl, rfl, rfl⟩ := gb
  rw [denN_inj hwf n n' _ h1 h1', mapM_inj (denN_inj hwf) h2 h2', denE_inj hwf t t' _ h3 h3',
    kind_inj hwf h4 h4']

/-- `hintsEq` is equality. -/
theorem hintsEq_iff (h h' : ConLeche.Frontend.HintsRec) :
    ConLeche.Frontend.Olean.hintsEq h h' = true ↔ h = h' := by
  cases h <;> cases h' <;> simp [ConLeche.Frontend.Olean.hintsEq]

/-- The twin's `rulesEq` is equality. -/
theorem rulesEqT_iff : ∀ (a b : List (NIdx × Nat × EIdx)),
    ConRon.Arena.Frontend.Olean.rulesEq a b = true ↔ a = b
  | [], [] => by simp [ConRon.Arena.Frontend.Olean.rulesEq]
  | [], _ :: _ => by simp [ConRon.Arena.Frontend.Olean.rulesEq]
  | _ :: _, [] => by simp [ConRon.Arena.Frontend.Olean.rulesEq]
  | (x, y, z) :: as, (x', y', z') :: bs => by
    simp [ConRon.Arena.Frontend.Olean.rulesEq, rulesEqT_iff as bs, and_assoc]

/-- Upstream's `rulesEq` is equality. -/
theorem rulesEqU_iff : ∀ (a b : List (Name × Nat × Expr)),
    ConLeche.Frontend.Olean.rulesEq a b = true ↔ a = b
  | [], [] => by simp [ConLeche.Frontend.Olean.rulesEq]
  | [], _ :: _ => by simp [ConLeche.Frontend.Olean.rulesEq]
  | _ :: _, [] => by simp [ConLeche.Frontend.Olean.rulesEq]
  | (x, y, z) :: as, (x', y', z') :: bs => by
    simp [ConLeche.Frontend.Olean.rulesEq, rulesEqU_iff as bs, and_assoc]

/-- The twin's `entrySame` is equality. -/
theorem entrySameT_iff (a b : CEntryF NIdx EIdx) :
    ConRon.Arena.Frontend.Olean.entrySame a b = true ↔ a = b := by
  rcases a with ⟨n, l, t, k⟩
  rcases b with ⟨n', l', t', k'⟩
  cases k <;> cases k' <;>
    simp [ConRon.Arena.Frontend.Olean.entrySame, hintsEq_iff, rulesEqT_iff, and_assoc]

/-- Upstream's `entrySame` is equality. -/
theorem entrySameU_iff (a b : CEntryF Name Expr) :
    ConLeche.Frontend.Olean.entrySame a b = true ↔ a = b := by
  rcases a with ⟨n, l, t, k⟩
  rcases b with ⟨n', l', t', k'⟩
  cases k <;> cases k' <;>
    simp [ConLeche.Frontend.Olean.entrySame, hintsEq_iff, rulesEqU_iff, and_assoc]

/-- A constant's denotation, field by field. -/
theorem denoteEntry_parts {st : EStore} {a : CEntryF NIdx EIdx} {z : CEntryF Name Expr}
    (h : denoteEntry st a = some z) :
    denoteN st.ns a.name = some z.name ∧ a.levelParams.mapM (denoteN st.ns) = some z.levelParams ∧
      denoteE st a.type = some z.type ∧ a.kind.mapM (denoteN st.ns) (denoteE st) = some z.kind := by
  rcases a with ⟨n, l, t, k⟩
  simp only [denoteEntry, CEntryF.mapM] at h
  obtain ⟨zn, h1, g⟩ := bind_some_left h
  obtain ⟨zl, h2, g⟩ := bind_some_left g
  obtain ⟨zt, h3, g⟩ := bind_some_left g
  obtain ⟨zk, h4, g⟩ := bind_some_left g
  simp only [pure, Option.some.injEq] at g
  subst g
  exact ⟨h1, h2, h3, h4⟩

/-- Two handles compare as their denotations, at a well-formed store. -/
theorem beq_den {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → Option β}
    (hf : ∀ a b z, f a = some z → f b = some z → a = b) {a b : α} {x y : β}
    (ha : f a = some x) (hb : f b = some y) : (a == b) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact hf a b x ha hb

/-- A list's `mapM` compares as its denotation. -/
theorem beq_mapM {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → Option β}
    (hf : ∀ a b z, f a = some z → f b = some z → a = b) {a b : List α} {x y : List β}
    (ha : a.mapM f = some x) (hb : b.mapM f = some y) : (a == b) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact mapM_inj hf ha hb

/-- **`expoOf` reads back**: the twin's verdict on two handle constants is upstream's on their
denotations, at a well-formed store. -/
theorem expoOf_den {st : EStore} (hwf : StoreWF st) {a b : CEntryF NIdx EIdx}
    {aC bC : CEntryF Name Expr} (ha : denoteEntry st a = some aC) (hb : denoteEntry st b = some bC) :
    ConRon.Arena.Frontend.Olean.expoOf a b = ConLeche.Frontend.Olean.expoOf aC bC := by
  have e1 : ConRon.Arena.Frontend.Olean.entrySame a b = ConLeche.Frontend.Olean.entrySame aC bC := by
    rw [Bool.eq_iff_iff, entrySameT_iff, entrySameU_iff]
    constructor
    · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
    · rintro rfl; exact denoteEntry_inj hwf ha hb
  obtain ⟨an, al, at', ak⟩ := denoteEntry_parts ha
  obtain ⟨bn, bl, bt, bk⟩ := denoteEntry_parts hb
  have e2 : (a.name == b.name) = (aC.name == bC.name) := beq_den (denN_inj hwf) an bn
  have e3 : (a.levelParams == b.levelParams) = (aC.levelParams == bC.levelParams) :=
    beq_mapM (denN_inj hwf) al bl
  have e4 : (a.type == b.type) = (aC.type == bC.type) := beq_den (denE_inj hwf) at' bt
  unfold ConRon.Arena.Frontend.Olean.expoOf ConLeche.Frontend.Olean.expoOf
  rw [e1, e2, e3, e4]
  rcases a with ⟨n1, l1, t1, k1⟩
  rcases b with ⟨n2, l2, t2, k2⟩
  rcases aC with ⟨n1', l1', t1', k1'⟩
  rcases bC with ⟨n2', l2', t2', k2'⟩
  simp only at ak bk ⊢
  cases k1 <;> cases k2 <;> simp only [CKindF.mapM] at ak bk <;>
    (repeat (first
      | (obtain ⟨_, _, ak⟩ := bind_some_left ak)
      | (obtain ⟨_, _, bk⟩ := bind_some_left bk))) <;>
    simp only [pure, Option.some.injEq] at ak bk <;> subst ak bk <;> rfl

/-! ## A constant read sparsely -/

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:244-248 sparseExprP — **an expression read
sparsely is the specification's**. -/
theorem sparseExprP_run {pk : OleanPins} {r : Region} {v : UInt64} {s s' : AState}
    (hok : StateOK s) (hpk : NullsRel s.store pk) {x : EIdx}
    (h : ConRon.Arena.Frontend.Olean.sparseExprP pk r v s = .ok (some x, s')) :
    ParseStep s s' ∧ ∃ e, exprP r v = some e ∧ denoteE s'.store x = some e := by
  unfold ConRon.Arena.Frontend.Olean.sparseExprP at h
  unfold exprP
  cases hc : r.loc v with
  | none => simp only [hc] at h; cases (AM.pure_ok h).1
  | some c =>
    simp only [hc] at h
    unfold ConRon.Arena.Frontend.Olean.frontierExpr at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none => cases (AM.pure_ok h2).1
    | some m =>
      obtain ⟨hx, rfl⟩ := AM.pure_ok h2
      obtain ⟨hst, hg, -, -⟩ := sparseGo_run c hok hpk (Or.inr (Or.inr (Or.inl rfl))) (SparseGood.empty _ _)
        (FrontierGood.empty _ _) h1
      obtain ⟨e, h3, h4⟩ := sparseLookup_good hg.exprs (FrontierGood.empty _ r).exprs hx.symm
      exact ⟨hst, e, h3, h4⟩

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:275-296 CKindF.mapM — **a kind read in
`OptionT AM`**, upstream's, read back. -/
theorem kindMap_run {pk : OleanPins} {fn : UInt64 → AM (Option NIdx)} {fe : UInt64 → AM (Option EIdx)}
    {gn : UInt64 → Option ConLeche.Name} {ge : UInt64 → Option Expr}
    (hn : ∀ a s s' y, Ctx pk s → fn a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (he : ∀ a s s' y, Ctx pk s → fe a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, ge a = some z ∧ denoteE s'.store y = some z)
    (k : CKindF UInt64 UInt64) {kr : CKindF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s)
    (h : (k.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) (fun v => OptionT.mk (fe v))) s
      = .ok (some kr, s')) :
    ParseStep s s' ∧ ∃ kC, k.mapM gn ge = some kC ∧
      kr.mapM (denoteN s'.store.ns) (denoteE s'.store) = some kC := by
  cases k with
  | ax u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | quot u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | defn v hh sf =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := he v s _ a hctx h1
    refine ⟨hst, .defn z hh sf, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [CKindF.mapM, hd, bind, Option.bind, pure]
  | opaq v u =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := he v s _ a hctx h1
    refine ⟨hst, .opaq z u, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [CKindF.mapM, hd, bind, Option.bind, pure]
  | thm v all =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨ns, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, z, hz, hd⟩ := he v s _ a hctx h1
    obtain ⟨hst2, zs, hzs, hds⟩ := names_run hn all (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .thm z zs, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hzs, bind, Option.bind, pure]
    · simp [CKindF.mapM, denote_ext hd hst2.ext, hds, bind, Option.bind, pure]
  | induct np ni all cs nn ir iu irf =>
    simp only [CKindF.mapM] at h
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨bs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := names_run hn all hctx h1
    obtain ⟨hst2, ws, hw, hdw⟩ := names_run hn cs (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .induct np ni zs ws nn ir iu irf, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hw, bind, Option.bind, pure]
    · have hd' := mapM_denoteN_ext hst2.ext hd
      simp [CKindF.mapM, hd', hdw, bind, Option.bind, pure]
  | ctor ind ci np nf iu =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := hn ind s _ a hctx h1
    refine ⟨hst, .ctor z ci np nf iu, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [CKindF.mapM, hd, bind, Option.bind, pure]
  | recur all np ni nmo nmi rules kk iu =>
    rw [recur_mapM] at h ⊢
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := names_run hn all hctx h1
    obtain ⟨hst2, ws, hw, hdw⟩ := optT_list_run (pk := pk)
      (den := fun st (x : NIdx × Nat × EIdx) => do
        let c ← denoteN st.ns x.1
        let e ← denoteE st x.2.2
        pure (c, x.2.1, e))
      (g := fun (x : UInt64 × Nat × UInt64) => do
        let c ← gn x.1
        let e ← ge x.2.2
        pure (c, x.2.1, e))
      (fun {st st' y z} hx hy => by
        obtain ⟨c, hc, hy⟩ := bind_some_left hy
        obtain ⟨e, he', hy⟩ := bind_some_left hy
        simp only [denoteN_ext hc hx, denote_ext he' hx]
        exact hy)
      (fun x s s' y hctx hrun => by
        obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok hrun
        obtain ⟨b, s₂, h3, h4⟩ := OT.bind_ok h2
        obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
        obtain ⟨hst1, z, hz, hd⟩ := hn x.1 s _ a hctx h1
        obtain ⟨hst2, w, hw', hdw'⟩ := he x.2.2 s₁ _ b (hctx.step hst1) h3
        exact ⟨hst1.trans hst2, (z, x.2.1, w), by simp [hz, hw', bind, Option.bind, pure],
          by simp [denoteN_ext hd hst2.ext, hdw', bind, Option.bind, pure]⟩) rules (hctx.step hst1) h3
    refine ⟨hst1.trans hst2, .recur zs np ni nmo nmi ws kk iu, ?_, ?_⟩
    · rw [hz, hw]; rfl
    · have hd' := mapM_denoteN_ext hst2.ext hd
      rw [recur_mapM, hd', hdw]; rfl

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM — **a constant read in
`OptionT AM`**, upstream's, read back. -/
theorem entryMapRd_run {pk : OleanPins} {rd : ConRon.Arena.Frontend.Olean.PtrRead}
    {gn : UInt64 → Option ConLeche.Name} {ge : UInt64 → Option Expr}
    (hn : ∀ a s s' y, Ctx pk s → rd.rdName a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (he : ∀ a s s' y, Ctx pk s → rd.rdExpr a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, ge a = some z ∧ denoteE s'.store y = some z)
    (c : CEntryF UInt64 UInt64) {e : CEntryF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.entryMap rd c s = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ z, c.mapM gn ge = some z ∧ denoteEntry s'.store e = some z := by
  unfold ConRon.Arena.Frontend.Olean.entryMap at h
  rcases c with ⟨name, lps, type, kind⟩
  have h' : (CEntryF.mapM (m := OptionT AM) (fun v => OptionT.mk (rd.rdName v))
      (fun v => OptionT.mk (rd.rdExpr v)) ⟨name, lps, type, kind⟩) s = .ok (some e, s') := h
  simp only [CEntryF.mapM] at h'
  obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h'
  obtain ⟨ls, s₂, h3, h4⟩ := OT.bind_ok h2
  obtain ⟨t, s₃, h5, h6⟩ := OT.bind_ok h4
  obtain ⟨k, s₄, h7, h8⟩ := OT.bind_ok h6
  obtain ⟨rfl, rfl⟩ := OT.pure_ok h8
  obtain ⟨hst1, zn, hzn, hdn⟩ := hn name s _ a hctx h1
  obtain ⟨hst2, zl, hzl, hdl⟩ := names_run hn lps (hctx.step hst1) h3
  obtain ⟨hst3, zt, hzt, hdt⟩ := he type s₂ _ t (hctx.step (hst1.trans hst2)) h5
  obtain ⟨hst4, zk, hzk, hdk⟩ := kindMap_run hn he kind (hctx.step ((hst1.trans hst2).trans hst3)) h7
  refine ⟨((hst1.trans hst2).trans hst3).trans hst4, ⟨zn, zl, zt, zk⟩, ?_, ?_⟩
  · simp [CEntryF.mapM, hzn, hzl, hzt, hzk, bind, Option.bind, pure]
  · have x1 := denoteN_ext hdn ((hst2.trans hst3).trans hst4).ext
    have x2 := mapM_denoteN_ext (hst3.trans hst4).ext hdl
    have x3 := denote_ext hdt hst4.ext
    simp [denoteEntry, CEntryF.mapM, x1, x2, x3, hdk, bind, Option.bind, pure]

/-- con-leche: ConLeche/Frontend/Olean/Reads.lean:82-84 entryAt — **a constant read sparsely is
the specification's** (`entryAt_eq`). -/
theorem entryAt_run {pk : OleanPins} {r : Region} {c : Nat} {e : CEntryF NIdx EIdx} {s s' : AState}
    (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.entryAt pk r c s = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ z, ConLeche.Frontend.Olean.entryAt r c = some z ∧ denoteEntry s'.store e = some z := by
  unfold ConRon.Arena.Frontend.Olean.entryAt at h
  rw [ConLeche.Frontend.Olean.entryAt_eq]
  unfold constSpec
  cases hsk : constSkel r c with
  | none => simp only [hsk] at h; cases (AM.pure_ok h).1
  | some sk =>
    simp only [hsk] at h
    obtain ⟨u, s₁, h1, h2⟩ := AM.bind_ok h
    have := skelFits_run h1
    subst this
    unfold ConRon.Arena.Frontend.Olean.sparseEntry at h2
    obtain ⟨hst, z, hz, hd⟩ := entryMapRd_run (gn := nameP r) (ge := exprP r)
      (fun a s s' y hctx hrun => sparseNameP_run hctx.ok hctx.nulls hrun)
      (fun a s s' y hctx hrun => sparseExprP_run hctx.ok hctx.nulls hrun) sk hctx h2
    exact ⟨hst, z, by simpa [bind, Option.bind] using hz, hd⟩

/-! ## The load -/

/-- A lazy load related position by position is a lazy load. -/
theorem lazyOf_of_rel {r : Region} {i : Nat} :
    ∀ {ss : List (CEntryF UInt64 UInt64)} {es : List ConLeche.Frontend.Olean.CEntry},
      ListRel (fun sk e => ConLeche.Frontend.Olean.lazyEntry (nameP r) (exprP r) r i sk =
        some e.toCEntryF) ss es → ConLeche.Frontend.Olean.LazyOf r i ss es
  | [], [], .nil => ⟨by simp, by simp⟩
  | _ :: _, _ :: _, .cons hh ht =>
    let ih := lazyOf_of_rel ht
    ⟨fun s0 hs0 => by
      rcases List.mem_cons.mp hs0 with rfl | hs0
      · exact ⟨_, List.mem_cons_self, hh⟩
      · obtain ⟨x, hx, h⟩ := ih.of_skel s0 hs0
        exact ⟨x, List.mem_cons_of_mem _ hx, h⟩,
     fun e0 he0 => by
      rcases List.mem_cons.mp he0 with rfl | he0
      · exact ⟨_, List.mem_cons_self, hh⟩
      · obtain ⟨x, hx, h⟩ := ih.to_skel e0 he0
        exact ⟨x, List.mem_cons_of_mem _ hx, h⟩⟩

/-- A relation position by position, at each position. -/
theorem listRel_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListRel R l l' →
      ∃ hl : l'.length = l.length, ∀ (j : Nat) (hj : j < l.length), R l[j] (l'[j]'(hl ▸ hj))
  | [], [], .nil => ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | _ :: _, _ :: _, .cons hh ht => by
    obtain ⟨hl, hk⟩ := listRel_getElem ht
    refine ⟨by simp [hl], fun j hj => ?_⟩
    cases j with
    | zero => exact hh
    | succ j => exact hk j (by simpa using hj)

/-- con-leche: ConLeche/Verify/Driver/Loads.lean:950 loadAt_loadOf — **the twin's load of the
home is a load by the specification** (`LoadOf`). -/
theorem loadView_run {pk : OleanPins} {m : NIdx} {mn : ConLeche.Name} {f : ModFiles}
    {l : ConRon.Arena.Frontend.Olean.Loaded} {s s' : AState}
    (hctx : Ctx pk s) (hp : PinsRel s.store pk) (hm : denoteN s.store.ns m = some mn)
    (h : ConRon.Arena.Frontend.Olean.loadView pk 0 m f s = .ok (l, s')) :
    ParseStep s s' ∧ FrontGoodAt s'.store f l.frontier ∧
      ∃ lC, LoadedRel s'.store l lC ∧ ConLeche.Driver.LoadOf 0 mn f lC := by
  unfold ConRon.Arena.Frontend.Olean.loadView at h
  obtain ⟨o, s₄, h7, h8⟩ := AM.bind_ok h
  cases o with
  | none =>
    obtain ⟨e, s₅, -, h9⟩ := AM.bind_ok h8
    obtain ⟨e', s₆, -, h10⟩ := AM.bind_ok h9
    exact absurd (AM.fail_ok h10) (by simp)
  | some l'' =>
  obtain ⟨hv, hs⟩ := AM.pure_ok h8
  cases hv
  subst hs
  obtain ⟨hst, hfg, lC, hrel, hn, -, hfr, r, a, sk, skels, hvr, hcno, hsk, hskels, hal, imports,
    himps, hpre⟩ := loadAt_runOf hctx hp hm h7
  obtain ⟨hl, hk⟩ := listRel_getElem hal
  refine ⟨hst, hfg, lC, hrel, ⟨r, a, sk, skels, hvr, hcno, hsk, hskels, hn, ?_, lazyOf_of_rel hal⟩,
    ⟨r, a, sk, skels, hvr, hsk, hskels, by simpa using hl, fun j hj => ?_⟩,
    r, a, sk, imports, hvr, hsk, himps, hpre⟩
  · rw [hfr]; exact ConLeche.Frontend.Olean.Frontier.good_empty r
  · have := hk j hj
    simpa using this

/-! ## The exported level of the private constants -/

open ConLeche.Frontend.Olean (Expo)

/-- Two position indexes built over the same positions answer alike at keys that agree. -/
theorem foldIdx_get {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [BEq β] [Hashable β]
    [LawfulBEq β] {x : α} {y : β} :
    ∀ (n m : Nat) (_ : n = m) (kT : (i : Nat) → i < n → α) (kU : (i : Nat) → i < m → β),
      (∀ i (h1 : i < n) (h2 : i < m), kT i h1 = x ↔ kU i h2 = y) →
      (n.fold (fun i h (acc : Std.HashMap α Nat) => acc.insert (kT i h) i) {})[x]? =
        (m.fold (fun i h (acc : Std.HashMap β Nat) => acc.insert (kU i h) i) {})[y]? := by
  rintro n m rfl
  induction n with
  | zero => intro _ _ _; simp
  | succ n ih =>
    intro kT kU hk
    rw [Nat.fold_succ, Nat.fold_succ, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    have e := hk n (by omega) (by omega)
    by_cases h1 : kT n (by omega) = x
    · have h2 := e.mp h1
      simp [h1, h2]
    · have h2 : ¬ kU n (by omega) = y := fun h => h1 (e.mpr h)
      simp only [beq_iff_eq, h1, h2, ↓reduceIte]
      exact ih _ _ (fun i a b => hk i (by omega) (by omega))

/-- An array's `mapM`, at each position. -/
theorem mapM_getElem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {zs : List β}, l.mapM f = some zs →
      ∃ hl : zs.length = l.length, ∀ (j : Nat) (hj : j < l.length), f l[j] = some (zs[j]'(hl ▸ hj))
  | [], zs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | a :: l, zs, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨z, hz, g⟩ := bind_some_left h
    obtain ⟨zs', hzs, g⟩ := bind_some_left g
    simp only [pure, Option.some.injEq] at g
    subst g
    obtain ⟨hl, hk⟩ := mapM_getElem hzs
    refine ⟨by simp [hl], fun j hj => ?_⟩
    cases j with
    | zero => exact hz
    | succ j => exact hk j (by simpa using hj)

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:106-152 expoOfParts — **the twin's loop over
the exported constants is upstream's `for`**, step by step, every step from a state `s₀` moved
to. -/
theorem expoLoop_run {pk : OleanPins} {r : Region} {privLoc : Std.HashMap Nat Nat}
    {privIdx : Std.HashMap NIdx Nat} {privLocs : Array Nat} {cs : Array (CEntryF NIdx EIdx)}
    {f : Nat → Array Expo → Except String (ForInStep (Array Expo))} {s₀ : AState} :
    ∀ (l : List Nat),
      (∀ c ∈ l, ∀ i expo, privLoc[c]? = some i → f c expo = .ok (.yield (expo.set! i .same))) →
      (∀ c ∈ l, privLoc[c]? = none → ∀ expo s s₁ expo₁, ParseStep s₀ s →
        ConRon.Arena.Frontend.Olean.expoStep pk r privIdx privLocs cs expo c s =
          .ok (.ok expo₁, s₁) → ParseStep s s₁ ∧ f c expo = .ok (.yield expo₁)) →
      ∀ expo {s s' : AState} {e : Array Expo}, ParseStep s₀ s →
        ConRon.Arena.Frontend.Olean.expoLoop pk r privLoc privIdx privLocs cs l expo s =
          .ok (.ok e, s') →
        ParseStep s s' ∧ forIn l expo f = .ok e
  | [], _, _, expo, s, s', e, h0, h => by
    rw [ConRon.Arena.Frontend.Olean.expoLoop] at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    exact ⟨ParseStep.refl h0.ok, rfl⟩
  | c :: l, hsame, hstep, expo, s, s', e, h0, h => by
    rw [ConRon.Arena.Frontend.Olean.expoLoop] at h
    rw [List.forIn_cons]
    cases hp : privLoc[c]? with
    | some i =>
      simp only [hp] at h
      obtain ⟨hst, hl⟩ := expoLoop_run l (fun c' hc' => hsame c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hstep c' (List.mem_cons_of_mem _ hc')) _ h0 h
      refine ⟨hst, ?_⟩
      rw [hsame c List.mem_cons_self i expo hp]
      exact hl
    | none =>
      simp only [hp] at h
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
      cases o with
      | error m => cases (AM.pure_ok h2).1
      | ok expo₁ =>
        simp only at h2
        obtain ⟨hst1, hf⟩ := hstep c List.mem_cons_self hp expo s s₁ expo₁ h0 h1
        obtain ⟨hst2, hl⟩ := expoLoop_run l (fun c' hc' => hsame c' (List.mem_cons_of_mem _ hc'))
          (fun c' hc' => hstep c' (List.mem_cons_of_mem _ hc')) _ (h0.trans hst1) h2
        refine ⟨hst1.trans hst2, ?_⟩
        rw [hf]
        exact hl

/-- `expoLoop_run`, the `for`'s value bound and returned, as upstream's `do` has it. -/
theorem expoLoop_run' {pk : OleanPins} {r : Region} {privLoc : Std.HashMap Nat Nat}
    {privIdx : Std.HashMap NIdx Nat} {privLocs : Array Nat} {cs : Array (CEntryF NIdx EIdx)}
    {l : List Nat} {expo : Array Expo} {s s' : AState} {e : Array Expo}
    {f : Nat → Array Expo → Except String (ForInStep (Array Expo))} (hctx : StateOK s)
    (h : ConRon.Arena.Frontend.Olean.expoLoop pk r privLoc privIdx privLocs cs l expo s =
      .ok (.ok e, s'))
    (hsame : ∀ c ∈ l, ∀ i expo, privLoc[c]? = some i → f c expo = .ok (.yield (expo.set! i .same)))
    (hstep : ∀ c ∈ l, privLoc[c]? = none → ∀ expo s₁ s₂ expo₁, ParseStep s s₁ →
      ConRon.Arena.Frontend.Olean.expoStep pk r privIdx privLocs cs expo c s₁ =
        .ok (.ok expo₁, s₂) → ParseStep s₁ s₂ ∧ f c expo = .ok (.yield expo₁)) :
    ParseStep s s' ∧ (forIn l expo f >>= fun x => pure x) = .ok e := by
  obtain ⟨hst, hf⟩ := expoLoop_run (s₀ := s) l hsame hstep expo (ParseStep.refl hctx) h
  exact ⟨hst, by rw [hf]; rfl⟩

/-- An `if` of the twin that answers, by its condition. -/
theorem ite_ok_cases {α : Type} {c : Prop} [Decidable c] {A B : AM α} {s : AState}
    {r : Except Arena.CheckError (α × AState)} (h : (if c then A else B) s = r) :
    (c ∧ A s = r) ∨ (¬c ∧ B s = r) := by
  by_cases hc : c
  · exact .inl ⟨hc, by simpa [hc] using h⟩
  · exact .inr ⟨hc, by simpa [hc] using h⟩

/-- An `if` of upstream's, by its condition. -/
theorem ite_goal {α : Type} {c : Prop} [Decidable c] {A B r : α} (h1 : c → A = r)
    (h2 : ¬c → B = r) : (if c then A else B) = r := by
  by_cases hc : c
  · simp [hc, h1 hc]
  · simp [hc, h2 hc]

/-- A theorem's kind, or not. -/
theorem kind_thm_or {N E : Type} (k : CKindF N E) : (∃ v a, k = .thm v a) ∨ ∀ v a, k ≠ .thm v a := by
  cases k <;> simp

/-- A constant read back is a theorem exactly where its denotation is. -/
theorem den_thm_iff {st : EStore} {a : CEntryF NIdx EIdx} {aC : CEntryF Name Expr}
    (h : denoteEntry st a = some aC) : a.kind.tag = aC.kind.tag :=
  (kind_tag (denoteEntry_parts h).2.2.2).symm

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:106-152 expoOfParts — **the twin's exported
level of the private constants is upstream's**, over the load's constants read back. -/
theorem expoOfParts_run {pk : OleanPins} {r : Region} {pa ea : UInt64}
    {csT : Array (CEntryF NIdx EIdx)} {csU : Array (CEntryF Name Expr)}
    {s s' : AState} {expo : Array Expo} (hctx : Ctx pk s)
    (hcs : csT.toList.mapM (denoteEntry s.store) = some csU.toList)
    (h : ConRon.Arena.Frontend.Olean.expoOfParts pk r pa ea csT s = .ok (.ok expo, s')) :
    ParseStep s s' ∧ ConLeche.Frontend.Olean.expoOfParts r pa ea csU = .ok expo := by
  obtain ⟨hlT, hgT⟩ := mapM_getElem hcs
  have hszT : csT.size = csU.size := by simpa using hlT.symm
  unfold ConRon.Arena.Frontend.Olean.expoOfParts at h
  cases hP : moduleSkel r pa with
  | none => simp only [hP] at h; cases (AM.pure_ok h).1
  | some skP =>
  simp only [hP] at h
  cases hE : moduleSkel r ea with
  | none => simp only [hE] at h; cases (AM.pure_ok h).1
  | some skE =>
  simp only [hE] at h
  unfold ConLeche.Frontend.Olean.expoOfParts
  simp only [hP, hE]
  have hmap : csU.map (fun _ => Expo.absent) = csT.map (fun _ => Expo.absent) := by
    apply Array.ext
    · simp [hszT]
    · intro i _ _; simp
  rw [hmap]
  refine expoLoop_run' hctx.ok h ?_ ?_
  · intro c _ i expo hp
    simp only [hp]
    rfl
  · intro c _ hpl expo s0 s1 expo1 hst0 hrun
    have hctx0 : Ctx pk s0 := hctx.step hst0
    simp only [hpl]
    unfold ConRon.Arena.Frontend.Olean.expoStep at hrun
    cases hse : constSkel r c with
    | none => simp only [hse] at hrun; cases (AM.pure_ok hrun).1
    | some se =>
    simp only [hse] at hrun ⊢
    obtain ⟨o, s₁, h1, hA⟩ := AM.bind_ok hrun
    cases o with
    | none => cases (AM.pure_ok hA).1
    | some en =>
    obtain ⟨hst1, enC, henC, hden⟩ := nameP_run hctx0.ok hctx0.nulls h1
    simp only [henC]
    obtain ⟨enName, s₂, h2, hB⟩ := AM.bind_ok hA
    obtain ⟨hs2, -⟩ := readName_run h2
    rw [hs2] at hB
    have hctx1 : Ctx pk s₁ := hctx0.step hst1
    have hx1 : Ext s.store s₁.store := (hst0.trans hst1).ext
    -- the private constant of the exported one's name
    cases hi : (csT.size.fold (fun i h (acc : Std.HashMap NIdx Nat) => acc.insert csT[i].name i)
        {})[en]? with
    | none => simp only [hi] at hB; cases (AM.pure_ok hB).1
    | some i =>
    have hiU : (csU.size.fold (fun i h (acc : Std.HashMap Name Nat) => acc.insert csU[i].name i)
        {})[enC]? = some i := by
      rw [← hi]
      symm
      refine foldIdx_get _ _ hszT _ _ (fun j h1 h2 => ?_)
      have hdj := hgT j (by simpa using h1)
      simp only [Array.getElem_toList] at hdj
      have hn := (denoteEntry_parts (denoteEntry_ext hx1 hdj)).1
      constructor
      · rintro rfl
        exact Option.some.inj (hn.symm.trans hden)
      · intro he
        rw [he] at hn
        exact denN_inj hctx1.ok.wf _ _ _ hn hden
    simp only [hi] at hB
    simp only [hiU]
    cases hsp : (skP.consts.toArray[i]?).bind (constSkel r) with
    | none => simp only [hsp] at hB; cases (AM.pure_ok hB).1
    | some sp =>
    simp only [hsp] at hB ⊢
    obtain ⟨loc, hloc, -⟩ := bind_some_left hsp
    rcases ite_ok_cases hB with ⟨hc, hB⟩ | ⟨hc, hB⟩
    · obtain ⟨hv, rfl⟩ := AM.pure_ok hB
      cases hv
      refine ⟨hst1, ite_goal (fun _ => rfl) (fun hu => ?_)⟩
      exfalso
      revert hc hu
      cases se.kind <;> cases sp.kind <;> simp
    · obtain ⟨o, s₃, h3, hC⟩ := AM.bind_ok hB
      cases o with
      | none => cases (AM.pure_ok hC).1
      | some e =>
      obtain ⟨hst3, eC, heC, hde⟩ := entryAt_run hctx1 h3
      simp only at hC
      cases hpc : csT[i]? with
      | none => simp only [hpc] at hC; cases (AM.pure_ok hC).1
      | some pc =>
      simp only [hpc] at hC
      obtain ⟨hiT, rfl⟩ := Array.getElem?_eq_some_iff.mp hpc
      have hiU' : i < csU.size := by omega
      have hdi := hgT i (by simpa using hiT)
      simp only [Array.getElem_toList] at hdi
      have hctx3 : Ctx pk s₃ := hctx1.step hst3
      have htag := den_thm_iff hdi
      have hlocs : skP.consts.toArray[i]! = loc := by
        rw [getElem!_pos skP.consts.toArray i (Array.getElem?_eq_some_iff.mp hloc).1]
        exact (Array.getElem?_eq_some_iff.mp hloc).2
      rcases kind_thm_or csT[i].kind with ⟨v, a, hk⟩ | hk
      · -- a theorem: its whole constant read off the file
        rw [hk] at hC htag
        obtain ⟨v', a', hkU⟩ := tag_thm htag.symm
        simp only at hC
        obtain ⟨o, s₄, h4, hD⟩ := AM.bind_ok hC
        cases o with
        | none => cases (AM.pure_ok hD).1
        | some pc2 =>
        simp only at hD
        rw [hlocs] at h4
        obtain ⟨hst4, pc2C, hpc2C, hdpc2⟩ := entryAt_run hctx3 h4
        have hexpo := expoOf_den (hctx3.step hst4).ok.wf hdpc2 (denoteEntry_ext hst4.ext hde)
        unfold ConRon.Arena.Frontend.Olean.expoAgainst at hD
        rw [hexpo] at hD
        cases hx : ConLeche.Frontend.Olean.expoOf pc2C eC with
        | none => rw [hx] at hD; cases (AM.pure_ok hD).1
        | some x =>
        rw [hx] at hD
        obtain ⟨hv, rfl⟩ := AM.pure_ok hD
        cases hv
        refine ⟨(hst1.trans hst3).trans hst4, ?_⟩
        refine ite_goal (fun hu => ?_) (fun _ => ?_)
        · exfalso
          revert hc hu
          cases se.kind <;> cases sp.kind <;> simp
        simp only [heC]
        rw [getElem!_pos csU i hiU']
        simp only [hkU, hloc, Option.bind, hpc2C]
        simp [hx] <;> rfl
      · -- any other constant: the load's
        have hkU : ∀ v a, csU[i].kind ≠ .thm v a := by
          intro v a he
          rw [he] at htag
          obtain ⟨v', a', hv⟩ := tag_thm htag
          exact hk v' a' hv
        replace hC : (pure (ConRon.Arena.Frontend.Olean.expoAgainst csT[i] e enName i expo) :
            AM _) s₃ = .ok (.ok expo1, s1) := by
          cases hkk : csT[i].kind <;> simp only [hkk] at hC
          all_goals first | exact hC | exact absurd hkk (hk _ _)
        have hexpo := expoOf_den hctx3.ok.wf (denoteEntry_ext (hx1.trans hst3.ext) hdi) hde
        unfold ConRon.Arena.Frontend.Olean.expoAgainst at hC
        rw [hexpo] at hC
        cases hx : ConLeche.Frontend.Olean.expoOf csU[i] eC with
        | none => rw [hx] at hC; cases (AM.pure_ok hC).1
        | some x =>
        rw [hx] at hC
        obtain ⟨hv, rfl⟩ := AM.pure_ok hC
        cases hv
        refine ⟨hst1.trans hst3, ?_⟩
        refine ite_goal (fun hu => ?_) (fun _ => ?_)
        · exfalso
          revert hc hu
          cases se.kind <;> cases sp.kind <;> simp
        simp only [heC]
        rw [getElem!_pos csU i hiU']
        split
        · rename_i v a he
          exact absurd he (hkU v a)
        · simp [hx] <;> rfl

/-! ## A read that does not answer, read back -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode — the tail of a name that does
not read. -/
theorem nameTail_none {s s' : AState} {r : Region} {g t : Nat} {p : NIdx}
    (hrun : ConRon.Arena.Frontend.Olean.nameTail r g t p s = .ok (none, s')) :
    (t = 1 → r.strP g (r.fld g 1) = none) ∧ (t ≠ 1 → r.natP g (r.fld g 1) = none) := by
  unfold ConRon.Arena.Frontend.Olean.nameTail at hrun
  by_cases ht : t = 1
  · subst ht
    simp only [BEq.rfl, ↓reduceIte] at hrun
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    cases hs : r.strP g (r.fld g 1) with
    | none => rfl
    | some str =>
      simp only [hs] at hrun
      obtain ⟨y, s₁, -, hrest⟩ := AM.bind_ok hrun
      cases (AM.pure_ok hrest).1
  · have hb : (t == 1) = false := by simpa using ht
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hrun
    refine ⟨fun h => absurd h ht, fun _ => ?_⟩
    cases hn : r.natP g (r.fld g 1) with
    | none => rfl
    | some i =>
      simp only [hn] at hrun
      obtain ⟨k, s₁, -, hrest⟩ := AM.bind_ok hrun
      obtain ⟨y, s₂, -, hrest⟩ := AM.bind_ok hrest
      cases (AM.pure_ok hrest).1

/-- The tail of a name that does not read leaves the state. -/
theorem nameTail_none_eq {s s' : AState} {r : Region} {g t : Nat} {p : NIdx}
    (hrun : ConRon.Arena.Frontend.Olean.nameTail r g t p s = .ok (none, s')) : s' = s := by
  unfold ConRon.Arena.Frontend.Olean.nameTail at hrun
  by_cases ht : t = 1
  · subst ht
    simp only [BEq.rfl, ↓reduceIte] at hrun
    cases hs : r.strP g (r.fld g 1) with
    | none => simp only [hs] at hrun; exact (AM.pure_ok hrun).2
    | some str =>
      simp only [hs] at hrun
      obtain ⟨y, s₁, -, hrest⟩ := AM.bind_ok hrun
      cases (AM.pure_ok hrest).1
  · have hb : (t == 1) = false := by simpa using ht
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hrun
    cases hn : r.natP g (r.fld g 1) with
    | none => simp only [hn] at hrun; exact (AM.pure_ok hrun).2
    | some i =>
      simp only [hn] at hrun
      obtain ⟨k, s₁, -, hrest⟩ := AM.bind_ok hrun
      obtain ⟨y, s₂, -, hrest⟩ := AM.bind_ok hrest
      cases (AM.pure_ok hrest).1

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:211-213 nameAt — **a name that does not read
for the twin does not for upstream**, the state moved as a read moves it. -/
theorem nameAt_none {r : Region} {pk : OleanPins} : ∀ (g : Nat) {s s' : AState},
    StateOK s → NullsRel s.store pk →
    ConRon.Arena.Frontend.Olean.nameAt pk r g s = .ok (none, s') →
    ParseStep s s' ∧ ConLeche.Frontend.Olean.nameAt r g = none := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
    intro s s' hok hpk hrun
    rw [ConRon.Arena.Frontend.Olean.nameAt] at hrun
    rw [ConLeche.Frontend.Olean.nameAt, ConLeche.Frontend.Olean.nameNode]
    generalize hF : (if r.fits g = true then _ else _ : AM (Option NIdx)) = f at hrun
    by_cases hf : r.fits g = true
    · simp only [hf, ↓reduceIte] at hF ⊢
      by_cases hc : ((r.tag g == 1 || r.tag g == 2) && r.nobjs g == 2) = true
      · simp only [hc, ↓reduceIte] at hF
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
        obtain ⟨htt, hn⟩ := hc
        have htail : ∀ {y : NIdx} {t : AState},
            ConRon.Arena.Frontend.Olean.nameTail r g (r.tag g) y t = .ok (none, s') →
            (match r.tag g, r.nobjs g with
              | 1, 2 => (do
                  let p ← r.nameIn g (r.fld g 0) fun c _ => ConLeche.Frontend.Olean.nameAt r c
                  let s ← r.strP g (r.fld g 1)
                  pure (ConLeche.Name.str p s))
              | 2, 2 => (do
                  let p ← r.nameIn g (r.fld g 0) fun c _ => ConLeche.Frontend.Olean.nameAt r c
                  let i ← r.natP g (r.fld g 1)
                  pure (ConLeche.Name.num p i))
              | _, _ => none) = none := by
          intro y t htl
          obtain ⟨h1, h2⟩ := nameTail_none htl
          rcases htt with ht | ht
          · simp [ht, hn, h1 ht]
          · have : r.tag g ≠ 1 := by omega
            simp [ht, hn, h2 this]
        have hpre : r.nameIn g (r.fld g 0) (fun c _ => ConLeche.Frontend.Olean.nameAt r c) = none →
            (match r.tag g, r.nobjs g with
              | 1, 2 => (do
                  let p ← r.nameIn g (r.fld g 0) fun c _ => ConLeche.Frontend.Olean.nameAt r c
                  let s ← r.strP g (r.fld g 1)
                  pure (ConLeche.Name.str p s))
              | 2, 2 => (do
                  let p ← r.nameIn g (r.fld g 0) fun c _ => ConLeche.Frontend.Olean.nameAt r c
                  let i ← r.natP g (r.fld g 1)
                  pure (ConLeche.Name.num p i))
              | _, _ => none) = none := by
          intro hq
          rcases htt with ht | ht <;> simp [ht, hn, hq]
        by_cases hv : (r.fld g 0 == 1) = true
        · simp only [hv, ↓reduceIte] at hF
          subst hF
          have he := nameTail_none_eq hrun
          subst he
          exact ⟨ParseStep.refl hok, htail hrun⟩
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hF
          have hv' : ¬ r.fld g 0 = 1 := by simpa using hv
          split at hF
          · rename_i heq
            subst hF
            obtain ⟨-, rfl⟩ := AM.pure_ok hrun
            refine ⟨ParseStep.refl hok, hpre ?_⟩
            simp only [ConLeche.Frontend.Olean.Region.nameIn, hv', beq_iff_eq, ↓reduceIte]
            split
            · rename_i c' heq'
              rw [heq] at heq'
              cases heq'
            · rfl
          · rename_i c heq
            subst hF
            obtain ⟨o, s₁, hat, hrest⟩ := AM.bind_ok hrun
            cases o with
            | none =>
              obtain ⟨hst, hc'⟩ := ih c (ConLeche.Frontend.Olean.Region.down_lt heq) hok hpk hat
              obtain ⟨-, rfl⟩ := AM.pure_ok hrest
              refine ⟨hst, hpre ?_⟩
              simp only [ConLeche.Frontend.Olean.Region.nameIn, hv', beq_iff_eq, ↓reduceIte]
              split
              · rename_i c' heq'
                rw [heq] at heq'
                cases heq'
                exact hc'
              · rfl
            | some p =>
              obtain ⟨hst, -⟩ := nameAt_run c hok hpk hat
              rw [nameTail_none_eq hrest]
              exact ⟨hst, htail hrest⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
        subst hF
        obtain ⟨-, rfl⟩ := AM.pure_ok hrun
        refine ⟨ParseStep.refl hok, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, not_and] at hc
        split
        · rename_i h1 h2; exact absurd h2 (hc (.inl h1))
        · rename_i h1 h2; exact absurd h2 (hc (.inr h1))
        · rfl
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hF
      subst hF
      obtain ⟨-, rfl⟩ := AM.pure_ok hrun
      exact ⟨ParseStep.refl hok, by simp [hf]⟩

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:231-236 nameP -/
theorem nameP_none {r : Region} {pk : OleanPins} {v : UInt64} {s s' : AState}
    (hok : StateOK s) (hpk : NullsRel s.store pk)
    (hrun : ConRon.Arena.Frontend.Olean.nameP pk r v s = .ok (none, s')) :
    ParseStep s s' ∧ nameP r v = none := by
  unfold ConRon.Arena.Frontend.Olean.nameP at hrun
  unfold nameP
  by_cases hv : (v == 1) = true
  · simp only [hv, ↓reduceIte] at hrun
    cases (AM.pure_ok hrun).1
  · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hrun ⊢
    cases hl : r.loc v with
    | none =>
      simp only [hl] at hrun
      obtain ⟨-, rfl⟩ := AM.pure_ok hrun
      exact ⟨ParseStep.refl hok, rfl⟩
    | some c =>
      simp only [hl] at hrun
      exact nameAt_none c hok hpk hrun

/-- An `OptionT AM` bind that does not answer: its first action does not, or its second. -/
theorem OT.bind_none {α β : Type} {x : OptionT AM α} {f : α → OptionT AM β} {s s' : AState}
    (h : (x >>= f) s = .ok (none, s')) :
    x s = .ok (none, s') ∨ ∃ a s₁, x s = .ok (some a, s₁) ∧ f a s₁ = .ok (none, s') := by
  have h' : (Bind.bind (m := AM) (x : AM (Option α)) (fun (o : Option α) => match o with
      | some a => (f a : AM (Option β))
      | none => (pure none : AM (Option β)))) s = .ok (none, s') := h
  obtain ⟨o, s₁, hx, hrest⟩ := AM.bind_ok h'
  cases o with
  | none =>
    obtain ⟨-, rfl⟩ := AM.pure_ok hrest
    exact .inl hx
  | some a => exact .inr ⟨a, s₁, hx, hrest⟩

/-- `pure` in `OptionT AM` answers. -/
theorem pure_some_ne {α : Type} {a : α} {s s' : AState}
    (h : (pure a : OptionT AM α) s = .ok (none, s')) : False := by
  have h' : (pure (some a) : AM (Option α)) s = .ok (none, s') := h
  cases (AM.pure_ok h').1

/-- A list read in `OptionT AM` that does not answer: neither does upstream's, each step
answering as upstream's or not at all as upstream's. -/
theorem optT_list_none {α β γ : Type} {pk : OleanPins} {den : EStore → β → Option γ}
    {f : α → OptionT AM β} {g : α → Option γ}
    (hstep : ∀ a s s' y, Ctx pk s → f a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, g a = some z ∧ den s'.store y = some z)
    (hnone : ∀ a s s', Ctx pk s → f a s = .ok (none, s') → ParseStep s s' ∧ g a = none) :
    ∀ (l : List α) {s s' : AState}, Ctx pk s →
      l.mapM f s = .ok (none, s') → ParseStep s s' ∧ l.mapM g = none
  | [], s, s', _, h => by
    simp only [List.mapM_nil] at h
    exact (pure_some_ne h).elim
  | x :: l, s, s', hctx, h => by
    simp only [List.mapM_cons] at h ⊢
    rcases OT.bind_none h with h1 | ⟨a, s₁, h1, h2⟩
    · obtain ⟨hst, hn⟩ := hnone x s s' hctx h1
      exact ⟨hst, by simp [hn]⟩
    · obtain ⟨hst, z, hz, -⟩ := hstep x s s₁ a hctx h1
      rcases OT.bind_none h2 with h3 | ⟨as, s₂, -, h4⟩
      · obtain ⟨hst2, hn⟩ := optT_list_none hstep hnone l (hctx.step hst) h3
        exact ⟨hst.trans hst2, by simp [hz, hn]⟩
      · exact (pure_some_ne h4).elim

/-- One import read in `OptionT AM`: upstream's, read back. -/
theorem importMap_run {pk : OleanPins} {r : Region} (i : ImportF UInt64) {y : ImportF NIdx}
    {s s' : AState} (hctx : Ctx pk s)
    (h : (i.mapM (m := OptionT AM) fun v => OptionT.mk (ConRon.Arena.Frontend.Olean.nameP pk r v)) s =
      .ok (some y, s')) :
    ParseStep s s' ∧ ∃ z, ImportF.mapM (nameP r) i = some z ∧ denoteImport s'.store y = some z := by
  simp only [ImportF.mapM] at h
  obtain ⟨n, s₁, h1, h2⟩ := OT.bind_ok h
  obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
  obtain ⟨hst, z, hz, hd⟩ := nameP_run hctx.ok hctx.nulls h1
  exact ⟨hst, { i with module := z }, by simp [ImportF.mapM, hz, bind, Option.bind, pure],
    by simp [denoteImport, ImportF.mapM, hd, bind, Option.bind, pure]⟩

/-- One import that does not read: neither does upstream's. -/
theorem importMap_none {pk : OleanPins} {r : Region} (i : ImportF UInt64) {s s' : AState}
    (hctx : Ctx pk s)
    (h : (i.mapM (m := OptionT AM) fun v => OptionT.mk (ConRon.Arena.Frontend.Olean.nameP pk r v)) s =
      .ok (none, s')) :
    ParseStep s s' ∧ ImportF.mapM (nameP r) i = none := by
  simp only [ImportF.mapM] at h
  rcases OT.bind_none h with h1 | ⟨a, s₁, -, h2⟩
  · obtain ⟨hst, hn⟩ := nameP_none hctx.ok hctx.nulls h1
    exact ⟨hst, by simp [ImportF.mapM, hn, bind, Option.bind]⟩
  · exact (pure_some_ne h2).elim

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn — the imports that do not
read. -/
theorem importsIn_none {pk : OleanPins} {r : Region} {c : Nat} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.importsIn pk r c s = .ok (none, s')) :
    ConLeche.Frontend.Olean.importsIn r c = none := by
  unfold ConRon.Arena.Frontend.Olean.importsIn at h
  unfold ConLeche.Frontend.Olean.importsIn
  by_cases h1 : (r.tag c == ConLeche.Frontend.Olean.tagArray) = true
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : c + 24 + 8 * (ConLeche.Frontend.Olean.rdU64 r.bytes (c + 8)).toNat ≤ r.fileEnd c
    · simp only [h2, ↓reduceIte] at h
      simp only [Array.mkEmpty_eq] at h ⊢
      cases himps : r.objArrayGo c (c + 24) (ConLeche.Frontend.Olean.rdU64 r.bytes (c + 8)).toNat 0
          #[] with
      | none => simp [h1, h2, bind, Option.bind]
      | some imps =>
        simp only [himps] at h
        unfold ConRon.Arena.Frontend.Olean.importsRead at h
        have h' : (imps.mapM (m := OptionT AM) fun i => do
            let sk ← OptionT.mk (pure (ConLeche.Frontend.Olean.importSkel r i))
            sk.mapM (m := OptionT AM) fun v => OptionT.mk (ConRon.Arena.Frontend.Olean.nameP pk r v)) s
            = .ok (none, s') := h
        rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h'
        rcases OT.bind_none h' with h3 | ⟨ys, s₁, -, h4⟩
        · have hn := optT_list_none (pk := pk) (den := denoteImport)
            (g := fun i => ConLeche.Frontend.Olean.importSkel r i >>= ImportF.mapM (nameP r))
            (fun i s s' y hctx hrun => by
              obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok hrun
              obtain ⟨hv, hs⟩ := AM.pure_ok h1
              have hsk : ConLeche.Frontend.Olean.importSkel r i = some a := by
                cases hsk : ConLeche.Frontend.Olean.importSkel r i with
                | none => rw [hsk] at hv; cases hv
                | some b => rw [hsk] at hv; cases hv; rfl
              subst hs
              obtain ⟨hst, z, hz, hd⟩ := importMap_run a hctx h2
              exact ⟨hst, z, by rw [hsk]; exact hz, hd⟩)
            (fun i s s' hctx hrun => by
              rcases OT.bind_none hrun with h1 | ⟨a, s₁, h1, h2⟩
              · obtain ⟨hv, rfl⟩ := AM.pure_ok h1
                cases hsk : ConLeche.Frontend.Olean.importSkel r i with
                | none => exact ⟨ParseStep.refl hctx.ok, by simp [bind, Option.bind]⟩
                | some b => rw [hsk] at hv; cases hv
              · obtain ⟨hv, hs1⟩ := AM.pure_ok h1
                have hsk : ConLeche.Frontend.Olean.importSkel r i = some a := by
                  cases hsk : ConLeche.Frontend.Olean.importSkel r i with
                  | none => rw [hsk] at hv; cases hv
                  | some b => rw [hsk] at hv; cases hv; rfl
                subst hs1
                obtain ⟨hst, hn⟩ := importMap_none a hctx h2
                exact ⟨hst, by simp [hsk, hn, bind, Option.bind]⟩) imps.toList hctx h3
          simp [h1, h2, Array.mapM_eq_mapM_toList]
          exact hn.2
        · exact (pure_some_ne h4).elim
    · simp only [h2, ↓reduceIte] at h
      simp [h1, h2, bind, Option.bind]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    simp [h1, bind, Option.bind]

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:75-83 importsPre — no imports off the start of
the file for the twin, none for upstream. -/
theorem importsPre_none {pk : OleanPins} {b : ByteArray} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.importsPre pk b s = .ok (none, s')) :
    ConLeche.Frontend.Olean.importsPre b = none := by
  generalize hF : ConRon.Arena.Frontend.Olean.importsPre pk b = fn at h
  unfold ConRon.Arena.Frontend.Olean.importsPre at hF
  unfold ConLeche.Frontend.Olean.importsPre
  split at hF
  · rename_i c e hw
    subst hF
    simp only [hw]
    exact importsIn_none hctx h
  · rename_i hw
    split
    · rename_i c e hw'
      exact absurd hw' (hw c e)
    · rfl

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:156-190 checkViews — the server part's imports
as upstream reads them, `simps`. -/
@[expose] def simpsOf (r : Region) (a : UInt64) : Option (Array ImportRec) :=
  (moduleSkel r a).bind fun sk => (sk.imports.mapM (ImportF.mapM (nameP r))).map List.toArray

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:156-190 checkViews — **the server part's imports
read back**: upstream's `simps`. -/
theorem skelImports_run {pk : OleanPins} {r : Region} {a : UInt64}
    {xs : Array (ImportF NIdx)} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.skelImports pk r a s = .ok (some xs, s')) :
    ParseStep s s' ∧ ∃ zs, simpsOf r a = some zs ∧
      xs.toList.mapM (denoteImport s'.store) = some zs.toList := by
  unfold ConRon.Arena.Frontend.Olean.skelImports at h
  unfold simpsOf
  cases hsk : moduleSkel r a with
  | none =>
    simp only [hsk] at h
    cases (AM.pure_ok h).1
  | some sk =>
  simp only [hsk] at h
  have h' : (sk.imports.mapM (m := OptionT AM) (fun i => i.mapM (m := OptionT AM)
      fun v => OptionT.mk (ConRon.Arena.Frontend.Olean.nameP pk r v)) >>= fun l =>
        (pure l.toArray : OptionT AM (Array (ImportF NIdx)))) s = .ok (some xs, s') := h
  obtain ⟨l, s₁, h1, h2⟩ := OT.bind_ok h'
  obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
  obtain ⟨hst, zs, hzs, hd⟩ := optT_list_run (pk := pk) (den := denoteImport)
    (g := ImportF.mapM (nameP r)) (fun hx hy => denoteImport_ext hx hy)
    (fun i s s' y hctx hrun => importMap_run i hctx hrun) sk.imports hctx h1
  refine ⟨hst, zs.toArray, ?_, by simpa using hd⟩
  simp [hzs]

/-- The server part's imports that do not read move the state as a read does. -/
theorem skelImports_none {pk : OleanPins} {r : Region} {a : UInt64} {s s' : AState} (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.skelImports pk r a s = .ok (none, s')) : ParseStep s s' := by
  unfold ConRon.Arena.Frontend.Olean.skelImports at h
  cases hsk : moduleSkel r a with
  | none =>
    simp only [hsk] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ParseStep.refl hctx.ok
  | some sk =>
  simp only [hsk] at h
  have h' : (sk.imports.mapM (m := OptionT AM) (fun i => i.mapM (m := OptionT AM)
      fun v => OptionT.mk (ConRon.Arena.Frontend.Olean.nameP pk r v)) >>= fun l =>
        (pure l.toArray : OptionT AM (Array (ImportF NIdx)))) s = .ok (none, s') := h
  rcases OT.bind_none h' with h1 | ⟨l, s₁, -, h2⟩
  · exact (optT_list_none (pk := pk) (den := denoteImport) (g := ImportF.mapM (nameP r))
      (fun i s s' y hctx hrun => importMap_run i hctx hrun)
      (fun i s s' hctx hrun => importMap_none i hctx hrun) sk.imports hctx h1).1
  · exact (pure_some_ne h2).elim

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:156-190 checkViews — **the server part's imports
are those at the start of `M.olean`**, upstream's check, where the start of `M.olean` holds
imports (as the home's load found). -/
theorem serverImportsOk_run {pk : OleanPins} {r : Region} {f : ModFiles} {a : UInt64}
    {s s' : AState} (hctx : Ctx pk s) {pre : Array ImportRec}
    (hpre : ConLeche.Frontend.Olean.importsPre f.exported.bytes = some pre)
    (h : ConRon.Arena.Frontend.Olean.serverImportsOk pk r f a s = .ok (true, s')) :
    ParseStep s s' ∧ (ConLeche.Frontend.Olean.importsPre f.exported.bytes == simpsOf r a) = true := by
  unfold ConRon.Arena.Frontend.Olean.serverImportsOk ConRon.Arena.Frontend.Olean.importsAgree at h
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨p, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hb, rfl⟩ := AM.pure_ok h4
  cases p with
  | none =>
    have hst1 : ParseStep s s₁ := by
      cases o with
      | none => exact skelImports_none hctx h1
      | some xs => exact (skelImports_run hctx h1).1
    exact absurd (importsPre_none (hctx.step hst1) h3) (by rw [hpre]; simp)
  | some p =>
  cases o with
  | none => simp at hb
  | some xs =>
  have he : p = xs := by simpa using hb.symm
  subst he
  obtain ⟨hst1, ws, hws, hdw⟩ := skelImports_run hctx h1
  obtain ⟨hst2, zs, hzs, hdz⟩ := importsPre_run (hctx.step hst1) h3
  refine ⟨hst1.trans hst2, ?_⟩
  rw [hzs, hws, imports_den_eq hdz (list_mono (fun _ _ hy => denoteImport_ext hst2.ext hy) _ hdw)]
  simp

/-! ## The views against each other -/

/-- The load's constants, read back. -/
theorem loadedEntries_den {st : EStore} :
    ∀ {l : List ConRon.Arena.Frontend.Olean.CEntry} {lC : List ConLeche.Frontend.Olean.CEntry},
      l.mapM (denoteCEntry st) = some lC →
      (l.map (·.c)).mapM (denoteEntry st) = some (lC.map (·.toCEntryF))
  | [], lC, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | x :: l, lC, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨z, hz, g⟩ := bind_some_left h
    obtain ⟨zs, hzs, g⟩ := bind_some_left g
    simp only [pure, Option.some.injEq] at g
    subst g
    unfold denoteCEntry at hz
    obtain ⟨e, he, hz⟩ := bind_some_left hz
    obtain ⟨u, -, hz⟩ := bind_some_left hz
    simp only [pure, Option.some.injEq] at hz
    subst hz
    simp only [List.map_cons, List.mapM_cons, he, loadedEntries_den hzs]
    rfl

/-- A failing branch of the twin: a few reads, then `fail`. -/
theorem fail_tail {α β γ δ : Type} {x : AM α} {y : α → AM β} {e : β → Arena.CheckError}
    {k : γ → AM δ} {s s' : AState} {r : δ}
    (h : (x >>= fun a => y a >>= fun b => (fail (e b) : AM γ) >>= k) s = .ok (r, s')) : False := by
  obtain ⟨_, _, _, h1⟩ := AM.bind_ok h
  obtain ⟨_, _, _, h2⟩ := AM.bind_ok h1
  obtain ⟨_, _, h3, _⟩ := AM.bind_ok h2
  exact AM.fail_ok h3

/-- A failing branch of the twin: a read, then `fail`. -/
theorem fail_tail1 {β γ δ : Type} {y : AM β} {e : β → Arena.CheckError}
    {k : γ → AM δ} {s s' : AState} {r : δ}
    (h : (y >>= fun b => (fail (e b) : AM γ) >>= k) s = .ok (r, s')) : False := by
  obtain ⟨_, _, _, h2⟩ := AM.bind_ok h
  obtain ⟨_, _, h3, _⟩ := AM.bind_ok h2
  exact AM.fail_ok h3

/-- A `pure` first step of the twin. -/
theorem pure_seq_ok {α β : Type} {a : α} {f : α → AM β} {s : AState}
    {r : Except Arena.CheckError (β × AState)} (h : ((pure a : AM α) >>= f) s = r) : f a s = r := h

/-- A failing last branch of the twin: a read, then `fail`. -/
theorem fail_tail0 {β γ : Type} {y : AM β} {e : β → Arena.CheckError} {s s' : AState} {r : γ}
    (h : (y >>= fun b => (fail (e b) : AM γ)) s = .ok (r, s')) : False := by
  obtain ⟨_, _, _, h2⟩ := AM.bind_ok h
  exact AM.fail_ok h2

/-- A constant array over two arrays of one size. -/
theorem map_const_eq {α β γ : Type} {a : Array α} {b : Array β} (x : γ) (h : a.size = b.size) :
    a.map (fun _ => x) = b.map (fun _ => x) := by
  apply Array.ext
  · simp [h]
  · intro i _ _; simp

/-- con-leche: ConLeche/Frontend/Olean/Module.lean:156-190 checkViews — **the twin's check of a
module's views, over its load, is upstream's**, at the load read back. -/
theorem checkViews_run {pk : OleanPins} {m : NIdx} {mC : Name} {f : ModFiles}
    {l : ConRon.Arena.Frontend.Olean.Loaded} {lC : ConLeche.Frontend.Olean.Loaded}
    {expo : Array Expo} {s s' : AState} {pre : Array ImportRec} (hctx : Ctx pk s)
    (hl : LoadedRel s.store l lC)
    (hpre : ConLeche.Frontend.Olean.importsPre f.exported.bytes = some pre)
    (h : ConRon.Arena.Frontend.Olean.checkViews pk m f l s = .ok (expo, s')) :
    ParseStep s s' ∧ ConLeche.Frontend.Olean.checkViews mC f lC = .ok expo := by
  have hcs : (ConRon.Arena.Frontend.Olean.loadedEntries l.constants).toList.mapM
      (denoteEntry s.store) = some (lC.constants.map (·.toCEntryF)).toList := by
    simpa [ConRon.Arena.Frontend.Olean.loadedEntries] using loadedEntries_den hl.constants
  have hsz : (ConRon.Arena.Frontend.Olean.loadedEntries l.constants).size =
      (lC.constants.map (·.toCEntryF)).size := by
    have := (mapM_getElem hcs).1
    simpa using this.symm
  unfold ConRon.Arena.Frontend.Olean.checkViews at h
  unfold ConLeche.Frontend.Olean.checkViews
  obtain ⟨ex, fs, fp⟩ := f
  cases fs with
  | none =>
    simp only at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    subst hv
    refine ⟨ParseStep.refl hctx.ok, ?_⟩
    simp only
    rw [map_const_eq Expo.same hsz]
    rfl
  | some sv =>
  cases fp with
  | none =>
    simp only at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    subst hv
    refine ⟨ParseStep.refl hctx.ok, ?_⟩
    simp only
    rw [map_const_eq Expo.same hsz]
    rfl
  | some pv =>
  simp only at h
  cases hm : ModFiles.isModule ⟨ex, some sv, some pv⟩ with
  | false =>
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    subst hv
    refine ⟨ParseStep.refl hctx.ok, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [map_const_eq Expo.same hsz]
    rfl
  | true =>
  simp only [hm, ↓reduceIte] at h
  replace h := pure_seq_ok h
  cases hr : ConLeche.Frontend.Olean.Region.ofParts #[ex, sv, pv] with
  | error e =>
    simp only [hr] at h
    exact absurd h (fun h' => AM.fail_ok h')
  | ok r =>
  simp only [hr] at h
  rcases ite_ok_cases h with ⟨hloc, h⟩ | ⟨-, h⟩
  rotate_left
  · exact (fail_tail h).elim
  replace h := pure_seq_ok h
  rcases ite_ok_cases h with ⟨hS, h⟩ | ⟨-, h⟩
  rotate_left
  · exact (fail_tail1 h).elim
  replace h := pure_seq_ok h
  rcases ite_ok_cases h with ⟨hP, h⟩ | ⟨-, h⟩
  rotate_left
  · exact (fail_tail1 h).elim
  replace h := pure_seq_ok h
  obtain ⟨b1, s₁, h1, h⟩ := AM.bind_ok h
  cases b1 with
  | false => exact (fail_tail1 h).elim
  | true =>
  simp only [↓reduceIte] at h
  replace h := pure_seq_ok h
  obtain ⟨hst1, himps⟩ := serverImportsOk_run hctx hpre h1
  obtain ⟨b2, s₂, h2, h⟩ := AM.bind_ok h
  cases b2 with
  | false => exact (fail_tail1 h).elim
  | true =>
  simp only [↓reduceIte] at h
  replace h := pure_seq_ok h
  obtain ⟨hst2, hcn1⟩ := constNamesOk_run (hctx.step hst1) h2
  obtain ⟨b3, s₃, h3, h⟩ := AM.bind_ok h
  cases b3 with
  | false => exact (fail_tail1 h).elim
  | true =>
  simp only [↓reduceIte] at h
  replace h := pure_seq_ok h
  have hst12 := hst1.trans hst2
  obtain ⟨hst3, hcn2⟩ := constNamesOk_run (hctx.step hst12) h3
  have hst123 := hst12.trans hst3
  obtain ⟨e1, s₄, h4, h⟩ := AM.bind_ok h
  obtain ⟨e2, s₅, h5, h⟩ := AM.bind_ok h
  have hcs3 := list_mono (fun _ _ hy => denoteEntry_ext hst123.ext hy) _ hcs
  cases e1 with
  | error msg => exact (fail_tail0 h).elim
  | ok ex1 =>
  cases e2 with
  | error msg => exact (fail_tail0 h).elim
  | ok ex2 =>
  obtain ⟨hv, rfl⟩ := AM.pure_ok h
  subst hv
  obtain ⟨hst4, hU1⟩ := expoOfParts_run (hctx.step hst123) hcs3 h4
  obtain ⟨hst5, hU2⟩ := expoOfParts_run (hctx.step (hst123.trans hst4))
    (list_mono (fun _ _ hy => denoteEntry_ext hst4.ext hy) _ hcs3) h5
  refine ⟨(hst123.trans hst4).trans hst5, ?_⟩
  unfold ConRon.Arena.Frontend.Olean.skelIsModule at hS hP
  unfold simpsOf at himps
  simp [hr, hloc, hS, hP, himps, hcn1, hcn2, hU1, hU2, bind, Except.bind]
  rfl

/-! ## The home -/

/-- con-leche: ConLeche/Verify/Driver/Worker.lean WorkerFacts.home — **the worker's home at the
twin is upstream's**: the private part's files read off the snapshot, their private view a load
by the specification (`LoadOf`), its views' check upstream's accept, the load read back, its
frontier good on the files' region. -/
theorem homeHyp_holds : HomeHyp := by
  intro pk F sp s s₁ s' m mC f l expo hsp hctx hpins hm hrf hhome
  cases hr : ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp mC .private with
  | error e =>
    simp only [hr, ConRon.Arena.Frontend.Olean.liftE] at hrf
    exact (AM.fail_ok hrf).elim
  | ok f' =>
  simp only [hr, ConRon.Arena.Frontend.Olean.liftE] at hrf
  obtain ⟨hv, rfl⟩ := AM.pure_ok hrf
  subst hv
  have hgives := readFiles_sim (roots_ok_of_bare hsp) rfl hr
  unfold ConRon.Arena.Modular.homeOf at hhome
  obtain ⟨l', s₂, h1, hA⟩ := AM.bind_ok hhome
  obtain ⟨expo', s₃, h2, hB⟩ := AM.bind_ok hA
  obtain ⟨hv, rfl⟩ := AM.pure_ok hB
  cases hv
  obtain ⟨hst1, hfg, lC, hrel, hload⟩ := loadView_run hctx hpins hm h1
  obtain ⟨-, -, ⟨r, a, sk, imports, -, -, -, hpre⟩⟩ := id hload
  obtain ⟨hst2, hcv⟩ := checkViews_run (mC := mC) (hctx.step hst1) hrel hpre h2
  exact ⟨hst1.trans hst2, lC, expo, hgives, hload, hcv, hrel.ext hst2.ext, hfg.ext hst2.ext⟩

end ConRon.Bridge.Modular.Home
