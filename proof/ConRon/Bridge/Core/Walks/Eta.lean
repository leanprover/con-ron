/-
# `ConRon.Bridge.Core.Walks.Eta` — the structure-η certificate's sub-walks

Task #97-P3-Core round 6.  `structEtaCertWith` (`Walks/Stuck.lean`) and
the η rescue of `majorToCtor` read two walks; they are here, each an equation
with con-leche's function of the same name:

| walk | twin | con-leche |
|---|---|---|
| `towerSlotsAll_spec` | `Arena/Core.lean` (`towerSlotsAllGo`) | `Kernel/CoreDefs.lean` |
| `etaProjs_spec` | `Arena/Core.lean` (`projNodesGo`) | `Kernel/CoreDefs.lean:723` |

(Task #119: con-leche's task #342 retired `recSlotsAll`,
`structEtaProjCerts` and the projection-FUNCTION fallback of `etaProjs` —
every slot of an η family the checker uses is a table entry — and their
Theorem-1 walks went with them.)

con-leche writes the slot walk as `(List.range nF).all`/`.map`; the twin's
counted recursions (DESIGN §3.4) are identified with `(List.range' j n)` at
their running index `j`, and `List.range_eq_range'` closes the gap at
`j = 0`.
-/
import ConRon.Bridge.Core.Walks.StrCtor
import ConRon.Bridge.Core.Walks.StrLit

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Small facts about the denotations -/

/-- con-leche: none — two denoting name-handle lists are equal exactly when
their denotations are (the store interns names injectively). -/
theorem denoteNList_eq_iff {st : EStore} (hwf : StoreWF st)
    {as bs : List NIdx} {xs ys : List ConLeche.Name}
    (ha : Frontend.denoteNList st.ns as = some xs)
    (hb : Frontend.denoteNList st.ns bs = some ys) : as = bs ↔ xs = ys := by
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact denoteNList_inj hwf as bs xs ha hb

/-- con-leche: none — a snoc of denoting handles denotes the snoc. -/
theorem denoteEList_snoc {st : EStore} :
    ∀ (l : List EIdx) (es : List Expr) (b : EIdx) (y : Expr),
      Frontend.denoteEList st l = some es → denoteE st b = some y →
      Frontend.denoteEList st (l ++ [b]) = some (es ++ [y])
  | [], es, b, y, h, hb => by
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp [Frontend.denoteEList, hb]
  | a :: as, es, b, y, h, hb => by
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.cons_append, Frontend.denoteEList, ha,
          denoteEList_snoc as xs b y has hb]

/-- con-leche: none — a concatenation of denoting handle lists denotes the
concatenation. -/
theorem denoteEList_appendC {st : EStore} :
    ∀ (l m : List EIdx) (es fs : List Expr),
      Frontend.denoteEList st l = some es → Frontend.denoteEList st m = some fs →
      Frontend.denoteEList st (l ++ m) = some (es ++ fs)
  | [], m, es, fs, h, hm => by
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h; simpa using hm
  | a :: as, m, es, fs, h, hm => by
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.cons_append, Frontend.denoteEList, ha,
          denoteEList_appendC as m xs fs has hm]

/-- con-leche: none — a stored recursor denotes a recursor, and nothing else
does. -/
theorem denoteCI_rec_iff {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) :
    (∃ v mI rP rs, ci = .recInfo v mI rP rs) ↔
      ∃ cv mI rP rules, c = .recInfo cv mI rP rules := by
  cases ci <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; simp)
    | (split at h
       · rename_i heq1 heq2; cases h; simp
       · simp at h)

/-- con-leche: none — an indexed recursor is an environment recursor, with
the denoted constant value. -/
theorem optCI_rec_some {st : EStore} {oc' : Option ConstantInfo}
    {v : IConstantVal} {mI rP : Nat} {rs : List IRecRule}
    (hrel : OptCI st (some (.recInfo v mI rP rs)) oc') :
    ∃ cv rules, Frontend.denoteCV st v = some cv ∧
      oc' = some (.recInfo cv mI rP rules) := by
  obtain ⟨c, hci, rfl⟩ := hrel
  simp only [Frontend.denoteCI] at hci
  split at hci
  · rename_i cv rules hcv _
    cases hci
    exact ⟨cv, rules, hcv, rfl⟩
  · simp at hci

/-- con-leche: none — and nothing else the index holds is a recursor. -/
theorem optCI_rec_none {st : EStore} {oc : Option IConstantInfo}
    {oc' : Option ConstantInfo} (hrel : OptCI st oc oc')
    (hnot : ∀ v mI rP rs, oc ≠ some (.recInfo v mI rP rs)) :
    ∀ cv mI rP rules, oc' ≠ some (.recInfo cv mI rP rules) := by
  intro cv mI rP rules h
  subst h
  cases oc with
  | none => simp only [OptCI] at hrel; cases hrel
  | some ci =>
    obtain ⟨c, hci, hc⟩ := hrel
    cases hc
    obtain ⟨v, mI', rP', rs, rfl⟩ :=
      (denoteCI_rec_iff hci).mpr ⟨cv, mI, rP, rules, rfl⟩
    exact hnot v mI' rP' rs rfl

/-! ## 2. The slot walk -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — **THEOREM
1 for the counted recursion `towerSlotsAllGo`**, at its running index. -/
theorem towerSlotsAllGo_spec (T : NIdx) (Tn : ConLeche.Name) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn →
      ⦃fun s => s = s₀⦄ ConRon.Arena.towerSlotsAllGo fe T n j
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          r = (List.range' j n).all (fun k => (env.findProj? Tn k).isSome); ⊤⦄
  | 0, j, s₀, hok, _ => by
    vcgen [ConRon.Arena.towerSlotsAllGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, by simp⟩
  | n + 1, j, s₀, hok, hT => by
    unfold ConRon.Arena.towerSlotsAllGo
    refine triple_seq (IFEnv.findProj?_spec s₀ T j Tn hok hT) ?_
    rintro o s1 ⟨hok1, hx1, _, _, hp1, hsome, hnone⟩
    have hiff : o.isSome = (env.findProj? Tn j).isSome := by
      cases o with
      | none => rw [hnone rfl]; rfl
      | some e => obtain ⟨p, _, hp⟩ := hsome e rfl; rw [hp]; rfl
    split
    next ho =>
      refine triple_mono (towerSlotsAllGo_spec T Tn n (j + 1) s1 hok1
        (denoteN_ext hT hx1)) ?_
      rintro r s2 ⟨hok2, hx2, hp2, hr⟩
      refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
      rw [hr, List.range'_succ, List.all_cons, ← hiff, ho, Bool.true_and]
    next ho =>
      vcgen
      bridge_peel; subst_vars
      refine ⟨hok1, hx1, hp1, ?_⟩
      have hf : (env.findProj? Tn j).isSome = false := by
        rw [← hiff]; simpa using ho
      rw [List.range'_succ, List.all_cons, hf, Bool.false_and]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — **THEOREM
1 for `towerSlotsAll`**: an equation with con-leche's slot walk. -/
theorem towerSlotsAll_spec (s₀ : AState) (T : NIdx) (Tn : ConLeche.Name)
    (nF : Nat) (hok : CheckOK mode env fe s₀)
    (hT : denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.towerSlotsAll fe T nF
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.towerSlotsAll env Tn nF; ⊤⦄ := by
  unfold ConRon.Arena.towerSlotsAll
  refine triple_mono (towerSlotsAllGo_spec T Tn nF 0 s₀ hok hT) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  rw [h4, ConLeche.towerSlotsAll, List.range_eq_range']

/-! ## 3. The fabricated projections -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:730-736 etaProjs — **THEOREM 1
for the `.proj` half**, the counted recursion `projNodesGo`. -/
theorem projNodesGo_spec (T : NIdx) (b : EIdx) (Tn : ConLeche.Name)
    (y : Expr) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteE s₀.store b = some y →
      ⦃fun s => s = s₀⦄ ConRon.Arena.projNodesGo T b n j
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r =
            some ((List.range' j n).map fun k => Expr.proj Tn k y); ⊤⦄
  | 0, j, s₀, hok, _, _ => by
    vcgen [ConRon.Arena.projNodesGo]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, rfl⟩
  | n + 1, j, s₀, hok, hT, hb => by
    unfold ConRon.Arena.projNodesGo
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s₀ (.proj T j b) hok (viewOK_proj (nview_isSome_of_denote hT)
        (by rw [hb]; rfl))) ?_
    rintro p s1 ⟨hok1, hx1, hp1, hp⟩
    have hp' : denoteE s1.store p = some (.proj Tn j y) := by
      rw [hp]
      simp only [denoteEView, denoteN_ext hT hx1, denote_ext hb hx1, opt2]
    refine triple_seq (projNodesGo_spec T b Tn y n (j + 1) s1 hok1
      (denoteN_ext hT hx1) (denote_ext hb hx1)) ?_
    rintro rest s2 ⟨hok2, hx2, hp2, hrest⟩
    vcgen
    bridge_peel; subst_vars
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [List.range'_succ, List.map_cons]
    simp only [Frontend.denoteEList, denote_ext hp' hx2, hrest]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:723-724 etaProjs — **THEOREM 1
for `etaProjs`**: the handles the twin fabricates denote con-leche's list. -/
theorem etaProjs_spec (s₀ : AState) (T : NIdx) (b : EIdx) (nF : Nat)
    (Tn : ConLeche.Name) (y : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hb : denoteE s₀.store b = some y) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaProjs T b nF
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaProjs Tn y nF); ⊤⦄ := by
  unfold ConRon.Arena.etaProjs
  refine triple_mono (projNodesGo_spec T b Tn y nF 0 s₀ hok hT hb) ?_
  rintro r s' ⟨hok', hx', hp', hr⟩
  refine ⟨hok', hx', hp', ?_⟩
  rw [hr, ConLeche.etaProjs, List.range_eq_range']

/-- con-leche: none — the fabricated projections are well-scoped wherever
the stuck side is. -/
theorem etaProjs_WScoped {d : Nat} {Tn : ConLeche.Name} {y : Expr} {nF : Nat}
    (hwy : Expr.WScoped d y) :
    ∀ p ∈ ConLeche.etaProjs Tn y nF, Expr.WScoped d p := by
  intro p hp
  unfold ConLeche.etaProjs at hp
  simp only [List.mem_map] at hp
  obtain ⟨k, _, rfl⟩ := hp
  simp only [Expr.WScoped]; exact hwy

/-! ## 4. The axiom census -/

section Census

#print axioms denoteNList_inj
#print axioms optCI_rec_some
#print axioms optCI_rec_none
#print axioms towerSlotsAll_spec
#print axioms projNodesGo_spec
#print axioms etaProjs_spec
#print axioms etaProjs_WScoped

end Census

end ConRon.Bridge.Core
