/-
# `ConRon.Bridge.Promote.WalkDecl` — the declaration layer's promotion, run forwards

`Arena/Promote.lean`'s record walk, field for field, over
`Bridge/Promote/Walk.lean`'s four handle-kind cores (task #97-P3-Promote).
Every lemma has the cores' shape — the invariant and the memo survive, the
arena only grows, the answer is persistent, and it denotes whatever the
subject denoted — at the `Arena/Frontend/Readback.lean` denotation of its
record.

One thing is added at the projection table: `denoteProjTable` drops
`tableName` (con-leche recomputes it), so the denotation cannot say what the
promotion did to it.  `PromotedTable` says it: the shape fields the index
invariant `IProjTableOK` reads are unchanged, and both name handles denote
what they denoted.  That is what carries `IProjTableOK` — hence `IFEnvOK`'s
`proj` clause — across the promotion (`IProjTableOK.promoted`).
-/
import ConRon.Bridge.Promote.Walk

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The lists -/

theorem promoteNList_step {fuel : Nat} : ∀ (ns : List NIdx) {m m' : PMemo}
    {ns' : List NIdx} {s s' : AState},
    StoreWF' s.store → PMemoOK m s.store →
    promoteNList m fuel ns s = .ok ((m', ns'), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      PersNList ns' ∧ ns'.length = ns.length ∧
      (∀ xs, Frontend.denoteNList s.store.ns ns = some xs →
        Frontend.denoteNList s'.store.ns ns' = some xs) := by
  intro ns
  induction ns with
  | nil =>
    intro m m' ns' s s' hwf hm hrun
    simp only [promoteNList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, Ext.refl _, fun _ h => absurd h (by simp), rfl, fun _ h => h⟩
  | cons n ns ih =>
    intro m m' ns' s s' hwf hm hrun
    simp only [promoteNList] at hrun
    obtain ⟨⟨m1, n1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hd1⟩ := promoteN_step hwf hm h1
    obtain ⟨⟨m2, ns2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, hl2, hd2⟩ := ih hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ?_, by simp [hl2], ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hp1
      · exact hp2 c hc
    · intro xs hxs
      simp only [Frontend.denoteNList] at hxs ⊢
      cases ha : denoteN s.store.ns n with
      | none => rw [ha] at hxs; simp at hxs
      | some a =>
        cases has : Frontend.denoteNList s.store.ns ns with
        | none => rw [ha, has] at hxs; simp at hxs
        | some as =>
          rw [ha, has] at hxs
          simp only [Option.some.injEq] at hxs
          subst hxs
          have h1' : denoteN s'.store.ns n1 = some a := hx2.lss.ls.ns _ _ (hd1 a ha)
          have h2' := hd2 as (denoteNList_ext hx1.lss.ls.ns ns as has)
          rw [h1', h2']

theorem promoteEList_step {fuel : Nat} : ∀ (es : List EIdx) {m m' : PMemo}
    {es' : List EIdx} {s s' : AState},
    StoreWF' s.store → PMemoOK m s.store →
    promoteEList m fuel es s = .ok ((m', es'), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      PersEList es' ∧ es'.length = es.length ∧
      (∀ xs, Frontend.denoteEList s.store es = some xs →
        Frontend.denoteEList s'.store es' = some xs) := by
  intro es
  induction es with
  | nil =>
    intro m m' es' s s' hwf hm hrun
    simp only [promoteEList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, Ext.refl _, fun _ h => absurd h (by simp), rfl, fun _ h => h⟩
  | cons e es ih =>
    intro m m' es' s s' hwf hm hrun
    simp only [promoteEList] at hrun
    obtain ⟨⟨m1, e1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hp1, hd1⟩ := promoteE_core fuel m e s m1 e1 s1 hwf hm h1
    have hx1 := (promoteE_aext m fuel e s (m1, e1) s1 h1).ext
    obtain ⟨⟨m2, es2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, hl2, hd2⟩ := ih hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ?_, by simp [hl2], ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hp1
      · exact hp2 c hc
    · intro xs hxs
      simp only [Frontend.denoteEList] at hxs ⊢
      cases ha : denoteE s.store e with
      | none => rw [ha] at hxs; simp at hxs
      | some a =>
        cases has : Frontend.denoteEList s.store es with
        | none => rw [ha, has] at hxs; simp at hxs
        | some as =>
          rw [ha, has] at hxs
          simp only [Option.some.injEq] at hxs
          subst hxs
          rw [hx2.expr _ _ (hd1 a ha), hd2 as (denoteEList_ext hx1 es as has)]

/-! ## The constant header -/

theorem promoteCV_step {m m' : PMemo} {fuel : Nat} {cv cv' : IConstantVal}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteCV m fuel cv s = .ok ((m', cv'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersCV cv' ∧
      (∀ x, denoteN s.store.ns cv.name = some x → denoteN s'.store.ns cv'.name = some x) ∧
      (∀ c, Frontend.denoteCV s.store cv = some c →
        Frontend.denoteCV s'.store cv' = some c) := by
  simp only [promoteCV] at hrun
  obtain ⟨⟨m1, n1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hwf1, hm1, hx1, hp1, hd1⟩ := promoteN_step hwf hm h1
  obtain ⟨⟨m2, l2⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hwf2, hm2, hx2, hp2, -, hd2⟩ := promoteNList_step _ hwf1 hm1 h3
  obtain ⟨⟨m3, t3⟩, s3, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨hwf3, hm3, hp3, hd3⟩ := promoteE_core fuel m2 _ s2 m3 t3 s3 hwf2 hm2 h5
  have hx3 := (promoteE_aext m2 fuel _ s2 (m3, t3) s3 h5).ext
  obtain ⟨hr, rfl⟩ := AM.pure_ok h6
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have hN : ∀ x, denoteN s.store.ns cv.name = some x → denoteN s'.store.ns n1 = some x :=
    fun x hx => (hx2.trans hx3).lss.ls.ns _ _ (hd1 x hx)
  refine ⟨hwf3, hm3, (hx1.trans hx2).trans hx3, ⟨hp1, hp2, hp3⟩, hN, ?_⟩
  intro c hc
  simp only [Frontend.denoteCV] at hc ⊢
  cases hn : denoteN s.store.ns cv.name with
  | none => rw [hn] at hc; simp at hc
  | some n =>
    cases hl : Frontend.denoteNList s.store.ns cv.levelParams with
    | none => rw [hn, hl] at hc; simp at hc
    | some lps =>
      cases ht : denoteE s.store cv.type with
      | none => rw [hn, hl, ht] at hc; simp at hc
      | some ty =>
        rw [hn, hl, ht] at hc
        have hl3 : Frontend.denoteNList s'.store.ns l2 = some lps :=
          denoteNList_ext hx3.lss.ls.ns _ _
            (hd2 lps (denoteNList_ext hx1.lss.ls.ns _ _ hl))
        have ht3 : denoteE s'.store t3 = some ty :=
          hd3 ty ((hx1.trans hx2).expr _ _ ht)
        rw [hN n hn, hl3, ht3]
        exact hc

/-! ## Recursor rules, capabilities, projection tables -/

theorem promoteFire_step {m m' : PMemo} {fuel : Nat} {f f' : IRecRuleFire}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteFire m fuel f s = .ok ((m', f'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersFire f' ∧
      (∀ c, Frontend.denoteFire s.store f = some c →
        Frontend.denoteFire s'.store f' = some c) := by
  cases f with
  | inert =>
    simp only [promoteFire] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, Ext.refl _, trivial, fun _ h => h⟩
  | plain =>
    simp only [promoteFire] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, Ext.refl _, trivial, fun _ h => h⟩
  | nested lvls pins =>
    simp only [promoteFire] at hrun
    obtain ⟨⟨m1, l1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, -, hd1⟩ := promoteLList_step lvls hwf hm h1
    obtain ⟨⟨m2, p2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, -, hd2⟩ := promoteEList_step pins hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩, ?_⟩
    intro c hc
    simp only [Frontend.denoteFire] at hc ⊢
    cases hl : denoteLList s.store.ls lvls with
    | none => rw [hl] at hc; simp at hc
    | some ls =>
      cases hp : Frontend.denoteEList s.store pins with
      | none => rw [hl, hp] at hc; simp at hc
      | some ps =>
        rw [hl, hp] at hc
        have e1 : denoteLList s'.store.ls l1 = some ls := denoteLList_ext hx2.lss.ls _ _ (hd1 ls hl)
        have e2 : Frontend.denoteEList s'.store p2 = some ps := hd2 ps (denoteEList_ext hx1 _ _ hp)
        rw [e1, e2]
        exact hc

theorem promoteRule_step {m m' : PMemo} {fuel : Nat} {rl rl' : IRecRule}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteRule m fuel rl s = .ok ((m', rl'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersRule rl' ∧
      (∀ c, Frontend.denoteRule s.store rl = some c →
        Frontend.denoteRule s'.store rl' = some c) := by
  simp only [promoteRule] at hrun
  obtain ⟨⟨m1, c1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hwf1, hm1, hx1, hp1, hd1⟩ := promoteN_step hwf hm h1
  obtain ⟨⟨m2, f2⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hwf2, hm2, hx2, hp2, hd2⟩ := promoteFire_step hwf1 hm1 h3
  obtain ⟨⟨m3, r3⟩, s3, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨hwf3, hm3, hp3, hd3⟩ := promoteE_core fuel m2 _ s2 m3 r3 s3 hwf2 hm2 h5
  have hx3 := (promoteE_aext m2 fuel _ s2 (m3, r3) s3 h5).ext
  obtain ⟨hr, rfl⟩ := AM.pure_ok h6
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨hwf3, hm3, (hx1.trans hx2).trans hx3, ⟨hp1, hp2, hp3⟩, ?_⟩
  intro c hc
  simp only [Frontend.denoteRule] at hc ⊢
  cases hn : denoteN s.store.ns rl.ctor with
  | none => rw [hn] at hc; simp at hc
  | some n =>
    cases hf : Frontend.denoteFire s.store rl.fire with
    | none => rw [hn, hf] at hc; simp at hc
    | some f =>
      cases hr : denoteE s.store rl.rhs with
      | none => rw [hn, hf, hr] at hc; simp at hc
      | some r =>
        rw [hn, hf, hr] at hc
        have hn3 : denoteN s'.store.ns c1 = some n :=
          (hx2.trans hx3).lss.ls.ns _ _ (hd1 n hn)
        rw [hn3, denoteFire_ext (hd2 f (denoteFire_ext hf hx1)) hx3,
          hd3 r ((hx1.trans hx2).expr _ _ hr)]
        exact hc

theorem promoteRules_step {fuel : Nat} : ∀ (rs : List IRecRule) {m m' : PMemo}
    {rs' : List IRecRule} {s s' : AState},
    StoreWF' s.store → PMemoOK m s.store →
    promoteRules m fuel rs s = .ok ((m', rs'), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      PersRules rs' ∧
      (∀ xs, Frontend.denoteRules s.store rs = some xs →
        Frontend.denoteRules s'.store rs' = some xs) := by
  intro rs
  induction rs with
  | nil =>
    intro m m' rs' s s' hwf hm hrun
    simp only [promoteRules] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, Ext.refl _, fun _ h => absurd h (by simp), fun _ h => h⟩
  | cons r rs ih =>
    intro m m' rs' s s' hwf hm hrun
    simp only [promoteRules] at hrun
    obtain ⟨⟨m1, r1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hd1⟩ := promoteRule_step hwf hm h1
    obtain ⟨⟨m2, rs2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, hd2⟩ := ih hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hp1
      · exact hp2 c hc
    · intro xs hxs
      simp only [Frontend.denoteRules] at hxs ⊢
      cases ha : Frontend.denoteRule s.store r with
      | none => rw [ha] at hxs; simp at hxs
      | some a =>
        cases has : Frontend.denoteRules s.store rs with
        | none => rw [ha, has] at hxs; simp at hxs
        | some as =>
          rw [ha, has] at hxs
          simp only [Option.some.injEq] at hxs
          subst hxs
          rw [denoteRule_ext (hd1 a ha) hx2, hd2 as (denoteRules_ext hx1 _ _ has)]

theorem promoteCaps_step {m m' : PMemo} {fuel : Nat} {c c' : IIndCaps}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteCaps m fuel c s = .ok ((m', c'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersCaps c' ∧
      (∀ x, Frontend.denoteCaps s.store c = some x →
        Frontend.denoteCaps s'.store c' = some x) := by
  simp only [promoteCaps] at hrun
  obtain ⟨⟨m1, n1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hwf1, hm1, hx1, hp1, hd1⟩ := promoteN_step hwf hm h1
  obtain ⟨hr, rfl⟩ := AM.pure_ok h2
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨hwf1, hm1, hx1, hp1, ?_⟩
  intro x hx
  simp only [Frontend.denoteCaps] at hx ⊢
  cases hn : denoteN s.store.ns c.etaCtor with
  | none => rw [hn] at hx; simp at hx
  | some n =>
    rw [hn] at hx
    have hn1 : denoteN s'.store.ns n1 = some n := hd1 n hn
    rw [hn1]
    exact hx

/-- con-leche: none — arena infrastructure; **what the promotion does to a
projection table** beyond its denotation: the fields `IProjTableOK` reads are
unchanged, and both name handles — `tableName` included, which
`denoteProjTable` drops — denote what they denoted. -/
structure PromotedTable (st st' : EStore) (t t' : IProjTable) : Prop where
  numFields : t'.numFields = t.numFields
  bodies : t'.bodies.size = t.bodies.size
  guards : t'.guards.length = t.guards.length
  structName : ∀ x, denoteN st.ns t.structName = some x →
    denoteN st'.ns t'.structName = some x
  tableName : ∀ x, denoteN st.ns t.tableName = some x →
    denoteN st'.ns t'.tableName = some x

theorem PromotedTable.mono {st st' st'' : EStore} {t t' : IProjTable}
    (h : PromotedTable st st' t t') (hx : Ext st' st'') : PromotedTable st st'' t t' where
  numFields := h.numFields
  bodies := h.bodies
  guards := h.guards
  structName := fun x hx' => hx.lss.ls.ns _ _ (h.structName x hx')
  tableName := fun x hx' => hx.lss.ls.ns _ _ (h.tableName x hx')

/-- con-leche: none — arena infrastructure; **`IProjTableOK` survives the
promotion** of its table. -/
theorem IProjTableOK.promoted {st st' : EStore} {t t' : IProjTable}
    (h : IProjTableOK st t) (hp : PromotedTable st st' t t') : IProjTableOK st' t' where
  bodies := by rw [hp.bodies, hp.numFields]; exact h.bodies
  guards := by rw [hp.guards, hp.numFields]; exact h.guards
  named := by
    obtain ⟨sn, h1, h2⟩ := h.named
    exact ⟨sn, hp.structName _ h1, hp.tableName _ h2⟩

theorem promoteProjTable_step {m m' : PMemo} {fuel : Nat} {t t' : IProjTable}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteProjTable m fuel t s = .ok ((m', t'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      PersProjTable t' ∧ PromotedTable s.store s'.store t t' ∧
      (∀ x, Frontend.denoteProjTable s.store t = some x →
        Frontend.denoteProjTable s'.store t' = some x) := by
  simp only [promoteProjTable] at hrun
  obtain ⟨⟨m1, sn1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hwf1, hm1, hx1, hp1, hd1⟩ := promoteN_step hwf hm h1
  obtain ⟨⟨m2, tn2⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hwf2, hm2, hx2, hp2, hd2⟩ := promoteN_step hwf1 hm1 h3
  obtain ⟨⟨m3, lps3⟩, s3, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨hwf3, hm3, hx3, hp3, -, hd3⟩ := promoteNList_step _ hwf2 hm2 h5
  obtain ⟨⟨m4, c4⟩, s4, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨hwf4, hm4, hx4, hp4, hd4⟩ := promoteN_step hwf3 hm3 h7
  obtain ⟨⟨m5, ss5⟩, s5, h9, h10⟩ := AM.bind_ok h8
  obtain ⟨hwf5, hm5, hx5, hp5, hd5⟩ := promoteL_step hwf4 hm4 h9
  obtain ⟨⟨m6, bs6⟩, s6, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨hwf6, hm6, hx6, hp6, hl6, hd6⟩ := promoteEList_step _ hwf5 hm5 h11
  obtain ⟨⟨m7, gs7⟩, s7, h13, h14⟩ := AM.bind_ok h12
  obtain ⟨hwf7, hm7, hx7, hp7, hl7, hd7⟩ := promoteLList_step _ hwf6 hm6 h13
  obtain ⟨hr, rfl⟩ := AM.pure_ok h14
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have x12 := hx1.trans hx2
  have x13 := x12.trans hx3
  have x14 := x13.trans hx4
  have x15 := x14.trans hx5
  have x16 := x15.trans hx6
  have x17 := x16.trans hx7
  have x27 := ((((hx2.trans hx3).trans hx4).trans hx5).trans hx6).trans hx7
  have x37 := (((hx3.trans hx4).trans hx5).trans hx6).trans hx7
  have x47 := ((hx4.trans hx5).trans hx6).trans hx7
  have x57 := (hx5.trans hx6).trans hx7
  have x67 := hx6.trans hx7
  refine ⟨hwf7, hm7, x17, ⟨hp1, hp2, hp3, hp4, hp5, by simpa using hp6, hp7⟩,
    ⟨rfl, by simp [hl6], hl7, fun x h => x27.lss.ls.ns _ _ (hd1 x h),
      fun x h => x37.lss.ls.ns _ _ (hd2 x (hx1.lss.ls.ns _ _ h))⟩, ?_⟩
  intro x hx
  simp only [Frontend.denoteProjTable] at hx ⊢
  cases hsn : denoteN s.store.ns t.structName with
  | none => rw [hsn] at hx; simp at hx
  | some sn =>
    cases hlp : Frontend.denoteNList s.store.ns t.levelParams with
    | none => rw [hsn, hlp] at hx; simp at hx
    | some lps =>
      cases hc : denoteN s.store.ns t.ctor with
      | none => rw [hsn, hlp, hc] at hx; simp at hx
      | some c =>
        rw [hsn, hlp, hc] at hx
        simp only at hx ⊢
        cases hss : denoteL s.store.ls t.structSort with
        | none => rw [hss] at hx; simp at hx
        | some ss =>
          cases hbs : Frontend.denoteEArray s.store t.bodies with
          | none => rw [hss, hbs] at hx; simp at hx
          | some bs =>
            cases hgs : denoteLList s.store.ls t.guards with
            | none => rw [hss, hbs, hgs] at hx; simp at hx
            | some gs =>
              rw [hss, hbs, hgs] at hx
              have e1 : denoteN s'.store.ns sn1 = some sn := x27.lss.ls.ns _ _ (hd1 sn hsn)
              have e2 : Frontend.denoteNList s'.store.ns lps3 = some lps :=
                denoteNList_ext x47.lss.ls.ns _ _
                  (hd3 lps (denoteNList_ext x12.lss.ls.ns _ _ hlp))
              have e3 : denoteN s'.store.ns c4 = some c :=
                x57.lss.ls.ns _ _ (hd4 c (x13.lss.ls.ns _ _ hc))
              have e4 : denoteL s'.store.ls ss5 = some ss :=
                x67.lss.ls.lvl _ _ (hd5 ss (x14.lss.ls.lvl _ _ hss))
              have e5 : Frontend.denoteEArray s'.store bs6.toArray = some bs := by
                have hbl : Frontend.denoteEList s.store t.bodies.toList = some bs.toList := by
                  simp only [Frontend.denoteEArray] at hbs
                  cases hq : Frontend.denoteEList s.store t.bodies.toList with
                  | none => rw [hq] at hbs; simp at hbs
                  | some q =>
                    rw [hq] at hbs
                    simp only [Option.some.injEq] at hbs
                    subst hbs; simp
                have := denoteEList_ext hx7 _ _ (hd6 _ (denoteEList_ext x15 _ _ hbl))
                simp [Frontend.denoteEArray, this]
              have e6 : denoteLList s'.store.ls gs7 = some gs :=
                hd7 gs (denoteLList_ext x16.lss.ls _ _ hgs)
              rw [e1, e2, e3]
              simp only
              rw [e4, e5, e6]
              exact hx

/-! ## The stored constant -/

/-- con-leche: none — arena infrastructure; `IConstantInfo.name`'s handle
denotes what it denoted.  At the six term kinds this is the header's name; at
a projection table it is `tableName`. -/
def CINameKept (st st' : EStore) (ci ci' : IConstantInfo) : Prop :=
  ∀ x, denoteN st.ns ci.name = some x → denoteN st'.ns ci'.name = some x

/-- con-leche: none — arena infrastructure; `CINameKept` entry by entry. -/
inductive CIListKept (st st' : EStore) : List IConstantInfo → List IConstantInfo → Prop
  | nil : CIListKept st st' [] []
  | cons {c c' : IConstantInfo} {cs cs' : List IConstantInfo} :
      CINameKept st st' c c' → CIListKept st st' cs cs' →
      CIListKept st st' (c :: cs) (c' :: cs')

theorem CIListKept.post {st st' st'' : EStore} {cs cs' : List IConstantInfo}
    (h : CIListKept st st' cs cs') (hx : Ext st' st'') : CIListKept st st'' cs cs' := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (fun x h => hx.lss.ls.ns _ _ (hc x h)) ih

theorem CIListKept.pre {st0 st st' : EStore} {cs cs' : List IConstantInfo}
    (h : CIListKept st st' cs cs') (hx : Ext st0 st) : CIListKept st0 st' cs cs' := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (fun x h => hc x (hx.lss.ls.ns _ _ h)) ih

theorem CIListKept.length {st st' : EStore} {cs cs' : List IConstantInfo}
    (h : CIListKept st st' cs cs') : cs'.length = cs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem promoteCI_step {m m' : PMemo} {fuel : Nat} {ci ci' : IConstantInfo}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteCI m fuel ci s = .ok ((m', ci'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersCI ci' ∧
      CINameKept s.store s'.store ci ci' ∧
      (∀ t', ci' = .projInfo t' → ∃ t, ci = .projInfo t ∧
        PromotedTable s.store s'.store t t') ∧
      (∀ c, Frontend.denoteCI s.store ci = some c →
        Frontend.denoteCI s'.store ci' = some c) := by
  cases ci with
  | axiomInfo v =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hwf hm h1
    obtain ⟨hr, rfl⟩ := AM.pure_ok h2
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf1, hm1, hx1, hp1, hn1, (fun _ h => by cases h), ?_⟩
    intro c hc
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc ⊢
    obtain ⟨cv, hcv, rfl⟩ := hc
    exact ⟨cv, hd1 cv hcv, rfl⟩
  | ctorInfo v nP nF =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hwf hm h1
    obtain ⟨hr, rfl⟩ := AM.pure_ok h2
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf1, hm1, hx1, hp1, hn1, (fun _ h => by cases h), ?_⟩
    intro c hc
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc ⊢
    obtain ⟨cv, hcv, rfl⟩ := hc
    exact ⟨cv, hd1 cv hcv, rfl⟩
  | defnInfo v e hint =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hwf hm h1
    obtain ⟨⟨m2, e2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hp2, hd2⟩ := promoteE_core fuel m1 e s1 m2 e2 s2 hwf1 hm1 h3
    have hx2 := (promoteE_aext m1 fuel e s1 (m2, e2) s2 h3).ext
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩,
      fun x h => hx2.lss.ls.ns _ _ (hn1 x h), (fun _ h => by cases h), ?_⟩
    intro c hc
    simp only [Frontend.denoteCI] at hc ⊢
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hc; simp at hc
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hc; simp at hc
      | some x =>
        rw [hcv, he] at hc
        rw [denoteCV_ext (hd1 cv hcv) hx2, hd2 x (hx1.expr _ _ he)]
        exact hc
  | thmInfo v e =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hwf hm h1
    obtain ⟨⟨m2, e2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hp2, hd2⟩ := promoteE_core fuel m1 e s1 m2 e2 s2 hwf1 hm1 h3
    have hx2 := (promoteE_aext m1 fuel e s1 (m2, e2) s2 h3).ext
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩,
      fun x h => hx2.lss.ls.ns _ _ (hn1 x h), (fun _ h => by cases h), ?_⟩
    intro c hc
    simp only [Frontend.denoteCI] at hc ⊢
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hc; simp at hc
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hc; simp at hc
      | some x =>
        rw [hcv, he] at hc
        rw [denoteCV_ext (hd1 cv hcv) hx2, hd2 x (hx1.expr _ _ he)]
        exact hc
  | indInfo v caps =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hwf hm h1
    obtain ⟨⟨m2, c2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, hd2⟩ := promoteCaps_step hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩,
      fun x h => hx2.lss.ls.ns _ _ (hn1 x h), (fun _ h => by cases h), ?_⟩
    intro c hc
    simp only [Frontend.denoteCI] at hc ⊢
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hc; simp at hc
    | some cv =>
      cases he : Frontend.denoteCaps s.store caps with
      | none => rw [hcv, he] at hc; simp at hc
      | some x =>
        rw [hcv, he] at hc
        rw [denoteCV_ext (hd1 cv hcv) hx2, hd2 x (denoteCaps_ext he hx1)]
        exact hc
  | recInfo v mI rP rs =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, v1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hn1, hd1⟩ := promoteCV_step hwf hm h1
    obtain ⟨⟨m2, r2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, hd2⟩ := promoteRules_step rs hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩,
      fun x h => hx2.lss.ls.ns _ _ (hn1 x h), (fun _ h => by cases h), ?_⟩
    intro c hc
    simp only [Frontend.denoteCI] at hc ⊢
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hc; simp at hc
    | some cv =>
      cases he : Frontend.denoteRules s.store rs with
      | none => rw [hcv, he] at hc; simp at hc
      | some x =>
        rw [hcv, he] at hc
        rw [denoteCV_ext (hd1 cv hcv) hx2, hd2 x (denoteRules_ext hx1 _ _ he)]
        exact hc
  | projInfo t =>
    simp only [promoteCI] at hrun
    obtain ⟨⟨m1, t1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hpt, hd1⟩ := promoteProjTable_step hwf hm h1
    obtain ⟨hr, rfl⟩ := AM.pure_ok h2
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf1, hm1, hx1, hp1, hpt.tableName, ?_, ?_⟩
    · intro t' h
      simp only [IConstantInfo.projInfo.injEq] at h
      subst h
      exact ⟨t, rfl, hpt⟩
    · intro c hc
      simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc ⊢
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨x, hd1 x hx, rfl⟩

/-- con-leche: none — arena infrastructure; a block's denotation survives an
append (the lanes above have their own copies; this tier cannot import them). -/
theorem denoteCIList_promote_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (cs : List IConstantInfo) (xs : List ConstantInfo),
      Frontend.denoteCIList st cs = some xs → Frontend.denoteCIList st' cs = some xs := by
  intro cs
  induction cs with
  | nil => intro _ h; exact h
  | cons c cs ih =>
    intro xs hxs
    simp only [Frontend.denoteCIList] at hxs ⊢
    cases ha : Frontend.denoteCI st c with
    | none => rw [ha] at hxs; simp at hxs
    | some a =>
      cases has : Frontend.denoteCIList st cs with
      | none => rw [ha, has] at hxs; simp at hxs
      | some as =>
        rw [ha, has] at hxs
        rw [denoteCI_ext ha hx, ih as has]
        exact hxs

theorem promoteCIList_step {fuel : Nat} : ∀ (cs : List IConstantInfo) {m m' : PMemo}
    {cs' : List IConstantInfo} {s s' : AState},
    StoreWF' s.store → PMemoOK m s.store →
    promoteCIList m fuel cs s = .ok ((m', cs'), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      PersCIList cs' ∧ CIListKept s.store s'.store cs cs' ∧
      (∀ t', IConstantInfo.projInfo t' ∈ cs' → ∃ t, IConstantInfo.projInfo t ∈ cs ∧
        PromotedTable s.store s'.store t t') ∧
      (∀ xs, Frontend.denoteCIList s.store cs = some xs →
        Frontend.denoteCIList s'.store cs' = some xs) := by
  intro cs
  induction cs with
  | nil =>
    intro m m' cs' s s' hwf hm hrun
    simp only [promoteCIList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, Ext.refl _, fun _ h => absurd h (by simp), .nil,
      fun _ h => absurd h (by simp), fun _ h => h⟩
  | cons c cs ih =>
    intro m m' cs' s s' hwf hm hrun
    simp only [promoteCIList] at hrun
    obtain ⟨⟨m1, c1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hn1, ht1, hd1⟩ := promoteCI_step hwf hm h1
    obtain ⟨⟨m2, cs2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, hn2, ht2, hd2⟩ := ih hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp1
      · exact hp2 x hx
    · refine .cons (fun x h => hx2.lss.ls.ns _ _ (hn1 x h)) ?_
      exact hn2.pre hx1
    · intro t' ht'
      simp only [List.mem_cons] at ht'
      rcases ht' with h | h
      · obtain ⟨t, rfl, hpt⟩ := ht1 t' h.symm
        exact ⟨t, by simp, hpt.mono hx2⟩
      · obtain ⟨t, hmem, hpt⟩ := ht2 t' h
        refine ⟨t, by simp [hmem], ?_⟩
        exact ⟨hpt.numFields, hpt.bodies, hpt.guards,
          fun x h => hpt.structName x (hx1.lss.ls.ns _ _ h),
          fun x h => hpt.tableName x (hx1.lss.ls.ns _ _ h)⟩
    · intro xs hxs
      simp only [Frontend.denoteCIList] at hxs ⊢
      cases ha : Frontend.denoteCI s.store c with
      | none => rw [ha] at hxs; simp at hxs
      | some a =>
        cases has : Frontend.denoteCIList s.store cs with
        | none => rw [ha, has] at hxs; simp at hxs
        | some as =>
          rw [ha, has] at hxs
          simp only [Option.some.injEq] at hxs
          subst hxs
          rw [denoteCI_ext (hd1 a ha) hx2, hd2 as (denoteCIList_promote_ext hx1 cs as has)]

/-! ## The install/check seam -/

theorem promoteVG_step {m m' : PMemo} {fuel : Nat} {g g' : Arena.ValueGroup}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteVG m fuel g s = .ok ((m', g'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersVG g' ∧
      g'.kind = g.kind ∧
      (∀ c, Frontend.denoteCV s.store g.cvA = some c →
        Frontend.denoteCV s'.store g'.cvA = some c) ∧
      (∀ e, denoteE s.store g.jv = some e → denoteE s'.store g'.jv = some e) := by
  simp only [promoteVG] at hrun
  obtain ⟨⟨m1, c1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hwf1, hm1, hx1, hp1, -, hd1⟩ := promoteCV_step hwf hm h1
  obtain ⟨⟨m2, j2⟩, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨hwf2, hm2, hp2, hd2⟩ := promoteE_core fuel m1 g.jv s1 m2 j2 s2 hwf1 hm1 h3
  have hx2 := (promoteE_aext m1 fuel g.jv s1 (m2, j2) s2 h3).ext
  obtain ⟨hr, rfl⟩ := AM.pure_ok h4
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨hwf2, hm2, hx1.trans hx2, ⟨hp1, hp2⟩, rfl,
    fun c hc => denoteCV_ext (hd1 c hc) hx2, fun e he => hd2 e (hx1.expr _ _ he)⟩

end ConRon.Bridge
