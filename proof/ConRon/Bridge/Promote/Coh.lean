/-
# `ConRon.Bridge.Promote.Coh` — the promotion's index coherence, extensionally

The structural coherence `fe = mkIFEnv fe.env` is an equation between
`Std.HashMap` VALUES, and `promoteNew` does not preserve it — its two index
passes (`eraseInstalled`, then `indexPromoted` newest first) build the same
bindings as `mkIFEnv` (oldest first) in a different insertion order, which is
a different bucket array whenever two keys share a bucket or a resize happened
on one side only.  So `IFEnvCoh` is EXTENSIONAL (DESIGN
`### Task #97-P3-Promote`): the same counter, the same answer at every key —
which is all any consumer reads — and this module proves it holds after the
promotion (`promoteNew_cohX`).  It needs one precondition the structural
statement would not: the step's constants name
pairwise DIFFERENT names (`NamesDistinct`).  Without it `indexPromoted`'s
newest-first insertion lets the OLDEST of two equally-named step constants
win, where `mkIFEnv` lets the newest win — a real difference in what
`find?` answers, not only in representation.  The checker installs no
duplicate names (`Bridge/Checker/Split.lean`'s `checkDecl_nodup` /
`SplitInstall.nodup`), and a split step installs one constant, for which the
precondition is trivial.

`promoteNew_spec` lives here, at the end, because its coherence conjunct is
`promoteNewConsts_cohX` (and the tables' half, `promoteNewTables_spec`, needs
no distinctness: the table map's re-index inserts oldest first).
-/
import ConRon.Bridge.Promote.Exact

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The two index builds, as lookups -/

/-- con-leche: none — arena infrastructure; the first entry of `cs` filed
under `n`, with the counter it is filed at when the entries count down from
`c`. -/
def lookupIdx (n : NIdx) : List IConstantInfo → Nat → Option (Nat × IConstantInfo)
  | [], _ => none
  | a :: as, c => if a.name == n then some (c - 1, a) else lookupIdx n as (c - 1)

theorem lookupIdx_none {n : NIdx} : ∀ (as : List IConstantInfo) (c : Nat),
    (∀ a ∈ as, a.name ≠ n) → lookupIdx n as c = none := by
  intro as
  induction as with
  | nil => intro c _; rfl
  | cons a as ih =>
    intro c h
    simp only [lookupIdx]
    rw [ite_eq_right (by simpa using h a (by simp)), ih _ (fun b hb => h b (by simp [hb]))]

/-- con-leche: ConLeche/Kernel/FEnv.lean:51-60 mkFEnvGo — the index of
`as ++ b` answers from `as` first, counting down from the whole length. -/
theorem mkIFEnvGo_append (n : NIdx) : ∀ (as b : List IConstantInfo),
    (mkIFEnvGo (as ++ b)).2[n]? =
      (lookupIdx n as (as.length + b.length)).or (mkIFEnvGo b).2[n]? := by
  intro as
  induction as with
  | nil => intro b; simp [lookupIdx]
  | cons a as ih =>
    intro b
    simp only [List.cons_append, mkIFEnvGo, Std.HashMap.getElem?_insert, lookupIdx,
      mkIFEnvGo_fst', List.length_append, List.length_cons]
    by_cases he : (a.name == n) = true
    · rw [ite_eq_left he, ite_eq_left he]
      simp only [Option.some_or, Option.some.injEq, Prod.mk.injEq, and_true]
      omega
    · rw [ite_eq_right he, ite_eq_right he, ih b]
      congr 2
      omega

/-- con-leche: none — arena infrastructure; `indexPromoted` at pairwise
distinct names answers from its list first. -/
theorem indexPromoted_getElem?_eq (n : NIdx) : ∀ (as : List IConstantInfo)
    (M : Std.HashMap NIdx (Nat × IConstantInfo)) (c : Nat),
    (as.map IConstantInfo.name).Nodup →
    (indexPromoted M c as)[n]? = (lookupIdx n as c).or M[n]? := by
  intro as
  induction as with
  | nil => intro M c _; simp [indexPromoted, lookupIdx]
  | cons a as ih =>
    intro M c hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [indexPromoted, lookupIdx]
    rw [ih _ _ hnd.2, Std.HashMap.getElem?_insert]
    by_cases he : (a.name == n) = true
    · have hn : a.name = n := eq_of_beq he
      rw [ite_eq_left he, ite_eq_left he, lookupIdx_none]
      · rfl
      · intro b hb hbn; exact hnd.1 b hb (hbn.trans hn.symm)
    · rw [ite_eq_right he, ite_eq_right he]

theorem eraseInstalled_getElem?_eq (n : NIdx) : ∀ (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)),
    (eraseInstalled idx cs)[n]? = if (∃ c ∈ cs, c.name = n) then none else idx[n]? := by
  intro cs
  induction cs with
  | nil => intro idx; simp [eraseInstalled]
  | cons c cs ih =>
    intro idx
    simp only [eraseInstalled, ih, Std.HashMap.getElem?_erase]
    by_cases h1 : ∃ c' ∈ cs, c'.name = n
    · rw [ite_eq_left h1, ite_eq_left ⟨_, List.mem_cons_of_mem _ h1.choose_spec.1, h1.choose_spec.2⟩]
    · rw [ite_eq_right h1]
      by_cases h2 : c.name = n
      · rw [ite_eq_left (beq_iff_eq.mpr h2), ite_eq_left ⟨c, by simp, h2⟩]
      · rw [ite_eq_right (by simpa using h2), ite_eq_right]
        rintro ⟨c', hc', hn⟩
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact h2 hn
        · exact h1 ⟨c', hc', hn⟩

/-! ## The promotion -/

/-- con-leche: none — arena infrastructure; the constants' names denote
pairwise DIFFERENT names.  `promoteNew_cohX`'s one added precondition, at
the step's constants. -/
def NamesDistinct (st : EStore) (cs : List IConstantInfo) : Prop :=
  cs.Pairwise fun a b => ∃ x y, denoteN st.ns a.name = some x ∧
    denoteN st.ns b.name = some y ∧ x ≠ y

theorem CIListKept.nodup {st st' : EStore} {cs cs' : List IConstantInfo}
    (h : CIListKept st st' cs cs') (hnd : NamesDistinct st cs) :
    (cs'.map IConstantInfo.name).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons c c' cs cs' hc hr ih =>
    simp only [NamesDistinct, List.pairwise_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2⟩
    intro hmem
    obtain ⟨b', hb', hbn⟩ := List.mem_map.mp hmem
    -- `b'` is the promotion of some `b ∈ cs`, whose name denotes differently
    have key : ∀ (xs xs' : List IConstantInfo), CIListKept st st' xs xs' →
        ∀ b' ∈ xs', ∃ b ∈ xs, NameKept st st' b.name b'.name := by
      intro xs xs' hk
      induction hk with
      | nil => intro _ h; exact absurd h (by simp)
      | @cons d d' ds ds' hd _ ih2 =>
        intro b' hb'
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact ⟨d, by simp, hd⟩
        · obtain ⟨b, hb, hk'⟩ := ih2 b' hb'
          exact ⟨b, List.mem_cons_of_mem _ hb, hk'⟩
    obtain ⟨b, hb, hkb⟩ := key cs cs' hr b' hb'
    obtain ⟨x, y, hx, hy, hxy⟩ := hnd.1 b hb
    have hx' := hc.denote x hx
    have hy' := hkb.denote y hy
    rw [hbn] at hy'
    rw [hx'] at hy'
    exact hxy (Option.some.inj hy')

/-- con-leche: none — arena infrastructure; **the fold's promotion keeps the
index EXTENSIONALLY coherent** — `promoteNew_spec`'s `IFEnvCoh` conjunct, at
the definition that the promotion can actually meet (this module's note), and
at the one precondition that makes it true (`NamesDistinct` of the step's
constants). -/
theorem promoteNewConsts_cohX {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hnd : NamesDistinct s.store (fe.env.consts.take k))
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) : IFEnvCoh fe' := by
  obtain ⟨htake, hdrop, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNewConsts_run_zero hrun
    subst fe'; exact hcoh
  obtain ⟨cs', h1, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
  obtain ⟨-, -, -, hp1, hkept, -⟩ := promoteCIList_step _ hwf hm h1
  have hlen' : cs'.length = k := by rw [hkept.length, hlen]
  have hnd' := hkept.nodup hnd
  have hvb : fe.visibleBelow = cs'.length + (fe.env.consts.drop k).length := by
    rw [hcoh.vb_eq, hlen', List.length_drop]
    have : k ≤ fe.env.consts.length := by
      rw [← hlen]; exact List.length_take_le' _ _
    omega
  refine ⟨by simp [hvb], fun n => ?_, fun n => hcoh.tbls n⟩
  show (indexPromoted (eraseInstalled fe.idx (fe.env.consts.take k)) fe.visibleBelow cs')[n]?
    = (mkIFEnvGo (cs' ++ fe.env.consts.drop k)).2[n]?
  rw [indexPromoted_getElem?_eq n _ _ _ hnd', mkIFEnvGo_append, hvb]
  cases hl : lookupIdx n cs' (cs'.length + (fe.env.consts.drop k).length) with
  | some p => rfl
  | none =>
    simp only [Option.none_or]
    -- `n` is no promoted name
    have hnot : ∀ a ∈ cs', a.name ≠ n := by
      intro a ha han
      -- the first promoted entry named `n` would be found
      have : ∀ (as : List IConstantInfo) (c : Nat), a ∈ as → a.name = n →
          lookupIdx n as c ≠ none := by
        intro as
        induction as with
        | nil => intro c h; simp at h
        | cons b bs ih =>
          intro c hb hn
          simp only [lookupIdx]
          split
          · simp
          · rename_i hne
            rcases List.mem_cons.mp hb with rfl | hb
            · exact absurd (beq_iff_eq.mpr hn) hne
            · exact ih _ hb hn
      exact this cs' _ ha han hl
    rw [eraseInstalled_getElem?_eq]
    split
    · -- `n` names a step constant but no promoted one: it is a scratch
      -- handle (a persistent one promotes to itself), so no row of the
      -- persistent tail carries it
      rename_i hin
      obtain ⟨c, hc, hcn⟩ := hin
      symm
      cases hg : (mkIFEnvGo (fe.env.consts.drop k)).2[n]? with
      | none => rfl
      | some p =>
        exfalso
        obtain ⟨hpm, hpn⟩ := mkIFEnvGo_key _ n p hg
        rw [hdrop] at hpm
        have hpers : PersN n := hpn ▸ persCI_name (hp0.env _ hpm)
        -- the promotion of `c` kept its (persistent) name
        have key : ∀ (xs xs' : List IConstantInfo), CIListKept s.store s'.store xs xs' →
            ∀ c ∈ xs, ∃ c' ∈ xs', NameKept s.store s'.store c.name c'.name := by
          intro xs xs' hk
          induction hk with
          | nil => intro _ h; exact absurd h (by simp)
          | @cons d d' ds ds' hd _ ih2 =>
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact ⟨d', by simp, hd⟩
            · obtain ⟨c', hc', hk'⟩ := ih2 c hc
              exact ⟨c', List.mem_cons_of_mem _ hc', hk'⟩
        obtain ⟨c', hc', hkc⟩ := key _ _ hkept c hc
        have : c'.name = n := by rw [hkc.pers (hcn ▸ hpers), hcn]
        exact hnot c' hc' this
    · rename_i hin
      rw [hdrop, hcoh.idx n]
      conv => lhs; rw [← htake]
      rw [mkIFEnvGo_append, lookupIdx_none, Option.none_or]
      intro a ha han
      exact hin ⟨a, ha, han⟩

/-- con-leche: none — arena infrastructure; **the constants' promotion is
exact**: the `k` constants the step installed are copied into the persistent
tier and re-indexed, the environment denotes what it denoted, and the tables
are untouched.

`fe0` is the PRE-step environment and `k` the counter difference; the
hypotheses say the step only pushed and that everything below it was already
persistent, which is the fold's own invariant one step earlier.  The proof:
`promoteCIList_step` on the step's constants (`Pushed.split` locates them),
the two index passes read row by row (`eraseInstalled_getElem?`,
`indexPromoted_getElem?`), and the denotation split at the `take`/`drop`. -/
theorem promoteNewConsts_spec {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {env : Env} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0)
    (hcoh : IFEnvCoh fe) (hpush : Pushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hnd : NamesDistinct s.store (fe.env.consts.take k))
    (hd : denoteFEnv s.store fe = some env)
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      PersIEnv fe'.env ∧ (∀ n p, fe'.idx[n]? = some p → PersN n ∧ PersCI p.2) ∧
      IFEnvCoh fe' ∧ denoteFEnv s'.store fe' = some env ∧
      fe'.visibleBelow = fe.visibleBelow ∧
      fe'.env.tables = fe.env.tables ∧ fe'.tbls = fe.tbls := by
  have hx := (promoteNewConsts_aext m fuel k fe s (m', fe') s' hrun).ext
  have hcohX := promoteNewConsts_cohX hwf hm hcoh0 hp0 hcoh hpush hk hnd hrun
  obtain ⟨htb, htbls⟩ := promoteNewConsts_tables hrun
  obtain ⟨htake, hdrop, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  obtain ⟨hdc, hdt⟩ := denoteIEnv_some.mp hd
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨h1, h2, h3⟩ := promoteNewConsts_run_zero hrun
    subst m'; subst fe'; subst s'
    have henv : fe.env.consts = fe0.env.consts := by
      simpa using htake.symm
    refine ⟨hwf, hm, Ext.refl _, ?_, fun n p hp => hp0.idx n p ?_,
      hcoh, hd, rfl, rfl, rfl⟩
    · show PersCIList fe.env.consts
      rw [henv]; exact hp0.env
    · rw [hcoh0.idx n, ← henv, ← hcoh.idx n]; exact hp
  obtain ⟨cs', h1, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
  obtain ⟨hwf1, hm1, hx1, hp1, -, hd1⟩ := promoteCIList_step _ hwf hm h1
  refine ⟨hwf1, hm1, hx1, ?_, ?_, hcohX, ?_, rfl, rfl, rfl⟩
  · -- the list: the promoted step, then the untouched (persistent) tail
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hp1 c hc
    · rw [hdrop] at hc; exact hp0.env c hc
  · -- the rows: a promoted one, or an old one the erase kept — and an old row
    -- the erase kept is filed under a name no step constant has, so it is a
    -- row of the tail
    intro n p hp
    rcases indexPromoted_getElem? _ _ _ n p hp with ⟨hmem, hname⟩ | hold
    · have hpc := hp1 _ hmem
      exact ⟨hname ▸ persCI_name hpc, hpc⟩
    · obtain ⟨hidx, hnot⟩ := eraseInstalled_getElem? _ _ n p hold
      have hidx' : (mkIFEnvGo fe.env.consts).2[n]? = some p := by
        rw [← hcoh.idx n]
        exact hidx
      obtain ⟨hmem, hname⟩ := mkIFEnvGo_key _ n p hidx'
      rw [← htake] at hmem
      rcases List.mem_append.mp hmem with hin | hin
      · exact absurd hname (hnot _ hin)
      · have hpc := hp0.env _ hin
        exact ⟨hname ▸ persCI_name hpc, hpc⟩
  · -- the denotation: the step's constants promoted exactly, the tail and the
    -- tables carried
    refine denoteIEnv_some.mpr ⟨?_, denoteProjTableList_mono hx1 _ _ hdt⟩
    have hzs := hdc
    rw [← List.take_append_drop k fe.env.consts] at hzs
    obtain ⟨za, zb, hza, hzb, hz⟩ := denoteCIList_append _ _ _ hzs
    rw [hz]
    exact denoteCIList_append_of _ _ za zb (hd1 za hza) (denoteCIList_mono hx1 _ zb hzb)

/-- con-leche: none — arena infrastructure; **the tables' promotion is exact**:
the `kt` tables the step installed are copied into the persistent tier and
re-keyed, the environment denotes what it denoted, the constants are untouched.
No distinctness is needed: the re-index inserts oldest first, as
`mkIFEnvTblsGo` does. -/
theorem promoteNewTables_spec {m m' : PMemo} {fuel kt : Nat} {fe0 fe fe' : IFEnv}
    {env : Env} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hp0 : PersIFEnv fe0)
    (hcoh : IFEnvCoh fe) (hpush : TPushed fe0 fe)
    (hk : kt = fe.env.tables.length - fe0.env.tables.length)
    (hd : denoteFEnv s.store fe = some env)
    (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      (∀ t ∈ fe'.env.tables, PersProjTable t) ∧
      (∀ n t, fe'.tbls[n]? = some t → PersN n ∧ PersProjTable t) ∧
      IFEnvCoh fe' ∧ denoteFEnv s'.store fe' = some env ∧
      fe'.env.consts = fe.env.consts ∧ fe'.idx = fe.idx ∧
      fe'.visibleBelow = fe.visibleBelow := by
  obtain ⟨htake, hdrop, hlen⟩ := TPushed.split hpush hk
  obtain ⟨hdc, hdt⟩ := denoteIEnv_some.mp hd
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨h1, h2, h3⟩ := promoteNewTables_run_zero hrun
    subst m'; subst fe'; subst s'
    have henv : fe.env.tables = fe0.env.tables := by simpa using htake.symm
    refine ⟨hwf, hm, Ext.refl _, henv ▸ hp0.tables, fun n t ht => ?_, hcoh, hd, rfl, rfl, rfl⟩
    rw [hcoh.tbls n] at ht
    obtain ⟨hmem, hname⟩ := mkIFEnvTblsGo_key _ n t ht
    rw [henv] at hmem
    have hpt := hp0.tables t hmem
    exact ⟨hname ▸ hpt.structName, hpt⟩
  obtain ⟨ts', h1, rfl⟩ := promoteNewTables_run_pos hk0 hrun
  obtain ⟨hwf1, hm1, hx1, hp1, hkept, hd1⟩ := promoteProjTables_step _ hwf hm h1
  -- a promoted table is the promotion of one of the step's own, and a step
  -- table whose structure name is persistent keeps it
  have key : ∀ (xs xs' : List IProjTable), TblListKept s.store s'.store xs xs' →
      ∀ b ∈ xs, ∃ b' ∈ xs', PromotedTable s.store s'.store b b' := by
    intro xs xs' hk
    induction hk with
    | nil => intro _ h; exact absurd h (by simp)
    | @cons d d' ds ds' hd _ ih2 =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨d', by simp, hd⟩
      · obtain ⟨b', hb', hk'⟩ := ih2 b hb
        exact ⟨b', List.mem_cons_of_mem _ hb', hk'⟩
  -- the step's tables that are found under a persistent name keep that name
  have hgone : ∀ n, (mkIFEnvTblsGo ts')[n]? = none → (∃ t ∈ fe.env.tables.take kt,
      t.structName = n) → (mkIFEnvTblsGo fe0.env.tables)[n]? = none := by
    intro n hnone hin
    obtain ⟨t, ht, htn⟩ := hin
    cases hg : (mkIFEnvTblsGo fe0.env.tables)[n]? with
    | none => rfl
    | some u =>
      exfalso
      obtain ⟨hum, hun⟩ := mkIFEnvTblsGo_key _ n u hg
      have hpers : PersN n := hun ▸ (hp0.tables u hum).structName
      obtain ⟨t', ht', hpt⟩ := key _ _ hkept t ht
      have htn' : t'.structName = n := by rw [hpt.structPers (htn ▸ hpers), htn]
      have : (mkIFEnvTblsGo ts')[n]? ≠ none := by
        have hall : ∀ (as : List IProjTable), t' ∈ as → (mkIFEnvTblsGo as)[n]? ≠ none := by
          intro as
          induction as with
          | nil => intro h; simp at h
          | cons b bs ih =>
            intro hb
            simp only [mkIFEnvTblsGo, Std.HashMap.getElem?_insert]
            split
            · simp
            · rename_i hne
              rcases List.mem_cons.mp hb with rfl | hb
              · exact absurd (beq_iff_eq.mpr htn') hne
              · exact ih hb
        exact hall ts' ht'
      exact this hnone
  refine ⟨hwf1, hm1, hx1, ?_, ?_, ⟨hcoh.1, fun n => hcoh.idx n, fun n => ?_⟩, ?_, rfl, rfl, rfl⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hp1 t ht
    · rw [hdrop] at ht; exact hp0.tables t ht
  · intro n t ht
    rw [indexPromotedTables_getElem?] at ht
    cases hn : (mkIFEnvTblsGo ts')[n]? with
    | some u =>
      rw [hn] at ht
      simp only [Option.some_or, Option.some.injEq] at ht
      subst ht
      obtain ⟨hmem, hname⟩ := mkIFEnvTblsGo_key _ n u hn
      have hpt := hp1 u hmem
      exact ⟨hname ▸ hpt.structName, hpt⟩
    | none =>
      rw [hn, Option.none_or, eraseInstalledTables_getElem?] at ht
      split at ht
      · cases ht
      · rename_i hnot
        rw [hcoh.tbls n] at ht
        obtain ⟨hmem, hname⟩ := mkIFEnvTblsGo_key _ n t ht
        rw [← htake] at hmem
        rcases List.mem_append.mp hmem with hin | hin
        · exact absurd ⟨t, hin, hname⟩ hnot
        · have hpt := hp0.tables t hin
          exact ⟨hname ▸ hpt.structName, hpt⟩
  · show (indexPromotedTables (eraseInstalledTables fe.tbls (fe.env.tables.take kt)) ts')[n]?
      = (mkIFEnvTblsGo (ts' ++ fe.env.tables.drop kt))[n]?
    rw [indexPromotedTables_getElem?, mkIFEnvTblsGo_append, eraseInstalledTables_getElem?]
    cases hn : (mkIFEnvTblsGo ts')[n]? with
    | some u => rfl
    | none =>
      simp only [Option.none_or]
      split
      · rename_i hin
        rw [hdrop]; exact (hgone n hn hin).symm
      · rename_i hnot
        rw [hcoh.tbls n]
        conv => lhs; rw [← List.take_append_drop kt fe.env.tables]
        rw [mkIFEnvTblsGo_append, mkIFEnvTblsGo_none _ n (fun t ht htn => hnot ⟨t, ht, htn⟩),
          Option.none_or]
  · refine denoteIEnv_some.mpr ⟨denoteCIList_mono hx1 _ _ hdc, ?_⟩
    have hzs := hdt
    rw [← List.take_append_drop kt fe.env.tables] at hzs
    obtain ⟨za, zb, hza, hzb, hz⟩ := denoteProjTableList_append _ _ _ hzs
    rw [hz]
    exact denoteProjTableList_append_of _ _ za zb (hd1 za hza)
      (denoteProjTableList_mono hx1 _ zb hzb)

/-- con-leche: none — arena infrastructure; **the fold's promotion is
exact**: the constants and the tables the step installed are copied into the
persistent tier and re-indexed, and the environment denotes what it denoted.

`fe0` is the PRE-step environment, `k` the counter difference and `kt` the
table-count difference, which is what `Arena/Checker.lean`'s `checkDeclStep`
and `installStep` compute; the hypotheses say the step only pushed (constants
and tables) and that everything below it was already persistent.  The
constants' half is `promoteNewConsts_spec`, which needs `hnd` (the step's
constants name pairwise different names, this module's note); the tables'
half is `promoteNewTables_spec`. -/
theorem promoteNew_spec {m m' : PMemo} {fuel k kt : Nat} {fe0 fe fe' : IFEnv}
    {env : Env} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0)
    (hcoh : IFEnvCoh fe) (hpush : Pushed fe0 fe) (htpush : TPushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hkt : kt = fe.env.tables.length - fe0.env.tables.length)
    (hnd : NamesDistinct s.store (fe.env.consts.take k))
    (hd : denoteFEnv s.store fe = some env)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersIFEnv fe' ∧ IFEnvCoh fe' ∧ denoteFEnv s'.store fe' = some env ∧
      fe'.visibleBelow = fe.visibleBelow ∧ PFrame s s' := by
  have hx := promoteNew_aext m fuel k kt fe s (m', fe') s' hrun
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨hwf1, hm1, -, hpe1, hpi1, hcoh1, hd1, hvb1, ht1, -⟩ :=
    promoteNewConsts_spec hwf hm hcoh0 hp0 hcoh hpush hk hnd hd h1
  have htpush1 : TPushed fe0 fe1 := by
    obtain ⟨n, hn⟩ := htpush; exact ⟨n, by rw [ht1, hn]⟩
  have hkt1 : kt = fe1.env.tables.length - fe0.env.tables.length := by rw [ht1]; exact hkt
  obtain ⟨hwf2, hm2, -, hpt2, hptb2, hcoh2, hd2, hc2, hi2, hvb2⟩ :=
    promoteNewTables_spec hwf1 hm1 hp0 hcoh1 htpush1 hkt1 hd1 h2
  refine ⟨hwf2, hx.ext, hm2, ⟨?_, ?_, hpt2, hptb2⟩, hcoh2, hd2, by rw [hvb2, hvb1],
    PFrame.of_aext hx⟩
  · show PersCIList fe'.env.consts
    rw [hc2]; exact hpe1
  · intro n p hp
    rw [hi2] at hp; exact hpi1 n p hp

/-! ## Census -/

/-- info: 'ConRon.Bridge.promoteNewConsts_cohX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNewConsts_cohX

/-- info: 'ConRon.Bridge.promoteNewTables_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNewTables_spec

/-- info: 'ConRon.Bridge.promoteNew_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_spec

end ConRon.Bridge
