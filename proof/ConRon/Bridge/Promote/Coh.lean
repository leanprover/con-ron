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
promotion (`promoteNewConsts_cohX`).  It needs one precondition the structural
statement would not: the promoted constants' name handles are pairwise different.
Without it `indexPromoted`'s newest-first insertion lets the OLDEST of two
equally-named step constants win, where `mkIFEnv` lets the newest win — a real
difference in what `find?` answers, not only in representation.  The checker
installs no duplicate names (`Bridge/Checker/Split.lean`'s `checkDecl_nodup` /
`SplitInstall.nodup`), and a split step installs one constant, for which the
precondition is trivial.

A promotion's persistence (`promoteNew_pers`) needs no such thing: a row of the
promoted index is a promoted constant or a row of the tail.

The two entries the fold's step and the stored install read are at the end:
`promoteNew_pi`, where the input's denotation in the source is known, and
`promoteNew_stored`, where only that the output denotes is, the premise on the names
then being one on the output.
-/
module

public import ConRon.Bridge.Promote.Exact
public import ConRon.Bridge.Promote.WalkDecl

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

variable {src : EStore}

/-! ## The two index builds, as lookups -/

/-- con-leche: none — arena infrastructure; the first entry of `cs` filed
under `n`, with the counter it is filed at when the entries count down from
`c`. -/
def lookupIdx (n : NIdx) : List IConstantInfo → Nat → Option (Nat × IConstantInfo)
  | [], _ => none
  | a :: as, c => if a.name == n then some (c - 1, a) else lookupIdx n as (c - 1)

/-- con-leche: none — arena infrastructure; no entry of that name, no answer. -/
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

/-- con-leche: none — arena infrastructure; the erase forgets exactly the rows of the
step's constants' names. -/
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
pairwise DIFFERENT names: `promoteNew_pi`'s one added precondition, at the step's
constants. -/
@[expose] def NamesDistinct (st : EStore) (cs : List IConstantInfo) : Prop :=
  cs.Pairwise fun a b => ∃ x y, denoteN st.ns a.name = some x ∧
    denoteN st.ns b.name = some y ∧ x ≠ y

/-- con-leche: none — arena infrastructure; names denoting differently in the source are
different handles after the promotion. -/
theorem CIListKept.nodup {src st' : EStore} {cs cs' : List IConstantInfo}
    (h : CIListKept src st' cs cs') (hnd : NamesDistinct src cs) :
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
    have key : ∀ (xs xs' : List IConstantInfo), CIListKept src st' xs xs' →
        ∀ b' ∈ xs', ∃ b ∈ xs, NameKept src st' b.name b'.name := by
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
index EXTENSIONALLY coherent**, at the definition that the promotion can actually
meet (this module's note), and at the one precondition that makes it true: the
promoted constants' name handles are pairwise different. -/
theorem promoteNewConsts_cohX {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hnd : ((fe'.env.consts.take k).map IConstantInfo.name).Nodup)
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) : IFEnvCoh fe' := by
  obtain ⟨htake, hdrop, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNewConsts_run_zero hrun
    subst fe'; exact hcoh
  obtain ⟨cs', h1, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
  obtain ⟨-, -, -, hp1, hkept, -⟩ := promoteCIList_step _ hs hm h1
  have hlen' : cs'.length = k := by rw [hkept.length, hlen]
  have hnd' : (cs'.map IConstantInfo.name).Nodup := by
    have e : (cs' ++ fe.env.consts.drop k).take k = cs' := List.take_left' hlen'
    have hnd2 : (((cs' ++ fe.env.consts.drop k).take k).map IConstantInfo.name).Nodup := hnd
    rwa [e] at hnd2
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
        have key : ∀ (xs xs' : List IConstantInfo),
            CIListKept src s'.store.dropScratch xs xs' →
            ∀ c ∈ xs, ∃ c' ∈ xs', NameKept src s'.store.dropScratch c.name c'.name := by
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

/-- con-leche: none — arena infrastructure; the counter does not move. -/
theorem promoteNewConsts_vb {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    fe'.visibleBelow = fe.visibleBelow := by
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNewConsts_run_zero hrun
    subst fe'
    rfl
  · obtain ⟨cs', -, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
    rfl

/-- con-leche: none — arena infrastructure; pairwise different denotations in the source
are pairwise different handles after the promotion. -/
theorem promoteNewConsts_nodup {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hlen : (fe.env.consts.take k).length = k)
    (hnd : NamesDistinct src (fe.env.consts.take k))
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    ((fe'.env.consts.take k).map IConstantInfo.name).Nodup := by
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · obtain ⟨cs', h1, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
    obtain ⟨-, -, -, -, hkept, -⟩ := promoteCIList_step _ hs hm h1
    have hl : cs'.length = k := by rw [hkept.length, hlen]
    have e : (cs' ++ fe.env.consts.drop k).take k = cs' := List.take_left' hl
    show (((cs' ++ fe.env.consts.drop k).take k).map IConstantInfo.name).Nodup
    rw [e]
    exact hkept.nodup hnd

/-- con-leche: none — arena infrastructure; **the constants' promotion is persistent**:
the list is the promoted step and the persistent tail, and a row of the index is a
promoted constant or, since the erase kept it, a row of the tail.  Nothing is asked of
the step's names. -/
theorem promoteNewConsts_pers {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    PersIEnv fe'.env ∧ (∀ n p, fe'.idx[n]? = some p → PersN n ∧ PersCI p.2) := by
  obtain ⟨htake, hdrop, -⟩ := Pushed.split hcoh0 hcoh hpush hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNewConsts_run_zero hrun
    subst fe'
    have henv : fe.env.consts = fe0.env.consts := by
      simpa using htake.symm
    refine ⟨?_, fun n p hp => hp0.idx n p ?_⟩
    · show PersCIList fe.env.consts
      rw [henv]; exact hp0.env
    · rw [hcoh0.idx n, ← henv, ← hcoh.idx n]; exact hp
  obtain ⟨cs', h1, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
  obtain ⟨-, -, -, hp1, -, -⟩ := promoteCIList_step _ hs hm h1
  refine ⟨?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hp1 c hc
    · rw [hdrop] at hc; exact hp0.env c hc
  · intro n p hp
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

/-- con-leche: none — arena infrastructure; **the constants' promotion is exact**: what
the constants denote in the source they denote in the projection after it.  The step's
own by the walk, the tail because it is persistent. -/
theorem promoteNewConsts_imp {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s'))
    (xs : List ConstantInfo) (hd : Frontend.denoteCIList src fe.env.consts = some xs) :
    Frontend.denoteCIList s'.store.dropScratch fe'.env.consts = some xs := by
  obtain ⟨htake, hdrop, -⟩ := Pushed.split hcoh0 hcoh hpush hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, h3⟩ := promoteNewConsts_run_zero hrun
    subst fe'; subst s'
    have henv : fe.env.consts = fe0.env.consts := by simpa using htake.symm
    exact hs.pext.denoteCIList _ (henv ▸ hp0.env) xs hd
  obtain ⟨cs', h1, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
  obtain ⟨hs1, -, -, -, -, hd1⟩ := promoteCIList_step _ hs hm h1
  have hzs := hd
  rw [← List.take_append_drop k fe.env.consts] at hzs
  obtain ⟨za, zb, hza, hzb, hz⟩ := denoteCIList_append _ _ _ hzs
  rw [hz]
  exact denoteCIList_append_of _ _ za zb (hd1.2 za hza)
    (hs1.pext.denoteCIList _ (hdrop ▸ hp0.env) zb hzb)

/-- con-leche: none — arena infrastructure; **what the constants' promotion leaves
denotes**, the step's own by the walk and the tail because it did before. -/
theorem promoteNewConsts_ex {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (h0 : ∃ xs, Frontend.denoteCIList s.store.dropScratch fe0.env.consts = some xs)
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    ∃ xs, Frontend.denoteCIList s'.store.dropScratch fe'.env.consts = some xs := by
  obtain ⟨htake, hdrop, -⟩ := Pushed.split hcoh0 hcoh hpush hk
  obtain ⟨z0, hz0⟩ := h0
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, h3⟩ := promoteNewConsts_run_zero hrun
    subst fe'; subst s'
    have henv : fe.env.consts = fe0.env.consts := by simpa using htake.symm
    exact ⟨z0, henv ▸ hz0⟩
  obtain ⟨cs', h1, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
  obtain ⟨-, -, hx1, -, -, ⟨za, hza⟩, -⟩ := promoteCIList_step _ hs hm h1
  exact ⟨za ++ z0, denoteCIList_append_of _ _ za z0 hza
    (hdrop ▸ denoteCIList_mono hx1 _ z0 hz0)⟩

/-- con-leche: none — arena infrastructure; a promoted table is the promotion of one of
the step's own, and conversely. -/
theorem TblListKept.exists_of_mem {src st' : EStore} {xs xs' : List IProjTable}
    (hk : TblListKept src st' xs xs') : ∀ b ∈ xs, ∃ b' ∈ xs', PromotedTable src st' b b' := by
  induction hk with
  | nil => intro _ h; exact absurd h (by simp)
  | @cons d d' ds ds' hd _ ih2 =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨d', by simp, hd⟩
    · obtain ⟨b', hb', hk'⟩ := ih2 b hb
      exact ⟨b', List.mem_cons_of_mem _ hb', hk'⟩

/-- con-leche: none — arena infrastructure; **the tables' promotion is persistent**:
the list is the promoted step and the persistent tail, and a row of the table map is a
promoted table or, since the erase kept it, a table of the tail. -/
theorem promoteNewTables_pers {m m' : PMemo} {fuel kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hp0 : PersIFEnv fe0)
    (htb : ∀ n : NIdx, fe.tbls[n]? = (mkIFEnvTblsGo fe.env.tables)[n]?)
    (hpush : TPushed fe0 fe) (hk : kt = fe.env.tables.length - fe0.env.tables.length)
    (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s')) :
    (∀ t ∈ fe'.env.tables, PersProjTable t) ∧
      (∀ n t, fe'.tbls[n]? = some t → PersN n ∧ PersProjTable t) := by
  obtain ⟨htake, hdrop, -⟩ := TPushed.split hpush hk
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNewTables_run_zero hrun
    subst fe'
    have henv : fe.env.tables = fe0.env.tables := by simpa using htake.symm
    refine ⟨henv ▸ hp0.tables, fun n t ht => ?_⟩
    rw [htb n] at ht
    obtain ⟨hmem, hname⟩ := mkIFEnvTblsGo_key _ n t ht
    rw [henv] at hmem
    have hpt := hp0.tables t hmem
    exact ⟨hname ▸ hpt.structName, hpt⟩
  obtain ⟨ts', h1, rfl⟩ := promoteNewTables_run_pos hk0 hrun
  obtain ⟨-, -, -, hp1, -, -⟩ := promoteProjTables_step _ hs hm h1
  refine ⟨?_, ?_⟩
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
        rw [htb n] at ht
        obtain ⟨hmem, hname⟩ := mkIFEnvTblsGo_key _ n t ht
        rw [← htake] at hmem
        rcases List.mem_append.mp hmem with hin | hin
        · exact absurd ⟨t, hin, hname⟩ hnot
        · have hpt := hp0.tables t hin
          exact ⟨hname ▸ hpt.structName, hpt⟩

/-- con-leche: none — arena infrastructure; **the table map stays coherent**.  No
distinctness is needed: the re-index inserts oldest first, as `mkIFEnvTblsGo` does. -/
theorem promoteNewTables_cohX {m m' : PMemo} {fuel kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hp0 : PersIFEnv fe0)
    (htb : ∀ n : NIdx, fe.tbls[n]? = (mkIFEnvTblsGo fe.env.tables)[n]?)
    (hpush : TPushed fe0 fe) (hk : kt = fe.env.tables.length - fe0.env.tables.length)
    (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s')) :
    ∀ n : NIdx, fe'.tbls[n]? = (mkIFEnvTblsGo fe'.env.tables)[n]? := by
  obtain ⟨htake, hdrop, -⟩ := TPushed.split hpush hk
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNewTables_run_zero hrun
    subst fe'
    exact htb
  obtain ⟨ts', h1, rfl⟩ := promoteNewTables_run_pos hk0 hrun
  obtain ⟨-, -, -, -, hkept, -⟩ := promoteProjTables_step _ hs hm h1
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
      obtain ⟨t', ht', hpt⟩ := hkept.exists_of_mem t ht
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
  intro n
  show (indexPromotedTables (eraseInstalledTables fe.tbls (fe.env.tables.take kt)) ts')[n]?
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
      rw [htb n]
      conv => lhs; rw [← List.take_append_drop kt fe.env.tables]
      rw [mkIFEnvTblsGo_append, mkIFEnvTblsGo_none _ n (fun t ht htn => hnot ⟨t, ht, htn⟩),
        Option.none_or]

/-- con-leche: none — arena infrastructure; **the tables' promotion is exact**: what
the tables denote in the source they denote in the projection after it.  The step's own
by the walk, the tail because it is persistent. -/
theorem promoteNewTables_imp {m m' : PMemo} {fuel kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hp0 : PersIFEnv fe0) (hpush : TPushed fe0 fe)
    (hk : kt = fe.env.tables.length - fe0.env.tables.length)
    (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s'))
    (xs : List ProjTable) (hd : Frontend.denoteProjTableList src fe.env.tables = some xs) :
    Frontend.denoteProjTableList s'.store.dropScratch fe'.env.tables = some xs := by
  obtain ⟨htake, hdrop, -⟩ := TPushed.split hpush hk
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨-, h2, h3⟩ := promoteNewTables_run_zero hrun
    subst fe'; subst s'
    have henv : fe.env.tables = fe0.env.tables := by simpa using htake.symm
    exact hs.pext.denoteProjTableList _ (henv ▸ hp0.tables) xs hd
  obtain ⟨ts', h1, rfl⟩ := promoteNewTables_run_pos hk0 hrun
  obtain ⟨hs1, -, -, -, -, hd1⟩ := promoteProjTables_step _ hs hm h1
  have hzs := hd
  rw [← List.take_append_drop kt fe.env.tables] at hzs
  obtain ⟨za, zb, hza, hzb, hz⟩ := denoteProjTableList_append _ _ _ hzs
  rw [hz]
  exact denoteProjTableList_append_of _ _ za zb (hd1.2 za hza)
    (hs1.pext.denoteProjTableList _ (hdrop ▸ hp0.tables) zb hzb)

/-- con-leche: none — arena infrastructure; **what the tables' promotion leaves
denotes**, the step's own by the walk and the tail because it did before. -/
theorem promoteNewTables_ex {m m' : PMemo} {fuel kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hpush : TPushed fe0 fe) (hk : kt = fe.env.tables.length - fe0.env.tables.length)
    (h0 : ∃ xs, Frontend.denoteProjTableList s.store.dropScratch fe0.env.tables = some xs)
    (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s')) :
    ∃ xs, Frontend.denoteProjTableList s'.store.dropScratch fe'.env.tables = some xs := by
  obtain ⟨htake, hdrop, -⟩ := TPushed.split hpush hk
  obtain ⟨z0, hz0⟩ := h0
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨-, h2, h3⟩ := promoteNewTables_run_zero hrun
    subst fe'; subst s'
    have henv : fe.env.tables = fe0.env.tables := by simpa using htake.symm
    exact ⟨z0, henv ▸ hz0⟩
  obtain ⟨ts', h1, rfl⟩ := promoteNewTables_run_pos hk0 hrun
  obtain ⟨-, -, hx1, -, -, ⟨za, hza⟩, -⟩ := promoteProjTables_step _ hs hm h1
  exact ⟨za ++ z0, denoteProjTableList_append_of _ _ za z0 hza
    (hdrop ▸ denoteProjTableList_mono hx1 _ z0 hz0)⟩

/-! ## The whole step -/

/-- con-leche: none — arena infrastructure; **a step's promotion leaves a persistent
environment**, whatever its names. -/
theorem promoteNew_pers {m m' : PMemo} {fuel k kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (htpush : TPushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hkt : kt = fe.env.tables.length - fe0.env.tables.length)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) :
    PersIFEnv fe' ∧ fe'.visibleBelow = fe.visibleBelow := by
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨ht1, htb1⟩ := promoteNewConsts_tables h1
  obtain ⟨hc2, hi2, hvb2⟩ := promoteNewTables_consts h2
  obtain ⟨hs1, hm1, -⟩ := promoteNewConsts_step hs hm h1
  obtain ⟨hpe1, hpi1⟩ := promoteNewConsts_pers hs hm hcoh0 hp0 hcoh hpush hk h1
  have htpush1 : TPushed fe0 fe1 := by
    obtain ⟨n, hn⟩ := htpush; exact ⟨n, by rw [ht1, hn]⟩
  have hkt1 : kt = fe1.env.tables.length - fe0.env.tables.length := by rw [ht1]; exact hkt
  have htbl : ∀ n : NIdx, fe1.tbls[n]? = (mkIFEnvTblsGo fe1.env.tables)[n]? := by
    intro n; rw [ht1, htb1]; exact hcoh.tbls n
  obtain ⟨hpt2, hptb2⟩ := promoteNewTables_pers hs1 hm1 hp0 htbl htpush1 hkt1 h2
  refine ⟨⟨?_, ?_, hpt2, hptb2⟩, by rw [hvb2, promoteNewConsts_vb h1]⟩
  · show PersCIList fe'.env.consts
    rw [hc2]; exact hpe1
  · intro n p hp
    rw [hi2] at hp; exact hpi1 n p hp

/-- con-leche: none — arena infrastructure; **a step's promotion keeps the index
coherent**, at pairwise different promoted name handles. -/
theorem promoteNew_coh {m m' : PMemo} {fuel k kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (htpush : TPushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hkt : kt = fe.env.tables.length - fe0.env.tables.length)
    (hnd : ((fe'.env.consts.take k).map IConstantInfo.name).Nodup)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) : IFEnvCoh fe' := by
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨ht1, htb1⟩ := promoteNewConsts_tables h1
  obtain ⟨hc2, hi2, hvb2⟩ := promoteNewTables_consts h2
  obtain ⟨hs1, hm1, -⟩ := promoteNewConsts_step hs hm h1
  have hc1 : IFEnvCoh fe1 :=
    promoteNewConsts_cohX hs hm hcoh0 hp0 hcoh hpush hk (by rw [← hc2]; exact hnd) h1
  have htpush1 : TPushed fe0 fe1 := by
    obtain ⟨n, hn⟩ := htpush; exact ⟨n, by rw [ht1, hn]⟩
  have hkt1 : kt = fe1.env.tables.length - fe0.env.tables.length := by rw [ht1]; exact hkt
  exact ⟨by rw [hvb2, hc2]; exact hc1.1, fun n => by rw [hi2, hc2]; exact hc1.idx n,
    promoteNewTables_cohX hs1 hm1 hp0 hc1.tbls htpush1 hkt1 h2⟩

/-- con-leche: none — arena infrastructure; **the fold's promotion is exact**: the
constants and the tables the step installed are copied into the persistent tier and
re-indexed, and the environment denotes in the projection what it denoted in the source.

`fe0` is the PRE-step environment, `k` the counter difference and `kt` the
table-count difference, which is what `Arena/Checker.lean`'s `checkDeclStep`
and `installStep` compute; the hypotheses say the step only pushed (constants
and tables) and that everything below it was already persistent. -/
theorem promoteNew_pi {m m' : PMemo} {fuel k kt : Nat} {fe0 fe fe' : IFEnv} {env : Env}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (htpush : TPushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hkt : kt = fe.env.tables.length - fe0.env.tables.length)
    (hnd : NamesDistinct src (fe.env.consts.take k))
    (hd : denoteFEnv src fe = some env)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) :
    PersIFEnv fe' ∧ IFEnvCoh fe' ∧ denoteFEnv s'.store.dropScratch fe' = some env ∧
      fe'.visibleBelow = fe.visibleBelow ∧ Pushed fe0 fe' ∧ TPushed fe0 fe' := by
  obtain ⟨hpers, hvb⟩ := promoteNew_pers hs hm hcoh0 hp0 hcoh hpush htpush hk hkt hrun
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨ht1, -⟩ := promoteNewConsts_tables h1
  obtain ⟨hc2, -, -⟩ := promoteNewTables_consts h2
  obtain ⟨hs1, hm1, -⟩ := promoteNewConsts_step hs hm h1
  obtain ⟨-, -, hx2⟩ := promoteNewTables_step hs1 hm1 h2
  obtain ⟨-, -, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  have hnd' : ((fe'.env.consts.take k).map IConstantInfo.name).Nodup := by
    rw [hc2]; exact promoteNewConsts_nodup hs hm hlen hnd h1
  have htpush1 : TPushed fe0 fe1 := by
    obtain ⟨n, hn⟩ := htpush; exact ⟨n, by rw [ht1, hn]⟩
  have hkt1 : kt = fe1.env.tables.length - fe0.env.tables.length := by rw [ht1]; exact hkt
  obtain ⟨hdc, hdt⟩ := denoteIEnv_some.mp hd
  refine ⟨hpers, promoteNew_coh hs hm hcoh0 hp0 hcoh hpush htpush hk hkt hnd' hrun,
    denoteIEnv_some.mpr ⟨?_, ?_⟩, hvb, promoteNew_pushed hcoh0 hcoh hpush hk hrun,
    promoteNew_tpushed htpush hkt hrun⟩
  · rw [hc2]
    exact denoteCIList_mono hx2 _ _ (promoteNewConsts_imp hs hm hcoh0 hp0 hcoh hpush hk h1 _ hdc)
  · exact promoteNewTables_imp hs1 hm1 hp0 htpush1 hkt1 h2 _ (by rw [ht1]; exact hdt)

/-- con-leche: none — arena infrastructure; **the same with no denotation of the input
known**, for an inductive block's stored install: what is promoted denotes SOMETHING,
below it stands what stood, and the promoted names' uniqueness is a premise on the
OUTPUT.  The environment is persistent regardless. -/
theorem promoteNew_stored {m m' : PMemo} {fuel k kt : Nat} {fe0 fe fe' : IFEnv} {env0 : Env}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (htpush : TPushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hkt : kt = fe.env.tables.length - fe0.env.tables.length)
    (hd0 : denoteFEnv s.store.dropScratch fe0 = some env0)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) :
    Pushed fe0 fe' ∧ TPushed fe0 fe' ∧ fe'.visibleBelow = fe.visibleBelow ∧ PersIFEnv fe' ∧
      (∃ env', denoteFEnv s'.store.dropScratch fe' = some env') ∧
      ((fe'.env.consts.map IConstantInfo.name).Nodup → IFEnvCoh fe') := by
  obtain ⟨hpers, hvb⟩ := promoteNew_pers hs hm hcoh0 hp0 hcoh hpush htpush hk hkt hrun
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨ht1, -⟩ := promoteNewConsts_tables h1
  obtain ⟨hc2, -, -⟩ := promoteNewTables_consts h2
  obtain ⟨hs1, hm1, hx1⟩ := promoteNewConsts_step hs hm h1
  obtain ⟨-, -, hx2⟩ := promoteNewTables_step hs1 hm1 h2
  obtain ⟨hdc0, hdt0⟩ := denoteIEnv_some.mp hd0
  have htpush1 : TPushed fe0 fe1 := by
    obtain ⟨n, hn⟩ := htpush; exact ⟨n, by rw [ht1, hn]⟩
  have hkt1 : kt = fe1.env.tables.length - fe0.env.tables.length := by rw [ht1]; exact hkt
  obtain ⟨xs, hxs⟩ := promoteNewConsts_ex hs hm hcoh0 hcoh hpush hk ⟨_, hdc0⟩ h1
  obtain ⟨ts, hts⟩ := promoteNewTables_ex hs1 hm1 htpush1 hkt1
    ⟨_, denoteProjTableList_mono hx1 _ _ hdt0⟩ h2
  refine ⟨promoteNew_pushed hcoh0 hcoh hpush hk hrun, promoteNew_tpushed htpush hkt hrun, hvb,
    hpers, ⟨⟨xs, ts⟩, denoteIEnv_some.mpr ⟨?_, hts⟩⟩, fun hnod => ?_⟩
  · rw [hc2]; exact denoteCIList_mono hx2 _ _ hxs
  · exact promoteNew_coh hs hm hcoh0 hp0 hcoh hpush htpush hk hkt
      (hnod.sublist ((List.take_sublist k _).map _)) hrun

/-! ## Census -/

/-- info: 'ConRon.Bridge.promoteNewConsts_cohX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNewConsts_cohX

/-- info: 'ConRon.Bridge.promoteNewTables_cohX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNewTables_cohX

/-- info: 'ConRon.Bridge.promoteNew_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_pi

/-- info: 'ConRon.Bridge.promoteNew_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_stored

end ConRon.Bridge
