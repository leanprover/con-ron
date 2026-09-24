/-
# `ConRon.Bridge.Promote.Coh` — the promotion's index coherence, extensionally

Task #97-P3-Promote's finding: `IFEnvCoh fe` (`fe = mkIFEnv fe.env`) is an
equation between `Std.HashMap` VALUES, and `promoteNew` does not preserve it —
its two index passes (`eraseInstalled`, then `indexPromoted` newest first)
build the same bindings as `mkIFEnv` (oldest first) in a different insertion
order, which is a different bucket array whenever two keys share a bucket or
a resize happened on one side only (the `sorry` stub `promoteNew_coh` once in
`Bridge/Promote/Exact.lean` said why in full).

This module is the repair, proved: the EXTENSIONAL coherence (`IFEnvCohX`
when this module was written, `IFEnvCoh` itself since task #97-P3-Checker
round 9) —
the same counter, the same answer at every key — which is all any consumer of
`IFEnvCoh` reads, holds after the promotion (`promoteNew_cohX`).  It needs one
precondition the structural statement did not: the step's constants name
pairwise DIFFERENT names (`NamesDistinct`).  Without it `indexPromoted`'s
newest-first insertion lets the OLDEST of two equally-named step constants
win, where `mkIFEnv` lets the newest win — a real difference in what
`find?` answers, not only in representation.  The checker installs no
duplicate names (`Bridge/Checker/Split.lean`'s `checkDecl_nodup` /
`SplitInstall.nodup`), and a split step installs one constant, for which the
precondition is trivial.

Switching `IFEnvCoh` to `IFEnvCohX` was a change of definition that reached
four lanes' statements (`FoldOK.coh`, `StepOK.coh`, `DeclOut.coh`,
`InstRel.coh`, `IndOut.coh`, …); the coordinator ruled for it and task
#97-P3-Checker round 9 made it.  `promoteNew_spec` lives here, at the end,
because its coherence conjunct is `promoteNew_cohX`.
-/
import ConRon.Bridge.Promote.Exact

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The extensional coherence

`IFEnvCohX` was defined here; on the coordinator's ruling (task
#97-P3-Checker round 9) it IS `IFEnvCoh` now (`Bridge/Promote/Exact.lean`),
and its `find?`/`push` lemmas are `IFEnvCoh.find?` (`Bridge/Checker/Inv.lean`)
and `IFEnvCoh.push`. -/

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
    rw [if_neg (by simpa using h a (by simp)), ih _ (fun b hb => h b (by simp [hb]))]

theorem lookupIdx_some {n : NIdx} : ∀ (as : List IConstantInfo) (c : Nat)
    (p : Nat × IConstantInfo), lookupIdx n as c = some p → p.2 ∈ as ∧ p.2.name = n := by
  intro as
  induction as with
  | nil => intro c p h; simp [lookupIdx] at h
  | cons a as ih =>
    intro c p h
    simp only [lookupIdx] at h
    split at h
    · rename_i he
      obtain rfl := Option.some.inj h
      exact ⟨by simp, eq_of_beq he⟩
    · obtain ⟨h1, h2⟩ := ih _ p h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

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
    · rw [if_pos he, if_pos he]
      simp only [Option.some_or, Option.some.injEq, Prod.mk.injEq, and_true]
      omega
    · rw [if_neg he, if_neg he, ih b]
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
      rw [if_pos he, if_pos he, lookupIdx_none]
      · rfl
      · intro b hb hbn; exact hnd.1 b hb (hbn.trans hn.symm)
    · rw [if_neg he, if_neg he]

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
    · rw [if_pos h1, if_pos ⟨_, List.mem_cons_of_mem _ h1.choose_spec.1, h1.choose_spec.2⟩]
    · rw [if_neg h1]
      by_cases h2 : c.name = n
      · rw [if_pos (beq_iff_eq.mpr h2), if_pos ⟨c, by simp, h2⟩]
      · rw [if_neg (by simpa using h2), if_neg]
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
theorem promoteNew_cohX {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hnd : NamesDistinct s.store (fe.env.consts.take k))
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) : IFEnvCoh fe' := by
  obtain ⟨htake, hdrop, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNew_run_zero hrun
    subst fe'; exact hcoh
  obtain ⟨cs', h1, rfl⟩ := promoteNew_run_pos hk0 hrun
  obtain ⟨-, -, -, hp1, hkept, -, -⟩ := promoteCIList_step _ hwf hm h1
  have hlen' : cs'.length = k := by rw [hkept.length, hlen]
  have hnd' := hkept.nodup hnd
  have hvb : fe.visibleBelow = cs'.length + (fe.env.consts.drop k).length := by
    rw [hcoh.vb_eq, hlen', List.length_drop]
    have : k ≤ fe.env.consts.length := by
      rw [← hlen]; exact List.length_take_le' _ _
    omega
  refine ⟨by simp [hvb], fun n => ?_⟩
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
      rw [hdrop, hcoh.2 n]
      conv => lhs; rw [← htake]
      rw [mkIFEnvGo_append, lookupIdx_none, Option.none_or]
      intro a ha han
      exact hin ⟨a, ha, han⟩

/-- con-leche: none — arena infrastructure; **the fold's promotion is
exact**: the `k` constants the step installed are copied into the persistent
tier and re-indexed, and the environment denotes what it denoted.

`fe0` is the PRE-step environment and `k` the counter difference, which is
what `Arena/Checker.lean`'s `checkDeclStep` and `annotStep` compute; the
hypotheses say the step only pushed and that everything below it was already
persistent, which is the fold's own invariant one step earlier.

PROVED (task #97-P3-Promote): `promoteCIList_step` on the step's constants (`Pushed.split` locates them), the two index passes read row by row (`eraseInstalled_getElem?`, `indexPromoted_getElem?`), and the denotation split at the `take`/`drop`.  The `IFEnvCoh fe'` conjunct is `promoteNew_cohX` (task #97-P3-Checker round 9: `IFEnvCoh` redefined extensionally, and the statement gained `hnd`, the step's constants name pairwise different names — the one precondition the coherence needs, see this module's note; it moved here from `Exact.lean` for it). -/
theorem promoteNew_spec {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {env : Env} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0)
    (hcoh : IFEnvCoh fe) (hpush : Pushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hnd : NamesDistinct s.store (fe.env.consts.take k))
    (hd : denoteFEnv s.store fe = some env)
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersIFEnv fe' ∧ IFEnvCoh fe' ∧ denoteFEnv s'.store fe' = some env ∧
      fe'.visibleBelow = fe.visibleBelow ∧ PFrame s s' := by
  have hx := promoteNew_aext m fuel k fe s (m', fe') s' hrun
  obtain ⟨htake, hdrop, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  refine (fun (H : StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersIFEnv fe' ∧
      denoteFEnv s'.store fe' = some env ∧ fe'.visibleBelow = fe.visibleBelow) =>
    ⟨H.1, hx.ext, H.2.1, H.2.2.1, promoteNew_cohX hwf hm hcoh0 hp0 hcoh hpush hk hnd hrun, H.2.2.2.1, H.2.2.2.2,
      PFrame.of_aext hx⟩) ?_
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨h1, h2, h3⟩ := promoteNew_run_zero hrun
    subst m'; subst fe'; subst s'
    -- nothing was pushed, so the step's index answers what the one before
    -- it answers
    have henv : fe.env = fe0.env := by
      simp only [List.take_zero, List.nil_append] at htake
      cases hfe : fe.env; cases hfe0 : fe0.env
      rw [hfe, hfe0] at htake; simp only at htake; rw [htake]
    have hpfe : PersIFEnv fe :=
      ⟨henv ▸ hp0.env, fun n p hp => hp0.idx n p (by
        rw [hcoh0.2 n, ← henv, ← hcoh.2 n]; exact hp)⟩
    exact ⟨hwf, hm, hpfe, hd, rfl⟩
  obtain ⟨cs', h1, rfl⟩ := promoteNew_run_pos hk0 hrun
  obtain ⟨hwf1, hm1, hx1, hp1, -, -, hd1⟩ := promoteCIList_step _ hwf hm h1
  refine ⟨hwf1, hm1, ⟨?_, ?_⟩, ?_, rfl⟩
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
        rw [← hcoh.2 n]
        exact hidx
      obtain ⟨hmem, hname⟩ := mkIFEnvGo_key _ n p hidx'
      rw [← htake] at hmem
      rcases List.mem_append.mp hmem with hin | hin
      · exact absurd hname (hnot _ hin)
      · have hpc := hp0.env _ hin
        exact ⟨hname ▸ persCI_name hpc, hpc⟩
  · -- the denotation: the step's constants promoted exactly, the tail carried
    simp only [denoteFEnv, denoteIEnv, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨zs, hzs, rfl⟩ := hd
    rw [← List.take_append_drop k fe.env.consts] at hzs
    obtain ⟨za, zb, hza, hzb, rfl⟩ := denoteCIList_append _ _ zs hzs
    exact ⟨za ++ zb, denoteCIList_append_of _ _ za zb (hd1 za hza)
      (denoteCIList_promote_ext hx1 _ zb hzb), rfl⟩

/-! ## Census -/

/-- info: 'ConRon.Bridge.promoteNew_cohX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_cohX

/-- info: 'ConRon.Bridge.promoteNew_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_spec

end ConRon.Bridge
