/-
# `ConRon.Bridge.Promote.Coh` — the promotion's index coherence, extensionally

Task #97-P3-Promote's finding: `IFEnvCoh fe` (`fe = mkIFEnv fe.env`) is an
equation between `Std.HashMap` VALUES, and `promoteNew` does not preserve it —
its two index passes (`eraseInstalled`, then `indexPromoted` newest first)
build the same bindings as `mkIFEnv` (oldest first) in a different insertion
order, which is a different bucket array whenever two keys share a bucket or
a resize happened on one side only (`Bridge/Promote/Exact.lean`'s
`promoteNew_coh`, `sorry`, says why in full).

This module is the repair, proved: the EXTENSIONAL coherence `IFEnvCohX` —
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

Switching `IFEnvCoh` to `IFEnvCohX` is a change of definition that reaches
four lanes' statements (`FoldOK.coh`, `StepOK.coh`, `DeclOut.coh`,
`InstRel.coh`, `IndOut.coh`, …); it is the coordinator's call.  The lemmas
here are what that switch needs from this lane.
-/
import ConRon.Bridge.Promote.Exact

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The extensional coherence -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — **the index answers
what its list's index answers**, at every key, and its counter is the list's
length: `IFEnvCoh` up to the representation of the hash map. -/
def IFEnvCohX (fe : IFEnv) : Prop :=
  fe.visibleBelow = fe.env.consts.length ∧
    ∀ n : NIdx, fe.idx[n]? = (mkIFEnvGo fe.env.consts).2[n]?

theorem IFEnvCoh.toX {fe : IFEnv} (h : IFEnvCoh fe) : IFEnvCohX fe :=
  ⟨h.vb_eq, fun n => by rw [show fe.idx = (mkIFEnvGo fe.env.consts).2 from
    congrArg IFEnv.idx h]⟩

/-- con-leche: ConLeche/Verify/EnvBound.lean:243 mkFEnv_find? — the lookup
through an extensionally coherent index is the list's lookup, which is what
`IFEnvCoh.find?` gives every consumer today. -/
theorem IFEnvCohX.find? {fe : IFEnv} (h : IFEnvCohX fe) (n : NIdx) :
    fe.find? n = (mkIFEnv fe.env).find? n := by
  simp only [IFEnv.find?, mkIFEnv, h.2 n, h.1, mkIFEnvGo_fst']

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — `IFEnv.push`
preserves the extensional coherence. -/
theorem IFEnvCohX.push {fe : IFEnv} (h : IFEnvCohX fe) (ci : IConstantInfo) :
    IFEnvCohX (fe.push ci) := by
  refine ⟨by simp [IFEnv.push, h.1], fun n => ?_⟩
  simp only [IFEnv.push, mkIFEnvGo, mkIFEnvGo_fst', Std.HashMap.getElem?_insert, h.2 n,
    h.1]

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
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) : IFEnvCohX fe' := by
  obtain ⟨htake, hdrop, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNew_run_zero hrun
    subst fe'; exact hcoh.toX
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
    have hidx : fe.idx = (mkIFEnvGo fe.env.consts).2 := congrArg IFEnv.idx hcoh
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
      rw [hdrop, hidx]
      conv => lhs; rw [← htake]
      rw [mkIFEnvGo_append, lookupIdx_none, Option.none_or]
      intro a ha han
      exact hin ⟨a, ha, han⟩

/-! ## Census -/

/-- info: 'ConRon.Bridge.IFEnvCoh.toX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IFEnvCoh.toX

/-- info: 'ConRon.Bridge.IFEnvCohX.find?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IFEnvCohX.find?

/-- info: 'ConRon.Bridge.IFEnvCohX.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IFEnvCohX.push

/-- info: 'ConRon.Bridge.promoteNew_cohX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_cohX

end ConRon.Bridge
