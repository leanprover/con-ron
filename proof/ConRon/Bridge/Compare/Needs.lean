/-
# `ConRon.Bridge.Compare.Needs` — the justification's name walks, covered

Theorem 1 for the twin's `Arena/Needs.lean` walks and `Arena/Justify.lean`'s `entryNeeds`, at
SET level: every name con-leche's walk lists (`ConLeche/Cached/Needs.lean`'s `needsGo`,
`NeedsSt.*`, `ConLeche/Cached/Justify.lean`'s `entryNeeds`) is denoted by a name the twin's walk
lists (`NamesCover`).  The justification reads these lists only as sets (the cone walk visits
every name of them), so no list simulation is needed, and the twin's memo keyed by handle and
con-leche's keyed by expression need not agree:

* con-leche's walk only adds the names of a specification list (`needsGoU_sub` … `entryNeedsU_sub`:
  `Expr.needs`, `specRule`, `specConst`, `specTable`, `specEntry`);
* the twin's walk covers that list and keeps what it was handed (`needsGo_cov` … `const_runT`,
  `table_runT`), its memo holding only nodes whose names are already listed (`NeedsInvT`).

`justifyNeeds_run` (a statement's type) and `entryNeeds_run` (a constant's entry) are what the
cone walk's bridge reads.  The walks are in the Checker tier's run form (`AM.bind_ok` per bind).
-/
module

public import ConRon.Bridge.Checker.Basis
public import ConRon.Arena.Justify
public import ConLeche.Cached.Justify
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Checker.NatOpNames
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-- con-leche: none — **every name of `L` is denoted by a handle of `hs`**. -/
@[expose] def NamesCover (st : EStore) (hs : List NIdx) (L : List ConLeche.Name) : Prop :=
  ∀ m ∈ L, ∃ h ∈ hs, denoteN st.ns h = some m

/-- con-leche: none — a cover by a smaller list is one by a larger list. -/
theorem NamesCover.sub {st : EStore} {hs hs' : List NIdx} {L : List ConLeche.Name}
    (h : NamesCover st hs L) (hsub : ∀ k ∈ hs, k ∈ hs') : NamesCover st hs' L :=
  fun m hm => let ⟨k, hk, hd⟩ := h m hm; ⟨k, hsub k hk, hd⟩

/-- con-leche: none — two covers by one list cover the concatenation. -/
theorem NamesCover.append {st : EStore} {hs : List NIdx} {L L' : List ConLeche.Name}
    (h : NamesCover st hs L) (h' : NamesCover st hs L') : NamesCover st hs (L ++ L') := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h m hm
  · exact h' m hm

/-- con-leche: none — nothing is covered by anything. -/
theorem NamesCover.nil (st : EStore) (hs : List NIdx) : NamesCover st hs [] :=
  fun _ h => nomatch h

/-- con-leche: none — a list of handles covers what it denotes. -/
theorem NamesCover.of_denoteNL {st : EStore} :
    ∀ {hs : List NIdx} {L : List ConLeche.Name}, denoteNL st hs L → NamesCover st hs L
  | [], [], _ => NamesCover.nil _ _
  | h :: hs, x :: xs, ⟨h1, h2⟩ => by
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨h, List.mem_cons_self, h1⟩
    · obtain ⟨k, hk, hd⟩ := NamesCover.of_denoteNL h2 m hm
      exact ⟨k, List.mem_cons_of_mem _ hk, hd⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- con-leche: none — a prefix of a denoting handle list denotes the prefix. -/
theorem denoteNL_take {st : EStore} :
    ∀ (n : Nat) {hs : List NIdx} {L : List ConLeche.Name}, denoteNL st hs L →
      denoteNL st (hs.take n) (L.take n)
  | 0, _, _, _ => by simp [denoteNL]
  | _ + 1, [], [], _ => by simp [denoteNL]
  | n + 1, h :: hs, x :: xs, ⟨h1, h2⟩ => ⟨h1, denoteNL_take n h2⟩
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

/-- con-leche: ConLeche/Verify/Driver/Reach.lean:91 NeedsInv — **the twin memo's invariant**: every
handle the memo holds denotes an expression whose `needs` the names so far cover. -/
@[expose] def NeedsInvT (st : EStore) (seen : Std.HashMap EIdx Bool) (acc : List NIdx) : Prop :=
  ∀ h b, seen[h]? = some b → ∃ t, denoteE st h = some t ∧ NamesCover st acc t.needs

/-- con-leche: ConLeche/Verify/Driver/Reach.lean:91 NeedsInv — the memo's invariant survives more
names. -/
theorem NeedsInvT.sub {st : EStore} {seen : Std.HashMap EIdx Bool} {acc acc' : List NIdx}
    (h : NeedsInvT st seen acc) (hsub : ∀ k ∈ acc, k ∈ acc') : NeedsInvT st seen acc' :=
  fun k b hk => let ⟨t, ht, hc⟩ := h k b hk; ⟨t, ht, hc.sub hsub⟩

/-- con-leche: ConLeche/Verify/Driver/Reach.lean:96 needsInv_insert — a node recorded once its
names are covered. -/
theorem NeedsInvT.insert {st : EStore} {seen : Std.HashMap EIdx Bool} {acc : List NIdx}
    (h : NeedsInvT st seen acc) {k : EIdx} {t : Expr} (ht : denoteE st k = some t)
    (hc : NamesCover st acc t.needs) : NeedsInvT st (seen.insert k true) acc := by
  intro j b hj
  rw [Std.HashMap.getElem?_insert] at hj
  split at hj
  · next he => rw [← eq_of_beq he]; exact ⟨t, ht, hc⟩
  · exact h j b hj

/-- con-leche: ConLeche/Cached/Needs.lean:24-29 litNeeds — the names a literal reads, off the pin
table. -/
theorem litNeeds_run {s s' : AState} {l : Literal} {acc r : List NIdx} (hp : PinsOK s)
    (hrun : Arena.litNeeds l acc s = .ok (r, s')) :
    s' = s ∧ (∀ k ∈ acc, k ∈ r) ∧ NamesCover s.store r (ConLeche.Cached.litNeeds l) := by
  simp only [Arena.litNeeds] at hrun
  obtain ⟨ns, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hns⟩ := Inductives.litGuardNames_run hp h1
  subst hs1
  have hsub : ∀ k ∈ acc, k ∈ acc ++ ns.take 3 := fun k hk => List.mem_append_left _ hk
  cases l with
  | natVal n =>
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    refine ⟨rfl, by simpa [nidxAppend] using hsub, ?_⟩
    have := NamesCover.of_denoteNL (denoteNL_take 3 hns)
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero]
    exact this.sub fun k hk => List.mem_append_right _ hk
  | strVal str =>
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    refine ⟨rfl, fun k hk => by simp [nidxAppend, hk], ?_⟩
    have := NamesCover.of_denoteNL hns
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero, List.take_length]
    exact this.sub fun k hk => List.mem_append_right _ hk

/-- con-leche: ConLeche/Verify/Driver/Reach.lean:114 needsGo_spec — what a walk leaves: the memo's
invariant, the names it was handed, and the expression's `needs` covered. -/
@[expose] def NeedsOut (st : EStore) (acc : List NIdx)
    (r : Std.HashMap EIdx Bool × List NIdx) (t : Expr) : Prop :=
  NeedsInvT st r.1 r.2 ∧ (∀ k ∈ acc, k ∈ r.2) ∧ NamesCover st r.2 t.needs

/-- con-leche: ConLeche/Verify/Driver/Reach.lean:114 needsGo_spec — **the twin's memoised walk
covers `Expr.needs`**: from a memo whose nodes' names the list covers, the walk of a denoting
handle moves nothing, keeps the list and the memo's invariant, and covers the expression's
`needs`. -/
theorem needsGo_cov (s : AState) (hok : StateOK s) (hp : PinsOK s) :
    ∀ (fuel : Nat) (h : EIdx) (seen : Std.HashMap EIdx Bool) (acc : List NIdx)
      {s' : AState} {r : Std.HashMap EIdx Bool × List NIdx} {t : Expr},
      NeedsInvT s.store seen acc → denoteE s.store h = some t →
      Arena.needsGo seen acc fuel h s = .ok (r, s') →
      s' = s ∧ NeedsOut s.store acc r t := by
  have hwf := hok.wf
  intro fuel
  induction fuel with
  | zero => intro h seen acc s' r t _ _ hrun; exact (AM.fail_ok hrun).elim
  | succ fuel ih =>
    intro h seen acc s' r t hinv ht hrun
    simp only [Arena.needsGo] at hrun
    obtain ⟨v, s1, hv, k⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hview⟩ := view_run hv
    subst s1
    -- the memo hit, for every compound node
    have hit : ∀ b, seen[h]? = some b → (pure (seen, acc) : AM _) s = .ok (r, s') →
        s' = s ∧ NeedsOut s.store acc r t := by
      intro b hb hk
      obtain ⟨hr, hs⟩ := AM.pure_ok hk
      subst hr hs
      obtain ⟨t', ht', hc⟩ := hinv h b hb
      rw [ht] at ht'; cases ht'
      exact ⟨rfl, hinv, fun k hk => hk, hc⟩
    -- a compound node walked: the children's result, the node recorded
    have fin : ∀ (q : Std.HashMap EIdx Bool × List NIdx), NeedsInvT s.store q.1 q.2 →
        (∀ k ∈ acc, k ∈ q.2) → NamesCover s.store q.2 t.needs →
        (pure (q.1.insert h true, q.2) : AM _) s = .ok (r, s') →
        s' = s ∧ NeedsOut s.store acc r t := by
      intro q h1 h2 h3 hk
      obtain ⟨hr, hs⟩ := AM.pure_ok hk
      subst hr hs
      exact ⟨rfl, h1.insert ht h3, h2, h3⟩
    cases v with
    | bvar i =>
      obtain ⟨hr, hs⟩ := AM.pure_ok k; subst hr hs
      rw [denote_bvar_inv hwf hview ht] at *
      exact ⟨rfl, hinv, fun k hk => hk, by simp [Expr.needs, NamesCover.nil]⟩
    | sort u =>
      obtain ⟨hr, hs⟩ := AM.pure_ok k; subst hr hs
      obtain ⟨_, rfl, -⟩ := denote_sort_inv hwf hview ht
      exact ⟨rfl, hinv, fun k hk => hk, by simp [Expr.needs, NamesCover.nil]⟩
    | lit l =>
      obtain ⟨a, s2, h1, h2⟩ := AM.bind_ok k
      obtain ⟨hs2, hsub, hc⟩ := litNeeds_run hp h1
      subst hs2
      obtain ⟨hr, hs⟩ := AM.pure_ok h2; subst hr hs
      rw [denote_lit_inv hwf hview ht]
      exact ⟨rfl, hinv.sub hsub, hsub, by simpa [Expr.needs] using hc⟩
    | const n us =>
      obtain ⟨hr, hs⟩ := AM.pure_ok k; subst hr hs
      obtain ⟨nm, ls, rfl, hn, -⟩ := denote_const_inv hwf hview ht
      have hsub : ∀ k ∈ acc, k ∈ acc ++ [n] := fun k hk => List.mem_append_left _ hk
      refine ⟨rfl, hinv.sub hsub, hsub, ?_⟩
      intro m hm
      simp only [Expr.needs, List.mem_singleton] at hm
      subst hm
      exact ⟨n, by simp, hn⟩
    | fvar i ty =>
      simp only at k
      cases hb : seen[h]? with
      | some b => rw [hb] at k; exact hit b hb k
      | none =>
        rw [hb] at k
        simp only at k
        obtain ⟨q, s2, h1, h2⟩ := AM.bind_ok k
        obtain ⟨tt, rfl, htt⟩ := denote_fvar_inv hwf hview ht
        obtain ⟨hs2, i1, i2, i3⟩ := ih ty seen acc hinv htt h1
        subst hs2
        exact fin q i1 i2 (by simpa [Expr.needs] using i3) h2
    | app f a =>
      simp only at k
      cases hb : seen[h]? with
      | some b => rw [hb] at k; exact hit b hb k
      | none =>
        rw [hb] at k
        simp only at k
        obtain ⟨q, s2, h1, h2⟩ := AM.bind_ok k
        obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hview ht
        obtain ⟨hs3, i1, i2, i3⟩ := ih f seen acc hinv hf h1
        subst hs3
        obtain ⟨p, s4, g1, g2⟩ := AM.bind_ok h2
        obtain ⟨hs4, j1, j2, j3⟩ := ih a q.1 q.2 i1 ha g1
        subst hs4
        exact fin p j1 (fun k hk => j2 k (i2 k hk))
          (by simpa [Expr.needs] using (i3.sub j2).append j3) g2
    | lam ty b =>
      simp only at k
      cases hb : seen[h]? with
      | some x => rw [hb] at k; exact hit x hb k
      | none =>
        rw [hb] at k
        simp only at k
        obtain ⟨q, s2, h1, h2⟩ := AM.bind_ok k
        obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_lam_inv hwf hview ht
        obtain ⟨hs3, i1, i2, i3⟩ := ih ty seen acc hinv hf h1
        subst hs3
        obtain ⟨p, s4, g1, g2⟩ := AM.bind_ok h2
        obtain ⟨hs4, j1, j2, j3⟩ := ih b q.1 q.2 i1 ha g1
        subst hs4
        exact fin p j1 (fun k hk => j2 k (i2 k hk))
          (by simpa [Expr.needs] using (i3.sub j2).append j3) g2
    | forallE ty b =>
      simp only at k
      cases hb : seen[h]? with
      | some x => rw [hb] at k; exact hit x hb k
      | none =>
        rw [hb] at k
        simp only at k
        obtain ⟨q, s2, h1, h2⟩ := AM.bind_ok k
        obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_forallE_inv hwf hview ht
        obtain ⟨hs3, i1, i2, i3⟩ := ih ty seen acc hinv hf h1
        subst hs3
        obtain ⟨p, s4, g1, g2⟩ := AM.bind_ok h2
        obtain ⟨hs4, j1, j2, j3⟩ := ih b q.1 q.2 i1 ha g1
        subst hs4
        exact fin p j1 (fun k hk => j2 k (i2 k hk))
          (by simpa [Expr.needs] using (i3.sub j2).append j3) g2
    | letE ty w b =>
      simp only at k
      cases hb : seen[h]? with
      | some x => rw [hb] at k; exact hit x hb k
      | none =>
        rw [hb] at k
        simp only at k
        obtain ⟨q, s2, h1, h2⟩ := AM.bind_ok k
        obtain ⟨et, ew, eb, rfl, hty, hw, hbd⟩ := denote_letE_inv hwf hview ht
        obtain ⟨hs3, i1, i2, i3⟩ := ih ty seen acc hinv hty h1
        subst hs3
        obtain ⟨q2, s4, g3, g4⟩ := AM.bind_ok h2
        obtain ⟨hs4, j1, j2, j3⟩ := ih w q.1 q.2 i1 hw g3
        subst hs4
        obtain ⟨p, s5, g5, g6⟩ := AM.bind_ok g4
        obtain ⟨hs5, l1, l2, l3⟩ := ih b q2.1 q2.2 j1 hbd g5
        subst hs5
        exact fin p l1 (fun k hk => l2 k (j2 k (i2 k hk)))
          (by simpa [Expr.needs, List.append_assoc] using
            ((i3.sub j2).sub l2).append ((j3.sub l2).append l3)) g6
    | proj n i sub =>
      simp only at k
      cases hb : seen[h]? with
      | some x => rw [hb] at k; exact hit x hb k
      | none =>
        rw [hb] at k
        simp only at k
        obtain ⟨q, s2, h1, h2⟩ := AM.bind_ok k
        obtain ⟨nm, es, rfl, hn, hs⟩ := denote_proj_inv hwf hview ht
        have hsub : ∀ k ∈ acc, k ∈ acc ++ [n] := fun k hk => List.mem_append_left _ hk
        obtain ⟨hs2, i1, i2, i3⟩ := ih sub seen (acc ++ [n]) (hinv.sub hsub) hs h1
        subst hs2
        refine fin q i1 (fun k hk => i2 k (hsub k hk)) ?_ h2
        intro m hm
        simp only [Expr.needs, List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact ⟨n, i2 n (by simp), hn⟩
        · exact i3 m hm


/-- con-leche: none — membership of a handle in a denoting list is membership of its name. -/
theorem denoteNL_contains {st : EStore} (hwf : StoreWF st) {hs : List NIdx}
    {L : List ConLeche.Name} (hL : denoteNL st hs L) {n : NIdx} {nm : ConLeche.Name}
    (hn : denoteN st.ns n = some nm) : hs.contains n = L.contains nm :=
  denoteNList_contains hwf _ _ (denoteNL_toList _ _ hL) n nm hn

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:96-97 reduceElemName — a compiler-trust
operation's element type's name. -/
theorem reduceElemName_run {n : NIdx} {nm : ConLeche.Name} {r : NIdx} {s s' : AState}
    (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.reduceElemName n s = .ok (r, s')) :
    s' = s ∧ denoteN s.store.ns r = some (ConLeche.reduceElemName nm) := by
  simp only [Arena.reduceElemName, Arena.reduceNatName, Arena.pinReduceNat] at hrun
  obtain ⟨rn, s0, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨p0, d1⟩ := pinAt_run (x := ConLeche.reduceNatName) hp (by rfl) g0
  subst s0
  have hiff := beq_handle_iff hok.wf hn d1
  rcases AM.ite_ok r0 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natName) hp (by rfl) k
    exact ⟨rfl, by rw [d2, ConLeche.reduceElemName, ite_eq_left (hiff.mp hc)]⟩
  · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.boolName) hp (by rfl) k
    exact ⟨rfl, by rw [d2, ConLeche.reduceElemName, ite_eq_right (fun h => hc (hiff.mpr h))]⟩

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — the second summand. -/
theorem pinFootprintReduce_run {n : NIdx} {nm : ConLeche.Name} {xs r : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.pinFootprintReduce n xs s = .ok (r, s')) :
    s' = s ∧ (∀ k ∈ xs, k ∈ r) ∧
      NamesCover s.store r
        (if ConLeche.reduceOpNames.contains nm then [ConLeche.reduceElemName nm] else []) := by
  simp only [Arena.pinFootprintReduce] at hrun
  obtain ⟨ns, s0, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨p0, d0⟩ := reduceOpNames_run hp g0
  subst s0
  have hc := denoteNL_contains hok.wf d0 hn
  rcases AM.ite_ok r0 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨e, s1, g1, r1⟩ := AM.bind_ok k
    obtain ⟨p1, d1⟩ := reduceElemName_run hok hp hn g1
    subst s1
    obtain ⟨hr, hs⟩ := AM.pure_ok r1
    subst hr hs
    rw [hc] at hb
    rw [ite_eq_left hb]
    refine ⟨rfl, fun k hk => List.mem_append_left _ hk, ?_⟩
    intro m hm
    rw [List.mem_singleton] at hm
    subst hm
    exact ⟨e, by simp, d1⟩
  · obtain ⟨hr, hs⟩ := AM.pure_ok k
    subst hr hs
    rw [hc] at hb
    rw [ite_eq_right hb]
    exact ⟨rfl, fun k hk => hk, NamesCover.nil _ _⟩

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — the first summand. -/
theorem pinFootprintNat_run {n : NIdx} {nm : ConLeche.Name} {dms r : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hdms : denoteNL s.store dms ConLeche.natDivModNames)
    (hrun : Arena.pinFootprintNat n dms s = .ok (r, s')) :
    s' = s ∧ NamesCover s.store r
      (ConLeche.natOpDeps nm ++ [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName] ++
        (if nm = ConLeche.natBeqName || nm = ConLeche.natBleName ||
            ConLeche.natDivModNames.contains nm then
          [ConLeche.boolName, ConLeche.boolTrueName, ConLeche.boolFalseName] else [])) := by
  simp only [Arena.pinFootprintNat, Arena.natBeqName, Arena.pinNatBeq, Arena.natBleName,
    Arena.pinNatBle, Arena.boolName, Arena.pinBool, Arena.boolTrueName, Arena.pinBoolTrue,
    Arena.boolFalseName, Arena.pinBoolFalse] at hrun
  obtain ⟨deps, s0, g0, r0⟩ := AM.bind_ok hrun
  have p0 := natOpDeps_state hp g0
  obtain ⟨-, -, -, -, d0⟩ := natOpDeps_run hok hp hn g0
  subst s0
  obtain ⟨lits, s1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨p1, d1⟩ := Inductives.litGuardNames_run hp g1
  subst s1
  obtain ⟨be, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨p2, d2⟩ := pinAt_run (x := ConLeche.natBeqName) hp (by rfl) g2
  subst s2
  obtain ⟨bl, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨p3, d3⟩ := pinAt_run (x := ConLeche.natBleName) hp (by rfl) g3
  subst s3
  have hbase : NamesCover s.store (nidxAppend deps lits 0 3)
      (ConLeche.natOpDeps nm ++ [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName]) := by
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero]
    exact ((NamesCover.of_denoteNL d0).sub fun k hk => List.mem_append_left _ hk).append
      ((NamesCover.of_denoteNL (denoteNL_take 3 d1)).sub fun k hk => List.mem_append_right _ hk)
  have hcond : ((n == be || n == bl || dms.contains n) = true) ↔
      ((nm = ConLeche.natBeqName || nm = ConLeche.natBleName ||
        ConLeche.natDivModNames.contains nm) = true) := by
    rw [denoteNL_contains hok.wf hdms hn]
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_handle_iff hok.wf hn d2,
      beq_handle_iff hok.wf hn d3]
  rcases AM.ite_ok r3 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨b, s4, g4, r4⟩ := AM.bind_ok k
    obtain ⟨p4, d4⟩ := pinAt_run (x := ConLeche.boolName) hp (by rfl) g4
    subst s4
    obtain ⟨bt, s5, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨p5, d5⟩ := pinAt_run (x := ConLeche.boolTrueName) hp (by rfl) g5
    subst s5
    obtain ⟨bf, s6, g6, r6⟩ := AM.bind_ok r5
    obtain ⟨p6, d6⟩ := pinAt_run (x := ConLeche.boolFalseName) hp (by rfl) g6
    subst s6
    obtain ⟨hr, hs⟩ := AM.pure_ok r6
    subst hr hs
    rw [ite_eq_left (hcond.mp hb)]
    refine ⟨rfl, (hbase.sub fun k hk =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hk))).append ?_⟩
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨b, by simp, d4⟩
    · exact ⟨bt, by simp, d5⟩
    · exact ⟨bf, by simp, d6⟩
  · obtain ⟨hr, hs⟩ := AM.pure_ok k
    subst hr hs
    rw [ite_eq_right (fun h => hb (hcond.mpr h)), List.append_nil]
    exact ⟨rfl, hbase⟩

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — **the names a pinned constant's
fast path reads, covered**. -/
theorem pinFootprint_run {n : NIdx} {nm : ConLeche.Name} {r : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.pinFootprint n s = .ok (r, s')) :
    s' = s ∧ NamesCover s.store r (ConLeche.pinFootprint nm) := by
  simp only [Arena.pinFootprint] at hrun
  obtain ⟨ops, s0, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨p0, d0⟩ := natOpNames_run hp g0
  subst s0
  obtain ⟨dms, s1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨p1, d1⟩ := natDivModNames_run hp g1
  subst s1
  have hcond : ((ops.contains n || dms.contains n) = true) ↔
      ((ConLeche.natOpNames.contains nm || ConLeche.natDivModNames.contains nm) = true) := by
    rw [denoteNL_contains hok.wf d0 hn, denoteNL_contains hok.wf d1 hn]
  unfold ConLeche.pinFootprint
  rcases AM.ite_ok r1 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨xs, s2, g2, r2⟩ := AM.bind_ok k
    obtain ⟨p2, c2⟩ := pinFootprintNat_run hok hp hn d1 g2
    subst s2
    obtain ⟨p3, hsub, c3⟩ := pinFootprintReduce_run hok hp hn r2
    subst s'
    rw [ite_eq_left (hcond.mp hb)]
    exact ⟨rfl, (c2.sub hsub).append c3⟩
  · obtain ⟨p3, -, c3⟩ := pinFootprintReduce_run hok hp hn k
    subst s'
    rw [ite_eq_right (fun h => hb (hcond.mpr h)), List.nil_append]
    exact ⟨rfl, c3⟩

/-! ## upstream -/

/-- con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo — con-leche's walk only adds names of
`Expr.needs`. -/
theorem needsGoU_sub : ∀ (t : Expr) (seen : Std.HashSet Expr) (acc : Array Name) (m : Name),
    m ∈ (ConLeche.Cached.needsGo seen acc t).2 → m ∈ acc ∨ m ∈ t.needs := by
  intro t
  induction t with
  | bvar i => intro seen acc m h; simp [ConLeche.Cached.needsGo] at h; exact .inl h
  | sort u => intro seen acc m h; simp [ConLeche.Cached.needsGo] at h; exact .inl h
  | lit l => intro seen acc m h; simp only [ConLeche.Cached.needsGo] at h; rw [← Array.mem_toList_iff] at h ⊢; simpa [Expr.needs] using h
  | const n us => intro seen acc m h; simp [ConLeche.Cached.needsGo] at h; simpa [Expr.needs] using h
  | fvar k ty ih =>
    intro seen acc m h; simp only [ConLeche.Cached.needsGo] at h
    split at h
    · exact .inl h
    · rcases ih _ _ m h with h | h <;> simp_all [Expr.needs]
  | app f a ihf iha =>
    intro seen acc m h; simp only [ConLeche.Cached.needsGo] at h
    split at h
    · exact .inl h
    · rcases iha _ _ m h with h | h
      · rcases ihf _ _ m h with h | h <;> simp_all [Expr.needs]
      · simp_all [Expr.needs]
  | lam ty b iht ihb =>
    intro seen acc m h; simp only [ConLeche.Cached.needsGo] at h
    split at h
    · exact .inl h
    · rcases ihb _ _ m h with h | h
      · rcases iht _ _ m h with h | h <;> simp_all [Expr.needs]
      · simp_all [Expr.needs]
  | forallE ty b iht ihb =>
    intro seen acc m h; simp only [ConLeche.Cached.needsGo] at h
    split at h
    · exact .inl h
    · rcases ihb _ _ m h with h | h
      · rcases iht _ _ m h with h | h <;> simp_all [Expr.needs]
      · simp_all [Expr.needs]
  | letE ty v b iht ihv ihb =>
    intro seen acc m h; simp only [ConLeche.Cached.needsGo] at h
    split at h
    · exact .inl h
    · rcases ihb _ _ m h with h | h
      · rcases ihv _ _ m h with h | h
        · rcases iht _ _ m h with h | h <;> simp_all [Expr.needs]
        · simp_all [Expr.needs]
      · simp_all [Expr.needs]
  | proj s i x ih =>
    intro seen acc m h; simp only [ConLeche.Cached.needsGo] at h
    split at h
    · exact .inl h
    · rcases ih _ _ m h with h | h
      · simp at h; rcases h with h | h <;> simp_all [Expr.needs]
      · simp_all [Expr.needs]

/-- con-leche: ConLeche/Cached/Needs.lean:74-75 NeedsSt.expr — the same over a list of
expressions. -/
theorem foldExprsU_sub : ∀ (es : List Expr) (x : ConLeche.Cached.NeedsSt) (m : ConLeche.Name),
    m ∈ (es.foldl ConLeche.Cached.NeedsSt.expr x).2 → m ∈ x.2 ∨ m ∈ es.flatMap Expr.needs
  | [], x, m, h => .inl h
  | e :: es, x, m, h => by
    rcases foldExprsU_sub es (x.expr e) m h with h | h
    · rcases needsGoU_sub e x.1 x.2 m h with h | h
      · exact .inl h
      · exact .inr (List.mem_append_left _ h)
    · exact .inr (List.mem_append_right _ h)

/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — the names a rule reads. -/
@[expose] def specRule (r : RecRule) : List ConLeche.Name :=
  r.rhs.needs ++ [r.ctor] ++
    (match r.fire with | .nested _ pins => pins.flatMap Expr.needs | _ => [])

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — the names a constant's laws read. -/
@[expose] def specConst (c : ConstantInfo) : List ConLeche.Name :=
  c.toConstantVal.type.needs ++
    (match c with
      | .defnInfo _ v _ => v.needs
      | .recInfo _ _ _ _ rules => rules.flatMap specRule
      | .indInfo _ caps => caps.all
      | _ => []) ++ ConLeche.pinFootprint c.toConstantVal.name

/-- con-leche: ConLeche/Cached/Needs.lean:97-99 NeedsSt.table — the names a table reads. -/
@[expose] def specTable (t : ProjTable) : List ConLeche.Name :=
  [t.structName, t.ctor] ++ t.bodies.toList.flatMap Expr.needs

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — the names a table lookup's answer
reads. -/
@[expose] def specOptTable : Option ProjTable → List ConLeche.Name
  | some t => specTable t
  | none => []

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — **the names `entryNeeds` lists**, as a list:
the laws', a type former's constructors and recursors, the mates, the table's. -/
@[expose] def specEntry (mates : Std.HashMap ConLeche.Name (Array ConLeche.Name))
    (findT : ConLeche.Name → Option ProjTable) (c : ConstantInfo) : List ConLeche.Name :=
  specConst c ++
    (match c with
      | .indInfo _ caps => caps.ctors ++ caps.all.map (fun m : ConLeche.Name => m.str "rec")
      | _ => []) ++ (mates.getD c.toConstantVal.name #[]).toList ++
    specOptTable (findT c.toConstantVal.name)

/-- con-leche: ConLeche/Cached/Needs.lean:77-78 NeedsSt.names — the names added are the names
given. -/
theorem namesU_sub (x : ConLeche.Cached.NeedsSt) (ns : List ConLeche.Name) (m : ConLeche.Name)
    (h : m ∈ (x.names ns).2) : m ∈ x.2 ∨ m ∈ ns := by
  simp only [ConLeche.Cached.NeedsSt.names] at h
  rw [← Array.mem_toList_iff] at h ⊢
  simpa using h

/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — a rule adds only `specRule`'s
names. -/
theorem ruleU_sub (x : ConLeche.Cached.NeedsSt) (r : RecRule) (m : ConLeche.Name)
    (h : m ∈ (x.rule r).2) : m ∈ x.2 ∨ m ∈ specRule r := by
  have step : ∀ m, m ∈ ((x.expr r.rhs).names [r.ctor]).2 → m ∈ x.2 ∨ m ∈ r.rhs.needs ++ [r.ctor] := by
    intro m hm
    rcases namesU_sub _ _ m hm with hm | hm
    · rcases needsGoU_sub r.rhs x.1 x.2 m hm with hm | hm
      · exact .inl hm
      · exact .inr (List.mem_append_left _ hm)
    · exact .inr (List.mem_append_right _ hm)
  unfold ConLeche.Cached.NeedsSt.rule at h
  unfold specRule
  split at h
  · next pins hf =>
    rw [hf]
    rcases foldExprsU_sub pins _ m h with hm | hm
    · rcases step m hm with hm | hm
      · exact .inl hm
      · exact .inr (List.mem_append_left _ hm)
    · exact .inr (List.mem_append_right _ hm)
  · next hf =>
    rcases step m h with hm | hm
    · exact .inl hm
    · refine .inr (List.mem_append_left _ hm)

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — the rules' fold. -/
theorem foldRulesU_sub : ∀ (rs : List RecRule) (x : ConLeche.Cached.NeedsSt) (m : ConLeche.Name),
    m ∈ (rs.foldl ConLeche.Cached.NeedsSt.rule x).2 → m ∈ x.2 ∨ m ∈ rs.flatMap specRule
  | [], x, m, h => .inl h
  | r :: rs, x, m, h => by
    rcases foldRulesU_sub rs (x.rule r) m h with h | h
    · rcases ruleU_sub x r m h with h | h
      · exact .inl h
      · exact .inr (List.mem_append_left _ h)
    · exact .inr (List.mem_append_right _ h)

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — a constant adds only `specConst`'s
names. -/
theorem constU_sub (x : ConLeche.Cached.NeedsSt) (c : ConstantInfo) (m : ConLeche.Name)
    (h : m ∈ (x.const c).2) : m ∈ x.2 ∨ m ∈ specConst c := by
  unfold ConLeche.Cached.NeedsSt.const at h
  rcases namesU_sub _ _ m h with h | h
  · have hty : ∀ m, m ∈ (x.expr c.toConstantVal.type).2 → m ∈ x.2 ∨ m ∈ specConst c := by
      intro m hm
      rcases needsGoU_sub _ x.1 x.2 m hm with hm | hm
      · exact .inl hm
      · exact .inr (List.mem_append_left _ (List.mem_append_left _ hm))
    cases c with
    | defnInfo cv v hint =>
      rcases needsGoU_sub v _ _ m h with h | h
      · exact hty m h
      · exact .inr (List.mem_append_left _ (List.mem_append_right _ h))
    | recInfo cv mI rP isK rules =>
      rcases foldRulesU_sub rules _ m h with h | h
      · exact hty m h
      · exact .inr (List.mem_append_left _ (List.mem_append_right _ h))
    | indInfo cv caps =>
      rcases namesU_sub _ _ m h with h | h
      · exact hty m h
      · exact .inr (List.mem_append_left _ (List.mem_append_right _ h))
    | axiomInfo cv => exact hty m h
    | thmInfo cv => exact hty m h
    | ctorInfo cv a b T => exact hty m h
  · exact .inr (List.mem_append_right _ h)

/-- con-leche: ConLeche/Cached/Needs.lean:97-99 NeedsSt.table — a table adds only `specTable`'s
names. -/
theorem tableU_sub (x : ConLeche.Cached.NeedsSt) (t : ProjTable) (m : ConLeche.Name)
    (h : m ∈ (x.table t).2) : m ∈ x.2 ∨ m ∈ specTable t := by
  unfold ConLeche.Cached.NeedsSt.table at h
  rcases foldExprsU_sub _ _ m h with h | h
  · rcases namesU_sub _ _ m h with h | h
    · exact .inl h
    · exact .inr (List.mem_append_left _ h)
  · exact .inr (List.mem_append_right _ h)

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — the mates and the table. -/
theorem entryTailU_sub (x : ConLeche.Cached.NeedsSt) (A : List ConLeche.Name)
    (hx : ∀ m, m ∈ x.2 → m ∈ A) (ms : List ConLeche.Name) (o : Option ProjTable)
    (m : ConLeche.Name)
    (h : m ∈ (match o with
      | some t => ((x.names ms).table t).2
      | none => (x.names ms).2)) :
    m ∈ A ++ ms ++ specOptTable o := by
  cases o with
  | some t =>
    rcases tableU_sub _ t m h with h | h
    · rcases namesU_sub _ _ m h with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ (hx m h))
      · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h
  | none =>
    rcases namesU_sub _ _ m h with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (hx m h))
    · exact List.mem_append_left _ (List.mem_append_right _ h)

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — **con-leche's entry lists only
`specEntry`'s names**. -/
theorem entryNeedsU_sub (mates : Std.HashMap ConLeche.Name (Array ConLeche.Name))
    (findT : ConLeche.Name → Option ProjTable) (c : ConstantInfo) (m : ConLeche.Name)
    (h : m ∈ (ConLeche.Cached.entryNeeds mates findT c).toList) : m ∈ specEntry mates findT c := by
  rw [Array.mem_toList_iff] at h
  have h0 : ∀ m, m ∈ (ConLeche.Cached.NeedsSt.const ({}, #[]) c).2 → m ∈ specConst c := by
    intro m hm
    rcases constU_sub _ c m hm with hm | hm
    · simp at hm
    · exact hm
  cases c
  case indInfo cv caps =>
    simp only [ConLeche.Cached.entryNeeds, specEntry] at h ⊢
    refine entryTailU_sub _ _ (fun m hm => ?_) _ _ m h
    rcases namesU_sub _ _ m hm with hm | hm
    · exact List.mem_append_left _ (h0 _ hm)
    · exact List.mem_append_right _ hm
  all_goals
    simp only [ConLeche.Cached.entryNeeds, specEntry] at h ⊢
    exact entryTailU_sub _ _ (fun m hm => List.mem_append_left _ (h0 _ hm)) _ _ m h


/-! ## The twin's walks over several expressions -/

/-- con-leche: none — one twin step's result: the memo's invariant, the names so far kept, `L`
covered. -/
@[expose] def TOut (st : EStore) (x y : Arena.NeedsSt) (L : List ConLeche.Name) : Prop :=
  NeedsInvT st y.seen y.acc ∧ (∀ k ∈ x.acc, k ∈ y.acc) ∧ NamesCover st y.acc L

/-- con-leche: none — two steps in sequence. -/
theorem TOut.trans {st : EStore} {x y z : Arena.NeedsSt} {L L' : List ConLeche.Name}
    (h : TOut st x y L) (h' : TOut st y z L') : TOut st x z (L ++ L') :=
  ⟨h'.1, fun k hk => h'.2.1 k (h.2.1 k hk), (h.2.2.sub h'.2.1).append h'.2.2⟩

/-- con-leche: none — no step. -/
theorem TOut.refl {st : EStore} {x : Arena.NeedsSt} (h : NeedsInvT st x.seen x.acc) :
    TOut st x x [] :=
  ⟨h, fun _ hk => hk, NamesCover.nil _ _⟩

/-- con-leche: none — a cover survives a store extension. -/
theorem NamesCover.mono {st st' : EStore} {hs : List NIdx} {L : List ConLeche.Name}
    (h : NamesCover st hs L) (hx : Ext st st') : NamesCover st' hs L :=
  fun m hm => let ⟨k, hk, hd⟩ := h m hm; ⟨k, hk, denoteN_ext hd hx⟩

/-- con-leche: none — the memo's invariant survives a store extension. -/
theorem NeedsInvT.mono {st st' : EStore} {seen : Std.HashMap EIdx Bool} {acc : List NIdx}
    (h : NeedsInvT st seen acc) (hx : Ext st st') : NeedsInvT st' seen acc :=
  fun k b hk => let ⟨t, ht, hc⟩ := h k b hk; ⟨t, denote_ext ht hx, hc.mono hx⟩

/-- con-leche: none — a step's result survives a store extension. -/
theorem TOut.mono {st st' : EStore} {x y : Arena.NeedsSt} {L : List ConLeche.Name}
    (h : TOut st x y L) (hx : Ext st st') : TOut st' x y L :=
  ⟨h.1.mono hx, h.2.1, h.2.2.mono hx⟩

/-- con-leche: ConLeche/Cached/Needs.lean:77-78 NeedsSt.names — some names. -/
theorem names_runT {st : EStore} {x : Arena.NeedsSt} {ns : List NIdx} {L : List ConLeche.Name}
    (hx : NeedsInvT st x.seen x.acc) (hL : NamesCover st ns L) : TOut st x (x.names ns) L := by
  have hsub : ∀ k ∈ x.acc, k ∈ (x.names ns).acc := fun k hk => by
    simp [Arena.NeedsSt.names, nidxAppend, hk]
  refine ⟨hx.sub hsub, hsub, hL.sub fun k hk => ?_⟩
  simp [Arena.NeedsSt.names, nidxAppend, hk]

/-- con-leche: ConLeche/Cached/Needs.lean:77-78 NeedsSt.names — one name. -/
theorem name_runT {st : EStore} {x : Arena.NeedsSt} {n : NIdx} {nm : ConLeche.Name}
    (hx : NeedsInvT st x.seen x.acc) (hn : denoteN st.ns n = some nm) :
    TOut st x (x.name n) [nm] := by
  have hsub : ∀ k ∈ x.acc, k ∈ (x.name n).acc := fun k hk => by
    simp [Arena.NeedsSt.name, hk]
  refine ⟨hx.sub hsub, hsub, ?_⟩
  intro m hm
  rw [List.mem_singleton] at hm
  subst hm
  exact ⟨n, by simp [Arena.NeedsSt.name], hn⟩

/-- con-leche: ConLeche/Cached/Needs.lean:74-75 NeedsSt.expr — one expression's names. -/
theorem expr_runT {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {e : EIdx} {t : Expr} (hx : NeedsInvT s.store x.seen x.acc)
    (he : denoteE s.store e = some t) (hrun : x.expr e s = .ok (y, s')) :
    s' = s ∧ TOut s.store x y t.needs := by
  simp only [Arena.NeedsSt.expr] at hrun
  obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, i1, i2, i3⟩ := needsGo_cov s hok hp _ e x.seen x.acc hx he h1
  subst s1
  obtain ⟨hr, hs⟩ := AM.pure_ok h2
  subst hr hs
  exact ⟨rfl, i1, i2, i3⟩

/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — the cited `pins.foldl
NeedsSt.expr`. -/
theorem exprs_runT {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (es : List EIdx) (ts : List Expr) (x : Arena.NeedsSt) {y : Arena.NeedsSt} {s' : AState},
      NeedsInvT s.store x.seen x.acc → Frontend.denoteEList s.store es = some ts →
      x.exprs es s = .ok (y, s') → s' = s ∧ TOut s.store x y (ts.flatMap Expr.needs)
  | [], ts, x, y, s', hx, hts, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hts
    subst hts
    simp only [Arena.NeedsSt.exprs] at hrun
    obtain ⟨hr, hs⟩ := AM.pure_ok hrun
    subst hr hs
    exact ⟨rfl, TOut.refl hx⟩
  | e :: es, ts, x, y, s', hx, hts, hrun => by
    obtain ⟨t, ts', he, hes, rfl⟩ := denoteEList_cons_inv hts
    simp only [Arena.NeedsSt.exprs] at hrun
    obtain ⟨x2, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, o1⟩ := expr_runT hok hp hx he h1
    subst s1
    obtain ⟨hs2, o2⟩ := exprs_runT hok hp es ts' x2 o1.1 hes h2
    exact ⟨hs2, by simpa using o1.trans o2⟩


/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — what a recursor rule reads. -/
theorem rule_runT {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {r : IRecRule} {R : RecRule} (hx : NeedsInvT s.store x.seen x.acc)
    (hR : Frontend.denoteRule s.store r = some R) (hrun : x.rule r s = .ok (y, s')) :
    s' = s ∧ TOut s.store x y (specRule R) := by
  obtain ⟨hc, hf, hrhs, -⟩ := denoteRule_inv hR
  simp only [Arena.NeedsSt.rule] at hrun
  obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, o1⟩ := expr_runT hok hp hx hrhs h1
  subst s1
  have o2 := o1.trans (name_runT o1.1 hc)
  unfold specRule
  cases hfr : r.fire with
  | nested lvls pins =>
    rw [hfr] at h2 hf
    rw [denoteFire_nested_opt] at hf
    simp only [opt2] at hf
    split at hf
    · next ls ps hls hps =>
      have hRf : R.fire = .nested ls ps := (Option.some.inj hf).symm
      rw [hRf]
      simp only at h2
      obtain ⟨hs2, o3⟩ := exprs_runT hok hp pins ps _ o2.1 hps h2
      exact ⟨hs2, o2.trans o3⟩
    · exact absurd hf (by simp)
  | plain =>
    rw [hfr] at h2 hf
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    rw [← hf]
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    exact ⟨rfl, by simpa using o2⟩
  | levels lvls =>
    rw [hfr] at h2 hf
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨_, -, hf⟩ := hf
    rw [← hf]
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    exact ⟨rfl, by simpa using o2⟩

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — the cited `rules.foldl
NeedsSt.rule`. -/
theorem rules_runT {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (rs : List IRecRule) (Rs : List RecRule) (x : Arena.NeedsSt) {y : Arena.NeedsSt}
      {s' : AState},
      NeedsInvT s.store x.seen x.acc → Frontend.denoteRules s.store rs = some Rs →
      x.rules rs s = .ok (y, s') → s' = s ∧ TOut s.store x y (Rs.flatMap specRule)
  | [], Rs, x, y, s', hx, hRs, hrun => by
    simp only [Frontend.denoteRules, Option.some.injEq] at hRs
    subst hRs
    simp only [Arena.NeedsSt.rules] at hrun
    obtain ⟨hr, hs⟩ := AM.pure_ok hrun
    subst hr hs
    exact ⟨rfl, TOut.refl hx⟩
  | r :: rs, Rs, x, y, s', hx, hRs, hrun => by
    obtain ⟨R, Rs', hR, hRs', rfl⟩ := denoteRules_cons hRs
    simp only [Arena.NeedsSt.rules] at hrun
    obtain ⟨x2, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, o1⟩ := rule_runT hok hp hx hR h1
    subst s1
    obtain ⟨hs2, o2⟩ := rules_runT hok hp rs Rs' x2 o1.1 hRs' h2
    exact ⟨hs2, by simpa using o1.trans o2⟩

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — the pin's fast-path names. -/
theorem constTail_runT {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    {x2 y : Arena.NeedsSt} {n : NIdx} {nm : ConLeche.Name}
    (hx : NeedsInvT s.store x2.seen x2.acc) (hn : denoteN s.store.ns n = some nm)
    (hrun : (do let fp ← Arena.pinFootprint n; pure (x2.names fp) : AM _) s = .ok (y, s')) :
    s' = s ∧ TOut s.store x2 y (ConLeche.pinFootprint nm) := by
  obtain ⟨fp, s3, h5, h6⟩ := AM.bind_ok hrun
  obtain ⟨hs3, hfp⟩ := pinFootprint_run hok hp hn h5
  subst s3
  obtain ⟨hr, hs⟩ := AM.pure_ok h6
  subst hr hs
  exact ⟨rfl, names_runT hx hfp⟩

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — **what a constant's laws read,
covered**. -/
theorem const_runT {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {ci : IConstantInfo} {c : ConstantInfo} (hx : NeedsInvT s.store x.seen x.acc)
    (hc : Frontend.denoteCI s.store ci = some c) (hrun : x.const ci s = .ok (y, s')) :
    s' = s ∧ TOut s.store x y (specConst c) := by
  obtain ⟨-, -, hty⟩ := denoteCV_inv (denoteCI_toConstantVal hc)
  have hn := denoteCI_name hc
  simp only [Arena.NeedsSt.const] at hrun
  obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, o1⟩ := expr_runT hok hp hx hty h1
  subst s1
  unfold specConst
  cases ci with
  | defnInfo v e hint =>
    obtain ⟨cv, xv, rfl, -, hxv⟩ := denoteCI_defn_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, o2⟩ := expr_runT hok hp o1.1 hxv h3
    subst s2
    obtain ⟨hs3, o3⟩ := constTail_runT hok hp o2.1 hn h4
    exact ⟨hs3, (o1.trans o2).trans o3⟩
  | recInfo v mI rP k rs =>
    obtain ⟨cv, Rs, rfl, -, hRs⟩ := denoteCI_rec_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, o2⟩ := rules_runT hok hp rs Rs x1 o1.1 hRs h3
    subst s2
    obtain ⟨hs3, o3⟩ := constTail_runT hok hp o2.1 hn h4
    exact ⟨hs3, (o1.trans o2).trans o3⟩
  | indInfo v cap =>
    obtain ⟨cv, d, rfl, -, hd⟩ := denoteCI_ind_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hr, hs⟩ := AM.pure_ok h3
    subst hr hs
    simp only [Frontend.denoteCaps] at hd
    split at hd
    · next all ctors hall hctors =>
      obtain rfl := (Option.some.inj hd).symm
      have o2 := names_runT o1.1 (NamesCover.of_denoteNL (denoteNL_of_denoteNList _ _ hall))
      obtain ⟨hs3, o3⟩ := constTail_runT hok hp o2.1 hn h4
      exact ⟨hs3, (o1.trans o2).trans o3⟩
    · exact absurd hd (by simp)
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hr, hs⟩ := AM.pure_ok h3
    subst hr hs
    obtain ⟨hs3, o3⟩ := constTail_runT hok hp o1.1 hn h4
    exact ⟨hs3, ((o1.trans (TOut.refl o1.1)).trans o3)⟩
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hr, hs⟩ := AM.pure_ok h3
    subst hr hs
    obtain ⟨hs3, o3⟩ := constTail_runT hok hp o1.1 hn h4
    exact ⟨hs3, ((o1.trans (TOut.refl o1.1)).trans o3)⟩
  | ctorInfo v nP nF T =>
    obtain ⟨cv, rfl, -⟩ := denoteCI_ctor_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hr, hs⟩ := AM.pure_ok h3
    subst hr hs
    obtain ⟨hs3, o3⟩ := constTail_runT hok hp o1.1 hn h4
    exact ⟨hs3, ((o1.trans (TOut.refl o1.1)).trans o3)⟩

/-- con-leche: ConLeche/Cached/Needs.lean:97-99 NeedsSt.table — what a table reads. -/
theorem table_runT {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {t : IProjTable} {pt : ProjTable} (hx : NeedsInvT s.store x.seen x.acc)
    (ht : Frontend.denoteProjTable s.store t = some pt) (hrun : x.table t s = .ok (y, s')) :
    s' = s ∧ TOut s.store x y (specTable pt) := by
  rw [denoteProjTable_opt, denoteEArray_map] at ht
  simp only [opt2, opt3] at ht
  split at ht
  · next a b hab hb =>
    split at hab
    · next sn lps c hsn hlps hc =>
      obtain rfl := (Option.some.inj hab).symm
      simp only [Option.map_eq_some_iff] at hb
      obtain ⟨bs, hbs, rfl⟩ := hb
      obtain rfl := (Option.some.inj ht).symm
      simp only [Arena.NeedsSt.table] at hrun
      have o1 := (name_runT hx hsn).trans (name_runT (name_runT hx hsn).1 hc)
      obtain ⟨hs1, o2⟩ := exprs_runT hok hp t.bodies.toList bs _ o1.1 hbs hrun
      refine ⟨hs1, ?_⟩
      unfold specTable
      simpa using o1.trans o2
    · exact absurd hab (by simp)
  · exact absurd ht (by simp)

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — `caps.all.map (·.str "rec")`,
interned. -/
theorem recNames_runT {s : AState} (hok : StateOK s) :
    ∀ (ms : List NIdx) (L : List ConLeche.Name) (out : List NIdx) {r : List NIdx}
      {s' : AState}, Frontend.denoteNList s.store.ns ms = some L →
      Arena.recNames out ms s = .ok (r, s') →
      Frontend.IStepS s s' ∧ (∀ k ∈ out, k ∈ r) ∧
        NamesCover s'.store r (L.map fun m : ConLeche.Name => m.str "rec")
  | [], L, out, r, s', hL, hrun => by
    simp only [Frontend.denoteNList, Option.some.injEq] at hL
    subst hL
    simp only [Arena.recNames] at hrun
    obtain ⟨hr, hs⟩ := AM.pure_ok hrun
    subst hr hs
    exact ⟨Frontend.IStepS.refl hok, fun _ hk => hk, NamesCover.nil _ _⟩
  | m :: ms, L, out, r, s', hL, hrun => by
    obtain ⟨y, ys, hy, hys, rfl⟩ := denoteNList_cons_inv hL
    simp only [Arena.recNames] at hrun
    obtain ⟨n, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨st1, hn⟩ := Frontend.internNNode_sstep hok
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc
          exact nview_isSome_of_denote hy) h1
    have hn' : denoteN s1.store.ns n = some (y.str "rec") := by
      rw [hn, denoteNView, denoteN_ext hy st1.ext, Option.map_some]
    obtain ⟨st2, hsub, hcov⟩ := recNames_runT st1.ok ms ys (out ++ [n])
      (denoteNListE_ext st1.ext _ _ hys) h2
    refine ⟨st1.trans st2, fun k hk => hsub k (List.mem_append_left _ hk), ?_⟩
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨n, hsub n (by simp), denoteN_ext hn' st2.ext⟩
    · exact hcov x hx


/-! ## A constant's entry -/

/-- con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates — the twin's record mates denote
con-leche's: at every denoting key, the twin's mates cover
con-leche's; and every name con-leche's mates map to something is denoted -/
@[expose] def MatesDen (st : EStore) (mates : Std.HashMap NIdx (List NIdx))
    (matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)) : Prop :=
  (∀ n nm, denoteN st.ns n = some nm →
    NamesCover st ((mates[n]?).getD []) (matesU.getD nm #[]).toList) ∧
  ∀ nm m, m ∈ (matesU.getD nm #[]).toList → ∃ n, denoteN st.ns n = some nm

/-- con-leche: none — the mates' denotation survives a store extension. -/
theorem MatesDen.mono {st st' : EStore} {mates : Std.HashMap NIdx (List NIdx)}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (h : MatesDen st mates matesU) (hwf : StoreWF st') (hx : Ext st st') :
    MatesDen st' mates matesU := by
  refine ⟨fun n nm hn m hm => ?_, fun nm m hm => ?_⟩
  · obtain ⟨n0, hn0⟩ := h.2 nm m hm
    have he := denoteN_injS hwf (denoteN_ext hn0 hx) hn
    rw [← he]
    exact (h.1 n0 nm hn0).mono hx m hm
  · obtain ⟨n0, hn0⟩ := h.2 nm m hm
    exact ⟨n0, denoteN_ext hn0 hx⟩

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — the record's mates. -/
theorem mates_runT {st : EStore} {mates : Std.HashMap NIdx (List NIdx)}
    {L : List ConLeche.Name} {y : Arena.NeedsSt} {n : NIdx}
    (hc : NamesCover st ((mates[n]?).getD []) L) (hy : NeedsInvT st y.seen y.acc) :
    TOut st y (match mates[n]? with | some ms => y.names ms | none => y) L := by
  split
  · next ms hms =>
    rw [hms] at hc
    exact names_runT hy hc
  · next hms =>
    rw [hms] at hc
    refine ⟨hy, fun _ hk => hk, fun m hm' => ?_⟩
    obtain ⟨k, hk, -⟩ := hc m hm'
    exact absurd hk (by simp)

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — the mates' state, then the
projection table, at the environment's table lookup. -/
theorem entryTail_runT {env : Env} {fe : IFEnv} {s s' : AState} (hck : CheckOK false env fe s)
    {y x3 : Arena.NeedsSt} {L : List ConLeche.Name} {n : NIdx} {nm : ConLeche.Name}
    {ns : List NIdx} (hn : denoteN s.store.ns n = some nm) (hx : TOut s.store y x3 L)
    (hrun : (match fe.findTable? n with
      | some t => do
        let x4 ← x3.table t
        pure x4.acc
      | none => pure x3.acc : AM (List NIdx)) s = .ok (ns, s')) :
    s' = s ∧ (∀ k ∈ y.acc, k ∈ ns) ∧ NamesCover s.store ns (L ++ specOptTable (env.findTable? nm)) := by
  have hok := hck.state
  have hp := hck.pins
  cases hf : fe.findTable? n with
  | some t =>
    rw [hf] at hrun
    simp only at hrun
    obtain ⟨nm', pt, hn', hpt, henv, -⟩ := hck.ienv.tblHit n t hf
    rw [hn] at hn'
    obtain rfl := Option.some.inj hn'
    obtain ⟨x4, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, o⟩ := table_runT hok hp hx.1 hpt h1
    subst s1
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    rw [henv]
    have := hx.trans o
    exact ⟨rfl, this.2.1, this.2.2⟩
  | none =>
    rw [hf] at hrun
    simp only at hrun
    obtain ⟨hr, hs⟩ := AM.pure_ok hrun
    subst hr hs
    have henv : env.findTable? nm = none := by
      cases he : env.findTable? nm with
      | none => rfl
      | some pt =>
        obtain ⟨n', t, hn', hf', -⟩ := hck.ienv.tblCover nm pt he
        rw [denoteN_injS hok.wf hn' hn, hf] at hf'
        exact nomatch hf'
    rw [henv]
    exact ⟨rfl, hx.2.1, by simpa [specOptTable] using hx.2.2⟩

/-- con-leche: none — only a type former denotes a type former. -/
theorem denoteCI_ind_of {st : EStore} {ci : IConstantInfo} {cv : ConstantVal} {caps : IndCaps}
    (h : Frontend.denoteCI st ci = some (.indInfo cv caps)) :
    ∃ v cap, ci = .indInfo v cap := by
  cases ci <;> simp only [Frontend.denoteCI] at h <;> (try split at h) <;> simp_all

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — **what the justification
follows from a constant, covered**: every name con-leche's `entryNeeds` lists (at the
environment's table lookup and con-leche's record mates) is denoted by a name the twin's
lists. -/
theorem entryNeeds_run {env : Env} {fe : IFEnv} {s s' : AState} {ci : IConstantInfo}
    {c : ConstantInfo} {mates : Std.HashMap NIdx (List NIdx)}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} {ns : List NIdx}
    (hck : CheckOK false env fe s)
    (hc : Frontend.denoteCI s.store ci = some c) (hm : MatesDen s.store mates matesU)
    (hrun : Arena.entryNeeds mates fe ci s = .ok (ns, s')) :
    RStep s s' ∧
      NamesCover s'.store ns (ConLeche.Cached.entryNeeds matesU env.findTable? c).toList := by
  have hok := hck.state
  have hp := hck.pins
  have hr0 := hck.readOK
  have hn : denoteN s.store.ns ci.name = some c.toConstantVal.name := denoteCI_name hc
  have hcov : ∀ {s' : AState}, RStep s s' → NamesCover s'.store ns (specEntry matesU env.findTable? c) →
      RStep s s' ∧
        NamesCover s'.store ns (ConLeche.Cached.entryNeeds matesU env.findTable? c).toList :=
    fun hst h => ⟨hst, fun m hm' => h m (entryNeedsU_sub _ _ _ m hm')⟩
  simp only [Arena.entryNeeds] at hrun
  obtain ⟨x0, s1, h1, h2⟩ := AM.bind_ok hrun
  have hinv0 : NeedsInvT s.store Arena.NeedsSt.empty.seen Arena.NeedsSt.empty.acc :=
    fun k b hk => by simp [Arena.NeedsSt.empty] at hk
  obtain ⟨hs1, o0⟩ := const_runT hok hp hinv0 hc h1
  subst s1
  have hmc := hm.1 _ _ hn
  cases ci
  case indInfo v cap =>
    obtain ⟨cv, d, rfl, -, hd⟩ := denoteCI_ind_inv hc
    simp only [Frontend.denoteCaps] at hd
    split at hd
    · next all ctors hall hctors =>
      obtain rfl := (Option.some.inj hd).symm
      obtain ⟨rn, s2, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨st2, hsub2, hrn⟩ := recNames_runT hok cap.all all [] hall h3
      obtain ⟨y, s3, h5, h6⟩ := AM.bind_ok h4
      obtain ⟨hr, hs⟩ := AM.pure_ok h5
      subst hr hs
      have hx2 := st2.ext
      have o1 := names_runT o0.1 (NamesCover.of_denoteNL (denoteNL_of_denoteNList _ _ hctors))
      have o2 := ((o0.trans o1).mono hx2).trans (names_runT (o1.1.mono hx2) hrn)
      have hst2 := RStep.of_istep st2 hr0
      have hck2 := hst2.checkOK hck
      have o3 := o2.trans (mates_runT (hmc.mono hx2) o2.1)
      obtain ⟨hs4, -, hfin⟩ := entryTail_runT hck2 (denoteN_ext hn hx2) o3 h6
      subst hs4
      refine hcov hst2 ?_
      unfold specEntry
      simpa [List.append_assoc] using hfin
    · exact absurd hd (by simp)
  all_goals
    obtain ⟨y, s3, h5, h6⟩ := AM.bind_ok h2
    obtain ⟨hr, hs⟩ := AM.pure_ok h5
    subst hr hs
    have o3 := o0.trans (mates_runT hmc o0.1)
    obtain ⟨hs4, -, hfin⟩ := entryTail_runT hck hn o3 h6
    subst hs4
    refine hcov (RStep.refl hok hr0) ?_
    unfold specEntry
    cases c
    case indInfo cv caps =>
      obtain ⟨_, _, h⟩ := denoteCI_ind_of hc
      exact nomatch h
    all_goals simpa [List.append_assoc] using hfin

/-- con-leche: ConLeche/Cached/Justify.lean:185-196 justifyWhy — **the names a statement's type
reads, covered**: the twin's walk of the type from scratch lists a name denoting each name
con-leche's walk lists. -/
theorem justifyNeeds_run {env : Env} {fe : IFEnv} {s s' : AState} {e : EIdx} {t : Expr}
    {seen : Std.HashMap EIdx Bool} {ns : List NIdx} (hck : CheckOK false env fe s)
    (he : denoteE s.store e = some t)
    (hrun : Arena.needsGo ∅ [] coreWalkFuel e s = .ok ((seen, ns), s')) :
    RStep s s' ∧ NamesCover s'.store ns (ConLeche.Cached.needsGo {} #[] t).2.toList := by
  have hinv0 : NeedsInvT s.store ∅ [] := fun k b hk => by simp at hk
  obtain ⟨hs, -, -, hc⟩ := needsGo_cov s hck.state hck.pins _ e ∅ [] hinv0 he hrun
  subst hs
  refine ⟨RStep.refl hck.state hck.readOK, fun m hm => hc m ?_⟩
  rcases needsGoU_sub t {} #[] m (Array.mem_toList_iff.mp hm) with h | h
  · simp at h
  · exact h

end ConRon.Bridge
