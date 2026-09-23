/-
# `ConRon.Bridge.Promote.Exact` — the promotion is EXACT, and its memo is sound

`Arena/Promote.lean`'s own module note names the obligation this file states:

> `denote (promote h) = denote h` is the exactness lemma P3 owes; it is an
> induction on the recursion below, with `EStore.internPersistent`'s `consP`
> and `derExact` at each node.

Three things are owed at every entry of `Arena/Promote.lean`, and they travel
together because the recursion threads all three:

1. **exactness** — the promoted handle denotes what the original denoted.
   This is the whole soundness content: the promotion is a change of
   REPRESENTATION and of nothing else, so an environment the fold promoted
   denotes the environment it denoted before;
2. **persistence** — the answer is in the persistent tier (`Pers…`,
   `Bridge/Promote/Pers.lean`).  This is what the *next* `dropScratch`
   consumes: `PExt` transports a persistent denotation and nothing else, so
   without this clause the fold's environment would decode to nothing one step
   later;
3. **the memo invariant** `PMemoOK` — every row of the promotion memo is a
   promoted pair.  It is `Bridge/StateOK.lean`'s `MemoOK` shape with
   persistence added and the pure function replaced by the identity: a
   promotion computes nothing, it copies.

`PMemoOK` is stated at the STORE and not at a pure function, which is what
makes `.mono` across an `Ext` the only transport it needs: a row recorded
before an append is still a promoted pair after it.

**Status (task #97-P3-Promote).**  Every statement here is PROVED except one
conjunct: the four handle-kind specs and the declaration layer's four are the
walks of `Bridge/Promote/Walk.lean` / `WalkDecl.lean` (fuel and list
inductions over `EStore.internPersistent_spec'`, at `Arena/WF.lean`'s promote
window invariant `StoreWF'`), and `promoteNew_spec` is `promoteCIList` plus
the two index passes — EXCEPT its `IFEnvCoh fe'` conjunct, which is
`promoteNew_coh` below and is FALSE as stated for `k ≠ 0` (a hash map's
representation depends on its insertion order; `Bridge/Promote/Coh.lean`
proves the extensional coherence instead, at one added precondition).
`Bridge/Checker/**`'s per-declaration brackets read `promoteNew_spec`,
`promoteVG_spec`, `promoteNew_pushed`, `promoteNew_projOK` and
`promoteBracket_close` from this file.
-/
import ConRon.Bridge.Promote.WalkDecl

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-- con-leche: none — arena infrastructure; **`promoteN` is exact.**

PROVED (task #97-P3-Promote): `Bridge/Promote/Walk.lean`'s `promoteN_core`, with `Ext` and the frame from `Arena/PromoteExt.lean`. -/
theorem promoteN_spec {m m' : PMemo} {fuel : Nat} {h r : NIdx} {x : ConLeche.Name}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hd : denoteN s.store.ns h = some x)
    (hrun : promoteN m fuel h s = .ok ((m', r), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersN r ∧ denoteN s'.store.ns r = some x ∧ PFrame s s' := by
  obtain ⟨a, b, c, d⟩ := promoteN_core fuel m h s m' r s' hwf hm hrun
  have hx := promoteN_aext m fuel h s (m', r) s' hrun
  exact ⟨a, hx.ext, b, c, d x hd, PFrame.of_aext hx⟩

/-- con-leche: none — arena infrastructure; **`promoteL` is exact.**

PROVED (task #97-P3-Promote): `promoteL_core`. -/
theorem promoteL_spec {m m' : PMemo} {fuel : Nat} {h r : LIdx} {u : Level}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hd : denoteL s.store.ls h = some u)
    (hrun : promoteL m fuel h s = .ok ((m', r), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersL r ∧ denoteL s'.store.ls r = some u ∧ PFrame s s' := by
  obtain ⟨a, b, c, d⟩ := promoteL_core fuel m h s m' r s' hwf hm hrun
  have hx := promoteL_aext m fuel h s (m', r) s' hrun
  exact ⟨a, hx.ext, b, c, d u hd, PFrame.of_aext hx⟩

/-- con-leche: none — arena infrastructure; **`promoteLs` is exact.**

PROVED (task #97-P3-Promote): `promoteLs_step`. -/
theorem promoteLs_spec {m m' : PMemo} {fuel : Nat} {h r : LsIdx}
    {us : List Level} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hd : denoteLs s.store.lss h = some us)
    (hrun : promoteLs m fuel h s = .ok ((m', r), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersLs r ∧ denoteLs s'.store.lss r = some us ∧ PFrame s s' := by
  obtain ⟨a, b, -, c, d⟩ := promoteLs_step hwf hm hrun
  have hx := promoteLs_aext m fuel h s (m', r) s' hrun
  exact ⟨a, hx.ext, b, c, d us hd, PFrame.of_aext hx⟩

/-- con-leche: none — arena infrastructure; **`promoteE` is exact** — THE
exactness lemma `Arena/Promote.lean` names ("`denote (promote h) = denote h`
is the exactness lemma P3 owes").

PROVED (task #97-P3-Promote): `promoteE_core`, the ten-arm fuel induction. -/
theorem promoteE_spec {m m' : PMemo} {fuel : Nat} {h r : EIdx} {e : Expr}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hd : denoteE s.store h = some e)
    (hrun : promoteE m fuel h s = .ok ((m', r), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersE r ∧ denoteE s'.store r = some e ∧ PFrame s s' := by
  obtain ⟨a, b, c, d⟩ := promoteE_core fuel m h s m' r s' hwf hm hrun
  have hx := promoteE_aext m fuel h s (m', r) s' hrun
  exact ⟨a, hx.ext, b, c, d e hd, PFrame.of_aext hx⟩

/-! ## The declaration layer

`Arena/Promote.lean`'s record walk, field for field, and the two entries the
fold calls.  Each is do-notation over the four above, so each is mechanical;
each is stated at the DENOTATION its consumer wants, which for the
declaration layer is `Arena/Frontend/Readback.lean`'s `denoteCV` / `denoteCI`
family. -/

/-- con-leche: none — arena infrastructure; **promoting a constant's header
keeps its denotation.**

PROVED (task #97-P3-Promote): `Bridge/Promote/WalkDecl.lean`'s `promoteCV_step`. -/
theorem promoteCV_spec {m m' : PMemo} {fuel : Nat} {cv cv' : IConstantVal}
    {c : ConstantVal} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hd : Frontend.denoteCV s.store cv = some c)
    (hrun : promoteCV m fuel cv s = .ok ((m', cv'), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersCV cv' ∧ Frontend.denoteCV s'.store cv' = some c ∧ PFrame s s' := by
  obtain ⟨a, b, -, c, -, d⟩ := promoteCV_step hwf hm hrun
  have hx := promoteCV_aext m fuel cv s (m', cv') s' hrun
  exact ⟨a, hx.ext, b, c, d _ hd, PFrame.of_aext hx⟩

/-- con-leche: none — arena infrastructure; **promoting a stored constant
keeps its denotation** — the seven `IConstantInfo` constructors.

PROVED (task #97-P3-Promote): `promoteCI_step`. -/
theorem promoteCI_spec {m m' : PMemo} {fuel : Nat} {ci ci' : IConstantInfo}
    {c : ConstantInfo} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hd : Frontend.denoteCI s.store ci = some c)
    (hrun : promoteCI m fuel ci s = .ok ((m', ci'), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersCI ci' ∧ Frontend.denoteCI s'.store ci' = some c ∧ PFrame s s' := by
  obtain ⟨a, b, -, c, -, -, d⟩ := promoteCI_step hwf hm hrun
  have hx := promoteCI_aext m fuel ci s (m', ci') s' hrun
  exact ⟨a, hx.ext, b, c, d _ hd, PFrame.of_aext hx⟩

/-- con-leche: none — arena infrastructure; a block's constants, at ONE memo.

PROVED (task #97-P3-Promote): `promoteCIList_step`. -/
theorem promoteCIList_spec {m m' : PMemo} {fuel : Nat}
    {cs cs' : List IConstantInfo} {xs : List ConstantInfo} {s s' : AState}
    (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hd : Frontend.denoteCIList s.store cs = some xs)
    (hrun : promoteCIList m fuel cs s = .ok ((m', cs'), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersCIList cs' ∧ Frontend.denoteCIList s'.store cs' = some xs ∧
      PFrame s s' := by
  obtain ⟨a, b, -, c, -, -, d⟩ := promoteCIList_step cs hwf hm hrun
  have hx := promoteCIList_aext m fuel cs s (m', cs') s' hrun
  exact ⟨a, hx.ext, b, c, d _ hd, PFrame.of_aext hx⟩

/-- con-leche: none — arena infrastructure; **the install/check seam is
promoted exactly**: an `opaque`'s value is not in the environment, so the
`ValueGroup` is promoted beside it and at the SAME memo, and phase B therefore
checks the same term phase A installed.

PROVED (task #97-P3-Promote): `promoteVG_step`. -/
theorem promoteVG_spec {m m' : PMemo} {fuel : Nat} {g g' : Arena.ValueGroup}
    {c : ConstantVal} {e : Expr} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hcv : Frontend.denoteCV s.store g.cvA = some c)
    (hjv : denoteE s.store g.jv = some e)
    (hrun : promoteVG m fuel g s = .ok ((m', g'), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersVG g' ∧ g'.kind = g.kind ∧
      Frontend.denoteCV s'.store g'.cvA = some c ∧
      denoteE s'.store g'.jv = some e ∧ PFrame s s' := by
  obtain ⟨a, b, -, c, d, e1, e2⟩ := promoteVG_step hwf hm hrun
  have hx := promoteVG_aext m fuel g s (m', g') s' hrun
  exact ⟨a, hx.ext, b, c, d, e1 _ hcv, e2 _ hjv, PFrame.of_aext hx⟩

/-! ## The fold's entry

`promoteNew` is the only one of these the fold calls on the environment, and
its statement is what makes the per-declaration bridge work: **the environment
after the promotion denotes the environment before it**, and every handle in
it is persistent, so the `dropScratch` that follows changes nothing the fold
can see.

The index clause is the one `Arena/Promote.lean`'s `eraseInstalled` /
`indexPromoted` exist for: the promotion MOVES a name handle, so a row under
the old key must go, and the new rows must be re-inserted at the counters the
constants were pushed with — otherwise `IFEnv.find?` answers a constant under
a word `dropScratch` is about to hand back to the next declaration. -/

/-- con-leche: none — arena infrastructure; the denotation of an environment
INDEX: its constant list, read back.  §8.2's `denoteEnv`. -/
def denoteIEnv (st : EStore) (e : IEnv) : Option Env :=
  (Frontend.denoteCIList st e.consts).map Env.mk

/-- con-leche: none — arena infrastructure; the denotation of the indexed
environment is the denotation of its list (the index is a cache of the list,
DESIGN §8.3 lesson 13). -/
def denoteFEnv (st : EStore) (fe : IFEnv) : Option Env := denoteIEnv st fe.env

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — **the index is its
list's index**, which is con-leche's own join-point clause
(`Verify/Cached/BridgeC.lean:609`'s `fe' = mkFEnv fe'.env`).  `IFEnv.push`
preserves it; `IFEnv.restrictTo` does not, which is why phase B's prefix view
is handled by a congruence (`mkFEnv_find?_visibleBelow`) and not by this. -/
def IFEnvCoh (fe : IFEnv) : Prop := fe = mkIFEnv fe.env

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **what a push does
to the denotation**: one more constant at the front, which is exactly what
con-leche's `⟨ci :: env.consts⟩` writes. -/
theorem denoteFEnv_push {st : EStore} {fe : IFEnv} {env : Env}
    {ci : IConstantInfo} {c : ConstantInfo} (h : denoteFEnv st fe = some env)
    (hci : Frontend.denoteCI st ci = some c) :
    denoteFEnv st (fe.push ci) = some ⟨c :: env.consts⟩ := by
  simp only [denoteFEnv, denoteIEnv, IFEnv.push, Option.map_eq_some_iff] at h ⊢
  obtain ⟨cs, hcs, he⟩ := h
  subst he
  exact ⟨c :: cs, by simp only [Frontend.denoteCIList, hci, hcs], rfl⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **`IFEnv.push`
preserves the coherence clause**: the index of the cons-extended environment
is the index `mkIFEnv` would build for it.

con-leche's `mkFEnvGo` inserts from the back, so `mkIFEnvGo (ci :: cs)` is
`mkIFEnvGo cs` with `ci` inserted at the counter `mkIFEnvGo cs` stopped at —
which is precisely what `IFEnv.push` does to `fe.idx` at `fe.visibleBelow`,
once `IFEnvCoh fe` says those two are `mkIFEnvGo fe.env.consts`'s two
components.

One of the two `IFEnv.push` lemmas task #97-P3-Ind §8 asks for (the other is
`Pushed.push` just below); fourteen install statements of
`Bridge/Inductives/**` want the pair. -/
theorem IFEnvCoh.push {fe : IFEnv} (h : IFEnvCoh fe) (ci : IConstantInfo) :
    IFEnvCoh (fe.push ci) := by
  have hidx : fe.idx = (mkIFEnvGo fe.env.consts).2 := congrArg IFEnv.idx h
  have hvb : fe.visibleBelow = (mkIFEnvGo fe.env.consts).1 :=
    congrArg IFEnv.visibleBelow h
  show fe.push ci = mkIFEnv (fe.push ci).env
  simp only [IFEnv.push, mkIFEnv, mkIFEnvGo, hidx, hvb]

/-- con-leche: ConLeche/Kernel/FEnv.lean:51-60 mkFEnvGo — **every counter the
index build hands out is BELOW the counter it stops at**, which is what makes
`IFEnv.push`'s raised `visibleBelow` safe: a push cannot REVEAL an entry the
old index was hiding.  `Bridge/Inductives/Rel.lean`'s `ProjOut.push` is the
consumer (task #97-P3-Ind round 2 proved it there and said it belonged here;
round 3 moved it). -/
theorem mkIFEnvGo_counter_lt : ∀ (cs : List IConstantInfo) (n : NIdx)
    (c : Nat) (ci : IConstantInfo),
    (mkIFEnvGo cs).2[n]? = some (c, ci) → c < (mkIFEnvGo cs).1 := by
  intro cs
  induction cs with
  | nil => intro n c ci h; simp [mkIFEnvGo] at h
  | cons a as ih =>
    intro n c ci h
    simp only [mkIFEnvGo] at h ⊢
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hEq
      obtain rfl := Prod.mk.inj (Option.some.inj h) |>.1
      omega
    · exact Nat.lt_succ_of_lt (ih n c ci h)

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **the step only
PUSHED**: everything the fold's step did to the environment was `IFEnv.push`,
so the old list is a suffix of the new one.  `Arena/Promote.lean`'s
`promoteNew` note is this fact in prose ("every install route in (B) grows the
environment by `IFEnv.push` alone […] so the `k` newest entries of
`fe.env.consts` are exactly the step's"), and it is what makes the promotion's
`k` mean what the fold thinks it means. -/
def Pushed (fe0 fe : IFEnv) : Prop :=
  ∃ new, fe.env.consts = new ++ fe0.env.consts

theorem Pushed.refl (fe : IFEnv) : Pushed fe fe := ⟨[], rfl⟩

theorem Pushed.trans {a b c : IFEnv} (h₁ : Pushed a b) (h₂ : Pushed b c) :
    Pushed a c := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  exact ⟨n₂ ++ n₁, by rw [e₂, e₁, List.append_assoc]⟩

theorem Pushed.push (fe : IFEnv) (ci : IConstantInfo) : Pushed fe (fe.push ci) :=
  ⟨[ci], rfl⟩

/-! ### The fold's entry, run

`promoteNew` is `promoteCIList` on the step's `k` newest constants plus two
index passes.  The lemmas below read the run (`promoteNew_run_zero`,
`promoteNew_run_pos`), locate the step's constants in the list
(`Pushed.split`), and say what the two index passes can answer
(`eraseInstalled_getElem?`, `indexPromoted_getElem?`). -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — the counter the index
build ends at is the list's length. -/
theorem mkIFEnvGo_fst' : ∀ (cs : List IConstantInfo), (mkIFEnvGo cs).1 = cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons a as ih => simp only [mkIFEnvGo, List.length_cons, ih]

/-- con-leche: ConLeche/Kernel/FEnv.lean:51-60 mkFEnvGo — a row of the index
build is an entry of its list, filed under that entry's own name. -/
theorem mkIFEnvGo_key : ∀ (cs : List IConstantInfo) (n : NIdx) (p : Nat × IConstantInfo),
    (mkIFEnvGo cs).2[n]? = some p → p.2 ∈ cs ∧ p.2.name = n := by
  intro cs
  induction cs with
  | nil => intro n p h; simp [mkIFEnvGo] at h
  | cons a as ih =>
    intro n p h
    simp only [mkIFEnvGo] at h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hEq
      obtain rfl := Option.some.inj h
      exact ⟨by simp, eq_of_beq hEq⟩
    · obtain ⟨h1, h2⟩ := ih n p h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem IFEnvCoh.vb_eq {fe : IFEnv} (h : IFEnvCoh fe) :
    fe.visibleBelow = fe.env.consts.length := by
  have : fe.visibleBelow = (mkIFEnvGo fe.env.consts).1 := congrArg IFEnv.visibleBelow h
  rw [this, mkIFEnvGo_fst']

/-- con-leche: none — arena infrastructure; **the step's constants are the
`k` newest**: with both ends coherent and the step only pushing, `k` is the
number of entries it pushed. -/
theorem Pushed.split {fe0 fe : IFEnv} {k : Nat} (hcoh0 : IFEnvCoh fe0)
    (hcoh : IFEnvCoh fe) (hpush : Pushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow) :
    fe.env.consts.take k ++ fe0.env.consts = fe.env.consts ∧
      fe.env.consts.drop k = fe0.env.consts ∧ (fe.env.consts.take k).length = k := by
  obtain ⟨new, hnew⟩ := hpush
  have hl : k = new.length := by
    rw [hk, hcoh.vb_eq, hcoh0.vb_eq, hnew, List.length_append]; omega
  subst hl
  rw [hnew]
  simp

theorem persCI_name {ci : IConstantInfo} (h : PersCI ci) : PersN ci.name := by
  cases ci with
  | axiomInfo v => exact (show PersCV v from h).name
  | defnInfo v e hint => exact h.1.name
  | thmInfo v e => exact h.1.name
  | indInfo v c => exact h.1.name
  | ctorInfo v nP nF => exact (show PersCV v from h).name
  | recInfo v mI rP rs => exact h.1.name
  | projInfo t => exact (show PersProjTable t from h).tableName

theorem eraseInstalled_getElem? : ∀ (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (n : NIdx) (p : Nat × IConstantInfo),
    (eraseInstalled idx cs)[n]? = some p → idx[n]? = some p ∧ ∀ ci ∈ cs, ci.name ≠ n := by
  intro cs
  induction cs with
  | nil => intro idx n p h; exact ⟨h, fun _ h => absurd h (by simp)⟩
  | cons c cs ih =>
    intro idx n p h
    simp only [eraseInstalled] at h
    obtain ⟨h1, h2⟩ := ih _ n p h
    rw [Std.HashMap.getElem?_erase] at h1
    split at h1
    · exact absurd h1 (by simp)
    · rename_i hne
      refine ⟨h1, ?_⟩
      intro ci hci
      simp only [List.mem_cons] at hci
      rcases hci with rfl | hci
      · intro heq; exact hne (by rw [heq]; exact BEq.rfl)
      · exact h2 ci hci

theorem indexPromoted_getElem? : ∀ (cs : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (c : Nat) (n : NIdx)
    (p : Nat × IConstantInfo),
    (indexPromoted idx c cs)[n]? = some p → (p.2 ∈ cs ∧ p.2.name = n) ∨ idx[n]? = some p := by
  intro cs
  induction cs with
  | nil => intro idx c n p h; exact Or.inr h
  | cons a as ih =>
    intro idx c n p h
    simp only [indexPromoted] at h
    rcases ih _ _ n p h with ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rw [Std.HashMap.getElem?_insert] at h1
      split at h1
      · rename_i hEq
        obtain rfl := Option.some.inj h1
        exact Or.inl ⟨by simp, eq_of_beq hEq⟩
      · exact Or.inr h1

theorem denoteCIList_append {st : EStore} : ∀ (a b : List IConstantInfo)
    (zs : List ConstantInfo), Frontend.denoteCIList st (a ++ b) = some zs →
    ∃ za zb, Frontend.denoteCIList st a = some za ∧ Frontend.denoteCIList st b = some zb ∧
      zs = za ++ zb := by
  intro a
  induction a with
  | nil => intro b zs h; exact ⟨[], zs, rfl, h, rfl⟩
  | cons c cs ih =>
    intro b zs h
    simp only [List.cons_append, Frontend.denoteCIList] at h ⊢
    cases hc : Frontend.denoteCI st c with
    | none => rw [hc] at h; simp at h
    | some x =>
      cases hcs : Frontend.denoteCIList st (cs ++ b) with
      | none => rw [hc, hcs] at h; simp at h
      | some xs =>
        rw [hc, hcs] at h
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨za, zb, h1, h2, rfl⟩ := ih b xs hcs
        exact ⟨x :: za, zb, by rw [h1], h2, rfl⟩

theorem denoteCIList_append_of {st : EStore} : ∀ (a b : List IConstantInfo)
    (za zb : List ConstantInfo), Frontend.denoteCIList st a = some za →
    Frontend.denoteCIList st b = some zb →
    Frontend.denoteCIList st (a ++ b) = some (za ++ zb) := by
  intro a
  induction a with
  | nil =>
    intro b za zb ha hb
    simp only [Frontend.denoteCIList, Option.some.injEq] at ha
    subst ha; exact hb
  | cons c cs ih =>
    intro b za zb ha hb
    simp only [Frontend.denoteCIList] at ha
    cases hc : Frontend.denoteCI st c with
    | none => rw [hc] at ha; simp at ha
    | some x =>
      cases hcs : Frontend.denoteCIList st cs with
      | none => rw [hc, hcs] at ha; simp at ha
      | some xs =>
        rw [hc, hcs] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        simp only [List.cons_append, Frontend.denoteCIList, hc, ih b xs zb hcs hb,
          List.cons_append]

/-- con-leche: none — arena infrastructure; `promoteNew` at `k = 0` does
nothing. -/
theorem promoteNew_run_zero {m m' : PMemo} {fuel : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hrun : promoteNew m fuel 0 fe s = .ok ((m', fe'), s')) :
    m' = m ∧ fe' = fe ∧ s' = s := by
  simp only [promoteNew] at hrun
  obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
  simp only [Prod.mk.injEq] at hr
  exact ⟨hr.1, hr.2, rfl⟩

/-- con-leche: none — arena infrastructure; `promoteNew` at `k ≠ 0` is the
block promotion and the two index passes. -/
theorem promoteNew_run_pos {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hk : k ≠ 0)
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) :
    ∃ cs', promoteCIList m fuel (fe.env.consts.take k) s = .ok ((m', cs'), s') ∧
      fe' = ⟨⟨cs' ++ fe.env.consts.drop k⟩,
        indexPromoted (eraseInstalled fe.idx (fe.env.consts.take k)) fe.visibleBelow cs',
        fe.visibleBelow⟩ := by
  obtain ⟨⟨consts⟩, idx, vb⟩ := fe
  unfold promoteNew at hrun
  rcases AM.ite_ok hrun with ⟨hk0, _⟩ | ⟨_, hrun⟩
  · exact absurd (by simpa using hk0) hk
  obtain ⟨⟨m1, cs1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hr, rfl⟩ := AM.pure_ok h2
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨cs1, h1, rfl⟩

/-- con-leche: none — arena infrastructure; **the coherence clause of the
fold's promotion — FALSE as stated for `k ≠ 0`** (task #97-P3-Promote's
finding).

`IFEnvCoh fe` is `fe = mkIFEnv fe.env`, an equation between `Std.HashMap`s,
and a `Std.HashMap` is a bucket array: two maps with the same bindings built
in different insertion orders are different VALUES when two keys share a
bucket (the bucket's association list records the order) or when one of them
was resized and the other was not.  `promoteNew` builds its index by
`eraseInstalled` (which never shrinks the bucket array) and then
`indexPromoted`, which inserts the step's constants NEWEST FIRST; `mkIFEnv`
builds from the back, OLDEST FIRST.  Two promoted names that hash to one
bucket therefore come out in opposite orders, and nothing in this statement's
hypotheses — which fix only the denotation — rules that out.

What IS true, and all that every consumer of `IFEnvCoh` reads
(`IFEnvCoh.find?`, `IFEnv.find?_mem`, `ProjOut.push`, `Split.lean`'s use), is
the EXTENSIONAL coherence: the same answer at every key, and the same
counter.  See this task's DESIGN section for the repair (it changes the
definition of `IFEnvCoh`, a conclusion of four other lanes' statements, and so
needs the coordinator's authorisation).  `k = 0` is proved: nothing moved. -/
theorem promoteNew_coh {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hcoh : IFEnvCoh fe)
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) : IFEnvCoh fe' := by
  by_cases hk : k = 0
  · subst hk
    obtain ⟨-, rfl, -⟩ := promoteNew_run_zero hrun
    exact hcoh
  · sorry

/-- con-leche: none — arena infrastructure; **the fold's promotion is
exact**: the `k` constants the step installed are copied into the persistent
tier and re-indexed, and the environment denotes what it denoted.

`fe0` is the PRE-step environment and `k` the counter difference, which is
what `Arena/Checker.lean`'s `checkDeclStep` and `annotStep` compute; the
hypotheses say the step only pushed and that everything below it was already
persistent, which is the fold's own invariant one step earlier.

PROVED (task #97-P3-Promote): `promoteCIList_step` on the step's constants (`Pushed.split` locates them), the two index passes read row by row (`eraseInstalled_getElem?`, `indexPromoted_getElem?`), and the denotation split at the `take`/`drop` — EXCEPT the `IFEnvCoh fe'` conjunct, which is `promoteNew_coh` and is false as stated (see it). -/
theorem promoteNew_spec {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {env : Env} {s s' : AState} (hwf : StoreWF' s.store)
    (hm : PMemoOK m s.store) (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0)
    (hcoh : IFEnvCoh fe) (hpush : Pushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hd : denoteFEnv s.store fe = some env)
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersIFEnv fe' ∧ IFEnvCoh fe' ∧ denoteFEnv s'.store fe' = some env ∧
      fe'.visibleBelow = fe.visibleBelow ∧ PFrame s s' := by
  have hx := promoteNew_aext m fuel k fe s (m', fe') s' hrun
  obtain ⟨htake, hdrop, hlen⟩ := Pushed.split hcoh0 hcoh hpush hk
  refine (fun (H : StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersIFEnv fe' ∧
      denoteFEnv s'.store fe' = some env ∧ fe'.visibleBelow = fe.visibleBelow) =>
    ⟨H.1, hx.ext, H.2.1, H.2.2.1, promoteNew_coh hcoh hrun, H.2.2.2.1, H.2.2.2.2,
      PFrame.of_aext hx⟩) ?_
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨h1, h2, h3⟩ := promoteNew_run_zero hrun
    subst m'; subst fe'; subst s'
    -- nothing was pushed, so the step's index IS the one before it
    have he : fe = fe0 := by
      rw [hcoh, hcoh0]
      simp only [List.take_zero, List.nil_append] at htake
      have : fe.env = fe0.env := by
        cases hfe : fe.env; cases hfe0 : fe0.env
        rw [hfe, hfe0] at htake; simp only at htake; rw [htake]
      rw [this]
    subst he
    exact ⟨hwf, hm, hp0, hd, rfl⟩
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
        rw [← show fe.idx = (mkIFEnvGo fe.env.consts).2 from congrArg IFEnv.idx hcoh]
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

/-! ## What the fold's step needs beside the spec

Three facts about the same run, stated separately so that
`promoteNew_spec`'s statement stays the one its consumers were written
against: the environment after the promotion still only PUSHED onto the one
before the step (`Arena.annotStep_split`'s `Pushed fe fe'`), `IFEnvOK`'s
`proj` clause survives it (the other half of "`IFEnvOK` at the pushed index"),
and the bracket's closing `dropScratch` turns the promote window's invariant
back into the strong one with every persistent denotation kept. -/

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **the promotion
keeps the step's environment a push onto the one before it**: the step's
constants are replaced by their promoted copies, the tail is untouched. -/
theorem promoteNew_pushed {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hcoh0 : IFEnvCoh fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) : Pushed fe0 fe' := by
  obtain ⟨-, hdrop, -⟩ := Pushed.split hcoh0 hcoh hpush hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, -⟩ := promoteNew_run_zero hrun
    subst fe'; exact hpush
  · obtain ⟨cs', -, rfl⟩ := promoteNew_run_pos hk0 hrun
    exact ⟨cs', by simp only [hdrop]⟩

/-- con-leche: none — arena infrastructure; **the projection tables survive
the promotion**: every table of the promoted environment is well shaped and
rightly named in the promoted store, given that every table of the
environment was before it.  (`IFEnvOK_of_denote`'s `hproj`, carried.) -/
theorem promoteNew_projOK {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hproj : ∀ t, IConstantInfo.projInfo t ∈ fe.env.consts → IProjTableOK s.store t)
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) :
    ∀ t, IConstantInfo.projInfo t ∈ fe'.env.consts → IProjTableOK s'.store t := by
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, h2, h3⟩ := promoteNew_run_zero hrun
    subst fe'; subst s'; exact hproj
  · obtain ⟨cs', h1, rfl⟩ := promoteNew_run_pos hk0 hrun
    obtain ⟨-, -, hx1, -, -, ht1, -⟩ := promoteCIList_step _ hwf hm h1
    intro t' ht'
    rcases List.mem_append.mp ht' with h | h
    · obtain ⟨t, hmem, hpt⟩ := ht1 t' h
      exact (hproj t (List.mem_of_mem_take hmem)).promoted hpt
    · exact (hproj t' (List.mem_of_mem_drop h)).mono hx1

/-- con-leche: none — arena infrastructure; **the promotion bracket closes**
— Theorem 1's `bracket_close_w` (`Refine2/Checker/Shape.lean`, the Theorem 2
side's bridge between its weak and strong relations), in the same shape: the
bracket was OPENED at a well-formed boundary `s0`, everything between the
opening `enterScratch` and the closing `dropScratch` only appended (`hext`),
and the promotions left the promote window's invariant; the drop then gives
the strong invariant back and every persistent denotation of the boundary. -/
theorem promoteBracket_close {s0 s : AState} (hwf0 : StoreWF s0.store)
    (hwf : StoreWF' s.store) (hext : Ext s0.store.enableScratch s.store) :
    (dropScratch : AM Unit) s = .ok ((),
      { store := s.store.dropScratch, memos := s.memos, caches := Caches.empty,
        pins := s.pins }) ∧
      StoreWF s.store.dropScratch ∧ PExt s0.store s.store.dropScratch ∧
      PExt s.store s.store.dropScratch :=
  ⟨rfl, StoreWF'.dropScratch_wf hwf,
    ((PExt.enterScratch hwf0).trans (PExt.of_ext hext)).trans (PExt.dropScratch' hwf),
    PExt.dropScratch' hwf⟩

/-! ## Census -/

/-- info: 'ConRon.Bridge.promoteN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteN_spec

/-- info: 'ConRon.Bridge.promoteL_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteL_spec

/-- info: 'ConRon.Bridge.promoteLs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteLs_spec

/-- info: 'ConRon.Bridge.promoteE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteE_spec

/-- info: 'ConRon.Bridge.promoteCV_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteCV_spec

/-- info: 'ConRon.Bridge.promoteCI_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteCI_spec

/-- info: 'ConRon.Bridge.promoteCIList_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteCIList_spec

/-- info: 'ConRon.Bridge.promoteVG_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteVG_spec

/-- info: 'ConRon.Bridge.promoteNew_pushed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_pushed

/-- info: 'ConRon.Bridge.promoteNew_projOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_projOK

/-- info: 'ConRon.Bridge.promoteBracket_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteBracket_close

/-- info: 'ConRon.Bridge.promoteNew_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_spec

end ConRon.Bridge
