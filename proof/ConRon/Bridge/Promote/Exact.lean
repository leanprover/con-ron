/-
# `ConRon.Bridge.Promote.Exact` — the promotion is EXACT, and its memo is sound

`Arena/Promote.lean`'s own module note names the obligation this file states:

> `denote (promote h) = denote h` is the exactness lemma P3 owes; it is an
> induction on the recursion below, with `EStore.internPersistent`'s `consP`
> and `derExact` at each node.

Three things are owed at every entry of `Arena/Promote.lean`, and they travel
together because the recursion threads all three:

1. **exactness** — the promoted handle denotes in the persistent projection, and
   what the original denoted in the source it denotes there (`Kept`).
   This is the whole soundness content: the promotion is a change of
   REPRESENTATION and of nothing else, so an environment the fold promoted
   denotes the environment it denoted before;
2. **persistence** — the answer is in the persistent tier (`Pers…`,
   `Bridge/Promote/Pers.lean`).  This is what the *next* `dropScratch`
   consumes: `PExt` transports a persistent denotation and nothing else, so
   without this clause the fold's environment would decode to nothing one step
   later;
3. **the memo invariant** `PMemoPi` — every row of the promotion memo is a
   promoted pair.

**How it is proved.**  The four handle-kind specs and the declaration layer's
four are the walks of `Bridge/Promote/Walk.lean` / `WalkDecl.lean` (fuel and
list inductions over `Bridge/Promote/Proj.lean`'s promote-interns at the
projection), and `promoteNew_pi` is `promoteCIList` plus the two index passes.
Its `IFEnvCoh fe'` conjunct needs `Bridge/Promote/Coh.lean`'s
`promoteNewConsts_cohX`, so `promoteNew_pi` itself lives there (`IFEnvCoh` is the
EXTENSIONAL coherence — see its definition).
-/
module

import ConRon.Bridge.Promote.WalkDecl
import ConRon.Bridge.Promote.Weak
public import ConRon.Bridge.Promote.Memo
public import ConRon.Bridge.StateOK

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The declaration layer

`Arena/Promote.lean`'s record walk, field for field, and the two entries the
fold calls.  Each is do-notation over the four above, so each is mechanical;
each is stated at the DENOTATION its consumer wants, which for the
declaration layer is `Arena/Frontend/Readback.lean`'s `denoteCV` / `denoteCI`
family. -/

/-- con-leche: none — arena infrastructure; **the install/check seam is
promoted exactly**: an `opaque`'s value is not in the environment, so the
`ValueGroup` is promoted beside it and at the SAME memo, and phase B therefore
checks the same term phase A installed.

The proof is `promoteVG_step`. -/
theorem promoteVG_pi {src : EStore} {m m' : PMemo} {fuel : Nat} {g g' : Arena.ValueGroup}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteVG m fuel g s = .ok ((m', g'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      PFrame s s' ∧ PersVG g' ∧ g'.kind = g.kind ∧
      (∃ c, Frontend.denoteCV s'.store.dropScratch g'.cv = some c) ∧
      (∃ e, denoteE s'.store.dropScratch g'.jv = some e) ∧
      (∀ c, Frontend.denoteCV src g.cv = some c →
        Frontend.denoteCV s'.store.dropScratch g'.cv = some c) ∧
      (∀ e, denoteE src g.jv = some e → denoteE s'.store.dropScratch g'.jv = some e) := by
  obtain ⟨a, b, c, d, e, ⟨f1, f2⟩, ⟨g1, g2⟩⟩ := promoteVG_step hs hm hrun
  exact ⟨a, b, c, PFrame.of_aext (promoteVG_aext m fuel g s (m', g') s' hrun), d, e, f1, g1,
    f2, g2⟩

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
INDEX: its constant list and its table list, read back.  §8.2's `denoteEnv`. -/
@[expose] def denoteIEnv (st : EStore) (e : IEnv) : Option Env :=
  match Frontend.denoteCIList st e.consts, Frontend.denoteProjTableList st e.tables with
  | some cs, some ts => some ⟨cs, ts⟩
  | _, _ => none

/-- con-leche: none — arena infrastructure; `denoteIEnv` read off: both lists
denote. -/
theorem denoteIEnv_some {st : EStore} {e : IEnv} {env : Env} :
    denoteIEnv st e = some env ↔
      Frontend.denoteCIList st e.consts = some env.consts ∧
        Frontend.denoteProjTableList st e.tables = some env.tables := by
  unfold denoteIEnv
  constructor
  · intro h
    split at h
    · rename_i cs ts hcs hts
      cases h; exact ⟨hcs, hts⟩
    · cases h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- con-leche: none — arena infrastructure; the denotation of the indexed
environment is the denotation of its list (the index is a cache of the list,
DESIGN §8.3 lesson 13). -/
@[expose] def denoteFEnv (st : EStore) (fe : IFEnv) : Option Env := denoteIEnv st fe.env

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — the counter the index
build ends at is the list's length. -/
theorem mkIFEnvGo_fst' : ∀ (cs : List IConstantInfo), (mkIFEnvGo cs).1 = cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons a as ih => simp only [mkIFEnvGo, List.length_cons, ih]

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — **the index is its
list's index**, which is con-leche's own join-point clause
(`Verify/Cached/BridgeC.lean:609`'s `fe' = mkFEnv fe'.env`), stated
EXTENSIONALLY: the same counter, and the same answer at every key.
`IFEnv.push` preserves it; `IFEnv.restrictTo` does not, which is why phase
B's prefix view is handled by a congruence (`mkFEnv_find?_visibleBelow`) and
not by this.

**Why extensional** (DESIGN `### Task #97-P3-Promote`).  The structural
`fe = mkIFEnv fe.env` is an equation between two `Std.HashMap` VALUES, which
includes their bucket layout: `promoteNew` inserts newest-first where
`mkIFEnv` inserts oldest-first, so the two differ under a bucket collision and
the promotion could not meet it.  Every consumer reads only the counter and
the lookups, which is what this says. -/
@[expose] def IFEnvCoh (fe : IFEnv) : Prop :=
  fe.visibleBelow = fe.env.consts.length ∧
    (∀ n : NIdx, fe.idx[n]? = (mkIFEnvGo fe.env.consts).2[n]?) ∧
    ∀ n : NIdx, fe.tbls[n]? = (mkIFEnvTblsGo fe.env.tables)[n]?

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — the constant index's
half of `IFEnvCoh`. -/
theorem IFEnvCoh.idx {fe : IFEnv} (h : IFEnvCoh fe) (n : NIdx) :
    fe.idx[n]? = (mkIFEnvGo fe.env.consts).2[n]? := h.2.1 n

/-- con-leche: ConLeche/Kernel/FEnv.lean:149-153 mkTblsGo — the table map's
half of `IFEnvCoh`. -/
theorem IFEnvCoh.tbls {fe : IFEnv} (h : IFEnvCoh fe) (n : NIdx) :
    fe.tbls[n]? = (mkIFEnvTblsGo fe.env.tables)[n]? := h.2.2 n

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — an index built by
`mkIFEnv` is coherent. -/
theorem IFEnvCoh.mk (e : IEnv) : IFEnvCoh (mkIFEnv e) :=
  ⟨mkIFEnvGo_fst' e.consts, fun _ => rfl, fun _ => rfl⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **what a push does
to the denotation**: one more constant at the front, which is exactly what
con-leche's `⟨ci :: env.consts, env.tables⟩` writes. -/
theorem denoteFEnv_push {st : EStore} {fe : IFEnv} {env : Env}
    {ci : IConstantInfo} {c : ConstantInfo} (h : denoteFEnv st fe = some env)
    (hci : Frontend.denoteCI st ci = some c) :
    denoteFEnv st (fe.push ci) = some ⟨c :: env.consts, env.tables⟩ := by
  obtain ⟨hcs, hts⟩ := denoteIEnv_some.mp h
  refine denoteIEnv_some.mpr ⟨?_, hts⟩
  simp only [IFEnv.push, Frontend.denoteCIList, hci, hcs]

/-- con-leche: ConLeche/Kernel/FEnv.lean:199-205 pushTable — **what a table
install does to the denotation**: one more table at the front, which is exactly
what con-leche's `⟨env.consts, t :: env.tables⟩` writes. -/
theorem denoteFEnv_pushTable {st : EStore} {fe : IFEnv} {env : Env}
    {t : IProjTable} {pt : ProjTable} (h : denoteFEnv st fe = some env)
    (ht : Frontend.denoteProjTable st t = some pt) :
    denoteFEnv st (fe.pushTable t) = some ⟨env.consts, pt :: env.tables⟩ := by
  obtain ⟨hcs, hts⟩ := denoteIEnv_some.mp h
  refine denoteIEnv_some.mpr ⟨hcs, ?_⟩
  simp only [IFEnv.pushTable, Frontend.denoteProjTableList, ht, hts]

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **`IFEnv.push`
preserves the coherence clause**: the index of the cons-extended environment
is the index `mkIFEnv` would build for it.

con-leche's `mkFEnvGo` inserts from the back, so `mkIFEnvGo (ci :: cs)` is
`mkIFEnvGo cs` with `ci` inserted at the counter `mkIFEnvGo cs` stopped at —
which is precisely what `IFEnv.push` does to `fe.idx` at `fe.visibleBelow`,
once `IFEnvCoh fe` says those two are `mkIFEnvGo fe.env.consts`'s two
components.

One of the two `IFEnv.push` lemmas (the other is `Pushed.push` just below);
fourteen install statements of `Bridge/Inductives/**` want the pair. -/
theorem IFEnvCoh.push {fe : IFEnv} (h : IFEnvCoh fe) (ci : IConstantInfo) :
    IFEnvCoh (fe.push ci) := by
  refine ⟨by simp [IFEnv.push, h.1], fun n => ?_, fun n => h.tbls n⟩
  simp only [IFEnv.push, mkIFEnvGo, mkIFEnvGo_fst', Std.HashMap.getElem?_insert, h.idx n,
    h.1]

/-- con-leche: ConLeche/Kernel/FEnv.lean:199-205 pushTable — **`IFEnv.pushTable`
preserves the coherence clause**: the table map of the extended environment is
the one `mkIFEnvTblsGo` builds for it, the constant index untouched. -/
theorem IFEnvCoh.pushTable {fe : IFEnv} (h : IFEnvCoh fe) (t : IProjTable) :
    IFEnvCoh (fe.pushTable t) := by
  refine ⟨h.1, fun n => h.idx n, fun n => ?_⟩
  simp only [IFEnv.pushTable, mkIFEnvTblsGo, Std.HashMap.getElem?_insert, h.tbls n]

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **the step only
PUSHED**: everything the fold's step did to the environment was `IFEnv.push`,
so the old list is a suffix of the new one.  `Arena/Promote.lean`'s
`promoteNew` note is this fact in prose ("every install route in (B) grows the
environment by `IFEnv.push` alone […] so the `k` newest entries of
`fe.env.consts` are exactly the step's"), and it is what makes the promotion's
`k` mean what the fold thinks it means. -/
@[expose] def Pushed (fe0 fe : IFEnv) : Prop :=
  ∃ new, fe.env.consts = new ++ fe0.env.consts

theorem Pushed.refl (fe : IFEnv) : Pushed fe fe := ⟨[], rfl⟩

theorem Pushed.trans {a b c : IFEnv} (h₁ : Pushed a b) (h₂ : Pushed b c) :
    Pushed a c := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  exact ⟨n₂ ++ n₁, by rw [e₂, e₁, List.append_assoc]⟩

theorem Pushed.push (fe : IFEnv) (ci : IConstantInfo) : Pushed fe (fe.push ci) :=
  ⟨[ci], rfl⟩

/-- con-leche: none — a table install pushes no constant. -/
theorem Pushed.pushTable (fe : IFEnv) (t : IProjTable) : Pushed fe (fe.pushTable t) :=
  ⟨[], rfl⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:199-205 pushTable — **the step only
pushed TABLES onto the table list**: the table half of `Pushed`, what makes
the promotion's `kt` mean the step's tables. -/
@[expose] def TPushed (fe0 fe : IFEnv) : Prop :=
  ∃ new, fe.env.tables = new ++ fe0.env.tables

theorem TPushed.refl (fe : IFEnv) : TPushed fe fe := ⟨[], rfl⟩

theorem TPushed.trans {a b c : IFEnv} (h₁ : TPushed a b) (h₂ : TPushed b c) :
    TPushed a c := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  exact ⟨n₂ ++ n₁, by rw [e₂, e₁, List.append_assoc]⟩

/-- con-leche: none — a constant push installs no table. -/
theorem TPushed.push (fe : IFEnv) (ci : IConstantInfo) : TPushed fe (fe.push ci) :=
  ⟨[], rfl⟩

theorem TPushed.pushTable (fe : IFEnv) (t : IProjTable) : TPushed fe (fe.pushTable t) :=
  ⟨[t], rfl⟩

/-! ### The fold's entry, run

`promoteNew` is `promoteNewConsts` then `promoteNewTables`: `promoteCIList` on
the step's `k` newest constants plus two index passes, then
`promoteProjTables` on its `kt` newest tables plus two table-map passes.  The
lemmas below read the runs (`promoteNew_run`, `promoteNewConsts_run_zero`,
`promoteNewConsts_run_pos`, and the tables' pair), locate the step's entries in
the lists (`Pushed.split`, `TPushed.split`), and say what the index passes can
answer (`eraseInstalled_getElem?`, `indexPromoted_getElem?`). -/

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
    fe.visibleBelow = fe.env.consts.length := h.1

/-- con-leche: none — arena infrastructure; **the step's tables are the `kt`
newest**, as `Pushed.split` for the constants. -/
theorem TPushed.split {fe0 fe : IFEnv} {kt : Nat} (hpush : TPushed fe0 fe)
    (hk : kt = fe.env.tables.length - fe0.env.tables.length) :
    fe.env.tables.take kt ++ fe0.env.tables = fe.env.tables ∧
      fe.env.tables.drop kt = fe0.env.tables ∧ (fe.env.tables.take kt).length = kt := by
  obtain ⟨new, hnew⟩ := hpush
  have hl : kt = new.length := by rw [hk, hnew, List.length_append]; omega
  subst hl
  rw [hnew]
  simp

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
  | thmInfo v => exact (show PersCV v from h).name
  | indInfo v c => exact h.1.name
  | ctorInfo v nP nF => exact (show PersCV v from h).name
  | recInfo v mI rP rs => exact h.1.name

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

theorem denoteProjTableList_append {st : EStore} : ∀ (a b : List IProjTable)
    (zs : List ProjTable), Frontend.denoteProjTableList st (a ++ b) = some zs →
    ∃ za zb, Frontend.denoteProjTableList st a = some za ∧
      Frontend.denoteProjTableList st b = some zb ∧ zs = za ++ zb := by
  intro a
  induction a with
  | nil => intro b zs h; exact ⟨[], zs, rfl, h, rfl⟩
  | cons c cs ih =>
    intro b zs h
    simp only [List.cons_append, Frontend.denoteProjTableList] at h ⊢
    cases hc : Frontend.denoteProjTable st c with
    | none => rw [hc] at h; simp at h
    | some x =>
      cases hcs : Frontend.denoteProjTableList st (cs ++ b) with
      | none => rw [hc, hcs] at h; simp at h
      | some xs =>
        rw [hc, hcs] at h
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨za, zb, h1, h2, rfl⟩ := ih b xs hcs
        exact ⟨x :: za, zb, by rw [h1], h2, rfl⟩

theorem denoteProjTableList_append_of {st : EStore} : ∀ (a b : List IProjTable)
    (za zb : List ProjTable), Frontend.denoteProjTableList st a = some za →
    Frontend.denoteProjTableList st b = some zb →
    Frontend.denoteProjTableList st (a ++ b) = some (za ++ zb) := by
  intro a
  induction a with
  | nil =>
    intro b za zb ha hb
    simp only [Frontend.denoteProjTableList, Option.some.injEq] at ha
    subst ha; exact hb
  | cons c cs ih =>
    intro b za zb ha hb
    simp only [Frontend.denoteProjTableList] at ha
    cases hc : Frontend.denoteProjTable st c with
    | none => rw [hc] at ha; simp at ha
    | some x =>
      cases hcs : Frontend.denoteProjTableList st cs with
      | none => rw [hc, hcs] at ha; simp at ha
      | some xs =>
        rw [hc, hcs] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        simp only [List.cons_append, Frontend.denoteProjTableList, hc, ih b xs zb hcs hb]

/-- con-leche: ConLeche/Kernel/FEnv.lean:149-153 mkTblsGo — a row of the table
map's build is a table of its list, filed under that table's structure. -/
theorem mkIFEnvTblsGo_key : ∀ (ts : List IProjTable) (n : NIdx) (t : IProjTable),
    (mkIFEnvTblsGo ts)[n]? = some t → t ∈ ts ∧ t.structName = n := by
  intro ts
  induction ts with
  | nil => intro n t h; simp [mkIFEnvTblsGo] at h
  | cons a as ih =>
    intro n t h
    simp only [mkIFEnvTblsGo] at h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hEq
      obtain rfl := Option.some.inj h
      exact ⟨by simp, eq_of_beq hEq⟩
    · obtain ⟨h1, h2⟩ := ih n t h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:149-153 mkTblsGo — the table map of a
list with no table of structure `n` has no row at `n`. -/
theorem mkIFEnvTblsGo_none : ∀ (ts : List IProjTable) (n : NIdx),
    (∀ t ∈ ts, t.structName ≠ n) → (mkIFEnvTblsGo ts)[n]? = none := by
  intro ts
  induction ts with
  | nil => intro n _; simp [mkIFEnvTblsGo]
  | cons a as ih =>
    intro n h
    simp only [mkIFEnvTblsGo, Std.HashMap.getElem?_insert]
    split
    · rename_i hEq
      exact absurd (eq_of_beq hEq) (h a (by simp))
    · exact ih n (fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- con-leche: ConLeche/Kernel/FEnv.lean:149-153 mkTblsGo — the table map of an
append: the front's row, else the back's. -/
theorem mkIFEnvTblsGo_append (n : NIdx) : ∀ (a b : List IProjTable),
    (mkIFEnvTblsGo (a ++ b))[n]? = ((mkIFEnvTblsGo a)[n]?).or (mkIFEnvTblsGo b)[n]? := by
  intro a b
  induction a with
  | nil => simp [mkIFEnvTblsGo]
  | cons c cs ih =>
    simp only [List.cons_append, mkIFEnvTblsGo, Std.HashMap.getElem?_insert]
    split
    · simp
    · exact ih

/-- con-leche: none — arena infrastructure; the re-index inserts the promoted
tables over what is there, the newest of a name winning: `mkIFEnvTblsGo`'s
row, else the old map's. -/
theorem indexPromotedTables_getElem? (n : NIdx) (tbls : Std.HashMap NIdx IProjTable) :
    ∀ (ts : List IProjTable),
      (indexPromotedTables tbls ts)[n]? = ((mkIFEnvTblsGo ts)[n]?).or tbls[n]? := by
  intro ts
  induction ts with
  | nil => simp [indexPromotedTables, mkIFEnvTblsGo]
  | cons c cs ih =>
    simp only [indexPromotedTables, mkIFEnvTblsGo, Std.HashMap.getElem?_insert]
    split
    · simp
    · exact ih

/-- con-leche: none — arena infrastructure; the erase forgets exactly the rows
of the step's tables' structure names. -/
theorem eraseInstalledTables_getElem? (n : NIdx) : ∀ (ts : List IProjTable)
    (tbls : Std.HashMap NIdx IProjTable),
    (eraseInstalledTables tbls ts)[n]? =
      if ∃ t ∈ ts, t.structName = n then none else tbls[n]? := by
  intro ts
  induction ts with
  | nil => intro tbls; simp [eraseInstalledTables]
  | cons c cs ih =>
    intro tbls
    simp only [eraseInstalledTables, ih, Std.HashMap.getElem?_erase]
    by_cases hc : c.structName = n
    · simp [hc]
    · have : (c.structName == n) = false := by simpa using hc
      by_cases hin : ∃ t ∈ cs, t.structName = n
      · have h2 : ∃ t ∈ c :: cs, t.structName = n := by
          obtain ⟨t, ht, htn⟩ := hin
          exact ⟨t, List.mem_cons_of_mem _ ht, htn⟩
        simp only [hin, h2, ↓reduceIte]
      · have h2 : ¬ ∃ t ∈ c :: cs, t.structName = n := by
          rintro ⟨t, ht, htn⟩
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hc htn
          · exact hin ⟨t, ht, htn⟩
        simp only [hin, h2, ↓reduceIte, this]
        simp

/-- con-leche: none — arena infrastructure; `promoteNew` is the constants'
promotion, then the tables'. -/
theorem promoteNew_run {m m' : PMemo} {fuel k kt : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) :
    ∃ m1 fe1 s1, promoteNewConsts m fuel k fe s = .ok ((m1, fe1), s1) ∧
      promoteNewTables m1 fuel kt fe1 s1 = .ok ((m', fe'), s') := by
  simp only [promoteNew] at hrun
  obtain ⟨⟨m1, fe1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  exact ⟨m1, fe1, s1, h1, h2⟩

/-- con-leche: none — arena infrastructure; `promoteNewConsts` at `k = 0` does
nothing. -/
theorem promoteNewConsts_run_zero {m m' : PMemo} {fuel : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hrun : promoteNewConsts m fuel 0 fe s = .ok ((m', fe'), s')) :
    m' = m ∧ fe' = fe ∧ s' = s := by
  simp only [promoteNewConsts] at hrun
  obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
  simp only [Prod.mk.injEq] at hr
  exact ⟨hr.1, hr.2, rfl⟩

/-- con-leche: none — arena infrastructure; `promoteNewConsts` at `k ≠ 0` is
the block promotion and the two index passes; the tables are untouched. -/
theorem promoteNewConsts_run_pos {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hk : k ≠ 0)
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    ∃ cs', promoteCIList m fuel (fe.env.consts.take k) s = .ok ((m', cs'), s') ∧
      fe' = ⟨⟨cs' ++ fe.env.consts.drop k, fe.env.tables⟩,
        indexPromoted (eraseInstalled fe.idx (fe.env.consts.take k)) fe.visibleBelow cs',
        fe.visibleBelow, fe.tbls⟩ := by
  obtain ⟨⟨consts, tables⟩, idx, vb, tbls⟩ := fe
  unfold promoteNewConsts at hrun
  rcases AM.ite_ok hrun with ⟨hk0, _⟩ | ⟨_, hrun⟩
  · exact absurd (by simpa using hk0) hk
  obtain ⟨⟨m1, cs1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hr, rfl⟩ := AM.pure_ok h2
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨cs1, h1, rfl⟩

/-- con-leche: none — arena infrastructure; the constants' promotion leaves the
table component and the table map alone. -/
theorem promoteNewConsts_tables {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    fe'.env.tables = fe.env.tables ∧ fe'.tbls = fe.tbls := by
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, rfl, -⟩ := promoteNewConsts_run_zero hrun
    exact ⟨rfl, rfl⟩
  · obtain ⟨cs', -, rfl⟩ := promoteNewConsts_run_pos hk0 hrun
    exact ⟨rfl, rfl⟩

/-- con-leche: none — arena infrastructure; `promoteNewTables` at `kt = 0` does
nothing. -/
theorem promoteNewTables_run_zero {m m' : PMemo} {fuel : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hrun : promoteNewTables m fuel 0 fe s = .ok ((m', fe'), s')) :
    m' = m ∧ fe' = fe ∧ s' = s := by
  simp only [promoteNewTables] at hrun
  obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
  simp only [Prod.mk.injEq] at hr
  exact ⟨hr.1, hr.2, rfl⟩

/-- con-leche: none — arena infrastructure; `promoteNewTables` at `kt ≠ 0` is
the tables' promotion and the two table-map passes; the constants, their index
and the counter are untouched. -/
theorem promoteNewTables_run_pos {m m' : PMemo} {fuel kt : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hk : kt ≠ 0)
    (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s')) :
    ∃ ts', promoteProjTables m fuel (fe.env.tables.take kt) s = .ok ((m', ts'), s') ∧
      fe' = ⟨⟨fe.env.consts, ts' ++ fe.env.tables.drop kt⟩, fe.idx, fe.visibleBelow,
        indexPromotedTables (eraseInstalledTables fe.tbls (fe.env.tables.take kt)) ts'⟩ := by
  obtain ⟨⟨consts, tables⟩, idx, vb, tbls⟩ := fe
  unfold promoteNewTables at hrun
  rcases AM.ite_ok hrun with ⟨hk0, _⟩ | ⟨_, hrun⟩
  · exact absurd (by simpa using hk0) hk
  obtain ⟨⟨m1, ts1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hr, rfl⟩ := AM.pure_ok h2
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨ts1, h1, rfl⟩

/-- con-leche: none — arena infrastructure; the tables' promotion leaves the
constants, their index and the counter alone. -/
theorem promoteNewTables_consts {m m' : PMemo} {fuel kt : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s')) :
    fe'.env.consts = fe.env.consts ∧ fe'.idx = fe.idx ∧ fe'.visibleBelow = fe.visibleBelow := by
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨-, rfl, -⟩ := promoteNewTables_run_zero hrun
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨ts', -, rfl⟩ := promoteNewTables_run_pos hk0 hrun
    exact ⟨rfl, rfl, rfl⟩

/-! ## What the fold's step needs beside the denotation

The environment after the promotion still only PUSHED onto the one before the step
(the install step's `Pushed fe fe'`), `IFEnvOK`'s `proj` clause survives it (the other
half of "`IFEnvOK` at the pushed index"), and the bracket's closing `dropScratch`
leaves the projection. -/

/-- con-leche: none — arena infrastructure; the constants' promotion keeps `PSrc` and
the memo's invariant, and the projection only grows. -/
theorem promoteNewConsts_step {src : EStore} {m m' : PMemo} {fuel k : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteNewConsts m fuel k fe s = .ok ((m', fe'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch := by
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨rfl, -, rfl⟩ := promoteNewConsts_run_zero hrun
    exact ⟨hs, hm, Ext.refl _⟩
  · obtain ⟨cs', h1, -⟩ := promoteNewConsts_run_pos hk0 hrun
    obtain ⟨hs1, hm1, hx1, -⟩ := promoteCIList_step _ hs hm h1
    exact ⟨hs1, hm1, hx1⟩

/-- con-leche: none — arena infrastructure; the tables' promotion keeps `PSrc` and the
memo's invariant, and the projection only grows. -/
theorem promoteNewTables_step {src : EStore} {m m' : PMemo} {fuel kt : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteNewTables m fuel kt fe s = .ok ((m', fe'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch := by
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨rfl, -, rfl⟩ := promoteNewTables_run_zero hrun
    exact ⟨hs, hm, Ext.refl _⟩
  · obtain ⟨ts', h1, -⟩ := promoteNewTables_run_pos hk0 hrun
    obtain ⟨hs1, hm1, hx1, -⟩ := promoteProjTables_step _ hs hm h1
    exact ⟨hs1, hm1, hx1⟩

/-- con-leche: none — arena infrastructure; **what any run of a step's promotion
leaves, with no hypothesis on the environment.** -/
theorem promoteNew_frame {src : EStore} {m m' : PMemo} {fuel k kt : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PFrame s s' := by
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨hs1, hm1, hx1⟩ := promoteNewConsts_step hs hm h1
  obtain ⟨hs2, hm2, hx2⟩ := promoteNewTables_step hs1 hm1 h2
  exact ⟨hs2, hm2, hx1.trans hx2, PFrame.of_aext (promoteNew_aext m fuel k kt fe s (m', fe') s' hrun)⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **the promotion
keeps the step's environment a push onto the one before it**: the step's
constants are replaced by their promoted copies, the tail is untouched, and
the tables' promotion does not touch the constants. -/
theorem promoteNew_pushed {m m' : PMemo} {fuel k kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hcoh0 : IFEnvCoh fe0) (hcoh : IFEnvCoh fe)
    (hpush : Pushed fe0 fe) (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) : Pushed fe0 fe' := by
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨hc2, -, -⟩ := promoteNewTables_consts h2
  obtain ⟨-, hdrop, -⟩ := Pushed.split hcoh0 hcoh hpush hk
  suffices H : Pushed fe0 fe1 by
    obtain ⟨new, hn⟩ := H; exact ⟨new, by rw [hc2, hn]⟩
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨-, rfl, -⟩ := promoteNewConsts_run_zero h1
    exact hpush
  · obtain ⟨cs', -, rfl⟩ := promoteNewConsts_run_pos hk0 h1
    exact ⟨cs', by simp only [hdrop]⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:199-205 pushTable — **the promotion keeps the
step's tables a push onto the ones before it**: the step's tables are replaced by their
promoted copies, the tail is untouched, and the constants' promotion does not touch the
tables. -/
theorem promoteNew_tpushed {m m' : PMemo} {fuel k kt : Nat} {fe0 fe fe' : IFEnv}
    {s s' : AState} (hpush : TPushed fe0 fe)
    (hk : kt = fe.env.tables.length - fe0.env.tables.length)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) : TPushed fe0 fe' := by
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨ht1, -⟩ := promoteNewConsts_tables h1
  obtain ⟨-, hdrop, -⟩ := TPushed.split hpush hk
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨-, rfl, -⟩ := promoteNewTables_run_zero h2
    obtain ⟨new, hn⟩ := hpush
    exact ⟨new, by rw [ht1, hn]⟩
  · obtain ⟨ts', -, rfl⟩ := promoteNewTables_run_pos hk0 h2
    exact ⟨ts', by simp only [ht1, hdrop]⟩

/-- con-leche: none — arena infrastructure; **the projection tables survive
the promotion**: every table of the promoted environment is well shaped, given
that every table of the environment was before it.  (`IFEnvOK_of_denote`'s
`hproj`, carried.) -/
theorem promoteNew_projOK {src : EStore} {m m' : PMemo} {fuel k kt : Nat} {fe fe' : IFEnv}
    {s s' : AState} (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hproj : ∀ t ∈ fe.env.tables, IProjTableOK t)
    (hrun : promoteNew m fuel k kt fe s = .ok ((m', fe'), s')) :
    ∀ t ∈ fe'.env.tables, IProjTableOK t := by
  obtain ⟨m1, fe1, s1, h1, h2⟩ := promoteNew_run hrun
  obtain ⟨ht1, -⟩ := promoteNewConsts_tables h1
  obtain ⟨hs1, hm1, -⟩ := promoteNewConsts_step hs hm h1
  rw [← ht1] at hproj
  by_cases hk0 : kt = 0
  · subst hk0
    obtain ⟨-, rfl, -⟩ := promoteNewTables_run_zero h2
    exact hproj
  · obtain ⟨ts', h3, rfl⟩ := promoteNewTables_run_pos hk0 h2
    obtain ⟨-, -, -, -, hkept, -⟩ := promoteProjTables_step _ hs1 hm1 h3
    intro t' ht'
    rcases List.mem_append.mp ht' with h | h
    · -- a promoted table: the promotion of one of the step's own
      have key : ∀ (xs xs' : List IProjTable), TblListKept src s'.store.dropScratch xs xs' →
          ∀ b' ∈ xs', ∃ b ∈ xs, PromotedTable src s'.store.dropScratch b b' := by
        intro xs xs' hk
        induction hk with
        | nil => intro _ h; exact absurd h (by simp)
        | @cons d d' ds ds' hd _ ih2 =>
          intro b' hb'
          rcases List.mem_cons.mp hb' with rfl | hb'
          · exact ⟨d, by simp, hd⟩
          · obtain ⟨b, hb, hk'⟩ := ih2 b' hb'
            exact ⟨b, List.mem_cons_of_mem _ hb, hk'⟩
      obtain ⟨t, ht, hpt⟩ := key _ _ hkept t' h
      exact (hproj t (List.mem_of_mem_take ht)).promoted hpt
    · exact hproj t' (List.mem_of_mem_drop h)

/-- con-leche: none — arena infrastructure; **the promotion bracket closes**: the drop
answers the projection, which `PSrc` says is well formed and keeps every persistent
denotation of the source. -/
theorem promoteBracket_close {src : EStore} {s : AState} (hs : PSrc src s.store) :
    (dropScratch : AM Unit) s = .ok ((),
      { store := s.store.dropScratch, memos := s.memos, caches := Caches.empty,
        pins := s.pins }) ∧
      StoreWF s.store.dropScratch ∧ PExt src s.store.dropScratch :=
  ⟨rfl, hs.piWF, hs.pext⟩

/-! ## Census -/

/-- info: 'ConRon.Bridge.promoteVG_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteVG_pi

/-- info: 'ConRon.Bridge.promoteNew_pushed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_pushed

/-- info: 'ConRon.Bridge.promoteNew_projOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteNew_projOK

/-- info: 'ConRon.Bridge.promoteBracket_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteBracket_close

end ConRon.Bridge
