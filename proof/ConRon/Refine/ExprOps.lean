/-
The refinement of `crates/con-ron-core/src/kernel/expr_ops.rs` (task #13) on
its generated model `ConRon.Generated.kernel.expr_ops.*` (DESIGN.md §3.5, P3.3
of §5; task #21).

**What the statements are against.**  Every Rust item of the module implements
the `*Fast` member of one of con-leche's `@[csimp]` families (task #13): the
executed, memoized walk.  The lemma per function is therefore stated against
the **logical** definition of `ConLeche/Kernel/ExprOps.lean` -- `instantiate1`,
`instantiateList`, `liftLooseBVars`, … -- with the memoized walk's own lemma
(`*_go_refines`) as the step, and the `@[csimp]` equation is never needed: a
`*Go_spec`-shaped induction proves the walk equal to the logical function
directly, which is the same argument con-leche's own `@[csimp]` lemma makes.

**Memos.**  Every memo here is local (created empty in the wrapper, dropped on
return).  The invariant is con-leche's own `*MemoInv` -- "every recorded answer
is the real one" (`Inst1MemoInv`, `InstLMemoInv`, … , the eleven `Prop`s task
#13 skipped as not executable) -- transposed onto the port's table through the
*entry list* `ConRon.Refine.HashMap.al_v` rather than through `toFun`.  That is
the one deliberate departure from task #16's `toFun`/`Rel` bridge, and the
reason is `Eq2Spec`: `toFun` is a lookup by *Lean* equality, so every lemma
about it assumes `eq2` decides equality on the whole key type, while
`expr::beq` is exact only on **well-formed** nodes (`Expr.beq_exact`).  The
entry-list view needs no such assumption: `get_mem` says a hit returns a value
that is *in* the table under an `eq2`-equal key, `insert_mem` says an insert
adds nothing but its own pair, and both are proved here without `Eq2Spec` and
without the table invariant `Inv`.  A key recorded in the memo is well formed
(that is a clause of every `MemoInv` below), so `beq`'s exactness applies at
exactly the pairs the walks compare.
-/
import ConRon.Refine.Expr
import ConRon.Refine.HashMap
import ConLeche.Kernel.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## Memo tables as entry lists

The facts every memoized walk below uses, about any key type and with no
assumption on the `Hashable` or `Eq2` dictionary. -/

section Memo

variable {K V : Type} {HashableInst : ron.hashmap.Hashable K}
  {Eq2Inst : ron.hashmap.Eq2 K}

/-- A bucket walk that hits returns an entry *of that bucket*, under a key the
dictionary declares equal. -/
theorem list_get_mem {ls : ron.hashmap.AList K V} {k : K} {r : V}
    (h : ron.hashmap.list_get Eq2Inst ls k = ok (some r)) :
    ∃ k', (k', r) ∈ HashMap.alv ls ∧ Eq2Inst.eq2 k' k = ok true := by
  induction ls with
  | Nil => rw [ron.hashmap.list_get.eq_def] at h; simp at h
  | Cons ckey cval tl ih =>
    rw [ron.hashmap.list_get.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨k', hmem, heq⟩ := ih h
      exact ⟨k', by rw [HashMap.alv]; exact List.mem_cons_of_mem _ hmem, heq⟩
    | true =>
      simp only [if_true, Result.ok.injEq, Option.some.injEq] at h
      exact ⟨ckey, by rw [HashMap.alv, ← h]; exact List.mem_cons_self, hb⟩

/-- **A memo hit returns a recorded entry.**  No `Eq2Spec`, no `Inv`: the
value comes back with a key that is really in the table. -/
theorem get_mem {m : ron.hashmap.HashMap K V} {k : K} {r : V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok (some r)) :
    ∃ k', (k', r) ∈ HashMap.al_v m ∧ Eq2Inst.eq2 k' k = ok true := by
  rw [ron.hashmap.HashMap.get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨_, -, i2, -, a, hidx, hget⟩ := h
  obtain ⟨hlt, rfl⟩ := HashMap.vec_index_eq hidx
  obtain ⟨k', hmem, heq⟩ := list_get_mem hget
  exact ⟨k', (HashMap.slot_sublist_flatten hlt).mem hmem, heq⟩

/-! ### Inserts add nothing but their own pair

`Compat` is the one side condition: a *recorded* entry whose key the dictionary
equates to the key being inserted accepts the inserted answer.  It is what
`list_insert`'s replacing arm needs — that arm keeps the *old* key and the new
value — and it holds for every invariant below because `expr::beq` is exact on
well-formed nodes and the invariants only ever speak about a key's
abstraction. -/

/-- A recorded entry whose key the dictionary equates to `k` accepts `k`'s
answer. -/
def Compat (Eq2Inst : ron.hashmap.Eq2 K) (R : K → V → Prop) : Prop :=
  ∀ k k' v r', R k v → R k' r' → Eq2Inst.eq2 k' k = ok true → R k' v

theorem list_insert_pres {R : K → V → Prop} (hc : Compat Eq2Inst R)
    {ls : ron.hashmap.AList K V} {k : K} {v : V} {old : Option V}
    {ls' : ron.hashmap.AList K V}
    (hls : ∀ p ∈ HashMap.alv ls, R p.1 p.2) (hnew : R k v)
    (h : ron.hashmap.list_insert Eq2Inst ls k v = ok (old, ls')) :
    ∀ p ∈ HashMap.alv ls', R p.1 p.2 := by
  induction ls generalizing old ls' with
  | Nil =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2, HashMap.alv, HashMap.alv]
    intro p hp
    simp only [List.mem_singleton] at hp
    rw [hp]; exact hnew
  | Cons ckey cval tl ih =>
    have hhd : R ckey cval := hls (ckey, cval) (by rw [HashMap.alv]; exact List.mem_cons_self)
    have htl : ∀ p ∈ HashMap.alv tl, R p.1 p.2 := fun p hp =>
      hls p (by rw [HashMap.alv]; exact List.mem_cons_of_mem _ hp)
    rw [ron.hashmap.list_insert.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | true =>
      simp only [if_true, core.mem.replace] at h
      simp at h
      obtain ⟨-, hls'⟩ := h
      subst hls'
      rw [HashMap.alv]
      intro p hp
      rcases List.mem_cons.1 hp with hp | hp
      · rw [hp]; exact hc k ckey v cval hnew hhd hb
      · exact htl p hp
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      replace h := bind_eq_ok_iff.mp h
      obtain ⟨q, hrec, h⟩ := h
      obtain ⟨o, tl1⟩ := q
      simp at h
      obtain ⟨-, hls'⟩ := h
      subst hls'
      rw [HashMap.alv]
      intro p hp
      rcases List.mem_cons.1 hp with hp | hp
      · rw [hp]; exact hhd
      · exact ih htl hrec p hp

/-- Entries of a table whose bucket `i` was replaced: everything is either in
the new bucket or in some other bucket of the old table. -/
theorem mem_al_v_set {s : List (ron.hashmap.AList K V)} {i : Nat} (hi : i < s.length)
    {b : ron.hashmap.AList K V} {x : K × V} (h : x ∈ ((s.set i b).map HashMap.alv).flatten) :
    x ∈ HashMap.alv b ∨ ∃ j, ∃ _ : j < s.length, x ∈ HashMap.alv s[j]! := by
  rcases List.mem_append.1 ((HashMap.al_v_set_perm_rest hi b).mem_iff.1 h) with hx | hx
  · exact Or.inl hx
  · obtain ⟨j, -, hj, hxj⟩ := HashMap.mem_restOf hx
    exact Or.inr ⟨j, hj, hxj⟩

theorem insert_no_resize_pres {R : K → V → Prop} (hc : Compat Eq2Inst R)
    {m : ron.hashmap.HashMap K V} {k : K} {v : V} {old : Option V}
    {m' : ron.hashmap.HashMap K V}
    (hm : ∀ p ∈ HashMap.al_v m, R p.1 p.2) (hnew : R k v)
    (h : ron.hashmap.HashMap.insert_no_resize HashableInst Eq2Inst m k v = ok (old, m')) :
    (∀ p ∈ HashMap.al_v m', R p.1 p.2) ∧ m'.slots.val.length = m.slots.val.length := by
  rw [ron.hashmap.HashMap.insert_no_resize] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨_, -, i2, -, p0, hidx, h⟩ := h
  obtain ⟨a, back⟩ := p0
  replace h := bind_eq_ok_iff.mp h
  obtain ⟨q, hins, h⟩ := h
  obtain ⟨o, a1⟩ := q
  obtain ⟨hlt, rfl, rfl⟩ := HashMap.vec_index_mut_eq hidx
  have hbucket : ∀ p ∈ HashMap.alv m.slots.val[i2.val]!, R p.1 p.2 := fun p hp =>
    hm p ((HashMap.slot_sublist_flatten hlt).mem hp)
  have hnew' : ∀ p ∈ HashMap.alv a1, R p.1 p.2 := list_insert_pres hc hbucket hnew hins
  have key : m'.slots.val = m.slots.val.set i2.val a1 := by
    cases o with
    | none =>
      obtain ⟨i3, -, hok⟩ := bind_eq_ok_iff.mp h
      have es : m'.slots = alloc.vec.Vec.set m.slots i2 a1 :=
        (congrArg (fun z => (Prod.snd z).slots) (Result.ok_injective hok)).symm
      rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _
    | some wold =>
      have es : m'.slots = alloc.vec.Vec.set m.slots i2 a1 :=
        (congrArg (fun z => (Prod.snd z).slots) (Result.ok_injective h)).symm
      rw [es]; exact alloc.vec.Vec.set_val_eq _ _ _
  refine ⟨?_, by rw [key]; simp⟩
  intro p hp
  rw [HashMap.al_v, key] at hp
  rcases mem_al_v_set hlt hp with hx | ⟨j, hj, hxj⟩
  · exact hnew' p hx
  · exact hm p ((HashMap.slot_sublist_flatten hj).mem hxj)

theorem move_elements_from_list_pres {R : K → V → Prop} (hc : Compat Eq2Inst R) :
    ∀ (ls : ron.hashmap.AList K V) (nt nt' : ron.hashmap.HashMap K V),
      (∀ p ∈ HashMap.alv ls, R p.1 p.2) → (∀ p ∈ HashMap.al_v nt, R p.1 p.2) →
      ron.hashmap.HashMap.move_elements_from_list HashableInst Eq2Inst nt ls = ok nt' →
      (∀ p ∈ HashMap.al_v nt', R p.1 p.2) ∧
        nt'.slots.val.length = nt.slots.val.length := by
  intro ls
  induction ls with
  | Nil =>
    intro nt nt' _ hnt h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    rw [← Result.ok_injective h]
    exact ⟨hnt, rfl⟩
  | Cons k v tl ih =>
    intro nt nt' hls hnt h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨⟨o, nt1⟩, hins, hrec⟩ := h
    have hhd : R k v := hls (k, v) (by rw [HashMap.alv]; exact List.mem_cons_self)
    obtain ⟨h1, h2⟩ := insert_no_resize_pres hc hnt hhd hins
    obtain ⟨h3, h4⟩ := ih nt1 nt'
      (fun p hp => hls p (by rw [HashMap.alv]; exact List.mem_cons_of_mem _ hp)) h1 hrec
    exact ⟨h3, by rw [h4, h2]⟩

theorem move_elements_pres {R : K → V → Prop} (hc : Compat Eq2Inst R) (N : Nat) :
    ∀ (nt nt' : ron.hashmap.HashMap K V)
      (slots slots' : alloc.vec.Vec (ron.hashmap.AList K V)) (lo hi : Std.Usize),
      hi.val - lo.val = N →
      (∀ j, j < slots.val.length → ∀ p ∈ HashMap.alv slots.val[j]!, R p.1 p.2) →
      (∀ p ∈ HashMap.al_v nt, R p.1 p.2) →
      ron.hashmap.HashMap.move_elements HashableInst Eq2Inst nt slots lo hi
        = ok (nt', slots') →
      (∀ p ∈ HashMap.al_v nt', R p.1 p.2) ∧ slots'.val.length = slots.val.length ∧
        (∀ j, j < slots'.val.length → ∀ p ∈ HashMap.alv slots'.val[j]!, R p.1 p.2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro nt nt' slots slots' lo hi hN hslots hnt h
    rw [ron.hashmap.HashMap.move_elements.eq_def] at h
    split at h
    · rename_i hgt
      have hlolt : lo.val < hi.val := by scalar_tac
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n.val = hi.val - lo.val := HashMap.uscalar_sub_eq hn
      split at h
      · obtain ⟨⟨a, back⟩, hidx, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hlt, rfl, rfl⟩ := HashMap.vec_index_mut_eq hidx
        have h2 : (do
            let nt1 ← ron.hashmap.HashMap.move_elements_from_list HashableInst Eq2Inst nt
              (core.mem.replace slots.val[lo.val]! ron.hashmap.AList.Nil).1
            ok (nt1, alloc.vec.Vec.set slots lo
              (core.mem.replace slots.val[lo.val]! ron.hashmap.AList.Nil).2))
              = ok (nt', slots') := h
        simp only [core.mem.replace, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h2
        obtain ⟨nt1, hmv, hnt', hsl'⟩ := h2
        obtain ⟨h3, -⟩ := move_elements_from_list_pres hc _ nt nt1
          (hslots lo.val hlt) hnt hmv
        refine ⟨hnt' ▸ h3, ?_, ?_⟩
        · rw [← hsl', alloc.vec.Vec.set_val_eq]; simp
        · intro j hj p hp
          rw [← hsl', alloc.vec.Vec.set_val_eq] at hj hp
          rw [List.length_set] at hj
          by_cases hji : j = lo.val
          · rw [hji, HashMap.getElem!_set_self _ hlt, HashMap.alv] at hp; simp at hp
          · rw [HashMap.getElem!_set_ne _ hji] at hp
            exact hslots j hj p hp
      · rename_i h1
        have hn2 : 2 ≤ n.val := by
          have : n.val ≠ 1 := by scalar_tac
          omega
        obtain ⟨i, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨mid, hmid, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨⟨nt1, slots1⟩, hrec1, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i.val = n.val / 2 := by
          rw [HashMap.uscalar_div_eq hi2, show (2#usize : Std.Usize).val = 2 by scalar_tac]
        have hmv2 : mid.val = lo.val + i.val := HashMap.uscalar_add_eq hmid
        obtain ⟨h3, h4, h5⟩ := ih (mid.val - lo.val) (by omega) nt nt1 slots slots1 lo mid
          rfl hslots hnt hrec1
        obtain ⟨h6, h7, h8⟩ := ih (hi.val - mid.val) (by omega) nt1 nt' slots1 slots' mid hi
          rfl h5 h3 h
        exact ⟨h6, by rw [h7, h4], h8⟩
    · have e := Result.ok_injective (α := ron.hashmap.HashMap K V × _) h
      have e1 : nt = nt' := congrArg Prod.fst e
      have e2 : slots = slots' := congrArg Prod.snd e
      subst e1; subst e2
      exact ⟨hnt, rfl, hslots⟩

theorem try_resize_pres {R : K → V → Prop} (hc : Compat Eq2Inst R)
    {m m' : ron.hashmap.HashMap K V} (hm : ∀ p ∈ HashMap.al_v m, R p.1 p.2)
    (h : ron.hashmap.HashMap.try_resize HashableInst Eq2Inst m = ok m') :
    ∀ p ∈ HashMap.al_v m', R p.1 p.2 := by
  rw [ron.hashmap.HashMap.try_resize] at h
  obtain ⟨lim, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨cap2, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nt, hnt, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨⟨nt1, sl1⟩, hmv, hok⟩ := bind_eq_ok_iff.mp h
    have hnil : HashMap.al_v nt = [] := by
      obtain ⟨hs, -, -⟩ := HashMap.new_with_capacity_pow2_spec hnt
      refine HashMap.al_v_eq_nil_of_slots_nil (fun j hj => ?_)
      rw [hs, HashMap.getElem!_replicate_nil]
    obtain ⟨h1, -, -⟩ := move_elements_pres hc
      ((alloc.vec.Vec.len m.slots).val - (0#usize : Std.Usize).val) nt nt1 m.slots sl1
      0#usize (alloc.vec.Vec.len m.slots) rfl
      (fun j hj p hp => hm p ((HashMap.slot_sublist_flatten hj).mem hp))
      (by rw [hnil]; simp) hmv
    have eslots : m'.slots = nt1.slots :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.slots) (Result.ok_injective hok)).symm
    rw [HashMap.al_v_congr eslots]
    exact h1
  · have eslots : m'.slots = m.slots :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.slots) (Result.ok_injective h)).symm
    rw [HashMap.al_v_congr eslots]
    exact hm

/-- **An insert records its own pair and nothing else.**  No `Eq2Spec`, no
`Inv`; the resize is covered because it only moves recorded entries. -/
theorem insert_pres {R : K → V → Prop} (hc : Compat Eq2Inst R)
    {m : ron.hashmap.HashMap K V} {k : K} {v : V} {old : Option V}
    {m' : ron.hashmap.HashMap K V}
    (hm : ∀ p ∈ HashMap.al_v m, R p.1 p.2) (hnew : R k v)
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    ∀ p ∈ HashMap.al_v m', R p.1 p.2 := by
  rw [ron.hashmap.HashMap.insert] at h
  obtain ⟨⟨old0, m1⟩, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨h1, -⟩ := insert_no_resize_pres hc hm hnew hins
  have h2 : (if m1.num_entries > m1.max_load then
        (if m1.saturated then ok (old0, m1)
         else do
           let s2 ← ron.hashmap.HashMap.try_resize HashableInst Eq2Inst m1
           ok (old0, s2))
      else ok (old0, m1)) = ok (old, m') := h
  split at h2
  · split at h2
    · have e : m' = m1 :=
        (congrArg Prod.snd (Result.ok_injective (α := Option V × _) h2)).symm
      rw [e]; exact h1
    · obtain ⟨m2, hres, hok⟩ := bind_eq_ok_iff.mp h2
      have e : m' = m2 :=
        (congrArg Prod.snd (Result.ok_injective (α := Option V × _) hok)).symm
      rw [e]
      exact try_resize_pres hc h1 hres
  · have e : m' = m1 :=
      (congrArg Prod.snd (Result.ok_injective (α := Option V × _) h2)).symm
    rw [e]; exact h1

/-! ### The memo invariant

`MemoInv KWF absK Q m` is con-leche's `*MemoInv` on the port's table: every
recorded entry has a well-formed key, and its value is what the logical
function gives for the key's *abstraction*.  `KeyExact` is the single fact
about the key dictionary the two hit/insert lemmas need. -/

/-- Keys the dictionary equates have equal abstractions (on well-formed
keys). -/
def KeyExact (Eq2Inst : ron.hashmap.Eq2 K) (KWF : K → Prop) (absK : K → A) : Prop :=
  ∀ a b, KWF a → KWF b → Eq2Inst.eq2 a b = ok true → absK a = absK b

/-- The memo invariant: "every recorded answer is the real one". -/
def MemoInv (KWF : K → Prop) (absK : K → A) (Q : A → V → Prop)
    (m : ron.hashmap.HashMap K V) : Prop :=
  ∀ k r, (k, r) ∈ HashMap.al_v m → KWF k ∧ Q (absK k) r

/-- A fresh memo is empty (`*MemoInv.empty`). -/
theorem MemoInv.empty {KWF : K → Prop} {absK : K → A} {Q : A → V → Prop}
    {m : ron.hashmap.HashMap K V} (h : HashMap.al_v m = []) : MemoInv KWF absK Q m := by
  intro k r hmem; rw [h] at hmem; simp at hmem

/-- **A memo hit is a correct answer** — for the key that was probed, not just
for the one that was recorded, because the dictionary only equates keys with
equal abstractions. -/
theorem MemoInv.hit {KWF : K → Prop} {absK : K → A} {Q : A → V → Prop}
    {m : ron.hashmap.HashMap K V} {k : K} {r : V}
    (hx : KeyExact Eq2Inst KWF absK) (hm : MemoInv KWF absK Q m) (hk : KWF k)
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok (some r)) :
    Q (absK k) r := by
  obtain ⟨k', hmem, heq⟩ := get_mem h
  obtain ⟨hk', hq⟩ := hm k' r hmem
  rw [← hx k' k hk' hk heq]
  exact hq

/-- **Recording a correct answer keeps the invariant** (`*MemoInv.insert`). -/
theorem MemoInv.set {KWF : K → Prop} {absK : K → A} {Q : A → V → Prop}
    {m m' : ron.hashmap.HashMap K V} {k : K} {v : V} {old : Option V}
    (hx : KeyExact Eq2Inst KWF absK) (hm : MemoInv KWF absK Q m) (hk : KWF k)
    (hq : Q (absK k) v)
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    MemoInv KWF absK Q m' := by
  have hc : Compat Eq2Inst (fun k r => KWF k ∧ Q (absK k) r) := by
    intro k1 k2 v1 r1 h1 h2 heq
    exact ⟨h2.1, by rw [hx k2 k1 h2.1 h1.1 heq]; exact h1.2⟩
  intro k1 r1 hmem
  exact insert_pres hc (fun p hp => hm p.1 p.2 hp) ⟨hk, hq⟩ h (k1, r1) hmem

end Memo

/-! ## The two memo key types

Five of this file's memos are keyed by `(node, cursor)` (`ExprNatKey`, whose
`Eq2` is `expr::beq` then the `u64`), three by the node alone.  `KeyExact` for
both is `Expr.beq`'s exactness on well-formed nodes (task #20). -/

/-- The `(node, cursor)` key's abstraction: con-leche's `(Expr × Nat)`. -/
def absKey (k : expr_ops.ExprNatKey) : ConLeche.Expr × Nat := (absExpr k.e, k.d.val)

/-- A memo key is well formed when its node is. -/
def KeyWF (k : expr_ops.ExprNatKey) : Prop := ExprWF k.e

/-- The key a walk builds is well formed when the node it walks is (stated at
the pair, which is what the `MemoInv` lemmas unify against). -/
theorem keyWF_mk {e : expr.Expr} {d : Std.U64} (h : ExprWF e) :
    KeyWF (⟨e, d⟩ : expr_ops.ExprNatKey) := h

@[simp] theorem absKey_mk (e : expr.Expr) (d : Std.U64) :
    absKey ⟨e, d⟩ = (absExpr e, d.val) := rfl

@[simp] theorem KeyWF_mk (e : expr.Expr) (d : Std.U64) : KeyWF ⟨e, d⟩ ↔ ExprWF e := Iff.rfl

theorem key_exact :
    KeyExact expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 KeyWF absKey := by
  intro a b ha hb h
  have h' : (do
        let c ← expr.beq a.e b.e
        if c = true then ok (decide (a.d = b.d)) else ok false) = ok true := h
  simp only [bind_eq_ok_iff] at h'
  obtain ⟨c, hbeq, h⟩ := h'
  cases c with
  | false => simp at h
  | true =>
    simp only [if_true, Result.ok.injEq, decide_eq_true_eq] at h
    have := Expr.beq_refines ha hb hbeq
    rw [absKey, absKey, of_decide_eq_true this.symm, h]

theorem expr_key_exact :
    KeyExact expr.Expr.Insts.Con_ron_coreRonHashmapEq2 ExprWF absExpr := by
  intro a b ha hb h
  exact of_decide_eq_true (Expr.eq2_refines ha hb h).symm

/-! ## The memo probes

`memo1_get`/`memo_e_get`/`memo_n_get` are the owning probes of task #13's
deviation 1; each is `HashMap.get` with a `dup` on the hit, so a hit is a
recorded answer and a miss says nothing. -/

theorem memo1_get_hit {m : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    {k : expr_ops.ExprNatKey} {r : expr.Expr}
    (h : expr_ops.memo1_get m k = ok (some r)) :
    ron.hashmap.HashMap.get expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapHashable
      expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 m k = ok (some r) := by
  rw [expr_ops.memo1_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, h⟩ := h
  cases o with
  | none => simp at h
  | some w =>
    simp only [bind_eq_ok_iff, Result.ok.injEq, Option.some.injEq] at h
    obtain ⟨c, hdup, hc⟩ := h
    rw [Expr.dup_eq hdup] at hc
    rw [hget, hc]

theorem memo_e_get_hit {m : ron.hashmap.HashMap expr.Expr expr.Expr}
    {k r : expr.Expr} (h : expr_ops.memo_e_get m k = ok (some r)) :
    ron.hashmap.HashMap.get expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 m k = ok (some r) := by
  rw [expr_ops.memo_e_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, h⟩ := h
  cases o with
  | none => simp at h
  | some w =>
    simp only [bind_eq_ok_iff, Result.ok.injEq, Option.some.injEq] at h
    obtain ⟨c, hdup, hc⟩ := h
    rw [Expr.dup_eq hdup] at hc
    rw [hget, hc]

theorem memo_n_get_hit {m : ron.hashmap.HashMap expr.Expr Std.U64}
    {k : expr.Expr} {r : Std.U64} (h : expr_ops.memo_n_get m k = ok (some r)) :
    ron.hashmap.HashMap.get expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 m k = ok (some r) := by
  rw [expr_ops.memo_n_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, h⟩ := h
  cases o with
  | none => simp at h
  | some w => simp only [Result.ok.injEq, Option.some.injEq] at h; rw [hget, h]

/-- The key a walk probes with (`expr_nat_key` is a `dup` and a pair). -/
theorem expr_nat_key_eq {e : expr.Expr} {d : Std.U64} {k : expr_ops.ExprNatKey}
    (h : expr_ops.expr_nat_key e d = ok k) : k = ⟨e, d⟩ := by
  rw [expr_ops.expr_nat_key] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨c, hdup, hk⟩ := h
  rw [← hk, Expr.dup_eq hdup]

/-- A fresh memo table is empty (`ron::hashmap::HashMap::new`; the `Inv` half
of `HashMap.new_refines` is not needed, so neither is a `Hashable`
dictionary). -/
theorem new_al_v {K V : Type} {m : ron.hashmap.HashMap K V}
    (h : ron.hashmap.HashMap.new K V = ok m) : HashMap.al_v m = [] := by
  rw [ron.hashmap.HashMap.new] at h
  obtain ⟨hs, -, -⟩ := HashMap.new_with_capacity_pow2_spec h
  refine HashMap.al_v_eq_nil_of_slots_nil (fun j hj => ?_)
  rw [hs, HashMap.getElem!_replicate_nil]

/-- A fresh memo satisfies every invariant of this file (`*MemoInv.empty`). -/
theorem new_memo_inv {K V A : Type} {KWF : K → Prop} {absK : K → A} {Q : A → V → Prop}
    {m : ron.hashmap.HashMap K V} (h : ron.hashmap.HashMap.new K V = ok m) :
    MemoInv KWF absK Q m := MemoInv.empty (new_al_v h)

/-! ## `instantiate1` (`ExprOps.lean:29-189`)

The recipe every memoized walk of this file follows:

* the statement is **against the logical definition** (`Expr.instantiate1`),
  generalised over the memo and the cursor, and proved by induction on the
  `ExprWF` derivation — which is what supplies both the node's shape
  (`Expr.app_inv` and friends) and the children's well-formedness, since an
  Aeneas `partial_fixpoint` gives no induction principle of its own (task #20);
* the five leaf constructors skip the memo, as in the cited code;
* the five rebuilding ones probe it (`MemoInv.hit`), and on a miss recurse and
  write the answer back (`MemoInv.set`).

The generated body destructures *tuples* at every bind (`let (memo1, r) ← …`,
`let (_, memo2) ← insert …`), which `bind_eq_ok_iff` does not see through, so
every such bind is inverted in two steps: `bind_eq_ok_iff.mp` and then
`obtain ⟨_, _⟩` on the pair (task #16's trap). -/

/-- con-leche's `Inst1MemoInv` (`ExprOps.lean:61`), as the `Q` of `MemoInv`:
every recorded answer is the real one, and it is well formed. -/
def Inst1Q (v : ConLeche.Expr) : ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun k r => ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1 k.1 v k.2

/-- The simp set that reduces one node's worth of a generated walk: the `Rc`
deref, the two projections of the node, and the monadic bind. -/
theorem node_kind (d : Std.U64) (k : expr.ExprKind) :
    (expr.Expr.mk (expr.ExprNode.mk d k))._0.kind = k := rfl

theorem instantiate1_go_refines {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr) (d : Std.U64)
      (r : expr.Expr),
      MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo →
      expr_ops.instantiate1_go v memo e d = ok (r, memo') →
      (ExprWF r ∧
          absExpr r = ConLeche.Expr.instantiate1 (absExpr e) (absExpr v) d.val) ∧
        MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo' := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    split at h
    · rename_i hid
      have hv' : i.val = d.val := by scalar_tac
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      refine ⟨⟨hv, ?_⟩, hm⟩
      simp [ConLeche.Expr.instantiate1, hv']
    · rename_i hid
      have hne : i.val ≠ d.val := fun hc => hid (Std.UScalar.eq_of_val_eq hc)
      split at h
      · rename_i hgt
        have hgt' : d.val < i.val := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨i1, hi1, c, hc, hr, hmm⟩ := h
        subst hr; subst hmm
        refine ⟨⟨Expr.bvar_wf hc, ?_⟩, hm⟩
        rw [Expr.bvar_refines hc, HashMap.uscalar_sub_eq hi1]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1]
        rw [if_neg hne, if_pos (by omega)]
        simp
      · rename_i hgt
        have hgt' : ¬ (d.val < i.val) := fun hc => hgt (by scalar_tac)
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨c, hc, hr, hmm⟩ := h
        subst hr; subst hmm
        refine ⟨⟨Expr.bvar_wf hc, ?_⟩, hm⟩
        rw [Expr.bvar_refines hc]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1]
        rw [if_neg hne, if_neg (by omega)]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.fvar hty h1, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @sort u e hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.sort hu h1, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.mk_const hn hus h1, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.lit hl h1, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hkk := expr_nat_key_eq hk
    subst hkk
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, hf2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨f2, memo2⟩ := p1
      obtain ⟨p2, ha2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨a2, memo3⟩ := p2
      obtain ⟨r1, happ, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 d f2 hm hf2
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 d a2 hm2 ha2
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : Inst1Q (absExpr v)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), d⟩) r := by
        refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
        rw [Expr.app_refines happ, habs2, habs3]
        simp [ConLeche.Expr.instantiate1]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hkk := expr_nat_key_eq hk
    subst hkk
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 dd b hm2 hb
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : Inst1Q (absExpr v)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), d⟩) r := by
        refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam, ?_⟩
        rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm,
          HashMap.uscalar_add_eq hdd]
        simp [ConLeche.Expr.instantiate1]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hkk := expr_nat_key_eq hk
    subst hkk
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 dd b hm2 hb
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : Inst1Q (absExpr v)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), d⟩) r := by
        refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
        rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
          HashMap.uscalar_add_eq hdd]
        simp [ConLeche.Expr.instantiate1]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hkk := expr_nat_key_eq hk
    subst hkk
    cases o with
    | some w' =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w' := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hv2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨w2, memo3⟩ := p2
      obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨p3, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo4⟩ := p3
      obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo4 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 d w2 hm2 hv2
      obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 dd b hm3 hb
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p4, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo5⟩ := p4
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo5 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : Inst1Q (absExpr v)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), d⟩) r := by
        refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
        rw [Expr.let_e_refines hlet, habs2, habs3, habs4, HashMap.uscalar_add_eq hdd]
        simp [ConLeche.Expr.instantiate1]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hkk := expr_nat_key_eq hk
    subst hkk
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, hu, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨u, memo2⟩ := p1
      obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hproj, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 d u hm hu
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hsn : n2 = s := Result.ok_injective (hn2.symm.trans (name_dup_eq s))
      subst hsn
      have hans : Inst1Q (absExpr v)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj n2 i x)), d⟩) r := by
        refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
        rw [Expr.proj_refines hproj, habs2]
        simp [ConLeche.Expr.instantiate1]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins

/-- **`expr_ops::instantiate1` refines `Expr.instantiate1`.**  The fresh memo
satisfies the invariant vacuously (`Inst1MemoInv.empty`), so the walk's own
lemma gives the logical function directly -- which is exactly what con-leche's
`@[csimp]` lemma `instantiate1_eq_instantiate1Fast` says. -/
theorem instantiate1_refines {e v r : expr.Expr} {d : Std.U64} (he : ExprWF e)
    (hv : ExprWF v) (h : expr_ops.instantiate1 e v d = ok r) :
    absExpr r = ConLeche.Expr.instantiate1 (absExpr e) (absExpr v) d.val ∧ ExprWF r := by
  rw [expr_ops.instantiate1] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ :=
    instantiate1_go_refines hv he memo memo' d r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

end ConRon.Refine.ExprOps
