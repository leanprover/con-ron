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

/-! ## Two plumbing steps the repacked node added (task #38)

Since the node was repacked, every place that used to write the binder datum
inline calls the smart constructor `expr::binder_meta`; and the `Vec`
accumulators are pre-sized (`Vec::with_capacity`, task #34).  Both are the
identity in the model, and both are stated as `simp` lemmas so that the bind
they add collapses inside the `simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, …]` step
every walk below already runs.  (Task #38 made `BinderMeta.pw` an
`Arc<PropWhen>`; task #90 shrank `PropWhen` to one word's payload and put the
datum back by value, so `binder_meta` no longer allocates -- but it is still
the one constructor every binder goes through, and this lemma is unchanged.) -/

/-- `expr::binder_meta` is the datum wrapper, i.e. the identity. -/
@[simp, rust_reduce, rust_invert] theorem binder_meta_eq (pw : prop_when.PropWhen) :
    expr.binder_meta pw = ok ⟨pw⟩ := by
  simp [expr.binder_meta]

/-- `Vec::with_capacity` is `Vec::new` in the model: an empty list. -/
@[simp] theorem with_capacity_val {α : Type} (c : Std.Usize) :
    (alloc.vec.Vec.with_capacity α c).val = [] := rfl

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
  induction ls using HashMap.AList.recTail with
  | nil => rw [ron.hashmap.list_get.eq_def] at h; simp at h
  | last ckey cval =>
    rw [ron.hashmap.list_get.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | false => simp at h
    | true =>
      simp only [if_true, Result.ok.injEq, Option.some.injEq] at h
      exact ⟨ckey, by rw [HashMap.alv_cons, ← h]; exact List.mem_cons_self, hb⟩
  | cons ckey cval tl ih =>
    rw [ron.hashmap.list_get.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨k', hmem, heq⟩ := ih h
      exact ⟨k', by rw [HashMap.alv_cons]; exact List.mem_cons_of_mem _ (by simpa only [HashMap.alvO_some] using hmem),
        heq⟩
    | true =>
      simp only [if_true, Result.ok.injEq, Option.some.injEq] at h
      exact ⟨ckey, by rw [HashMap.alv_cons, ← h]; exact List.mem_cons_self, hb⟩

/-- **A memo hit returns a recorded entry.**  No `Eq2Spec`, no `Inv`: the
value comes back with a key that is really in the table. -/
theorem get_mem {m : ron.hashmap.HashMap K V} {k : K} {r : V}
    (h : ron.hashmap.HashMap.get HashableInst Eq2Inst m k = ok (some r)) :
    ∃ k', (k', r) ∈ HashMap.al_v m ∧ Eq2Inst.eq2 k' k = ok true := by
  rw [ron.hashmap.HashMap.get] at h
  -- task #35: an unallocated table (no buckets at all) answers `none` at once.
  split at h
  · simp at h
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
  induction ls using HashMap.AList.recTail generalizing old ls' with
  | nil =>
    rw [ron.hashmap.list_insert.eq_def] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2, HashMap.alv_cons]
    intro p hp
    simp only [HashMap.alvO_none, List.mem_singleton] at hp
    rw [hp]; exact hnew
  | last ckey cval =>
    have hhd : R ckey cval := hls (ckey, cval) (by rw [HashMap.alv_cons]; exact List.mem_cons_self)
    rw [ron.hashmap.list_insert.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | true =>
      simp only [if_true, core.mem.replace] at h
      simp at h
      obtain ⟨-, hls'⟩ := h
      subst hls'
      rw [HashMap.alv_cons]
      intro p hp
      simp only [HashMap.alvO_none, List.mem_singleton] at hp
      rw [hp]; exact hc k ckey v cval hnew hhd hb
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hls'⟩ := h
      subst hls'
      rw [HashMap.alv_cons]
      intro p hp
      simp only [HashMap.alvO_some, HashMap.alv_cons, HashMap.alvO_none,
        List.mem_cons] at hp
      rcases hp with hp | hp | hp
      · rw [hp]; exact hhd
      · rw [hp]; exact hnew
      · exact absurd hp (by simp)
  | cons ckey cval tl ih =>
    have hhd : R ckey cval := hls (ckey, cval) (by rw [HashMap.alv_cons]; exact List.mem_cons_self)
    have htl : ∀ p ∈ HashMap.alv tl, R p.1 p.2 := fun p hp =>
      hls p (by rw [HashMap.alv_cons]; exact List.mem_cons_of_mem _ (by simpa only [HashMap.alvO_some] using hp))
    rw [ron.hashmap.list_insert.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | true =>
      simp only [if_true, core.mem.replace] at h
      simp at h
      obtain ⟨-, hls'⟩ := h
      subst hls'
      rw [HashMap.alv_cons]
      intro p hp
      rcases List.mem_cons.1 hp with hp | hp
      · rw [hp]; exact hc k ckey v cval hnew hhd hb
      · exact htl p (by simpa only [HashMap.alvO_some] using hp)
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      replace h := bind_eq_ok_iff.mp h
      obtain ⟨q, hrec, h⟩ := h
      obtain ⟨o, tl1⟩ := q
      simp at h
      obtain ⟨-, hls'⟩ := h
      subst hls'
      rw [HashMap.alv_cons]
      intro p hp
      rcases List.mem_cons.1 hp with hp | hp
      · rw [hp]; exact hhd
      · exact ih htl hrec p (by simpa only [HashMap.alvO_some] using hp)

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
  induction ls using HashMap.AList.recTail with
  | nil =>
    intro nt nt' _ hnt h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    rw [← Result.ok_injective h]
    exact ⟨hnt, rfl⟩
  | last k v =>
    intro nt nt' hls hnt h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨⟨o, nt1⟩, hins, hrec⟩ := h
    have hhd : R k v := hls (k, v) (by rw [HashMap.alv_cons]; exact List.mem_cons_self)
    obtain ⟨h1, h2⟩ := insert_no_resize_pres hc hnt hhd hins
    rw [← Result.ok_injective hrec]
    exact ⟨h1, h2⟩
  | cons k v tl ih =>
    intro nt nt' hls hnt h
    rw [ron.hashmap.HashMap.move_elements_from_list.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨⟨o, nt1⟩, hins, hrec⟩ := h
    have hhd : R k v := hls (k, v) (by rw [HashMap.alv_cons]; exact List.mem_cons_self)
    obtain ⟨h1, h2⟩ := insert_no_resize_pres hc hnt hhd hins
    have htl : ∀ p ∈ HashMap.alv tl, R p.1 p.2 := fun p hp =>
      hls p (by rw [HashMap.alv_cons]
                exact List.mem_cons_of_mem _ (by simpa only [HashMap.alvO_some] using hp))
    obtain ⟨h3, h4⟩ := ih nt1 nt' htl h1 hrec
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

/-- `ensure_slots` (task #35's lazy allocation) either leaves the table alone
or replaces an *empty* bucket vector by a longer one of empty buckets: either
way every recorded entry of the result was already recorded.  This is the one
step `insert` gained since task #21, and it needs no `Inv`. -/
theorem ensure_slots_pres {R : K → V → Prop} {m m' : ron.hashmap.HashMap K V}
    (hm : ∀ p ∈ HashMap.al_v m, R p.1 p.2)
    (h : ron.hashmap.HashMap.ensure_slots m = ok m') :
    ∀ p ∈ HashMap.al_v m', R p.1 p.2 := by
  rw [ron.hashmap.HashMap.ensure_slots] at h
  split at h
  · obtain ⟨t, ht, hok⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hts, -, -⟩ := HashMap.new_with_capacity_pow2_spec ht
    have hslots : m'.slots = t.slots :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.slots) (Result.ok_injective hok)).symm
    have hnil : HashMap.al_v m' = [] := by
      refine HashMap.al_v_eq_nil_of_slots_nil (fun j hj => ?_)
      rw [hslots, hts, HashMap.getElem!_replicate_nil]
    rw [hnil]; simp
  · have eslots : m'.slots = m.slots :=
      (congrArg (fun z : ron.hashmap.HashMap K V => z.slots) (Result.ok_injective h)).symm
    rw [HashMap.al_v_congr eslots]; exact hm

/-- **An insert records its own pair and nothing else.**  No `Eq2Spec`, no
`Inv`; the resize is covered because it only moves recorded entries. -/
theorem insert_pres {R : K → V → Prop} (hc : Compat Eq2Inst R)
    {m : ron.hashmap.HashMap K V} {k : K} {v : V} {old : Option V}
    {m' : ron.hashmap.HashMap K V}
    (hm : ∀ p ∈ HashMap.al_v m, R p.1 p.2) (hnew : R k v)
    (h : ron.hashmap.HashMap.insert HashableInst Eq2Inst m k v = ok (old, m')) :
    ∀ p ∈ HashMap.al_v m', R p.1 p.2 := by
  rw [ron.hashmap.HashMap.insert] at h
  obtain ⟨m0, hens, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨old0, m1⟩, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨h1, -⟩ := insert_no_resize_pres hc (ensure_slots_pres hm hens) hnew hins
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

/-! ### The same two, keyed on the Rust equation (task #71)

`MemoInv.hit`/`MemoInv.set` take the invariant first, which is what a hand
proof wants; a `grind [→ …]` lemma needs the **Rust equation first**, so that
its E-matching trigger is the probe or the insert the inverted body provides
rather than every memo invariant in scope (`Refine/README.md` §"Writing a new
refinement lemma", the first keying rule).  These two are what every memoised
walk registers. -/

end Memo

/-! ## The two memo key types

Five of this file's memos are keyed by `(node, cursor)` (`ExprNatKey`, whose
`Eq2` is `expr::beq` then the `u64`), three by the node alone.  `KeyExact` for
both is `Expr.beq`'s exactness on well-formed nodes (task #20). -/

/-- The `(node, cursor)` key's abstraction: con-leche's `(Expr × Nat)`. -/
def absKey (k : expr_ops.ExprNatKey) : ConLeche.Expr × Nat := (absExpr k.e, k.d.val)

/-- A memo key is well formed when its node is. -/
def KeyWF (k : expr_ops.ExprNatKey) : Prop := ExprWF k.e

@[simp] theorem absKey_mk (e : expr.Expr) (d : Std.U64) :
    absKey ⟨e, d⟩ = (absExpr e, d.val) := rfl

@[simp] theorem KeyWF_mk (e : expr.Expr) (d : Std.U64) : KeyWF ⟨e, d⟩ ↔ ExprWF e := Iff.rfl

/-! ## The memo probes

`memo1_get`/`memo_e_get`/`memo_n_get` are the owning probes of task #13's
deviation 1; each is `HashMap.get` with a `dup` on the hit, so a hit is a
recorded answer and a miss says nothing. -/

/-! ## `instantiate1` (`ExprOps.lean:29-189`)

The recipe every memoized walk of this file follows:

* the statement is **against the logical definition** (`Expr.instantiate1`),
  generalised over the memo and the cursor, and proved by induction on the
  `ExprWF` derivation — which is what supplies both the node's shape
  (`Expr.app_inv` and friends) and the children's well-formedness in one step,
  where the `partial_fixpoint`'s own `fixpoint_induct` would want an admissible
  motive and supply neither (task #20; DESIGN.md task #99-PFIX);
* the five leaf constructors skip the memo, as in the cited code;
* the five rebuilding ones probe it (`MemoInv.hit`), and on a miss recurse and
  write the answer back (`MemoInv.set`).

The generated body destructures *tuples* at every bind (`let (memo1, r) ← …`,
`let (_, memo2) ← insert …`), which `bind_eq_ok_iff` does not see through, so
every such bind is inverted in two steps: `bind_eq_ok_iff.mp` and then
`obtain ⟨_, _⟩` on the pair (task #16's trap). -/

/-! ## Plumbing for the `Vec` walks -/

/-- A `usize`-to-`u64` cast is the identity in the model: `usize` is never
wider than 64 bits (`System.Platform.numBits_eq`). -/
theorem usize_cast_u64_val (x : Std.Usize) :
    (Std.UScalar.cast .U64 x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_greater_numBits_eq _ _ ?_
  rw [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> omega

/-- A `u64`-to-`usize` cast is the identity on values that fit a `usize` --
which is what an in-range index is. -/
theorem u64_cast_usize_val {x : Std.U64} (h : x.val ≤ Std.Usize.max) :
    (Std.UScalar.cast .Usize x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_
  have hpos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  have hmax : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    simp only [Std.Usize.max, Std.Usize.numBits]
    omega
  omega

/-- The empty `Vec` abstracts to the empty list. -/
@[simp] theorem absExprs_new : absExprs (alloc.vec.Vec.new expr.Expr) = [] := rfl

/-- `Vec::index` without an `Inhabited` instance on the element type (the
`getElem!` form of `HashMap.vec_index_eq` is unavailable for `expr::Expr`). -/
theorem vec_index_getElem? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-! ## The `Vec` copies

`levels_copy` and `cons_expr` have no Lean counterpart at all: they are the
`Vec` copies that stand for Lean's shared lists (task #13's deviation 3), so
their lemmas are *raw* `Vec` equations -- the copy is the same list, because
`level::dup` and `expr::dup` are the identity in the model (DESIGN.md §3.2) --
and the abstraction equation follows by `congrArg`. -/

end ConRon.Refine.ExprOps

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`instantiate1_refines` is the file's headline lemma and the deepest chain in it
-- the `(node, cursor)` memo through `HashMap.insert`'s resize, `expr::beq`'s
exactness on well-formed nodes, and the ten smart constructors -- so it is the
one worth pinning. -/

