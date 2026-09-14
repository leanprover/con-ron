/-
`ConRon.Refine.Frontend.IndValidateR` — **an inductive record, validated,
exact against con-leche** (task #87, phase 3).

`crates/con-ron-core/src/frontend/export_c.rs:1425-1993` against
`ConLeche/Frontend/ExportC.lean:412-563 validateIndD`: the half of an
inductive record's processing that reads the state and changes nothing — the
verdict, or the block's constructors in the block's own order with the
declared parameter count.

## What this file gives the line layer

    theorem validate_ind_d_refines {st lst tys cts rcs o}
        (hrel : StateDRel st lst) (hwf : StateDWF st)
        (h : frontend.export_c.validate_ind_d st tys cts rcs = ok o) :
        ValidateOut o (ConLeche.Frontend.validateIndD lst (absIndTypeRecs tys)
          (absIndCtorRecs cts) (absIndRecRecs rcs))

`ValidateOut` is agent R's (`Refine/Frontend/IndR.lean`): `validateIndD`
returns `M (RecordVerdict ⊕ (List IndCtorRec × Nat))` — the verdict on the
**left**, where `LineOutV` puts it on the right — and the port returns it
through `LineErr`, the module's one merged error channel.

Task #84 split that one Lean function into eighteen Rust ones for Aeneas's
loop-shape rule.  Agent R's `IndR.lean` proves the first eight
(`any_ty_unsafe`, `any_ty_nested`, `all_num_params`, `ty_names_of`,
`ty_types_of`, `listed_ctors_of`, `ctor_names_of`, `flatten_listed`); this
file proves the other nine and composes all seventeen into the capstone:

    names_have_dup_refines     the cited `unless flat.Nodup`
    ctor_index_of_refines      the cited `ctorIx` fold
    check_one_ctor_refines     `cidx`, `induct` and `numFields`, at the step
    order_type_ctors_refines   the inner `for n in ns`
    order_block_ctors_refines  the outer `for tn in tyNames.zip listed`
    k_expected_of_refines      official's `is_K_target`
    check_rec_indices_refines  the `for tt in tyNames.zip tyTypes`
    check_one_rec_refines      one step of the `for r in rcs`
    check_rec_records_refines  that whole loop
    validate_ind_d_refines     the capstone

The outcome vocabulary is `ValidateOut` (agent R's) at the top and, for the
fragments, `LoopOut`, `StepLoopOut`, `OrderStepOut`, `OrderOut` and
`BlockOut`: every early return of `validateIndD`'s four loops is an
`.invalid` verdict, so each of those names only the verdict's *kind*.

## The port bug this file found

`export_c::ctor_index_of` used to build the name -> record-index map **first
record wins**:

    if !m.contains_key(&ns[k]) { m.insert(name::dup(&ns[k]), k as u64); }

with a doc comment citing `HashMap.insertIfNew` — a function con-leche does
not call.  `ExportC.lean:412-563` builds the map **last wins**:

    (ctorNames.foldl (fun mi n => (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1

— `Std.HashMap.insert` overwrites.  The two maps differ exactly when
`ctorNames` repeats a name, and the difference is **observable through
`ValidateOut`**, which is why this is a bug and not a deviation to prove
around.  The witness: `listed = [[a, b]]` (so `flat = [a, b]` is `Nodup` and
two long), `cts = [c0 named a, c1 named a]` (so `flat.length == cts.length`
passes), `ctorNames = [a, a]`.  At the name `a` the port took `cts[0]` and
con-leche takes `cts[1]`; if `c0.cv.ty` is an index the expression table does
not hold and `c1.cv.ty` is, the port returns `.Err (.Msg …)` while con-leche
runs on to `b`, finds no such constructor and returns
`.ok (.inl (.invalid "No such constructor b"))` — and `ValidateOut` demands an
`.error` of con-leche in that case.  The Rust now inserts unconditionally and
`ctor_index_of_refines` is an ordinary loop induction against the fold.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.IndR
import ConRon.Refine.Frontend.Ind

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Plumbing

The shapes `Refine/Frontend/IndR.lean` keeps `private`; this file is above it
but cannot see them, so the three lines are restated. -/

/-- A `Vec` read at `i`, forwards. -/
private theorem iv_index_val {α : Type} {v : alloc.vec.Vec α}
    {i : Std.Usize} {x : α} {hlt : i.val < v.val.length}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]'hlt = x := by
  have hg := ExprOps.vec_index_getElem? h
  rw [List.getElem?_eq_getElem hlt] at hg
  exact Option.some_injective _ hg

/-- The abstracted prefix, extended by one. -/
private theorem iv_take_succ {v : alloc.vec.Vec name.Name} {i : Nat}
    (hlt : i < v.val.length) :
    (absNames v).take (i + 1) = (absNames v).take i ++ [absName (v.val[i]'hlt)] := by
  simp only [absNames]
  rw [List.take_add_one]
  simp [List.getElem?_eq_getElem hlt]

/-! ## `names_have_dup`

`export_c.rs:1425-1437` against the cited `unless flat.Nodup`.  con-leche
tests the list; the port walks it with a `ron::HashMap<Name, bool>` seen-set,
so the loop invariant is *what the table holds is the abstracted prefix*. -/

/-- The seen-set's membership, as a predicate on the abstracted prefix. -/
private def SeenPrefix (seen : ron.hashmap.HashMap name.Name Bool)
    (l : List ConLeche.Name) : Prop :=
  ∀ k, NameWF k → ((HashMap.toFun seen k).isSome = true ↔ absName k ∈ l)

/-- The index recursion behind `export_c::names_have_dup`. -/
private theorem names_have_dup_loop_refines {flat : alloc.vec.Vec name.Name}
    (hwf : NamesWF flat) (N : Nat) :
    ∀ (seen : ron.hashmap.HashMap name.Name Bool) (n i : Std.Usize) (b : Bool),
      flat.val.length - i.val = N → n.val = flat.val.length →
      HashMap.Inv State.hName seen → HashMap.KeysOk NameWF seen →
      SeenPrefix seen ((absNames flat).take i.val) →
      ((absNames flat).take i.val).Nodup →
      frontend.export_c.names_have_dup_loop flat seen n i = ok b →
      (b = true ↔ ¬ (absNames flat).Nodup) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro seen n i b hN hn hinv hkeys hsp hnd h
    rw [frontend.export_c.names_have_dup_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < flat.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨nm, hidx, h⟩ := h
      have hnmv : flat.val[i.val]'hltv = nm := iv_index_val hidx
      have hnmwf : NameWF nm := by rw [← hnmv]; exact hwf _ (List.getElem_mem _)
      obtain ⟨c, hc, h⟩ := h
      -- `contains_key` is `get`, and `get` is `toFun`
      have hcv : c = (HashMap.toFun seen nm).isSome := by
        rw [ron.hashmap.HashMap.contains_key] at hc
        obtain ⟨r, hr, hc⟩ := bind_eq_ok_iff.mp hc
        rw [HashMap.get_refines_wf State.nameEq2Fwd hinv hkeys hnmwf hr] at hc
        cases hq : HashMap.toFun seen nm <;> rw [hq] at hc <;> simp_all
      split at h
      · -- a repeat: the name at `i` is already in the prefix
        rename_i hct
        simp only [Result.ok.injEq] at h
        rw [← h]
        have hmem : absName nm ∈ (absNames flat).take i.val := by
          rw [← hsp nm hnmwf]; rw [← hcv]; exact hct
        constructor
        · intro _ hcon
          have hsub : ((absNames flat).take (i.val + 1)).Nodup :=
            List.Nodup.sublist (List.take_sublist _ _) hcon
          rw [iv_take_succ hltv] at hsub
          have hmem2 : absName (flat.val[i.val]'hltv) ∈ (absNames flat).take i.val := by
            rw [hnmv]; exact hmem
          exact (List.nodup_cons.mp
            ((List.perm_append_singleton _ _).nodup_iff.mp hsub)).1 hmem2
        · intro _; rfl
      · -- fresh: extend the prefix and recurse
        rename_i hct
        have hnotmem : absName nm ∉ (absNames flat).take i.val := by
          intro hc
          exact hct ((hsp nm hnmwf).mpr hc ▸ hcv ▸ rfl)
        obtain ⟨nm2, hdup, h⟩ := bind_eq_ok_iff.mp h
        have hnm2 : nm2 = nm := by rw [name_dup_eq] at hdup; exact (Result.ok_injective hdup).symm
        have hnm2wf : NameWF nm2 := by rw [hnm2]; exact hnmwf
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨old, seen1⟩ := p
        simp only [uncurry_apply_pair] at h
        obtain ⟨hinv1, -, hupd, hkeys1⟩ :=
          HashMap.insert_refines_wf State.nameEq2Fwd hinv hkeys hnm2wf hins
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        refine ih (flat.val.length - i2.val) (by omega) seen1 n i2 b (by omega) hn
          hinv1 hkeys1 ?_ ?_ h
        · intro k hk
          rw [hupd, Function.update_apply, hi2v, iv_take_succ hltv]
          by_cases hkk : k = nm2
          · subst hkk
            simp [hnm2, hnmv]
          · rw [if_neg hkk, hsp k hk]
            constructor
            · intro hm; exact List.mem_append_left _ hm
            · intro hm
              rcases List.mem_append.mp hm with hm | hm
              · exact hm
              · exfalso
                simp only [List.mem_singleton] at hm
                exact hkk (Name.absName_injective hk hnm2wf (by rw [hm, hnmv, hnm2]))
        · rw [hi2v, iv_take_succ hltv]
          refine (List.perm_append_singleton _ _).nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, hnd⟩)
          rw [hnmv]
          exact hnotmem
    · rename_i hlt
      have hge : flat.val.length ≤ i.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      have htake : (absNames flat).take i.val = absNames flat := by
        rw [List.take_of_length_le]; simpa [absNames] using hge
      rw [htake] at hnd
      simp [hnd]

/-- **`export_c::names_have_dup` is con-leche's `flat.Nodup`**, negated
(`ExportC.lean:412-563`, the cited `unless flat.Nodup`). -/
theorem names_have_dup_refines {flat : alloc.vec.Vec name.Name} (hwf : NamesWF flat)
    {b : Bool} (h : frontend.export_c.names_have_dup flat = ok b) :
    (b = true ↔ ¬ (absNames flat).Nodup) := by
  rw [frontend.export_c.names_have_dup] at h
  obtain ⟨seen, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hinv, hav, htf⟩ := HashMap.new_refines hnew
  refine names_have_dup_loop_refines hwf (flat.val.length - (0#usize : Std.Usize).val)
    seen (alloc.vec.Vec.len flat) 0#usize b rfl (by simp) hinv ?_ ?_ (by simp) h
  · intro p hp; rw [hav] at hp; simp at hp
  · intro k _; rw [htf k]; simp


/-! ## `ctor_index_of`

`export_c.rs:1449-1458` against the cited `ctorIx` fold of
`ExportC.lean:412-563`:

    (ctorNames.foldl (fun mi n => (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1

**This is where task #87 found a port bug.**  Until commit `0cdb73c` the port
guarded its insert with `if !m.contains_key(&ns[k])` — *first* record wins —
on the strength of a doc comment naming `HashMap.insertIfNew`, a function
con-leche does not call; `Std.HashMap.insert` overwrites, so con-leche is
*last* wins.  The two differ exactly when `ctorNames` repeats a name, and the
difference is **observable**: at a repeated name the two sides run the
constructor checks on *different* records, and those checks can fail with a
`LineErr::Msg` (an unknown `induct` or type index) on one side while the other
runs on to a plain `.invalid` — which `ValidateOut` distinguishes.  The port
now inserts unconditionally and the loop below is a one-to-one mirror of the
fold. -/

/-- con-leche's `ctorIx` fold, named.  `ExportC.lean:412-563`:
`(ctorNames.foldl (fun mi n => (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1`. -/
private def ctorIxAux (m : Std.HashMap ConLeche.Name Nat) (j : Nat)
    (ns : List ConLeche.Name) : Std.HashMap ConLeche.Name Nat × Nat :=
  ns.foldl (fun (mi : Std.HashMap ConLeche.Name Nat × Nat) n =>
    (mi.1.insert n mi.2, mi.2 + 1)) (m, j)

private theorem ctorIxAux_cons (m : Std.HashMap ConLeche.Name Nat) (j : Nat)
    (n : ConLeche.Name) (ns : List ConLeche.Name) :
    ctorIxAux m j (n :: ns) = ctorIxAux (m.insert n j) (j + 1) ns := rfl

/-- A name the fold never sees is left alone. -/
private theorem ctorIxAux_not_mem (n : ConLeche.Name) :
    ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat) (j : Nat),
      n ∉ ns → (ctorIxAux m j ns).1[n]? = m[n]? := by
  intro ns
  induction ns with
  | nil => intro m j _; rfl
  | cons a t iht =>
    intro m j hn
    rw [ctorIxAux_cons, iht _ _ (fun hc => hn (List.mem_cons_of_mem _ hc))]
    rw [Std.HashMap.getElem?_insert]
    rw [if_neg (by simpa using fun hc => hn (by rw [hc]; exact List.mem_cons_self))]

/-- The fold's key set is what it has seen: the names occurring in
`ctorNames`.  This is what the reordering loop's `ctorIx[n]?` reads. -/
private theorem ctorIxAux_mem (n : ConLeche.Name) :
    ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat) (j : Nat),
      ((ctorIxAux m j ns).1[n]?).isSome = true ↔ ((m[n]?).isSome = true ∨ n ∈ ns) := by
  intro ns
  induction ns with
  | nil => intro m j; simp [ctorIxAux]
  | cons a t iht =>
    intro m j
    rw [ctorIxAux_cons, iht]
    by_cases hna : n = a
    · subst hna
      simp
    · rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun hc => hna hc.symm)]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h hna
          · exact Or.inr h

/-- **Under `Nodup` the fold is the index.**  Not needed by the refinement —
the port is the same fold — but it is what makes `ordered` the block's own
order, so it is kept as the fold's characterisation. -/
private theorem ctorIxAux_nodup :
    ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat) (j : Nat),
      ns.Nodup → ∀ (k : Nat) (hk : k < ns.length),
        (ctorIxAux m j ns).1[ns[k]'hk]? = some (j + k) := by
  intro ns
  induction ns with
  | nil => intro m j _ k hk; simp at hk
  | cons a t iht =>
    intro m j hnd k hk
    rw [ctorIxAux_cons]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      rw [ctorIxAux_not_mem a t _ _ (List.nodup_cons.mp hnd).1]
      simp
    | succ s =>
      have hs : s < t.length := by simpa using hk
      simp only [List.getElem_cons_succ]
      rw [iht _ _ (List.nodup_cons.mp hnd).2 s hs]
      congr 1
      omega

/-- The index recursion behind `export_c::ctor_index_of`. -/
private theorem ctor_index_of_loop_refines {ns : alloc.vec.Vec name.Name}
    (hwf : NamesWF ns) (N : Nat) :
    ∀ (m : ron.hashmap.HashMap name.Name Std.U64) (s : Std.HashMap ConLeche.Name Nat)
      (n k : Std.Usize) (m' : ron.hashmap.HashMap name.Name Std.U64),
      ns.val.length - k.val = N → n.val = ns.val.length →
      HashMap.Inv State.hName m → HashMap.KeysOk NameWF m →
      HashMap.RelOn NameWF m s absName (fun u => u.val) →
      frontend.export_c.ctor_index_of_loop ns m n k = ok m' →
      HashMap.Inv State.hName m' ∧ HashMap.KeysOk NameWF m' ∧
        HashMap.RelOn NameWF m'
          (ctorIxAux s k.val ((absNames ns).drop k.val)).1 absName (fun u => u.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m s n k m' hN hn hinv hkeys hrel h
    rw [frontend.export_c.ctor_index_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : k.val < ns.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨nm, hidx, h⟩ := h
      have hnmv : ns.val[k.val]'hltv = nm := iv_index_val hidx
      have hnmwf : NameWF nm := by rw [← hnmv]; exact hwf _ (List.getElem_mem _)
      obtain ⟨nm2, hdup, h⟩ := h
      have hnm2 : nm2 = nm := by
        rw [name_dup_eq] at hdup; exact (Result.ok_injective hdup).symm
      have hnm2wf : NameWF nm2 := by rw [hnm2]; exact hnmwf
      obtain ⟨u, hu, h⟩ := h
      have huv : u.val = k.val := by
        rw [lift_eq, Result.ok.injEq] at hu
        rw [← hu]; exact Env.usize_cast_u64_val k
      obtain ⟨p, hins, h⟩ := h
      obtain ⟨old, m1⟩ := p
      simp only [uncurry_apply_pair] at h
      obtain ⟨hinv1, -, -, hkeys1⟩ :=
        HashMap.insert_refines_wf State.nameEq2Fwd hinv hkeys hnm2wf hins
      obtain ⟨hrel1, -⟩ :=
        HashMap.Rel_insert_wf State.nameEq2Fwd
          (fun a b ha hb hab => Name.absName_injective ha hb hab) hinv hkeys hrel
          hnm2wf hins
      obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
      have hk1v : k1.val = k.val + 1 := HashMap.uscalar_add_eq hk1
      have hdrop : (absNames ns).drop k.val
          = absName nm :: (absNames ns).drop (k.val + 1) := by
        simp only [absNames]
        rw [List.drop_eq_getElem_cons (by simpa using hltv), List.getElem_map, hnmv]
      rw [hnm2, huv] at hrel1
      have hres := ih (ns.val.length - k1.val) (by omega) m1
        (s.insert (absName nm) k.val) n k1 m' rfl hn hinv1 hkeys1 hrel1 h
      rw [hdrop, ctorIxAux_cons, ← hk1v]
      exact hres
    · rename_i hlt
      have hge : ns.val.length ≤ k.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hdrop : (absNames ns).drop k.val = [] := by
        rw [List.drop_eq_nil_iff]; simpa [absNames] using hge
      rw [hdrop]
      exact ⟨hinv, hkeys, hrel⟩

/-- **`export_c::ctor_index_of` refines the `ctorIx` fold of `validateIndD`**
(`ConLeche/Frontend/ExportC.lean:412-563`), key for key and index for index. -/
theorem ctor_index_of_refines {ns : alloc.vec.Vec name.Name} (hwf : NamesWF ns)
    {m : ron.hashmap.HashMap name.Name Std.U64}
    (h : frontend.export_c.ctor_index_of ns = ok m) :
    HashMap.Inv State.hName m ∧ HashMap.KeysOk NameWF m ∧
      HashMap.RelOn NameWF m (ctorIxAux ∅ 0 (absNames ns)).1 absName (fun u => u.val) := by
  rw [frontend.export_c.ctor_index_of] at h
  obtain ⟨m0, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hinv, hav, htf⟩ := HashMap.new_refines hnew
  have hres := ctor_index_of_loop_refines hwf (ns.val.length - (0#usize : Std.Usize).val)
    m0 ∅ (alloc.vec.Vec.len ns) 0#usize m rfl (by simp) hinv
    (by intro p hp; rw [hav] at hp; simp at hp) (HashMap.RelOn_empty htf) h
  simpa using hres

/-! ## con-leche's `validateIndD`, with its four loops named

`ExportC.lean:412-563` is one `do` block with four `for` loops and an early
`return` out of each; task #84 split it into twenty-odd Rust functions.  A
refinement lemma per Rust function therefore needs the *fragments* of
`validateIndD` those functions refine, and Lean has no way to name a loop body
that lives inside another definition.

So this section is the **one escape hatch of the file** (the maintainer's rule
for "where the port and the Lean do not line up one for one"): a verbatim copy
of `validateIndD` in which each loop body is a named definition,

    lOrderStep       the `for n in ns` body (one constructor record)
    lOrderBlockStep  the `for tn in tyNames.zip listed` body (one type former)
    lRecIdxStep      the `for tt in tyNames.zip tyTypes` body (`numIndices`)
    lRecStep         the `for r in rcs` body (one recursor record)
    lKExpectedOf     the `kExpected?` match

glued by `lForIn`, `forIn` on a list written as a structural recursion, and
**proved equal to `validateIndD` itself** by `lValidateIndD_eq`.  The copy is
exact — the verdict messages included — so the equation is an identity, not a
weakening; what it is *not* is `rfl`, because Lean's `match` auxiliaries are
per-definition constants that `isDefEq` will not unfold (a `match` written
here and the identical `match` written in `ExportC.lean` elaborate to
`lOrderBlockStep.match_1` and `validateIndD.match_7`, and no transparency
setting identifies them).  `lValidateIndD_eq` therefore descends with
`mIteCong`/`mBindCong`/`lForIn_congr` and does `cases` on each scrutinee,
which reduces both matchers.  That descent is the whole proof; nothing about
what `validateIndD` *computes* is assumed. -/

section Mirror

open ConLeche ConLeche.Frontend

/-- `forIn` over a list in `M`, as a structural recursion. -/
def lForIn {α σ : Type} (f : α → σ → M (ForInStep σ)) : List α → σ → M σ
  | [], s => pure s
  | a :: l, s => do
      match ← f a s with
      | .done s' => pure s'
      | .yield s' => lForIn f l s'

theorem forIn_eq_lForIn {α σ : Type} (f : α → σ → M (ForInStep σ)) (L : List α) (s : σ) :
    forIn L s f = lForIn f L s := by
  induction L generalizing s with
  | nil => simp only [List.forIn_nil, lForIn]
  | cons a l ih => simp only [List.forIn_cons, ih, lForIn]; rfl

theorem lForIn_congr {α σ : Type} {f g : α → σ → M (ForInStep σ)}
    (h : ∀ a s, f a s = g a s) (L : List α) (s : σ) : lForIn f L s = lForIn g L s := by
  have hfg : f = g := funext fun a => funext fun s => h a s
  rw [hfg]

theorem mIteCong {α : Type} {c : Prop} [Decidable c] {a a' b b' : α}
    (ha : a = a') (hb : b = b') : (if c then a else b) = (if c then a' else b') := by
  rw [ha, hb]

theorem mBindCong {α β : Type} {x y : M α} {f g : α → M β} (hx : x = y)
    (hf : ∀ a, f a = g a) : x >>= f = y >>= g := by
  rw [hx]; exact bind_congr hf

/-- The outcome of `validateIndD`. -/
abbrev LVRes := RecordVerdict ⊕ (List IndCtorRec × Nat)

/-- One step of the inner reordering loop. -/
def lOrderStep (st : StateD) (T : Name) (ctorIx : Std.HashMap Name Nat)
    (ctsA : Array IndCtorRec) (nPd : Nat)
    (n : Name) (s : Option LVRes × Array IndCtorRec × Nat) :
    M (ForInStep (Option LVRes × Array IndCtorRec × Nat)) := do
  let ordered := s.2.1
  let j := s.2.2
  let some k := ctorIx[n]? |
    return .done (some (.inl (.invalid s!"No such constructor {n}")), ordered, j)
  let some c := ctsA[k]? |
    return .done (some (.inl (.invalid s!"No such constructor {n}")), ordered, j)
  if let some ci := c.cidx then
    unless ci == j do
      return .done (some (.inl (.invalid s!"constructor {n} declares cidx {ci}; it is \
        constructor {j} of {T}")), ordered, j)
  if let some iw := c.induct then
    let iwn ← st.name iw
    unless iwn == T do
      return .done (some (.inl (.invalid s!"constructor {n} declares induct {iwn}; it is \
        a constructor of {T}")), ordered, j)
  let cty ← getDeclD st c.cv.type
  unless nPd + c.numFields == indPiTeleLen cty do
    return .done (some (.inl (.invalid s!"constructor {n} declares {c.numFields} fields at \
      {nPd} parameters; its type has {indPiTeleLen cty} binders")), ordered, j)
  return .yield (none, ordered.push c, j + 1)

/-- One step of the outer reordering loop. -/
def lOrderBlockStep (st : StateD) (ctorIx : Std.HashMap Name Nat)
    (ctsA : Array IndCtorRec) (nPd : Nat)
    (tn : Name × List Name) (s : Option LVRes × Array IndCtorRec) :
    M (ForInStep (Option LVRes × Array IndCtorRec)) := do
  let r ← lForIn (fun n s' => lOrderStep st tn.1 ctorIx ctsA nPd n s') tn.2 (none, s.2, 0)
  match r.1 with
  | some rr => pure (.done (some rr, r.2.1))
  | none => pure (.yield (none, r.2.1))

/-- One step of the `numIndices` loop. -/
def lRecIdxStep (T : Name) (rn : Name) (numIndices nPd : Nat)
    (tt : Name × Expr) (_s : Option LVRes × Unit) :
    M (ForInStep (Option LVRes × Unit)) :=
  if tt.1 == T then
    match tt.2.piSortTeleLen? with
    | some n =>
      if nPd + numIndices == n then pure (.yield (none, ()))
      else pure (.done (some (.inl (.invalid s!"recursor {rn} declares {numIndices} indices; \
        {T} has {n - nPd} at {nPd} parameters")), ()))
    | none => pure (.yield (none, ()))
  else pure (.yield (none, ()))

/-- One step of the recursor-record loop. -/
def lRecStep (st : StateD) (tyNames : List Name) (tyTypes : List Expr)
    (nPd nTypes nCtors : Nat) (kExpected? : Option Bool)
    (r : IndRecRec) (_s : Option LVRes × Unit) :
    M (ForInStep (Option LVRes × Unit)) := do
  let rn ← st.name r.cv.name
  unless r.numParams == nPd do
    return .done (some (.inl (.invalid s!"recursor {rn} declares {r.numParams} parameters; \
      the block declares {nPd}")), ())
  unless r.numMotives == nTypes do
    return .done (some (.inl (.invalid s!"recursor {rn} declares {r.numMotives} motives; \
      the block has {nTypes} inductive types")), ())
  unless r.numMinors == nCtors do
    return .done (some (.inl (.invalid s!"recursor {rn} declares {r.numMinors} minor premises; \
      the block has {nCtors} constructors")), ())
  if let some kE := kExpected? then
    unless r.k == kE do
      return .done (some (.inl (.invalid s!"recursor {rn} declares k := {r.k}; the generated \
        recursor of this block is{if kE then "" else " not"} K-like")), ())
  match rn with
  | .str T "rec" => do
    let res ← lForIn (fun tt s' => lRecIdxStep T rn r.numIndices nPd tt s')
      (tyNames.zip tyTypes) (none, ())
    match res.1 with
    | some rr => pure (.done (some rr, ()))
    | none => pure (.yield (none, ()))
  | _ => pure (.yield (none, ()))

/-- con-leche's `kExpected?`. -/
def lKExpectedOf (tyTypes : List Expr) (listed : List (List Name)) (cts : List IndCtorRec) :
    Option Bool :=
  match tyTypes, listed, cts with
  | [ty], [[_]], [c] =>
    match ty.piResult with
    | .sort s => some (c.numFields == 0 && Level.isEquiv s .zero == some true)
    | _ => none
  | _, _, _ => some false

/-- con-leche's `validateIndD`, with its four loops named. -/
def lValidateIndD (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) : M LVRes := do
  if tys.any (·.isUnsafe) then
    return .inl (.declined "unsafe inductive declaration")
  let nPs := tys.map (·.numParams)
  let nPd := nPs.head?.getD 0
  unless nPs.all (· == nPd) do
    return .inl (.declined "inductive block whose type records disagree on numParams")
  let tyNames ← tys.mapM fun t => st.name t.cv.name
  let tyTypes ← tys.mapM fun t => getDeclD st t.cv.type
  let listed ← tys.mapM fun t => t.ctors.mapM st.name
  let ctorNames ← cts.mapM fun c => st.name c.cv.name
  let flat := listed.flatten
  unless flat.Nodup do
    return .inl (.invalid "duplicate constructor name in an inductive type's ctors")
  unless flat.length == cts.length do
    return .inl (.invalid s!"the inductive block lists {flat.length} constructors \
      and carries {cts.length} constructor records")
  let ctorIx : Std.HashMap Name Nat :=
    (ctorNames.foldl (fun (mi : Std.HashMap Name Nat × Nat) n =>
      (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1
  let ctsA := cts.toArray
  let res ← lForIn (fun tn s => lOrderBlockStep st ctorIx ctsA nPd tn s)
    (tyNames.zip listed) (none, #[])
  match res.1 with
  | some r => return r
  | none =>
  let cts := res.2.toList
  let nested := tys.any (·.numNested != 0)
  let nTypes := tys.length
  let nCtors := cts.length
  let kExpected? := lKExpectedOf tyTypes listed cts
  let res2 ← lForIn (fun r s => lRecStep st tyNames tyTypes nPd nTypes nCtors kExpected? r s)
    (if nested then [] else rcs) (none, ())
  match res2.1 with
  | some r => return r
  | none => return .inr (cts, nPd)

set_option maxHeartbeats 1000000 in
theorem lValidateIndD_eq (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) :
    validateIndD st tys cts rcs = lValidateIndD st tys cts rcs := by
  rw [validateIndD, lValidateIndD]
  simp only [forIn_eq_lForIn, lOrderBlockStep, lOrderStep, lRecStep, lRecIdxStep, lKExpectedOf]
  refine mIteCong rfl ?_
  refine mIteCong ?_ rfl
  refine mBindCong rfl fun tyNames => ?_
  refine mBindCong rfl fun tyTypes => ?_
  refine mBindCong rfl fun listed => ?_
  refine mBindCong rfl fun ctorNames => ?_
  refine mIteCong ?_ rfl
  refine mIteCong ?_ rfl
  refine mBindCong (lForIn_congr ?_ _ _) ?_
  · intro tn s
    refine mBindCong (lForIn_congr (fun n s' => rfl) _ _) ?_
    intro r
    cases hr : r.1 <;> rfl
  · intro res
    cases hres : res.1 with
    | some r => rfl
    | none =>
      refine mBindCong (lForIn_congr ?_ _ _) ?_
      · intro r s
        refine mBindCong rfl fun rn => ?_
        refine mIteCong ?_ rfl
        refine mIteCong ?_ rfl
        refine mIteCong ?_ rfl
        congr 1
        · funext kE
          refine mIteCong ?_ rfl
          congr 1
          funext T
          refine mBindCong (lForIn_congr ?_ _ _) ?_
          · intro tt s'
            refine mIteCong ?_ rfl
            cases htt : tt.2.piSortTeleLen? <;> rfl
          · intro res3
            cases hres3 : res3.1 <;> rfl
        · funext x
          congr 1
          funext T
          refine mBindCong (lForIn_congr ?_ _ _) ?_
          · intro tt s'
            refine mIteCong ?_ rfl
            cases htt : tt.2.piSortTeleLen? <;> rfl
          · intro res3
            cases hres3 : res3.1 <;> rfl
      · intro res2
        cases hres2 : res2.1 <;> rfl

end Mirror

/-! ## The recursor records (`ExportC.lean:412-563`, the `for r in rcs` loop)

Three port functions — `check_rec_indices`, `check_one_rec`,
`check_rec_records` — against `lRecIdxStep`, `lRecStep` and the `lForIn` over
them.  Every early return of those loops is an `.invalid` verdict, so the two
outcome shapes below name only `.invalid`'s *kind*, never its message
(DESIGN.md §3.1). -/

/-- **The outcome of a `Result<(), LineErr>` whose con-leche twin is one of
`validateIndD`'s loops, run to the end.** -/
def LoopOut (o : core.result.Result Unit frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M (Option LVRes × Unit)) : Prop :=
  match o with
  | .Ok _ => x = .ok (none, ())
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict v) =>
    ∃ lv u, x = .ok (some (.inl lv), u) ∧ lVerdictKind lv = absVerdictKind v

/-- **The outcome of a `Result<(), LineErr>` whose con-leche twin is one
*step* of such a loop.** -/
def StepLoopOut (o : core.result.Result Unit frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M (ForInStep (Option LVRes × Unit))) : Prop :=
  match o with
  | .Ok _ => x = .ok (.yield (none, ()))
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict v) =>
    ∃ lv u, x = .ok (.done (some (.inl lv), u)) ∧ lVerdictKind lv = absVerdictKind v

/-- `lForIn` at a cons. -/
private theorem lForIn_cons {α σ : Type}
    (f : α → σ → ConLeche.Frontend.M (ForInStep σ)) (a : α) (l : List α) (s : σ) :
    lForIn f (a :: l) s =
      (f a s >>= fun r => match r with
        | .done s' => pure s'
        | .yield s' => lForIn f l s') := rfl

/-- `lForIn` at nil. -/
private theorem lForIn_nil {α σ : Type}
    (f : α → σ → ConLeche.Frontend.M (ForInStep σ)) (s : σ) :
    lForIn f [] s = pure s := rfl

/-- A `zip`, dropped. -/
private theorem iv_zip_drop {α β : Type} : ∀ (k : Nat) (l₁ : List α) (l₂ : List β),
    (l₁.zip l₂).drop k = (l₁.drop k).zip (l₂.drop k)
  | 0, _, _ => by simp
  | _ + 1, [], _ => by simp
  | _ + 1, _ :: _, [] => by simp
  | m + 1, a :: t₁, b :: t₂ => by
    simp only [List.zip_cons_cons, List.drop_succ_cons]
    exact iv_zip_drop m t₁ t₂

/-- A mapped `Vec`, dropped at an index in range. -/
private theorem iv_drop_map {α β : Type} {v : alloc.vec.Vec α} {i : Nat} (f : α → β)
    (hlt : i < v.val.length) :
    (v.val.map f).drop i = f (v.val[i]'hlt) :: (v.val.map f).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map]

/-- An out-of-range `Vec` read does not return. -/
private theorem iv_index_lt {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length := by
  by_contra hc
  have hg := ExprOps.vec_index_getElem? h
  rw [List.getElem?_eq_none (by omega)] at hg
  simp at hg

/-! ### `lRecIdxStep`, arm by arm -/

section StepArms
open ConLeche ConLeche.Frontend

/-- The name does not match: the step yields. -/
private theorem lRecIdxStep_ne {T rn : ConLeche.Name} {ni nPd : Nat}
    {tt : ConLeche.Name × ConLeche.Expr} (h : tt.1 ≠ T) (s : Option LVRes × Unit) :
    lRecIdxStep T rn ni nPd tt s = pure (.yield (none, ())) := by
  simp only [lRecIdxStep]; rw [if_neg (by simpa using h)]

/-- The telescope is unreadable: the step yields. -/
private theorem lRecIdxStep_unreadable {T rn : ConLeche.Name} {ni nPd : Nat}
    {tt : ConLeche.Name × ConLeche.Expr} (h : tt.2.piSortTeleLen? = none)
    (s : Option LVRes × Unit) :
    lRecIdxStep T rn ni nPd tt s = pure (.yield (none, ())) := by
  simp only [lRecIdxStep, h]
  split <;> rfl

/-- The counts agree: the step yields. -/
private theorem lRecIdxStep_ok {T rn : ConLeche.Name} {ni nPd k : Nat}
    {tt : ConLeche.Name × ConLeche.Expr} (h : tt.2.piSortTeleLen? = some k)
    (hk : nPd + ni = k) (s : Option LVRes × Unit) :
    lRecIdxStep T rn ni nPd tt s = pure (.yield (none, ())) := by
  simp only [lRecIdxStep, h]
  split
  · rw [if_pos (by simpa using hk)]
  · rfl

/-- The counts disagree: the step stops with an `.invalid` verdict. -/
private theorem lRecIdxStep_bad {T rn : ConLeche.Name} {ni nPd k : Nat}
    {tt : ConLeche.Name × ConLeche.Expr} (h1 : tt.1 = T)
    (h : tt.2.piSortTeleLen? = some k) (hk : nPd + ni ≠ k) (s : Option LVRes × Unit) :
    ∃ m, lRecIdxStep T rn ni nPd tt s
      = pure (.done (some (.inl (.invalid m)), ())) := by
  simp only [lRecIdxStep, h]
  rw [if_pos (by simpa using h1), if_neg (by simpa using hk)]
  exact ⟨_, rfl⟩

end StepArms

/-- The index recursion behind `export_c::check_rec_indices`. -/
private theorem check_rec_indices_loop_refines {rn t_pre : name.Name}
    {num_indices n_pd : Std.U64}
    {ty_names : alloc.vec.Vec name.Name} {ty_types : alloc.vec.Vec expr.Expr}
    (hnwf : NamesWF ty_names) (htwf : ExprsWF ty_types) (htp : NameWF t_pre) (N : Nat) :
    ∀ (n i : Std.Usize) (o : core.result.Result Unit frontend.export_c.LineErr),
      ty_names.val.length - i.val = N → n.val = ty_names.val.length →
      frontend.export_c.check_rec_indices_loop rn t_pre num_indices ty_names ty_types
        n_pd n i = ok o →
      LoopOut o (lForIn (fun tt s => lRecIdxStep (absName t_pre) (absName rn)
          num_indices.val n_pd.val tt s)
        (((absNames ty_names).zip (absExprs ty_types)).drop i.val) (none, ())) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n i o hN hn h
    rw [frontend.export_c.check_rec_indices_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < ty_names.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n1, hidx, h⟩ := h
      have hn1v : ty_names.val[i.val]'hltv = n1 := iv_index_val hidx
      have hn1wf : NameWF n1 := by rw [← hn1v]; exact hnwf _ (List.getElem_mem _)
      obtain ⟨b, hb, h⟩ := h
      have hbv : b = decide (absName n1 = absName t_pre) := Name.beq_refines hn1wf htp hb
      split at h
      · -- the names match: read `ty_types` at the same index
        rename_i hbt
        have habs : absName n1 = absName t_pre := by
          have hd : decide (absName n1 = absName t_pre) = true := by rw [← hbv]; exact hbt
          simpa using hd
        simp only [bind_eq_ok_iff] at h
        obtain ⟨e, hidxe, h⟩ := h
        have hltt : i.val < ty_types.val.length := iv_index_lt hidxe
        have hev : ty_types.val[i.val]'hltt = e := iv_index_val hidxe
        have hewf : ExprWF e := by rw [← hev]; exact htwf _ (List.getElem_mem _)
        obtain ⟨oo, hoo, h⟩ := h
        have hooabs : oo.map Std.UScalar.val
            = ConLeche.Expr.piSortTeleLen? (absExpr e) := Env.pi_sort_tele_len_refines hewf hoo
        have hdrop : ((absNames ty_names).zip (absExprs ty_types)).drop i.val
            = (absName n1, absExpr e) ::
              ((absNames ty_names).zip (absExprs ty_types)).drop (i.val + 1) := by
          rw [iv_zip_drop, iv_zip_drop]
          simp only [absNames, absExprs]
          rw [iv_drop_map absName hltv, iv_drop_map absExpr hltt, hn1v, hev]
          simp
        rw [hdrop, lForIn_cons]
        cases oo with
        | none =>
          have hpst : (absExpr e).piSortTeleLen? = none := by
            rw [← hooabs]; simp
          rw [lRecIdxStep_unreadable (T := absName t_pre)
            (rn := absName rn) (ni := num_indices.val) (nPd := n_pd.val)
            (tt := (absName n1, absExpr e)) hpst (none, ())]
          simp only [bind_eq_ok_iff] at h
          obtain ⟨i2, hi2, h⟩ := h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          have hres := ih (ty_names.val.length - i2.val) (by omega) n i2 o rfl hn h
          rw [hi2v] at hres
          simpa using hres
        | some k =>
          have hpst : (absExpr e).piSortTeleLen? = some k.val := by
            rw [← hooabs]; simp
          obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
          have hi1v : i1.val = n_pd.val + num_indices.val := HashMap.uscalar_add_eq hi1
          split at h
          · -- the declared count disagrees: an `.invalid` verdict
            rename_i hne
            have hsum : n_pd.val + num_indices.val ≠ k.val := by
              rw [← hi1v]
              intro hc
              have : (i1 != k) = false := by
                simp only [bne_eq_false_iff_eq]
                exact Std.UScalar.eq_of_val_eq hc
              rw [this] at hne
              exact absurd hne (by simp)
            obtain ⟨m, hm⟩ := lRecIdxStep_bad (T := absName t_pre) (rn := absName rn)
              (ni := num_indices.val) (nPd := n_pd.val) (tt := (absName n1, absExpr e))
              habs hpst hsum (none, ())
            rw [hm]
            simp only [bind_eq_ok_iff] at h
            obtain ⟨sub, -, h⟩ := h
            obtain ⟨msg, -, h⟩ := h
            rw [frontend.export_c.invalid] at h
            simp only [Result.ok.injEq] at h
            rw [← h]
            exact ⟨_, _, rfl, rfl⟩
          · rename_i heq
            have hsum : n_pd.val + num_indices.val = k.val := by
              rw [← hi1v]
              simpa using heq
            rw [lRecIdxStep_ok (T := absName t_pre) (rn := absName rn)
              (ni := num_indices.val) (nPd := n_pd.val) (tt := (absName n1, absExpr e))
              hpst hsum (none, ())]
            simp only [bind_eq_ok_iff] at h
            obtain ⟨i2, hi2, h⟩ := h
            have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
            have hres := ih (ty_names.val.length - i2.val) (by omega) n i2 o rfl hn h
            rw [hi2v] at hres
            simpa using hres
      · -- the names differ: the port steps, and so does con-leche when it can
        rename_i hbf
        have habs : absName n1 ≠ absName t_pre := by
          intro hc
          exact hbf (by rw [hbv, hc]; simp)
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hres := ih (ty_names.val.length - i2.val) (by omega) n i2 o rfl hn h
        rw [hi2v] at hres
        have hzl : ((absNames ty_names).zip (absExprs ty_types)).length
            ≤ ty_types.val.length := by
          simp only [List.length_zip, absExprs, List.length_map]
          exact Nat.min_le_right _ _
        by_cases hltt : i.val < ty_types.val.length
        · have hdrop : ((absNames ty_names).zip (absExprs ty_types)).drop i.val
              = (absName n1, absExpr (ty_types.val[i.val]'hltt)) ::
                ((absNames ty_names).zip (absExprs ty_types)).drop (i.val + 1) := by
            rw [iv_zip_drop, iv_zip_drop]
            simp only [absNames, absExprs]
            rw [iv_drop_map absName hltv, iv_drop_map absExpr hltt, hn1v]
            simp
          rw [hdrop, lForIn_cons]
          rw [lRecIdxStep_ne (T := absName t_pre) (rn := absName rn)
            (ni := num_indices.val) (nPd := n_pd.val)
            (tt := (absName n1, absExpr (ty_types.val[i.val]'hltt))) habs (none, ())]
          simpa using hres
        · have hnil : ((absNames ty_names).zip (absExprs ty_types)).drop i.val = [] :=
            List.drop_eq_nil_of_le (by omega)
          have hnil2 : ((absNames ty_names).zip (absExprs ty_types)).drop (i.val + 1) = [] :=
            List.drop_eq_nil_of_le (by omega)
          rw [hnil]
          rw [hnil2] at hres
          exact hres
    · rename_i hge
      have hle : ty_names.val.length ≤ i.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hzl : ((absNames ty_names).zip (absExprs ty_types)).length
          ≤ ty_names.val.length := by
        simp only [List.length_zip, absNames, List.length_map]
        exact Nat.min_le_left _ _
      have hnil : ((absNames ty_names).zip (absExprs ty_types)).drop i.val = [] :=
        List.drop_eq_nil_of_le (by omega)
      rw [hnil, lForIn_nil]
      rfl

/-- **`export_c::check_rec_indices` refines the `for tt in tyNames.zip tyTypes`
of `validateIndD`** (`ConLeche/Frontend/ExportC.lean:412-563`).  The port walks
`ty_names` by index and reads `ty_types` at the same index only when the name
matches, so a `ty_types` shorter than `ty_names` is a port *failure* exactly
where con-leche's `zip` stops — and nothing is claimed about a failure. -/
theorem check_rec_indices_refines {rn t_pre : name.Name} {num_indices n_pd : Std.U64}
    {ty_names : alloc.vec.Vec name.Name} {ty_types : alloc.vec.Vec expr.Expr}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hnwf : NamesWF ty_names) (htwf : ExprsWF ty_types) (htp : NameWF t_pre)
    (h : frontend.export_c.check_rec_indices rn t_pre num_indices ty_names ty_types n_pd
      = ok o) :
    LoopOut o (lForIn (fun tt s => lRecIdxStep (absName t_pre) (absName rn)
        num_indices.val n_pd.val tt s)
      ((absNames ty_names).zip (absExprs ty_types)) (none, ())) := by
  rw [frontend.export_c.check_rec_indices] at h
  have hres := check_rec_indices_loop_refines hnwf htwf htp _ _ 0#usize o rfl
    (by simp [alloc.vec.Vec.len]) h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hres


/-! ### `check_one_rec` -/

/-- `Except`'s bind at a value. -/
private theorem iv_ok_bind {α β : Type} (a : α) (f : α → ConLeche.Frontend.M β) :
    (Except.ok a : ConLeche.Frontend.M α) >>= f = f a := rfl

/-- `Except`'s bind at an error. -/
private theorem iv_err_bind {α β : Type} (e : String) (f : α → ConLeche.Frontend.M β) :
    (Except.error e : ConLeche.Frontend.M α) >>= f = Except.error e := rfl

/-- An `[u32; N]` literal, as a slice's value.  (`Refine/Frontend/ProjRecR.lean`
keeps the same one-liner `private`; the coordinator should merge them when the
files meet.) -/
private theorem iv_slice_lit_val {k : Std.Usize} {S : Array Std.U32 k} {s : Slice Std.U32}
    (h : lift (Array.to_slice S) = ok s) : s.val = S.val := by
  simp only [lift_eq, Result.ok.injEq] at h
  subst h
  simp [Array.val_to_slice]

/-- A well-formed name whose kind is `Str` has a well-formed prefix and a
well-formed spelling.  (Agent R's caution: `absString` is injective only under
`StrWF`, so the `.str T "rec"` test carries this hypothesis rather than
assuming injectivity.) -/
private theorem iv_namewf_str {hh : Std.U64} {t_pre : name.Name}
    {last : alloc.vec.Vec Std.U32}
    (hwf : NameWF (name.Name.mk (name.NameNode.mk hh (.Str t_pre last)))) :
    NameWF t_pre ∧ StrWF last := by
  cases hwf with
  | anonymous hA =>
    have hv := name_anonymous_inv hA
    simp only [name.Name.mk.injEq, name.NameNode.mk.injEq] at hv
    exact absurd hv.2 (by simp)
  | str hp hs hmk =>
    obtain ⟨hh2, hv⟩ := mk_str_inv hmk
    simp only [name.Name.mk.injEq, name.NameNode.mk.injEq, name.NameKind.Str.injEq] at hv
    obtain ⟨-, hpre, hlast⟩ := hv
    exact ⟨hpre ▸ hp, hlast ▸ hs⟩
  | num hp hmk =>
    obtain ⟨hh2, hv⟩ := mk_num_inv hmk
    simp only [name.Name.mk.injEq, name.NameNode.mk.injEq] at hv
    exact absurd hv.2 (by simp)

/-- **`export_c::check_one_rec` refines one step of `validateIndD`'s recursor
loop** (`ConLeche/Frontend/ExportC.lean:412-563`): the three declared counts,
the K flag, and — at a name spelled `T.rec` — the index count. -/
theorem check_one_rec_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {r : frontend.scan_types.IndRecRec}
    {ty_names : alloc.vec.Vec name.Name} {ty_types : alloc.vec.Vec expr.Expr}
    {n_pd n_types n_ctors : Std.U64} {k_exp : Option Bool}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hnwf : NamesWF ty_names) (htwf : ExprsWF ty_types)
    (h : frontend.export_c.check_one_rec st r ty_names ty_types n_pd n_types n_ctors k_exp
      = ok o) :
    StepLoopOut o (lRecStep lst (absNames ty_names) (absExprs ty_types)
      n_pd.val n_types.val n_ctors.val k_exp (absIndRecRec r) (none, ())) := by
  rw [frontend.export_c.check_one_rec] at h
  obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
  have hst := st_name_refines hrel hwf hr1
  cases r1 with
  | Err e =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    cases e with
    | Msg m =>
      obtain ⟨s0, hs0⟩ := hst
      refine ⟨s0, ?_⟩
      simp only [lRecStep, absIndRecRec, absCVRec, absU64, hs0]
      rw [iv_err_bind]
    | Verdict v => exact hst.elim
  | Ok v =>
    obtain ⟨habs, hvwf⟩ := hst
    obtain ⟨⟨hsh, kv⟩⟩ := v
    simp only [arc_deref_eq, bind_tc_ok] at h
    simp only [lRecStep, absIndRecRec, absCVRec, absU64, habs]
    rw [iv_ok_bind]
    simp only [beq_iff_eq]
    -- the tail: the K flag has been dealt with, the name is all that is left
    have htail : ∀ (kv0 : name.NameKind),
        NameWF (name.Name.mk (name.NameNode.mk hsh kv0)) →
        ∀ (o' : core.result.Result Unit frontend.export_c.LineErr),
        (match kv0 with
         | .Anonymous => ok (core.result.Result.Ok ())
         | .Str t_pre last => do
           let s ← lift (Array.to_slice frontend.export_c.check_one_rec.R)
           let b ← frontend.text.cps_beq last s
           if b = true then
             frontend.export_c.check_rec_indices
               (name.Name.mk (name.NameNode.mk hsh kv0)) t_pre r.num_indices
               ty_names ty_types n_pd
           else ok (core.result.Result.Ok ())
         | .Num _ _ => ok (core.result.Result.Ok ())) = ok o' →
        StepLoopOut o' (match absName (name.Name.mk (name.NameNode.mk hsh kv0)) with
          | .str T "rec" => do
            let res ← lForIn (fun tt s' => lRecIdxStep T
              (absName (name.Name.mk (name.NameNode.mk hsh kv0)))
              r.num_indices.val n_pd.val tt s') ((absNames ty_names).zip
              (absExprs ty_types)) (none, ())
            match res.1 with
            | some rr => pure (.done (some rr, ()))
            | none => pure (.yield (none, ()))
          | _ => pure (.yield (none, ()))) := by
      intro kv0 hkwf o' h'
      simp only [absName, absNameNode]
      cases kv0 with
      | Anonymous =>
        simp only [Result.ok.injEq] at h'
        rw [← h']
        rfl
      | Num p m =>
        simp only [Result.ok.injEq] at h'
        rw [← h']
        rfl
      | Str t_pre last =>
        obtain ⟨htpwf, hlastwf⟩ := iv_namewf_str hkwf
        simp only [bind_eq_ok_iff] at h'
        obtain ⟨sl, hsl, b, hb, h'⟩ := h'
        have hslv : sl.val = [114#u32, 101#u32, 99#u32] := by
          rw [iv_slice_lit_val hsl]; simp [frontend.export_c.check_one_rec.R]
        have hbR : (b = true ↔ absString last = "rec") := by
          rw [cps_beq_str hlastwf (by rw [hslv]; decide) hb, hslv]; rfl
        simp only [absNameKind]
        by_cases hbt : b = true
        · rw [if_pos hbt] at h'
          have hstr : absString last = "rec" := hbR.mp hbt
          have hidx := check_rec_indices_refines (rn := name.Name.mk
            (name.NameNode.mk hsh (.Str t_pre last))) hnwf htwf htpwf h'
          simp only [absName, absNameNode, absNameKind] at hidx ⊢
          rw [hstr] at hidx ⊢
          split
          · rename_i rn0 T0 heq0
            have hT : absName t_pre = T0 := by simpa using heq0
            subst hT
            cases o' with
            | Ok u =>
              simp only [LoopOut] at hidx
              simp only [StepLoopOut]
              rw [hidx, iv_ok_bind]
              rfl
            | Err e =>
              cases e with
              | Msg m =>
                obtain ⟨s0, hs0⟩ := hidx
                exact ⟨s0, by rw [hs0, iv_err_bind]⟩
              | Verdict vv =>
                obtain ⟨lv, u, hu, hk⟩ := hidx
                exact ⟨lv, (), by rw [hu, iv_ok_bind]; rfl, hk⟩
          · rename_i rn0 hcon
            exact absurd rfl (hcon (absName t_pre))
        · rw [if_neg hbt] at h'
          have hne : absString last ≠ "rec" := fun hc => hbt (hbR.mpr hc)
          simp only [Result.ok.injEq] at h'
          rw [← h']
          split
          · rename_i rn0 T0 heq0
            exact absurd (by simpa using heq0 : absName t_pre = T0 ∧ absString last = "rec").2 hne
          · rfl
    by_cases hc1 : (r.num_params != n_pd) = true
    · rw [if_pos hc1] at h
      have hnev : ¬ (r.num_params.val = n_pd.val) := by simpa using hc1
      rw [if_neg hnev]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨m, -, h⟩ := h
      rw [frontend.export_c.invalid] at h
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact ⟨_, _, rfl, rfl⟩
    · rw [if_neg hc1] at h
      have heq1v : r.num_params.val = n_pd.val := by simpa using hc1
      rw [if_pos heq1v]
      by_cases hc2 : (r.num_motives != n_types) = true
      · rw [if_pos hc2] at h
        have hnev : ¬ (r.num_motives.val = n_types.val) := by simpa using hc2
        rw [if_neg hnev]
        simp only [bind_eq_ok_iff] at h
        obtain ⟨m, -, h⟩ := h
        rw [frontend.export_c.invalid] at h
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact ⟨_, _, rfl, rfl⟩
      · rw [if_neg hc2] at h
        have heq2v : r.num_motives.val = n_types.val := by simpa using hc2
        rw [if_pos heq2v]
        by_cases hc3 : (r.num_minors != n_ctors) = true
        · rw [if_pos hc3] at h
          have hnev : ¬ (r.num_minors.val = n_ctors.val) := by simpa using hc3
          rw [if_neg hnev]
          simp only [bind_eq_ok_iff] at h
          obtain ⟨m, -, h⟩ := h
          rw [frontend.export_c.invalid] at h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ⟨_, _, rfl, rfl⟩
        · rw [if_neg hc3] at h
          have heq3v : r.num_minors.val = n_ctors.val := by simpa using hc3
          rw [if_pos heq3v]
          cases k_exp with
          | none =>
            simp only [] at h ⊢
            exact htail kv hvwf o h
          | some k_e =>
            simp only [] at h ⊢
            by_cases hc4 : (r.k != k_e) = true
            · rw [if_pos hc4] at h
              have hnev : ¬ (r.k = k_e) := by simpa using hc4
              rw [if_neg hnev]
              simp only [bind_eq_ok_iff] at h
              obtain ⟨m, -, h⟩ := h
              rw [frontend.export_c.invalid] at h
              simp only [Result.ok.injEq] at h
              rw [← h]
              exact ⟨_, _, rfl, rfl⟩
            · rw [if_neg hc4] at h
              have heqv : r.k = k_e := by simpa using hc4
              rw [if_pos heqv]
              exact htail kv hvwf o h


/-! ### `check_rec_records` -/

/-- The index recursion behind `export_c::check_rec_records`. -/
private theorem check_rec_records_loop_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {ty_names : alloc.vec.Vec name.Name} {ty_types : alloc.vec.Vec expr.Expr}
    {n_pd n_types n_ctors : Std.U64} {k_exp : Option Bool}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hnwf : NamesWF ty_names) (htwf : ExprsWF ty_types) (N : Nat) :
    ∀ (n i : Std.Usize) (o : core.result.Result Unit frontend.export_c.LineErr),
      rcs.val.length - i.val = N → n.val = rcs.val.length →
      frontend.export_c.check_rec_records_loop st rcs ty_names ty_types n_pd n_types
        n_ctors k_exp n i = ok o →
      LoopOut o (lForIn (fun r s => lRecStep lst (absNames ty_names) (absExprs ty_types)
          n_pd.val n_types.val n_ctors.val k_exp r s)
        ((absIndRecRecs rcs).drop i.val) (none, ())) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n i o hN hn h
    rw [frontend.export_c.check_rec_records_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < rcs.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨irr, hidx, h⟩ := h
      have hirrv : rcs.val[i.val]'hltv = irr := iv_index_val hidx
      obtain ⟨r1, hr1, h⟩ := h
      have hone := check_one_rec_refines hrel hwf hnwf htwf hr1
      have hdrop : (absIndRecRecs rcs).drop i.val
          = absIndRecRec irr :: (absIndRecRecs rcs).drop (i.val + 1) := by
        simp only [absIndRecRecs]
        rw [iv_drop_map absIndRecRec hltv, hirrv]
      rw [hdrop, lForIn_cons]
      cases r1 with
      | Ok u =>
        simp only [StepLoopOut] at hone
        rw [hone, iv_ok_bind]
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hres := ih (rcs.val.length - i2.val) (by omega) n i2 o rfl hn h
        rw [hi2v] at hres
        exact hres
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        cases e with
        | Msg m =>
          obtain ⟨s0, hs0⟩ := hone
          exact ⟨s0, by rw [hs0, iv_err_bind]⟩
        | Verdict vv =>
          obtain ⟨lv, u, hu, hk⟩ := hone
          exact ⟨lv, u, by rw [hu, iv_ok_bind]; rfl, hk⟩
    · rename_i hge
      have hle : rcs.val.length ≤ i.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndRecRecs rcs).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndRecRecs, List.length_map]
        omega
      rw [hnil, lForIn_nil]
      rfl

/-- **`export_c::check_rec_records` refines the `for r in rcs` of
`validateIndD`** (`ConLeche/Frontend/ExportC.lean:412-563`).  The nested-block
guard is `validate_ind_d`'s, not this function's: con-leche iterates over
`if nested then [] else rcs`, and the port skips the call. -/
theorem check_rec_records_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {ty_names : alloc.vec.Vec name.Name} {ty_types : alloc.vec.Vec expr.Expr}
    {n_pd n_types n_ctors : Std.U64} {k_exp : Option Bool}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hnwf : NamesWF ty_names) (htwf : ExprsWF ty_types)
    (h : frontend.export_c.check_rec_records st rcs ty_names ty_types n_pd n_types
      n_ctors k_exp = ok o) :
    LoopOut o (lForIn (fun r s => lRecStep lst (absNames ty_names) (absExprs ty_types)
        n_pd.val n_types.val n_ctors.val k_exp r s) (absIndRecRecs rcs) (none, ())) := by
  rw [frontend.export_c.check_rec_records] at h
  have hres := check_rec_records_loop_refines hrel hwf hnwf htwf _ _ 0#usize o rfl
    (by simp [alloc.vec.Vec.len]) h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hres


/-! ### `k_expected_of` (`ExportC.lean:412-563`, official's `is_K_target`) -/

section KExp
open ConLeche ConLeche.Frontend

/-- Anything but "one type, one listed constructor, one constructor record"
is not K-like. -/
private theorem lKExpectedOf_false {tt : List Expr} {ls : List (List Name)}
    {cs : List IndCtorRec}
    (h : ¬ (∃ ty x c, tt = [ty] ∧ ls = [[x]] ∧ cs = [c])) :
    lKExpectedOf tt ls cs = some false := by
  unfold lKExpectedOf
  split
  · rename_i ty x c
    exact absurd ⟨ty, x, c, rfl, rfl, rfl⟩ h
  · rfl

/-- The single former's type ends in a sort: the flag is readable. -/
private theorem lKExpectedOf_sort {ty : Expr} {s : Level} {x : Name} {c : IndCtorRec}
    (h : ty.piResult = .sort s) :
    lKExpectedOf [ty] [[x]] [c]
      = some (c.numFields == 0 && Level.isEquiv s .zero == some true) := by
  simp only [lKExpectedOf, h]

/-- The single former's type does not end in a sort: the flag is left to the
install. -/
private theorem lKExpectedOf_nonsort {ty : Expr} {x : Name} {c : IndCtorRec}
    (h : ∀ s, ty.piResult ≠ .sort s) : lKExpectedOf [ty] [[x]] [c] = none := by
  have key : ∀ (e : Expr), ty.piResult = e → (∀ s, e ≠ .sort s) →
      lKExpectedOf [ty] [[x]] [c] = none := by
    intro e he hne
    cases e <;> first | (exact absurd rfl (hne _)) | simp [lKExpectedOf, he]
  exact key _ rfl h

end KExp

/-- **`export_c::k_expected_of` refines the `kExpected?` of `validateIndD`**
(`ConLeche/Frontend/ExportC.lean:412-563`): official's `is_K_target` — the
block is a `Prop`, has ONE type with ONE constructor, and that constructor
takes only the parameters. -/
theorem k_expected_of_refines {ty_types : alloc.vec.Vec expr.Expr}
    {listed : alloc.vec.Vec (alloc.vec.Vec name.Name)}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec} {o : Option Bool}
    (htwf : ExprsWF ty_types)
    (h : frontend.export_c.k_expected_of ty_types listed cts = ok o) :
    o = lKExpectedOf (absExprs ty_types) (absNamess listed) (absIndCtorRecs cts) := by
  rw [frontend.export_c.k_expected_of] at h
  by_cases h1 : (alloc.vec.Vec.len ty_types != 1#usize) = true
  · rw [if_pos h1] at h
    simp only [Result.ok.injEq] at h
    rw [← h, lKExpectedOf_false]
    rintro ⟨ty, x, c, hty, -, -⟩
    have : (absExprs ty_types).length = 1 := by rw [hty]; rfl
    simp only [absExprs, List.length_map] at this
    simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq] at h1
    exact h1 (by scalar_tac)
  · rw [if_neg h1] at h
    have hlt : ty_types.val.length = 1 := by
      simp only [alloc.vec.Vec.len] at h1
      scalar_tac
    by_cases h2 : (alloc.vec.Vec.len listed != 1#usize) = true
    · rw [if_pos h2] at h
      simp only [Result.ok.injEq] at h
      rw [← h, lKExpectedOf_false]
      rintro ⟨ty, x, c, -, hls, -⟩
      have : (absNamess listed).length = 1 := by rw [hls]; rfl
      simp only [absNamess, List.length_map] at this
      simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq] at h2
      exact h2 (by scalar_tac)
    · rw [if_neg h2] at h
      have hll : listed.val.length = 1 := by
        simp only [alloc.vec.Vec.len] at h2
        scalar_tac
      by_cases h3 : (alloc.vec.Vec.len cts != 1#usize) = true
      · rw [if_pos h3] at h
        simp only [Result.ok.injEq] at h
        rw [← h, lKExpectedOf_false]
        rintro ⟨ty, x, c, -, -, hcs⟩
        have : (absIndCtorRecs cts).length = 1 := by rw [hcs]; rfl
        simp only [absIndCtorRecs, List.length_map] at this
        simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq] at h3
        exact h3 (by scalar_tac)
      · rw [if_neg h3] at h
        have hcl : cts.val.length = 1 := by
          simp only [alloc.vec.Vec.len] at h3
          scalar_tac
        simp only [bind_eq_ok_iff] at h
        obtain ⟨v, hv, h⟩ := h
        have hv0 : listed.val[0]'(by omega) = v := iv_index_val hv
        by_cases h4 : (alloc.vec.Vec.len v != 1#usize) = true
        · rw [if_pos h4] at h
          simp only [Result.ok.injEq] at h
          rw [← h, lKExpectedOf_false]
          rintro ⟨ty, x, c, -, hls, -⟩
          have hhead : (absNamess listed)[0]? = some [x] := by rw [hls]; rfl
          simp only [absNamess, List.getElem?_map,
            List.getElem?_eq_getElem (show 0 < listed.val.length by omega), hv0] at hhead
          simp only [Option.map_some, Option.some.injEq] at hhead
          have : (absNames v).length = 1 := by rw [hhead]; rfl
          simp only [absNames, List.length_map] at this
          simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq] at h4
          exact h4 (by scalar_tac)
        · rw [if_neg h4] at h
          have hvl : v.val.length = 1 := by
            simp only [alloc.vec.Vec.len] at h4
            scalar_tac
          -- the shapes
          obtain ⟨ty0, hty0⟩ := List.length_eq_one_iff.mp hlt
          obtain ⟨x0, hx0⟩ := List.length_eq_one_iff.mp hvl
          obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hcl
          obtain ⟨l0, hl0⟩ := List.length_eq_one_iff.mp hll
          have hl0v : l0 = v := by
            have h0 : listed.val[0]? = some v := by
              rw [List.getElem?_eq_getElem (show 0 < listed.val.length by omega), hv0]
            rw [hl0] at h0
            simpa using h0
          subst hl0v
          have habsT : absExprs ty_types = [absExpr ty0] := by
            simp [absExprs, hty0]
          have habsL : absNamess listed = [[absName x0]] := by
            simp [absNamess, hl0, absNames, hx0]
          have habsC : absIndCtorRecs cts = [absIndCtorRec c0] := by
            simp [absIndCtorRecs, hc0]
          rw [habsT, habsL, habsC]
          simp only [bind_eq_ok_iff] at h
          obtain ⟨e, he, h⟩ := h
          have hev : ty_types.val[0]'(by omega) = e := iv_index_val he
          have hewf : ExprWF e := by rw [← hev]; exact htwf _ (List.getElem_mem _)
          have hety : e = ty0 := by
            have h0 : ty_types.val[0]? = some e := by
              rw [List.getElem?_eq_getElem (show 0 < ty_types.val.length by omega), hev]
            rw [hty0] at h0
            have h1 : ty0 = e := by simpa using h0
            exact h1.symm
          obtain ⟨res, hres, h⟩ := h
          obtain ⟨habsr, hrwf⟩ := ExprOps.pi_result_refines hewf hres
          rw [hety] at habsr
          obtain ⟨⟨d, k⟩⟩ := res
          simp only [arc_deref_eq] at h
          obtain ⟨en, hen, h⟩ := h
          have henv : en = (expr.Expr.mk (expr.ExprNode.mk d k))._0 :=
            (Result.ok_injective hen).symm
          subst henv
          simp only [ExprOps.node_kind] at h
          cases k with
          | «Sort» u =>
            have huwf : LevelWF u := CoreK.wf_sort_inv hrwf rfl
            try simp only [absExpr_mk, absExprKind] at habsr
            simp only [bind_eq_ok_iff] at h
            obtain ⟨z, hz, oo, hoo, h⟩ := h
            have hzwf : LevelWF z := LevelWF.zero hz
            have heq := Level.is_equiv_refines huwf hzwf hoo
            rw [Level.zero_refines hz] at heq
            rw [lKExpectedOf_sort habsr.symm]
            obtain ⟨ip, hip, icr, hicr, h⟩ := h
            have hicrv : cts.val[0]'(by omega) = icr := iv_index_val hicr
            have hicrc : icr = c0 := by
              have h0 : cts.val[0]? = some icr := by
                rw [List.getElem?_eq_getElem (show 0 < cts.val.length by omega), hicrv]
              rw [hc0] at h0
              have h1 : c0 = icr := by simpa using h0
              exact h1.symm
            rw [heq]
            cases oo with
            | none =>
              have hipv : ip = false := by simpa using hip.symm
              subst hipv
              by_cases hnf : icr.num_fields = 0#u64
              · rw [if_pos hnf] at h
                simp only [Result.ok.injEq] at h
                rw [← h, ← hicrc]
                simp [absIndCtorRec, absU64]
              · rw [if_neg hnf] at h
                simp only [Result.ok.injEq] at h
                rw [← h, ← hicrc]
                simp [absIndCtorRec, absU64]
            | some bo =>
              have hipv : ip = bo := by simpa using hip.symm
              subst hipv
              by_cases hnf : icr.num_fields = 0#u64
              · rw [if_pos hnf] at h
                simp only [Result.ok.injEq] at h
                rw [← h, ← hicrc]
                simp [absIndCtorRec, absU64, hnf]
              · rw [if_neg hnf] at h
                simp only [Result.ok.injEq] at h
                rw [← h, ← hicrc]
                have hnf' : ¬ (icr.num_fields.val = 0) := fun hc =>
                  hnf (Std.UScalar.eq_of_val_eq hc)
                simp [absIndCtorRec, absU64, hnf']
          | _ =>
            simp only [Result.ok.injEq] at h
            rw [← h, lKExpectedOf_nonsort]
            intro s hc
            rw [← habsr] at hc
            simp only [absExpr_mk, absExprKind] at hc
            exact ConLeche.Expr.noConfusion hc


/-! ## The reordering (`ExportC.lean:412-563`, `types[].ctors` in type order) -/

/-- **The outcome of one step of the reordering loop**: the constructor record
is appended and `j` advances, or the step stops with an `.invalid` verdict, or
a state read throws. -/
def OrderStepOut (o : core.result.Result Unit frontend.export_c.LineErr)
    (c : ConLeche.Frontend.IndCtorRec) (ordered : Array ConLeche.Frontend.IndCtorRec)
    (j : Nat)
    (x : ConLeche.Frontend.M (ForInStep (Option LVRes ×
      Array ConLeche.Frontend.IndCtorRec × Nat))) : Prop :=
  match o with
  | .Ok _ => x = .ok (.yield (none, ordered.push c, j + 1))
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict v) =>
    ∃ lv w, x = .ok (.done (some (.inl lv), w)) ∧ lVerdictKind lv = absVerdictKind v

/-- **`export_c::check_one_ctor` refines the checks of `validateIndD`'s inner
reordering step** (`ConLeche/Frontend/ExportC.lean:412-563`): the redundant
`cidx` and `induct` fields and the declared `numFields`.  It is stated at the
step, past the two lookups, because that is where con-leche writes it. -/
theorem check_one_ctor_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {n t : name.Name}
    {c : frontend.scan_types.IndCtorRec} {j n_pd : Std.U64}
    {ctorIx : Std.HashMap ConLeche.Name Nat}
    {ctsA : Array ConLeche.Frontend.IndCtorRec} {k : Nat}
    {ordered : Array ConLeche.Frontend.IndCtorRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (ht : NameWF t)
    (hk : ctorIx[absName n]? = some k) (hck : ctsA[k]? = some (absIndCtorRec c))
    (h : frontend.export_c.check_one_ctor st n t c j n_pd = ok o) :
    OrderStepOut o (absIndCtorRec c) ordered j.val
      (lOrderStep lst (absName t) ctorIx ctsA n_pd.val (absName n)
        (none, ordered, j.val)) := by
  rw [frontend.export_c.check_one_ctor] at h
  simp only [lOrderStep, hk, hck]
  -- the `numFields` check, shared by the four arms of the two optional fields
  have hfields : ∀ (o' : core.result.Result Unit frontend.export_c.LineErr),
      (do let r ← frontend.export_c.get_decl_d st c.cv.ty
          match r with
          | .Ok v => do
            let b ← frontend.export_c.ind_pi_tele_len v
            let i ← n_pd + c.num_fields
            if i != b then do
              let v1 ← frontend.export_c.fields_error n c.num_fields n_pd b
              frontend.export_c.invalid Unit v1
            else ok (core.result.Result.Ok ())
          | .Err e => ok (core.result.Result.Err e)) = ok o' →
      OrderStepOut o' (absIndCtorRec c) ordered j.val
        (do let cty ← ConLeche.Frontend.getDeclD lst (absIndCtorRec c).cv.type
            if n_pd.val + (absIndCtorRec c).numFields
                == ConLeche.Frontend.indPiTeleLen cty then
              pure (.yield (none, ordered.push (absIndCtorRec c), j.val + 1))
            else pure (.done (some (.inl (.invalid
              s!"constructor {absName n} declares {(absIndCtorRec c).numFields} fields at \
                {n_pd.val} parameters; its type has \
                {ConLeche.Frontend.indPiTeleLen cty} binders")), ordered, j.val))) := by
    intro o' h'
    obtain ⟨r, hr, h'⟩ := bind_eq_ok_iff.mp h'
    have hget := get_decl_d_refines hrel hwf hr
    cases r with
    | Err e =>
      simp only [Result.ok.injEq] at h'
      rw [← h']
      cases e with
      | Msg m =>
        obtain ⟨s0, hs0⟩ := hget
        exact ⟨s0, by simp only [absIndCtorRec, absCVRec, absU64, hs0]; rw [iv_err_bind]⟩
      | Verdict vv => exact hget.elim
    | Ok v =>
      obtain ⟨habs, hvwf⟩ := hget
      simp only [absIndCtorRec, absCVRec, absU64, habs]
      rw [iv_ok_bind]
      simp only [beq_iff_eq]
      obtain ⟨b, hb, h'⟩ := bind_eq_ok_iff.mp h'
      have hbv : b.val = ConLeche.Frontend.indPiTeleLen (absExpr v) :=
        ind_pi_tele_len_refines hvwf hb
      obtain ⟨i1, hi1, h'⟩ := bind_eq_ok_iff.mp h'
      have hi1v : i1.val = n_pd.val + c.num_fields.val := HashMap.uscalar_add_eq hi1
      by_cases hne : (i1 != b) = true
      · rw [if_pos hne] at h'
        have hnev : n_pd.val + c.num_fields.val ≠ ConLeche.Frontend.indPiTeleLen (absExpr v) := by
          rw [← hi1v, ← hbv]
          simpa using hne
        rw [if_neg hnev]
        obtain ⟨m, -, h'⟩ := bind_eq_ok_iff.mp h'
        rw [frontend.export_c.invalid] at h'
        simp only [Result.ok.injEq] at h'
        rw [← h']
        exact ⟨_, _, rfl, rfl⟩
      · rw [if_neg hne] at h'
        have heqv : n_pd.val + c.num_fields.val = ConLeche.Frontend.indPiTeleLen (absExpr v) := by
          rw [← hi1v, ← hbv]
          simpa using hne
        rw [if_pos heqv]
        simp only [Result.ok.injEq] at h'
        rw [← h']
        rfl
  -- the `induct` check, shared by the two arms of `cidx`
  have hinduct : ∀ (o' : core.result.Result Unit frontend.export_c.LineErr),
      (match c.induct with
       | none => do
         let r ← frontend.export_c.get_decl_d st c.cv.ty
         match r with
         | .Ok v => do
           let b ← frontend.export_c.ind_pi_tele_len v
           let i ← n_pd + c.num_fields
           if i != b then do
             let v1 ← frontend.export_c.fields_error n c.num_fields n_pd b
             frontend.export_c.invalid Unit v1
           else ok (core.result.Result.Ok ())
         | .Err e => ok (core.result.Result.Err e)
       | some iw => do
         let r ← frontend.export_c.st_name st iw
         match r with
         | .Ok v => do
           let b ← kernel.name.beq v t
           if b then do
             let r1 ← frontend.export_c.get_decl_d st c.cv.ty
             match r1 with
             | .Ok v1 => do
               let b1 ← frontend.export_c.ind_pi_tele_len v1
               let i ← n_pd + c.num_fields
               if i != b1 then do
                 let v2 ← frontend.export_c.fields_error n c.num_fields n_pd b1
                 frontend.export_c.invalid Unit v2
               else ok (core.result.Result.Ok ())
             | .Err e => ok (core.result.Result.Err e)
           else do
             let v1 ← frontend.export_c.induct_error n v t
             frontend.export_c.invalid Unit v1
         | .Err e => ok (core.result.Result.Err e)) = ok o' →
      OrderStepOut o' (absIndCtorRec c) ordered j.val
        (match (absIndCtorRec c).induct with
         | some iw => do
           let iwn ← lst.name iw
           if iwn == absName t then
             (do let cty ← ConLeche.Frontend.getDeclD lst (absIndCtorRec c).cv.type
                 if n_pd.val + (absIndCtorRec c).numFields
                     == ConLeche.Frontend.indPiTeleLen cty then
                   pure (.yield (none, ordered.push (absIndCtorRec c), j.val + 1))
                 else pure (.done (some (.inl (.invalid
                   s!"constructor {absName n} declares {(absIndCtorRec c).numFields} fields at \
                     {n_pd.val} parameters; its type has \
                     {ConLeche.Frontend.indPiTeleLen cty} binders")), ordered, j.val)))
           else pure (.done (some (.inl (.invalid
             s!"constructor {absName n} declares induct {iwn}; it is \
               a constructor of {absName t}")), ordered, j.val))
         | _ =>
           (do let cty ← ConLeche.Frontend.getDeclD lst (absIndCtorRec c).cv.type
               if n_pd.val + (absIndCtorRec c).numFields
                   == ConLeche.Frontend.indPiTeleLen cty then
                 pure (.yield (none, ordered.push (absIndCtorRec c), j.val + 1))
               else pure (.done (some (.inl (.invalid
                 s!"constructor {absName n} declares {(absIndCtorRec c).numFields} fields at \
                   {n_pd.val} parameters; its type has \
                   {ConLeche.Frontend.indPiTeleLen cty} binders")), ordered, j.val)))) := by
    intro o' h'
    rw [show (absIndCtorRec c).induct = c.induct.map absU64 from rfl]
    cases hiw : c.induct with
    | none =>
      rw [hiw] at h'
      simp only [] at h'
      simp only [Option.map_none]
      exact hfields o' h'
    | some iw =>
      rw [hiw] at h'
      simp only [] at h'
      simp only [Option.map_some, absU64]
      obtain ⟨r, hr, h'⟩ := bind_eq_ok_iff.mp h'
      have hst := st_name_refines hrel hwf hr
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h'
        rw [← h']
        cases e with
        | Msg m =>
          obtain ⟨s0, hs0⟩ := hst
          exact ⟨s0, by rw [hs0, iv_err_bind]⟩
        | Verdict vv => exact hst.elim
      | Ok v =>
        obtain ⟨habs, hvwf⟩ := hst
        rw [habs, iv_ok_bind]
        obtain ⟨b, hb, h'⟩ := bind_eq_ok_iff.mp h'
        have hbv : b = decide (absName v = absName t) := Name.beq_refines hvwf ht hb
        by_cases hbt : b = true
        · rw [if_pos hbt] at h'
          have habst : absName v = absName t := by
            have hd : decide (absName v = absName t) = true := by rw [← hbv]; exact hbt
            simpa using hd
          rw [if_pos (by simpa using habst)]
          exact hfields o' h'
        · rw [if_neg hbt] at h'
          have habst : absName v ≠ absName t := by
            intro hc
            exact hbt (by rw [hbv, hc]; simp)
          rw [if_neg (by simpa using habst)]
          obtain ⟨m, -, h'⟩ := bind_eq_ok_iff.mp h'
          rw [frontend.export_c.invalid] at h'
          simp only [Result.ok.injEq] at h'
          rw [← h']
          exact ⟨_, _, rfl, rfl⟩
  -- the `cidx` check
  rw [show (absIndCtorRec c).cidx = c.cidx.map absU64 from rfl]
  cases hci : c.cidx with
  | none =>
    rw [hci] at h
    simp only [] at h
    simp only [Option.map_none]
    exact hinduct o h
  | some ci =>
    rw [hci] at h
    simp only [] at h
    simp only [Option.map_some, absU64]
    by_cases hne : (ci != j) = true
    · rw [if_pos hne] at h
      have hnev : ¬ (ci.val = j.val) := by simpa using hne
      rw [if_neg (by simpa using hnev)]
      obtain ⟨m, -, h⟩ := bind_eq_ok_iff.mp h
      rw [frontend.export_c.invalid] at h
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact ⟨_, _, rfl, rfl⟩
    · rw [if_neg hne] at h
      have heqv : ci.val = j.val := by simpa using hne
      rw [if_pos (by simpa using heqv)]
      exact hinduct o h


/-! ### `order_type_ctors` and `order_block_ctors` -/

/-- **The outcome of `export_c::order_type_ctors`**: one type former's
constructors, appended to the accumulator in the order its record lists
them. -/
def OrderOut (o : core.result.Result (alloc.vec.Vec frontend.scan_types.IndCtorRec)
      frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M (Option LVRes ×
      Array ConLeche.Frontend.IndCtorRec × Nat)) : Prop :=
  match o with
  | .Ok v => ∃ j, x = .ok (none, (absIndCtorRecs v).toArray, j)
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict vv) =>
    ∃ lv w, x = .ok (some (.inl lv), w) ∧ lVerdictKind lv = absVerdictKind vv

/-- **The outcome of `export_c::order_block_ctors`**: the whole block's
constructors, in the block's own order. -/
def BlockOut (o : core.result.Result (alloc.vec.Vec frontend.scan_types.IndCtorRec)
      frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M (Option LVRes × Array ConLeche.Frontend.IndCtorRec)) : Prop :=
  match o with
  | .Ok v => x = .ok (none, (absIndCtorRecs v).toArray)
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict vv) =>
    ∃ lv w, x = .ok (some (.inl lv), w) ∧ lVerdictKind lv = absVerdictKind vv

/-- A push, on the abstracted `Vec<IndCtorRec>` seen as con-leche's `Array`. -/
private theorem iv_absIndCtorRecs_push {out out1 : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {c : frontend.scan_types.IndCtorRec} (h : alloc.vec.Vec.push out c = ok out1) :
    (absIndCtorRecs out1).toArray = (absIndCtorRecs out).toArray.push (absIndCtorRec c) := by
  rw [absIndCtorRecs, vec_push_val h]
  simp [absIndCtorRecs]

/-- The index recursion behind `export_c::order_type_ctors`. -/
private theorem order_type_ctors_loop_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {t : name.Name}
    {ns : alloc.vec.Vec name.Name} {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {ctor_ix : ron.hashmap.HashMap name.Name Std.U64} {n_pd : Std.U64}
    {s : Std.HashMap ConLeche.Name Nat}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (ht : NameWF t) (hnswf : NamesWF ns)
    (hinv : HashMap.Inv State.hName ctor_ix) (hkeys : HashMap.KeysOk NameWF ctor_ix)
    (hrelm : HashMap.RelOn NameWF ctor_ix s absName (fun u => u.val))
    (hbound : ∀ (nn : ConLeche.Name) (v : Nat), s[nn]? = some v → v ≤ Std.Usize.max) (N : Nat) :
    ∀ (out : alloc.vec.Vec frontend.scan_types.IndCtorRec) (n : Std.Usize) (j : Std.U64)
      (i : Std.Usize) (o : core.result.Result (alloc.vec.Vec frontend.scan_types.IndCtorRec)
        frontend.export_c.LineErr),
      ns.val.length - i.val = N → n.val = ns.val.length →
      frontend.export_c.order_type_ctors_loop st t ns cts ctor_ix n_pd out n j i = ok o →
      OrderOut o (lForIn (fun nm s' => lOrderStep lst (absName t) s
          (absIndCtorRecs cts).toArray n_pd.val nm s')
        ((absNames ns).drop i.val) (none, (absIndCtorRecs out).toArray, j.val)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro out n j i o hN hn h
    rw [frontend.export_c.order_type_ctors_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < ns.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨nm, hidx, h⟩ := h
      have hnmv : ns.val[i.val]'hltv = nm := iv_index_val hidx
      have hnmwf : NameWF nm := by rw [← hnmv]; exact hnswf _ (List.getElem_mem _)
      have hdrop : (absNames ns).drop i.val
          = absName nm :: (absNames ns).drop (i.val + 1) := by
        simp only [absNames]
        rw [iv_drop_map absName hltv, hnmv]
      rw [hdrop, lForIn_cons]
      obtain ⟨o1, ho1, h⟩ := h
      have hget : o1.map (fun u : Std.U64 => u.val) = s[absName nm]? :=
        HashMap.Rel_get_wf State.nameEq2Fwd hinv hkeys hrelm hnmwf ho1
      cases o1 with
      | none =>
        have hs : s[absName nm]? = none := by rw [← hget]; rfl
        simp only [lOrderStep, hs]
        obtain ⟨m, -, h⟩ := bind_eq_ok_iff.mp h
        rw [frontend.export_c.invalid] at h
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact ⟨_, _, rfl, rfl⟩
      | some k =>
        have hs : s[absName nm]? = some k.val := by rw [← hget]; rfl
        obtain ⟨k1, hk1, h⟩ := bind_eq_ok_iff.mp h
        have hk1v : k1.val = k.val := by
          rw [lift_eq, Result.ok.injEq] at hk1
          rw [← hk1]
          exact ExprOps.u64_cast_usize_val (hbound _ _ hs)
        simp only [lOrderStep, hs]
        by_cases hge : k1 ≥ alloc.vec.Vec.len cts
        · rw [if_pos hge] at h
          have hgev : cts.val.length ≤ k.val := by
            rw [← hk1v]
            simpa [alloc.vec.Vec.len] using hge
          have hnone : ((absIndCtorRecs cts).toArray)[k.val]? = none := by
            rw [List.getElem?_toArray]
            refine List.getElem?_eq_none ?_
            simp only [absIndCtorRecs, List.length_map]
            exact hgev
          simp only [hnone]
          obtain ⟨m, -, h⟩ := bind_eq_ok_iff.mp h
          rw [frontend.export_c.invalid] at h
          simp only [Result.ok.injEq] at h
          rw [← h]
          exact ⟨_, _, rfl, rfl⟩
        · rw [if_neg hge] at h
          have hltc : k.val < cts.val.length := by
            rw [← hk1v]
            simpa [alloc.vec.Vec.len] using hge
          obtain ⟨icr, hicr, h⟩ := bind_eq_ok_iff.mp h
          have hicrv : cts.val[k1.val]'(by omega) = icr := iv_index_val hicr
          have hsome : ((absIndCtorRecs cts).toArray)[k.val]? = some (absIndCtorRec icr) := by
            rw [List.getElem?_toArray]
            simp only [absIndCtorRecs]
            rw [List.getElem?_map, List.getElem?_eq_getElem hltc]
            rw [show cts.val[k.val]'hltc = icr by rw [← hicrv]; congr 1; omega]
            rfl
          simp only [hsome]
          obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
          have hone := check_one_ctor_refines (ctorIx := s)
            (ctsA := (absIndCtorRecs cts).toArray) (ordered := (absIndCtorRecs out).toArray)
            hrel hwf ht hs hsome hr
          simp only [lOrderStep, hs, hsome] at hone
          cases r with
          | Ok u =>
            simp only [OrderStepOut] at hone
            rw [hone, iv_ok_bind]
            simp only [bind_eq_ok_iff] at h
            obtain ⟨icr1, hdup, out1, hpush, j1, hj1, i2, hi2, h⟩ := h
            have hicr1 : icr1 = icr := ind_ctor_rec_dup_refines hdup
            rw [hicr1] at hpush
            have hj1v : j1.val = j.val + 1 := HashMap.uscalar_add_eq hj1
            have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
            have hres := ih (ns.val.length - i2.val) (by omega) out1 n j1 i2 o rfl hn h
            rw [hi2v, hj1v, iv_absIndCtorRecs_push hpush] at hres
            exact hres
          | Err e =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            cases e with
            | Msg m =>
              obtain ⟨s0, hs0⟩ := hone
              exact ⟨s0, by rw [hs0, iv_err_bind]⟩
            | Verdict vv =>
              obtain ⟨lv, w, hu, hkd⟩ := hone
              exact ⟨lv, w, by rw [hu, iv_ok_bind]; rfl, hkd⟩
    · rename_i hge
      have hle : ns.val.length ≤ i.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absNames ns).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absNames, List.length_map]
        omega
      rw [hnil, lForIn_nil]
      exact ⟨j.val, rfl⟩

/-- **`export_c::order_type_ctors` refines the inner `for n in ns` of
`validateIndD`'s reordering** (`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem order_type_ctors_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {t : name.Name}
    {ns : alloc.vec.Vec name.Name} {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {ctor_ix : ron.hashmap.HashMap name.Name Std.U64} {n_pd : Std.U64}
    {s : Std.HashMap ConLeche.Name Nat}
    {out : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {o : core.result.Result (alloc.vec.Vec frontend.scan_types.IndCtorRec)
      frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st) (ht : NameWF t) (hnswf : NamesWF ns)
    (hinv : HashMap.Inv State.hName ctor_ix) (hkeys : HashMap.KeysOk NameWF ctor_ix)
    (hrelm : HashMap.RelOn NameWF ctor_ix s absName (fun u => u.val))
    (hbound : ∀ (nn : ConLeche.Name) (v : Nat), s[nn]? = some v → v ≤ Std.Usize.max)
    (h : frontend.export_c.order_type_ctors st t ns cts ctor_ix n_pd out = ok o) :
    OrderOut o (lForIn (fun nm s' => lOrderStep lst (absName t) s
        (absIndCtorRecs cts).toArray n_pd.val nm s')
      (absNames ns) (none, (absIndCtorRecs out).toArray, 0)) := by
  rw [frontend.export_c.order_type_ctors] at h
  have hres := order_type_ctors_loop_refines hrel hwf ht hnswf hinv hkeys hrelm hbound
    _ out _ 0#u64 0#usize o rfl (by simp [alloc.vec.Vec.len]) h
  simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac,
    show ((0#u64 : Std.U64)).val = 0 by scalar_tac] using hres

/-- The index recursion behind `export_c::order_block_ctors`. -/
private theorem order_block_ctors_loop_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {ty_names : alloc.vec.Vec name.Name}
    {listed : alloc.vec.Vec (alloc.vec.Vec name.Name)}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {ctor_ix : ron.hashmap.HashMap name.Name Std.U64} {n_pd : Std.U64}
    {s : Std.HashMap ConLeche.Name Nat}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (htwf : NamesWF ty_names) (hlwf : NamessWF listed)
    (hinv : HashMap.Inv State.hName ctor_ix) (hkeys : HashMap.KeysOk NameWF ctor_ix)
    (hrelm : HashMap.RelOn NameWF ctor_ix s absName (fun u => u.val))
    (hbound : ∀ (nn : ConLeche.Name) (v : Nat), s[nn]? = some v → v ≤ Std.Usize.max) (N : Nat) :
    ∀ (out : alloc.vec.Vec frontend.scan_types.IndCtorRec) (n t_at : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec frontend.scan_types.IndCtorRec)
        frontend.export_c.LineErr),
      ty_names.val.length - t_at.val = N → n.val = ty_names.val.length →
      frontend.export_c.order_block_ctors_loop st ty_names listed cts ctor_ix n_pd out
        n t_at = ok o →
      BlockOut o (lForIn (fun tn s' => lOrderBlockStep lst s (absIndCtorRecs cts).toArray
          n_pd.val tn s')
        (((absNames ty_names).zip (absNamess listed)).drop t_at.val)
        (none, (absIndCtorRecs out).toArray)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro out n t_at o hN hn h
    rw [frontend.export_c.order_block_ctors_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : t_at.val < ty_names.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨t, hidxt, h⟩ := h
      have htv : ty_names.val[t_at.val]'hltv = t := iv_index_val hidxt
      have htwf1 : NameWF t := by rw [← htv]; exact htwf _ (List.getElem_mem _)
      obtain ⟨v, hidxv, h⟩ := h
      have hltl : t_at.val < listed.val.length := iv_index_lt hidxv
      have hvv : listed.val[t_at.val]'hltl = v := iv_index_val hidxv
      have hvwf : NamesWF v := by rw [← hvv]; exact hlwf _ (List.getElem_mem _)
      have hdrop : ((absNames ty_names).zip (absNamess listed)).drop t_at.val
          = (absName t, absNames v) ::
            ((absNames ty_names).zip (absNamess listed)).drop (t_at.val + 1) := by
        rw [iv_zip_drop, iv_zip_drop]
        simp only [absNames, absNamess]
        rw [iv_drop_map absName hltv, iv_drop_map absNames hltl, htv, hvv]
        simp [absNames]
      rw [hdrop, lForIn_cons]
      obtain ⟨r, hr, h⟩ := h
      have hinner := order_type_ctors_refines hrel hwf htwf1 hvwf hinv hkeys hrelm hbound hr
      simp only [lOrderBlockStep]
      cases r with
      | Ok w =>
        obtain ⟨jw, hjw⟩ := hinner
        rw [hjw, iv_ok_bind]
        simp only [bind_eq_ok_iff] at h
        obtain ⟨t_at1, ht1, h⟩ := h
        have ht1v : t_at1.val = t_at.val + 1 := HashMap.uscalar_add_eq ht1
        have hres := ih (ty_names.val.length - t_at1.val) (by omega) w n t_at1 o rfl hn h
        rw [ht1v] at hres
        exact hres
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        cases e with
        | Msg m =>
          obtain ⟨s0, hs0⟩ := hinner
          exact ⟨s0, by rw [hs0]; rfl⟩
        | Verdict vv =>
          obtain ⟨lv, w, hu, hkd⟩ := hinner
          exact ⟨lv, w.1, by rw [hu, iv_ok_bind]; rfl, hkd⟩
    · rename_i hge
      have hle : ty_names.val.length ≤ t_at.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : ((absNames ty_names).zip (absNamess listed)).drop t_at.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        have : ((absNames ty_names).zip (absNamess listed)).length
            ≤ ty_names.val.length := by
          simp only [List.length_zip, absNames, List.length_map]
          exact Nat.min_le_left _ _
        omega
      rw [hnil, lForIn_nil]
      rfl

/-- **`export_c::order_block_ctors` refines the outer
`for tn in tyNames.zip listed` of `validateIndD`** — the constructors in the
block's own order (`ConLeche/Frontend/ExportC.lean:412-563`, con-leche task
#271 / issue #5). -/
theorem order_block_ctors_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {ty_names : alloc.vec.Vec name.Name}
    {listed : alloc.vec.Vec (alloc.vec.Vec name.Name)}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {ctor_ix : ron.hashmap.HashMap name.Name Std.U64} {n_pd : Std.U64}
    {s : Std.HashMap ConLeche.Name Nat}
    {o : core.result.Result (alloc.vec.Vec frontend.scan_types.IndCtorRec)
      frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (htwf : NamesWF ty_names) (hlwf : NamessWF listed)
    (hinv : HashMap.Inv State.hName ctor_ix) (hkeys : HashMap.KeysOk NameWF ctor_ix)
    (hrelm : HashMap.RelOn NameWF ctor_ix s absName (fun u => u.val))
    (hbound : ∀ (nn : ConLeche.Name) (v : Nat), s[nn]? = some v → v ≤ Std.Usize.max)
    (h : frontend.export_c.order_block_ctors st ty_names listed cts ctor_ix n_pd = ok o) :
    BlockOut o (lForIn (fun tn s' => lOrderBlockStep lst s (absIndCtorRecs cts).toArray
        n_pd.val tn s')
      ((absNames ty_names).zip (absNamess listed)) (none, #[])) := by
  rw [frontend.export_c.order_block_ctors] at h
  have hres := order_block_ctors_loop_refines hrel hwf htwf hlwf hinv hkeys hrelm hbound
    _ _ _ 0#usize o rfl (by simp [alloc.vec.Vec.len]) h
  simpa [absIndCtorRecs, alloc.vec.Vec.new,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hres


/-! ### `flatten_listed`, well formed

Agent R's `flatten_listed_refines` gives the abstraction; `names_have_dup`
needs the well-formedness too, and abstraction is not injective without it. -/

/-- The inner index recursion of `export_c::flatten_listed` keeps `NamesWF`. -/
private theorem flatten_listed_inner_wf {inner : alloc.vec.Vec name.Name}
    (hinner : NamesWF inner) (N : Nat) :
    ∀ (out r : alloc.vec.Vec name.Name) (k j : Std.Usize),
      inner.val.length - j.val = N → NamesWF out →
      frontend.export_c.flatten_listed_loop0_loop0 out inner k j = ok r → NamesWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro out r k j hN hout h
    rw [frontend.export_c.flatten_listed_loop0_loop0.eq_def] at h
    split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨nm, hidx, nm1, hdup, out1, hpush, j2, hj2, h⟩ := h
      have hltv : j.val < inner.val.length := iv_index_lt hidx
      have hnmv : inner.val[j.val]'hltv = nm := iv_index_val hidx
      have hnmwf : NameWF nm := by rw [← hnmv]; exact hinner _ (List.getElem_mem _)
      have hnm1 : nm1 = nm := by
        rw [name_dup_eq] at hdup; exact (Result.ok_injective hdup).symm
      have hj2v : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
      refine ih (inner.val.length - j2.val) (by omega) out1 r k j2 rfl ?_ h
      intro x hx
      rw [vec_push_val hpush] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hout x hx
      · rw [List.mem_singleton.mp hx, hnm1]; exact hnmwf
    · rw [← Result.ok_injective h]; exact hout

/-- The outer index recursion of `export_c::flatten_listed` keeps `NamesWF`. -/
private theorem flatten_listed_loop_wf
    {listed : alloc.vec.Vec (alloc.vec.Vec name.Name)}
    (hwf : NamessWF listed) (N : Nat) :
    ∀ (out r : alloc.vec.Vec name.Name) (n i : Std.Usize),
      listed.val.length - i.val = N → NamesWF out →
      frontend.export_c.flatten_listed_loop0 listed out n i = ok r → NamesWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro out r n i hN hout h
    rw [frontend.export_c.flatten_listed_loop0.eq_def] at h
    split at h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨inner, hidx, out1, hin, i2, hi2, h⟩ := h
      have hltv : i.val < listed.val.length := iv_index_lt hidx
      have hinv : listed.val[i.val]'hltv = inner := iv_index_val hidx
      have hinwf : NamesWF inner := by rw [← hinv]; exact hwf _ (List.getElem_mem _)
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      refine ih (listed.val.length - i2.val) (by omega) out1 r n i2 rfl ?_ h
      exact flatten_listed_inner_wf hinwf _ out out1 _ 0#usize rfl hout hin
    · rw [← Result.ok_injective h]; exact hout

/-- **`export_c::flatten_listed` keeps `NamesWF`.** -/
private theorem flatten_listed_wf {listed : alloc.vec.Vec (alloc.vec.Vec name.Name)}
    (hwf : NamessWF listed) {r : alloc.vec.Vec name.Name}
    (h : frontend.export_c.flatten_listed listed = ok r) : NamesWF r := by
  rw [frontend.export_c.flatten_listed] at h
  exact flatten_listed_loop_wf hwf _ _ r _ 0#usize rfl
    (by intro x hx; simp [alloc.vec.Vec.new] at hx) h

/-! ## `validate_ind_d` — the capstone

`export_c.rs:1921-2001` against `ConLeche/Frontend/ExportC.lean:412-563`
`validateIndD`, composed out of agent R's eight readers and this file's nine
fragments through `lValidateIndD_eq`. -/

/-- Every index the `ctorIx` fold stores is one it counted, so a bound on the
list's length bounds them all.  This is what lets the reordering loop's
`k as usize` cast be the identity. -/
private theorem ctorIxAux_bound (B : Nat) :
    ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat) (j : Nat),
      (∀ (n : ConLeche.Name) (v : Nat), m[n]? = some v → v ≤ B) →
      (∀ i, i < ns.length → j + i ≤ B) →
      ∀ (n : ConLeche.Name) (v : Nat), (ctorIxAux m j ns).1[n]? = some v → v ≤ B := by
  intro ns
  induction ns with
  | nil => intro m j hm _ n v hv; exact hm n v hv
  | cons a t iht =>
    intro m j hm hj n v hv
    rw [ctorIxAux_cons] at hv
    refine iht (m.insert a j) (j + 1) ?_ ?_ n v hv
    · intro n' v' hv'
      rw [Std.HashMap.getElem?_insert] at hv'
      by_cases hna : a = n'
      · rw [if_pos (by simpa using hna)] at hv'
        simp only [Option.some.injEq] at hv'
        rw [← hv']
        simpa using hj 0 (by simp)
      · rw [if_neg (by simpa using hna)] at hv'
        exact hm n' v' hv'
    · intro i hi
      have := hj (i + 1) (by simpa using hi)
      omega

/-- **`export_c::validate_ind_d` refines `validateIndD`**
(`ConLeche/Frontend/ExportC.lean:412-563`).  This is the `validateInd` clause
of agent R's `IndRSpec` (`Refine/Frontend/IndR.lean`), discharged. -/
theorem validate_ind_d_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndCtorRec) × Std.U64)
      frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.validate_ind_d st tys cts rcs = ok o) :
    ValidateOut o (ConLeche.Frontend.validateIndD lst (absIndTypeRecs tys)
      (absIndCtorRecs cts) (absIndRecRecs rcs)) := by
  rw [lValidateIndD_eq, lValidateIndD]
  simp only [pure_bind]
  rw [frontend.export_c.validate_ind_d] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := any_ty_unsafe_refines hb
  by_cases hbt : b = true
  · -- an `unsafe inductive` is DECLINED
    rw [if_pos hbt] at h
    rw [if_pos (by rw [← hbv]; exact hbt)]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨s1, -, m1, -, h⟩ := h
    rw [frontend.export_c.declined] at h
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ⟨_, rfl, rfl⟩
  · rw [if_neg hbt] at h
    rw [if_neg (by rw [← hbv]; exact hbt)]
    obtain ⟨n_pd, hnpd, h⟩ := bind_eq_ok_iff.mp h
    -- the declared parameter count
    have hnpdv : n_pd.val
        = (((absIndTypeRecs tys).map (fun t => t.numParams)).head?).getD 0 := by
      by_cases hz : alloc.vec.Vec.len tys = 0#usize
      · rw [if_pos hz] at hnpd
        simp only [Result.ok.injEq] at hnpd
        have hnil : tys.val = [] := by
          have : tys.val.length = 0 := by
            have := congrArg Std.UScalar.val hz
            simpa [alloc.vec.Vec.len] using this
          exact List.eq_nil_of_length_eq_zero this
        rw [← hnpd]
        simp [absIndTypeRecs, hnil]
      · rw [if_neg hz] at hnpd
        obtain ⟨itr, hitr, hnpd⟩ := bind_eq_ok_iff.mp hnpd
        have hlt : 0 < tys.val.length := iv_index_lt hitr
        have hitrv : tys.val[0]'hlt = itr := iv_index_val hitr
        simp only [Result.ok.injEq] at hnpd
        rw [← hnpd]
        simp only [absIndTypeRecs]
        rw [List.head?_eq_getElem?, List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_getElem hlt, hitrv]
        rfl
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := all_num_params_refines hb1
    by_cases hb1t : b1 = true
    · rw [if_pos hb1t] at h
      rw [if_pos (by rw [← hnpdv, ← hb1v]; exact hb1t)]
      -- the four readers
      obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
      have hty := ty_names_of_refines hrel hwf hr
      cases r with
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        cases e with
        | Msg m => obtain ⟨s0, hs0⟩ := hty; exact ⟨s0, by rw [hs0]; rfl⟩
        | Verdict v => exact hty.elim
      | Ok v =>
        obtain ⟨htyabs, htywf⟩ := hty
        rw [htyabs, iv_ok_bind]
        obtain ⟨r1, hr1, h⟩ := bind_eq_ok_iff.mp h
        have htt := ty_types_of_refines hrel hwf hr1
        cases r1 with
        | Err e =>
          simp only [Result.ok.injEq] at h
          rw [← h]
          cases e with
          | Msg m => obtain ⟨s0, hs0⟩ := htt; exact ⟨s0, by rw [hs0]; rfl⟩
          | Verdict vv => exact htt.elim
        | Ok v1 =>
          obtain ⟨httabs, httwf⟩ := htt
          rw [httabs, iv_ok_bind]
          obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
          have hls := listed_ctors_of_refines hrel hwf hr2
          cases r2 with
          | Err e =>
            simp only [Result.ok.injEq] at h
            rw [← h]
            cases e with
            | Msg m => obtain ⟨s0, hs0⟩ := hls; exact ⟨s0, by rw [hs0]; rfl⟩
            | Verdict vv => exact hls.elim
          | Ok v2 =>
            obtain ⟨hlsabs, hlswf⟩ := hls
            rw [hlsabs, iv_ok_bind]
            obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
            have hcn := ctor_names_of_refines hrel hwf hr3
            cases r3 with
            | Err e =>
              simp only [Result.ok.injEq] at h
              rw [← h]
              cases e with
              | Msg m => obtain ⟨s0, hs0⟩ := hcn; exact ⟨s0, by rw [hs0]; rfl⟩
              | Verdict vv => exact hcn.elim
            | Ok v3 =>
              obtain ⟨hcnabs, hcnwf⟩ := hcn
              rw [hcnabs, iv_ok_bind]
              -- `flat`, and the duplicate test
              obtain ⟨flat, hflat, h⟩ := bind_eq_ok_iff.mp h
              have hflatabs : absNames flat = (absNamess v2).flatten :=
                flatten_listed_refines hflat
              have hflatwf : NamesWF flat := flatten_listed_wf hlswf hflat
              obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
              have hb2v := names_have_dup_refines hflatwf hb2
              by_cases hb2t : b2 = true
              · rw [if_pos hb2t] at h
                rw [if_neg (by rw [← hflatabs]; exact hb2v.mp hb2t)]
                simp only [bind_eq_ok_iff] at h
                obtain ⟨s1, -, m1, -, h⟩ := h
                rw [frontend.export_c.invalid] at h
                simp only [Result.ok.injEq] at h
                rw [← h]
                exact ⟨_, rfl, rfl⟩
              · rw [if_neg hb2t] at h
                have hnd : ((absNamess v2).flatten).Nodup := by
                  rw [← hflatabs]
                  by_contra hc
                  exact hb2t (hb2v.mpr hc)
                rw [if_pos hnd]
                by_cases hlen : (alloc.vec.Vec.len flat != alloc.vec.Vec.len cts) = true
                · rw [if_pos hlen] at h
                  have hlenv : ((absNamess v2).flatten).length ≠ (absIndCtorRecs cts).length := by
                    rw [← hflatabs]
                    simp only [absNames, absIndCtorRecs, List.length_map]
                    simpa [alloc.vec.Vec.len] using hlen
                  rw [if_neg (by simpa using hlenv)]
                  simp only [bind_eq_ok_iff] at h
                  obtain ⟨i4, -, i6, -, m1, -, h⟩ := h
                  rw [frontend.export_c.invalid] at h
                  simp only [Result.ok.injEq] at h
                  rw [← h]
                  exact ⟨_, rfl, rfl⟩
                · rw [if_neg hlen] at h
                  have hlenv : ((absNamess v2).flatten).length = (absIndCtorRecs cts).length := by
                    rw [← hflatabs]
                    simp only [absNames, absIndCtorRecs, List.length_map]
                    simpa [alloc.vec.Vec.len] using hlen
                  rw [if_pos (by simpa using hlenv)]
                  -- the index map
                  obtain ⟨ctor_ix, hcix, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨hinv, hkeys, hrelm⟩ := ctor_index_of_refines hcnwf hcix
                  have hbound : ∀ (nn : ConLeche.Name) (vv : Nat),
                      (ctorIxAux ∅ 0 (absNames v3)).1[nn]? = some vv → vv ≤ Std.Usize.max := by
                    refine ctorIxAux_bound _ _ ∅ 0 (by intro n' v' hv'; simp at hv') ?_
                    intro i hi
                    simp only [absNames, List.length_map] at hi
                    have : v3.val.length ≤ Std.Usize.max := by scalar_tac
                    omega
                  -- the reordering
                  obtain ⟨r4, hr4, h⟩ := bind_eq_ok_iff.mp h
                  have hord := order_block_ctors_refines (s := (ctorIxAux ∅ 0 (absNames v3)).1)
                    hrel hwf htywf hlswf hinv hkeys hrelm hbound hr4
                  rw [hnpdv] at hord
                  simp only [ctorIxAux] at hord
                  cases r4 with
                  | Err e =>
                    simp only [Result.ok.injEq] at h
                    rw [← h]
                    cases e with
                    | Msg m =>
                      obtain ⟨s0, hs0⟩ := hord
                      exact ⟨s0, by rw [hs0]; rfl⟩
                    | Verdict vv =>
                      obtain ⟨lv, w, hu, hkd⟩ := hord
                      exact ⟨lv, by rw [hu]; rfl, hkd⟩
                  | Ok v4 =>
                    simp only [BlockOut] at hord
                    rw [hord, iv_ok_bind]
                    obtain ⟨nested, hnst, h⟩ := bind_eq_ok_iff.mp h
                    have hnstv := any_ty_nested_refines hnst
                    obtain ⟨n_types, hnt, h⟩ := bind_eq_ok_iff.mp h
                    have hntv : n_types.val = (absIndTypeRecs tys).length := by
                      rw [lift_eq, Result.ok.injEq] at hnt
                      rw [← hnt, Env.usize_cast_u64_val]
                      simp [absIndTypeRecs, alloc.vec.Vec.len]
                    obtain ⟨n_ctors, hnc, h⟩ := bind_eq_ok_iff.mp h
                    have hncv : n_ctors.val = (absIndCtorRecs v4).length := by
                      rw [lift_eq, Result.ok.injEq] at hnc
                      rw [← hnc, Env.usize_cast_u64_val]
                      simp [absIndCtorRecs, alloc.vec.Vec.len]
                    obtain ⟨k_exp, hkx, h⟩ := bind_eq_ok_iff.mp h
                    have hkxv := k_expected_of_refines httwf hkx
                    by_cases hnt2 : nested = true
                    · rw [if_pos hnt2] at h
                      rw [if_pos (by rw [← hnstv]; exact hnt2)]
                      simp only [Result.ok.injEq] at h
                      rw [← h]
                      simp only [ValidateOut]
                      rw [← hnpdv]
                      rfl
                    · rw [if_neg hnt2] at h
                      rw [if_neg (by rw [← hnstv]; exact hnt2)]
                      obtain ⟨r5, hr5, h⟩ := bind_eq_ok_iff.mp h
                      have hrec := check_rec_records_refines hrel hwf htywf httwf hr5
                      rw [hnpdv, hntv, hncv, hkxv] at hrec
                      cases r5 with
                      | Ok u =>
                        simp only [LoopOut] at hrec
                        rw [hrec, iv_ok_bind]
                        simp only [Result.ok.injEq] at h
                        rw [← h]
                        simp only [ValidateOut]
                        rw [← hnpdv]
                        rfl
                      | Err e =>
                        simp only [Result.ok.injEq] at h
                        rw [← h]
                        cases e with
                        | Msg m =>
                          obtain ⟨s0, hs0⟩ := hrec
                          exact ⟨s0, by rw [hs0]; rfl⟩
                        | Verdict vv =>
                          obtain ⟨lv, u, hu, hkd⟩ := hrec
                          exact ⟨lv, by rw [hu]; rfl, hkd⟩
    · rw [if_neg hb1t] at h
      rw [if_neg (by rw [← hnpdv, ← hb1v]; exact hb1t)]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s1, -, m1, -, h⟩ := h
      rw [frontend.export_c.declined] at h
      simp only [Result.ok.injEq] at h
      rw [← h]
      exact ⟨_, rfl, rfl⟩

end ConRon.Refine.Frontend
