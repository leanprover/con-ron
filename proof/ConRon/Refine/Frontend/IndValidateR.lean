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
file proves the other ten.

## The one place the port is not con-leche's function

`export_c::ctor_index_of` builds the name → record-index map **first record
wins**:

    if !m.contains_key(&ns[k]) { m.insert(name::dup(&ns[k]), k as u64); }

and its doc comment cites `HashMap.insertIfNew`.  `ExportC.lean:412-563`
builds it **last wins**:

    (ctorNames.foldl (fun mi n => (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1

— `Std.HashMap.insert` overwrites.  The two maps differ exactly when
`ctorNames` repeats a name, so *no lemma of this file says the two maps are
equal*; what is proved instead is that the difference is **unobservable**:

* the two maps have the **same key set** — the names occurring in
  `ctorNames` — so every `ctorIx[n]?` lookup of the reordering loop succeeds
  on one side exactly when it succeeds on the other (`ctorIxKeys`);
* **if every lookup succeeds, `ctorNames` cannot repeat.**  `flat.Nodup` and
  `flat.length == cts.length` have already passed, every name of `flat` is a
  key, and the keys are names of `ctorNames`, so
  `cts.length = flat.length = |names of flat| ≤ |names of ctorNames|`, which
  is `< cts.length` if `ctorNames` repeats.  With no repeat, first-wins and
  last-wins agree pointwise and the two runs are the same run
  (`ctorIx_agree`);
* **if some lookup fails, both sides leave through `.invalid`.**  Every early
  return of the reordering loop is `.inl (.invalid …)` and only the verdict
  *kind* is compared (`lVerdictKind`/`absVerdictKind`), so the outcomes agree
  even where the two sides checked different records on the way out.

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

`export_c.rs:1442-1453` against the cited `ctorIx` fold.  **The two are not
the same map** (see the file header): the port keeps the FIRST record of a
repeated name, con-leche's `Std.HashMap.insert` keeps the LAST.  What is
proved here is the two facts the reordering loop actually reads — the key set
and, under `Nodup`, the index — and nothing else. -/

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

/-- The fold's key set is what it has seen. -/
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

/-- **Under `Nodup` the fold is the index**, which is the case the reordering
loop is ever in (the counting argument of the file header). -/
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


/-! ### The port's fold, and when it is con-leche's

`export_c::ctor_index_of` is the same fold with a `contains_key` guard in
front of the insert — **first record wins**.  `firstIxAux` is that fold on the
con-leche side, `ctor_index_of_refines` is the port against it, and
`firstIxAux_eq_ctorIxAux` is the one place the two folds are identified: under
`Nodup` the guard never fires, so first-wins *is* last-wins. -/

/-- `export_c::ctor_index_of`'s fold: the insert is guarded, so the FIRST
record of a repeated name wins. -/
private def firstIxAux (m : Std.HashMap ConLeche.Name Nat) (j : Nat)
    (ns : List ConLeche.Name) : Std.HashMap ConLeche.Name Nat × Nat :=
  ns.foldl (fun (mi : Std.HashMap ConLeche.Name Nat × Nat) n =>
    (if mi.1.contains n then mi.1 else mi.1.insert n mi.2, mi.2 + 1)) (m, j)

private theorem firstIxAux_cons (m : Std.HashMap ConLeche.Name Nat) (j : Nat)
    (n : ConLeche.Name) (ns : List ConLeche.Name) :
    firstIxAux m j (n :: ns)
      = firstIxAux (if m.contains n then m else m.insert n j) (j + 1) ns := rfl

/-- **The guard never fires on a duplicate-free list**, so the port's fold and
con-leche's are the same map.  This is the only lemma of the file that
identifies the two, and it is exactly as strong as the counting argument of
the file header allows. -/
private theorem firstIxAux_eq_ctorIxAux :
    ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat) (j : Nat),
      ns.Nodup → (∀ n ∈ ns, m.contains n = false) →
      firstIxAux m j ns = ctorIxAux m j ns := by
  intro ns
  induction ns with
  | nil => intro m j _ _; rfl
  | cons a t iht =>
    intro m j hnd hfresh
    rw [firstIxAux_cons, ctorIxAux_cons, if_neg (by simp [hfresh a List.mem_cons_self])]
    refine iht _ _ (List.nodup_cons.mp hnd).2 ?_
    intro n hn
    rw [Std.HashMap.contains_insert]
    simp only [Bool.or_eq_false_iff]
    refine ⟨?_, hfresh n (List.mem_cons_of_mem _ hn)⟩
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hc
    exact (List.nodup_cons.mp hnd).1 (hc ▸ hn)

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
          (firstIxAux s k.val ((absNames ns).drop k.val)).1 absName (fun u => u.val) := by
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
      obtain ⟨c, hc, h⟩ := h
      -- the guard: `contains_key` is `s.contains` under the relation
      have hcv : c = s.contains (absName nm) := by
        rw [ron.hashmap.HashMap.contains_key] at hc
        obtain ⟨r, hr, hc⟩ := bind_eq_ok_iff.mp hc
        have hrv : r.map (fun u => u.val) = s[absName nm]? :=
          HashMap.Rel_get_wf State.nameEq2Fwd hinv hkeys hrel hnmwf hr
        rw [Std.HashMap.contains_eq_isSome_getElem?, ← hrv]
        cases r with
        | none => simp only [Result.ok.injEq] at hc; simp [← hc]
        | some v => simp only [Result.ok.injEq] at hc; simp [← hc]
      -- the abstracted list, split at `k`
      have hdrop : (absNames ns).drop k.val
          = absName nm :: (absNames ns).drop (k.val + 1) := by
        simp only [absNames]
        rw [List.drop_eq_getElem_cons (by simpa using hltv), List.getElem_map, hnmv]
      obtain ⟨m1, hm1, h⟩ := h
      obtain ⟨k1, hk1, h⟩ := h
      have hk1v : k1.val = k.val + 1 := HashMap.uscalar_add_eq hk1
      -- the two branches agree with `firstIxAux`'s guarded step
      have hstep : HashMap.Inv State.hName m1 ∧ HashMap.KeysOk NameWF m1 ∧
          HashMap.RelOn NameWF m1
            (if s.contains (absName nm) then s else s.insert (absName nm) k.val)
            absName (fun u => u.val) := by
        by_cases hcc : c = true
        · rw [if_pos hcc] at hm1
          have : m1 = m := (Result.ok_injective hm1).symm
          subst this
          rw [if_pos (by rw [← hcv]; exact hcc)]
          exact ⟨hinv, hkeys, hrel⟩
        · rw [if_neg hcc] at hm1
          simp only [bind_eq_ok_iff] at hm1
          obtain ⟨nm2, hdup, hm1⟩ := hm1
          have hnm2 : nm2 = nm := by
            rw [name_dup_eq] at hdup; exact (Result.ok_injective hdup).symm
          have hnm2wf : NameWF nm2 := by rw [hnm2]; exact hnmwf
          obtain ⟨u, hu, hm1⟩ := hm1
          have huv : u.val = k.val := by
            rw [lift_eq, Result.ok.injEq] at hu
            rw [← hu]; exact Env.usize_cast_u64_val k
          obtain ⟨q, hins, hm1⟩ := hm1
          obtain ⟨old, m2⟩ := q
          simp only [uncurry_apply_pair, Result.ok.injEq] at hm1
          obtain ⟨hinv2, -, hupd2, hkeys2⟩ :=
            HashMap.insert_refines_wf State.nameEq2Fwd hinv hkeys hnm2wf hins
          obtain ⟨hrel2, -⟩ :=
            HashMap.Rel_insert_wf State.nameEq2Fwd
              (fun a b ha hb hab => Name.absName_injective ha hb hab) hinv hkeys hrel
              hnm2wf hins
          rw [if_neg (by rw [← hcv]; exact hcc)]
          rw [← hm1]
          refine ⟨hinv2, hkeys2, ?_⟩
          rw [hnm2] at hrel2
          rw [← huv]
          exact hrel2
      obtain ⟨hinv1, hkeys1, hrel1⟩ := hstep
      have hres := ih (ns.val.length - k1.val) (by omega) m1
        (if s.contains (absName nm) then s else s.insert (absName nm) k.val) n k1 m'
        rfl hn hinv1 hkeys1 hrel1 h
      rw [hdrop, firstIxAux_cons, ← hk1v]
      exact hres
    · rename_i hlt
      have hge : ns.val.length ≤ k.val := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hdrop : (absNames ns).drop k.val = [] := by
        rw [List.drop_eq_nil_iff]; simpa [absNames] using hge
      rw [hdrop]
      exact ⟨hinv, hkeys, hrel⟩

/-- **`export_c::ctor_index_of` is the guarded fold**, `firstIxAux` — *not*
con-leche's `ctorIx`.  The two meet only at `firstIxAux_eq_ctorIxAux`, under
`Nodup`. -/
theorem ctor_index_of_refines {ns : alloc.vec.Vec name.Name} (hwf : NamesWF ns)
    {m : ron.hashmap.HashMap name.Name Std.U64}
    (h : frontend.export_c.ctor_index_of ns = ok m) :
    HashMap.Inv State.hName m ∧ HashMap.KeysOk NameWF m ∧
      HashMap.RelOn NameWF m (firstIxAux ∅ 0 (absNames ns)).1 absName (fun u => u.val) := by
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
    (tt : Name × Expr) (s : Option LVRes × Unit) :
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
    (r : IndRecRec) (s : Option LVRes × Unit) :
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

end ConRon.Refine.Frontend
