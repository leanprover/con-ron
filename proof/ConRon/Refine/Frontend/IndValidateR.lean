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

end ConRon.Refine.Frontend
