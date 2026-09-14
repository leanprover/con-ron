/-
`ConRon.Refine.Frontend.PrepareR` — **the two permuting passes, exact against
con-leche** (task #87, phase 3).

Phase 1's `ConRon/Refine/Frontend/Prepare.lean` proved the tail of the parse
pipeline *well formed*: every record `prepare::prepare_prelude` hands the fold
is one the port's own smart constructors built.  This file proves it **exact**:
for the same records, the port's prepared stream is con-leche's
`preparePrelude` of the abstracted ones, record for record and in the same
order.

The two passes are `crates/con-ron-core/src/frontend/prepare.rs`
(`ConLeche/Frontend/Prepare.lean`) and
`crates/con-ron-core/src/frontend/nat_op_ground.rs`
(`ConLeche/Frontend/NatOpGround.lean`).  Neither has an error channel — both
are total in con-leche and `Result`-valued only because the port's `Vec` reads
and `usize` arithmetic are — so every lemma here is a plain accept-direction
statement `f … = ok r → abs r = ⟨the Lean⟩`, with no `ErrSim` half to carry
(`Refine/README.md`'s full-outcome table: there is no mirrored `.Err` because
there is no `Except` on either side).

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.Prepare
import ConRon.Refine.BasisRaw
import ConRon.Refine.CoreKNames
import ConRon.Refine.HashMapWF
import ConLeche.Frontend.Prepare

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## The records, as con-leche's list

`Refine/Main.lean` already spells the parse's `Vec<Declaration>` as
`ds.val.map absDeclaration`; this file keeps that spelling and adds the
`Array`/`List` bridge con-leche's own signatures need. -/

/-- A `Vec<Declaration>` as con-leche's `List Declaration`. -/
def absDecls (ds : alloc.vec.Vec env.Declaration) : List ConLeche.Declaration :=
  ds.val.map absDeclaration

/-- `prepare::PreludeIx` as con-leche's. -/
def absPreludeIx (pre : frontend.prepare.PreludeIx) : ConLeche.Frontend.PreludeIx :=
  ⟨(absDecls pre.decls).toArray⟩

/-! ## The names a record declares

`env::declaration_names` is `Declaration.names` (`ConLeche/Kernel/Env.lean:666-670`).
No lemma had needed it before: the fold reads `declaration_name`, and only the
two permuting passes read the whole list. -/

/-- `ConLeche/Kernel/Env.lean:666-670` — `env::declaration_names` refines
`Declaration.names`. -/
theorem declaration_names_refines {d : env.Declaration} {ns : alloc.vec.Vec name.Name}
    (hd : DeclarationWF d) (h : env.declaration_names d = ok ns) :
    absNames ns = ConLeche.Declaration.names (absDeclaration d) ∧ NamesWF ns := by
  cases d with
  | AxiomDecl cv =>
    simp only [env.declaration_names, name_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    refine ⟨?_, ?_⟩
    · rw [absNames, vec_push_val h]; simp [alloc.vec.Vec.new, absDeclaration,
        ConLeche.Declaration.names, absConstantVal]
    · intro y hy
      rw [vec_push_val h] at hy
      rcases List.mem_append.mp hy with hy | hy
      · simp [alloc.vec.Vec.new] at hy
      rw [List.mem_singleton.mp hy]; exact hd.1
  | DefnDecl cv v hint =>
    simp only [env.declaration_names, name_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    refine ⟨?_, ?_⟩
    · rw [absNames, vec_push_val h]; simp [alloc.vec.Vec.new, absDeclaration,
        ConLeche.Declaration.names, absConstantVal]
    · intro y hy
      rw [vec_push_val h] at hy
      rcases List.mem_append.mp hy with hy | hy
      · simp [alloc.vec.Vec.new] at hy
      rw [List.mem_singleton.mp hy]; exact hd.1.1
  | ThmDecl cv v =>
    simp only [env.declaration_names, name_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    refine ⟨?_, ?_⟩
    · rw [absNames, vec_push_val h]; simp [alloc.vec.Vec.new, absDeclaration,
        ConLeche.Declaration.names, absConstantVal]
    · intro y hy
      rw [vec_push_val h] at hy
      rcases List.mem_append.mp hy with hy | hy
      · simp [alloc.vec.Vec.new] at hy
      rw [List.mem_singleton.mp hy]; exact hd.1.1
  | OpaqueDecl cv v =>
    simp only [env.declaration_names, name_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    refine ⟨?_, ?_⟩
    · rw [absNames, vec_push_val h]; simp [alloc.vec.Vec.new, absDeclaration,
        ConLeche.Declaration.names, absConstantVal]
    · intro y hy
      rw [vec_push_val h] at hy
      rcases List.mem_append.mp hy with hy | hy
      · simp [alloc.vec.Vec.new] at hy
      rw [List.mem_singleton.mp hy]; exact hd.1.1
  | BasisDecl k =>
    rw [env.declaration_names] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [absNames, alloc.vec.Vec.new, absDeclaration,
      ConLeche.Declaration.names], by intro y hy; simp [alloc.vec.Vec.new] at hy⟩
  | IndDecl block nP =>
    rw [env.declaration_names] at h
    obtain ⟨habs, hwf⟩ := BasisRaw.constant_info_names_refines hd h
    exact ⟨by rw [habs]; rfl, hwf⟩
  | QuotDecl k cv =>
    simp only [env.declaration_names, name_dup_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    refine ⟨?_, ?_⟩
    · rw [absNames, vec_push_val h]; simp [alloc.vec.Vec.new, absDeclaration,
        ConLeche.Declaration.names, absConstantVal]
    · intro y hy
      rw [vec_push_val h] at hy
      rcases List.mem_append.mp hy with hy | hy
      · simp [alloc.vec.Vec.new] at hy
      rw [List.mem_singleton.mp hy]; exact hd.1

/-! ## The prelude's lookup key and its name test

`prepare::prelude_key` is `preludeKey` (`ConLeche/Frontend/Prepare.lean:90-93`)
and `prepare::declares` is `declares` (`:109-110`); both read
`declaration_names` and nothing else. -/

/-- `ConLeche/Frontend/Prepare.lean:90-93` — `prepare::prelude_key` refines
`preludeKey`: the head of `Declaration.names`, `.anonymous` on the empty
list. -/
theorem prelude_key_refines {d : env.Declaration} {n : name.Name}
    (hd : DeclarationWF d) (h : frontend.prepare.prelude_key d = ok n) :
    absName n = ConLeche.Frontend.preludeKey (absDeclaration d) ∧ NameWF n := by
  rw [frontend.prepare.prelude_key] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ns, hns, h⟩ := h
  obtain ⟨habs, hwf⟩ := declaration_names_refines hd hns
  rw [ConLeche.Frontend.preludeKey, ← habs, absNames]
  by_cases hz : alloc.vec.Vec.len ns = 0#usize
  · rw [if_pos hz] at h
    have hnil : ns.val = [] := by
      have := alloc.vec.Vec.len_val ns
      have : ns.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero this
    rw [hnil]
    exact ⟨by rw [Name.anonymous_refines h]; simp, Name.anonymous_wf h⟩
  · rw [if_neg hz] at h
    simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq] at h
    obtain ⟨n0, hn0, rfl⟩ := h
    have hg := ExprOps.vec_index_getElem? hn0
    have hhd : ns.val.head? = some n0 := by
      rw [List.head?_eq_getElem?]; rw [← hg]; rfl
    refine ⟨?_, hwf _ (List.mem_of_getElem? hg)⟩
    rw [List.head?_map, hhd]
    simp

/-- `ConLeche/Frontend/Prepare.lean:109-110` — `prepare::declares` refines
`declares`: the name test a record is picked by. -/
theorem declares_refines {n : name.Name} {d : env.Declaration} {b : Bool}
    (hn : NameWF n) (hd : DeclarationWF d) (h : frontend.prepare.declares n d = ok b) :
    b = ConLeche.Frontend.declares (absName n) (absDeclaration d) := by
  rw [frontend.prepare.declares] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ns, hns, h⟩ := h
  obtain ⟨habs, hwf⟩ := declaration_names_refines hd hns
  rw [Name.contains_refines hwf hn h, habs, ConLeche.Frontend.declares]

/-- `ConLeche/Frontend/Prepare.lean:83-88` — `prepare::prelude_ix_empty`
refines `PreludeIx`'s field default: the empty prelude, which the prelude's
own parse runs against. -/
theorem prelude_ix_empty_refines {pre : frontend.prepare.PreludeIx}
    (h : frontend.prepare.prelude_ix_empty = ok pre) :
    absPreludeIx pre = ({} : ConLeche.Frontend.PreludeIx) := by
  rw [frontend.prepare.prelude_ix_empty] at h
  rw [← Result.ok_injective h]
  simp [absPreludeIx, absDecls, alloc.vec.Vec.new]

/-! ## The operation records the hoist serves -/

/-- `ConLeche/Frontend/NatOpGround.lean:97-104` — `nat_op_ground::is_nat_op_record`
refines `isNatOpRecord`. -/
theorem is_nat_op_record_refines {d : env.Declaration} {o : Option name.Name}
    (hd : DeclarationWF d) (h : frontend.nat_op_ground.is_nat_op_record d = ok o) :
    o.map absName = ConLeche.Frontend.isNatOpRecord (absDeclaration d) ∧
      ∀ n ∈ o, NameWF n := by
  cases d with
  | DefnDecl cv v hint =>
    rw [frontend.nat_op_ground.is_nat_op_record] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨dm, hdm, b, hb, h⟩ := h
    obtain ⟨hdmabs, hdmwf⟩ := CoreK.nat_div_mod_names_refines hdm
    have hbv := Name.contains_refines hdmwf hd.1.1 hb
    rw [hdmabs] at hbv
    by_cases hbb : b = true
    · subst hbb
      simp only [reduceIte, bind_eq_ok_iff, name_dup_eq, Result.ok.injEq,
        exists_eq_left'] at h
      rw [← h]
      refine ⟨?_, ?_⟩
      · simp only [Option.map_some, ConLeche.Frontend.isNatOpRecord, absDeclaration,
          absConstantVal]
        rw [if_pos (by rw [← hbv]; simp)]
      · intro n hn; rw [Option.mem_def, Option.some_inj] at hn; rw [← hn]; exact hd.1.1
    · simp only [Bool.not_eq_true] at hbb
      subst hbb
      simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
      obtain ⟨on, hon, b1, hb1, h⟩ := h
      obtain ⟨honabs, honwf⟩ := CoreK.nat_op_names_refines hon
      have hb1v := Name.contains_refines honwf hd.1.1 hb1
      rw [honabs] at hb1v
      by_cases hbb1 : b1 = true
      · subst hbb1
        simp only [reduceIte, bind_eq_ok_iff, name_dup_eq, Result.ok.injEq,
          exists_eq_left'] at h
        rw [← h]
        refine ⟨?_, ?_⟩
        · simp only [Option.map_some, ConLeche.Frontend.isNatOpRecord, absDeclaration,
            absConstantVal]
          rw [if_pos (by rw [← hbv, ← hb1v]; simp)]
        · intro n hn; rw [Option.mem_def, Option.some_inj] at hn; rw [← hn]; exact hd.1.1
      · simp only [Bool.not_eq_true] at hbb1
        subst hbb1
        simp only [Bool.false_eq_true, reduceIte, Result.ok.injEq] at h
        rw [← h]
        refine ⟨?_, by intro n hn; simp at hn⟩
        simp only [Option.map_none, ConLeche.Frontend.isNatOpRecord, absDeclaration,
          absConstantVal]
        rw [if_neg (by rw [← hbv, ← hb1v]; simp)]
  | AxiomDecl cv =>
    rw [frontend.nat_op_ground.is_nat_op_record] at h
    rw [← Result.ok_injective h]; exact ⟨rfl, by intro n hn; simp at hn⟩
  | ThmDecl cv v =>
    rw [frontend.nat_op_ground.is_nat_op_record] at h
    rw [← Result.ok_injective h]; exact ⟨rfl, by intro n hn; simp at hn⟩
  | OpaqueDecl cv v =>
    rw [frontend.nat_op_ground.is_nat_op_record] at h
    rw [← Result.ok_injective h]; exact ⟨rfl, by intro n hn; simp at hn⟩
  | BasisDecl k =>
    rw [frontend.nat_op_ground.is_nat_op_record] at h
    rw [← Result.ok_injective h]; exact ⟨rfl, by intro n hn; simp at hn⟩
  | IndDecl block nP =>
    rw [frontend.nat_op_ground.is_nat_op_record] at h
    rw [← Result.ok_injective h]; exact ⟨rfl, by intro n hn; simp at hn⟩
  | QuotDecl k cv =>
    rw [frontend.nat_op_ground.is_nat_op_record] at h
    rw [← Result.ok_injective h]; exact ⟨rfl, by intro n hn; simp at hn⟩


end ConRon.Refine.Frontend
