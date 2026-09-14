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


/-! ## The mask, and what con-leche's erasure leaves behind

**The one place the port's shape differs from con-leche's** (`prepare.rs`'s
module note, DESIGN.md task #84 §7).  con-leche's `pick` ERASES the picked
record from the array (`Array.eraseIdxIfInBounds`) and `frontOf` carries the
shrinking array along; the Aeneas subset has no way to take an element out of
a `Vec`, so the port records the erasure in a `picked` mask instead and reads
the array by its original index.

`residual` is the bridge: the records the mask does not carry, in the stream's
order — exactly the array con-leche is left holding.  `pickIdx` is the port's
`pick_idx` as a plain list recursion, the index *into the original list* of
the record con-leche finds at `findIdx` *into the residual*.  The two lemmas
`pick_residual_get` and `pick_residual_set` are the whole of the
correspondence: the same record is found, and the same list stays behind.

Neither is an "intermediate Lean definition matching the port's shape" in the
brief's sense — they are proof vocabulary, and no statement of this file is
phrased over them except through those two lemmas. -/

/-- The entries the mask does not carry, in order. -/
private def residual {α : Type} : List Bool → List α → List α
  | [], _ => []
  | _ :: _, [] => []
  | b :: bs, d :: ds => if b then residual bs ds else d :: residual bs ds

/-- `prepare::pick_idx` as a list recursion: the first index the mask does not
carry and that passes `P`, and the length when there is none. -/
private def pickIdx {α : Type} (P : α → Bool) : List Bool → List α → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | b :: bs, d :: ds => if !b && P d then 0 else pickIdx P bs ds + 1

private theorem residual_nil_right {α : Type} (bs : List Bool) :
    residual bs ([] : List α) = [] := by
  cases bs <;> rw [residual]

private theorem pickIdx_nil_right {α : Type} (P : α → Bool) (bs : List Bool) :
    pickIdx P bs ([] : List α) = 0 := by
  cases bs <;> rw [pickIdx]

/-- A mask of all `false`s carries nothing away. -/
private theorem residual_replicate_false {α : Type} :
    ∀ (l : List α), residual (List.replicate l.length false) l = l
  | [] => by rw [residual_nil_right]
  | d :: ds => by
    rw [List.length_cons, List.replicate_succ, residual, if_neg (by simp),
      residual_replicate_false ds]

/-- `pick_idx` never answers past the end. -/
private theorem pickIdx_le {α : Type} (P : α → Bool) :
    ∀ (bs : List Bool) (l : List α), pickIdx P bs l ≤ l.length
  | [], l => by rw [pickIdx]; simp
  | _ :: _, [] => by rw [pickIdx]; simp
  | b :: bs, d :: ds => by
    rw [pickIdx, List.length_cons]
    split
    · omega
    · have := pickIdx_le P bs ds; omega

/-- The residual is as long as the mask says. -/
private theorem residual_length {α : Type} :
    ∀ (bs : List Bool) (l : List α), (residual bs l).length ≤ l.length
  | [], l => by rw [residual]; exact Nat.zero_le _
  | _ :: _, [] => by rw [residual]
  | b :: bs, d :: ds => by
    have ih := residual_length bs ds
    rw [residual]
    split
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

/-- **`pick` finds the same record.**  `ConLeche/Frontend/Prepare.lean:121-124`'s
`ds[ds.findIdx (declares n)]?` on the residual array is the port's
`ds[pick_idx n ds picked]?` on the original. -/
private theorem pick_residual_get {α : Type} (P : α → Bool) :
    ∀ (bs : List Bool) (l : List α), bs.length = l.length →
      l[pickIdx P bs l]? = (residual bs l)[(residual bs l).findIdx P]?
  | [], [], _ => by simp [pickIdx, residual]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b :: bs, d :: ds, h => by
    have hlen : bs.length = ds.length := by simpa using h
    rw [pickIdx, residual]
    by_cases hb : b = true
    · subst hb
      rw [if_neg (by simp), if_pos rfl, List.getElem?_cons_succ]
      exact pick_residual_get P bs ds hlen
    · simp only [Bool.not_eq_true] at hb
      subst hb
      by_cases hP : P d = true
      · rw [if_pos (by simp [hP]), if_neg (by simp), List.findIdx_cons, hP, cond_true]
        simp
      · simp only [Bool.not_eq_true] at hP
        rw [if_neg (by simp [hP]), if_neg (by simp), List.getElem?_cons_succ,
          List.findIdx_cons, hP, cond_false, List.getElem?_cons_succ]
        exact pick_residual_get P bs ds hlen

/-- **`pick` leaves the same list behind.**  Masking the picked index is
`Array.eraseIdxIfInBounds` on the residual. -/
private theorem pick_residual_set {α : Type} (P : α → Bool) :
    ∀ (bs : List Bool) (l : List α), bs.length = l.length →
      residual (bs.set (pickIdx P bs l) true) l
        = (residual bs l).eraseIdx ((residual bs l).findIdx P)
  | [], [], _ => by simp [pickIdx, residual]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b :: bs, d :: ds, h => by
    have hlen : bs.length = ds.length := by simpa using h
    rw [pickIdx]
    by_cases hb : b = true
    · subst hb
      rw [if_neg (by simp), List.set_cons_succ, residual, if_pos rfl,
        residual, if_pos rfl]
      exact pick_residual_set P bs ds hlen
    · simp only [Bool.not_eq_true] at hb
      subst hb
      by_cases hP : P d = true
      · rw [if_pos (by simp [hP]), List.set_cons_zero, residual, if_pos rfl,
          residual, if_neg (by simp), List.findIdx_cons, hP, cond_true]
        simp
      · simp only [Bool.not_eq_true] at hP
        rw [if_neg (by simp [hP]), List.set_cons_succ, residual, if_neg (by simp),
          residual, if_neg (by simp), List.findIdx_cons, hP, cond_false]
        simp only [List.eraseIdx_cons_succ, List.cons.injEq, true_and]
        exact pick_residual_set P bs ds hlen


/-! ## The plan's two components

`prepare::no_picks` is the mask before anything is picked, and
`prepare::pick_idx` is the cited `ds.findIdx (declares n)` read through it. -/

/-- `prepare::no_picks`' loop: `n - i` more `false`s. -/
private theorem no_picks_loop_val :
    ∀ k : Nat, ∀ (n i : Std.Usize) (picked v : alloc.vec.Vec Bool),
      n.val - i.val ≤ k →
      frontend.prepare.no_picks_loop n picked i = ok v →
      v.val = picked.val ++ List.replicate (n.val - i.val) false := by
  intro k
  induction k with
  | zero =>
    intro n i picked v hk h
    rw [frontend.prepare.no_picks_loop.eq_def] at h
    rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n.val - i.val = 0 by omega]; simp
  | succ k ih =>
    intro n i picked v hk h
    rw [frontend.prepare.no_picks_loop.eq_def] at h
    by_cases hi : i.val < n.val
    · rw [if_pos (show i < n by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨picked1, hp1, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
      rw [ih n i1 picked1 v (by omega) h, vec_push_val hp1, hi1v]
      rw [show n.val - i.val = (n.val - (i.val + 1)) + 1 by omega]
      rw [List.replicate_succ]
      simp
    · rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
      rw [← h, show n.val - i.val = 0 by omega]; simp

/-- `ConLeche/Frontend/Prepare.lean:121-124` — `prepare::no_picks` is the mask
in which nothing has been picked out of the stream yet. -/
theorem no_picks_refines {n : Std.Usize} {v : alloc.vec.Vec Bool}
    (h : frontend.prepare.no_picks n = ok v) :
    v.val = List.replicate n.val false := by
  rw [frontend.prepare.no_picks] at h
  rw [no_picks_loop_val n.val n 0#usize _ v (by scalar_tac) h]
  simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]

/-- `prepare::pick_idx`'s loop once the sentinel is gone: the answer stands. -/
private theorem pick_idx_loop_hit {n : name.Name} {ds : alloc.vec.Vec env.Declaration}
    {picked : alloc.vec.Vec Bool} {m i hit r : Std.Usize} (hne : hit ≠ m)
    (h : frontend.prepare.pick_idx_loop n ds picked m i hit = ok r) : r = hit := by
  rw [frontend.prepare.pick_idx_loop.eq_def] at h
  by_cases hi : i < m
  · rw [if_pos hi, if_neg hne, Result.ok.injEq] at h; exact h.symm
  · rw [if_neg hi, Result.ok.injEq] at h; exact h.symm

/-- `ConLeche/Frontend/Prepare.lean:121-124` — `prepare::pick_idx`'s loop is
`pickIdx` from `i` on. -/
private theorem pick_idx_loop_val {n : name.Name} {ds : alloc.vec.Vec env.Declaration}
    {picked : alloc.vec.Vec Bool} (hn : NameWF n)
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (hlen : picked.val.length = ds.val.length) :
    ∀ k : Nat, ∀ (i r : Std.Usize),
      ds.val.length - i.val ≤ k → i.val ≤ ds.val.length →
      frontend.prepare.pick_idx_loop n ds picked (alloc.vec.Vec.len ds) i
          (alloc.vec.Vec.len ds) = ok r →
      r.val = i.val + pickIdx (ConLeche.Frontend.declares (absName n))
        (picked.val.drop i.val) ((ds.val.drop i.val).map absDeclaration) := by
  have hm : (alloc.vec.Vec.len ds).val = ds.val.length := alloc.vec.Vec.len_val ds
  intro k
  induction k with
  | zero =>
    intro i r hk hi h
    have hieq : i.val = ds.val.length := by omega
    rw [frontend.prepare.pick_idx_loop.eq_def] at h
    rw [if_neg (show ¬ i < alloc.vec.Vec.len ds by scalar_tac), Result.ok.injEq] at h
    rw [← h, hm, hieq, List.drop_length, List.map_nil, pickIdx_nil_right]
    simp
  | succ k ih =>
    intro i r hk hi h
    rw [frontend.prepare.pick_idx_loop.eq_def] at h
    by_cases hlt : i.val < ds.val.length
    · rw [if_pos (show i < alloc.vec.Vec.len ds by scalar_tac),
        if_pos rfl] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, hit1, hhit1, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
      have hbg := ExprOps.vec_index_getElem? hb
      have hpl : i.val < picked.val.length := by omega
      have hbx : picked.val[i.val] = b := by
        rw [List.getElem?_eq_getElem hpl] at hbg; exact Option.some_injective _ hbg
      rw [List.drop_eq_getElem_cons hpl, List.drop_eq_getElem_cons hlt, hbx]
      simp only [List.map_cons]
      rw [pickIdx]
      by_cases hbb : b = true
      · subst hbb
        rw [if_pos rfl, Result.ok.injEq] at hhit1
        rw [if_neg (by simp)]
        rw [ih i1 r (by omega) (by omega) (by rw [← hhit1] at h; exact h), hi1v]
        omega
      · simp only [Bool.not_eq_true] at hbb
        subst hbb
        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at hhit1
        obtain ⟨d, hd, b1, hb1, hhit1⟩ := hhit1
        have hdg := ExprOps.vec_index_getElem? hd
        have hdx : ds.val[i.val] = d := by
          rw [List.getElem?_eq_getElem hlt] at hdg; exact Option.some_injective _ hdg
        have hdwf : DeclarationWF d := hds _ (List.mem_of_getElem? hdg)
        have hb1v := declares_refines hn hdwf hb1
        rw [hdx]
        by_cases hbb1 : b1 = true
        · subst hbb1
          rw [if_pos rfl, Result.ok.injEq] at hhit1
          rw [if_pos (by simp [← hb1v])]
          rw [← hhit1] at h
          have hine : i ≠ alloc.vec.Vec.len ds := by
            intro hc; rw [hc] at hlt; simp [hm] at hlt
          rw [pick_idx_loop_hit hine h]
          omega
        · simp only [Bool.not_eq_true] at hbb1
          subst hbb1
          simp only [Bool.false_eq_true, reduceIte, Result.ok.injEq] at hhit1
          rw [if_neg (by simp [← hb1v])]
          rw [← hhit1] at h
          rw [ih i1 r (by omega) (by omega) h, hi1v]
          omega
    · rw [if_neg (show ¬ i < alloc.vec.Vec.len ds by scalar_tac), Result.ok.injEq] at h
      have hieq : i.val = ds.val.length := by omega
      rw [← h, hm, hieq, List.drop_length, List.map_nil, pickIdx_nil_right]
      simp

/-- `ConLeche/Frontend/Prepare.lean:121-124` — **`prepare::pick_idx` refines
`pick`'s `ds.findIdx (declares n)`**, read through the mask: the index *into
the stream* of the record con-leche's `findIdx` names in the residual. -/
theorem pick_idx_refines {n : name.Name} {ds : alloc.vec.Vec env.Declaration}
    {picked : alloc.vec.Vec Bool} {r : Std.Usize} (hn : NameWF n)
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (hlen : picked.val.length = ds.val.length)
    (h : frontend.prepare.pick_idx n ds picked = ok r) :
    r.val = pickIdx (ConLeche.Frontend.declares (absName n)) picked.val
      (ds.val.map absDeclaration) := by
  rw [frontend.prepare.pick_idx] at h
  have := pick_idx_loop_val hn hds hlen ds.val.length 0#usize r (by scalar_tac)
    (by scalar_tac) h
  simpa using this


end ConRon.Refine.Frontend
