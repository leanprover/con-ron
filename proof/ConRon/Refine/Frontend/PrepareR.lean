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


/-! ## Materialising the prepared stream

`prepare::prepared_stream` is the cited `acc.push (m.getD p)` followed by
`front ++ rest`, in one pass (`prepare.rs`'s module note).  `frontFrom` is that
front as a function of the *plan*: slot `j` is the stream's own record where
`front_of` found one (`l[k]?` is `some`) and the prelude's where it did not. -/

/-- The front of the prepared stream as a function of the plan: the cited
`m.getD p`, one per prelude record. -/
private def frontFrom (picks : List Nat) (l ps : List ConLeche.Declaration) :
    List ConLeche.Declaration :=
  (ps.zip picks).map (fun q => (l[q.2]?).getD q.1)

private theorem frontFrom_cons (k : Nat) (ks : List Nat)
    (l : List ConLeche.Declaration) (p : ConLeche.Declaration)
    (ps : List ConLeche.Declaration) :
    frontFrom (k :: ks) l (p :: ps) = (l[k]?).getD p :: frontFrom ks l ps := by
  rw [frontFrom, frontFrom, List.zip_cons_cons, List.map_cons]

/-- `ConLeche/Frontend/Prepare.lean:159-163` — `prepare::prepared_rest`'s loop:
the stream's records the mask does not carry. -/
private theorem prepared_rest_loop_refines {ds : alloc.vec.Vec env.Declaration}
    {picked : alloc.vec.Vec Bool}
    (hlen : picked.val.length = ds.val.length) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec env.Declaration),
      ds.val.length - i.val ≤ k → i.val ≤ ds.val.length →
      frontend.prepare.prepared_rest_loop ds picked out (alloc.vec.Vec.len ds) i = ok v →
      v.val.map absDeclaration = out.val.map absDeclaration ++
        residual (picked.val.drop i.val) ((ds.val.drop i.val).map absDeclaration) := by
  have hm : (alloc.vec.Vec.len ds).val = ds.val.length := alloc.vec.Vec.len_val ds
  intro k
  induction k with
  | zero =>
    intro i out v hk hi h
    have hieq : i.val = ds.val.length := by omega
    rw [frontend.prepare.prepared_rest_loop.eq_def] at h
    rw [if_neg (show ¬ i < alloc.vec.Vec.len ds by scalar_tac), Result.ok.injEq] at h
    rw [← h, hieq, List.drop_length, List.map_nil, residual_nil_right]
    simp
  | succ k ih =>
    intro i out v hk hi h
    rw [frontend.prepare.prepared_rest_loop.eq_def] at h
    by_cases hlt : i.val < ds.val.length
    · rw [if_pos (show i < alloc.vec.Vec.len ds by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, out1, hout1, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
      have hbg := ExprOps.vec_index_getElem? hb
      have hpl : i.val < picked.val.length := by omega
      have hbx : picked.val[i.val] = b := by
        rw [List.getElem?_eq_getElem hpl] at hbg; exact Option.some_injective _ hbg
      rw [ih i1 out1 v (by omega) (by omega) h, hi1v]
      rw [List.drop_eq_getElem_cons hpl, List.drop_eq_getElem_cons hlt, hbx,
        List.map_cons, residual]
      by_cases hbb : b = true
      · subst hbb
        rw [if_pos rfl, Result.ok.injEq] at hout1
        rw [if_pos rfl, ← hout1]
      · simp only [Bool.not_eq_true] at hbb
        subst hbb
        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at hout1
        obtain ⟨d, hd, d1, hd1, hpush⟩ := hout1
        have hdg := ExprOps.vec_index_getElem? hd
        have hdx : ds.val[i.val] = d := by
          rw [List.getElem?_eq_getElem hlt] at hdg; exact Option.some_injective _ hdg
        rw [if_neg (by simp), vec_push_val hpush, declaration_dup_refines hd1, hdx]
        simp
    · rw [if_neg (show ¬ i < alloc.vec.Vec.len ds by scalar_tac), Result.ok.injEq] at h
      have hieq : i.val = ds.val.length := by omega
      rw [← h, hieq, List.drop_length, List.map_nil, residual_nil_right]
      simp

/-- `ConLeche/Frontend/Prepare.lean:159-163` — **`prepare::prepared_rest`
refines the cited `front ++ rest`'s second half**: the residual, appended to
the accumulator. -/
theorem prepared_rest_refines {ds out v : alloc.vec.Vec env.Declaration}
    {picked : alloc.vec.Vec Bool}
    (hlen : picked.val.length = ds.val.length)
    (h : frontend.prepare.prepared_rest out ds picked = ok v) :
    v.val.map absDeclaration = out.val.map absDeclaration ++
      residual picked.val (ds.val.map absDeclaration) := by
  rw [frontend.prepare.prepared_rest] at h
  have := prepared_rest_loop_refines hlen ds.val.length 0#usize out v
    (by scalar_tac) (by scalar_tac) h
  simpa using this

/-- `ConLeche/Frontend/Prepare.lean:126-135` — `prepare::prepared_front`'s
loop: the cited `acc.push (m.getD p)`, one prelude record at a time. -/
private theorem prepared_front_loop_refines {ps ds : alloc.vec.Vec env.Declaration}
    {picks : alloc.vec.Vec Std.Usize}
    (hlen : picks.val.length = ps.val.length) :
    ∀ k : Nat, ∀ (j : Std.Usize) (out v : alloc.vec.Vec env.Declaration),
      ps.val.length - j.val ≤ k → j.val ≤ ps.val.length →
      frontend.prepare.prepared_front_loop ps ds picks out (alloc.vec.Vec.len ds)
          (alloc.vec.Vec.len ps) j = ok v →
      v.val.map absDeclaration = out.val.map absDeclaration ++
        frontFrom ((picks.val.map (·.val)).drop j.val) (ds.val.map absDeclaration)
          ((ps.val.drop j.val).map absDeclaration) := by
  have hmp : (alloc.vec.Vec.len ps).val = ps.val.length := alloc.vec.Vec.len_val ps
  have hmd : (alloc.vec.Vec.len ds).val = ds.val.length := alloc.vec.Vec.len_val ds
  intro k
  induction k with
  | zero =>
    intro j out v hk hj h
    have hjeq : j.val = ps.val.length := by omega
    rw [frontend.prepare.prepared_front_loop.eq_def] at h
    rw [if_neg (show ¬ j < alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    rw [← h, hjeq, List.drop_length, List.map_nil, frontFrom]
    simp
  | succ k ih =>
    intro j out v hk hj h
    rw [frontend.prepare.prepared_front_loop.eq_def] at h
    by_cases hlt : j.val < ps.val.length
    · rw [if_pos (show j < alloc.vec.Vec.len ps by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨kk, hkk, out1, hout1, j1, hj1, h⟩ := h
      have hj1v : j1.val = j.val + 1 := by have := Nat.uadd_val hj1; simpa using this
      have hkg := ExprOps.vec_index_getElem? hkk
      have hpl : j.val < picks.val.length := by omega
      have hkx : picks.val[j.val] = kk := by
        rw [List.getElem?_eq_getElem hpl] at hkg; exact Option.some_injective _ hkg
      have hsplit : frontFrom ((picks.val.map (·.val)).drop j.val)
            (ds.val.map absDeclaration) ((ps.val.drop j.val).map absDeclaration)
          = ((ds.val.map absDeclaration)[kk.val]?).getD (absDeclaration ps.val[j.val])
            :: frontFrom ((picks.val.map (·.val)).drop (j.val + 1))
                 (ds.val.map absDeclaration)
                 ((ps.val.drop (j.val + 1)).map absDeclaration) := by
        rw [show (picks.val.map (·.val)).drop j.val
              = kk.val :: (picks.val.map (·.val)).drop (j.val + 1) from by
            rw [List.drop_eq_getElem_cons (by simpa using hpl), List.getElem_map, hkx],
          List.drop_eq_getElem_cons hlt, List.map_cons, frontFrom_cons]
      rw [ih j1 out1 v (by omega) (by omega) h, hj1v, hsplit]
      by_cases hk2 : kk.val < ds.val.length
      · rw [if_pos (show kk < alloc.vec.Vec.len ds by scalar_tac)] at hout1
        simp only [bind_eq_ok_iff] at hout1
        obtain ⟨d, hd, d1, hd1, hpush⟩ := hout1
        have hdg := ExprOps.vec_index_getElem? hd
        have hdx : ds.val[kk.val] = d := by
          rw [List.getElem?_eq_getElem hk2] at hdg; exact Option.some_injective _ hdg
        rw [vec_push_val hpush, declaration_dup_refines hd1,
          show (ds.val.map absDeclaration)[kk.val]? = some (absDeclaration d) from by
            rw [List.getElem?_map, List.getElem?_eq_getElem hk2, hdx]; rfl]
        simp
      · rw [if_neg (show ¬ kk < alloc.vec.Vec.len ds by scalar_tac)] at hout1
        simp only [bind_eq_ok_iff] at hout1
        obtain ⟨d, hd, d1, hd1, hpush⟩ := hout1
        have hdg := ExprOps.vec_index_getElem? hd
        have hdx : ps.val[j.val] = d := by
          rw [List.getElem?_eq_getElem hlt] at hdg; exact Option.some_injective _ hdg
        rw [vec_push_val hpush, declaration_dup_refines hd1,
          show (ds.val.map absDeclaration)[kk.val]? = none from by
            rw [List.getElem?_map,
              List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hk2)]
            rfl,
          hdx]
        simp
    · rw [if_neg (show ¬ j < alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      have hjeq : j.val = ps.val.length := by omega
      rw [← h, hjeq, List.drop_length, List.map_nil, frontFrom]
      simp

/-- `ConLeche/Frontend/Prepare.lean:126-135` — **`prepare::prepared_front`
refines the cited `acc.push (m.getD p)`**. -/
theorem prepared_front_refines {ps ds out v : alloc.vec.Vec env.Declaration}
    {picks : alloc.vec.Vec Std.Usize}
    (hlen : picks.val.length = ps.val.length)
    (h : frontend.prepare.prepared_front out ps ds picks = ok v) :
    v.val.map absDeclaration = out.val.map absDeclaration ++
      frontFrom (picks.val.map (·.val)) (ds.val.map absDeclaration)
        (ps.val.map absDeclaration) := by
  rw [frontend.prepare.prepared_front] at h
  have := prepared_front_loop_refines hlen ps.val.length 0#usize out v
    (by scalar_tac) (by scalar_tac) h
  simpa using this

/-- `ConLeche/Frontend/Prepare.lean:126-135`, `159-163` —
**`prepare::prepared_stream` refines the cited `front ++ rest`.** -/
theorem prepared_stream_refines {ps ds v : alloc.vec.Vec env.Declaration}
    {picks : alloc.vec.Vec Std.Usize} {picked : alloc.vec.Vec Bool}
    (hpicks : picks.val.length = ps.val.length)
    (hpicked : picked.val.length = ds.val.length)
    (h : frontend.prepare.prepared_stream ps ds picks picked = ok v) :
    v.val.map absDeclaration =
      frontFrom (picks.val.map (·.val)) (ds.val.map absDeclaration)
        (ps.val.map absDeclaration)
      ++ residual picked.val (ds.val.map absDeclaration) := by
  rw [frontend.prepare.prepared_stream] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨cap, -, front, hfront, h⟩ := h
  rw [prepared_rest_refines hpicked h,
    prepared_front_refines hpicks hfront]
  simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]


/-! ## The plan: `front_of` against `frontOf`

This is the one lemma the deviation of `prepare.rs`'s module note has to pay
for.  con-leche's `frontOf` carries the array `pick` has already erased from;
the port carries the original array and a mask.  `pick_residual_get` and
`pick_residual_set` say the two agree at every step, and the loop invariant
below is exactly "the array con-leche is holding is the port's residual". -/

/-- `ConLeche/Frontend/Prepare.lean:126-135` — `frontOf`'s accumulator only
prefixes: the front it builds from `acc` is `acc` followed by the front it
builds from nothing, and the residual array does not depend on `acc`. -/
private theorem frontOf_acc :
    ∀ (L : List ConLeche.Declaration) (acc ds : Array ConLeche.Declaration),
      (ConLeche.Frontend.frontOf acc L ds).1.toList
          = acc.toList ++ (ConLeche.Frontend.frontOf #[] L ds).1.toList
        ∧ (ConLeche.Frontend.frontOf acc L ds).2
          = (ConLeche.Frontend.frontOf #[] L ds).2
  | [], acc, ds => by
    rw [ConLeche.Frontend.frontOf, ConLeche.Frontend.frontOf]; simp
  | p :: ps, acc, ds => by
    rw [ConLeche.Frontend.frontOf, ConLeche.Frontend.frontOf]
    obtain ⟨h1, h2⟩ := frontOf_acc ps
      (acc.push (((ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey p) ds).1).getD p))
      (ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey p) ds).2
    obtain ⟨h1', h2'⟩ := frontOf_acc ps
      ((#[] : Array ConLeche.Declaration).push
        (((ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey p) ds).1).getD p))
      (ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey p) ds).2
    exact ⟨by rw [h1, h1']; simp, by rw [h2, h2']⟩

/-- `Array.findIdx` is `List.findIdx`. -/
private theorem array_findIdx_toList {α : Type} (a : Array α) (p : α → Bool) :
    a.findIdx p = a.toList.findIdx p := by rcases a with ⟨l⟩; simp

/-- `Array.eraseIdxIfInBounds` is `List.eraseIdx` — the out-of-range case is
"nothing is erased" on both sides. -/
private theorem toList_eraseIdxIfInBounds {α : Type} (a : Array α) (i : Nat) :
    (a.eraseIdxIfInBounds i).toList = a.toList.eraseIdx i := by
  unfold Array.eraseIdxIfInBounds
  split
  · simp
  · rename_i hge
    simp only [Nat.not_lt] at hge
    rw [List.eraseIdx_of_length_le (by simpa using hge)]

/-- `ConLeche/Frontend/Prepare.lean:126-135` — **`prepare::front_of`'s loop is
`frontOf`**: the mask's residual is the array con-leche is holding, the pick is
the same record, and the plan's entry is the index of it in the stream. -/
private theorem front_of_loop_refines {ps ds : alloc.vec.Vec env.Declaration}
    (hps : ∀ d ∈ ps.val, DeclarationWF d) (hds : ∀ d ∈ ds.val, DeclarationWF d) :
    ∀ k : Nat, ∀ (j : Std.Usize) (picked picked2 : alloc.vec.Vec Bool)
      (picks picks2 : alloc.vec.Vec Std.Usize) (res : Array ConLeche.Declaration),
      ps.val.length - j.val ≤ k → j.val ≤ ps.val.length →
      picked.val.length = ds.val.length →
      res.toList = residual picked.val (ds.val.map absDeclaration) →
      frontend.prepare.front_of_loop ps ds (alloc.vec.Vec.len ds) picked
          (alloc.vec.Vec.len ps) picks j = ok (picks2, picked2) →
      ∃ tail : List Std.Usize, picks2.val = picks.val ++ tail ∧
        tail.length = ps.val.length - j.val ∧
        picked2.val.length = ds.val.length ∧
        (ConLeche.Frontend.frontOf #[] ((ps.val.drop j.val).map absDeclaration) res).1.toList
          = frontFrom (tail.map (·.val)) (ds.val.map absDeclaration)
              ((ps.val.drop j.val).map absDeclaration) ∧
        (ConLeche.Frontend.frontOf #[] ((ps.val.drop j.val).map absDeclaration) res).2.toList
          = residual picked2.val (ds.val.map absDeclaration) := by
  have hmp : (alloc.vec.Vec.len ps).val = ps.val.length := alloc.vec.Vec.len_val ps
  have hmd : (alloc.vec.Vec.len ds).val = ds.val.length := alloc.vec.Vec.len_val ds
  intro k
  induction k with
  | zero =>
    intro j picked picked2 picks picks2 res hk hj hlen hres h
    have hjeq : j.val = ps.val.length := by omega
    rw [frontend.prepare.front_of_loop.eq_def] at h
    rw [if_neg (show ¬ j < alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
    have e1 : picks = picks2 := (congrArg Prod.fst h)
    have e2 : picked = picked2 := (congrArg Prod.snd h)
    subst e1; subst e2
    refine ⟨[], by simp, by simp; omega, hlen, ?_, ?_⟩
    · rw [hjeq, List.drop_length, List.map_nil, ConLeche.Frontend.frontOf]
      simp [frontFrom]
    · rw [hjeq, List.drop_length, List.map_nil, ConLeche.Frontend.frontOf]
      exact hres
  | succ k ih =>
    intro j picked picked2 picks picks2 res hk hj hlen hres h
    rw [frontend.prepare.front_of_loop.eq_def] at h
    by_cases hlt : j.val < ps.val.length
    · rw [if_pos (show j < alloc.vec.Vec.len ps by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨d, hd, n1, hn1, kk, hkk, picked1, hpicked1, picks1, hpicks1, j1, hj1, h⟩ := h
      have hj1v : j1.val = j.val + 1 := by have := Nat.uadd_val hj1; simpa using this
      have hdg := ExprOps.vec_index_getElem? hd
      have hdx : ps.val[j.val] = d := by
        rw [List.getElem?_eq_getElem hlt] at hdg; exact Option.some_injective _ hdg
      have hdwf : DeclarationWF d := hps _ (List.mem_of_getElem? hdg)
      obtain ⟨hkey, hkeywf⟩ := prelude_key_refines hdwf hn1
      have hkv := pick_idx_refines hkeywf hds hlen hkk
      -- the port's mask update is `List.set`, out of range included
      have hset : picked1.val = picked.val.set kk.val true := by
        by_cases hk2 : kk.val < ds.val.length
        · rw [if_pos (show kk < alloc.vec.Vec.len ds by scalar_tac)] at hpicked1
          obtain ⟨⟨b, f⟩, hf, hb⟩ := bind_eq_ok_iff.mp hpicked1
          obtain ⟨-, -, rfl⟩ := HashMap.vec_index_mut_eq hf
          rw [← Result.ok_injective hb]
          simp [alloc.vec.Vec.set]
        · rw [if_neg (show ¬ kk < alloc.vec.Vec.len ds by scalar_tac),
            Result.ok.injEq] at hpicked1
          rw [← hpicked1, List.set_eq_of_length_le (by omega)]
      have hlen1 : picked1.val.length = ds.val.length := by rw [hset]; simpa using hlen
      -- con-leche's `pick`, read through the residual
      set L := ds.val.map absDeclaration with hL
      set P := ConLeche.Frontend.declares (ConLeche.Frontend.preludeKey (absDeclaration d))
        with hP
      have hPn : P = ConLeche.Frontend.declares (absName n1) := by rw [hP, hkey]
      have hLlen : picked.val.length = L.length := by rw [hL]; simpa using hlen
      have harr : res.findIdx P = res.toList.findIdx P := array_findIdx_toList res P
      have hpickfst :
          (ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey (absDeclaration d)) res).1
            = L[kk.val]? := by
        rw [ConLeche.Frontend.pick]
        simp only []
        rw [show res[res.findIdx P]? = res.toList[res.toList.findIdx P]? from by
          rw [harr]; simp]
        rw [hres, ← pick_residual_get P picked.val L hLlen, hkv, hPn]
      have hpicksnd :
          ((ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey (absDeclaration d))
              res).2).toList = residual picked1.val L := by
        rw [ConLeche.Frontend.pick]
        simp only []
        rw [toList_eraseIdxIfInBounds, harr, hres,
          ← pick_residual_set P picked.val L hLlen, hset, hkv, hPn]
      obtain ⟨tail, htail, htaillen, hp2len, hfront, hrest⟩ :=
        ih j1 picked1 picked2 picks1 picks2
          (ConLeche.Frontend.pick (ConLeche.Frontend.preludeKey (absDeclaration d)) res).2
          (by omega) (by omega) hlen1 hpicksnd (by rw [hj1v] at *; exact h)
      refine ⟨kk :: tail, ?_, ?_, hp2len, ?_, ?_⟩
      · rw [htail, vec_push_val hpicks1]; simp
      · simp only [List.length_cons]; omega
      · rw [List.drop_eq_getElem_cons hlt, List.map_cons, hdx,
          ConLeche.Frontend.frontOf]
        rw [(frontOf_acc ((ps.val.drop (j.val + 1)).map absDeclaration) _ _).1]
        rw [show (ps.val.drop (j.val + 1)) = ps.val.drop j1.val from by rw [hj1v]]
        rw [hfront, List.map_cons, frontFrom_cons, hpickfst, hj1v]
        simp
      · rw [List.drop_eq_getElem_cons hlt, List.map_cons, hdx,
          ConLeche.Frontend.frontOf]
        rw [(frontOf_acc ((ps.val.drop (j.val + 1)).map absDeclaration) _ _).2]
        rw [show (ps.val.drop (j.val + 1)) = ps.val.drop j1.val from by rw [hj1v]]
        exact hrest
    · rw [if_neg (show ¬ j < alloc.vec.Vec.len ps by scalar_tac), Result.ok.injEq] at h
      have hjeq : j.val = ps.val.length := by omega
      have e1 : picks = picks2 := (congrArg Prod.fst h)
      have e2 : picked = picked2 := (congrArg Prod.snd h)
      subst e1; subst e2
      refine ⟨[], by simp, by simp; omega, hlen, ?_, ?_⟩
      · rw [hjeq, List.drop_length, List.map_nil, ConLeche.Frontend.frontOf]
        simp [frontFrom]
      · rw [hjeq, List.drop_length, List.map_nil, ConLeche.Frontend.frontOf]
        exact hres

/-- `ConLeche/Frontend/Prepare.lean:126-135` — **`prepare::front_of` refines
`frontOf`**: the plan the port computes materialises, through
`prepared_stream`, into exactly the front and the rest con-leche builds. -/
theorem front_of_refines {ps ds : alloc.vec.Vec env.Declaration}
    {picks : alloc.vec.Vec Std.Usize} {picked : alloc.vec.Vec Bool}
    (hps : ∀ d ∈ ps.val, DeclarationWF d) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.prepare.front_of ps ds = ok (picks, picked)) :
    picks.val.length = ps.val.length ∧ picked.val.length = ds.val.length ∧
      frontFrom (picks.val.map (·.val)) (ds.val.map absDeclaration)
          (ps.val.map absDeclaration)
        = (ConLeche.Frontend.frontOf #[] (ps.val.map absDeclaration)
            (ds.val.map absDeclaration).toArray).1.toList ∧
      residual picked.val (ds.val.map absDeclaration)
        = (ConLeche.Frontend.frontOf #[] (ps.val.map absDeclaration)
            (ds.val.map absDeclaration).toArray).2.toList := by
  rw [frontend.prepare.front_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨picked0, hpicked0, h⟩ := h
  have h0 : picked0.val = List.replicate (ds.val.length) false := by
    rw [no_picks_refines hpicked0, alloc.vec.Vec.len_val]
  have hres0 : (ds.val.map absDeclaration).toArray.toList
      = residual picked0.val (ds.val.map absDeclaration) := by
    rw [h0, List.toList_toArray,
      show ds.val.length = (ds.val.map absDeclaration).length from by simp,
      residual_replicate_false]
  obtain ⟨tail, htail, htaillen, hp2len, hfront, hrest⟩ :=
    front_of_loop_refines hps hds ps.val.length 0#usize picked0 picked
      (alloc.vec.Vec.with_capacity Std.Usize (alloc.vec.Vec.len ps)) picks
      (ds.val.map absDeclaration).toArray (by scalar_tac) (by scalar_tac)
      (by rw [h0]; simp) hres0 h
  have hpickseq : picks.val = tail := by
    rw [htail]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  refine ⟨by rw [hpickseq, htaillen]; simp, hp2len, ?_, ?_⟩
  · rw [hpickseq]
    have := hfront
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
    exact this.symm
  · have := hrest
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
    exact this.symm


/-! ## The capstone

`prepare::prepare_d` is `prepareD` and `prepare::prepare_prelude` is
`preparePrelude`.  The hoist enters as a hypothesis, `HoistSpec` — see the
section after this one for what is proved of it and what is not. -/

/-- **The residue of this file** (the `Refine/IndSpec.lean` pattern): the
hoist's own refinement, which `hoist_nat_op_ground_refines` below discharges
from `HoistTargetsSpec`. -/
structure HoistSpec : Prop where
  /-- `ConLeche/Frontend/NatOpGround.lean:164-169` — the port's hoist reorders
  the stream the way `hoistNatOpGround` does. -/
  hoist : ∀ {ds : alloc.vec.Vec env.Declaration}
    {r : (alloc.vec.Vec env.Declaration) × (alloc.vec.Vec name.Name)},
    (∀ d ∈ ds.val, DeclarationWF d) →
    frontend.nat_op_ground.hoist_nat_op_ground ds = ok r →
    absDecls r.1 = (ConLeche.Frontend.hoistNatOpGround (absDecls ds).toArray).1.toList

/-- `ConLeche/Frontend/Prepare.lean:159-163` — `prepareD`'s records, with its
two `let (a, b) := …` destructurings resolved (structure eta). -/
private theorem prepareD_decls (pre : ConLeche.Frontend.PreludeIx)
    (ds : Array ConLeche.Declaration) :
    (ConLeche.Frontend.prepareD pre ds).decls
      = (ConLeche.Frontend.hoistNatOpGround
          ((ConLeche.Frontend.frontOf #[] pre.decls.toList ds).1
            ++ (ConLeche.Frontend.frontOf #[] pre.decls.toList ds).2)).1 := rfl

/-- `ConLeche/Frontend/Prepare.lean:159-163` — **`prepare::prepare_d` refines
`prepareD`**: the prepared records.  The other two fields are the driver's
receipts (a count and the hoisted names) and no verdict reads them. -/
theorem prepare_d_refines (hspec : HoistSpec) {pre : frontend.prepare.PreludeIx}
    {ds : alloc.vec.Vec env.Declaration} {p : frontend.prepare.Prepared}
    (hpre : PreludeIxWF pre) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.prepare.prepare_d pre ds = ok p) :
    absDecls p.decls
      = (ConLeche.Frontend.prepareD (absPreludeIx pre) (absDecls ds).toArray).decls.toList := by
  rw [frontend.prepare.prepare_d] at h
  obtain ⟨⟨picks, picked⟩, hplan, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨all, hall, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨out, names⟩, hhoist, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i1, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨syn, -, h⟩ := bind_eq_ok_iff.mp h
  have hp := Result.ok_injective h
  subst hp
  obtain ⟨hpl, hml, hfront, hrest⟩ := front_of_refines hpre hds hplan
  have hallabs : absDecls all
      = (ConLeche.Frontend.frontOf #[] (absDecls pre.decls) (absDecls ds).toArray).1.toList
        ++ (ConLeche.Frontend.frontOf #[] (absDecls pre.decls)
              (absDecls ds).toArray).2.toList := by
    simp only [absDecls]
    rw [prepared_stream_refines hpl hml hall, hfront, hrest]
  have hallwf : ∀ d ∈ all.val, DeclarationWF d := prepared_stream_wf hpre hds hall
  have hkey : (absPreludeIx pre).decls.toList = absDecls pre.decls := by
    rw [absPreludeIx, List.toList_toArray]
  have harr : (ConLeche.Frontend.frontOf #[] (absPreludeIx pre).decls.toList
        (absDecls ds).toArray).1
      ++ (ConLeche.Frontend.frontOf #[] (absPreludeIx pre).decls.toList
        (absDecls ds).toArray).2
      = (absDecls all).toArray := by
    refine Array.ext' ?_
    rw [Array.toList_append, List.toList_toArray, hallabs, hkey]
  rw [prepareD_decls, harr]
  exact hspec.hoist hallwf hhoist

/-- `ConLeche/Frontend/Prepare.lean:165-172` — **`prepare::prepare_prelude`
refines `preparePrelude`**: the parsed stream, prepared for the fold, is
con-leche's prepared stream record for record and in the same order.  This is
what task #87's headline composes with. -/
theorem prepare_prelude_refines (hspec : HoistSpec) {pre : frontend.prepare.PreludeIx}
    {ds out : alloc.vec.Vec env.Declaration}
    (hpre : PreludeIxWF pre) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.prepare.prepare_prelude pre ds = ok out) :
    absDecls out
      = (ConLeche.Frontend.preparePrelude (absPreludeIx pre) (absDecls ds).toArray).toList := by
  rw [frontend.prepare.prepare_prelude] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨p, hp, hout⟩ := h
  rw [← hout, ConLeche.Frontend.preparePrelude]
  exact prepare_d_refines hspec hpre hds hp


end ConRon.Refine.Frontend
