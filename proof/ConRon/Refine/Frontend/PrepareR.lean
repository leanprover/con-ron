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

## What is proved

Everything of `prepare.rs` — `prelude_ix_empty`, `prelude_key`, `declares`,
`pick_idx`, `no_picks`, `front_of` (against `frontOf`/`pick`, **not** against
`frontSpec`/`pickSpec`, which the port deliberately does not port: DESIGN.md
task #84 §7), `prepared_front`, `prepared_rest`, `prepared_stream`,
`prepare_d` and the capstone `prepare_prelude_refines` — and everything of
`nat_op_ground.rs`: `used_consts_go`, `decl_used_consts`, `block_used_consts`,
`is_nat_op_record`, `hoist_name_index`, `idx_get`, `hoist_targets`,
`hoist_targets_at`, `hoist_targets_one`, `hoist_close`, `hoist_close_step`,
`hoist_push_deps`, `hoist_push_dep`, `target_done`, `target_is`,
`hoist_moved_idxs`, `hoist_order_at`, `hoist_order`, `hoist_reorder`,
`hoist_moved_names`, `apply_hoist` and `hoist_nat_op_ground`.  (`declaration_dup` and `block_copy` are phase 1's
`Frontend/Prepare.lean`: the copy *is* the record, so its refinement is that
file's `declaration_dup_refines`.)

**Nothing is left over.**  The file's one-time hypothesis `HoistSpec` (that
`hoist_targets` computes `hoistTargets`) is the theorem `hoist_targets_refines`,
so the capstone `prepare_prelude_refines` asks for well-formedness of its input
and nothing else.

## `sorry` count in this file: 0
-/
import Init.Internal.Order.While
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



/-! ## The hoist

`nat_op_ground::hoist_nat_op_ground` computes a permutation of the stream's
positions and applies it.  The permutation is a `ron::HashMap<u64, u64>` where
con-leche's is a `Std.HashMap Nat Nat`; `HoistTargetRel` is the bridge, and
`HoistBounded` is what the map's own producer guarantees and `applyHoist`'s
`mergeSort` needs: every key and every value is a position of the stream.
(Without it the two sides genuinely differ — the port's bucket pass drops a
record whose target is past the end, while `mergeSort` keeps it.  `hoistTargets`
only ever stores `target[k] = i` with `k`, `i < ds.size`, so the hypothesis is
free at the one call site.) -/

/-- The target map's `Hashable` dictionary. -/
private abbrev tgtHashable := U64.Insts.Con_ron_coreRonHashmapHashable
/-- The target map's `Eq2` dictionary: `u64`'s `==`, which is exact and total,
so the `Eq2Spec` of `Refine/HashMap.lean` holds outright (unlike at a `Name`
key — `Refine/HashMapWF.lean`'s note). -/
private abbrev tgtEq2 := U64.Insts.Con_ron_coreRonHashmapEq2

private theorem tgt_eq2_spec : HashMap.Eq2Spec tgtEq2 := by intro a b; rfl

/-- `nat_op_ground`'s target map: the port's `ron::HashMap<u64,u64>` denotes
con-leche's `Std.HashMap Nat Nat`. -/
structure HoistTargetRel (t : ron.hashmap.HashMap Std.U64 Std.U64)
    (s : _root_.Std.HashMap Nat Nat) : Prop where
  /-- the port's own hash-table invariant (task #16's `Inv`), which a probe
  needs and no abstraction can supply -/
  inv : HashMap.Inv tgtHashable t
  /-- key for key -/
  get : ∀ k : Std.U64, (HashMap.toFun t k).map (·.val) = s[k.val]?
  /-- and the same number of them, which is what `hoist_nat_op_ground`'s
  `target.len() == 0` reads as `target.isEmpty` -/
  size : (HashMap.al_v t).length = s.size

/-- Every key and every value of the target map is a position of the stream. -/
def HoistBounded (s : _root_.Std.HashMap Nat Nat) (n : Nat) : Prop :=
  ∀ k t, s[k]? = some t → k < n ∧ t < n

/-- `ConLeche/Frontend/NatOpGround.lean:150-162` — `applyHoist`'s sort key (the
cited `let key`). -/
private def hoistKey (s : _root_.Std.HashMap Nat Nat) (k : Nat) : Nat × Nat × Nat :=
  match s[k]? with
  | some t => (t, 0, k)
  | none => (k, 1, k)

/-- `ConLeche/Frontend/NatOpGround.lean:150-162` — `applyHoist`'s strict order
(the cited `let lt`). -/
private def hoistLt (s : _root_.Std.HashMap Nat Nat) (a b : Nat) : Bool :=
  let (ta, sa, ka) := hoistKey s a
  let (tb, sb, kb) := hoistKey s b
  ta < tb || (ta == tb && (sa < sb || (sa == sb && ka < kb)))

/-- `applyHoist`'s records, its `let`s resolved. -/
private theorem applyHoist_fst (ds : Array ConLeche.Declaration)
    (s : _root_.Std.HashMap Nat Nat) :
    (ConLeche.Frontend.applyHoist ds s).1
      = (((List.range ds.size).mergeSort
          (fun a b => !hoistLt s b a)).map (fun k => ds[k]!)).toArray := rfl

/-- `applyHoist`'s receipt, its `let`s resolved. -/
private theorem applyHoist_snd (ds : Array ConLeche.Declaration)
    (s : _root_.Std.HashMap Nat Nat) :
    (ConLeche.Frontend.applyHoist ds s).2
      = ((Array.range ds.size).filter (fun k => s.contains k)).flatMap
          (fun k => (ConLeche.Declaration.names ds[k]!).toArray) := rfl

/-! ### The moved records' indices -/

/-- `ConLeche/Frontend/NatOpGround.lean:161` — `nat_op_ground::hoist_moved_idxs`'
loop: the cited `(Array.range ds.size).filter (target.contains ·)` from `k`
on. -/
private theorem hoist_moved_idxs_loop_refines
    {target : ron.hashmap.HashMap Std.U64 Std.U64} {s : _root_.Std.HashMap Nat Nat}
    {n : Std.Usize} (hrel : HoistTargetRel target s) :
    ∀ f : Nat, ∀ (k : Std.Usize) (out v : alloc.vec.Vec Std.U64),
      n.val - k.val ≤ f → k.val ≤ n.val →
      frontend.nat_op_ground.hoist_moved_idxs_loop n target out k = ok v →
      v.val.map (·.val) = out.val.map (·.val)
        ++ (List.range' k.val (n.val - k.val)).filter (fun j => s.contains j) := by
  intro f
  induction f with
  | zero =>
    intro k out v hf hk h
    rw [frontend.nat_op_ground.hoist_moved_idxs_loop.eq_def] at h
    rw [if_neg (show ¬ k < n by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n.val - k.val = 0 by omega]
    simp
  | succ f ih =>
    intro k out v hf hk h
    rw [frontend.nat_op_ground.hoist_moved_idxs_loop.eq_def] at h
    by_cases hlt : k.val < n.val
    · rw [if_pos (show k < n by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq] at h
      obtain ⟨kk, hkk, b, hb, out1, hout1, k1, hk1, h⟩ := h
      have hk1v : k1.val = k.val + 1 := by have := Nat.uadd_val hk1; simpa using this
      have hkkv : kk.val = k.val := by
        rw [← Result.ok_injective hkk]; exact Env.usize_cast_u64_val k
      have hbv : b = s.contains k.val := by
        rw [HashMap.contains_key_refines tgt_eq2_spec hrel.inv hb]
        have := hrel.get kk
        rw [hkkv] at this
        rw [_root_.Std.HashMap.contains_eq_isSome_getElem?, ← this]
        simp
      rw [ih k1 out1 v (by omega) (by omega) h, hk1v]
      rw [show n.val - k.val = (n.val - (k.val + 1)) + 1 by omega, List.range'_succ,
        List.filter_cons]
      by_cases hbb : b = true
      · subst hbb
        simp only [reduceIte, bind_eq_ok_iff] at hout1
        obtain ⟨kk2, hkk2, hpush⟩ := hout1
        have hkk2v : kk2.val = k.val := by
          rw [← Result.ok_injective hkk2]; exact Env.usize_cast_u64_val k
        rw [vec_push_val hpush, if_pos (by rw [← hbv])]
        simp [hkk2v]
      · simp only [Bool.not_eq_true] at hbb
        subst hbb
        simp only [Bool.false_eq_true, reduceIte, Result.ok.injEq] at hout1
        rw [← hout1, if_neg (by rw [← hbv]; simp)]
    · rw [if_neg (show ¬ k < n by scalar_tac), Result.ok.injEq] at h
      rw [← h, show n.val - k.val = 0 by omega]
      simp

/-- `ConLeche/Frontend/NatOpGround.lean:161` — **`nat_op_ground::hoist_moved_idxs`
refines the cited `(Array.range ds.size).filter (target.contains ·)`.** -/
theorem hoist_moved_idxs_refines {target : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {n : Std.Usize} {v : alloc.vec.Vec Std.U64}
    (hrel : HoistTargetRel target s)
    (h : frontend.nat_op_ground.hoist_moved_idxs n target = ok v) :
    v.val.map (·.val) = (List.range n.val).filter (fun j => s.contains j) := by
  rw [frontend.nat_op_ground.hoist_moved_idxs] at h
  have := hoist_moved_idxs_loop_refines hrel n.val 0#usize _ v (by scalar_tac)
    (by scalar_tac) h
  simpa [List.range_eq_range', alloc.vec.Vec.new] using this

/-! ### Applying the order -/

/-- `ConLeche/Frontend/NatOpGround.lean:162` — `nat_op_ground::hoist_reorder`'s
loop: the cited `order.map (ds[·]!)` from `i` on.  The port's `Vec` read fails
out of range where con-leche's `ds[k]!` answers the default, so the forward
shape claims nothing there. -/
private theorem hoist_reorder_loop_refines {ds : alloc.vec.Vec env.Declaration}
    {order : alloc.vec.Vec Std.U64}
    (horder : ∀ k ∈ order.val, k.val ≤ Std.Usize.max) :
    ∀ f : Nat, ∀ (i : Std.Usize) (out v : alloc.vec.Vec env.Declaration),
      order.val.length - i.val ≤ f → i.val ≤ order.val.length →
      frontend.nat_op_ground.hoist_reorder_loop ds order (alloc.vec.Vec.len order)
          out i = ok v →
      v.val.map absDeclaration = out.val.map absDeclaration
        ++ ((order.val.drop i.val).map (·.val)).map
             (fun k => (ds.val.map absDeclaration)[k]!) := by
  have hmo : (alloc.vec.Vec.len order).val = order.val.length :=
    alloc.vec.Vec.len_val order
  intro f
  induction f with
  | zero =>
    intro i out v hf hi h
    have hieq : i.val = order.val.length := by omega
    rw [frontend.nat_op_ground.hoist_reorder_loop.eq_def] at h
    rw [if_neg (show ¬ i < alloc.vec.Vec.len order by scalar_tac), Result.ok.injEq] at h
    rw [← h, hieq, List.drop_length]
    simp
  | succ f ih =>
    intro i out v hf hi h
    rw [frontend.nat_op_ground.hoist_reorder_loop.eq_def] at h
    by_cases hlt : i.val < order.val.length
    · rw [if_pos (show i < alloc.vec.Vec.len order by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq] at h
      obtain ⟨kk, hkk, kw, hkw, d, hd, d1, hd1, out1, hout1, i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
      have hkg := ExprOps.vec_index_getElem? hkk
      have hkx : order.val[i.val] = kk := by
        rw [List.getElem?_eq_getElem hlt] at hkg; exact Option.some_injective _ hkg
      have hkwv : kw.val = kk.val := by
        rw [← Result.ok_injective hkw]
        exact Env.u64_cast_usize_val (horder kk (by rw [← hkx]; exact List.getElem_mem hlt))
      have hdg := ExprOps.vec_index_getElem? hd
      have hdlt : kw.val < ds.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hdg
        simp at hdg
      have hdx : ds.val[kw.val] = d := by
        rw [List.getElem?_eq_getElem hdlt] at hdg; exact Option.some_injective _ hdg
      rw [ih i1 out1 v (by omega) (by omega) h, hi1v,
        List.drop_eq_getElem_cons hlt, hkx, vec_push_val hout1,
        declaration_dup_refines hd1]
      simp only [List.map_cons, List.map_append]
      rw [show (ds.val.map absDeclaration)[kk.val]! = absDeclaration d from by
        rw [← hkwv, getElem!_pos _ _ (by simpa using hdlt), List.getElem_map, hdx]]
      simp
    · rw [if_neg (show ¬ i < alloc.vec.Vec.len order by scalar_tac), Result.ok.injEq] at h
      have hieq : i.val = order.val.length := by omega
      rw [← h, hieq, List.drop_length]
      simp

/-- `ConLeche/Frontend/NatOpGround.lean:162` — **`nat_op_ground::hoist_reorder`
refines the cited `(order.map (ds[·]!)).toArray`.** -/
theorem hoist_reorder_refines {ds v : alloc.vec.Vec env.Declaration}
    {order : alloc.vec.Vec Std.U64}
    (horder : ∀ k ∈ order.val, k.val ≤ Std.Usize.max)
    (h : frontend.nat_op_ground.hoist_reorder ds order = ok v) :
    absDecls v = (order.val.map (·.val)).map
      (fun k => (ds.val.map absDeclaration)[k]!) := by
  rw [frontend.nat_op_ground.hoist_reorder] at h
  have := hoist_reorder_loop_refines horder order.val.length 0#usize _ v (by scalar_tac)
    (by scalar_tac) h
  simpa [absDecls, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using this

/-! ### The two owning probes, and the bucket pass -/

/-- `ConLeche/Frontend/NatOpGround.lean:129-131` — **`nat_op_ground::target_done`
refines the cited `match target[k]? with | some t => if t ≤ i then continue |
none => pure ()`**: "`k` is already targeted at `i` or earlier". -/
theorem target_done_refines {target : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {k i : Std.U64} {b : Bool}
    (hrel : HoistTargetRel target s)
    (h : frontend.nat_op_ground.target_done target k i = ok b) :
    b = (match s[k.val]? with | some t => decide (t ≤ i.val) | none => false) := by
  rw [frontend.nat_op_ground.target_done] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, hb⟩ := h
  rw [HashMap.get_refines tgt_eq2_spec hrel.inv hget] at hb
  have hk := hrel.get k
  cases ho : HashMap.toFun target k with
  | none =>
    rw [ho] at hb hk
    simp only [Option.map_none] at hk
    rw [← hk]
    simp at hb
    rw [← hb]
  | some t =>
    rw [ho] at hb hk
    simp only [Option.map_some] at hk
    rw [← hk]
    simp only [Result.ok.injEq] at hb
    rw [← hb]
    simp

/-- `ConLeche/Frontend/NatOpGround.lean:152-155` — **`nat_op_ground::target_is`
refines the cited `key`'s `target[k]? = some t` test**: the bucket pass's
owning probe. -/
theorem target_is_refines {target : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {k t : Std.U64} {b : Bool}
    (hrel : HoistTargetRel target s)
    (h : frontend.nat_op_ground.target_is target k t = ok b) :
    b = decide (s[k.val]? = some t.val) := by
  rw [frontend.nat_op_ground.target_is] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, hb⟩ := h
  rw [HashMap.get_refines tgt_eq2_spec hrel.inv hget] at hb
  have hk := hrel.get k
  cases ho : HashMap.toFun target k with
  | none =>
    rw [ho] at hb hk
    simp only [Option.map_none] at hk
    rw [← hk]
    simp only [Result.ok.injEq] at hb
    rw [← hb]
    simp
  | some tt =>
    rw [ho] at hb hk
    simp only [Option.map_some] at hk
    rw [← hk]
    simp only [Result.ok.injEq] at hb
    rw [← hb]
    simp only [Option.some.injEq, decide_eq_decide]
    exact ⟨fun hc => by rw [hc], fun hc => Env.u64_val_inj hc⟩

/-- `ConLeche/Frontend/NatOpGround.lean:150-162` — the port's bucket pass, as a
list: at each position `t`, first the moved records targeted at `t` (increasing
original index, which is dependency order), then the record `t` itself unless
it is one of them.  `applyHoist` gets the same order out of a `mergeSort` on
the key `(t, s, k)`; that the two agree is `hoistBuckets_eq_mergeSort`. -/
private def bucketAt (s : _root_.Std.HashMap Nat Nat) (moved : List Nat)
    (t : Nat) : List Nat :=
  (moved.filter (fun k => decide (s[k]? = some t)))
    ++ (if s.contains t then [] else [t])

private def hoistBuckets (s : _root_.Std.HashMap Nat Nat) (moved : List Nat)
    (n : Nat) : List Nat :=
  (List.range n).flatMap (bucketAt s moved)

/-- `ConLeche/Frontend/NatOpGround.lean:150-162` — `nat_op_ground::hoist_order_at`'s
loop: one bucket's moved records. -/
private theorem hoist_order_at_loop_refines
    {target : ron.hashmap.HashMap Std.U64 Std.U64} {s : _root_.Std.HashMap Nat Nat}
    {moved : alloc.vec.Vec Std.U64} {t : Std.U64} (hrel : HoistTargetRel target s) :
    ∀ f : Nat, ∀ (a : Std.Usize) (order v : alloc.vec.Vec Std.U64),
      moved.val.length - a.val ≤ f → a.val ≤ moved.val.length →
      frontend.nat_op_ground.hoist_order_at_loop target moved t order
          (alloc.vec.Vec.len moved) a = ok v →
      v.val.map (·.val) = order.val.map (·.val)
        ++ ((moved.val.drop a.val).map (·.val)).filter
             (fun k => decide (s[k]? = some t.val)) := by
  have hm : (alloc.vec.Vec.len moved).val = moved.val.length :=
    alloc.vec.Vec.len_val moved
  intro f
  induction f with
  | zero =>
    intro a order v hf ha h
    have haeq : a.val = moved.val.length := by omega
    rw [frontend.nat_op_ground.hoist_order_at_loop.eq_def] at h
    rw [if_neg (show ¬ a < alloc.vec.Vec.len moved by scalar_tac), Result.ok.injEq] at h
    rw [← h, haeq, List.drop_length]; simp
  | succ f ih =>
    intro a order v hf ha h
    rw [frontend.nat_op_ground.hoist_order_at_loop.eq_def] at h
    by_cases hlt : a.val < moved.val.length
    · rw [if_pos (show a < alloc.vec.Vec.len moved by scalar_tac)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨kk, hkk, b, hb, order1, horder1, a1, ha1, h⟩ := h
      have ha1v : a1.val = a.val + 1 := by have := Nat.uadd_val ha1; simpa using this
      have hkg := ExprOps.vec_index_getElem? hkk
      have hkx : moved.val[a.val] = kk := by
        rw [List.getElem?_eq_getElem hlt] at hkg; exact Option.some_injective _ hkg
      have hbv := target_is_refines hrel hb
      rw [ih a1 order1 v (by omega) (by omega) h, ha1v,
        List.drop_eq_getElem_cons hlt, hkx]
      simp only [List.map_cons, List.filter_cons]
      by_cases hbb : b = true
      · subst hbb
        rw [if_pos (by rw [← hbv]), vec_push_val horder1]
        simp
      · simp only [Bool.not_eq_true] at hbb
        subst hbb
        simp only [Bool.false_eq_true, reduceIte, Result.ok.injEq] at horder1
        rw [← horder1, if_neg (by rw [← hbv]; simp)]
    · rw [if_neg (show ¬ a < alloc.vec.Vec.len moved by scalar_tac), Result.ok.injEq] at h
      have haeq : a.val = moved.val.length := by omega
      rw [← h, haeq, List.drop_length]; simp

/-- `ConLeche/Frontend/NatOpGround.lean:150-162` — **`nat_op_ground::hoist_order_at`
is one bucket's `s = 0` half**: the moved records whose target is `t`, in
increasing original index. -/
theorem hoist_order_at_refines {target : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {moved order v : alloc.vec.Vec Std.U64}
    {t : Std.U64} (hrel : HoistTargetRel target s)
    (h : frontend.nat_op_ground.hoist_order_at order target moved t = ok v) :
    v.val.map (·.val) = order.val.map (·.val)
      ++ (moved.val.map (·.val)).filter (fun k => decide (s[k]? = some t.val)) := by
  rw [frontend.nat_op_ground.hoist_order_at] at h
  have := hoist_order_at_loop_refines hrel moved.val.length 0#usize order v
    (by scalar_tac) (by scalar_tac) h
  simpa using this

/-- `ConLeche/Frontend/NatOpGround.lean:150-162` — `nat_op_ground::hoist_order`'s
loop: the buckets from `t` on. -/
private theorem hoist_order_loop_refines
    {target : ron.hashmap.HashMap Std.U64 Std.U64} {s : _root_.Std.HashMap Nat Nat}
    {moved : alloc.vec.Vec Std.U64} {n : Std.Usize} (hrel : HoistTargetRel target s) :
    ∀ f : Nat, ∀ (t : Std.Usize) (order v : alloc.vec.Vec Std.U64),
      n.val - t.val ≤ f → t.val ≤ n.val →
      frontend.nat_op_ground.hoist_order_loop n target moved order t = ok v →
      v.val.map (·.val) = order.val.map (·.val)
        ++ (List.range' t.val (n.val - t.val)).flatMap
             (bucketAt s (moved.val.map (·.val))) := by
  intro f
  induction f with
  | zero =>
    intro t order v hf ht h
    rw [frontend.nat_op_ground.hoist_order_loop.eq_def] at h
    rw [if_neg (show ¬ t < n by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n.val - t.val = 0 by omega]; simp
  | succ f ih =>
    intro t order v hf ht h
    rw [frontend.nat_op_ground.hoist_order_loop.eq_def] at h
    by_cases hlt : t.val < n.val
    · rw [if_pos (show t < n by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq] at h
      obtain ⟨t1, ht1, order1, horder1, t2, ht2, b, hb, order2, horder2, t3, ht3, h⟩ := h
      have ht1v : t1.val = t.val := by
        rw [← Result.ok_injective ht1]; exact Env.usize_cast_u64_val t
      have ht2v : t2.val = t.val := by
        rw [← Result.ok_injective ht2]; exact Env.usize_cast_u64_val t
      have ht3v : t3.val = t.val + 1 := by have := Nat.uadd_val ht3; simpa using this
      have hbv : b = s.contains t.val := by
        rw [HashMap.contains_key_refines tgt_eq2_spec hrel.inv hb]
        have := hrel.get t2
        rw [ht2v] at this
        rw [_root_.Std.HashMap.contains_eq_isSome_getElem?, ← this]
        simp
      have h1 := hoist_order_at_refines hrel horder1
      rw [ht1v] at h1
      rw [ih t3 order2 v (by omega) (by omega) h, ht3v]
      rw [show n.val - t.val = (n.val - (t.val + 1)) + 1 by omega, List.range'_succ,
        List.flatMap_cons, bucketAt]
      by_cases hbb : b = true
      · subst hbb
        rw [if_pos rfl, Result.ok.injEq] at horder2
        rw [← horder2, h1, if_pos (by rw [← hbv])]
        simp
      · simp only [Bool.not_eq_true] at hbb
        subst hbb
        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at horder2
        obtain ⟨t4, ht4, hpush⟩ := horder2
        have ht4v : t4.val = t.val := by
          rw [← Result.ok_injective ht4]; exact Env.usize_cast_u64_val t
        rw [vec_push_val hpush]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [h1, if_neg (by rw [← hbv]; simp)]
        simp [ht4v]
    · rw [if_neg (show ¬ t < n by scalar_tac), Result.ok.injEq] at h
      rw [← h, show n.val - t.val = 0 by omega]; simp

/-- `ConLeche/Frontend/NatOpGround.lean:150-162` — **`nat_op_ground::hoist_order`
is the bucket pass**: `hoistBuckets`, position by position. -/
theorem hoist_order_refines {target : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {moved v : alloc.vec.Vec Std.U64}
    {n : Std.Usize} (hrel : HoistTargetRel target s)
    (h : frontend.nat_op_ground.hoist_order n target moved = ok v) :
    v.val.map (·.val) = hoistBuckets s (moved.val.map (·.val)) n.val := by
  rw [frontend.nat_op_ground.hoist_order] at h
  have := hoist_order_loop_refines hrel n.val 0#usize _ v (by scalar_tac)
    (by scalar_tac) h
  simpa [hoistBuckets, List.range_eq_range', alloc.vec.Vec.with_capacity,
    alloc.vec.Vec.new] using this

/-! ### The name index's probe

`nat_op_ground::idx_get` is task #13's *owning* probe of the name index: it
answers a `u64`, not a borrow into the map (AENEAS_FINDINGS §2.1 F1).
con-leche writes the index inline in `hoistTargets`' `Id.run do`, so there is
no Lean function to cite; the probe is therefore stated against the map
`HoistIdxRel` says the port is holding. -/

/-- The name index's `Hashable` dictionary. -/
private abbrev idxHashable := name.Name.Insts.Con_ron_coreRonHashmapHashable
/-- The name index's `Eq2` dictionary: the port's own `name::beq`. -/
private abbrev idxEq2 := name.Name.Insts.Con_ron_coreRonHashmapEq2

/-- `name::beq` never lies about well-formed names — `Refine/HashMapWF.lean`'s
hypothesis, discharged (the same one-liner as `Refine/FEnv.lean`'s
`name_eq2_fwd`, which this file does not import). -/
private theorem idx_eq2_fwd : HashMap.Eq2Fwd idxEq2 NameWF := by
  intro a b c ha hb h
  have h' : name.beq a b = ok c := h
  rw [Name.beq_refines ha hb h']
  exact decide_eq_decide.mpr
    ⟨fun hc => Name.absName_injective ha hb hc, fun hc => by rw [hc]⟩

/-- `ConLeche/Frontend/NatOpGround.lean:112-116` — `hoistTargets`' name index:
the port's `ron::HashMap<Name, u64>` denotes con-leche's
`Std.HashMap Name Nat`. -/
structure HoistIdxRel (idx : ron.hashmap.HashMap name.Name Std.U64)
    (s : _root_.Std.HashMap ConLeche.Name Nat) : Prop where
  /-- the port's own hash-table invariant -/
  inv : HashMap.Inv idxHashable idx
  /-- every key it holds is a name a smart constructor built, without which
  `name::beq` is not exact -/
  keys : HashMap.KeysOk NameWF idx
  /-- name for name -/
  get : ∀ n, NameWF n → (HashMap.toFun idx n).map (·.val) = s[absName n]?

/-- `ConLeche/Frontend/NatOpGround.lean:121`, `:134` — **`nat_op_ground::idx_get`
refines the cited `idx[g]?`.** -/
theorem idx_get_refines {idx : ron.hashmap.HashMap name.Name Std.U64}
    {s : _root_.Std.HashMap ConLeche.Name Nat} {n : name.Name} {o : Option Std.U64}
    (hrel : HoistIdxRel idx s) (hn : NameWF n)
    (h : frontend.nat_op_ground.idx_get idx n = ok o) :
    o.map (·.val) = s[absName n]? := by
  rw [frontend.nat_op_ground.idx_get] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hget, ho⟩ := h
  rw [HashMap.get_refines_wf idx_eq2_fwd hrel.inv hrel.keys hn hget] at ho
  rw [← hrel.get n hn]
  cases hr : HashMap.toFun idx n with
  | none => rw [hr] at ho; simp only [Result.ok.injEq] at ho; rw [← ho]
  | some x => rw [hr] at ho; simp only [Result.ok.injEq] at ho; rw [← ho]

/-! ### The bucket pass *is* the sort

`applyHoist` sorts `List.range ds.size` by the key `(t, s, k)`; the port walks
the positions and emits each bucket in turn.  The keys are pairwise distinct
(each carries its own index in its third component), so there is exactly one
sorted permutation and the two lists are equal.  This discharges what was
what was `HoistSpec.order`. -/

/-- The sort key's strict order, as a `Prop`. -/
private def keyLt (p q : Nat × Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ (p.2.1 < q.2.1 ∨ (p.2.1 = q.2.1 ∧ p.2.2 < q.2.2)))

private theorem hoistLt_iff (s : _root_.Std.HashMap Nat Nat) (a b : Nat) :
    hoistLt s a b = true ↔ keyLt (hoistKey s a) (hoistKey s b) := by
  rcases ha : s[a]? with _ | ta <;> rcases hb : s[b]? with _ | tb <;>
    simp [hoistLt, hoistKey, ha, hb, keyLt]

private theorem hoistKey_some {s : _root_.Std.HashMap Nat Nat} {k t : Nat}
    (h : s[k]? = some t) : hoistKey s k = (t, 0, k) := by simp [hoistKey, h]

private theorem hoistKey_none {s : _root_.Std.HashMap Nat Nat} {k : Nat}
    (h : s[k]? = none) : hoistKey s k = (k, 1, k) := by simp [hoistKey, h]

/-- The key's third component is the index itself, which is what makes the
keys pairwise distinct. -/
private theorem hoistKey_third (s : _root_.Std.HashMap Nat Nat) (k : Nat) :
    (hoistKey s k).2.2 = k := by
  rw [hoistKey]; rcases s[k]? with _ | t <;> rfl

private theorem keyLt_irrefl {p : Nat × Nat × Nat} : ¬ keyLt p p := by
  rw [keyLt]; omega

private theorem keyLt_trans {p q r : Nat × Nat × Nat} (h1 : keyLt p q) (h2 : keyLt q r) :
    keyLt p r := by
  rw [keyLt] at h1 h2 ⊢; omega

private theorem keyLt_total (s : _root_.Std.HashMap Nat Nat) {a b : Nat} (h : a ≠ b) :
    keyLt (hoistKey s a) (hoistKey s b) ∨ keyLt (hoistKey s b) (hoistKey s a) := by
  have ha := hoistKey_third s a
  have hb := hoistKey_third s b
  rw [keyLt, keyLt]
  omega

/-- The comparison `applyHoist` sorts by: "not strictly after". -/
private theorem hle_iff (s : _root_.Std.HashMap Nat Nat) (a b : Nat) :
    (!hoistLt s b a) = true ↔ ¬ keyLt (hoistKey s b) (hoistKey s a) := by
  rw [Bool.not_eq_true', ← hoistLt_iff, Bool.not_eq_true]

private theorem hle_trans (s : _root_.Std.HashMap Nat Nat) (a b c : Nat)
    (h1 : (!hoistLt s b a) = true) (h2 : (!hoistLt s c b) = true) :
    (!hoistLt s c a) = true := by
  rw [hle_iff] at h1 h2 ⊢
  intro hc
  rcases (by rw [keyLt] at *; omega : keyLt (hoistKey s c) (hoistKey s b)
      ∨ keyLt (hoistKey s b) (hoistKey s a)) with h | h
  · exact h2 h
  · exact h1 h

private theorem hle_total (s : _root_.Std.HashMap Nat Nat) (a b : Nat) :
    ((!hoistLt s b a) || (!hoistLt s a b)) = true := by
  by_cases h : hoistLt s b a = true
  · have hy : hoistLt s a b = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      rw [hoistLt_iff] at h hc
      exact keyLt_irrefl (keyLt_trans h hc)
    simp [hy]
  · simp only [Bool.not_eq_true] at h
    simp [h]

private theorem hle_antisymm (s : _root_.Std.HashMap Nat Nat) (a b : Nat)
    (h1 : (!hoistLt s b a) = true) (h2 : (!hoistLt s a b) = true) : a = b := by
  rw [hle_iff] at h1 h2
  by_contra hne
  rcases keyLt_total s hne with h | h
  · exact h2 h
  · exact h1 h

/-- Every entry of a bucket has the bucket's position as its key's first
component — the moved ones by their target, the unmoved one by itself. -/
private theorem bucketAt_key_fst {s : _root_.Std.HashMap Nat Nat} {moved : List Nat}
    {t x : Nat} (h : x ∈ bucketAt s moved t) : (hoistKey s x).1 = t := by
  rw [bucketAt] at h
  rcases List.mem_append.mp h with h | h
  · have := (List.mem_filter.mp h).2
    simp only [decide_eq_true_eq] at this
    rw [hoistKey_some this]
  · by_cases hc : s.contains t
    · rw [if_pos hc] at h; simp at h
    · rw [if_neg hc] at h
      rw [List.mem_singleton.mp h, hoistKey_none
        (show s[t]? = none from by
          rw [_root_.Std.HashMap.contains_eq_isSome_getElem?] at hc
          simpa using hc)]

private theorem bucketAt_pairwise {s : _root_.Std.HashMap Nat Nat} {moved : List Nat}
    (hmoved : moved.Pairwise (· < ·)) (t : Nat) :
    (bucketAt s moved t).Pairwise (fun a b => keyLt (hoistKey s a) (hoistKey s b)) := by
  rw [bucketAt]
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem ?_ (hmoved.filter _)
    intro a b hma hmb hab
    have ha : s[a]? = some t := by
      have := (List.mem_filter.mp hma).2; simpa using this
    have hb : s[b]? = some t := by
      have := (List.mem_filter.mp hmb).2; simpa using this
    rw [hoistKey_some ha, hoistKey_some hb]
    exact Or.inr ⟨rfl, Or.inr ⟨rfl, hab⟩⟩
  · split <;> simp
  · intro a ha b hb
    have hat : s[a]? = some t := by
      have := (List.mem_filter.mp ha).2; simpa using this
    by_cases hc : s.contains t
    · rw [if_pos hc] at hb; simp at hb
    · rw [if_neg hc] at hb
      have hbt : b = t := List.mem_singleton.mp hb
      have hnone : s[t]? = none := by
        rw [_root_.Std.HashMap.contains_eq_isSome_getElem?] at hc; simpa using hc
      rw [hoistKey_some hat, hbt, hoistKey_none hnone]
      exact Or.inr ⟨rfl, Or.inl Nat.zero_lt_one⟩

private theorem hoistBuckets_pairwise {s : _root_.Std.HashMap Nat Nat}
    {moved : List Nat} (hmoved : moved.Pairwise (· < ·)) :
    ∀ n : Nat, (hoistBuckets s moved n).Pairwise
      (fun a b => keyLt (hoistKey s a) (hoistKey s b))
  | 0 => by rw [hoistBuckets]; simp
  | n + 1 => by
    rw [hoistBuckets, List.range_succ, List.flatMap_append]
    refine List.pairwise_append.mpr ⟨hoistBuckets_pairwise hmoved n,
      by simpa using bucketAt_pairwise hmoved n, ?_⟩
    intro a ha b hb
    obtain ⟨t, ht, hat⟩ := List.mem_flatMap.mp ha
    rw [List.mem_range] at ht
    have h1 : (hoistKey s a).1 = t := bucketAt_key_fst hat
    have h2 : (hoistKey s b).1 = n := bucketAt_key_fst (by simpa using hb)
    rw [keyLt]; omega

private theorem mem_hoistBuckets {s : _root_.Std.HashMap Nat Nat} {n x : Nat}
    (hb : HoistBounded s n) :
    x ∈ hoistBuckets s ((List.range n).filter (fun k => s.contains k)) n ↔ x < n := by
  rw [hoistBuckets]
  constructor
  · intro h
    obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp h
    rw [List.mem_range] at ht
    rw [bucketAt] at hxt
    rcases List.mem_append.mp hxt with h | h
    · have := (List.mem_filter.mp (List.mem_filter.mp h).1).1
      rwa [List.mem_range] at this
    · by_cases hc : s.contains t
      · rw [if_pos hc] at h; simp at h
      · rw [if_neg hc] at h; rw [List.mem_singleton.mp h]; exact ht
  · intro hx
    by_cases hc : s.contains x
    · obtain ⟨t, ht⟩ : ∃ t, s[x]? = some t := by
        rw [_root_.Std.HashMap.contains_eq_isSome_getElem?] at hc
        rcases hx2 : s[x]? with _ | t
        · rw [hx2] at hc; simp at hc
        · exact ⟨t, rfl⟩
      refine List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (hb x t ht).2, ?_⟩
      rw [bucketAt]
      refine List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨?_, by simp [ht]⟩))
      exact List.mem_filter.mpr ⟨List.mem_range.mpr hx, by simpa using hc⟩
    · refine List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩
      rw [bucketAt]
      exact List.mem_append.mpr (Or.inr (by rw [if_neg hc]; simp))


private theorem hoistBuckets_nodup {s : _root_.Std.HashMap Nat Nat} {moved : List Nat}
    (hmoved : moved.Pairwise (· < ·)) (n : Nat) :
    (hoistBuckets s moved n).Nodup := by
  refine List.Pairwise.imp ?_ (hoistBuckets_pairwise hmoved n)
  intro a b hab hc
  rw [hc] at hab
  exact keyLt_irrefl hab

private theorem hoistBuckets_perm {s : _root_.Std.HashMap Nat Nat} {n : Nat}
    (hb : HoistBounded s n) :
    (hoistBuckets s ((List.range n).filter (fun k => s.contains k)) n).Perm
      (List.range n) := by
  refine (List.perm_ext_iff_of_nodup
    (hoistBuckets_nodup (List.pairwise_lt_range.filter _) n) (List.nodup_range)).mpr ?_
  intro x
  rw [mem_hoistBuckets hb, List.mem_range]

/-- **The bucket pass is the sort.**  `ConLeche/Frontend/NatOpGround.lean:150-162`'s
`(List.range ds.size).mergeSort` and the port's `hoist_order` produce the same
list: both are `Pairwise` for the key order, they are permutations of each
other, and the key order is antisymmetric because each key carries its own
index. -/
private theorem hoistBuckets_eq_mergeSort (s : _root_.Std.HashMap Nat Nat) (n : Nat)
    (hb : HoistBounded s n) :
    hoistBuckets s ((List.range n).filter (fun k => s.contains k)) n
      = (List.range n).mergeSort (fun a b => !hoistLt s b a) := by
  refine List.Perm.eq_of_pairwise (le := fun a b => (!hoistLt s b a) = true)
    (fun a b _ _ h1 h2 => hle_antisymm s a b h1 h2) ?_ ?_ ?_
  · refine List.Pairwise.imp ?_
      (hoistBuckets_pairwise (s := s) (List.pairwise_lt_range.filter _) n)
    intro a b hab
    rw [hle_iff]
    intro hc
    exact keyLt_irrefl (keyLt_trans hab hc)
  · exact List.pairwise_mergeSort (hle_trans s) (hle_total s) _
  · exact (hoistBuckets_perm hb).trans (List.mergeSort_perm _ _).symm

/-! ### The constants a record references

`nat_op_ground::used_consts_go` is an explicit `Vec<Expr>` worklist where
con-leche's `usedConstsGo` is *structural* recursion; the two are matched by
reading the worklist as the list of terms still to be walked, top first, and
running con-leche's walk along it (`usedGo` below).  Two things make that
go through: the port's `ron::HashMap<Expr, bool>` denotes con-leche's
`Std.HashSet Expr` (`SeenRel`, on `Refine/HashMapWF.lean`'s `Eq2Fwd` at the
`Expr` key — `expr::beq` is exact only on well-formed terms), and the sum of
`Expr.sizeF` over the worklist strictly decreases at every turn, which is the
`Nat` bound the loop is inducted on. -/

/-- The seen table's `Hashable` dictionary. -/
private abbrev seenHashable := expr.Expr.Insts.Con_ron_coreRonHashmapHashable
/-- The seen table's `Eq2` dictionary: the port's own `expr::beq`. -/
private abbrev seenEq2 := expr.Expr.Insts.Con_ron_coreRonHashmapEq2

/-- `expr::beq` never lies about well-formed terms (`Refine/Expr.lean`'s
`eq2_refines` plus injectivity of `absExpr`). -/
private theorem seen_eq2_fwd : HashMap.Eq2Fwd seenEq2 ExprWF := by
  intro a b c ha hb h
  rw [Expr.eq2_refines ha hb h]
  exact decide_eq_decide.mpr
    ⟨fun hc => Expr.absExpr_injective ha hb hc, fun hc => by rw [hc]⟩

/-- `ConLeche/Frontend/NatOpGround.lean:54-56` — `used_consts_go`'s seen
table: the port's `ron::HashMap<Expr, bool>` denotes con-leche's
`Std.HashSet Expr`. -/
structure SeenRel (seen : ron.hashmap.HashMap expr.Expr Bool)
    (S : _root_.Std.HashSet ConLeche.Expr) : Prop where
  /-- the port's own hash-table invariant (task #16's `Inv`) -/
  inv : HashMap.Inv seenHashable seen
  /-- every key it holds is a term a smart constructor built, without which
  `expr::beq` is not exact -/
  keys : HashMap.KeysOk ExprWF seen
  /-- membership for membership -/
  mem : ∀ e, ExprWF e → (HashMap.toFun seen e).isSome = S.contains (absExpr e)

/-- A fresh table is the empty set. -/
private theorem seen_new {seen : ron.hashmap.HashMap expr.Expr Bool}
    (h : ron.hashmap.HashMap.new expr.Expr Bool = ok seen) :
    SeenRel seen (∅ : _root_.Std.HashSet ConLeche.Expr) := by
  obtain ⟨hinv, halv, hnone⟩ := HashMap.new_refines (HashableInst := seenHashable) h
  refine ⟨hinv, ?_, ?_⟩
  · intro p hp; rw [halv] at hp; simp at hp
  · intro e _; rw [hnone e]; simp

/-- The seen table's probe. -/
private theorem seen_contains {seen : ron.hashmap.HashMap expr.Expr Bool}
    {S : _root_.Std.HashSet ConLeche.Expr} {e : expr.Expr} {b : Bool}
    (hrel : SeenRel seen S) (he : ExprWF e)
    (h : ron.hashmap.HashMap.contains_key seenHashable seenEq2 seen e = ok b) :
    b = S.contains (absExpr e) := by
  rw [ron.hashmap.HashMap.contains_key] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, hb⟩ := h
  rw [HashMap.get_refines_wf seen_eq2_fwd hrel.inv hrel.keys he hget] at hb
  rw [← hrel.mem e he]
  cases ho : HashMap.toFun seen e with
  | none => rw [ho] at hb; simp only [Result.ok.injEq] at hb; rw [← hb]; simp
  | some v => rw [ho] at hb; simp only [Result.ok.injEq] at hb; rw [← hb]; simp

/-- The seen table's insert. -/
private theorem seen_insert {seen seen' : ron.hashmap.HashMap expr.Expr Bool}
    {S : _root_.Std.HashSet ConLeche.Expr} {e : expr.Expr} {old : Option Bool}
    (hrel : SeenRel seen S) (he : ExprWF e)
    (h : ron.hashmap.HashMap.insert seenHashable seenEq2 seen e true = ok (old, seen')) :
    SeenRel seen' (S.insert (absExpr e)) := by
  obtain ⟨hinv', -, hupd, hkeys'⟩ :=
    HashMap.insert_refines_wf seen_eq2_fwd hrel.inv hrel.keys he h
  refine ⟨hinv', hkeys', ?_⟩
  intro k hk
  rw [hupd, Function.update_apply, _root_.Std.HashSet.contains_insert]
  by_cases hke : k = e
  · subst hke; simp
  · rw [if_neg hke, hrel.mem k hk]
    have hne : ¬ (absExpr e = absExpr k) := by
      intro hc; exact hke (Expr.absExpr_injective hk he hc.symm)
    simp [hne]

/-- `ConLeche/Frontend/NatOpGround.lean:54-77` — `usedConstsGo` run along a
list of terms, left to right: what the port's worklist computes out of the
stack it is holding, its top the head of the list. -/
private def usedGo (p : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name)
    (xs : List ConLeche.Expr) : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name :=
  xs.foldl (fun q x => ConLeche.Frontend.usedConstsGo q.1 q.2 x) p

private theorem usedGo_nil (p : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name) :
    usedGo p [] = p := rfl

private theorem usedGo_cons (p : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name)
    (x : ConLeche.Expr) (xs : List ConLeche.Expr) :
    usedGo p (x :: xs) = usedGo (ConLeche.Frontend.usedConstsGo p.1 p.2 x) xs := rfl

private theorem usedGo_append (p : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name)
    (xs ys : List ConLeche.Expr) : usedGo p (xs ++ ys) = usedGo (usedGo p xs) ys :=
  List.foldl_append ..

/-- Every term has at least one node. -/
private theorem sizeF_pos (e : ConLeche.Expr) : 0 < e.sizeF := by
  cases e <;> simp [ConLeche.Expr.sizeF]

/-- The port's worklist measure: the total `sizeF` of the live stack. -/
private def stackMeasure (stack : alloc.vec.Vec expr.Expr) (sp : Nat) : Nat :=
  (((stack.val.take sp).map (fun e => (absExpr e).sizeF)).sum)

/-- `bind_eq_ok_iff` for the generated `let (a, b) ← f x` binds: the pair the
call answers, destructured at once.  Without it the pattern `let` the do-block
elaborates to stands in simp's way (it is not a matcher, so neither `dsimp` nor
`split` reduces it) and no later rewrite reaches the loop's tail call. -/
private theorem bind_pair_eq_ok_iff {α β γ : Type} {e : Result (α × β)}
    {F : α → β → Result γ} {v : γ} :
    ((do let (a, b) ← e; F a b) = ok v) ↔ ∃ a b, e = ok (a, b) ∧ F a b = ok v := by
  rw [bind_eq_ok_iff]
  constructor
  · rintro ⟨⟨a, b⟩, he, hf⟩; exact ⟨a, b, he, hf⟩
  · rintro ⟨a, b, he, hf⟩; exact ⟨(a, b), he, hf⟩

/-- The write-back of a `Vec::index_mut` is `Vec.set` (`Refine/HashMap.lean`'s
`vec_index_mut_eq` says more but asks for `Inhabited α`). -/
private theorem push_index_mut_back {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {a : α} {f : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (a, f)) :
    f = alloc.vec.Vec.set v i := by
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨y, hy, hok⟩ := h
  exact (congrArg Prod.snd (Result.ok_injective hok)).symm

/-- Overwriting the slot at `n` and taking one more is appending. -/
private theorem take_set_succ {α : Type} {l : List α} {n : Nat} {x : α}
    (hn : n < l.length) : (l.set n x).take (n + 1) = l.take n ++ [x] := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_set, List.length_append,
      List.length_singleton]
    omega
  · intro m h1 h2
    simp only [List.length_take, List.length_set, List.length_append,
      List.length_singleton] at h1 h2
    rw [List.getElem_take, List.getElem_set]
    by_cases hm : m = n
    · subst hm
      rw [if_pos rfl, List.getElem_append_right (by simp only [List.length_take]; omega)]
      simp
    · rw [if_neg (fun hc => hm hc.symm),
        List.getElem_append_left (by simp only [List.length_take]; omega),
        List.getElem_take]

/-- `nat_op_ground::stack_push_expr`: the live prefix grows by the pushed
term. -/
private theorem stack_push_expr_take {stack stack' : alloc.vec.Vec expr.Expr}
    {sp sp' : Std.Usize} {x : expr.Expr} (hsp : sp.val ≤ stack.val.length)
    (h : frontend.nat_op_ground.stack_push_expr stack sp x = ok (stack', sp')) :
    sp'.val = sp.val + 1 ∧ sp'.val ≤ stack'.val.length ∧
      stack'.val.take sp'.val = stack.val.take sp.val ++ [x] := by
  rw [frontend.nat_op_ground.stack_push_expr] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, hv, i, hi, hr⟩ := h
  have hiv : i.val = sp.val + 1 := by have := Nat.uadd_val hi; simpa using this
  have he := Result.ok_injective hr
  have hv' : stack' = v := (congrArg Prod.fst he).symm
  have hi' : sp' = i := (congrArg Prod.snd he).symm
  subst hv'; subst hi'
  refine ⟨hiv, ?_, ?_⟩ <;> rw [hiv] <;> revert hv <;> split <;> intro hv
  · rename_i hlt
    have hlt' : sp.val < stack.val.length := by scalar_tac
    simp only [bind_eq_ok_iff] at hv
    obtain ⟨p, hidx, hok⟩ := hv
    obtain ⟨a, back⟩ := p
    rw [push_index_mut_back hidx] at hok
    rw [← Result.ok_injective hok, alloc.vec.Vec.set_val_eq, List.length_set]
    omega
  · rw [vec_push_val hv]; simpa using hsp
  · rename_i hlt
    have hlt' : sp.val < stack.val.length := by scalar_tac
    simp only [bind_eq_ok_iff] at hv
    obtain ⟨p, hidx, hok⟩ := hv
    obtain ⟨a, back⟩ := p
    rw [push_index_mut_back hidx] at hok
    rw [← Result.ok_injective hok, alloc.vec.Vec.set_val_eq, take_set_succ hlt']
  · rename_i hge
    have hlen : sp.val = stack.val.length := by scalar_tac
    rw [vec_push_val hv, hlen]
    simp

/-! con-leche's walk, one node at a time: the `if seen.contains e` guard and
then the ten arms, each already in the `usedGo` spelling the worklist needs. -/

private theorem usedConstsGo_hit {S : _root_.Std.HashSet ConLeche.Expr}
    {A : _root_.Array ConLeche.Name} {e : ConLeche.Expr} (h : S.contains e = true) :
    ConLeche.Frontend.usedConstsGo S A e = (S, A) := by
  cases e <;> (rw [ConLeche.Frontend.usedConstsGo, h]; rfl)

private theorem usedConstsGo_bvar {S A} {i : Nat} (h : S.contains (.bvar i) = false) :
    ConLeche.Frontend.usedConstsGo S A (.bvar i) = (S.insert (.bvar i), A) := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_sort {S A} {u : ConLeche.Level}
    (h : S.contains (.sort u) = false) :
    ConLeche.Frontend.usedConstsGo S A (.sort u) = (S.insert (.sort u), A) := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_lit {S A} {l : ConLeche.Literal}
    (h : S.contains (.lit l) = false) :
    ConLeche.Frontend.usedConstsGo S A (.lit l) = (S.insert (.lit l), A) := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_const {S A} {n : ConLeche.Name} {us : List ConLeche.Level}
    (h : S.contains (.const n us) = false) :
    ConLeche.Frontend.usedConstsGo S A (.const n us) = (S.insert (.const n us), A.push n) := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_fvar {S A} {idx : Nat} {ty : ConLeche.Expr}
    (h : S.contains (.fvar idx ty) = false) :
    ConLeche.Frontend.usedConstsGo S A (.fvar idx ty)
      = usedGo (S.insert (.fvar idx ty), A) [ty] := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_app {S A} {f a : ConLeche.Expr}
    (h : S.contains (.app f a) = false) :
    ConLeche.Frontend.usedConstsGo S A (.app f a)
      = usedGo (S.insert (.app f a), A) [f, a] := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_lam {S A} {ty b : ConLeche.Expr} {m : ConLeche.BinderMeta}
    (h : S.contains (.lam ty b m) = false) :
    ConLeche.Frontend.usedConstsGo S A (.lam ty b m)
      = usedGo (S.insert (.lam ty b m), A) [ty, b] := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_forallE {S A} {ty b : ConLeche.Expr} {m : ConLeche.BinderMeta}
    (h : S.contains (.forallE ty b m) = false) :
    ConLeche.Frontend.usedConstsGo S A (.forallE ty b m)
      = usedGo (S.insert (.forallE ty b m), A) [ty, b] := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_letE {S A} {ty v b : ConLeche.Expr}
    (h : S.contains (.letE ty v b) = false) :
    ConLeche.Frontend.usedConstsGo S A (.letE ty v b)
      = usedGo (S.insert (.letE ty v b), A) [ty, v, b] := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

private theorem usedConstsGo_proj {S A} {sn : ConLeche.Name} {i : Nat} {x : ConLeche.Expr}
    (h : S.contains (.proj sn i x) = false) :
    ConLeche.Frontend.usedConstsGo S A (.proj sn i x)
      = usedGo (S.insert (.proj sn i x), A.push sn) [x] := by
  rw [ConLeche.Frontend.usedConstsGo, h]; rfl

/-- The bound `take` step: popping the top of the stack. -/
private theorem take_pred {α : Type} {l : List α} {n : Nat} {x : α} (hn : 0 < n)
    (hx : l[n - 1]? = some x) : l.take n = l.take (n - 1) ++ [x] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hx ⊢
  rw [List.take_add_one, hx]
  simp

/-- The measure of a stack whose live prefix is known. -/
private theorem stackMeasure_eq {stack : alloc.vec.Vec expr.Expr} {n : Nat}
    {l : List expr.Expr} (h : stack.val.take n = l) :
    stackMeasure stack n = (l.map (fun e => (absExpr e).sizeF)).sum := by
  rw [stackMeasure, h]

/-- An empty stack stops the loop. -/
private theorem used_consts_go_loop_stop
    {seen : ron.hashmap.HashMap expr.Expr Bool} {acc : alloc.vec.Vec name.Name}
    {stack : alloc.vec.Vec expr.Expr} {sp : Std.Usize}
    {r : (alloc.vec.Vec name.Name) × ron.hashmap.HashMap expr.Expr Bool}
    (hsp0 : sp.val = 0)
    (h : frontend.nat_op_ground.used_consts_go_loop seen acc stack sp = ok r) :
    r = (acc, seen) := by
  rw [frontend.nat_op_ground.used_consts_go_loop.eq_def,
    if_neg (show ¬ sp > 0#usize by scalar_tac)] at h
  exact (Result.ok_injective h).symm

/-- `ConLeche/Frontend/NatOpGround.lean:54-77` — **the port's worklist is
con-leche's walk.**  Holding the stack `stack[0:sp]`, `used_consts_go`'s loop
computes `usedConstsGo` along that stack from the top down.  The `Nat` bound
is the total `Expr.sizeF` of the live stack, which drops by at least one at
every turn: a term already seen is popped (`sizeF ≥ 1`), and one not yet seen
is replaced by its children, whose sizes sum to one less. -/
private theorem used_consts_go_loop_refines :
    ∀ (fuel : Nat) (seen : ron.hashmap.HashMap expr.Expr Bool)
      (S : _root_.Std.HashSet ConLeche.Expr) (acc : alloc.vec.Vec name.Name)
      (stack : alloc.vec.Vec expr.Expr) (sp : Std.Usize)
      (r : (alloc.vec.Vec name.Name) × ron.hashmap.HashMap expr.Expr Bool),
      sp.val ≤ stack.val.length →
      (∀ e ∈ stack.val.take sp.val, ExprWF e) →
      stackMeasure stack sp.val ≤ fuel →
      NamesWF acc →
      SeenRel seen S →
      frontend.nat_op_ground.used_consts_go_loop seen acc stack sp = ok r →
      NamesWF r.1 ∧
        SeenRel r.2 (usedGo (S, (absNames acc).toArray)
          ((stack.val.take sp.val).reverse.map absExpr)).1 ∧
        (absNames r.1).toArray = (usedGo (S, (absNames acc).toArray)
          ((stack.val.take sp.val).reverse.map absExpr)).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen S acc stack sp r hsp hwf hm hacc hrel h
    have hsp0 : sp.val = 0 := by
      by_contra hc
      have hlt : sp.val - 1 < stack.val.length := by omega
      have hy : stack.val[sp.val - 1]? = some stack.val[sp.val - 1] :=
        List.getElem?_eq_getElem hlt
      rw [stackMeasure_eq (take_pred (by omega) hy)] at hm
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil] at hm
      have := sizeF_pos (absExpr stack.val[sp.val - 1])
      omega
    have hr := used_consts_go_loop_stop hsp0 h
    subst hr
    rw [hsp0]
    simp only [List.take_zero, List.reverse_nil, List.map_nil, usedGo_nil]
    refine ⟨hacc, hrel, ?_⟩; trivial
  | succ fuel ih =>
    intro seen S acc stack sp r hsp hwf hm hacc hrel h
    by_cases hsp0 : sp.val = 0
    · have hr := used_consts_go_loop_stop hsp0 h
      subst hr
      rw [hsp0]
      simp only [List.take_zero, List.reverse_nil, List.map_nil, usedGo_nil]
      refine ⟨hacc, hrel, ?_⟩; trivial
    rw [frontend.nat_op_ground.used_consts_go_loop.eq_def,
      if_pos (show sp > 0#usize by scalar_tac)] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨sp1, hsp1, e0, he0, x, hx, b, hb, h⟩ := h
    have hsp1v : sp1.val = sp.val - 1 := (Nat.usub_val hsp1).2.trans (by simp)
    have hxe : x = e0 := Expr.dup_eq hx
    subst hxe
    have hidx : stack.val[sp.val - 1]? = some x := by
      rw [← hsp1v]; exact ExprOps.vec_index_getElem? he0
    have htake : stack.val.take sp.val = stack.val.take sp1.val ++ [x] := by
      rw [hsp1v]; exact take_pred (by omega) hidx
    have hxwf : ExprWF x := hwf x (by rw [htake]; simp)
    have hsp1le : sp1.val ≤ stack.val.length := by omega
    have hwf1 : ∀ e ∈ stack.val.take sp1.val, ExprWF e := by
      intro e he; exact hwf e (by rw [htake]; simp [he])
    have hmsplit : stackMeasure stack sp.val
        = stackMeasure stack sp1.val + (absExpr x).sizeF := by
      rw [stackMeasure_eq htake, stackMeasure]; simp
    have hxpos := sizeF_pos (absExpr x)
    have hbv : b = S.contains (absExpr x) := seen_contains hrel hxwf hb
    have hlist : (stack.val.take sp.val).reverse.map absExpr
        = absExpr x :: ((stack.val.take sp1.val).reverse.map absExpr) := by
      rw [htake]; simp
    by_cases hbt : b = true
    · rw [if_pos hbt] at h
      have hc : S.contains (absExpr x) = true := by rw [← hbv]; exact hbt
      obtain ⟨h1, h2, h3⟩ :=
        ih seen S acc stack sp1 r hsp1le hwf1 (by omega) hacc hrel h
      rw [hlist]
      simpa only [usedGo_cons, usedConstsGo_hit hc] using ⟨h1, h2, h3⟩
    · rw [if_neg hbt] at h
      have hc : S.contains (absExpr x) = false := by
        rw [← hbv]; simpa using hbt
      rw [bind_eq_ok_iff] at h
      obtain ⟨e1, he1, h⟩ := h
      rw [bind_pair_eq_ok_iff] at h
      obtain ⟨old, seen1, hins, h⟩ := h
      have he1x : x = e1 := (Expr.dup_eq he1).symm
      subst he1x
      have hrel1 : SeenRel seen1 (S.insert (absExpr x)) := seen_insert hrel hxwf hins
      obtain ⟨⟨d, k⟩⟩ := x
      simp only [absExpr_mk] at hc hlist hmsplit hrel1
      rw [hlist]
      cases k with
      | Bvar i =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack sp1 r hsp1le hwf1
            (by rw [hmsplit] at hm; simp only [ConLeche.Expr.sizeF] at hm; omega) hacc hrel1 h
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_bvar hc] using ⟨h1, h2, h3⟩
      | «Sort» u =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack sp1 r hsp1le hwf1
            (by rw [hmsplit] at hm; simp only [ConLeche.Expr.sizeF] at hm; omega) hacc hrel1 h
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_sort hc] using ⟨h1, h2, h3⟩
      | Lit l =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack sp1 r hsp1le hwf1
            (by rw [hmsplit] at hm; simp only [ConLeche.Expr.sizeF] at hm; omega) hacc hrel1 h
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_lit hc] using ⟨h1, h2, h3⟩
      | Const n us =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, acc1, hacc1, h⟩ := h
        have hn1e : n1 = n := by
          rw [name_dup_eq] at hn1; exact (Result.ok_injective hn1).symm
        rw [hn1e] at hacc1
        have hnwf : NameWF n := (ExprWF.const_kids hxwf).1
        have haccwf : NamesWF acc1 := by
          intro y hy
          rw [vec_push_val hacc1] at hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hacc y hy
          · rw [List.mem_singleton.mp hy]; exact hnwf
        have habs : (absNames acc1).toArray = (absNames acc).toArray.push (absName n) := by
          rw [absNames, vec_push_val hacc1, List.map_append, List.push_toArray]; rfl
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc1 stack sp1 r hsp1le hwf1
            (by rw [hmsplit] at hm; simp only [ConLeche.Expr.sizeF] at hm; omega) haccwf hrel1 h
        rw [habs] at h2 h3
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_const hc] using ⟨h1, h2, h3⟩
      | Fvar idx ty =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e2, he2, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack2, sp2, hq2, h⟩ := h
        have he2x : ty = e2 := (Expr.dup_eq he2).symm
        subst he2x
        obtain ⟨hA2, hB2, hC2⟩ := stack_push_expr_take hsp1le hq2
        have hkids := ExprWF.fvar_kids hxwf
        have hwf2 : ∀ e ∈ stack2.val.take sp2.val, ExprWF e := by
          intro e he; rw [hC2] at he
          rcases List.mem_append.mp he with he | he
          · exact hwf1 e he
          · rw [List.mem_singleton.mp he]; exact ExprWF.fvar_kids hxwf
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack2 sp2 r hB2 hwf2
            (by
              rw [hmsplit] at hm
              rw [stackMeasure_eq hC2]
              simp only [stackMeasure, List.map_append, List.sum_append,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                ConLeche.Expr.sizeF] at hm ⊢
              omega)
            hacc hrel1 h
        rw [hC2] at h2 h3
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.map_cons, List.cons_append] at h2 h3
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_fvar hc] using ⟨h1, h2, h3⟩
      | Proj sn i sub =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨acc1, hacc1, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e2, he2, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack2, sp2, hq2, h⟩ := h
        have hn1e : n1 = sn := by
          rw [name_dup_eq] at hn1; exact (Result.ok_injective hn1).symm
        rw [hn1e] at hacc1
        have he2x : sub = e2 := (Expr.dup_eq he2).symm
        subst he2x
        have hnwf : NameWF sn := (ExprWF.proj_kids hxwf).1
        have haccwf : NamesWF acc1 := by
          intro y hy
          rw [vec_push_val hacc1] at hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hacc y hy
          · rw [List.mem_singleton.mp hy]; exact hnwf
        have habs : (absNames acc1).toArray = (absNames acc).toArray.push (absName sn) := by
          rw [absNames, vec_push_val hacc1, List.map_append, List.push_toArray]; rfl
        obtain ⟨hA2, hB2, hC2⟩ := stack_push_expr_take hsp1le hq2
        have hkids := ExprWF.proj_kids hxwf
        have hwf2 : ∀ e ∈ stack2.val.take sp2.val, ExprWF e := by
          intro e he; rw [hC2] at he
          rcases List.mem_append.mp he with he | he
          · exact hwf1 e he
          · rw [List.mem_singleton.mp he]; exact (ExprWF.proj_kids hxwf).2
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc1 stack2 sp2 r hB2 hwf2
            (by
              rw [hmsplit] at hm
              rw [stackMeasure_eq hC2]
              simp only [stackMeasure, List.map_append, List.sum_append,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                ConLeche.Expr.sizeF] at hm ⊢
              omega)
            haccwf hrel1 h
        rw [hC2] at h2 h3
        rw [habs] at h2 h3
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.map_cons, List.cons_append] at h2 h3
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_proj hc] using ⟨h1, h2, h3⟩
      | App f a =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e2, he2, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack2, sp2, hq2, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e3, he3, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack3, sp3, hq3, h⟩ := h
        have he2x : a = e2 := (Expr.dup_eq he2).symm
        subst he2x
        have he3x : f = e3 := (Expr.dup_eq he3).symm
        subst he3x
        obtain ⟨hA2, hB2, hC2⟩ := stack_push_expr_take hsp1le hq2
        obtain ⟨hA3, hB3, hC3⟩ := stack_push_expr_take hB2 hq3
        rw [hC2] at hC3
        have hkids := ExprWF.app_kids hxwf
        have hwf2 : ∀ e ∈ stack3.val.take sp3.val, ExprWF e := by
          intro e he; rw [hC3] at he
          rcases List.mem_append.mp he with he | he
          · rcases List.mem_append.mp he with he | he
            · exact hwf1 e he
            · rw [List.mem_singleton.mp he]; exact (ExprWF.app_kids hxwf).2
          · rw [List.mem_singleton.mp he]; exact (ExprWF.app_kids hxwf).1
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack3 sp3 r hB3 hwf2
            (by
              rw [hmsplit] at hm
              rw [stackMeasure_eq hC3]
              simp only [stackMeasure, List.map_append, List.sum_append,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                ConLeche.Expr.sizeF] at hm ⊢
              omega)
            hacc hrel1 h
        rw [hC3] at h2 h3
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.map_cons, List.cons_append] at h2 h3
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_app hc] using ⟨h1, h2, h3⟩
      | Lam ty bo m =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e2, he2, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack2, sp2, hq2, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e3, he3, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack3, sp3, hq3, h⟩ := h
        have he2x : bo = e2 := (Expr.dup_eq he2).symm
        subst he2x
        have he3x : ty = e3 := (Expr.dup_eq he3).symm
        subst he3x
        obtain ⟨hA2, hB2, hC2⟩ := stack_push_expr_take hsp1le hq2
        obtain ⟨hA3, hB3, hC3⟩ := stack_push_expr_take hB2 hq3
        rw [hC2] at hC3
        have hkids := ExprWF.lam_kids hxwf
        have hwf2 : ∀ e ∈ stack3.val.take sp3.val, ExprWF e := by
          intro e he; rw [hC3] at he
          rcases List.mem_append.mp he with he | he
          · rcases List.mem_append.mp he with he | he
            · exact hwf1 e he
            · rw [List.mem_singleton.mp he]; exact (ExprWF.lam_kids hxwf).2.1
          · rw [List.mem_singleton.mp he]; exact (ExprWF.lam_kids hxwf).1
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack3 sp3 r hB3 hwf2
            (by
              rw [hmsplit] at hm
              rw [stackMeasure_eq hC3]
              simp only [stackMeasure, List.map_append, List.sum_append,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                ConLeche.Expr.sizeF] at hm ⊢
              omega)
            hacc hrel1 h
        rw [hC3] at h2 h3
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.map_cons, List.cons_append] at h2 h3
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_lam hc] using ⟨h1, h2, h3⟩
      | ForallE ty bo m =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e2, he2, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack2, sp2, hq2, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e3, he3, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack3, sp3, hq3, h⟩ := h
        have he2x : bo = e2 := (Expr.dup_eq he2).symm
        subst he2x
        have he3x : ty = e3 := (Expr.dup_eq he3).symm
        subst he3x
        obtain ⟨hA2, hB2, hC2⟩ := stack_push_expr_take hsp1le hq2
        obtain ⟨hA3, hB3, hC3⟩ := stack_push_expr_take hB2 hq3
        rw [hC2] at hC3
        have hkids := ExprWF.forall_e_kids hxwf
        have hwf2 : ∀ e ∈ stack3.val.take sp3.val, ExprWF e := by
          intro e he; rw [hC3] at he
          rcases List.mem_append.mp he with he | he
          · rcases List.mem_append.mp he with he | he
            · exact hwf1 e he
            · rw [List.mem_singleton.mp he]; exact (ExprWF.forall_e_kids hxwf).2.1
          · rw [List.mem_singleton.mp he]; exact (ExprWF.forall_e_kids hxwf).1
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack3 sp3 r hB3 hwf2
            (by
              rw [hmsplit] at hm
              rw [stackMeasure_eq hC3]
              simp only [stackMeasure, List.map_append, List.sum_append,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                ConLeche.Expr.sizeF] at hm ⊢
              omega)
            hacc hrel1 h
        rw [hC3] at h2 h3
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.map_cons, List.cons_append] at h2 h3
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_forallE hc] using ⟨h1, h2, h3⟩
      | LetE ty v bo =>
        simp only [absExprKind] at hc hmsplit hrel1 ⊢
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e2, he2, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack2, sp2, hq2, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e3, he3, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack3, sp3, hq3, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨e4, he4, h⟩ := h
        rw [bind_pair_eq_ok_iff] at h
        obtain ⟨stack4, sp4, hq4, h⟩ := h
        have he2x : bo = e2 := (Expr.dup_eq he2).symm
        subst he2x
        have he3x : v = e3 := (Expr.dup_eq he3).symm
        subst he3x
        have he4x : ty = e4 := (Expr.dup_eq he4).symm
        subst he4x
        obtain ⟨hA2, hB2, hC2⟩ := stack_push_expr_take hsp1le hq2
        obtain ⟨hA3, hB3, hC3⟩ := stack_push_expr_take hB2 hq3
        rw [hC2] at hC3
        obtain ⟨hA4, hB4, hC4⟩ := stack_push_expr_take hB3 hq4
        rw [hC3] at hC4
        have hkids := ExprWF.let_e_kids hxwf
        have hwf2 : ∀ e ∈ stack4.val.take sp4.val, ExprWF e := by
          intro e he; rw [hC4] at he
          rcases List.mem_append.mp he with he | he
          · rcases List.mem_append.mp he with he | he
            · rcases List.mem_append.mp he with he | he
              · exact hwf1 e he
              · rw [List.mem_singleton.mp he]; exact (ExprWF.let_e_kids hxwf).2.2
            · rw [List.mem_singleton.mp he]; exact (ExprWF.let_e_kids hxwf).2.1
          · rw [List.mem_singleton.mp he]; exact (ExprWF.let_e_kids hxwf).1
        obtain ⟨h1, h2, h3⟩ :=
          ih seen1 _ acc stack4 sp4 r hB4 hwf2
            (by
              rw [hmsplit] at hm
              rw [stackMeasure_eq hC4]
              simp only [stackMeasure, List.map_append, List.sum_append,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                ConLeche.Expr.sizeF] at hm ⊢
              omega)
            hacc hrel1 h
        rw [hC4] at h2 h3
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.map_cons, List.cons_append] at h2 h3
        simpa only [usedGo_cons, usedGo_nil, usedConstsGo_letE hc] using ⟨h1, h2, h3⟩

/-! ### The constants a record references, one record at a time

The loop above is the walk; these three are what sit on top of it —
`Declaration.usedConsts`' `match` (`decl_used_consts`) and its `indDecl` arm's
`block.foldl` (`block_used_consts`, a loop of its own in the port so that
`decl_used_consts` stays the match con-leche writes). -/

/-- `ConLeche/Frontend/NatOpGround.lean:54-77` — **`nat_op_ground::used_consts_go`
refines `usedConstsGo`**: the worklist started at the single term `e`. -/
private theorem used_consts_go_refines {seen : ron.hashmap.HashMap expr.Expr Bool}
    {S : _root_.Std.HashSet ConLeche.Expr} {acc : alloc.vec.Vec name.Name} {e : expr.Expr}
    {r : (alloc.vec.Vec name.Name) × ron.hashmap.HashMap expr.Expr Bool}
    (hacc : NamesWF acc) (hrel : SeenRel seen S) (he : ExprWF e)
    (h : frontend.nat_op_ground.used_consts_go seen acc e = ok r) :
    NamesWF r.1 ∧
      SeenRel r.2 (ConLeche.Frontend.usedConstsGo S (absNames acc).toArray (absExpr e)).1 ∧
      (absNames r.1).toArray
        = (ConLeche.Frontend.usedConstsGo S (absNames acc).toArray (absExpr e)).2 := by
  rw [frontend.nat_op_ground.used_consts_go] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e1, he1, stack, hstack, h⟩ := h
  have he1x : e = e1 := (Expr.dup_eq he1).symm
  subst he1x
  have hsv : stack.val = [e] := by
    rw [vec_push_val hstack]; simp [alloc.vec.Vec.new]
  have htake : stack.val.take (1#usize).val = [e] := by rw [hsv]; rfl
  obtain ⟨h1, h2, h3⟩ :=
    used_consts_go_loop_refines (absExpr e).sizeF seen S acc stack 1#usize r
      (by rw [hsv]; simp) (by rw [htake]; intro x hx; rw [List.mem_singleton.mp hx]; exact he)
      (by rw [stackMeasure_eq htake]; simp) hacc hrel h
  rw [htake] at h2 h3
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
    List.map_nil, usedGo_cons, usedGo_nil] using ⟨h1, h2, h3⟩

/-- `ConLeche/Frontend/NatOpGround.lean:91` — the cited `rules.foldl`'s body:
one recursor rule's right-hand side. -/
private def ruleBody (p : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name)
    (r : ConLeche.RecRule) : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name :=
  ConLeche.Frontend.usedConstsGo p.1 p.2 r.rhs

/-- `ConLeche/Frontend/NatOpGround.lean:86-93` — the cited `block.foldl`'s body:
one block member's type, then a recursor's rule right-hand sides. -/
private def blockBody (p : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name)
    (ci : ConLeche.ConstantInfo) : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name :=
  let q := ConLeche.Frontend.usedConstsGo p.1 p.2 ci.toConstantVal.type
  match ci with
  | .recInfo _ _ _ rules => rules.foldl ruleBody q
  | _ => q

/-- `ConLeche/Frontend/NatOpGround.lean:86-93` — `Declaration.usedConsts`' `indDecl`
arm, its two `let (seen, acc) := …` destructurings resolved (structure eta). -/
private theorem usedConsts_indDecl (block : List ConLeche.ConstantInfo) (np : Nat) :
    ConLeche.Declaration.usedConsts (.indDecl block np)
      = (block.foldl blockBody (∅, #[])).2 := rfl

/-- `ConLeche/Frontend/NatOpGround.lean:91` — `nat_op_ground::block_used_consts`'
inner loop: the cited `rules.foldl` from `j` on. -/
private theorem block_used_consts_loop0_loop0_refines :
    ∀ (f : Nat) (seen : ron.hashmap.HashMap expr.Expr Bool)
      (S : _root_.Std.HashSet ConLeche.Expr) (acc : alloc.vec.Vec name.Name)
      (rules : alloc.vec.Vec env.RecRule) (m j : Std.Usize)
      (r : (ron.hashmap.HashMap expr.Expr Bool) × (alloc.vec.Vec name.Name)),
      m.val - j.val ≤ f → m.val = rules.val.length → j.val ≤ m.val →
      (∀ rr ∈ rules.val, RecRuleWF rr) → NamesWF acc → SeenRel seen S →
      frontend.nat_op_ground.block_used_consts_loop0_loop0 seen acc rules m j = ok r →
      NamesWF r.2 ∧
        SeenRel r.1 (((absRecRules rules).drop j.val).foldl ruleBody
          (S, (absNames acc).toArray)).1 ∧
        (absNames r.2).toArray = (((absRecRules rules).drop j.val).foldl ruleBody
          (S, (absNames acc).toArray)).2 := by
  intro f
  induction f with
  | zero =>
    intro seen S acc rules m j r hf hm hj hrwf hacc hrel h
    rw [frontend.nat_op_ground.block_used_consts_loop0_loop0.eq_def,
      if_neg (show ¬ j < m by scalar_tac), Result.ok.injEq] at h
    rw [← h, show (absRecRules rules).drop j.val = [] from by
      rw [List.drop_eq_nil_iff]; simp only [absRecRules, List.length_map]; omega]
    exact ⟨hacc, hrel, rfl⟩
  | succ f ih =>
    intro seen S acc rules m j r hf hm hj hrwf hacc hrel h
    rw [frontend.nat_op_ground.block_used_consts_loop0_loop0.eq_def] at h
    by_cases hlt : j.val < m.val
    · rw [if_pos (show j < m by scalar_tac)] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨rr, hrr, h⟩ := h
      rw [bind_pair_eq_ok_iff] at h
      obtain ⟨acc1, seen1, hgo, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨j1, hj1, h⟩ := h
      have hj1v : j1.val = j.val + 1 := by have := Nat.uadd_val hj1; simpa using this
      have hrlt : j.val < rules.val.length := by omega
      have hrx : rules.val[j.val] = rr := by
        have hg := ExprOps.vec_index_getElem? hrr
        rw [List.getElem?_eq_getElem hrlt] at hg; exact Option.some_injective _ hg
      have hrrwf : RecRuleWF rr := by rw [← hrx]; exact hrwf _ (List.getElem_mem hrlt)
      obtain ⟨ha1, hs1, hn1⟩ := used_consts_go_refines hacc hrel hrrwf.2.2 hgo
      dsimp only at ha1 hs1 hn1
      obtain ⟨h1, h2, h3⟩ := ih seen1 _ acc1 rules m j1 r (by omega) hm (by omega)
        hrwf ha1 hs1 h
      rw [hj1v, hn1] at h2 h3
      have hlenr : j.val < (absRecRules rules).length := by
        simp only [absRecRules, List.length_map]; omega
      have hgetr : (absRecRules rules)[j.val] = absRecRule rr := by
        simp only [absRecRules, List.getElem_map, hrx]
      rw [List.drop_eq_getElem_cons hlenr, hgetr, List.foldl_cons]
      exact ⟨h1, h2, h3⟩
    · rw [if_neg (show ¬ j < m by scalar_tac), Result.ok.injEq] at h
      rw [← h, show (absRecRules rules).drop j.val = [] from by
        rw [List.drop_eq_nil_iff]; simp only [absRecRules, List.length_map]; omega]
      exact ⟨hacc, hrel, rfl⟩

/-- `ConLeche/Frontend/NatOpGround.lean:86-93` — `nat_op_ground::block_used_consts`'
outer loop: the cited `block.foldl` from `i` on. -/
private theorem block_used_consts_loop0_refines :
    ∀ (f : Nat) (seen : ron.hashmap.HashMap expr.Expr Bool)
      (S : _root_.Std.HashSet ConLeche.Expr) (acc : alloc.vec.Vec name.Name)
      (block : alloc.vec.Vec env.ConstantInfo) (n i : Std.Usize)
      (r : (alloc.vec.Vec name.Name) × (ron.hashmap.HashMap expr.Expr Bool)),
      n.val - i.val ≤ f → n.val = block.val.length → i.val ≤ n.val →
      ConstantInfosWF block → NamesWF acc → SeenRel seen S →
      frontend.nat_op_ground.block_used_consts_loop0 seen block acc n i = ok r →
      NamesWF r.1 ∧
        SeenRel r.2 (((absConstantInfos block).drop i.val).foldl blockBody
          (S, (absNames acc).toArray)).1 ∧
        (absNames r.1).toArray = (((absConstantInfos block).drop i.val).foldl blockBody
          (S, (absNames acc).toArray)).2 := by
  intro f
  induction f with
  | zero =>
    intro seen S acc block n i r hf hn hi hbwf hacc hrel h
    rw [frontend.nat_op_ground.block_used_consts_loop0.eq_def,
      if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
    rw [← h, show (absConstantInfos block).drop i.val = [] from by
      rw [List.drop_eq_nil_iff]; simp only [absConstantInfos, List.length_map]; omega]
    exact ⟨hacc, hrel, rfl⟩
  | succ f ih =>
    intro seen S acc block n i r hf hn hi hbwf hacc hrel h
    rw [frontend.nat_op_ground.block_used_consts_loop0.eq_def] at h
    by_cases hlt : i.val < n.val
    · rw [if_pos (show i < n by scalar_tac)] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨ci, hci, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨cv, hcv, h⟩ := h
      rw [bind_pair_eq_ok_iff] at h
      obtain ⟨acc1, seen1, hgo, h⟩ := h
      have hilt : i.val < block.val.length := by omega
      have hcix : block.val[i.val] = ci := by
        have hg := ExprOps.vec_index_getElem? hci
        rw [List.getElem?_eq_getElem hilt] at hg; exact Option.some_injective _ hg
      have hciwf : ConstantInfoWF ci := by rw [← hcix]; exact hbwf _ (List.getElem_mem hilt)
      have hcvwf : ConstantValWF cv := BasisRaw.to_constant_val_wf hciwf hcv
      have hcvabs : absConstantVal cv = ConLeche.ConstantInfo.toConstantVal (absConstantInfo ci) :=
        Env.to_constant_val_refines hcv
      obtain ⟨ha1, hs1, hn1⟩ := used_consts_go_refines hacc hrel hcvwf.2.2 hgo
      dsimp only at ha1 hs1 hn1
      have hlenb : i.val < (absConstantInfos block).length := by
        simp only [absConstantInfos, List.length_map]; omega
      have hgetb : (absConstantInfos block)[i.val] = absConstantInfo ci := by
        simp only [absConstantInfos, List.getElem_map, hcix]
      have hty : (ConLeche.ConstantInfo.toConstantVal (absConstantInfo ci)).type
          = absExpr cv.ty := by rw [← hcvabs]; rfl
      have shared : ∀ (P : _root_.Std.HashSet ConLeche.Expr × _root_.Array ConLeche.Name)
          (seen2 : ron.hashmap.HashMap expr.Expr Bool)
          (acc2 : alloc.vec.Vec name.Name) (i1 : Std.Usize),
          SeenRel seen2 P.1 → NamesWF acc2 → (absNames acc2).toArray = P.2 →
          i + 1#usize = ok i1 →
          frontend.nat_op_ground.block_used_consts_loop0 seen2 block acc2 n i1 = ok r →
          NamesWF r.1 ∧
            SeenRel r.2 (((absConstantInfos block).drop (i.val + 1)).foldl blockBody P).1 ∧
            (absNames r.1).toArray
              = (((absConstantInfos block).drop (i.val + 1)).foldl blockBody P).2 := by
        intro P seen2 acc2 i1 hs2 ha2 hn2 hi1 h
        have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
        obtain ⟨h1, h2, h3⟩ := ih seen2 _ acc2 block n i1 r (by omega) hn (by omega)
          hbwf ha2 hs2 h
        rw [hi1v, hn2] at h2 h3
        exact ⟨h1, h2, h3⟩
      rw [List.drop_eq_getElem_cons hlenb, hgetb, List.foldl_cons]
      clear hgo hcvabs hcix hci hgetb
      cases ci with
      | AxiomInfo cv0 =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        simp only [blockBody, hty]
        exact shared _ seen1 acc1 i1 hs1 ha1 hn1 hi1 h
      | DefnInfo cv0 v0 h0 =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        simp only [blockBody, hty]
        exact shared _ seen1 acc1 i1 hs1 ha1 hn1 hi1 h
      | ThmInfo cv0 v0 =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        simp only [blockBody, hty]
        exact shared _ seen1 acc1 i1 hs1 ha1 hn1 hi1 h
      | IndInfo cv0 c0 =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        simp only [blockBody, hty]
        exact shared _ seen1 acc1 i1 hs1 ha1 hn1 hi1 h
      | CtorInfo cv0 a0 b0 =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        simp only [blockBody, hty]
        exact shared _ seen1 acc1 i1 hs1 ha1 hn1 hi1 h
      | ProjInfo t0 =>
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        simp only [blockBody, hty]
        exact shared _ seen1 acc1 i1 hs1 ha1 hn1 hi1 h
      | RecInfo cv0 mi rp rs =>
        rw [bind_eq_ok_iff] at h
        obtain ⟨⟨seen2, acc2⟩, hinner, h⟩ := h
        have hm : (alloc.vec.Vec.len rs).val = rs.val.length := alloc.vec.Vec.len_val rs
        obtain ⟨hi1, hi2, hi3⟩ :=
          block_used_consts_loop0_loop0_refines rs.val.length seen1 _ acc1 rs
            (alloc.vec.Vec.len rs) 0#usize (seen2, acc2) (by simp [hm]) hm.symm (by simp [hm])
            (fun rr hrr => (hciwf.2 rr hrr)) ha1 hs1 hinner
        dsimp only at hi1 hi2 hi3
        obtain ⟨i1, hi1', h⟩ := bind_eq_ok_iff.mp h
        simp only [blockBody, hty]
        rw [hn1] at hi2 hi3
        simp only [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero,
          absRecRules] at hi2 hi3
        exact shared _ seen2 acc2 i1 hi2 hi1 hi3 hi1' h
    · rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
      rw [← h, show (absConstantInfos block).drop i.val = [] from by
        rw [List.drop_eq_nil_iff]; simp only [absConstantInfos, List.length_map]; omega]
      exact ⟨hacc, hrel, rfl⟩

/-- `ConLeche/Frontend/NatOpGround.lean:86-93` — **`nat_op_ground::block_used_consts`
refines the cited `block.foldl`.** -/
private theorem block_used_consts_refines {seen : ron.hashmap.HashMap expr.Expr Bool}
    {S : _root_.Std.HashSet ConLeche.Expr} {acc : alloc.vec.Vec name.Name}
    {block : alloc.vec.Vec env.ConstantInfo}
    {r : (alloc.vec.Vec name.Name) × (ron.hashmap.HashMap expr.Expr Bool)}
    (hbwf : ConstantInfosWF block) (hacc : NamesWF acc) (hrel : SeenRel seen S)
    (h : frontend.nat_op_ground.block_used_consts seen acc block = ok r) :
    NamesWF r.1 ∧
      SeenRel r.2 ((absConstantInfos block).foldl blockBody (S, (absNames acc).toArray)).1 ∧
      (absNames r.1).toArray
        = ((absConstantInfos block).foldl blockBody (S, (absNames acc).toArray)).2 := by
  rw [frontend.nat_op_ground.block_used_consts] at h
  have hm : (alloc.vec.Vec.len block).val = block.val.length := alloc.vec.Vec.len_val block
  have := block_used_consts_loop0_refines block.val.length seen S acc block
    (alloc.vec.Vec.len block) 0#usize r (by simp [hm]) hm.symm (by simp [hm]) hbwf hacc hrel h
  simpa only [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero] using this

/-- `ConLeche/Frontend/NatOpGround.lean:79-95` — **`nat_op_ground::decl_used_consts`
refines `Declaration.usedConsts`.** -/
private theorem decl_used_consts_refines {d : env.Declaration} {acc : alloc.vec.Vec name.Name}
    (hd : DeclarationWF d) (h : frontend.nat_op_ground.decl_used_consts d = ok acc) :
    NamesWF acc ∧ (absNames acc).toArray = (absDeclaration d).usedConsts := by
  rw [frontend.nat_op_ground.decl_used_consts] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨seen, hseen, h⟩ := h
  have hrel := seen_new hseen
  have hempty : (absNames (alloc.vec.Vec.new name.Name)).toArray = (#[] : _root_.Array ConLeche.Name) := by
    simp [absNames, alloc.vec.Vec.new]
  have hnwf : NamesWF (alloc.vec.Vec.new name.Name) := by
    intro x hx; simp [alloc.vec.Vec.new] at hx
  cases d with
  | AxiomDecl cv =>
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc1, seen1, hgo, hr⟩ := h
    obtain ⟨h1, -, h3⟩ := used_consts_go_refines hnwf hrel hd.2.2 hgo
    dsimp only at h1 h3
    rw [← Result.ok_injective hr]
    rw [hempty] at h3
    exact ⟨h1, h3⟩
  | DefnDecl cv v hint =>
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc1, seen1, hgo, h⟩ := h
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc2, seen2, hgo2, hr⟩ := h
    obtain ⟨h1, h2, h3⟩ := used_consts_go_refines hnwf hrel hd.1.2.2 hgo
    dsimp only at h1 h2 h3
    rw [hempty] at h2 h3
    obtain ⟨g1, -, g3⟩ := used_consts_go_refines h1 h2 hd.2 hgo2
    dsimp only at g1 g3
    rw [h3] at g3
    rw [← Result.ok_injective hr]
    exact ⟨g1, g3⟩
  | ThmDecl cv v =>
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc1, seen1, hgo, h⟩ := h
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc2, seen2, hgo2, hr⟩ := h
    obtain ⟨h1, h2, h3⟩ := used_consts_go_refines hnwf hrel hd.1.2.2 hgo
    dsimp only at h1 h2 h3
    rw [hempty] at h2 h3
    obtain ⟨g1, -, g3⟩ := used_consts_go_refines h1 h2 hd.2 hgo2
    dsimp only at g1 g3
    rw [h3] at g3
    rw [← Result.ok_injective hr]
    exact ⟨g1, g3⟩
  | OpaqueDecl cv v =>
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc1, seen1, hgo, h⟩ := h
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc2, seen2, hgo2, hr⟩ := h
    obtain ⟨h1, h2, h3⟩ := used_consts_go_refines hnwf hrel hd.1.2.2 hgo
    dsimp only at h1 h2 h3
    rw [hempty] at h2 h3
    obtain ⟨g1, -, g3⟩ := used_consts_go_refines h1 h2 hd.2 hgo2
    dsimp only at g1 g3
    rw [h3] at g3
    rw [← Result.ok_injective hr]
    exact ⟨g1, g3⟩
  | BasisDecl k =>
    rw [← Result.ok_injective h]
    exact ⟨hnwf, by rw [hempty]; rfl⟩
  | IndDecl block np =>
    rw [bind_pair_eq_ok_iff] at h
    obtain ⟨acc1, seen1, hgo, hr⟩ := h
    obtain ⟨h1, -, h3⟩ := block_used_consts_refines hd hnwf hrel hgo
    dsimp only at h1 h3
    rw [hempty] at h3
    rw [← Result.ok_injective hr]
    exact ⟨h1, by rw [h3]; rw [absDeclaration, usedConsts_indDecl]⟩
  | QuotDecl k cv =>
    rw [← Result.ok_injective h]
    exact ⟨hnwf, by rw [hempty]; rfl⟩

/-! ### `hoistTargets`, as list recursion

con-leche writes the target-map computation as one `Id.run do` with four
nested loops — three `for`s and a `while` — and the port is four functions.
The two are matched by **restating con-leche's do-block as the same pieces**,
each a definition of its own over the list the loop walks, and proving the
restatement equal to `hoistTargets` (`hoistTargets_split`, by `rfl` once the
ranges are lists: the do-block's `forIn`s ARE these pieces, so the split is
definitional).  This is the intermediate-definition escape hatch task #87's
brief allows, and it is used only here.

The `while` stays a `Lean.Loop.forIn` — `hoistClose` below — because it is the
one loop whose termination is not structural: nothing but the port's own run
witnesses that it stops, so `hoistClose_eq` is a *one-step* unfolding
(`Lean.Loop.forIn_eq_of_monadTail`) and every fact about it is proved by
induction on the port's measure. -/

/-- `ConLeche/Frontend/NatOpGround.lean:113-115` — the cited
`for n in ds[i]!.names do if !idx.contains n then idx := idx.insert n i`. -/
private def hoistIdxNames (i : Nat) (ns : List ConLeche.Name)
    (idx0 : _root_.Std.HashMap ConLeche.Name Nat) :
    _root_.Std.HashMap ConLeche.Name Nat := Id.run do
  let mut idx := idx0
  for n in ns do
    if !idx.contains n then idx := idx.insert n i
  return idx

/-- `ConLeche/Frontend/NatOpGround.lean:112-115` — the cited
`for i in [0:ds.size]` of the name index, over the positions still to walk. -/
private def hoistIdx (ds : _root_.Array ConLeche.Declaration) (l : List Nat)
    (idx0 : _root_.Std.HashMap ConLeche.Name Nat) :
    _root_.Std.HashMap ConLeche.Name Nat := Id.run do
  let mut idx := idx0
  for i in l do
    idx := hoistIdxNames i ds[i]!.names idx
  return idx

/-- `ConLeche/Frontend/NatOpGround.lean:133-136` — the cited
`for n in ds[k]!.usedConsts do if let some m := idx[n]? then …`. -/
private def hoistPushDeps (idx : _root_.Std.HashMap ConLeche.Name Nat) (i k : Nat)
    (ns : List ConLeche.Name) (stack0 : _root_.Array Nat) : _root_.Array Nat := Id.run do
  let mut stack := stack0
  for n in ns do
    if let some m := idx[n]? then
      if m > i && m != k then stack := stack.push m
  return stack

/-- `ConLeche/Frontend/NatOpGround.lean:125-136` — the cited
`while h : stack.size > 0`, the closure of the records on the stack. -/
private def hoistClose (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (i : Nat)
    (target0 : _root_.Std.HashMap Nat Nat) (stack0 : _root_.Array Nat) :
    _root_.Std.HashMap Nat Nat := Id.run do
  let mut target := target0
  let mut stack := stack0
  while h : stack.size > 0 do
    let k := stack[stack.size - 1]
    stack := stack.pop
    match target[k]? with
    | some t => if t ≤ i then continue
    | none => pure ()
    target := target.insert k i
    for n in ds[k]!.usedConsts do
      if let some m := idx[n]? then
        if m > i && m != k then stack := stack.push m
  return target

/-- `ConLeche/Frontend/NatOpGround.lean:121-124` — the cited
`for g in natOpDeps c`, over the grounds still to walk. -/
private def hoistTargetsAt (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (i : Nat) (gs : List ConLeche.Name)
    (target0 : _root_.Std.HashMap Nat Nat) : _root_.Std.HashMap Nat Nat := Id.run do
  let mut target := target0
  for g in gs do
    let some j := idx[g]? | continue
    unless j > i do continue
    target := hoistClose ds idx i target #[j]
  return target

/-- `ConLeche/Frontend/NatOpGround.lean:119-136` — the cited second
`for i in [0:ds.size]`, over the positions still to walk. -/
private def hoistTargetsGo (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (l : List Nat)
    (target0 : _root_.Std.HashMap Nat Nat) : _root_.Std.HashMap Nat Nat := Id.run do
  let mut target := target0
  for i in l do
    let some c := ConLeche.Frontend.isNatOpRecord ds[i]! | continue
    target := hoistTargetsAt ds idx i (ConLeche.natOpDeps c) target
  return target

/-- **The split is definitional**: `hoistTargets` IS the pieces above. -/
private theorem hoistTargets_split (ds : _root_.Array ConLeche.Declaration) :
    ConLeche.Frontend.hoistTargets ds
      = hoistTargetsGo ds (hoistIdx ds (List.range' 0 ds.size) {})
          (List.range' 0 ds.size) {} := by
  simp only [ConLeche.Frontend.hoistTargets, hoistTargetsGo, hoistTargetsAt, hoistIdx,
    hoistIdxNames, hoistClose, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

private theorem hoistIdxNames_nil (i : Nat) (idx : _root_.Std.HashMap ConLeche.Name Nat) :
    hoistIdxNames i [] idx = idx := rfl

private theorem hoistIdxNames_cons (i : Nat) (n : ConLeche.Name) (ns : List ConLeche.Name)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) :
    hoistIdxNames i (n :: ns) idx
      = hoistIdxNames i ns (if !idx.contains n then idx.insert n i else idx) := by
  simp only [hoistIdxNames, Id.run, List.forIn_cons]
  split <;> rfl

private theorem hoistIdx_nil (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) : hoistIdx ds [] idx = idx := rfl

private theorem hoistIdx_cons (ds : _root_.Array ConLeche.Declaration) (i : Nat) (l : List Nat)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) :
    hoistIdx ds (i :: l) idx = hoistIdx ds l (hoistIdxNames i ds[i]!.names idx) := by
  simp only [hoistIdx, Id.run, List.forIn_cons]
  rfl

private theorem hoistPushDeps_nil (idx : _root_.Std.HashMap ConLeche.Name Nat) (i k : Nat)
    (st : _root_.Array Nat) : hoistPushDeps idx i k [] st = st := rfl

set_option linter.unusedSimpArgs false in
private theorem hoistPushDeps_cons (idx : _root_.Std.HashMap ConLeche.Name Nat) (i k : Nat)
    (n : ConLeche.Name) (ns : List ConLeche.Name) (st : _root_.Array Nat) :
    hoistPushDeps idx i k (n :: ns) st
      = hoistPushDeps idx i k ns (match idx[n]? with
          | some m => if m > i && m != k then st.push m else st
          | none => st) := by
  simp only [hoistPushDeps, Id.run, List.forIn_cons]
  cases hm : idx[n]? with
  | none => simp only [hm]; rfl
  | some m => simp only [hm]; split <;> rfl

private theorem hoistTargetsAt_nil (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (i : Nat)
    (target : _root_.Std.HashMap Nat Nat) : hoistTargetsAt ds idx i [] target = target := rfl

set_option linter.unusedSimpArgs false in
private theorem hoistTargetsAt_cons (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (i : Nat) (g : ConLeche.Name)
    (gs : List ConLeche.Name) (target : _root_.Std.HashMap Nat Nat) :
    hoistTargetsAt ds idx i (g :: gs) target
      = hoistTargetsAt ds idx i gs (match idx[g]? with
          | some j => if j > i then hoistClose ds idx i target #[j] else target
          | none => target) := by
  simp only [hoistTargetsAt, Id.run, List.forIn_cons]
  cases hj : idx[g]? with
  | none => simp only [hj]; rfl
  | some j => simp only [hj]; split <;> rfl

private theorem hoistTargetsGo_nil (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (target : _root_.Std.HashMap Nat Nat) :
    hoistTargetsGo ds idx [] target = target := rfl

set_option linter.unusedSimpArgs false in
private theorem hoistTargetsGo_cons (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (i : Nat) (l : List Nat)
    (target : _root_.Std.HashMap Nat Nat) :
    hoistTargetsGo ds idx (i :: l) target
      = hoistTargetsGo ds idx l (match ConLeche.Frontend.isNatOpRecord ds[i]! with
          | some c => hoistTargetsAt ds idx i (ConLeche.natOpDeps c) target
          | none => target) := by
  simp only [hoistTargetsGo, Id.run, List.forIn_cons]
  cases hc : ConLeche.Frontend.isNatOpRecord ds[i]! <;> simp only [hc] <;> rfl

/-- One step of `Lean.Loop.forIn` in `Id`, as a rewrite rule (the class
application `forIn`, which is what the `while` elaborates to). -/
private theorem loop_forIn_eq {β : Type} (b : β) (f : Unit → β → Id (ForInStep β)) :
    forIn (m := Id) Lean.Loop.mk b f
      = (do match ← f () b with
            | .done v => pure v
            | .yield v => forIn (m := Id) Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

/-- **One turn of con-leche's `while`.**  The only equation this file has
about `hoistClose`: it does not say the loop stops, and every use is inside an
induction on the port's own measure. -/
private theorem hoistClose_eq (ds : _root_.Array ConLeche.Declaration)
    (idx : _root_.Std.HashMap ConLeche.Name Nat) (i : Nat)
    (target : _root_.Std.HashMap Nat Nat) (stack : _root_.Array Nat) :
    hoistClose ds idx i target stack
      = if 0 < stack.size then
          (fun k =>
            match target[k]? with
            | some t =>
              if t ≤ i then hoistClose ds idx i target stack.pop
              else hoistClose ds idx i (target.insert k i)
                     (hoistPushDeps idx i k (ds[k]!.usedConsts).toList stack.pop)
            | none => hoistClose ds idx i (target.insert k i)
                     (hoistPushDeps idx i k (ds[k]!.usedConsts).toList stack.pop))
            stack[stack.size - 1]!
        else target := by
  simp only [hoistClose, hoistPushDeps, Id.run, Array.forIn_toList]
  rw [loop_forIn_eq]
  by_cases hs : 0 < stack.size
  · rw [dif_pos hs, if_pos hs,
      show stack[stack.size - 1]! = stack[stack.size - 1]'(by omega) from
        getElem!_pos _ _ (by omega)]
    cases ht : target[stack[stack.size - 1]'(by omega)]? with
    | none => rfl
    | some t =>
      by_cases hti : t ≤ i
      · simp only [if_pos hti]; rfl
      · simp only [if_neg hti]; rfl
  · rw [dif_neg hs, if_neg hs]; rfl

/-! ### The name index

`nat_op_ground::hoist_name_index` is the cited first `for i in [0:ds.size]`:
every name a record declares, mapped to the index of the record declaring it
(the first, on a duplicate). -/

/-- A record of the stream, abstracted (`ds[i]!` on con-leche's side). -/
private theorem absDecls_getElem! {ds : alloc.vec.Vec env.Declaration} {i : Nat}
    {d : env.Declaration} (h : ds.val[i]? = some d) :
    (absDecls ds).toArray[i]! = absDeclaration d := by
  have hsome : (absDecls ds).toArray[i]? = some (absDeclaration d) := by
    simp only [absDecls, List.getElem?_toArray, List.getElem?_map, h, Option.map_some]
  rw [getElem!_def, hsome]

/-- A fresh name index is the empty map. -/
private theorem idx_new {idx : ron.hashmap.HashMap name.Name Std.U64}
    (h : ron.hashmap.HashMap.new name.Name Std.U64 = ok idx) :
    HoistIdxRel idx (∅ : _root_.Std.HashMap ConLeche.Name Nat) := by
  obtain ⟨hinv, halv, hnone⟩ := HashMap.new_refines (HashableInst := idxHashable) h
  refine ⟨hinv, ?_, ?_⟩
  · intro p hp; rw [halv] at hp; simp at hp
  · intro n _; rw [hnone n]; simp

/-- The name index's probe. -/
private theorem idx_contains {idx : ron.hashmap.HashMap name.Name Std.U64}
    {s : _root_.Std.HashMap ConLeche.Name Nat} {n : name.Name} {b : Bool}
    (hrel : HoistIdxRel idx s) (hn : NameWF n)
    (h : ron.hashmap.HashMap.contains_key idxHashable idxEq2 idx n = ok b) :
    b = s.contains (absName n) := by
  rw [ron.hashmap.HashMap.contains_key] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, hget, hb⟩ := h
  rw [HashMap.get_refines_wf idx_eq2_fwd hrel.inv hrel.keys hn hget] at hb
  have hk := hrel.get n hn
  cases ho : HashMap.toFun idx n with
  | none =>
    rw [ho] at hb hk
    simp only [Option.map_none] at hk
    simp only [Result.ok.injEq] at hb
    rw [← hb, _root_.Std.HashMap.contains_eq_isSome_getElem?, ← hk]; simp
  | some v =>
    rw [ho] at hb hk
    simp only [Option.map_some] at hk
    simp only [Result.ok.injEq] at hb
    rw [← hb, _root_.Std.HashMap.contains_eq_isSome_getElem?, ← hk]; simp

/-- The name index's insert. -/
private theorem idx_insert {idx idx' : ron.hashmap.HashMap name.Name Std.U64}
    {s : _root_.Std.HashMap ConLeche.Name Nat} {n : name.Name} {v : Std.U64}
    {old : Option Std.U64}
    (hrel : HoistIdxRel idx s) (hn : NameWF n)
    (h : ron.hashmap.HashMap.insert idxHashable idxEq2 idx n v = ok (old, idx')) :
    HoistIdxRel idx' (s.insert (absName n) v.val) := by
  obtain ⟨hinv', -, hupd, hkeys'⟩ :=
    HashMap.insert_refines_wf idx_eq2_fwd hrel.inv hrel.keys hn h
  refine ⟨hinv', hkeys', ?_⟩
  intro k hk
  rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
  by_cases hke : k = n
  · subst hke; simp
  · rw [if_neg hke, hrel.get k hk]
    have hne : ¬ (absName n = absName k) := by
      intro hc; exact hke (Name.absName_injective hk hn hc.symm)
    simp [hne]

/-- `ConLeche/Frontend/NatOpGround.lean:113-115` — `hoist_name_index`' inner
loop: the cited `for n in ds[i]!.names` from `j` on. -/
private theorem hoist_name_index_loop0_loop0_refines :
    ∀ (f : Nat) (idx : ron.hashmap.HashMap name.Name Std.U64)
      (s : _root_.Std.HashMap ConLeche.Name Nat) (i : Std.Usize)
      (ns : alloc.vec.Vec name.Name) (m j : Std.Usize)
      (idx' : ron.hashmap.HashMap name.Name Std.U64),
      m.val - j.val ≤ f → m.val = ns.val.length → j.val ≤ m.val →
      NamesWF ns → HoistIdxRel idx s →
      frontend.nat_op_ground.hoist_name_index_loop0_loop0 idx i ns m j = ok idx' →
      HoistIdxRel idx' (hoistIdxNames i.val ((absNames ns).drop j.val) s) := by
  intro f
  induction f with
  | zero =>
    intro idx s i ns m j idx' hf hm hj hns hrel h
    rw [frontend.nat_op_ground.hoist_name_index_loop0_loop0.eq_def,
      if_neg (show ¬ j < m by scalar_tac), Result.ok.injEq] at h
    rw [← h, show (absNames ns).drop j.val = [] from by
      rw [List.drop_eq_nil_iff]; simp only [absNames, List.length_map]; omega]
    exact hrel
  | succ f ih =>
    intro idx s i ns m j idx' hf hm hj hns hrel h
    rw [frontend.nat_op_ground.hoist_name_index_loop0_loop0.eq_def] at h
    by_cases hlt : j.val < m.val
    · rw [if_pos (show j < m by scalar_tac)] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨n, hn, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨b, hb, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨idx1, hidx1, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨j1, hj1, h⟩ := h
      have hj1v : j1.val = j.val + 1 := by have := Nat.uadd_val hj1; simpa using this
      have hnlt : j.val < ns.val.length := by omega
      have hnx : ns.val[j.val] = n := by
        have hg := ExprOps.vec_index_getElem? hn
        rw [List.getElem?_eq_getElem hnlt] at hg; exact Option.some_injective _ hg
      have hnwf : NameWF n := by rw [← hnx]; exact hns _ (List.getElem_mem hnlt)
      have hbv : b = s.contains (absName n) := idx_contains hrel hnwf hb
      have hdrop : (absNames ns).drop j.val = absName n :: (absNames ns).drop (j.val + 1) := by
        have hlen : j.val < (absNames ns).length := by
          simp only [absNames, List.length_map]; omega
        rw [List.drop_eq_getElem_cons hlen]
        simp only [absNames, List.getElem_map, hnx]
      rw [hdrop, hoistIdxNames_cons, ← hj1v]
      refine ih idx1 _ i ns m j1 idx' (by omega) hm (by omega) hns ?_ h
      by_cases hbb : b = true
      · subst hbb
        simp only [reduceIte, Result.ok.injEq] at hidx1
        rw [← hidx1, if_neg (by simp [← hbv])]
        exact hrel
      · simp only [Bool.not_eq_true] at hbb
        subst hbb
        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff, lift_eq] at hidx1
        obtain ⟨n1, hn1, i1, hi1, ⟨old, idx2⟩, hins, hidx2⟩ := hidx1
        replace hidx2 : idx2 = idx1 := Result.ok_injective hidx2
        have hn1x : n1 = n := by rw [name_dup_eq] at hn1; exact (Result.ok_injective hn1).symm
        subst hn1x
        have hi1v : i1.val = i.val := by
          rw [← Result.ok_injective hi1]; exact Env.usize_cast_u64_val i
        rw [← hidx2, if_pos (by simp [← hbv]), ← hi1v]
        exact idx_insert hrel hnwf hins
    · rw [if_neg (show ¬ j < m by scalar_tac), Result.ok.injEq] at h
      rw [← h, show (absNames ns).drop j.val = [] from by
        rw [List.drop_eq_nil_iff]; simp only [absNames, List.length_map]; omega]
      exact hrel

/-- `ConLeche/Frontend/NatOpGround.lean:112-115` — `hoist_name_index`' outer
loop: the cited `for i in [0:ds.size]` from `i` on. -/
private theorem hoist_name_index_loop0_refines {ds : alloc.vec.Vec env.Declaration}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) :
    ∀ (f : Nat) (idx : ron.hashmap.HashMap name.Name Std.U64)
      (s : _root_.Std.HashMap ConLeche.Name Nat) (n i : Std.Usize)
      (idx' : ron.hashmap.HashMap name.Name Std.U64),
      n.val - i.val ≤ f → n.val = ds.val.length → i.val ≤ n.val →
      HoistIdxRel idx s →
      frontend.nat_op_ground.hoist_name_index_loop0 ds idx n i = ok idx' →
      HoistIdxRel idx' (hoistIdx (absDecls ds).toArray
        (List.range' i.val (n.val - i.val)) s) := by
  intro f
  induction f with
  | zero =>
    intro idx s n i idx' hf hn hi hrel h
    rw [frontend.nat_op_ground.hoist_name_index_loop0.eq_def,
      if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n.val - i.val = 0 by omega, List.range'_zero, hoistIdx_nil]
    exact hrel
  | succ f ih =>
    intro idx s n i idx' hf hn hi hrel h
    rw [frontend.nat_op_ground.hoist_name_index_loop0.eq_def] at h
    by_cases hlt : i.val < n.val
    · rw [if_pos (show i < n by scalar_tac)] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨d, hd, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨ns, hns, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨idx1, hidx1, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
      have hdlt : i.val < ds.val.length := by omega
      have hg : ds.val[i.val]? = some d := ExprOps.vec_index_getElem? hd
      have hdx : ds.val[i.val] = d := by
        rw [List.getElem?_eq_getElem hdlt] at hg; exact Option.some_injective _ hg
      have hdwf : DeclarationWF d := by rw [← hdx]; exact hds _ (List.getElem_mem hdlt)
      obtain ⟨hnsabs, hnswf⟩ := declaration_names_refines hdwf hns
      have hm : (alloc.vec.Vec.len ns).val = ns.val.length := alloc.vec.Vec.len_val ns
      have hstep : HoistIdxRel idx1 (hoistIdxNames i.val (absNames ns) s) := by
        have := hoist_name_index_loop0_loop0_refines ns.val.length idx s i ns
          (alloc.vec.Vec.len ns) 0#usize idx1 (by simp [hm]) hm.symm (by simp [hm])
          hnswf hrel hidx1
        simpa only [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero] using this
      rw [show n.val - i.val = (n.val - (i.val + 1)) + 1 by omega, List.range'_succ,
        hoistIdx_cons, absDecls_getElem! (by rw [List.getElem?_eq_getElem hdlt, hdx]),
        ← hnsabs, ← hi1v]
      exact ih idx1 _ n i1 idx' (by omega) hn (by omega) hstep h
    · rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
      rw [← h, show n.val - i.val = 0 by omega, List.range'_zero, hoistIdx_nil]
      exact hrel

/-- `ConLeche/Frontend/NatOpGround.lean:112-115` — **`nat_op_ground::hoist_name_index`
refines the cited name index.** -/
private theorem hoist_name_index_refines {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.nat_op_ground.hoist_name_index ds = ok idx) :
    HoistIdxRel idx (hoistIdx (absDecls ds).toArray
      (List.range' 0 (absDecls ds).toArray.size) ∅) := by
  rw [frontend.nat_op_ground.hoist_name_index] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨idx0, hidx0, h⟩ := h
  have hn : (alloc.vec.Vec.len ds).val = ds.val.length := alloc.vec.Vec.len_val ds
  have := hoist_name_index_loop0_refines hds ds.val.length idx0 ∅
    (alloc.vec.Vec.len ds) 0#usize idx (by simp [hn]) hn.symm (by simp [hn])
    (idx_new hidx0) h
  simpa only [show ((0#usize : Std.Usize).val) = 0 from rfl, Nat.sub_zero, hn,
    absDecls, List.size_toArray, List.length_map] using this

/-! ### The closure worklist's pushes

`nat_op_ground::hoist_push_deps` is the cited `for n in ds[k]!.usedConsts do if
let some m := idx[n]? then …`, and `hoist_push_dep` its body (task #13's owning
probe again: the index's borrow must not reach the branch).  The port's
worklist is a `Vec<u64>` with a top-of-stack index where con-leche's is an
`Array Nat`, so the two are matched by `stack[0:sp]`. -/

/-- Every value the name index holds is a position of the stream. -/
private def HoistIdxBounded (s : _root_.Std.HashMap ConLeche.Name Nat) (n : Nat) : Prop :=
  ∀ (g : ConLeche.Name) (j : Nat), s[g]? = some j → j < n

private theorem hoistIdxNames_bounded {i n : Nat} (hi : i < n) :
    ∀ (ns : List ConLeche.Name) (s : _root_.Std.HashMap ConLeche.Name Nat),
      HoistIdxBounded s n → HoistIdxBounded (hoistIdxNames i ns s) n := by
  intro ns
  induction ns with
  | nil => intro s hs; rw [hoistIdxNames_nil]; exact hs
  | cons x xs ih =>
    intro s hs
    rw [hoistIdxNames_cons]
    refine ih _ ?_
    by_cases hc : s.contains x = true
    · simp only [hc, Bool.not_true, Bool.false_eq_true, reduceIte]; exact hs
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.not_false, reduceIte]
      rw [HoistIdxBounded]
      intro g j hg
      rw [_root_.Std.HashMap.getElem?_insert] at hg
      by_cases hgx : (x == g) = true
      · rw [if_pos hgx] at hg; rw [← Option.some_injective _ hg]; exact hi
      · rw [if_neg hgx] at hg; exact hs g j hg

private theorem hoistIdx_bounded {n : Nat} (ds : _root_.Array ConLeche.Declaration) :
    ∀ (l : List Nat) (s : _root_.Std.HashMap ConLeche.Name Nat),
      (∀ i ∈ l, i < n) → HoistIdxBounded s n → HoistIdxBounded (hoistIdx ds l s) n := by
  intro l
  induction l with
  | nil => intro s _ hs; rw [hoistIdx_nil]; exact hs
  | cons x xs ih =>
    intro s hl hs
    rw [hoistIdx_cons]
    exact ih _ (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (hoistIdxNames_bounded (hl x (List.mem_cons_self ..)) _ s hs)

/-- `stack_push_expr_take` for the closure walk's `u64` stack (the port has the
two pushes separately: Rust has no generic here — §3.4's monomorphic rule). -/
private theorem stack_push_u64_take {stack stack' : alloc.vec.Vec Std.U64}
    {sp sp' : Std.Usize} {x : Std.U64} (hsp : sp.val ≤ stack.val.length)
    (h : frontend.nat_op_ground.stack_push_u64 stack sp x = ok (stack', sp')) :
    sp'.val = sp.val + 1 ∧ sp'.val ≤ stack'.val.length ∧
      stack'.val.take sp'.val = stack.val.take sp.val ++ [x] := by
  rw [frontend.nat_op_ground.stack_push_u64] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, hv, i, hi, hr⟩ := h
  have hiv : i.val = sp.val + 1 := by have := Nat.uadd_val hi; simpa using this
  have he := Result.ok_injective hr
  have hv' : stack' = v := (congrArg Prod.fst he).symm
  have hi' : sp' = i := (congrArg Prod.snd he).symm
  subst hv'; subst hi'
  refine ⟨hiv, ?_, ?_⟩ <;> rw [hiv] <;> revert hv <;> split <;> intro hv
  · rename_i hlt
    have hlt' : sp.val < stack.val.length := by scalar_tac
    simp only [bind_eq_ok_iff] at hv
    obtain ⟨p, hidx, hok⟩ := hv
    obtain ⟨a, back⟩ := p
    rw [push_index_mut_back hidx] at hok
    rw [← Result.ok_injective hok, alloc.vec.Vec.set_val_eq, List.length_set]
    omega
  · rw [vec_push_val hv]; simpa using hsp
  · rename_i hlt
    have hlt' : sp.val < stack.val.length := by scalar_tac
    simp only [bind_eq_ok_iff] at hv
    obtain ⟨p, hidx, hok⟩ := hv
    obtain ⟨a, back⟩ := p
    rw [push_index_mut_back hidx] at hok
    rw [← Result.ok_injective hok, alloc.vec.Vec.set_val_eq, take_set_succ hlt']
  · rename_i hge
    have hlen : sp.val = stack.val.length := by scalar_tac
    rw [vec_push_val hv, hlen]
    simp

/-- `ConLeche/Frontend/NatOpGround.lean:134-136` — **`nat_op_ground::hoist_push_dep`
refines the cited `if let some m := idx[n]? then if m > i && m != k then
stack := stack.push m`.** -/
private theorem hoist_push_dep_refines {idx : ron.hashmap.HashMap name.Name Std.U64}
    {s : _root_.Std.HashMap ConLeche.Name Nat} {n : name.Name}
    {stack stack' : alloc.vec.Vec Std.U64} {sp sp' : Std.Usize} {i k : Std.U64}
    {a : _root_.Array Nat}
    (hrel : HoistIdxRel idx s) (hn : NameWF n) (hsp : sp.val ≤ stack.val.length)
    (ha : (stack.val.take sp.val).map (·.val) = a.toList)
    (h : frontend.nat_op_ground.hoist_push_dep idx n stack sp i k = ok (stack', sp')) :
    sp'.val ≤ stack'.val.length ∧
      (stack'.val.take sp'.val).map (·.val)
        = (match s[absName n]? with
           | some m => if m > i.val && m != k.val then a.push m else a
           | none => a).toList := by
  rw [frontend.nat_op_ground.hoist_push_dep] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  have hov := idx_get_refines hrel hn ho
  cases o with
  | none =>
    simp only [Option.map_none] at hov
    rw [← hov]
    dsimp only at h ⊢
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]
    exact ⟨hsp, ha⟩
  | some m =>
    simp only [Option.map_some] at hov
    rw [← hov]
    dsimp only at h ⊢
    by_cases hmi : m.val > i.val
    · rw [if_pos (show m > i by scalar_tac)] at h
      by_cases hmk : m.val = k.val
      · have hmk' : m = k := Env.u64_val_inj hmk
        rw [if_neg (by simp [hmk'])] at h
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2]
        refine ⟨hsp, ?_⟩
        rw [ha]
        simp [hmk]
      · rw [if_pos (show m != k by simp only [bne_iff_ne, ne_eq]; intro hc; exact hmk (by rw [hc]))] at h
        obtain ⟨h1, h2, h3⟩ := stack_push_u64_take hsp h
        refine ⟨h2, ?_⟩
        rw [h3]
        simp only [List.map_append, List.map_cons, List.map_nil, ha]
        simp only [decide_true, hmi, Bool.true_and]
        rw [if_pos (by simp only [bne_iff_ne, ne_eq]; exact hmk), Array.toList_push]
    · rw [if_neg (show ¬ m > i by scalar_tac)] at h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      refine ⟨hsp, ?_⟩
      rw [ha]
      simp [hmi]

/-- `ConLeche/Frontend/NatOpGround.lean:133-136` — `nat_op_ground::hoist_push_deps`'
loop: the cited `for n in ds[k]!.usedConsts` from `u` on. -/
private theorem hoist_push_deps_loop_refines :
    ∀ (f : Nat) (idx : ron.hashmap.HashMap name.Name Std.U64)
      (s : _root_.Std.HashMap ConLeche.Name Nat) (used : alloc.vec.Vec name.Name)
      (i k : Std.U64) (stack stack' : alloc.vec.Vec Std.U64) (sp sp' n u : Std.Usize)
      (a : _root_.Array Nat),
      n.val - u.val ≤ f → n.val = used.val.length → u.val ≤ n.val →
      NamesWF used → HoistIdxRel idx s →
      sp.val ≤ stack.val.length →
      (stack.val.take sp.val).map (·.val) = a.toList →
      frontend.nat_op_ground.hoist_push_deps_loop idx used i k stack sp n u = ok (stack', sp') →
      sp'.val ≤ stack'.val.length ∧
        (stack'.val.take sp'.val).map (·.val)
          = (hoistPushDeps s i.val k.val ((absNames used).drop u.val) a).toList := by
  intro f
  induction f with
  | zero =>
    intro idx s used i k stack stack' sp sp' n u a hf hn hu hwf hrel hsp ha h
    rw [frontend.nat_op_ground.hoist_push_deps_loop.eq_def,
      if_neg (show ¬ u < n by scalar_tac), Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2, show (absNames used).drop u.val = [] from by
      rw [List.drop_eq_nil_iff]; simp only [absNames, List.length_map]; omega,
      hoistPushDeps_nil]
    exact ⟨hsp, ha⟩
  | succ f ih =>
    intro idx s used i k stack stack' sp sp' n u a hf hn hu hwf hrel hsp ha h
    rw [frontend.nat_op_ground.hoist_push_deps_loop.eq_def] at h
    by_cases hlt : u.val < n.val
    · rw [if_pos (show u < n by scalar_tac)] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨x, hx, h⟩ := h
      rw [bind_pair_eq_ok_iff] at h
      obtain ⟨stack1, sp1, hstep, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨u1, hu1, h⟩ := h
      have hu1v : u1.val = u.val + 1 := by have := Nat.uadd_val hu1; simpa using this
      have hxlt : u.val < used.val.length := by omega
      have hxx : used.val[u.val] = x := by
        have hg := ExprOps.vec_index_getElem? hx
        rw [List.getElem?_eq_getElem hxlt] at hg; exact Option.some_injective _ hg
      have hxwf : NameWF x := by rw [← hxx]; exact hwf _ (List.getElem_mem hxlt)
      obtain ⟨h1, h2⟩ := hoist_push_dep_refines hrel hxwf hsp ha hstep
      have hdrop : (absNames used).drop u.val
          = absName x :: (absNames used).drop (u.val + 1) := by
        have hlen : u.val < (absNames used).length := by
          simp only [absNames, List.length_map]; omega
        rw [List.drop_eq_getElem_cons hlen]
        simp only [absNames, List.getElem_map, hxx]
      rw [hdrop, hoistPushDeps_cons, ← hu1v]
      exact ih idx s used i k stack1 stack' sp1 sp' n u1 _ (by omega) hn (by omega)
        hwf hrel h1 h2 h
    · rw [if_neg (show ¬ u < n by scalar_tac), Result.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2, show (absNames used).drop u.val = [] from by
        rw [List.drop_eq_nil_iff]; simp only [absNames, List.length_map]; omega,
        hoistPushDeps_nil]
      exact ⟨hsp, ha⟩

/-- `ConLeche/Frontend/NatOpGround.lean:133-136` — **`nat_op_ground::hoist_push_deps`
refines the cited `for n in ds[k]!.usedConsts`.** -/
private theorem hoist_push_deps_refines {idx : ron.hashmap.HashMap name.Name Std.U64}
    {s : _root_.Std.HashMap ConLeche.Name Nat} {used : alloc.vec.Vec name.Name}
    {i k : Std.U64} {stack stack' : alloc.vec.Vec Std.U64} {sp sp' : Std.Usize}
    {a : _root_.Array Nat}
    (hwf : NamesWF used) (hrel : HoistIdxRel idx s)
    (hsp : sp.val ≤ stack.val.length)
    (ha : (stack.val.take sp.val).map (·.val) = a.toList)
    (h : frontend.nat_op_ground.hoist_push_deps idx used stack sp i k = ok (stack', sp')) :
    sp'.val ≤ stack'.val.length ∧
      (stack'.val.take sp'.val).map (·.val)
        = (hoistPushDeps s i.val k.val (absNames used) a).toList := by
  rw [frontend.nat_op_ground.hoist_push_deps] at h
  have hn : (alloc.vec.Vec.len used).val = used.val.length := alloc.vec.Vec.len_val used
  have := hoist_push_deps_loop_refines used.val.length idx s used i k stack stack' sp sp'
    (alloc.vec.Vec.len used) 0#usize a (by simp [hn]) hn.symm (by simp [hn]) hwf hrel hsp ha h
  simpa only [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero] using this

/-- Every index the closure walk pushes comes from the name index, so it is a
position of the stream. -/
private theorem hoistPushDeps_bounded {s : _root_.Std.HashMap ConLeche.Name Nat} {N i k : Nat}
    (hb : HoistIdxBounded s N) :
    ∀ (ns : List ConLeche.Name) (a : _root_.Array Nat),
      (∀ x ∈ a.toList, x < N) → ∀ x ∈ (hoistPushDeps s i k ns a).toList, x < N := by
  intro ns
  induction ns with
  | nil => intro a ha; rw [hoistPushDeps_nil]; exact ha
  | cons y ys ih =>
    intro a ha
    rw [hoistPushDeps_cons]
    refine ih _ ?_
    cases hy : s[y]? with
    | none => simpa only [hy] using ha
    | some m =>
      dsimp only
      by_cases hc : (decide (m > i) && m != k) = true
      · rw [if_pos hc]
        intro x hx
        rw [Array.toList_push, List.mem_append] at hx
        rcases hx with hx | hx
        · exact ha x hx
        · rw [List.mem_singleton.mp hx]; exact hb y m hy
      · rw [if_neg hc]; exact ha

/-! ### The closure walk

`nat_op_ground::hoist_close` is the cited `while h : stack.size > 0`, and it is
the pass's one loop with no structural measure — the stack grows as well as
shrinks.  What makes it stop is that the target map only ever *grows*: each
turn either pops (the record is already targeted at `i` or earlier) or targets
one more of the stream's finitely many positions, and a position once targeted
at `i` stays targeted at `i`.  So the induction is lexicographic — first on
`undone` (how many positions are not yet targeted at `i`), then on the top of
the port's stack — and con-leche's `while` is unfolded one turn at a time
beside the port's, `hoistClose_eq` against `hoist_close_loop.eq_def`. -/

/-- `ConLeche/Frontend/NatOpGround.lean:129-131` — the cited `match target[k]?
with | some t => if t ≤ i then continue | none => pure ()`, as a `Bool`.  This
is what `nat_op_ground::target_done` computes (`target_done_refines`). -/
private def targetDone (s : _root_.Std.HashMap Nat Nat) (i k : Nat) : Bool :=
  match s[k]? with | some t => decide (t ≤ i) | none => false

/-- The closure walk's measure: the stream positions not yet targeted at `i`
or earlier. -/
private def undone (s : _root_.Std.HashMap Nat Nat) (i n : Nat) : Nat :=
  ((List.range n).filter (fun k => !targetDone s i k)).length

private theorem filter_length_le {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, q x = true → p x = true) →
      (l.filter q).length ≤ (l.filter p).length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x xs ih =>
    intro hle
    have ihx := ih (fun y hy => hle y (List.mem_cons_of_mem _ hy))
    by_cases hq : q x = true
    · have hp : p x = true := hle x (List.mem_cons_self ..) hq
      rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hp]
      simpa using ihx
    · simp only [Bool.not_eq_true] at hq
      rw [List.filter_cons_of_neg (by simp [hq])]
      by_cases hp : p x = true
      · rw [List.filter_cons_of_pos hp]; simp; omega
      · simp only [Bool.not_eq_true] at hp
        rw [List.filter_cons_of_neg (by simp [hp])]; exact ihx

private theorem filter_length_lt {α : Type} {p q : α → Bool} {y : α} :
    ∀ (l : List α), (∀ x ∈ l, q x = true → p x = true) → y ∈ l → p y = true → q y = false →
      (l.filter q).length < (l.filter p).length := by
  intro l
  induction l with
  | nil => intro _ hy; simp at hy
  | cons x xs ih =>
    intro hle hy hpy hqy
    have hle' := fun z hz => hle z (List.mem_cons_of_mem _ hz)
    by_cases hyx : y = x
    · subst hyx
      rw [List.filter_cons_of_neg (by simp [hqy]), List.filter_cons_of_pos hpy]
      have := filter_length_le (p := p) (q := q) xs hle'
      simp only [List.length_cons]
      omega
    · have hy' : y ∈ xs := by rcases List.mem_cons.mp hy with h | h; · exact absurd h hyx
                              · exact h
      have ihx := ih hle' hy' hpy hqy
      by_cases hq : q x = true
      · have hp : p x = true := hle x (List.mem_cons_self ..) hq
        rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hp]
        simp only [List.length_cons]; omega
      · simp only [Bool.not_eq_true] at hq
        rw [List.filter_cons_of_neg (by simp [hq])]
        by_cases hp : p x = true
        · rw [List.filter_cons_of_pos hp]; simp only [List.length_cons]; omega
        · simp only [Bool.not_eq_true] at hp
          rw [List.filter_cons_of_neg (by simp [hp])]; exact ihx

/-- Targeting one more position strictly shrinks the measure: the position
targeted was not done, and it is done now, and no other position changes. -/
private theorem undone_insert_lt {s : _root_.Std.HashMap Nat Nat} {i k n : Nat}
    (hk : k < n) (hnd : targetDone s i k = false) :
    undone (s.insert k i) i n < undone s i n := by
  have hmono : ∀ x, targetDone s i x = true → targetDone (s.insert k i) i x = true := by
    intro x hx
    rw [targetDone, _root_.Std.HashMap.getElem?_insert]
    by_cases hxk : (k == x) = true
    · rw [if_pos hxk]; simp
    · rw [if_neg hxk]; exact hx
  refine filter_length_lt (List.range n) ?_ (List.mem_range.mpr hk) (by simp [hnd]) ?_
  · intro x _ hx
    simp only [Bool.not_eq_true'] at hx ⊢
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [hmono x hc] at hx
    simp at hx
  · simp only [Bool.not_eq_false']
    rw [targetDone, _root_.Std.HashMap.getElem?_insert, if_pos (by simp)]
    simp

/-- The target map's insert, with the entry count `HoistTargetRel` carries. -/
private theorem tgt_insert {target target' : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {k v : Std.U64} {old : Option Std.U64}
    (hrel : HoistTargetRel target s)
    (h : ron.hashmap.HashMap.insert tgtHashable tgtEq2 target k v = ok (old, target')) :
    HoistTargetRel target' (s.insert k.val v.val) := by
  obtain ⟨hinv', -, hupd⟩ := HashMap.insert_refines tgt_eq2_spec hrel.inv h
  have hget : ∀ q : Std.U64,
      (HashMap.toFun target' q).map (·.val) = (s.insert k.val v.val)[q.val]? := by
    intro q
    rw [hupd, Function.update_apply, _root_.Std.HashMap.getElem?_insert]
    by_cases hq : q = k
    · subst hq; simp
    · rw [if_neg hq, hrel.get q]
      have hne : ¬ (k.val = q.val) := by
        intro hc; exact hq (Env.u64_val_inj hc.symm)
      simp [hne]
  refine ⟨hinv', hget, ?_⟩
  have hmem : (k ∈ HashMap.support target) ↔ (k.val ∈ s) := by
    rw [HashMap.mem_support_iff, _root_.Std.HashMap.mem_iff_contains,
      _root_.Std.HashMap.contains_eq_isSome_getElem?, ← hrel.get k]
    simp
  have hsupp : HashMap.support target' = Insert.insert k (HashMap.support target) := by
    ext q
    rw [HashMap.mem_support_iff, hupd, Function.update_apply, Finset.mem_insert,
      HashMap.mem_support_iff]
    by_cases hq : q = k
    · subst hq; simp
    · simp [hq]
  rw [← HashMap.card_support hinv', hsupp, _root_.Std.HashMap.size_insert]
  by_cases hk : k.val ∈ s
  · rw [if_pos hk, Finset.insert_eq_self.mpr (hmem.mpr hk), HashMap.card_support hrel.inv,
      hrel.size]
  · rw [if_neg hk, Finset.card_insert_of_notMem (fun hc => hk (hmem.mp hc)),
      HashMap.card_support hrel.inv, hrel.size]

/-- The port's live stack, popped: its top is con-leche's last entry. -/
private theorem stack_top {stack : alloc.vec.Vec Std.U64} {sp : Std.Usize}
    {a : _root_.Array Nat} {k : Std.U64}
    (hpos : 0 < sp.val) (hk : stack.val[sp.val - 1]? = some k)
    (ha : (stack.val.take sp.val).map (·.val) = a.toList) :
    0 < a.size ∧ a[a.size - 1]! = k.val ∧ k.val ∈ a.toList ∧
      (stack.val.take (sp.val - 1)).map (·.val) = a.pop.toList := by
  have htake : stack.val.take sp.val = stack.val.take (sp.val - 1) ++ [k] := take_pred hpos hk
  have hal : a.toList = ((stack.val.take (sp.val - 1)).map (·.val)) ++ [k.val] := by
    rw [← ha, htake]; simp
  have hsize : a.size = ((stack.val.take (sp.val - 1)).map (·.val)).length + 1 := by
    rw [← Array.length_toList, hal]; simp
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have hsome : a[a.size - 1]? = some k.val := by
      rw [← Array.getElem?_toList, hal, hsize]; simp
    rw [getElem!_def, hsome]
  · rw [hal]; simp
  · rw [Array.toList_pop, hal]; simp

/-- `ConLeche/Frontend/NatOpGround.lean:128-131` — one turn of the closure
walk that does nothing: the record is targeted at `i` or earlier already. -/
private theorem hoist_close_step_done {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {target target1 : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {stack stack1 : alloc.vec.Vec Std.U64}
    {sp sp1 : Std.Usize} {k i : Std.U64}
    (hrel : HoistTargetRel target s) (hb : targetDone s i.val k.val = true)
    (h : frontend.nat_op_ground.hoist_close_step ds idx target stack sp k i
      = ok (target1, stack1, sp1)) :
    target1 = target ∧ stack1 = stack ∧ sp1 = sp := by
  rw [frontend.nat_op_ground.hoist_close_step] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨b, hbb, h⟩ := h
  have hbv : b = targetDone s i.val k.val := target_done_refines hrel hbb
  rw [hbv, hb, if_pos rfl, Result.ok.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- `ConLeche/Frontend/NatOpGround.lean:132-136` — one turn of the closure walk
that targets a record: `target[k] := i`, and the record's own references that
are declared after `i` go on the worklist. -/
private theorem hoist_close_step_push {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {idxS : _root_.Std.HashMap ConLeche.Name Nat}
    {target target1 : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {stack stack1 : alloc.vec.Vec Std.U64}
    {sp sp1 : Std.Usize} {k i : Std.U64} {a : _root_.Array Nat}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) (hidx : HoistIdxRel idx idxS)
    (hrel : HoistTargetRel target s) (hsp : sp.val ≤ stack.val.length)
    (ha : (stack.val.take sp.val).map (·.val) = a.toList)
    (hb : targetDone s i.val k.val = false) (hklt : k.val < ds.val.length)
    (h : frontend.nat_op_ground.hoist_close_step ds idx target stack sp k i
      = ok (target1, stack1, sp1)) :
    HoistTargetRel target1 (s.insert k.val i.val) ∧
      sp1.val ≤ stack1.val.length ∧
      (stack1.val.take sp1.val).map (·.val)
        = (hoistPushDeps idxS i.val k.val
            (((absDecls ds).toArray[k.val]!).usedConsts).toList a).toList := by
  rw [frontend.nat_op_ground.hoist_close_step] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨b, hbb, h⟩ := h
  have hbv : b = targetDone s i.val k.val := target_done_refines hrel hbb
  rw [hbv, hb, if_neg (by simp)] at h
  rw [bind_pair_eq_ok_iff] at h
  obtain ⟨old, target2, hins, h⟩ := h
  rw [bind_eq_ok_iff] at h
  obtain ⟨kk, hkk, h⟩ := h
  rw [bind_eq_ok_iff] at h
  obtain ⟨d, hd, h⟩ := h
  rw [bind_eq_ok_iff] at h
  obtain ⟨used, hused, h⟩ := h
  rw [bind_pair_eq_ok_iff] at h
  obtain ⟨v, sp2, hpush, h⟩ := h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  rw [lift_eq] at hkk
  have hdslen : ds.val.length ≤ Std.Usize.max := by have := ds.slice.property; scalar_tac
  have hkkv : kk.val = k.val := by
    rw [← Result.ok_injective hkk]
    exact Env.u64_cast_usize_val (by omega)
  have hdg : ds.val[kk.val]? = some d := ExprOps.vec_index_getElem? hd
  rw [hkkv] at hdg
  have hdx : ds.val[k.val] = d := by
    rw [List.getElem?_eq_getElem hklt] at hdg; exact Option.some_injective _ hdg
  have hdwf : DeclarationWF d := by rw [← hdx]; exact hds _ (List.getElem_mem hklt)
  obtain ⟨huwf, huabs⟩ := decl_used_consts_refines hdwf hused
  have hnames : absNames used = (((absDecls ds).toArray[k.val]!).usedConsts).toList := by
    rw [absDecls_getElem! hdg, ← huabs, List.toList_toArray]
  obtain ⟨hsp2, ha2⟩ := hoist_push_deps_refines huwf hidx hsp ha hpush
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.1]; exact tgt_insert hrel hins
  · rw [← h.2.1, ← h.2.2]; exact hsp2
  · rw [← h.2.1, ← h.2.2, ha2, hnames]

/-- `bind_pair_eq_ok_iff` for the triple `hoist_close_step` answers. -/
private theorem bind_triple_eq_ok_iff {α β γ δ : Type} {e : Result (α × β × γ)}
    {F : α → β → γ → Result δ} {v : δ} :
    ((do let (a, b, c) ← e; F a b c) = ok v) ↔ ∃ a b c, e = ok (a, b, c) ∧ F a b c = ok v := by
  rw [bind_eq_ok_iff]
  constructor
  · rintro ⟨⟨a, b, c⟩, he, hf⟩; exact ⟨a, b, c, he, hf⟩
  · rintro ⟨a, b, c, he, hf⟩; exact ⟨(a, b, c), he, hf⟩

/-- `ConLeche/Frontend/NatOpGround.lean:125-136` — **`nat_op_ground::hoist_close`'s
loop is con-leche's `while`.**  The induction is lexicographic: `undone` first
(a turn that targets a record shrinks it), then the port's top of stack (a turn
that does not targets nothing and pops). -/
private theorem hoist_close_loop_refines {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {idxS : _root_.Std.HashMap ConLeche.Name Nat}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) (hidx : HoistIdxRel idx idxS)
    (hib : HoistIdxBounded idxS ds.val.length) :
    ∀ (fuelU fuelS : Nat) (i : Std.U64)
      (target target' : ron.hashmap.HashMap Std.U64 Std.U64)
      (s : _root_.Std.HashMap Nat Nat) (stack : alloc.vec.Vec Std.U64) (sp : Std.Usize)
      (a : _root_.Array Nat),
      undone s i.val ds.val.length ≤ fuelU → sp.val ≤ fuelS →
      i.val < ds.val.length →
      HoistTargetRel target s → HoistBounded s ds.val.length →
      sp.val ≤ stack.val.length →
      (stack.val.take sp.val).map (·.val) = a.toList →
      (∀ x ∈ a.toList, x < ds.val.length) →
      frontend.nat_op_ground.hoist_close_loop ds idx i target stack sp = ok target' →
      HoistTargetRel target' (hoistClose (absDecls ds).toArray idxS i.val s a) ∧
        HoistBounded (hoistClose (absDecls ds).toArray idxS i.val s a) ds.val.length := by
  intro fuelU
  induction fuelU using Nat.strong_induction_on with
  | _ fuelU ihU =>
    intro fuelS
    induction fuelS with
    | zero =>
      intro i target target' s stack sp a hu hs hi hrel hb hsp ha hab h
      have hsp0 : sp.val = 0 := by omega
      have ha0 : a.toList = [] := by rw [← ha, hsp0]; simp
      have hasz : ¬ (0 < a.size) := by
        rw [← Array.length_toList, ha0]; simp
      rw [frontend.nat_op_ground.hoist_close_loop.eq_def,
        if_neg (show ¬ sp > 0#usize by scalar_tac), Result.ok.injEq] at h
      rw [hoistClose_eq, if_neg hasz, ← h]
      exact ⟨hrel, hb⟩
    | succ fuelS ihS =>
      intro i target target' s stack sp a hu hs hi hrel hb hsp ha hab h
      by_cases hsp0 : 0 < sp.val
      · rw [frontend.nat_op_ground.hoist_close_loop.eq_def,
          if_pos (show sp > 0#usize by scalar_tac)] at h
        rw [bind_eq_ok_iff] at h
        obtain ⟨sp1, hsp1, h⟩ := h
        rw [bind_eq_ok_iff] at h
        obtain ⟨k, hk, h⟩ := h
        rw [bind_triple_eq_ok_iff] at h
        obtain ⟨target1, stack1, sp2, hstep, h⟩ := h
        have hsp1v : sp1.val = sp.val - 1 := (Nat.usub_val hsp1).2.trans (by simp)
        have hkidx : stack.val[sp.val - 1]? = some k := by
          rw [← hsp1v]; exact ExprOps.vec_index_getElem? hk
        obtain ⟨hapos, hatop, hamem, hapop⟩ := stack_top hsp0 hkidx ha
        rw [← hsp1v] at hapop
        have hklt : k.val < ds.val.length := hab _ hamem
        rw [hoistClose_eq, if_pos hapos, hatop]
        by_cases hbv : targetDone s i.val k.val = true
        · obtain ⟨e1, e2, e3⟩ := hoist_close_step_done hrel hbv hstep
          rw [e1, e2, e3] at h
          rw [targetDone] at hbv
          cases hsk : s[k.val]? with
          | none => rw [hsk] at hbv; simp at hbv
          | some t =>
            rw [hsk] at hbv
            simp only [decide_eq_true_eq] at hbv
            simp only [hsk]
            rw [if_pos hbv]
            refine ihS i target target' s stack sp1 a.pop hu (by omega) hi hrel hb
              (by omega) hapop ?_ h
            intro x hx
            exact hab x (by rw [Array.toList_pop] at hx; exact List.dropLast_subset _ hx)
        · simp only [Bool.not_eq_true] at hbv
          obtain ⟨hrel1, hsp2, ha2⟩ :=
            hoist_close_step_push (sp := sp1) (stack := stack) (a := a.pop)
              hds hidx hrel (by omega) hapop hbv hklt hstep
          have hundone : undone (s.insert k.val i.val) i.val ds.val.length
              < undone s i.val ds.val.length := undone_insert_lt hklt hbv
          have hb1 : HoistBounded (s.insert k.val i.val) ds.val.length := by
            intro q t hq
            rw [_root_.Std.HashMap.getElem?_insert] at hq
            by_cases hqk : (k.val == q) = true
            · rw [if_pos hqk] at hq
              rw [← Option.some_injective _ hq, show q = k.val from (by simpa using hqk : k.val = q).symm]
              exact ⟨hklt, hi⟩
            · rw [if_neg hqk] at hq; exact hb q t hq
          have habnew : ∀ x ∈ (hoistPushDeps idxS i.val k.val
              (((absDecls ds).toArray[k.val]!).usedConsts).toList a.pop).toList,
              x < ds.val.length := by
            refine hoistPushDeps_bounded hib _ a.pop ?_
            · intro x hx
              exact hab x (by rw [Array.toList_pop] at hx; exact List.dropLast_subset _ hx)
          have hgoal : ∀ (P : _root_.Std.HashMap Nat Nat),
              P = hoistClose (absDecls ds).toArray idxS i.val (s.insert k.val i.val)
                    (hoistPushDeps idxS i.val k.val
                      (((absDecls ds).toArray[k.val]!).usedConsts).toList a.pop) →
              HoistTargetRel target' P ∧ HoistBounded P ds.val.length := by
            intro P hP
            subst hP
            exact ihU (undone s i.val ds.val.length - 1) (by omega) sp2.val i target1 target'
              (s.insert k.val i.val) stack1 sp2 _ (by omega) (le_refl _) hi hrel1 hb1
              hsp2 ha2 habnew h
          rw [targetDone] at hbv
          cases hsk : s[k.val]? with
          | none => simp only [hsk]; exact hgoal _ rfl
          | some t =>
            rw [hsk] at hbv
            simp only [decide_eq_false_iff_not] at hbv
            simp only [hsk]
            rw [if_neg hbv]
            exact hgoal _ rfl
      · have hsp0' : sp.val = 0 := by omega
        have ha0 : a.toList = [] := by rw [← ha, hsp0']; simp
        have hasz : ¬ (0 < a.size) := by
          rw [← Array.length_toList, ha0]; simp
        rw [frontend.nat_op_ground.hoist_close_loop.eq_def,
          if_neg (show ¬ sp > 0#usize by scalar_tac), Result.ok.injEq] at h
        rw [hoistClose_eq, if_neg hasz, ← h]
        exact ⟨hrel, hb⟩

/-! ### The target map itself

The three loops above the closure walk: one ground (`hoist_targets_one`), one
operation record's grounds (`hoist_targets_at`) and the stream
(`hoist_targets`). -/

/-- A fresh target map is the empty map. -/
private theorem tgt_new {target : ron.hashmap.HashMap Std.U64 Std.U64}
    (h : ron.hashmap.HashMap.new Std.U64 Std.U64 = ok target) :
    HoistTargetRel target (∅ : _root_.Std.HashMap Nat Nat) := by
  obtain ⟨hinv, halv, hnone⟩ := HashMap.new_refines (HashableInst := tgtHashable) h
  refine ⟨hinv, ?_, ?_⟩
  · intro k; rw [hnone k]; simp
  · rw [halv]; simp

/-- `ConLeche/Frontend/NatOpGround.lean:125-136` — **`nat_op_ground::hoist_close`
refines the cited `while`, started at the single ground record `j`.** -/
private theorem hoist_close_refines {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {idxS : _root_.Std.HashMap ConLeche.Name Nat}
    {target target' : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {j i : Std.U64}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) (hidx : HoistIdxRel idx idxS)
    (hib : HoistIdxBounded idxS ds.val.length)
    (hi : i.val < ds.val.length) (hj : j.val < ds.val.length)
    (hrel : HoistTargetRel target s) (hb : HoistBounded s ds.val.length)
    (h : frontend.nat_op_ground.hoist_close ds idx target j i = ok target') :
    HoistTargetRel target' (hoistClose (absDecls ds).toArray idxS i.val s #[j.val]) ∧
      HoistBounded (hoistClose (absDecls ds).toArray idxS i.val s #[j.val])
        ds.val.length := by
  rw [frontend.nat_op_ground.hoist_close] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨stack, hstack, h⟩ := h
  have hsv : stack.val = [j] := by
    rw [vec_push_val hstack]; simp [alloc.vec.Vec.new]
  refine hoist_close_loop_refines hds hidx hib (undone s i.val ds.val.length) 1 i target
    target' s stack 1#usize #[j.val] (le_refl _) (by simp) hi hrel hb
    (by rw [hsv]; simp) (by rw [hsv]; simp) ?_ h
  intro x hx
  simp only [List.mem_singleton] at hx
  rw [show x = j.val from by simpa using hx]; exact hj

/-- `ConLeche/Frontend/NatOpGround.lean:121-124` — **`nat_op_ground::hoist_targets_one`
refines the cited `let some j := idx[g]? | continue; unless j > i do continue`.** -/
private theorem hoist_targets_one_refines {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {idxS : _root_.Std.HashMap ConLeche.Name Nat}
    {target target' : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {g : name.Name} {i : Std.U64}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) (hidx : HoistIdxRel idx idxS)
    (hib : HoistIdxBounded idxS ds.val.length) (hg : NameWF g)
    (hi : i.val < ds.val.length)
    (hrel : HoistTargetRel target s) (hb : HoistBounded s ds.val.length)
    (h : frontend.nat_op_ground.hoist_targets_one ds idx target g i = ok target') :
    HoistTargetRel target' (match idxS[absName g]? with
        | some j => if j > i.val then hoistClose (absDecls ds).toArray idxS i.val s #[j] else s
        | none => s) ∧
      HoistBounded (match idxS[absName g]? with
        | some j => if j > i.val then hoistClose (absDecls ds).toArray idxS i.val s #[j] else s
        | none => s) ds.val.length := by
  rw [frontend.nat_op_ground.hoist_targets_one] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  have hov := idx_get_refines hidx hg ho
  cases o with
  | none =>
    simp only [Option.map_none] at hov
    rw [← hov]
    dsimp only at h ⊢
    simp only [Result.ok.injEq] at h
    rw [← h]; exact ⟨hrel, hb⟩
  | some j =>
    simp only [Option.map_some] at hov
    have hjlt : j.val < ds.val.length := hib _ _ hov.symm
    rw [← hov]
    dsimp only at h ⊢
    by_cases hji : j.val > i.val
    · rw [if_pos (show j > i by scalar_tac)] at h
      rw [if_pos hji]
      exact hoist_close_refines hds hidx hib hi hjlt hrel hb h
    · rw [if_neg (show ¬ j > i by scalar_tac)] at h
      rw [if_neg hji]
      simp only [Result.ok.injEq] at h
      rw [← h]; exact ⟨hrel, hb⟩

/-- `ConLeche/Frontend/NatOpGround.lean:121-124` — `nat_op_ground::hoist_targets_at`'s
loop: the cited `for g in natOpDeps c` from `k` on. -/
private theorem hoist_targets_at_loop_refines {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {idxS : _root_.Std.HashMap ConLeche.Name Nat}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) (hidx : HoistIdxRel idx idxS)
    (hib : HoistIdxBounded idxS ds.val.length) :
    ∀ (f : Nat) (target target' : ron.hashmap.HashMap Std.U64 Std.U64)
      (s : _root_.Std.HashMap Nat Nat) (gs : alloc.vec.Vec name.Name)
      (m k : Std.Usize) (i : Std.U64),
      m.val - k.val ≤ f → m.val = gs.val.length → k.val ≤ m.val → NamesWF gs →
      i.val < ds.val.length →
      HoistTargetRel target s → HoistBounded s ds.val.length →
      frontend.nat_op_ground.hoist_targets_at_loop ds idx i target gs m k = ok target' →
      HoistTargetRel target' (hoistTargetsAt (absDecls ds).toArray idxS i.val
          ((absNames gs).drop k.val) s) ∧
        HoistBounded (hoistTargetsAt (absDecls ds).toArray idxS i.val
          ((absNames gs).drop k.val) s) ds.val.length := by
  intro f
  induction f with
  | zero =>
    intro target target' s gs m k i hf hm hk hwf hi hrel hb h
    rw [frontend.nat_op_ground.hoist_targets_at_loop.eq_def,
      if_neg (show ¬ k < m by scalar_tac), Result.ok.injEq] at h
    rw [← h, show (absNames gs).drop k.val = [] from by
      rw [List.drop_eq_nil_iff]; simp only [absNames, List.length_map]; omega,
      hoistTargetsAt_nil]
    exact ⟨hrel, hb⟩
  | succ f ih =>
    intro target target' s gs m k i hf hm hk hwf hi hrel hb h
    rw [frontend.nat_op_ground.hoist_targets_at_loop.eq_def] at h
    by_cases hlt : k.val < m.val
    · rw [if_pos (show k < m by scalar_tac)] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨n, hn, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨target1, hone, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨k1, hk1, h⟩ := h
      have hk1v : k1.val = k.val + 1 := by have := Nat.uadd_val hk1; simpa using this
      have hnlt : k.val < gs.val.length := by omega
      have hnx : gs.val[k.val] = n := by
        have hg := ExprOps.vec_index_getElem? hn
        rw [List.getElem?_eq_getElem hnlt] at hg; exact Option.some_injective _ hg
      have hnwf : NameWF n := by rw [← hnx]; exact hwf _ (List.getElem_mem hnlt)
      have hdrop : (absNames gs).drop k.val = absName n :: (absNames gs).drop (k.val + 1) := by
        have hlen : k.val < (absNames gs).length := by
          simp only [absNames, List.length_map]; omega
        rw [List.drop_eq_getElem_cons hlen]
        simp only [absNames, List.getElem_map, hnx]
      obtain ⟨hrel1, hb1⟩ := hoist_targets_one_refines hds hidx hib hnwf hi hrel hb hone
      rw [hdrop, hoistTargetsAt_cons, ← hk1v]
      exact ih target1 target' _ gs m k1 i (by omega) hm (by omega) hwf hi hrel1 hb1 h
    · rw [if_neg (show ¬ k < m by scalar_tac), Result.ok.injEq] at h
      rw [← h, show (absNames gs).drop k.val = [] from by
        rw [List.drop_eq_nil_iff]; simp only [absNames, List.length_map]; omega,
        hoistTargetsAt_nil]
      exact ⟨hrel, hb⟩

/-- `ConLeche/Frontend/NatOpGround.lean:121-124` — **`nat_op_ground::hoist_targets_at`
refines the cited `for g in natOpDeps c`.** -/
private theorem hoist_targets_at_refines {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {idxS : _root_.Std.HashMap ConLeche.Name Nat}
    {target target' : ron.hashmap.HashMap Std.U64 Std.U64}
    {s : _root_.Std.HashMap Nat Nat} {c : name.Name} {i : Std.U64}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) (hidx : HoistIdxRel idx idxS)
    (hib : HoistIdxBounded idxS ds.val.length) (hc : NameWF c)
    (hi : i.val < ds.val.length)
    (hrel : HoistTargetRel target s) (hb : HoistBounded s ds.val.length)
    (h : frontend.nat_op_ground.hoist_targets_at ds idx target c i = ok target') :
    HoistTargetRel target' (hoistTargetsAt (absDecls ds).toArray idxS i.val
        (ConLeche.natOpDeps (absName c)) s) ∧
      HoistBounded (hoistTargetsAt (absDecls ds).toArray idxS i.val
        (ConLeche.natOpDeps (absName c)) s) ds.val.length := by
  rw [frontend.nat_op_ground.hoist_targets_at] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨gs, hgs, h⟩ := h
  obtain ⟨hgsabs, hgswf⟩ := CoreK.nat_op_deps_refines hc hgs
  have hm : (alloc.vec.Vec.len gs).val = gs.val.length := alloc.vec.Vec.len_val gs
  have := hoist_targets_at_loop_refines hds hidx hib gs.val.length target target' s gs
    (alloc.vec.Vec.len gs) 0#usize i (by simp [hm]) hm.symm (by simp [hm]) hgswf hi hrel hb h
  rw [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero, hgsabs] at this
  exact this

/-- `ConLeche/Frontend/NatOpGround.lean:119-136` — `nat_op_ground::hoist_targets`'
loop: the cited second `for i in [0:ds.size]` from `i` on. -/
private theorem hoist_targets_loop_refines {ds : alloc.vec.Vec env.Declaration}
    {idx : ron.hashmap.HashMap name.Name Std.U64}
    {idxS : _root_.Std.HashMap ConLeche.Name Nat}
    (hds : ∀ d ∈ ds.val, DeclarationWF d) (hidx : HoistIdxRel idx idxS)
    (hib : HoistIdxBounded idxS ds.val.length) :
    ∀ (f : Nat) (target target' : ron.hashmap.HashMap Std.U64 Std.U64)
      (s : _root_.Std.HashMap Nat Nat) (n i : Std.Usize),
      n.val - i.val ≤ f → n.val = ds.val.length → i.val ≤ n.val →
      HoistTargetRel target s → HoistBounded s ds.val.length →
      frontend.nat_op_ground.hoist_targets_loop ds idx target n i = ok target' →
      HoistTargetRel target' (hoistTargetsGo (absDecls ds).toArray idxS
          (List.range' i.val (n.val - i.val)) s) ∧
        HoistBounded (hoistTargetsGo (absDecls ds).toArray idxS
          (List.range' i.val (n.val - i.val)) s) ds.val.length := by
  intro f
  induction f with
  | zero =>
    intro target target' s n i hf hn hi hrel hb h
    rw [frontend.nat_op_ground.hoist_targets_loop.eq_def,
      if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
    rw [← h, show n.val - i.val = 0 by omega, List.range'_zero, hoistTargetsGo_nil]
    exact ⟨hrel, hb⟩
  | succ f ih =>
    intro target target' s n i hf hn hi hrel hb h
    rw [frontend.nat_op_ground.hoist_targets_loop.eq_def] at h
    by_cases hlt : i.val < n.val
    · rw [if_pos (show i < n by scalar_tac)] at h
      rw [bind_eq_ok_iff] at h
      obtain ⟨d, hd, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨o, ho, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨target1, htarget1, h⟩ := h
      rw [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = i.val + 1 := by have := Nat.uadd_val hi1; simpa using this
      have hdlt : i.val < ds.val.length := by omega
      have hg : ds.val[i.val]? = some d := ExprOps.vec_index_getElem? hd
      have hdx : ds.val[i.val] = d := by
        rw [List.getElem?_eq_getElem hdlt] at hg; exact Option.some_injective _ hg
      have hdwf : DeclarationWF d := by rw [← hdx]; exact hds _ (List.getElem_mem hdlt)
      obtain ⟨hoabs, howf⟩ := is_nat_op_record_refines hdwf ho
      rw [show n.val - i.val = (n.val - (i.val + 1)) + 1 by omega, List.range'_succ,
        hoistTargetsGo_cons, absDecls_getElem! hg, ← hoabs, ← hi1v]
      cases o with
      | none =>
        simp only [Option.map_none]
        dsimp only at h htarget1 ⊢
        simp only [Result.ok.injEq] at htarget1
        rw [← htarget1] at h
        exact ih target target' s n i1 (by omega) hn (by omega) hrel hb h
      | some c =>
        simp only [Option.map_some]
        dsimp only at h htarget1 ⊢
        rw [bind_eq_ok_iff] at htarget1
        obtain ⟨ii, hii, htarget1⟩ := htarget1
        rw [lift_eq] at hii
        have hiiv : ii.val = i.val := by
          rw [← Result.ok_injective hii]; exact Env.usize_cast_u64_val i
        obtain ⟨hrel1, hb1⟩ := hoist_targets_at_refines hds hidx hib
          (howf c rfl) (by omega) hrel hb htarget1
        rw [hiiv] at hrel1 hb1
        exact ih target1 target' _ n i1 (by omega) hn (by omega) hrel1 hb1 h
    · rw [if_neg (show ¬ i < n by scalar_tac), Result.ok.injEq] at h
      rw [← h, show n.val - i.val = 0 by omega, List.range'_zero, hoistTargetsGo_nil]
      exact ⟨hrel, hb⟩

/-- `ConLeche/Frontend/NatOpGround.lean:106-136` — **`nat_op_ground::hoist_targets`
computes `hoistTargets`**, and its keys and values are positions of the stream.
This was `HoistSpec`, the file's last hypothesis, and it is now proved. -/
theorem hoist_targets_refines {ds : alloc.vec.Vec env.Declaration}
    {t : ron.hashmap.HashMap Std.U64 Std.U64}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.nat_op_ground.hoist_targets ds = ok t) :
    HoistTargetRel t (ConLeche.Frontend.hoistTargets (absDecls ds).toArray) ∧
      HoistBounded (ConLeche.Frontend.hoistTargets (absDecls ds).toArray)
        ds.val.length := by
  rw [frontend.nat_op_ground.hoist_targets] at h
  rw [bind_eq_ok_iff] at h
  obtain ⟨idx, hidx, h⟩ := h
  rw [bind_eq_ok_iff] at h
  obtain ⟨target0, htarget0, h⟩ := h
  have hsize : (absDecls ds).toArray.size = ds.val.length := by
    simp [absDecls]
  have hrelidx := hoist_name_index_refines hds hidx
  rw [hsize] at hrelidx
  have hbidx : HoistIdxBounded (hoistIdx (absDecls ds).toArray
      (List.range' 0 ds.val.length) ∅) ds.val.length := by
    refine hoistIdx_bounded _ _ ∅ (fun i hi => by
      rw [List.mem_range'_1] at hi; omega) ?_
    intro g j hg; simp at hg
  have hn : (alloc.vec.Vec.len ds).val = ds.val.length := alloc.vec.Vec.len_val ds
  have := hoist_targets_loop_refines hds hrelidx hbidx ds.val.length target0 t ∅
    (alloc.vec.Vec.len ds) 0#usize (by simp [hn]) hn.symm (by simp [hn])
    (tgt_new htarget0) (by intro k v hk; simp at hk) h
  rw [show ((0#usize : Std.Usize).val) = 0 from rfl, Nat.sub_zero, hn,
    ← hsize, ← hoistTargets_split] at this
  rw [hsize] at this
  exact this

/-! ### Nothing is left over

This file's last hypothesis was `HoistSpec`, the `Refine/IndSpec.lean`-style
`Prop` that the port's `hoist_targets` computes `hoistTargets`.  It is now the
theorem `hoist_targets_refines` above, and **every theorem of this file is
hypothesis-free**: `prepare_prelude_refines` asks for well-formedness of its
input and nothing else. -/

/-! ### The receipt -/

/-- `ConLeche/Frontend/NatOpGround.lean:162` — `nat_op_ground::hoist_moved_names`'
inner loop: the cited `(ds[k]!.names).toArray`, one name at a time. -/
private theorem hoist_moved_names_inner {ns : alloc.vec.Vec name.Name}
    (hns : NamesWF ns) :
    ∀ f : Nat, ∀ (j : Std.Usize) (out v : alloc.vec.Vec name.Name),
      ns.val.length - j.val ≤ f → j.val ≤ ns.val.length → NamesWF out →
      frontend.nat_op_ground.hoist_moved_names_loop0_loop0 out ns
          (alloc.vec.Vec.len ns) j = ok v →
      absNames v = absNames out ++ (absNames ns).drop j.val ∧ NamesWF v := by
  have hm : (alloc.vec.Vec.len ns).val = ns.val.length := alloc.vec.Vec.len_val ns
  intro f
  induction f with
  | zero =>
    intro j out v hf hj hout h
    have hjeq : j.val = ns.val.length := by omega
    rw [frontend.nat_op_ground.hoist_moved_names_loop0_loop0.eq_def] at h
    rw [if_neg (show ¬ j < alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
    subst h
    exact ⟨by rw [hjeq, absNames, List.drop_eq_nil_of_le (by simp [absNames])]; simp, hout⟩
  | succ f ih =>
    intro j out v hf hj hout h
    rw [frontend.nat_op_ground.hoist_moved_names_loop0_loop0.eq_def] at h
    by_cases hlt : j.val < ns.val.length
    · rw [if_pos (show j < alloc.vec.Vec.len ns by scalar_tac)] at h
      simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨n0, hn0, out1, hout1, j1, hj1, h⟩ := h
      have hj1v : j1.val = j.val + 1 := by have := Nat.uadd_val hj1; simpa using this
      have hng := ExprOps.vec_index_getElem? hn0
      have hnx : ns.val[j.val] = n0 := by
        rw [List.getElem?_eq_getElem hlt] at hng; exact Option.some_injective _ hng
      have hn0wf : NameWF n0 := hns _ (List.mem_of_getElem? hng)
      have hout1wf : NamesWF out1 := by
        intro y hy
        rw [vec_push_val hout1] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hout y hy
        · rw [List.mem_singleton.mp hy]; exact hn0wf
      obtain ⟨habs, hwf⟩ := ih j1 out1 v (by omega) (by omega) hout1wf h
      refine ⟨?_, hwf⟩
      rw [habs, hj1v, absNames, vec_push_val hout1]
      rw [show (absNames ns).drop j.val
          = absName n0 :: (absNames ns).drop (j.val + 1) from by
        rw [absNames, List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map,
          hnx]]
      simp [absNames]
    · rw [if_neg (show ¬ j < alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
      subst h
      have hjeq : j.val = ns.val.length := by omega
      exact ⟨by rw [hjeq, absNames, List.drop_eq_nil_of_le (by simp [absNames])]; simp, hout⟩

/-- `ConLeche/Frontend/NatOpGround.lean:162` — `nat_op_ground::hoist_moved_names`'
outer loop: the cited `moved.flatMap fun k => (ds[k]!.names).toArray`. -/
private theorem hoist_moved_names_loop_refines {ds : alloc.vec.Vec env.Declaration}
    {moved : alloc.vec.Vec Std.U64} (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (hmoved : ∀ k ∈ moved.val, k.val ≤ Std.Usize.max) :
    ∀ f : Nat, ∀ (a : Std.Usize) (out v : alloc.vec.Vec name.Name),
      moved.val.length - a.val ≤ f → a.val ≤ moved.val.length → NamesWF out →
      frontend.nat_op_ground.hoist_moved_names_loop0 ds moved out
          (alloc.vec.Vec.len moved) a = ok v →
      absNames v = absNames out ++ ((moved.val.drop a.val).map (·.val)).flatMap
        (fun k => ConLeche.Declaration.names ((ds.val.map absDeclaration)[k]!)) := by
  have hm : (alloc.vec.Vec.len moved).val = moved.val.length :=
    alloc.vec.Vec.len_val moved
  intro f
  induction f with
  | zero =>
    intro a out v hf ha hout h
    have haeq : a.val = moved.val.length := by omega
    rw [frontend.nat_op_ground.hoist_moved_names_loop0.eq_def] at h
    rw [if_neg (show ¬ a < alloc.vec.Vec.len moved by scalar_tac), Result.ok.injEq] at h
    rw [← h, haeq, List.drop_length]; simp
  | succ f ih =>
    intro a out v hf ha hout h
    rw [frontend.nat_op_ground.hoist_moved_names_loop0.eq_def] at h
    by_cases hlt : a.val < moved.val.length
    · rw [if_pos (show a < alloc.vec.Vec.len moved by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq] at h
      obtain ⟨kk, hkk, kw, hkw, d, hd, ns, hns, out1, hout1, a1, ha1, h⟩ := h
      have ha1v : a1.val = a.val + 1 := by have := Nat.uadd_val ha1; simpa using this
      have hkg := ExprOps.vec_index_getElem? hkk
      have hkx : moved.val[a.val] = kk := by
        rw [List.getElem?_eq_getElem hlt] at hkg; exact Option.some_injective _ hkg
      have hkwv : kw.val = kk.val := by
        rw [← Result.ok_injective hkw]
        exact Env.u64_cast_usize_val
          (hmoved kk (by rw [← hkx]; exact List.getElem_mem hlt))
      have hdg := ExprOps.vec_index_getElem? hd
      have hdlt : kw.val < ds.val.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hdg
        simp at hdg
      have hdx : ds.val[kw.val] = d := by
        rw [List.getElem?_eq_getElem hdlt] at hdg; exact Option.some_injective _ hdg
      have hdwf : DeclarationWF d := hds _ (List.mem_of_getElem? hdg)
      obtain ⟨hnsabs, hnswf⟩ := declaration_names_refines hdwf hns
      obtain ⟨hinner, hinnerwf⟩ :=
        hoist_moved_names_inner hnswf ns.val.length 0#usize out out1
          (by scalar_tac) (by scalar_tac) hout hout1
      rw [ih a1 out1 v (by omega) (by omega) hinnerwf h, ha1v, hinner]
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero]
      rw [List.drop_eq_getElem_cons hlt, hkx]
      simp only [List.map_cons, List.flatMap_cons]
      rw [hnsabs, show (ds.val.map absDeclaration)[kk.val]! = absDeclaration d from by
        rw [← hkwv, getElem!_pos _ _ (by simpa using hdlt), List.getElem_map, hdx]]
      simp
    · rw [if_neg (show ¬ a < alloc.vec.Vec.len moved by scalar_tac), Result.ok.injEq] at h
      have haeq : a.val = moved.val.length := by omega
      rw [← h, haeq, List.drop_length]; simp

/-- `ConLeche/Frontend/NatOpGround.lean:162` — **`nat_op_ground::hoist_moved_names`
refines the cited `moved.flatMap fun k => (ds[k]!.names).toArray`**: the
driver's receipt. -/
theorem hoist_moved_names_refines {ds : alloc.vec.Vec env.Declaration}
    {moved : alloc.vec.Vec Std.U64} {v : alloc.vec.Vec name.Name}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (hmoved : ∀ k ∈ moved.val, k.val ≤ Std.Usize.max)
    (h : frontend.nat_op_ground.hoist_moved_names ds moved = ok v) :
    absNames v = (moved.val.map (·.val)).flatMap
      (fun k => ConLeche.Declaration.names ((ds.val.map absDeclaration)[k]!)) := by
  rw [frontend.nat_op_ground.hoist_moved_names] at h
  have := hoist_moved_names_loop_refines hds hmoved moved.val.length 0#usize _ v
    (by scalar_tac) (by scalar_tac) (fun y hy => by simp [alloc.vec.Vec.new] at hy) h
  simpa [absNames, alloc.vec.Vec.new] using this

/-! ### `apply_hoist` and the hoist itself -/

/-- `ConLeche/Frontend/NatOpGround.lean:138-162` — **`nat_op_ground::apply_hoist`
refines `applyHoist`'s records.**  Its second component is the driver's receipt
(`hoist_moved_names_refines` above); the fold never sees it. -/
theorem apply_hoist_refines {ds : alloc.vec.Vec env.Declaration}
    {target : ron.hashmap.HashMap Std.U64 Std.U64} {s : _root_.Std.HashMap Nat Nat}
    {r : (alloc.vec.Vec env.Declaration) × (alloc.vec.Vec name.Name)}
    (hrel : HoistTargetRel target s) (hb : HoistBounded s ds.val.length)
    (h : frontend.nat_op_ground.apply_hoist ds target = ok r) :
    absDecls r.1 = (ConLeche.Frontend.applyHoist (absDecls ds).toArray s).1.toList := by
  rw [frontend.nat_op_ground.apply_hoist] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨moved, hmoved, ord, hord, out, hout, names, -, hr⟩ := h
  subst hr
  have hlen : (alloc.vec.Vec.len ds).val = ds.val.length := alloc.vec.Vec.len_val ds
  have hmv : moved.val.map (·.val)
      = (List.range ds.val.length).filter (fun k => s.contains k) := by
    rw [← hlen]; exact hoist_moved_idxs_refines hrel hmoved
  have hov : ord.val.map (·.val)
      = (List.range ds.val.length).mergeSort (fun a b => !hoistLt s b a) := by
    rw [hoist_order_refines hrel hord, hlen, hmv]
    exact hoistBuckets_eq_mergeSort s ds.val.length hb
  have hordlt : ∀ k ∈ ord.val, k.val ≤ Std.Usize.max := by
    intro k hk
    have hmem : k.val ∈ (List.range ds.val.length).mergeSort
        (fun a b => !hoistLt s b a) := by
      rw [← hov]; exact List.mem_map_of_mem hk
    have hr2 := (List.mergeSort_perm (List.range ds.val.length)
      (fun a b => !hoistLt s b a)).mem_iff.mp hmem
    rw [List.mem_range] at hr2
    have hb2 : ds.val.length ≤ Std.Usize.max := by
      have := ds.slice.property; scalar_tac
    omega
  rw [hoist_reorder_refines hordlt hout, hov, applyHoist_fst]
  simp [absDecls]

/-- `ConLeche/Frontend/NatOpGround.lean:164-169` — **`nat_op_ground::hoist_nat_op_ground`
refines `hoistNatOpGround`'s records**: either the target map is empty and the
vector comes back untouched, or `apply_hoist` rebuilds it. -/
theorem hoist_nat_op_ground_refines
    {ds : alloc.vec.Vec env.Declaration}
    {r : (alloc.vec.Vec env.Declaration) × (alloc.vec.Vec name.Name)}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.nat_op_ground.hoist_nat_op_ground ds = ok r) :
    absDecls r.1
      = (ConLeche.Frontend.hoistNatOpGround (absDecls ds).toArray).1.toList := by
  rw [frontend.nat_op_ground.hoist_nat_op_ground] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨target, htarget, i, hi, h⟩ := h
  obtain ⟨hrel, hb⟩ := hoist_targets_refines hds htarget
  have hiv : i.val = (ConLeche.Frontend.hoistTargets (absDecls ds).toArray).size := by
    rw [(HashMap.len_refines hrel.inv hi).1, hrel.size]
  rw [ConLeche.Frontend.hoistNatOpGround]
  by_cases hz : i = 0#usize
  · rw [if_pos hz, Result.ok.injEq] at h
    have hi0 : i.val = 0 := by rw [hz]; rfl
    rw [show r.1 = ds from by rw [← h], if_pos (by
      rw [_root_.Std.HashMap.isEmpty_eq_size_eq_zero, ← hiv, hi0]; rfl)]
  · rw [if_neg hz] at h
    have hine : i.val ≠ 0 := fun hc => hz (by scalar_tac)
    rw [if_neg (by
      rw [_root_.Std.HashMap.isEmpty_eq_size_eq_zero, ← hiv]
      simp [hine])]
    exact apply_hoist_refines hrel hb h

/-! ## The capstone

`prepare::prepare_d` is `prepareD` and `prepare::prepare_prelude` is
`preparePrelude`.  The hoist's target map enters through
`hoist_targets_refines`; there is no hypothesis left. -/

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
theorem prepare_d_refines {pre : frontend.prepare.PreludeIx}
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
  exact hoist_nat_op_ground_refines hallwf hhoist

/-- `ConLeche/Frontend/Prepare.lean:165-172` — **`prepare::prepare_prelude`
refines `preparePrelude`**: the parsed stream, prepared for the fold, is
con-leche's prepared stream record for record and in the same order.  This is
what task #87's headline composes with. -/
theorem prepare_prelude_refines {pre : frontend.prepare.PreludeIx}
    {ds out : alloc.vec.Vec env.Declaration}
    (hpre : PreludeIxWF pre) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : frontend.prepare.prepare_prelude pre ds = ok out) :
    absDecls out
      = (ConLeche.Frontend.preparePrelude (absPreludeIx pre) (absDecls ds).toArray).toList := by
  rw [frontend.prepare.prepare_prelude] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨p, hp, hout⟩ := h
  rw [← hout, ConLeche.Frontend.preparePrelude]
  exact prepare_d_refines hpre hds hp




/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Every theorem of this file is a plain forward argument over the generated model
and reaches past nothing but Lean's own three axioms.  The file's one-time
hypothesis `HoistSpec` is gone: `hoist_targets_refines` proves it, and the
capstone `prepare_prelude_refines` carries no hypothesis but its input's
well-formedness. -/

/-- info: 'ConRon.Refine.Frontend.prepare_prelude_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prepare_prelude_refines

/-- info: 'ConRon.Refine.Frontend.hoist_nat_op_ground_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoist_nat_op_ground_refines

/-- info: 'ConRon.Refine.Frontend.hoist_targets_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoist_targets_refines

/-- info: 'ConRon.Refine.Frontend.front_of_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms front_of_refines


end ConRon.Refine.Frontend
