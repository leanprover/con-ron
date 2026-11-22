/-
# `ConRon.Refine2.Modular.WorkerCopies` — `modular/worker.rs`: a compared challenge's copies and holes

**Task #166, Theorem 2.**  The functions of `worker.rs` that check a compared challenge's
copies against the loaded constants of their names and its own records for holes, against their
twins (`Arena/Modular/Worker.lean`).

* The pure helpers are `@[lockstep]` `LSP` lemmas (`TwinEq` of the twin's expression):
  `infos_beq`, `copy_rec_eq`, `ctor_names`, `split_ctor_names`, `names_nodup_go` (from the empty
  set), `find_named`, `any_ind`, `push_all`, `ifenv_layer(0, 0, false, false)`.
* The checks that reject at the twin's kind are in the lockstep shape (`LS`): `uses_sorry`,
  `copy_stmt`, `same_def_up_to_levels`, `block_read_b`, `copy_reads_b`, `find_constant`,
  `copy_ind_ok`, `is_hole_rec` (at any `UsedConsts` instance the twin's `uses` relates to,
  `UsedRel`), `ctx_layer` (over a tier whose frozen base is empty, the twin's empty layer).
* The checks whose rejects name records (`copy_against`, `copy_check`, `own_hole_ok`,
  `own_holes_ok`, `copies_ok`) claim their accept only (`LA`): the twin's message reads the names
  back with `readName`, which declines a dangling handle at another kind.  `copies_ok` takes the
  accepts of `reach::owner_map` (lane L2's, no Theorem 2 yet) and `copy_recs`, `own_holes_ok` that of
  `recs_loaded` (lane L3-H1's), as hypotheses.
* `copy_msg` only builds a reject: no theorem.
-/
import ConRon.Refine2.Frontend.Compare
import ConRon.Refine2.Inductives.IotaRead
import ConRon.Refine2.Inductives.Positivity
import ConRon.Refine2.Checker.Basis
import ConRon.Refine2.Checker.LitFlags
import ConRon.Refine2.Checker.Install
import ConRon.Refine2.Frontend.Olean.Index
import ConRon.Refine2.Modular.Graph
import ConRon.Arena.Modular.Worker
import ConRon.Refine2.Modular.ReachCheck

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.worker

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Lockstep
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine2.Frontend (absIDeclArr absNIdxArr)

/-! ## The pure helpers -/

theorem infos_beq_loop_eq (b b2 : alloc.vec.Vec arena.env.IConstantInfo)
    (hl : b.val.length = b2.val.length) :
    ∀ (i : Std.Usize) (o : Bool), infos_beq_loop b b2 i = ok o →
      o = (absICILFrom b i == absICILFrom b2 i) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) b.val.length
    (fun i (_ : Unit) => ∀ o, infos_beq_loop b b2 i = ok o →
      o = (absICILFrom b i == absICILFrom b2 i)) ?_ ?_ i ()
  · intro i _ hn o h
    rw [infos_beq_loop.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len b by scalar_tac)] at h
    cases Result.ok_injective h
    simp [absICILFrom, List.drop_eq_nil_of_le hn, List.drop_eq_nil_of_le (hl ▸ hn)]
  · intro i _ hi ih o h
    rw [infos_beq_loop.eq_def, ite_eq_left (show i < alloc.vec.Vec.len b by scalar_tac)] at h
    peel h as x, hx
    peel h as y, hy
    peel h as c, hc
    have ex := vec_index_some hx
    have ey := vec_index_some hy
    have ec := ConRon.Refine2.i_constant_info_beq_refines hc
    have hi2 : i.val < b2.val.length := hl ▸ hi
    have dx : b.val.drop i.val = x :: b.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp [List.getElem?_eq_some_iff.mp ex |>.2]
    have dy : b2.val.drop i.val = y :: b2.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi2]; simp [List.getElem?_eq_some_iff.mp ey |>.2]
    simp only [absICILFrom, dx, dy, List.map_cons, List.cons_beq_cons]
    by_cases cc : c = true
    · rw [ite_eq_left cc] at h
      peel h as i2, hi2'
      have hv := ConRon.Refine.Nat.uadd_val hi2'
      have := ih i2 () (by simp at hv; omega) o h
      subst cc
      simp only [absICILFrom] at this
      rw [this, show i2.val = i.val + 1 by simp at hv; omega]
      simp_all
    · rw [ite_eq_right cc] at h
      cases Result.ok_injective h
      simp_all

/-- **`infos_beq` is `==`** on the abstracted blocks. -/
@[lockstep] theorem infos_beq_spec (b b2 : alloc.vec.Vec arena.env.IConstantInfo) :
    LSP (infos_beq b b2) (fun o => TwinEq (absICIL b == absICIL b2) o) := by
  intro o h
  rw [infos_beq] at h
  by_cases hl : alloc.vec.Vec.len b = alloc.vec.Vec.len b2
  · rw [ite_eq_right (by simp [hl])] at h
    have hl' : b.val.length = b2.val.length := by
      have := congrArg Aeneas.Std.UScalar.val hl; simpa using this
    rw [TwinEq, infos_beq_loop_eq b b2 hl' _ o h]
    simp [absICILFrom, absICIL]
  · rw [ite_eq_left (by simp [hl])] at h
    cases Result.ok_injective h
    have hl' : b.val.length ≠ b2.val.length := fun e => hl (by scalar_tac)
    have : (absICIL b == absICIL b2) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      exact hl' (by simpa [absICIL] using congrArg List.length e)
    rw [TwinEq, this]

/-- **`copy_rec_eq` is `copyRecEq`.** -/
@[lockstep] theorem copy_rec_eq_spec (d e : arena.env.IDeclaration) :
    LSP (copy_rec_eq d e)
      (fun o => TwinEq (Modular.copyRecEq (absIDeclaration d) (absIDeclaration e)) o) := by
  intro o h
  cases d <;> cases e <;> simp only [copy_rec_eq, Result.ok.injEq] at h <;>
    try (subst h; rfl)
  rename_i b n b2 n2
  by_cases hn : n = n2
  · rw [ite_eq_left hn] at h
    have := infos_beq_spec b b2 o h
    subst hn
    simp only [TwinEq, absIDeclaration, Modular.copyRecEq] at this ⊢
    simpa [absICIL] using this
  · rw [ite_eq_right hn] at h
    cases Result.ok_injective h
    have : absU n ≠ absU n2 := fun e => hn (UScalar.eq_of_val_eq e)
    simp [TwinEq, absIDeclaration, Modular.copyRecEq, this]

theorem ctor_names_loop_eq (xs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx), ctor_names_loop xs out i = ok o →
      absNIdxL o = absNIdxL out ++ (absCtorsLFrom xs i).map (·.1.name) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i out => ∀ o, ctor_names_loop xs out i = ok o →
      absNIdxL o = absNIdxL out ++ (absCtorsLFrom xs i).map (·.1.name)) ?_ ?_ i
  · intro i out hn o h
    rw [ctor_names_loop.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len xs by scalar_tac)] at h
    cases Result.ok_injective h
    simp [absCtorsLFrom, List.drop_eq_nil_of_le hn]
  · intro i out hi ih o h
    rw [ctor_names_loop.eq_def, ite_eq_left (show i < alloc.vec.Vec.len xs by scalar_tac)] at h
    peel h as x, hx
    peel h as n, hn
    peel h as out1, hout1
    peel h as i2, hi2
    have ex := vec_index_some hx
    have hv := ConRon.Refine.Nat.uadd_val hi2
    rw [ih i2 out1 (by simp at hv; omega) o h]
    simp only [absNIdxL, absCtorsLFrom]
    rw [ConRon.Refine.vec_push_val hout1, show i2.val = i.val + 1 by simp at hv; omega,
      nidx_dup2_ok hn]
    have dx : xs.val.drop i.val = x :: xs.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp [List.getElem?_eq_some_iff.mp ex |>.2]
    simp [dx, absIConstantVal_name]

/-- **`ctor_names` is `map (·.1.name)`** of the constructors. -/
@[lockstep] theorem ctor_names_spec (xs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSP (ctor_names xs) (fun o => TwinEq ((absCtorsL xs).map (·.1.name)) (absNIdxL o)) := by
  intro o h
  rw [ctor_names] at h
  rw [TwinEq, ctor_names_loop_eq xs _ _ o h]
  simp [absNIdxL, absCtorsLFrom, absCtorsL]

theorem split_ctor_names_loop_eq (xs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      split_ctor_names_loop xs out i = ok o →
      absNIdxL o = absNIdxL out ++ (absCtors3LFrom xs i).map (·.1.name) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i out => ∀ o, split_ctor_names_loop xs out i = ok o →
      absNIdxL o = absNIdxL out ++ (absCtors3LFrom xs i).map (·.1.name)) ?_ ?_ i
  · intro i out hn o h
    rw [split_ctor_names_loop.eq_def,
      ite_eq_right (show ¬ i < alloc.vec.Vec.len xs by scalar_tac)] at h
    cases Result.ok_injective h
    simp [absCtors3LFrom, List.drop_eq_nil_of_le hn]
  · intro i out hi ih o h
    rw [split_ctor_names_loop.eq_def,
      ite_eq_left (show i < alloc.vec.Vec.len xs by scalar_tac)] at h
    peel h as x, hx
    peel h as n, hn
    peel h as out1, hout1
    peel h as i2, hi2
    have ex := vec_index_some hx
    have hv := ConRon.Refine.Nat.uadd_val hi2
    rw [ih i2 out1 (by simp at hv; omega) o h]
    simp only [absNIdxL, absCtors3LFrom]
    rw [ConRon.Refine.vec_push_val hout1, show i2.val = i.val + 1 by simp at hv; omega,
      nidx_dup2_ok hn]
    have dx : xs.val.drop i.val = x :: xs.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp [List.getElem?_eq_some_iff.mp ex |>.2]
    simp [dx, absIConstantVal_name]

/-- **`split_ctor_names` is `map (·.1.name)`** of a split's constructors. -/
@[lockstep] theorem split_ctor_names_spec
    (xs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) :
    LSP (split_ctor_names xs) (fun o => TwinEq ((absCtors3L xs).map (·.1.name)) (absNIdxL o)) := by
  intro o h
  rw [split_ctor_names] at h
  rw [TwinEq, split_ctor_names_loop_eq xs _ _ o h]
  simp [absNIdxL, absCtors3LFrom, absCtors3L]

/-- `names_nodup_go` from `k` on, against `namesNodupGo` of the rest. -/
theorem names_nodup_go_loop_eq' (ns : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (k : Std.Usize) (s : ron.hashmap2.HashMap2 arena.handle.NIdx Bool) (S : _root_.Std.HashSet NIdx)
      (o : Bool × ron.hashmap2.HashMap2 arena.handle.NIdx Bool), NSet s S →
      names_nodup_go_loop s ns k = ok o →
      o.1 = (Modular.namesNodupGo S ((ns.val.drop k.val).map absNIdx)).1 := by
  intro k
  refine cursor_induction (fun i : Std.Usize => i.val) ns.val.length
    (fun k (_ : Unit) => ∀ s S o, NSet s S → names_nodup_go_loop s ns k = ok o →
      o.1 = (Modular.namesNodupGo S ((ns.val.drop k.val).map absNIdx)).1) ?_ ?_ k ()
  · intro k _ hn s S o _ h
    rw [names_nodup_go_loop.eq_def,
      ite_eq_right (show ¬ k < alloc.vec.Vec.len ns by scalar_tac)] at h
    cases Result.ok_injective h
    simp [List.drop_eq_nil_of_le hn, Modular.namesNodupGo]
  · intro k _ hi ih s S o hs h
    rw [names_nodup_go_loop.eq_def,
      ite_eq_left (show k < alloc.vec.Vec.len ns by scalar_tac)] at h
    peel h as x, hx
    have ex := vec_index_some hx
    have dx : ns.val.drop k.val = x :: ns.val.drop (k.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp [List.getElem?_eq_some_iff.mp ex |>.2]
    rw [dx, List.map_cons, Modular.namesNodupGo]
    peel h as b, hb
    have eb := SetRel.contains_key nidx_eq2 hs hb
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      cases Result.ok_injective h
      rw [ite_eq_left (by rw [← eb]; exact cb)]
    · rw [ite_eq_right cb] at h
      peel h as n1, hn1
      cases nidx_dup2_ok hn1
      peel h as p, hp
      obtain ⟨old, s1⟩ := p
      have hs1 := SetRel.insert nidx_eq2 absNIdx_inj hs hp
      peel h as k1, hk1
      have hv := ConRon.Refine.Nat.uadd_val hk1
      rw [ite_eq_right (by rw [← eb]; exact cb)]
      rw [ih k1 () (by simp at hv; omega) s1 _ o hs1 h, show k1.val = k.val + 1 by simp at hv; omega]

/-- An empty memo of names is the empty name set. -/
theorem nset_of_nmemo_empty {s : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    (hs : Lockstep.NMemoRel s ∅) : NSet s {} := by
  refine ⟨hs.2, fun k => ?_⟩
  have := hs.1 k trivial
  simp only [Std.HashMap.getElem?_empty, Option.map_eq_none_iff] at this
  simp [this]

/-- **`names_nodup_go` from `0`, from the empty set, is `namesNodupGo {}`.** -/
@[lockstep] theorem names_nodup_go_spec {s : ron.hashmap2.HashMap2 arena.handle.NIdx Bool}
    (hs : Lockstep.NMemoRel s ∅) (ns : alloc.vec.Vec arena.handle.NIdx) :
    LSP (names_nodup_go s ns 0#usize)
      (fun o => TwinEq (Modular.namesNodupGo {} (absNIdxL ns)).1 o.1) := by
  intro o h
  rw [names_nodup_go] at h
  rw [TwinEq, names_nodup_go_loop_eq' ns _ s {} o (nset_of_nmemo_empty hs) h]
  simp [absNIdxL]

theorem find_named_loop_eq (cs : alloc.vec.Vec arena.env.IConstantInfo) (n : arena.handle.NIdx) :
    ∀ (i : Std.Usize) o, find_named_loop cs n i = ok o →
      o.map absIConstantInfo = Modular.findNamed (absICILFrom cs i) (absNIdx n) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i (_ : Unit) => ∀ o, find_named_loop cs n i = ok o →
      o.map absIConstantInfo = Modular.findNamed (absICILFrom cs i) (absNIdx n)) ?_ ?_ i ()
  · intro i _ hn o h
    rw [find_named_loop.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len cs by scalar_tac)] at h
    cases Result.ok_injective h
    simp [absICILFrom, List.drop_eq_nil_of_le hn, Modular.findNamed]
  · intro i _ hi ih o h
    rw [find_named_loop.eq_def, ite_eq_left (show i < alloc.vec.Vec.len cs by scalar_tac)] at h
    peel h as x, hx
    have ex := vec_index_some hx
    have dx : cs.val.drop i.val = x :: cs.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp [List.getElem?_eq_some_iff.mp ex |>.2]
    simp only [absICILFrom, dx, List.map_cons, Modular.findNamed, List.find?_cons]
    peel h as n1, hn1
    have en1 := i_constant_info_name_abs hn1
    peel h as b, hb
    have eb := nidx_eq2_val hb
    by_cases cb : b = true
    · rw [ite_eq_left cb] at h
      peel h as c, hc
      cases Result.ok_injective h
      rw [← en1, ← eb, cb]
      simp [i_constant_info_dup_abs hc]
    · rw [ite_eq_right cb] at h
      peel h as i2, hi2
      have hv := ConRon.Refine.Nat.uadd_val hi2
      rw [← en1, ← eb, show b = false by simpa using cb]
      have := ih i2 () (by simp at hv; omega) o h
      rw [this]
      simp only [absICILFrom, show i2.val = i.val + 1 by simp at hv; omega, Modular.findNamed]

/-- **`find_named` is `findNamed`.** -/
@[lockstep] theorem find_named_spec (cs : alloc.vec.Vec arena.env.IConstantInfo) (n : arena.handle.NIdx) :
    LSP (find_named cs n)
      (fun o => TwinEq (Modular.findNamed (absICIL cs) (absNIdx n)) (o.map absIConstantInfo)) := by
  intro o h
  rw [TwinEq, find_named_loop_eq cs n 0#usize o h]
  simp [absICILFrom, absICIL]

theorem any_ind_loop_eq (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (i : Std.Usize) o, any_ind_loop ds i = ok o →
      o = Modular.anyInd ((ds.val.drop i.val).map absIDeclaration).toArray := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ds.val.length
    (fun i (_ : Unit) => ∀ o, any_ind_loop ds i = ok o →
      o = Modular.anyInd ((ds.val.drop i.val).map absIDeclaration).toArray) ?_ ?_ i ()
  · intro i _ hn o h
    rw [any_ind_loop.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len ds by scalar_tac)] at h
    cases Result.ok_injective h
    simp [List.drop_eq_nil_of_le hn, Modular.anyInd]
  · intro i _ hi ih o h
    rw [any_ind_loop.eq_def, ite_eq_left (show i < alloc.vec.Vec.len ds by scalar_tac)] at h
    peel h as x, hx
    have ex := vec_index_some hx
    have dx : ds.val.drop i.val = x :: ds.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp [List.getElem?_eq_some_iff.mp ex |>.2]
    rw [dx, List.map_cons]
    clear dx ex hx
    cases x <;> simp only at h <;>
      first
      | (cases Result.ok_injective h; simp [Modular.anyInd, absIDeclaration])
      | (obtain ⟨i2, hi2, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
         have hv := ConRon.Refine.Nat.uadd_val hi2
         rw [ih i2 () (by simp at hv; omega) o h2, show i2.val = i.val + 1 by simp at hv; omega]
         simp [Modular.anyInd, absIDeclaration])

/-- **`any_ind` is `anyInd`.** -/
@[lockstep] theorem any_ind_spec (ds : alloc.vec.Vec arena.env.IDeclaration) :
    LSP (any_ind ds) (fun o => TwinEq (Modular.anyInd (absIDeclArr ds)) o) := by
  intro o h
  rw [TwinEq, any_ind_loop_eq ds 0#usize o h]
  simp only [absIDeclArr, Lockstep.usize_zero_val', List.drop_zero]

/-! ## The statements and blocks a copy is read by -/

open Lockstep in
/-- **`uses_sorry` is `usesSorry`.** -/
@[lockstep] theorem uses_sorry_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (uses_sorry pers st v) lst (Modular.usesSorry (absEIdx v)) := by
  rw [uses_sorry, Modular.usesSorry]
  lockstep

open Lockstep in
/-- **`copy_stmt` is `copyStmt`.** -/
@[lockstep] theorem copy_stmt_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = a.map absIConstantVal) (copy_stmt pers st d) lst
      (Modular.copyStmt (absIDeclaration d)) := by
  cases d <;> rw [copy_stmt.eq_def] <;> simp only [absIDeclaration, Modular.copyStmt] <;> lockstep

open Lockstep in
/-- **`same_def_up_to_levels` is `sameDefUpToLevels`.** -/
@[lockstep] theorem same_def_up_to_levels_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (c c2 : arena.env.IConstantInfo) :
    LS pers (fun a b => b = a) (same_def_up_to_levels pers st c c2) lst
      (Modular.sameDefUpToLevels (absIConstantInfo c) (absIConstantInfo c2)) := by
  rw [same_def_up_to_levels, Modular.sameDefUpToLevels]
  lockstep

open Lockstep in
/-- **`block_read_b` is `blockReadB`.** -/
@[lockstep] theorem block_read_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = a) (block_read_b pers st d) lst
      (Modular.blockReadB (absIDeclaration d)) := by
  cases d <;> rw [block_read_b.eq_def] <;> simp only [absIDeclaration, Modular.blockReadB] <;>
    (try rw [show ∀ b : alloc.vec.Vec arena.env.IConstantInfo, b.val.map absIConstantInfo = absICIL b
      from fun _ => rfl]) <;>
    lockstep

attribute [local lockstep] decl_constants_ls
attribute [local lockstep high] bt_block_recs_ls0

section
attribute [local lockstep_simp] absBlockShape_recs

open Lockstep in
/-- **`copy_reads_b` is `copyReadsB`**, against a related layer. -/
@[lockstep] theorem copy_reads_b_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hfe : IFEnvRelI pers fe lfe)
    (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = a) (copy_reads_b pers st fe d) lst
      (Modular.copyReadsB lfe (absIDeclaration d)) := by
  have hctx := hfe.coreCtx
  cases d <;> rw [copy_reads_b.eq_def] <;> simp only [absIDeclaration, Modular.copyReadsB] <;>
    lockstep

end

open Lockstep in
/-- **`find_constant` is `findConstant`.** -/
@[lockstep] theorem find_constant_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (e : arena.env.IDeclaration) (n : arena.handle.NIdx) :
    LS pers (fun a b => b = a.map absIConstantInfo) (find_constant pers st e n) lst
      (Modular.findConstant (absIDeclaration e) (absNIdx n)) := by
  rw [find_constant, Modular.findConstant]
  lockstep

open Lockstep in
/-- **`copy_ind_ok` is `copyIndOk`.** -/
@[lockstep] theorem copy_ind_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hfe : IFEnvRelI pers fe lfe)
    (d e : arena.env.IDeclaration) :
    LS pers (fun a b => b = a) (copy_ind_ok pers st fe d e) lst
      (Modular.copyIndOk lfe (absIDeclaration d) (absIDeclaration e)) := by
  rw [copy_ind_ok, Modular.copyIndOk]
  lockstep

open Lockstep in
/-- **`is_hole_rec` is `isHoleRec`**, at any `UsedConsts` instance the twin's `uses` relates
to. -/
@[lockstep] theorem is_hole_rec_ls {U : Type} {inst : frontend.nat_op_ground.UsedConsts U} {u : U}
    {used : IDeclaration → AM (Array NIdx)} {pers : arena.store.PersTier}
    (hu : ConRon.Refine2.Frontend.UsedRel inst u used pers) {st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = a) (is_hole_rec inst u pers st d) lst
      (Modular.isHoleRec used (absIDeclaration d)) := by
  have hU := @ConRon.Refine2.Frontend.used_consts_ls U inst u used pers hu
  cases d <;> rw [is_hole_rec.eq_def] <;> simp only [absIDeclaration, Modular.isHoleRec] <;>
    lockstep

/-! ## The context's layer -/

open Lockstep in
/-- **`push_all` is `foldl IFEnv.push`**, from the cursor on. -/
theorem push_all_loop_rel {pers : arena.store.PersTier} (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    ∀ (i : Std.Usize) (fe : arena.env.IFEnv) (lf : IFEnv) (r : arena.env.IFEnv),
      IFEnvRelI pers fe lf → push_all_loop pers cs fe i = ok r →
      IFEnvRelI pers r ((absICILFrom cs i).foldl IFEnv.push lf) := by
  intro i fe
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i fe => ∀ lf r, IFEnvRelI pers fe lf → push_all_loop pers cs fe i = ok r →
      IFEnvRelI pers r ((absICILFrom cs i).foldl IFEnv.push lf)) ?_ ?_ i fe
  · intro i fe hn lf r hfe h
    rw [push_all_loop.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len cs by scalar_tac)] at h
    cases Result.ok_injective h
    simpa [absICILFrom, List.drop_eq_nil_of_le hn] using hfe
  · intro i fe hi ih lf r hfe h
    rw [push_all_loop.eq_def, ite_eq_left (show i < alloc.vec.Vec.len cs by scalar_tac)] at h
    peel h as x, hx
    peel h as x1, hx1
    peel h as fe1, hfe1
    peel h as i2, hi2
    have ex := vec_index_some hx
    have hv := ConRon.Refine.Nat.uadd_val hi2
    have h1 := ifenv_push_spec hfe x1 fe1 hfe1
    rw [i_constant_info_dup_abs hx1] at h1
    have := ih i2 fe1 (by simp at hv; omega) _ r h1 h
    have dx : cs.val.drop i.val = x :: cs.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; simp [List.getElem?_eq_some_iff.mp ex |>.2]
    simpa [absICILFrom, dx, show i2.val = i.val + 1 by simp at hv; omega] using this

open Lockstep in
/-- **`push_all` is `foldl IFEnv.push`.** -/
@[lockstep] theorem push_all_spec {pers : arena.store.PersTier} {fe : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers fe lf) (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    LSP (push_all pers fe cs) (fun r => IFEnvRelI pers r ((cs.val.map absIConstantInfo).foldl IFEnv.push lf)) := by
  intro r h
  have := push_all_loop_rel cs 0#usize fe lf r hfe h
  simpa [absICILFrom] using this

/-- The twin's empty layer. -/
abbrev emptyLayer : IFEnv := ⟨⟨[], []⟩, {}, {}, {}, false, false⟩

/-- **`ifenv_layer(0, 0, false, false)` is the twin's empty layer**, over a tier whose frozen
base is empty. -/
theorem ifenv_layer00_rel {pers : arena.store.PersTier} (hb : BaseRel pers.env {})
    (hok : BaseOK pers) {r : arena.env.IFEnv}
    (h : arena.env.ifenv_layer 0#u64 0#u64 false false = ok r) : IFEnvRelI pers r emptyLayer := by
  rw [arena.env.ifenv_layer] at h
  simp only [arena.env.i_env_empty, ron.hashmap2.HashMap2.new, bind_ok] at h
  obtain rfl := (Result.ok_injective h).symm
  have hn := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64) (m' := layer00.idx) rfl
  refine ⟨⟨⟨fun n => ?_, fun n => ?_, hb, rfl, rfl, hok, rfl, rfl⟩, ?_⟩,
    hn.1, fun n p hp => ?_, hn.1, fun n s hs => ?_⟩
  · show (ConRon.Refine.HashMap2.toFun layer00.idx n).bind _ = _
    simp [hn.2.2 n]
  · show (ConRon.Refine.HashMap2.toFun layer00.tbls n).bind _ = _
    rw [show layer00.tbls = layer00.idx from rfl]
    simp [hn.2.2 n]
  · simp [absIEnv]
  · have hp' : ConRon.Refine.HashMap2.toFun layer00.idx n = some p := hp
    rw [hn.2.2 n] at hp'; cases hp'
  · have hs' : ConRon.Refine.HashMap2.toFun layer00.idx n = some s := hs
    rw [hn.2.2 n] at hs'; cases hs'

open Lockstep in
/-- The twin's step of `ctxLayer`. -/
def ctxStep (fe : IFEnv) (d : IDeclaration) : AM IFEnv := do
  pure ((← declConstants d).foldl IFEnv.push fe)

open Lockstep in
/-- `ctx_layer`'s loop from the cursor on. -/
theorem ctx_layer_loop_ls {pers : arena.store.PersTier} (ctx : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (i : Std.Usize) (fe : arena.env.IFEnv) st lst (lf : IFEnv), IFEnvRelI pers fe lf →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (IFEnvRelI pers) (ctx_layer_loop pers st ctx fe i) lst
        (((ctx.val.drop i.val).map absIDeclaration).foldlM ctxStep lf) := by
  intro i fe
  refine cursor_induction (fun i : Std.Usize => i.val) ctx.val.length
    (fun i fe => ∀ st lst (lf : IFEnv), IFEnvRelI pers fe lf →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (IFEnvRelI pers) (ctx_layer_loop pers st ctx fe i) lst
        (((ctx.val.drop i.val).map absIDeclaration).foldlM ctxStep lf)) ?_ ?_ i fe
  · intro i fe hn st lst lf hfe hrel hinv
    rw [ctx_layer_loop.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len ctx by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, List.foldlM_nil]
    lockstep
  · intro i fe hi ih st lst lf hfe hrel hinv
    rw [ctx_layer_loop.eq_def, ite_eq_left (show i < alloc.vec.Vec.len ctx by scalar_tac),
      List.drop_eq_getElem_cons hi, List.map_cons, List.foldlM_cons, ctxStep]
    have ih' : ∀ (fe : arena.env.IFEnv) st lst (j : Std.Usize) (lf : IFEnv), j.val = i.val + 1 →
        IFEnvRelI pers fe lf → AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (IFEnvRelI pers) (ctx_layer_loop pers st ctx fe j) lst
          (((ctx.val.drop (i.val + 1)).map absIDeclaration).foldlM ctxStep lf) := by
      intro fe st lst j lf hj hfe hrel hinv
      have := ih j fe hj st lst lf hfe hrel hinv
      rwa [hj] at this
    lockstep

open Lockstep in
/-- **`ctx_layer` is `ctxLayer`**, over a tier whose frozen base is empty. -/
@[lockstep] theorem ctx_layer_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hb : BaseRel pers.env {}) (hok : BaseOK pers)
    (ctx : alloc.vec.Vec arena.env.IDeclaration) :
    LS pers (IFEnvRelI pers) (ctx_layer pers st ctx) lst (Modular.ctxLayer (absIDeclArr ctx)) := by
  rw [ctx_layer]
  intro o st' hm
  obtain ⟨fe, hfe, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h0 := ifenv_layer00_rel hb hok hfe
  have := ctx_layer_loop_ls ctx 0#usize fe st lst emptyLayer h0 hrel hinv o st' hm
  have e : Modular.ctxLayer (absIDeclArr ctx) =
      ((ctx.val.drop (0#usize : Std.Usize).val).map absIDeclaration).foldlM ctxStep emptyLayer := by
    rw [Modular.ctxLayer, absIDeclArr, List.foldlM_toArray, Lockstep.usize_zero_val', List.drop_zero]
    rfl
  rw [e]
  exact this

/-! ## `LA`: the accept of a check that names its reject

`copy_against`, `copy_check`, `own_hole_ok` and the loops over them reject with a message that
reads names out of the store; the twin's message reads them back (`readName`), which declines a
dangling handle at a different kind.  So these claim their accept only: the Rust's `Ok` is a run
of the twin in related states, and an `Err` claims nothing (`LS.la` from the lockstep shape). -/

section LA
variable {α β α₁ β₁ γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}

open Lockstep in
theorem LS.la {m} {lst : AState} {x : AM β} (h : LS pers R m lst x) : LA pers R m lst x :=
  fun _ _ hm => h _ _ hm

theorem LA.err {e : kernel.core_types.CheckError} {st : arena.monad.AState} {lst : AState}
    {x : AM β} : LA pers R (ok (.Err e, st)) lst x := by
  intro a st' h; cases Result.ok_injective h

theorem LA.accept {a : α} {b : β} {st : arena.monad.AState} {lst : AState} (hR : R a b)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LA pers R (ok (.Ok a, st)) lst (Pure.pure b) := by
  intro a' st' h
  simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨b, lst, rfl, hR, hrel, hinv⟩

/-- A Rust-only step. -/
theorem LA.rust {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : ∀ v, f = ok v → LA pers R (k v) lst x) :
    LA pers R (Std.bind f k) lst x := by
  intro a st' hm
  obtain ⟨v, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h v h1 a st' h2

open Lockstep in
/-- **The bind of a stateful Rust callee** against the twin's. -/
theorem LA.bind {R₁ : α₁ → β₁ → Prop}
    {f : Result (core.result.Result α₁ kernel.core_types.CheckError × arena.monad.AState)}
    {k : core.result.Result α₁ kernel.core_types.CheckError × arena.monad.AState →
      Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β₁} {g : β₁ → AM β}
    (hf : LA pers R₁ f lst x)
    (he : ∀ e st1 a st', k (.Err e, st1) = ok (.Ok a, st') → False)
    (hk : ∀ a b st1 lst1, R₁ a b → AStateRel₀ pers st1 lst1 → AStateInv pers st1 →
      LA pers R (k (.Ok a, st1)) lst1 (g b)) :
    LA pers R (Std.bind f k) lst (x >>= g) := by
  intro a st' hm
  obtain ⟨⟨r, st1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  cases r with
  | Err e => exact (he e st1 a st' h2).elim
  | Ok a1 =>
    obtain ⟨b, lst1, hx, hR, hr, hi⟩ := hf a1 st1 h1
    obtain ⟨c, lst2, hx2, hR2, hr2, hi2⟩ := hk a1 b st1 lst1 hR hr hi a st' h2
    exact ⟨c, lst2, by rw [run_bind_ok hx]; exact hx2, hR2, hr2, hi2⟩

open Lockstep in
/-- **The bind of a Rust read** against the twin's. -/
theorem LA.bindR {R₁ : α₁ → β₁ → Prop} {st : arena.monad.AState}
    {f : Result (core.result.Result α₁ kernel.core_types.CheckError)}
    {k : core.result.Result α₁ kernel.core_types.CheckError →
      Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β₁} {g : β₁ → AM β}
    (hf : LSR pers R₁ f st lst x)
    (he : ∀ e a st', k (.Err e) = ok (.Ok a, st') → False)
    (hk : ∀ a b lst1, R₁ a b → AStateRel₀ pers st lst1 → AStateInv pers st →
      LA pers R (k (.Ok a)) lst1 (g b)) :
    LA pers R (Std.bind f k) lst (x >>= g) := by
  intro a st' hm
  obtain ⟨r, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  cases r with
  | Err e => exact (he e a st' h2).elim
  | Ok a1 =>
    obtain ⟨b, lst1, hx, hR, hr, hi⟩ := hf _ h1
    obtain ⟨c, lst2, hx2, hR2, hr2, hi2⟩ := hk a1 b lst1 hR hr hi a st' h2
    exact ⟨c, lst2, by rw [run_bind_ok hx]; exact hx2, hR2, hr2, hi2⟩

end LA

/-- A Rust branch that ends in a reject. -/
macro "la_err" : tactic => `(tactic| (repeat (first | exact LA.err | refine LA.rust fun _ _ => ?_)))

/-! ## A copy against the loaded constant -/

/-- **`copy_against`'s accept is `copyAgainst`'s**, against a related layer.  `src` and `h` only
name the rejects, so the twin's are any. -/
theorem copy_against_la {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {fe : arena.env.IFEnv} {lfe : IFEnv} (hfe : IFEnvRelI pers fe lfe)
    (m src n : arena.handle.NIdx) (e : arena.env.IDeclaration) (h : arena.handle.NIdx)
    (d : arena.env.IDeclaration) (src' h' : NIdx) :
    LA pers (fun _ _ => True) (copy_against pers st fe m src n e h d) lst
      (Modular.copyAgainst lfe (absNIdx m) src' (absNIdx n) (absIDeclaration e) h'
        (absIDeclaration d)) := by
  rw [copy_against, Modular.copyAgainst]
  refine LA.bind (LS.la (find_constant_ls hrel hinv e n)) (fun _ _ _ _ h => by simp at h) ?_
  rintro c _ st1 lst1 rfl hrel1 hinv1
  refine LA.bind (LS.la (copy_stmt_ls hrel1 hinv1 d)) (fun _ _ _ _ h => by simp at h) ?_
  rintro c1 _ st2 lst2 rfl hrel2 hinv2
  refine LA.rust fun mt _ => ?_
  cases c1 with
  | some cv =>
    cases c with
    | none => la_err
    | some ci =>
      dsimp only [Option.map]
      refine LA.rust fun iv hiv => ?_
      rw [← i_constant_info_to_constant_val_abs hiv]
      refine LA.bind (LS.la (same_cv_up_to_levels_ls hrel2 hinv2 cv iv))
        (fun _ _ _ _ h => by simp at h) ?_
      rintro _ b st3 lst3 rfl hrel3 hinv3
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · la_err
      · exact LA.accept trivial hrel3 hinv3
  | none =>
    dsimp only [Option.map]
    cases d with
    | DefnDecl cv v hint =>
      cases c with
      | none => la_err
      | some ci =>
        dsimp only [Option.map, absIDeclaration]
        refine LA.rust fun iv hiv => ?_
        refine LA.rust fun e1 he1 => ?_
        refine LA.rust fun rh hrh => ?_
        cases Lockstep.PC2.i_constant_val_dup_id hiv
        cases eidx_dup2_ok he1
        cases reducibility_hint_dup_ls hint rh hrh
        refine LA.bind (LS.la (same_def_up_to_levels_ls hrel2 hinv2 _ ci))
          (fun _ _ _ _ h => by simp at h) ?_
        rintro _ b st3 lst3 rfl hrel3 hinv3
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · la_err
        · exact LA.accept trivial hrel3 hinv3
    | IndDecl block np =>
      dsimp only [absIDeclaration]
      refine LA.bind (LS.la (copy_ind_ok_ls hrel2 hinv2 hfe _ e))
        (fun _ _ _ _ h => by simp at h) ?_
      rintro _ b st3 lst3 rfl hrel3 hinv3
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · la_err
      · exact LA.accept trivial hrel3 hinv3
    | _ => cases c <;> la_err

/-- **`rec_key` is `recKey`.** -/
theorem rec_key_abs {d : arena.env.IDeclaration} {o : Option arena.handle.NIdx}
    (h : frontend.compare.rec_key d = ok o) :
    o.map absNIdx = ConRon.Arena.Frontend.recKey (absIDeclaration d) := by
  cases d with
  | IndDecl b np =>
    simp only [frontend.compare.rec_key] at h
    by_cases hb : alloc.vec.Vec.len b = 0#usize
    · rw [ite_eq_left hb] at h
      cases Result.ok_injective h
      have : b.val = [] := by
        have : b.val.length = 0 := by have := congrArg UScalar.val hb; simpa using this
        exact List.eq_nil_of_length_eq_zero this
      simp [absIDeclaration, ConRon.Arena.Frontend.recKey, this]
    · rw [ite_eq_right hb] at h
      peel h as x, hx
      peel h as n, hn
      cases Result.ok_injective h
      have ex := vec_index_some hx
      have hh : b.val.head? = some x := by
        rw [List.head?_eq_getElem?]; simpa using ex
      simp [absIDeclaration, ConRon.Arena.Frontend.recKey, List.head?_map, hh,
        i_constant_info_name_abs hn]
  | _ =>
    simp only [frontend.compare.rec_key] at h
    peel h as n, hn
    cases nidx_dup2_ok hn
    cases Result.ok_injective h
    rfl

/-- **`copy_check`'s accept is `copyCheck`'s**: the owner table a `IdxRel` of the twin's, the
context's records the twin's, the layer related.  The header's loads and the name index only
name a reject, so the twin's are any. -/
theorem copy_check_la {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {fe : arena.env.IFEnv} {lfe : IFEnv} (hfe : IFEnvRelI pers fe lfe)
    (pk : frontend.olean.spec.OleanPins) (m : arena.handle.NIdx)
    (ld : frontend.olean.levels.HeaderLoads) (ix : frontend.olean.index.NameIndex)
    (r : frontend.modular.reach.Reach) {r' : Modular.Reach} (hr : r'.ctx = absIDeclArr r.ctx)
    {owner : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64} {O : Std.HashMap NIdx Nat}
    (ho : IdxRel owner O) (d : arena.env.IDeclaration)
    (ld' : Arena.Frontend.Olean.HeaderLoads) (ix' : Arena.Frontend.Olean.NameIndex) :
    LA pers (fun _ _ => True) (copy_check pk pers st m ld ix r owner fe d) lst
      (Modular.copyCheck (absPins pk) (absNIdx m) ld' ix' r' O lfe (absIDeclaration d)) := by
  rw [copy_check, Modular.copyCheck]
  refine LA.rust fun o ho1 => ?_
  have eo := rec_key_abs ho1
  refine LA.rust fun pn hpn => ?_
  obtain ⟨pk1, n⟩ := pn
  have hn : pk1 = pk ∧ absNIdx n = (ConRon.Arena.Frontend.recKey (absIDeclaration d)).getD
      (absPins pk).anon := by
    rw [← eo]
    cases o with
    | none =>
      simp only at hpn
      peel hpn as n1, hn1
      cases nidx_dup2_ok hn1
      cases Result.ok_injective hpn
      exact ⟨rfl, rfl⟩
    | some k =>
      cases Result.ok_injective hpn
      exact ⟨rfl, rfl⟩
  obtain ⟨rfl, hn⟩ := hn
  refine LA.rust fun o1 _ => ?_
  refine LA.rust fun ps _ => ?_
  obtain ⟨pk2, src⟩ := ps
  simp only [← hn]
  refine LA.bindR (ConRon.Refine2.Lockstep.PA1.pin_quot_sound_ls hrel hinv)
    (fun _ _ _ h => by simp at h) ?_
  rintro q _ lst1 rfl hrel1 hinv1
  refine LA.bindR (ConRon.Refine2.pin_sorry_ax_ls hrel1 hinv1) (fun _ _ _ h => by simp at h) ?_
  rintro sa _ lst2 rfl hrel2 hinv2
  refine LA.rust fun b hb => ?_
  have eb := nidx_eq2_val hb
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine LA.rust fun b1 hb1 => ?_
    have eb1 := nidx_eq2_val hb1
    cases b1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [← eb, ← eb1, Bool.or_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine LA.bind (LS.la (basis_names_ok_ls hrel2 hinv2)) (fun _ _ _ _ h => by simp at h) ?_
      rintro _ b2 st3 lst3 rfl hrel3 hinv3
      cases b2
      · la_err
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine LA.rust fun o2 ho2 => ?_
        obtain ⟨eo2, fit⟩ := ho.get_eq ho2
        cases o2 with
        | none => la_err
        | some k =>
          simp only [absOpt, Option.map_some] at eo2
          simp only [← eo2]
          refine LA.rust fun k1 hk1 => ?_
          have hk1v : k1.val = k.val := ConRon.Refine2.Modular.cast_usize_val (fit k rfl) hk1
          by_cases hlt : k1 < alloc.vec.Vec.len r.ctx
          · simp only [hlt, ↓reduceIte]
            refine LA.rust fun hh _ => ?_
            refine LA.rust fun i2 hi2 => ?_
            have ei2 := vec_index_some hi2
            have : r'.ctx[k.val]? = some (absIDeclaration i2) := by
              rw [hr, absIDeclArr, ← hk1v]
              simp [List.getElem?_map, ei2]
            simp only [this]
            exact copy_against_la hrel3 hinv3 hfe m src n i2 hh d _ _
          · simp only [hlt, ↓reduceIte]
            la_err
    · simp only [↓reduceIte]
      la_err
  · simp only [↓reduceIte]
    la_err

/-! ## The holes -/

/-- **`own_hole_ok`'s accept is `ownHoleOk`'s.** -/
theorem own_hole_ok_la {U : Type} {inst : frontend.nat_op_ground.UsedConsts U} {u : U}
    {used : IDeclaration → AM (Array NIdx)} {pers : arena.store.PersTier}
    (hu : ConRon.Refine2.Frontend.UsedRel inst u used pers) {st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pk : frontend.olean.spec.OleanPins) (m : arena.handle.NIdx)
    (d : arena.env.IDeclaration) :
    LA pers (fun _ _ => True) (own_hole_ok inst pk u pers st m d) lst
      (Modular.ownHoleOk (absPins pk) used (absNIdx m) (absIDeclaration d)) := by
  rw [own_hole_ok, Modular.ownHoleOk]
  refine LA.bind (LS.la (is_hole_rec_ls hu hrel hinv d)) (fun _ _ _ _ h => by simp at h) ?_
  rintro _ b st1 lst1 rfl hrel1 hinv1
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact LA.accept trivial hrel1 hinv1
  · simp only [↓reduceIte]
    la_err

/-- `own_holes_ok`'s loop from the cursor on. -/
theorem own_holes_ok_loop_la {U : Type} {inst : frontend.nat_op_ground.UsedConsts U} {u : U}
    {used : IDeclaration → AM (Array NIdx)} {pers : arena.store.PersTier}
    (hu : ConRon.Refine2.Frontend.UsedRel inst u used pers) (pk : frontend.olean.spec.OleanPins)
    (m : arena.handle.NIdx) (own : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun _ _ => True) (own_holes_ok_loop inst pk u pers st m own i) lst
        (((own.val.drop i.val).map absIDeclaration).forM
          (Modular.ownHoleOk (absPins pk) used (absNIdx m))) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) own.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun _ _ => True) (own_holes_ok_loop inst pk u pers st m own i) lst
        (((own.val.drop i.val).map absIDeclaration).forM
          (Modular.ownHoleOk (absPins pk) used (absNIdx m)))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv
    rw [own_holes_ok_loop.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len own by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, List.forM]
    exact LA.accept trivial hrel hinv
  · intro i _ hi ih st lst hrel hinv
    rw [own_holes_ok_loop.eq_def, ite_eq_left (show i < alloc.vec.Vec.len own by scalar_tac),
      List.drop_eq_getElem_cons hi, List.map_cons, List.forM]
    refine LA.rust fun x hx => ?_
    have ex := vec_index_some hx
    have hxe : own.val[i.val] = x := (List.getElem?_eq_some_iff.mp ex).2
    rw [hxe]
    refine LA.bind (own_hole_ok_la hu hrel hinv pk m x) (fun _ _ _ _ h => by simp at h) ?_
    rintro _ _ st1 lst1 _ hrel1 hinv1
    refine LA.rust fun i2 hi2 => ?_
    have hv := ConRon.Refine.Nat.uadd_val hi2
    have := ih i2 () (by simp at hv; omega) st1 lst1 hrel1 hinv1
    rwa [show i2.val = i.val + 1 by simp at hv; omega] at this

/-- **`own_holes_ok`'s accept is `ownHolesOk`'s**, from the accept of the own records'
selection (`recs_loaded`, lane L3-H1's: `hrl`). -/
theorem own_holes_ok_la {U : Type} {inst : frontend.nat_op_ground.UsedConsts U} {u : U}
    {used : IDeclaration → AM (Array NIdx)} {pers : arena.store.PersTier}
    (hu : ConRon.Refine2.Frontend.UsedRel inst u used pers) {st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pk : frontend.olean.spec.OleanPins) (m : arena.handle.NIdx)
    (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) {x' : Array ConRon.Arena.Frontend.Olean.ImportRec}
    (hx : x'.size = x.val.length) (ix : frontend.olean.index.NameIndex)
    {ix' : Arena.Frontend.Olean.NameIndex} (ds : alloc.vec.Vec arena.env.IDeclaration)
    (hrl : ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun a b => b = absIDeclArr a) (recs_loaded pers st ix ds false) lst
        (Modular.recsLoaded ix' (absIDeclArr ds) false)) :
    LA pers (fun _ _ => True) (own_holes_ok inst pk u pers st m x ix ds) lst
      (Modular.ownHolesOk (absPins pk) used (absNIdx m) x' ix' (absIDeclArr ds)) := by
  rw [own_holes_ok, Modular.ownHolesOk]
  by_cases h0 : alloc.vec.Vec.len x = 0#usize
  · have : x'.isEmpty = true := by
      have : x.val.length = 0 := by have := congrArg UScalar.val h0; simpa using this
      have : x'.size = 0 := by omega
      simp [Array.isEmpty, this]
    simp only [h0, this, ↓reduceIte]
    exact LA.accept trivial hrel hinv
  · have : x'.isEmpty = false := by
      have : x.val.length ≠ 0 := fun e => h0 (by scalar_tac)
      have : x'.size ≠ 0 := by omega
      simp [Array.isEmpty, this]
    simp only [h0, this, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine LA.bind (hrl st lst hrel hinv) (fun _ _ _ _ h => by simp at h) ?_
    rintro o _ st1 lst1 rfl hrel1 hinv1
    have := own_holes_ok_loop_la hu pk m o 0#usize st1 lst1 hrel1 hinv1
    simpa [absIDeclArr] using this

/-! ## The copies -/

/-- `copies_ok`'s loops from the cursor on (the two are the same loop, on the two layers). -/
theorem copies_ok_loop0_la {pers : arena.store.PersTier} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hfe : IFEnvRelI pers fe lfe) (pk : frontend.olean.spec.OleanPins) (m : arena.handle.NIdx)
    (hl : frontend.olean.levels.HeaderLoads) (ni : frontend.olean.index.NameIndex)
    (v : alloc.vec.Vec arena.env.IDeclaration) (v1 : alloc.vec.Vec arena.handle.NIdx)
    (v2 : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)) (i0 i1 : Std.U64)
    (v3 : alloc.vec.Vec ((alloc.vec.Vec Std.U32) × arena.handle.NIdx × frontend.olean.spec.StmtRec))
    {r' : Modular.Reach} (hr : r'.ctx = absIDeclArr v)
    {owner : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64} {O : Std.HashMap NIdx Nat}
    (ho : IdxRel owner O) (ld' : Arena.Frontend.Olean.HeaderLoads)
    (ix' : Arena.Frontend.Olean.NameIndex) (cs : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun _ _ => True) (copies_ok_loop0 pk pers st m hl ni v v1 v2 i0 i1 v3 owner cs fe i) lst
        (((cs.val.drop i.val).map absIDeclaration).forM
          (Modular.copyCheck (absPins pk) (absNIdx m) ld' ix' r' O lfe)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun _ _ => True) (copies_ok_loop0 pk pers st m hl ni v v1 v2 i0 i1 v3 owner cs fe i) lst
        (((cs.val.drop i.val).map absIDeclaration).forM
          (Modular.copyCheck (absPins pk) (absNIdx m) ld' ix' r' O lfe))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv
    rw [copies_ok_loop0.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len cs by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, List.forM]
    exact LA.accept trivial hrel hinv
  · intro i _ hi ih st lst hrel hinv
    rw [copies_ok_loop0.eq_def, ite_eq_left (show i < alloc.vec.Vec.len cs by scalar_tac),
      List.drop_eq_getElem_cons hi, List.map_cons, List.forM]
    refine LA.rust fun x hx => ?_
    have ex := vec_index_some hx
    have hxe : cs.val[i.val] = x := (List.getElem?_eq_some_iff.mp ex).2
    rw [hxe]
    refine LA.bind (copy_check_la hrel hinv hfe pk m hl ni ⟨v, v1, v2, i0, i1, v3⟩ hr ho x ld' ix')
      (fun _ _ _ _ h => by simp at h) ?_
    rintro _ _ st1 lst1 _ hrel1 hinv1
    refine LA.rust fun i2 hi2 => ?_
    have hv := ConRon.Refine.Nat.uadd_val hi2
    have := ih i2 () (by simp at hv; omega) st1 lst1 hrel1 hinv1
    rwa [show i2.val = i.val + 1 by simp at hv; omega] at this

/-- `copies_ok`'s second loop (over the empty layer), the same. -/
theorem copies_ok_loop1_la {pers : arena.store.PersTier} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hfe : IFEnvRelI pers fe lfe) (pk : frontend.olean.spec.OleanPins) (m : arena.handle.NIdx)
    (hl : frontend.olean.levels.HeaderLoads) (ni : frontend.olean.index.NameIndex)
    (v : alloc.vec.Vec arena.env.IDeclaration) (v1 : alloc.vec.Vec arena.handle.NIdx)
    (v2 : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)) (i0 i1 : Std.U64)
    (v3 : alloc.vec.Vec ((alloc.vec.Vec Std.U32) × arena.handle.NIdx × frontend.olean.spec.StmtRec))
    {r' : Modular.Reach} (hr : r'.ctx = absIDeclArr v)
    {owner : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64} {O : Std.HashMap NIdx Nat}
    (ho : IdxRel owner O) (ld' : Arena.Frontend.Olean.HeaderLoads)
    (ix' : Arena.Frontend.Olean.NameIndex) (cs : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun _ _ => True) (copies_ok_loop1 pk pers st m hl ni v v1 v2 i0 i1 v3 owner cs fe i) lst
        (((cs.val.drop i.val).map absIDeclaration).forM
          (Modular.copyCheck (absPins pk) (absNIdx m) ld' ix' r' O lfe)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun _ _ => True) (copies_ok_loop1 pk pers st m hl ni v v1 v2 i0 i1 v3 owner cs fe i) lst
        (((cs.val.drop i.val).map absIDeclaration).forM
          (Modular.copyCheck (absPins pk) (absNIdx m) ld' ix' r' O lfe))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv
    rw [copies_ok_loop1.eq_def, ite_eq_right (show ¬ i < alloc.vec.Vec.len cs by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, List.forM]
    exact LA.accept trivial hrel hinv
  · intro i _ hi ih st lst hrel hinv
    rw [copies_ok_loop1.eq_def, ite_eq_left (show i < alloc.vec.Vec.len cs by scalar_tac),
      List.drop_eq_getElem_cons hi, List.map_cons, List.forM]
    refine LA.rust fun x hx => ?_
    have ex := vec_index_some hx
    have hxe : cs.val[i.val] = x := (List.getElem?_eq_some_iff.mp ex).2
    rw [hxe]
    refine LA.bind (copy_check_la hrel hinv hfe pk m hl ni ⟨v, v1, v2, i0, i1, v3⟩ hr ho x ld' ix')
      (fun _ _ _ _ h => by simp at h) ?_
    rintro _ _ st1 lst1 _ hrel1 hinv1
    refine LA.rust fun i2 hi2 => ?_
    have hv := ConRon.Refine.Nat.uadd_val hi2
    have := ih i2 () (by simp at hv; omega) st1 lst1 hrel1 hinv1
    rwa [show i2.val = i.val + 1 by simp at hv; omega] at this


/-- **`copies_ok`'s accept is `copiesOk`'s**, over a tier whose frozen base is empty, from the
accepts of the context's owner table (`owner_map`, lane L2's, no Theorem 2 yet: `hom`, an `IdxRel`) and of
the copies' selection (`copy_recs`, lane L3-H1's: `hcr`).  The worker's reads only name a
reject, so the twin's are any. -/
theorem copies_ok_la {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hb : BaseRel pers.env {}) (hok : BaseOK pers)
    (pk : frontend.olean.spec.OleanPins) (m : arena.handle.NIdx)
    (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (x' : Array ConRon.Arena.Frontend.Olean.ImportRec)
    (wr : frontend.olean.index.WorkerReads) (wr' : Arena.Frontend.Olean.WorkerReads)
    (r : frontend.modular.reach.Reach) {r' : Modular.Reach} (hr : r'.ctx = absIDeclArr r.ctx)
    (ds : alloc.vec.Vec arena.env.IDeclaration)
    (hom : ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers IdxRel (frontend.modular.reach.owner_map pers st r.ctx) lst
        (Modular.ownerMap r'.ctx.toList))
    (hcr : ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LA pers (fun a b => b = absIDeclArr a) (copy_recs pers st x wr.index ds) lst
        (Modular.copyRecs x' wr'.index (absIDeclArr ds))) :
    LA pers (fun _ _ => True) (copies_ok pk pers st m x wr r ds) lst
      (Modular.copiesOk (absPins pk) (absNIdx m) x' wr' r' (absIDeclArr ds)) := by
  rw [copies_ok, Modular.copiesOk]
  refine LA.bind (hom st lst hrel hinv) (fun _ _ _ _ h => by simp at h) ?_
  rintro o O st1 lst1 hO hrel1 hinv1
  refine LA.bind (hcr st1 lst1 hrel1 hinv1) (fun _ _ _ _ h => by simp at h) ?_
  rintro c _ st2 lst2 rfl hrel2 hinv2
  refine LA.rust fun b hb' => ?_
  have eb : Modular.anyInd (absIDeclArr c) = b := any_ind_spec c b hb'
  cases b
  · simp only [eb, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine LA.rust fun fe hfe0 => ?_
    have hfe := ifenv_layer00_rel hb hok hfe0
    have := copies_ok_loop1_la hfe pk m wr.loads wr.index r.ctx r.homes r.completed r.searches
      r.inferred r.pending hr hO wr'.loads wr'.index c 0#usize st2 lst2 hrel2 hinv2
    simpa [absIDeclArr] using this
  · simp only [eb, ↓reduceIte]
    rw [hr]
    refine LA.bind (LS.la (ctx_layer_ls hrel2 hinv2 hb hok r.ctx)) (fun _ _ _ _ h => by simp at h) ?_
    rintro fe lfe st3 lst3 hfe hrel3 hinv3
    have := copies_ok_loop0_la hfe pk m wr.loads wr.index r.ctx r.homes r.completed r.searches
      r.inferred r.pending hr hO wr'.loads wr'.index c 0#usize st3 lst3 hrel3 hinv3
    simpa [absIDeclArr] using this

end ConRon.Refine2.Modular
