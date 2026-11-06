/-
# `ConRon.Refine2.Frontend.Olean.FastRoots` — the skeletons and the roots of `olean/fast.rs`

**Task #142, Theorem 2.**  What reads no value: `consts_skel` and `many_skels` take no store,
against the twin's that leave it alone (`PS`); `push_all`, `c_entry_names`, `c_entry_exprs`,
`many_roots`, `stmts_roots` collect pointers, against upstream's lists.
-/
import ConRon.Refine2.Frontend.Olean.FastBuild
import ConRon.Refine2.Frontend.Olean.SpecEntry

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.fast (push_all push_all_loop c_entry_names c_entry_names_loop c_entry_exprs
  c_entry_exprs_loop many_roots many_roots_loop0 many_roots_loop0_loop0 many_roots_loop1
  many_roots_loop1_loop0 stmts_roots stmts_roots_loop consts_skel consts_skel_loop many_skels
  many_skels_loop)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (constsSkel manySkels skelFits)
open ConLeche.Frontend.Olean (CKindF CEntryF ModSkel constSkel moduleSkel)
open ConRon.Refine.HashMap (uscalar_add_eq)

/-! ## A loop that appends -/

/-- **A loop that appends `f x` to an accumulator, for each `x` of `src`.** -/
theorem append_loop {σ ξ β : Type} {src : List ξ} {Ab : σ → List β} {f : ξ → List β}
    {loop : σ → Std.Usize → Result σ}
    (hstep : ∀ s i o, loop s i = ok o → (src.length ≤ i.val ∧ o = s) ∨
      ∃ x s1 i1, src[i.val]? = some x ∧ Ab s1 = Ab s ++ f x ∧ i1.val = i.val + 1 ∧ loop s1 i1 = ok o) :
    ∀ (k : Nat) {s : σ} {i : Std.Usize} {o : σ}, src.length - i.val ≤ k → loop s i = ok o →
      Ab o = Ab s ++ (src.drop i.val).flatMap f := by
  intro k
  induction k with
  | zero =>
    intro s i o hk h
    rcases hstep s i o h with ⟨-, rfl⟩ | ⟨x, s1, i1, hx, -, -, -⟩
    · rw [List.drop_eq_nil_of_le (by omega)]; simp
    · have := (List.getElem?_eq_some_iff.mp hx).1
      omega
  | succ k ih =>
    intro s i o hk h
    rcases hstep s i o h with ⟨hle, rfl⟩ | ⟨x, s1, i1, hx, hab, hi1, h1⟩
    · rw [List.drop_eq_nil_of_le hle]; simp
    · obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hx
      rw [ih (by omega) h1, hab, List.drop_eq_getElem_cons hlt, hi1, he]
      simp

/-- The whole of a loop from index `0`. -/
theorem append_loop0 {σ ξ β : Type} {src : List ξ} {Ab : σ → List β} {f : ξ → List β}
    {loop : σ → Std.Usize → Result σ}
    (hstep : ∀ s i o, loop s i = ok o → (src.length ≤ i.val ∧ o = s) ∨
      ∃ x s1 i1, src[i.val]? = some x ∧ Ab s1 = Ab s ++ f x ∧ i1.val = i.val + 1 ∧ loop s1 i1 = ok o)
    {s : σ} {o : σ} (h : loop s 0#usize = ok o) : Ab o = Ab s ++ src.flatMap f := by
  simpa using append_loop hstep _ (Nat.le_refl _) h

/-- A loop that appends one a turn. -/
theorem flatMap_single {α β : Type} (f : α → β) (l : List α) : l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-! ## The pointers of a skeleton -/

/-- The names a skeleton holds, as the Rust collects them. -/
def namesL (c : frontend.olean.spec.CEntryF Std.U64 Std.U64) : List Std.U64 :=
  c.name :: c.level_params.val ++
  match c.kind with
  | .Thm _ all => all.val
  | .Induct _ _ all cs _ _ _ _ => all.val ++ cs.val
  | .Ctor ind _ _ _ _ => [ind]
  | .Recur all _ _ _ _ rules _ _ => all.val ++ rules.val.map (·.1)
  | _ => []

/-- The expressions a skeleton holds, as the Rust collects them. -/
def exprsL (c : frontend.olean.spec.CEntryF Std.U64 Std.U64) : List Std.U64 :=
  c.ty ::
  match c.kind with
  | .Defn v _ _ => [v]
  | .Thm v _ => [v]
  | .Opaq v _ => [v]
  | .Recur _ _ _ _ _ rules _ _ => rules.val.map (·.2.2)
  | _ => []

/-- **`push_all` is `++`.** -/
theorem push_all_val {xs out o : alloc.vec.Vec Std.U64} (h : push_all xs out = ok o) :
    o.val = out.val ++ xs.val := by
  rw [push_all] at h
  have := append_loop0 (src := xs.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val)
    (f := fun x => [x]) (loop := push_all_loop xs) ?_ h
  · simpa using this
  · intro s i o h
    rw [push_all_loop] at h
    by_cases hi : i < alloc.vec.Vec.len xs
    · right
      rw [ite_eq_left hi] at h
      peel h as x, hx
      peel h as s1, hs1
      peel h as i1, hi1
      exact ⟨x, s1, i1, ConRon.Refine.ExprOps.vec_index_getElem? hx, ConRon.Refine.vec_push_val hs1,
        uscalar_add_eq hi1, h⟩
    · left
      rw [ite_eq_right hi] at h
      exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩

/-- `c_entry_names` of a recursor: its rules' names. -/
theorem c_entry_names_loop_val {rules : alloc.vec.Vec (Std.U64 × Std.U64 × Std.U64)} {out o}
    (h : c_entry_names_loop out rules 0#usize = ok o) :
    o.val = out.val ++ rules.val.map (·.1) := by
  have := append_loop0 (src := rules.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val)
    (f := fun x => [x.1]) (loop := fun s i => c_entry_names_loop s rules i) ?_ h
  · rw [this, flatMap_single]
  · intro s i o h
    rw [c_entry_names_loop] at h
    by_cases hi : i < alloc.vec.Vec.len rules
    · right
      rw [ite_eq_left hi] at h
      peel h as x, hx
      obtain ⟨a, b, c⟩ := x
      peel h as s1, hs1
      peel h as i1, hi1
      exact ⟨(a, b, c), s1, i1, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.vec_push_val hs1, uscalar_add_eq hi1, h⟩
    · left
      rw [ite_eq_right hi] at h
      exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩

/-- `c_entry_exprs` of a recursor: its rules' right-hand sides. -/
theorem c_entry_exprs_loop_val {rules : alloc.vec.Vec (Std.U64 × Std.U64 × Std.U64)} {out o}
    (h : c_entry_exprs_loop out rules 0#usize = ok o) :
    o.val = out.val ++ rules.val.map (·.2.2) := by
  have := append_loop0 (src := rules.val) (Ab := fun s : alloc.vec.Vec Std.U64 => s.val)
    (f := fun x => [x.2.2]) (loop := fun s i => c_entry_exprs_loop s rules i) ?_ h
  · rw [this, flatMap_single]
  · intro s i o h
    rw [c_entry_exprs_loop] at h
    by_cases hi : i < alloc.vec.Vec.len rules
    · right
      rw [ite_eq_left hi] at h
      peel h as x, hx
      obtain ⟨a, b, c⟩ := x
      peel h as s1, hs1
      peel h as i1, hi1
      exact ⟨(a, b, c), s1, i1, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.vec_push_val hs1, uscalar_add_eq hi1, h⟩
    · left
      rw [ite_eq_right hi] at h
      exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩

/-- **`c_entry_names` collects `namesL`.** -/
theorem c_entry_names_val {c out o} (h : c_entry_names c out = ok o) : o.val = out.val ++ namesL c := by
  rw [c_entry_names] at h
  peel h as s1, hs1
  peel h as s2, hs2
  have e1 := ConRon.Refine.vec_push_val hs1
  have e2 := push_all_val hs2
  rw [e1] at e2
  obtain ⟨n, lp, ty, k⟩ := c
  simp only [namesL] at e2 ⊢
  cases k with
  | Ax _ => cases Result.ok_injective h; simpa using e2
  | Defn _ _ _ => cases Result.ok_injective h; simpa using e2
  | Thm _ _ => rw [push_all_val h, e2]; simp
  | Opaq _ _ => cases Result.ok_injective h; simpa using e2
  | Quot _ => cases Result.ok_injective h; simpa using e2
  | Induct _ _ _ _ _ _ _ _ =>
    peel h as s3, hs3
    rw [push_all_val h, push_all_val hs3, e2]; simp
  | Ctor _ _ _ _ _ => rw [ConRon.Refine.vec_push_val h, e2]; simp
  | Recur _ _ _ _ _ _ _ _ =>
    peel h as s3, hs3
    rw [c_entry_names_loop_val h, push_all_val hs3, e2]; simp

/-- **`c_entry_exprs` collects `exprsL`.** -/
theorem c_entry_exprs_val {c out o} (h : c_entry_exprs c out = ok o) : o.val = out.val ++ exprsL c := by
  rw [c_entry_exprs] at h
  peel h as s1, hs1
  have e1 := ConRon.Refine.vec_push_val hs1
  obtain ⟨n, lp, ty, k⟩ := c
  simp only [exprsL] at e1 ⊢
  cases k with
  | Ax _ => cases Result.ok_injective h; simpa using e1
  | Defn _ _ _ => rw [ConRon.Refine.vec_push_val h, e1]; simp
  | Thm _ _ => rw [ConRon.Refine.vec_push_val h, e1]; simp
  | Opaq _ _ => rw [ConRon.Refine.vec_push_val h, e1]; simp
  | Quot _ => cases Result.ok_injective h; simpa using e1
  | Induct _ _ _ _ _ _ _ _ => cases Result.ok_injective h; simpa using e1
  | Ctor _ _ _ _ _ => cases Result.ok_injective h; simpa using e1
  | Recur _ _ _ _ _ _ _ _ => rw [c_entry_exprs_loop_val h, e1]; simp

/-- The rules' names, as upstream's. -/
theorem rules_names {E E' : Type} {AE : E → E'} {RN : NatRel} {l : List (Std.U64 × Std.U64 × E)}
    {l' : List (UInt64 × Nat × E')} (h : List.Forall₂ (RuleRel absWord AE RN) l l') :
    (l.map (·.1)).map absWord = l'.map (·.1) := by
  induction h with
  | nil => rfl
  | cons h0 _ ih => simp only [List.map_cons, ih, h0.1]

/-- The rules' right-hand sides, as upstream's. -/
theorem rules_exprs {N N' : Type} {AN : N → N'} {RN : NatRel} {l : List (N × Std.U64 × Std.U64)}
    {l' : List (N' × Nat × UInt64)} (h : List.Forall₂ (RuleRel AN absWord RN) l l') :
    (l.map (·.2.2)).map absWord = l'.map (·.2.2) := by
  induction h with
  | nil => rfl
  | cons h0 _ ih => simp only [List.map_cons, ih, h0.2.2]

/-- **`namesL` is `CEntryF.names`.** -/
theorem namesL_abs {RN : NatRel} {c : frontend.olean.spec.CEntryF Std.U64 Std.U64}
    {c' : CEntryF UInt64 UInt64} (h : EntryRel absWord absWord RN c c') :
    (namesL c).map absWord = c'.names := by
  obtain ⟨n, lp, ty, k⟩ := c
  obtain ⟨n', lp', ty', k'⟩ := c'
  obtain ⟨h1, h2, -, hk⟩ := h
  simp only [namesL, ConLeche.Frontend.Olean.CEntryF.names, List.cons_append, List.map_cons,
    List.map_append] at h1 h2 ⊢
  rw [h1, show List.map absWord lp.val = lp' from h2]
  congr 2
  cases k <;> cases k' <;> try exact hk.elim
  all_goals first
    | rfl
    | (obtain ⟨-, h⟩ := hk; simpa using h)
    | (obtain ⟨-, -, h3, h4, -⟩ := hk; simp only [List.map_append]; exact congrArg₂ (· ++ ·) h3 h4)
    | (obtain ⟨h3, -⟩ := hk; simpa using h3)
    | (obtain ⟨h3, -, -, -, -, h4, -⟩ := hk; simp only [List.map_append]; exact congrArg₂ (· ++ ·) h3 (rules_names h4))

/-- **`exprsL` is `CEntryF.exprs`.** -/
theorem exprsL_abs {RN : NatRel} {c : frontend.olean.spec.CEntryF Std.U64 Std.U64}
    {c' : CEntryF UInt64 UInt64} (h : EntryRel absWord absWord RN c c') :
    (exprsL c).map absWord = c'.exprs := by
  obtain ⟨n, lp, ty, k⟩ := c
  obtain ⟨n', lp', ty', k'⟩ := c'
  obtain ⟨-, -, h3, hk⟩ := h
  simp only [exprsL, ConLeche.Frontend.Olean.CEntryF.exprs, List.map_cons] at h3 ⊢
  rw [h3]
  congr 1
  cases k <;> cases k' <;> try exact hk.elim
  all_goals first
    | rfl
    | (obtain ⟨-, -, -, -, -, h4, -⟩ := hk; exact rules_exprs h4)
    | (obtain ⟨h, -⟩ := hk; simp [h])

end ConRon.Refine2.Frontend.Olean
