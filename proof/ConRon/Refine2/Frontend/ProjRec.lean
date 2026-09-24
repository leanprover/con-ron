/-
# `ConRon.Refine2.Frontend.ProjRec` — `frontend/proj_rec.rs`

**Task #97-P5-Frontend.**  The projection-function rewrite: a structure-like
owner's projection function, exported as a `.proj` node, rebuilt as a
recursor application so that the fold's own install route serves it.
Fifty-six `pub fn`s against `Arena/Frontend/ProjRec.lean`'s twenty-four
declarations — 2.3×, the campaign's lowest ratio, for the reason task
#97-P4e part 2 gives (straight-line term building, no interpolated message).

## What the statements look like

The module splits three ways, and the split is the RETURN TYPE, exactly as
task #97-P5-0's did for `expr_ops`:

| slice | shape |
|---|---|
| pure (no `pers`/`st`) | an equation |
| `pers, &AState` — reads, never interns | `SimRE`, or `OOut` for the memoised walk |
| `pers, &mut AState` — interns | `Sim₀` |

**The memoised walk is the one shape this file adds.**  `occurs_const_go`
threads its `seen` table as an argument-and-result pair INSIDE the `Result`
(where `nat_op_ground::used_consts_go` returns it outside), so `OOut` is task
#97-P5-0's finding 4 at a third memo — and the twin's is a `Std.HashSet`, so
`Refine2/Frontend/NatOpGround.lean`'s `HSetRel` is what relates it.

## Three deviations, each stated rather than assumed

1. **`build_binders` takes a KIND, not a function** (`ProjRec.lean`'s own
   deviation 1).  con-leche passes `mk : Expr → Option Expr`; the twin passes
   a `ProjBinderKind` tag and a `ProjBuild` record, and the port takes the
   twin's.  So there is no `RenameRel`-style higher-order seam here at all —
   task #97-P5-0's finding 6 does NOT recur, because the twin already
   defunctionalised it.
2. **`find_ctor_rec` / `find_rec_rec` return an INDEX**, where the twin
   returns the record (the port would copy a `Vec<NIdx>` and an `EIdx` the
   caller reads in place).  The statement is *"the index the port answers
   names the record the twin found"*.
3. **`proj_rec_candidates` drops the twin's unused `fuel`.**  The twin takes
   a `fuel` its body never reads; an unused parameter is a warning under
   `-D warnings`, so the port has none and the statement quantifies over the
   twin's at any value.  (Task #97-P4e part 2 asks for the argument to come
   off the LEAN side too; until it does, this is where the difference lives.)

## `sorry` count in this file: 0

Round 3 (task #97-T2-LOCKSTEP lane Frontend): every statement proved on the
shared `lockstep` tactic; the walks `expr_ops` owns are the ExprOps lane's
`@[lockstep]` `_ls` lemmas (`Refine2/ExprOps/{Read,Mut}.lean`; the round's
interim `ExprOpsSeam.lean` statements were deleted at the `arena` merge).
-/
import ConRon.Refine2.Frontend.Spec
import ConRon.Refine2.ExprOps.Mut
import ConRon.Refine2.Inductives.NativeParts
import ConRon.Refine2.Inductives.StructParts

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend

/-! ## The binder kind, the build record, and the memoised walk's outcome -/

def absProjBinderKind : frontend.proj_rec.ProjBinderKind → ProjBinderKind
  | .Motive => .motive
  | .Minor => .minor

def absProjBuild (p : frontend.proj_rec.ProjBuild) : ProjBuild :=
  ⟨absNIdx p.t, absNIdx p.ctor, absEIdx p.r, absU p.i, absEIdx p.punit_c,
    absEIdx p.punit_unit_c⟩

attribute [simp] absProjBinderKind absProjBuild

/-- The outcome of `occurs_const_go`: the answer and the visited set, both
inside the `Result`, against the twin's `AM (Bool × Std.HashSet EIdx)`.  The
walk READS the store — an occurrence test interns nothing — so there is no
post-state. -/
def OOut (lst : AState)
    (o : core.result.Result (Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      kernel.core_types.CheckError)
    (x : AM (Bool × Std.HashSet EIdx)) : Prop :=
  match o with
  | .Ok r => ∃ s', x.run lst = .ok ((r.1, s'), lst) ∧ HSetRel r.2 s'
  | .Err e => AErrSim e (x.run lst)

/-! ## The pure slice (nine functions) -/

/-- **`proj_rec_owner_dup` is the identity**, the house `foo_dup` (§3.4). -/
theorem proj_rec_owner_dup_refines {o o'}
    (h : frontend.proj_rec.proj_rec_owner_dup o = ok o') :
    absProjRecOwner o' = absProjRecOwner o := by
  rw [frontend.proj_rec.proj_rec_owner_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hn, dupId_nidx _ _ hn1, dupId_nidx _ _ hn2, dupId_eidx _ _ he]
  simp only [absProjRecOwner, nidx_vec_dup_val hv, nidx_vec_dup_val hv1]

/-! ### `text::cps_beq` (moved here from `ExportC.lean`, round 3: `is_proj_iota_name` reads it) -/

theorem slice_index_some {α : Type} {s : Slice α} {i : Std.Usize} {x : α}
    (h : Slice.index_usize s i = ok x) : s.val[i.val]? = some x := by
  rw [Slice.index_usize] at h
  have hb : s[i]? = s.val[i.val]? := rfl
  rcases hi : s.val[i.val]? with _ | y
  · rw [hb, hi] at h; simp at h
  · rw [hb, hi] at h
    exact congrArg some (Result.ok_injective h)

theorem cps_beq_loop_val (N : Nat) :
    ∀ (s : alloc.vec.Vec Std.U32) (lit : Slice Std.U32) (n i : Std.Usize) (b : Bool),
      s.val.length - i.val = N → n.val = s.val.length → s.val.length = lit.val.length →
      frontend.text.cps_beq_loop s lit n i = ok b →
      (b = true ↔ s.val.drop i.val = lit.val.drop i.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s lit n i b hN hn hlen h
    rw [frontend.text.cps_beq_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < s.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hcv : s.val[i.val]'(by omega) = c := by
        have hg := vec_index_some hc
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hc2v : lit.val[i.val]'(by omega) = c2 := by
        have hg := slice_index_some hc2
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hds : s.val.drop i.val = c :: s.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (show i.val < s.val.length by omega), hcv]
      have hdl : lit.val.drop i.val = c2 :: lit.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (show i.val < lit.val.length by omega), hc2v]
      rw [hds, hdl]
      split at h
      · rename_i hne
        simp only [Result.ok.injEq] at h
        have hval : ¬ (c.val = c2.val) := by simpa using hne
        have hcc : c ≠ c2 := fun hq => hval (congrArg Std.UScalar.val hq)
        simp [← h, hcc]
      · rename_i hne
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi2
        have hceq : c = c2 := Std.UScalar.val_eq_imp_iff.mpr (by simpa using hne)
        rw [ih (s.val.length - i2.val) (by omega) s lit n i2 b rfl hn hlen h, hi2v]
        simp [hceq]
    · rename_i hge
      have hle : s.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      simp

/-- `text::cps_beq` is list equality of the code points. -/
theorem cps_beq_val {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
    (h : frontend.text.cps_beq s lit = ok b) : (b = true ↔ s.val = lit.val) := by
  rw [frontend.text.cps_beq] at h
  split at h
  · rename_i hne
    have hl : s.val.length ≠ lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    simp only [Result.ok.injEq] at h
    refine ⟨fun hb => absurd (h ▸ hb) (by simp), fun he => ?_⟩
    exact absurd (congrArg List.length he) hl
  · rename_i hne
    have hl : s.val.length = lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    have hh := cps_beq_loop_val _ s lit _ 0#usize b rfl (by simp [alloc.vec.Vec.len]) hl h
    simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- A scanned spelling equals a literal exactly when `cps_beq` says so. -/
theorem cps_beq_str {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
    (hs : ConRon.Refine.StrWF s) (hL : ∀ c ∈ lit.val, Nat.isValidChar c.val)
    (h : frontend.text.cps_beq s lit = ok b) :
    (b = true ↔ ConRon.Refine.absString s = String.ofList (lit.val.map fun c => Char.ofNat c.val)) := by
  rw [cps_beq_val h]
  constructor
  · intro he; simp only [ConRon.Refine.absString, he]
  · intro he
    have hlen : lit.val.length ≤ Std.Usize.max := by scalar_tac
    have ht : ConRon.Refine.StrWF (alloc.vec.Vec.from lit.val hlen) := by
      intro c hc; exact hL c (by simpa using hc)
    have := ConRon.Refine.Name.absString_inj hs ht
      (by rw [he]; simp [ConRon.Refine.absString, alloc.vec.Vec.from_val])
    rw [this, alloc.vec.Vec.from_val]

/-- **`cps_starts_with`** — `String.startsWith` on code points. -/
theorem cps_starts_with_loop_val (N : Nat) :
    ∀ (s : alloc.vec.Vec Std.U32) (lit : Slice Std.U32) (n i : Std.Usize) (b : Bool),
      lit.val.length - i.val = N → n.val = lit.val.length → lit.val.length ≤ s.val.length →
      frontend.proj_rec.cps_starts_with_loop s lit n i = ok b →
      (b = true ↔ (lit.val.drop i.val).map (fun c => c.val) <+:
        (s.val.drop i.val).map (fun c => c.val)) := by
  induction N with
  | zero =>
    intro s lit n i b hN hn hle h
    rw [frontend.proj_rec.cps_starts_with_loop, if_neg (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (show lit.val.length ≤ i.val by omega)]
    simp
  | succ k ih =>
    intro s lit n i b hN hn hle h
    have hil : i.val < lit.val.length := by omega
    have his : i.val < s.val.length := by omega
    rw [frontend.proj_rec.cps_starts_with_loop, if_pos (by scalar_tac)] at h
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hcv : s.val[i.val] = c := by
      have hg := vec_index_some hc
      rw [List.getElem?_eq_getElem his] at hg
      exact Option.some_injective _ hg
    have hc2v : lit.val[i.val] = c2 := by
      have hg := slice_index_some hc2
      rw [List.getElem?_eq_getElem hil] at hg
      exact Option.some_injective _ hg
    rw [List.drop_eq_getElem_cons his, List.drop_eq_getElem_cons hil, hcv, hc2v,
      List.map_cons, List.map_cons, List.cons_prefix_cons]
    split at h
    · rename_i hne
      cases Result.ok_injective h
      have hval : ¬ (c.val = c2.val) := by simpa using hne
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro he; exact absurd he.symm hval
    · rename_i hne
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi2
      have hceq : c.val = c2.val := by simpa using hne
      rw [ih s lit n i2 b (by omega) hn hle h, hi2v]
      simp [hceq]

theorem cps_starts_with_refines {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32}
    {v : Bool} (h : frontend.proj_rec.cps_starts_with s lit = ok v) :
    v = (lit.val.map (fun c => c.val)).isPrefixOf (s.val.map (fun c => c.val)) := by
  rw [frontend.proj_rec.cps_starts_with] at h
  split at h
  · rename_i hlt
    cases Result.ok_injective h
    have hl : s.val.length < lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hlt
    symm
    rw [Bool.eq_false_iff]
    intro hp
    rw [List.isPrefixOf_iff_prefix] at hp
    have := hp.length_le
    simp at this; omega
  · rename_i hge
    have hl : lit.val.length ≤ s.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hge
    have hh := cps_starts_with_loop_val _ s lit _ 0#usize v rfl (by simp [Slice.len]) hl h
    have e0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
    rw [e0, List.drop_zero, List.drop_zero] at hh
    rw [Bool.eq_iff_iff, hh, List.isPrefixOf_iff_prefix]

/-- `Char.ofNat` is injective on valid code points: a prefix test survives it. -/
theorem prefix_map_ofNat : ∀ {A B : List Nat}, (∀ x ∈ A, Nat.isValidChar x) →
    (∀ x ∈ B, Nat.isValidChar x) →
    (A.map Char.ofNat <+: B.map Char.ofNat ↔ A <+: B)
  | [], _, _, _ => by simp
  | a :: A, [], _, _ => by simp
  | a :: A, b :: B, hA, hB => by
    have ha := hA a List.mem_cons_self
    have hb := hB b List.mem_cons_self
    have hinj : Char.ofNat a = Char.ofNat b ↔ a = b := by
      constructor
      · intro he
        have h1 := congrArg Char.toNat he
        simpa [Char.ofNat, Char.ofNatAux, Char.toNat, ha, hb] using h1
      · intro he; rw [he]
    simp only [List.map_cons, List.cons_prefix_cons, hinj]
    rw [prefix_map_ofNat (fun x hx => hA x (List.mem_cons_of_mem a hx))
      (fun x hx => hB x (List.mem_cons_of_mem b hx))]

/-- `String.startsWith` at a literal of valid code points, on a well-formed
`absString`, is the port's code-point prefix test. -/
theorem absString_startsWith {s : alloc.vec.Vec Std.U32} (hs : ConRon.Refine.StrWF s)
    (L : List Std.U32) (hL : ∀ c ∈ L, Nat.isValidChar c.val) :
    (ConRon.Refine.absString s).startsWith (absCodesF L) =
      (L.map (fun c => c.val)).isPrefixOf (s.val.map (fun c => c.val)) := by
  rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]
  simp only [ConRon.Refine.absString, absCodesF, String.toList_ofList]
  have e1 : L.map (fun c => Char.ofNat c.val) = (L.map (fun c => c.val)).map Char.ofNat := by
    simp [List.map_map, Function.comp_def]
  have e2 : s.val.map (fun c => Char.ofNat c.val) =
      (s.val.map (fun c => c.val)).map Char.ofNat := by
    simp [List.map_map, Function.comp_def]
  rw [e1, e2]
  exact prefix_map_ofNat (by simpa using hL) (by simpa [ConRon.Refine.StrWF] using hs)

/-- **`one_lidx`** — the singleton level list. -/
theorem one_lidx_refines {l v} (h : frontend.proj_rec.one_lidx l = ok v) :
    v.val.map absLIdx = [absLIdx l] := by
  rw [frontend.proj_rec.one_lidx] at h
  obtain ⟨l1, hl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [dupId_lidx _ _ hl1] at h
  rw [ConRon.Refine.vec_push_val h]
  simp [alloc.vec.Vec.with_capacity]

/-- **`cons_lidx`** — the twin's `l :: us`. -/
theorem cons_lidx_loop_val (us : alloc.vec.Vec arena.handle.LIdx) :
    ∀ (k : Nat) (out : alloc.vec.Vec arena.handle.LIdx) (i : Std.Usize) r,
      us.val.length - i.val = k →
      frontend.proj_rec.cons_lidx_loop us out (alloc.vec.Vec.len us) i = ok r →
      r.val = out.val ++ us.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro out i r hk h
    rw [frontend.proj_rec.cons_lidx_loop, if_neg (by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    intro out i r hk h
    have hlt : i.val < us.val.length := by omega
    rw [frontend.proj_rec.cons_lidx_loop, if_pos (by scalar_tac),
      vec_index_ok_eq us i hlt, bind_tc_ok] at h
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_lidx _ _ hd] at h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi1v : i1.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi1).trans (by simp)
    rw [ih o1 i1 r (by omega) h, ConRon.Refine.vec_push_val ho1, hi1v,
      List.drop_eq_getElem_cons hlt]
    simp

theorem cons_lidx_refines {l us v} (h : frontend.proj_rec.cons_lidx l us = ok v) :
    v.val.map absLIdx = absLIdx l :: us.val.map absLIdx := by
  rw [frontend.proj_rec.cons_lidx] at h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l1, hl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [dupId_lidx _ _ hl1] at h
  obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [cons_lidx_loop_val us _ o1 0#usize v rfl h, ConRon.Refine.vec_push_val ho1]
  simp [alloc.vec.Vec.with_capacity]

/-- **`append_eidx`** — the twin's `out ++ xs`. -/
theorem append_eidx_loop_val (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (k : Nat) (out : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) r,
      xs.val.length - i.val = k →
      frontend.proj_rec.append_eidx_loop xs out (alloc.vec.Vec.len xs) i = ok r →
      r.val = out.val ++ xs.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro out i r hk h
    rw [frontend.proj_rec.append_eidx_loop, if_neg (by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    intro out i r hk h
    have hlt : i.val < xs.val.length := by omega
    rw [frontend.proj_rec.append_eidx_loop, if_pos (by scalar_tac),
      vec_index_ok_eq xs i hlt, bind_tc_ok] at h
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ hd] at h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi1v : i1.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi1).trans (by simp)
    rw [ih o1 i1 r (by omega) h, ConRon.Refine.vec_push_val ho1, hi1v,
      List.drop_eq_getElem_cons hlt]
    simp

theorem append_eidx_refines {out xs v}
    (h : frontend.proj_rec.append_eidx out xs = ok v) :
    absEIdxL v = absEIdxL out ++ absEIdxL xs := by
  rw [frontend.proj_rec.append_eidx] at h
  simp [absEIdxL, append_eidx_loop_val xs _ out 0#usize v rfl h]

/-- **`type_names`** — the block's type-former names, `types.map (·.1)`. -/
theorem type_names_refines {types v}
    (h : frontend.proj_rec.type_names types = ok v) :
    absNIdxL v = (absProjTypeRecL types).map (·.1) := by
  rw [frontend.proj_rec.type_names] at h
  have key : ∀ (k : Nat) (out : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize) r,
      types.val.length - i.val = k →
      frontend.proj_rec.type_names_loop types (alloc.vec.Vec.len types) out i = ok r →
      r.val = out.val ++ (types.val.drop i.val).map (·.1) := by
    intro k
    induction k with
    | zero =>
      intro out i r hk h
      rw [frontend.proj_rec.type_names_loop, if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by omega)]; simp
    | succ k ih =>
      intro out i r hk h
      have hi : i.val < types.val.length := by omega
      rw [frontend.proj_rec.type_names_loop, if_pos (by scalar_tac),
        vec_index_ok_eq types i hi, bind_tc_ok] at h
      obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [dupId_nidx _ _ hn2] at h
      obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi1).trans (by simp)
      rw [ih o1 i1 r (by omega) h, ConRon.Refine.vec_push_val ho1, hi1v,
        List.drop_eq_getElem_cons hi]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]
      rfl
  have := key _ _ 0#usize v rfl h
  simp [absNIdxL, absProjTypeRecL, this, alloc.vec.Vec.with_capacity, absProjTypeRec,
    Function.comp_def]

/-- **`any_is_rec`** — `types.any (·.2.2.2.2.2.2)`. -/
theorem any_is_rec_refines {types v}
    (h : frontend.proj_rec.any_is_rec types = ok v) :
    v = (absProjTypeRecL types).any (·.2.2.2.2.2.2) := by
  rw [frontend.proj_rec.any_is_rec] at h
  have key : ∀ (k : Nat) (i : Std.Usize) b, types.val.length - i.val = k →
      frontend.proj_rec.any_is_rec_loop types (alloc.vec.Vec.len types) i = ok b →
      b = ((types.val.drop i.val).map absProjTypeRec).any (·.2.2.2.2.2.2) := by
    intro k
    induction k with
    | zero =>
      intro i b hk h
      rw [frontend.proj_rec.any_is_rec_loop, if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by omega)]; rfl
    | succ k ih =>
      intro i b hk h
      have hi : i.val < types.val.length := by omega
      rw [frontend.proj_rec.any_is_rec_loop, if_pos (by scalar_tac),
        vec_index_ok_eq types i hi, bind_tc_ok] at h
      rw [List.drop_eq_getElem_cons hi, List.map_cons, List.any_cons]
      rcases hx : types.val[i.val] with ⟨a1, a2, a3, a4, a5, a6, b0⟩
      rw [hx] at h
      change (if b0 = true then ok true else _) = ok b at h
      split at h
      · rename_i hb
        cases Result.ok_injective h
        simp [absProjTypeRec, hb]
      · rename_i hb
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi1).trans (by simp)
        rw [ih i1 b (by omega) h, hi1v]
        simp [absProjTypeRec, hb]
  simpa [absProjTypeRecL] using key _ 0#usize v rfl h

/-- **`declared_num_params`** — the first type record's parameter count, `0`
at an empty block: the twin's `(types.head?.map (·.2.2.2.1)).getD 0`. -/
theorem declared_num_params_refines {types v}
    (h : frontend.proj_rec.declared_num_params types = ok v) :
    absU v = (((absProjTypeRecL types).head?).map (·.2.2.2.1)).getD 0 := by
  rw [frontend.proj_rec.declared_num_params] at h
  split at h
  · rename_i h0
    cases Result.ok_injective h
    have : types.val = [] := by
      have := congrArg UScalar.val h0; simpa using this
    simp [absProjTypeRecL, this]
  · rename_i h0
    have hp : 0 < types.val.length := by
      have : (alloc.vec.Vec.len types).val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq e)
      simpa using Nat.pos_of_ne_zero this
    rw [vec_index_ok_eq types 0#usize hp, bind_tc_ok] at h
    cases Result.ok_injective h
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hp)
    simp [absProjTypeRecL, hx, absProjTypeRec]

/-- **`occurs_record`** — the visited set's insert. -/
theorem occurs_record_refines {rm ls h' m'} (hs : HSetRel rm ls)
    (h : frontend.proj_rec.occurs_record rm h' = ok m') :
    HSetRel m' (ls.insert (absEIdx h')) := by
  rw [frontend.proj_rec.occurs_record] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [dupId_eidx _ _ he] at h
  obtain ⟨⟨old, m1⟩, hins, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  obtain ⟨hinv', -, htf, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen eidx_eq2 hs.2
    ConRon.Refine.HashMap2.KeysOk_true trivial hins
  refine ⟨fun k => ?_, hinv'⟩
  rw [htf, Std.HashSet.contains_insert]
  by_cases hk : k = h'
  · subst hk; simp
  · have hne : (absEIdx h' == absEIdx k) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun e => hk (absEIdx_inj e).symm
    rw [Function.update_of_ne hk, hs.1 k, hne, Bool.false_or]

/-- **`occurs_seen`** — the visited set's probe. -/
theorem occurs_seen_refines {rm ls h' v} (hs : HSetRel rm ls)
    (h : frontend.proj_rec.occurs_seen rm h' = ok v) :
    v = ls.contains (absEIdx h') := by
  rw [frontend.proj_rec.occurs_seen] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [eidx_get hs.2 hr] at h
  rw [← hs.1 h']
  cases hto : ConRon.Refine.HashMap2.toFun rm h' <;> rw [hto] at h <;> simp only [Result.ok.injEq] at h <;>
    simp [← h]

/-! ## The artifact name and its pre-filter -/

/-- A code-point literal, copied out of its `const` array. -/
theorem lit_cps {k : Std.Usize} {M : Std.Array Std.U32 k} {sl : Slice Std.U32}
    (hs : lift (Std.Array.to_slice M) = ok sl) {v : alloc.vec.Vec Std.U32}
    (hv : kernel.core_types.code_points sl = ok v) : v.val = M.val := by
  simp only [lift, Result.ok.injEq] at hs
  subst hs
  rw [ConRon.Refine.Env.code_points_val hv, Std.Array.val_to_slice]

/-- **`proj_iota_name` refines `projIotaName`** (`ProjRec.lean:77-81`): the
rewrite's artifact name `T._model.proj_i.iota`, three interns in the same
order.  Round 3's F11: false only while `AStateRel` carried `storeWF` (`t`
need not resolve; neither side checks); lockstep, it is the three interns and
the two literals' and the index rendering's spelling (`Text.lean`). -/
theorem proj_iota_name_refines {pers rst lst t i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_iota_name pers rst t i = ok o) :
    Sim₀ absNIdx pers lst o (projIotaName (absNIdx t) (absU i)) := by
  rw [frontend.proj_rec.proj_iota_name] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnt : n = t := dupId_nidx _ _ hn
  rw [hnt] at h
  clear hn hnt
  obtain ⟨sl, hsl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hvv := lit_cps hsl hv
  obtain ⟨⟨r, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hS1 := intern_n_node_run₀ hrel hinv (.Str t v)
    (by show ConRon.Refine.StrWF v; intro c hc; rw [hvv] at hc
        simp only [frontend.proj_rec.M_MODEL, Std.Array.make] at hc
        revert c; decide) h1
  have ha1 : absNNodeView (.Str t v) = .str (absNIdx t) "_model" := by
    simp only [absNNodeView, ConRon.Refine.absString, hvv, frontend.proj_rec.M_MODEL,
      Std.Array.make]
    rfl
  rw [ha1] at hS1
  unfold Sim₀
  rw [projIotaName, am_run_bind']
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact AErrSim.bind (Sim₀.apply_err hS1) _
  | Ok a =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
    rw [hx1, except_ok_bind]
    obtain ⟨sl1, hsl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hv1v := lit_cps hsl1 hv1
    obtain ⟨v2, hv2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hv2s, hv2w⟩ := u64_str_refines hv2
    obtain ⟨s2, hs2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hs2v := cat_val hs2
    obtain ⟨⟨r1, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hv1w : ConRon.Refine.StrWF v1 := by
      intro c hc; rw [hv1v] at hc
      simp only [frontend.proj_rec.M_PROJ, Std.Array.make] at hc
      revert c; decide
    have hS2 := intern_n_node_run₀ hrel1 hinv1 (.Str a s2)
      (by show ConRon.Refine.StrWF s2; exact cat_wf hv1w hv2w hs2) h2
    have ha2 : absNNodeView (.Str a s2) = .str (absNIdx a) s!"proj_{absU i}" := by
      simp only [absNNodeView, absString_eq_codesF, hs2v, absCodesF_append, hv2s, hv1v,
        frontend.proj_rec.M_PROJ, Std.Array.make]
      rfl
    rw [ha2] at hS2
    rw [am_run_bind']
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact AErrSim.bind (Sim₀.apply_err hS2) _
    | Ok b =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
      rw [hx2, except_ok_bind]
      obtain ⟨sl3, hsl3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v3, hv3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hv3v := lit_cps hsl3 hv3
      have hS3 := intern_n_node_run₀ hrel2 hinv2 (.Str b v3)
        (by show ConRon.Refine.StrWF v3; intro c hc; rw [hv3v] at hc
            simp only [frontend.proj_rec.M_IOTA, Std.Array.make] at hc
            revert c; decide) h
      have ha3 : absNNodeView (.Str b v3) = .str (absNIdx b) "iota" := by
        simp only [absNNodeView, ConRon.Refine.absString, hv3v, frontend.proj_rec.M_IOTA,
          Std.Array.make]
        rfl
      rw [ha3] at hS3
      exact hS3

/-! ### `is_proj_iota_name` (round 3)

The port reads the three spellings with `text::cps_beq` / `cps_starts_with`
against its code-point literals, the twin matches string literals; on a
well-formed name string (`NNodeViewWF`, from the store) the two agree. -/

theorem slice_lit_val {n : Std.Usize} {M : Std.Array Std.U32 n} {sl : Slice Std.U32}
    (hs : lift (Std.Array.to_slice M) = ok sl) : sl.val = M.val := by
  simp only [lift, Result.ok.injEq] at hs
  subst hs
  rw [Std.Array.val_to_slice]

theorem iota_spelling {sl : Slice Std.U32}
    (hsl : lift (Std.Array.to_slice frontend.proj_rec.M_IOTA) = ok sl)
    {s : alloc.vec.Vec Std.U32} {b : Bool} (hwf : ConRon.Refine.StrWF s)
    (hb : frontend.text.cps_beq s sl = ok b) :
    (b = true ↔ ConRon.Refine.absString s = "iota") := by
  have hv := slice_lit_val hsl
  simp only [frontend.proj_rec.M_IOTA, Std.Array.make] at hv
  rw [cps_beq_str hwf (by rw [hv]; decide) hb, hv]
  rfl

theorem model_spelling {sl : Slice Std.U32}
    (hsl : lift (Std.Array.to_slice frontend.proj_rec.M_MODEL) = ok sl)
    {s : alloc.vec.Vec Std.U32} {b : Bool} (hwf : ConRon.Refine.StrWF s)
    (hb : frontend.text.cps_beq s sl = ok b) :
    (b = true ↔ ConRon.Refine.absString s = "_model") := by
  have hv := slice_lit_val hsl
  simp only [frontend.proj_rec.M_MODEL, Std.Array.make] at hv
  rw [cps_beq_str hwf (by rw [hv]; decide) hb, hv]
  rfl

theorem proj_prefix_spelling {sl : Slice Std.U32}
    (hsl : lift (Std.Array.to_slice frontend.proj_rec.M_PROJ) = ok sl)
    {s : alloc.vec.Vec Std.U32} {b : Bool} (hwf : ConRon.Refine.StrWF s)
    (hb : frontend.proj_rec.cps_starts_with s sl = ok b) :
    b = (ConRon.Refine.absString s).startsWith "proj_" := by
  have hv := slice_lit_val hsl
  simp only [frontend.proj_rec.M_PROJ, Std.Array.make] at hv
  have hv' : sl.val = [112#u32, 114#u32, 111#u32, 106#u32, 95#u32] := by rw [hv]; rfl
  rw [cps_starts_with_refines hb, hv']
  have := absString_startsWith hwf [112#u32, 114#u32, 111#u32, 106#u32, 95#u32] (by decide)
  rw [← this]
  rfl

/-- The twin's `viewN` at a handle the port viewed. -/
theorem viewN_step {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {h : arena.handle.NIdx} {o} (hv : arena.monad.view_n pers st h = ok o) :
    match o with
    | .Ok v => (viewN (absNIdx h)).run lst = .ok (absNNodeView v, lst) ∧ NNodeViewWF v
    | .Err e => AErrSim e ((viewN (absNIdx h)).run lst) := by
  have hL := Lockstep.view_n_ls hrel hinv h o hv
  have hrun : (viewN (absNIdx h)).run lst = (match lst.store.ns.view (absNIdx h) with
      | some v => Except.ok (v, lst)
      | none => Except.error (Arena.CheckError.internal "arena: dangling name handle")) := by
    show ((match lst.store.ns.view (absNIdx h) with
      | some v => (pure v : AM NNodeView)
      | none => Arena.fail (.internal "arena: dangling name handle")).run lst) = _
    cases lst.store.ns.view (absNIdx h) <;> rfl
  cases o with
  | Err e => exact hL
  | Ok v =>
    obtain ⟨b, lst', hx, ⟨hb, hwf⟩, -, -⟩ := hL
    refine ⟨?_, hwf⟩
    rw [hx, hb]
    rw [hrun] at hx
    split at hx
    · cases hx; rfl
    · cases hx

/-- **`is_proj_iota_name` refines `isProjIotaName`** (`ProjRec.lean:85-97`),
the port's `is_proj_iota_pre` (its split of the two inner `viewN`s) inline. -/
theorem is_proj_iota_name_refines {pers rst lst n o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.is_proj_iota_name pers rst n = ok o) :
    SimRE id lst o (isProjIotaName (absNIdx n)) := by
  have htagstr : ∀ {m : arena.handle.NIdx} {t : Std.U32}, arena.handle.NIdx.tag m = ok t →
      (((absNIdx m).tag == NTag.str) = true ↔ t = arena.handle.NTAG_STR) := by
    intro m t ht
    rw [nidx_tag_abs ht, ← ntag_str_abs]
    constructor
    · intro he; exact absU32_inj (by simpa using he)
    · intro he; rw [he]; simp
  unfold SimRE
  rw [frontend.proj_rec.is_proj_iota_name] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  unfold isProjIotaName
  by_cases hts : t = arena.handle.NTAG_STR
  swap
  · rw [if_neg hts] at h
    cases Result.ok_injective h
    rw [if_neg (by rw [htagstr ht]; exact hts)]
    rfl
  rw [if_pos hts] at h
  rw [if_pos ((htagstr ht).mpr hts)]
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hv := viewN_step hrel hinv hr
  rw [am_run_bind']
  cases r with
  | Err e => cases Result.ok_injective h; exact AErrSim.bind hv _
  | Ok nv =>
  obtain ⟨hrun, hwf⟩ := hv
  rw [hrun, except_ok_bind]
  cases nv with
  | Anonymous => cases Result.ok_injective h; rfl
  | Num p k => cases Result.ok_injective h; rfl
  | Str p1 last =>
  simp only [absNNodeView]
  obtain ⟨sl, hsl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hbi := iota_spelling hsl hwf hb
  by_cases hbt : b = true
  swap
  · rw [if_neg hbt] at h
    cases Result.ok_injective h
    have hne : ConRon.Refine.absString last ≠ "iota" := fun e => hbt (hbi.mpr e)
    dsimp only
    split
    · rename_i heq; simp at heq; exact absurd heq.2 hne
    · rfl
  rw [if_pos hbt] at h
  rw [hbi.mp hbt]
  simp only []
  -- `is_proj_iota_pre`
  rw [frontend.proj_rec.is_proj_iota_pre] at h
  obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  by_cases hts1 : t1 = arena.handle.NTAG_STR
  swap
  · rw [if_neg hts1] at h
    cases Result.ok_injective h
    rw [if_neg (by rw [htagstr ht1]; exact hts1)]
    rfl
  rw [if_pos hts1] at h
  rw [if_pos ((htagstr ht1).mpr hts1)]
  obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hv1 := viewN_step hrel hinv hr1
  rw [am_run_bind']
  cases r1 with
  | Err e => cases Result.ok_injective h; exact AErrSim.bind hv1 _
  | Ok nv1 =>
  obtain ⟨hrun1, hwf1⟩ := hv1
  rw [hrun1, except_ok_bind]
  cases nv1 with
  | Anonymous => cases Result.ok_injective h; rfl
  | Num p k => cases Result.ok_injective h; rfl
  | Str p2 s2 =>
  simp only [absNNodeView]
  obtain ⟨t2, ht2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  by_cases hts2 : t2 = arena.handle.NTAG_STR
  swap
  · rw [if_neg hts2] at h
    cases Result.ok_injective h
    rw [if_neg (by rw [htagstr ht2]; exact hts2)]
    rfl
  rw [if_pos hts2] at h
  rw [if_pos ((htagstr ht2).mpr hts2)]
  obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hv2 := viewN_step hrel hinv hr2
  rw [am_run_bind']
  cases r2 with
  | Err e => cases Result.ok_injective h; exact AErrSim.bind hv2 _
  | Ok nv2 =>
  obtain ⟨hrun2, hwf2⟩ := hv2
  rw [hrun2, except_ok_bind]
  cases nv2 with
  | Anonymous => cases Result.ok_injective h; rfl
  | Num p k => cases Result.ok_injective h; rfl
  | Str p3 m =>
  simp only [absNNodeView]
  obtain ⟨sl2, hsl2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hbm := model_spelling hsl2 hwf2 hb2
  by_cases hbt2 : b2 = true
  swap
  · rw [if_neg hbt2] at h
    cases Result.ok_injective h
    have hne : ConRon.Refine.absString m ≠ "_model" := fun e => hbt2 (hbm.mpr e)
    dsimp only
    split
    · rename_i heq; simp at heq; exact absurd heq.2 hne
    · rfl
  rw [if_pos hbt2] at h
  rw [hbm.mp hbt2]
  obtain ⟨sl3, hsl3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b3, hb3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [proj_prefix_spelling hsl3 hwf1 hb3]
  rfl

open ConRon.Refine2.Lockstep in
@[lockstep] theorem intern_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : kernel.name.Name) (hwf : ConRon.Refine.NameWF n) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_name pers st n) lst
      (Arena.internName (ConRon.Refine.absName n)) :=
  LS.ofSim₀ fun _ h => intern_name_run₀ hrel hinv hwf h

open ConRon.Refine2.Lockstep in
/-- `intern_name` at a basis name the port built (`kernel::basis_names`),
against the twin's `internName` at the con-leche constant: the Rust-only step
that built it answers the conjunction this premise takes. -/
@[lockstep] theorem intern_basis_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : kernel.name.Name) (N : ConLeche.Name)
    (hn : ConRon.Refine.absName n = N ∧ ConRon.Refine.NameWF n) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_name pers st n) lst
      (Arena.internName N) := by
  rw [← hn.1]; exact intern_name_ls hrel hinv n hn.2

open ConRon.Refine2.Lockstep in
@[lockstep] theorem punit_name_spec :
    LSP kernel.basis_names.punit_name
      (fun n => ConRon.Refine.absName n = ConLeche.punitName ∧ ConRon.Refine.NameWF n) :=
  fun _ h => ConRon.Refine.BasisNames.punit_name_refines h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem punit_unit_name_spec :
    LSP kernel.basis_names.punit_unit_name
      (fun n => ConRon.Refine.absName n = ConLeche.punitUnitName ∧ ConRon.Refine.NameWF n) :=
  fun _ h => ConRon.Refine.BasisNames.punit_unit_name_refines h

open ConRon.Refine2.Lockstep in
/-- `arena::monad::view_const` against `Arena.viewConst`. -/
@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a) (arena.monad.view_const pers st h) st lst
      (Arena.viewConst (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewConst (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by
      have := view_const_run₀ hrel hr
      have h2 : (Except.ok (lst.store.viewConst (absEIdx h), lst) :
          Except Arena.CheckError _) = _ := this
      simp only [Except.ok.injEq, Prod.mk.injEq] at h2
      exact h2.1)
    hrel hinv

open ConRon.Refine2.Lockstep in
@[lockstep] theorem eq_name_spec :
    LSP kernel.basis_names.eq_name
      (fun n => ConRon.Refine.absName n = ConLeche.eqName ∧ ConRon.Refine.NameWF n) :=
  fun _ h => ConRon.Refine.BasisNames.eq_name_refines h

/-- The twin's `match l with | [x] => … | _ => …` at a list that is not a
singleton. -/
theorem match_single_ne' {α γ : Type} (l : List α) (hl : l.length ≠ 1) (f : α → γ)
    (g : γ) : (match l with | [x] => f x | _ => g) = g := by
  match l, hl with
  | [], _ => rfl
  | [_], hl => simp at hl
  | _ :: _ :: _, _ => rfl

open ConRon.Refine2.Lockstep in
/-- **`proj_iota_level_at`** — the port's split at the resolved view of the
artifact's type, against the twin's `match ← viewLs us with` arm. -/
@[lockstep] theorem proj_iota_level_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (us : arena.handle.LsIdx) :
    LS pers (fun a b => b = Option.map absLIdx a)
      (frontend.proj_rec.proj_iota_level_at pers st n us) lst
      (do
        match ← viewLs (absLsIdx us) with
        | [l] => do
          let eqH ← internName ConLeche.eqName
          pure (if absNIdx n == eqH then some l else none)
        | _ => pure none) := by
  rw [frontend.proj_rec.proj_iota_level_at]
  refine LSR.bind (view_lsv_ls hrel hinv us) rfl (fun _ => by lockstep_errarm)
    (fun a b lst1 hR hrel1 hinv1 => ?_)
  subst hR
  by_cases hl : a.val.length = 1
  · obtain ⟨l, hp⟩ := List.length_eq_one_iff.mp hl
    have habs : absLsNodeView a = [absLIdx l] := by simp [absLsNodeView, hp]
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) a 0#usize
        = ok l := by
      rw [vec_index_ok_eq a 0#usize (by simp [hp])]
      simp [hp]
    rw [habs]
    dsimp only
    rw [if_neg (by scalar_tac)]
    lockstep
  · dsimp only
    rw [if_pos (by scalar_tac)]
    split
    · rename_i x heq
      exact absurd (by simpa [absLsNodeView] using congrArg List.length heq) hl
    · lockstep

open ConRon.Refine2.Lockstep in
@[lockstep] theorem proj_iota_level_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (ty : arena.handle.EIdx) :
    LS pers (fun a b => b = Option.map absLIdx a)
      (frontend.proj_rec.proj_iota_level pers st fuel ty) lst
      (projIotaLevel (absU fuel) (absEIdx ty)) := by
  rw [frontend.proj_rec.proj_iota_level, projIotaLevel]
  lockstep
  all_goals first
    | (rw [if_pos (by rw [‹Idx.tag _ = absU32 arena.handle.ETAG_CONST›, etag_const_abs]; rfl)]
       apply LS.twin_view_const (by rw [‹Idx.tag _ = absU32 arena.handle.ETAG_CONST›, etag_const_abs])
       refine LSV.bind (view_const_ls ‹_› ‹_› _) rfl (fun p b lst2 hR hrel2 hinv2 => ?_)
       subst hR
       cases p with
       | none => lockstep
       | some p =>
         obtain ⟨n, us⟩ := p
         exact proj_iota_level_at_ls hrel2 hinv2 n us)
    | (rename_i hP hc
       rw [if_neg (by
         rw [hP, ← etag_const_abs]
         simpa using fun h => hc (absU32_inj h))]
       lockstep)

/-- **`proj_iota_level` refines `projIotaLevel`** (`ProjRec.lean:100-112`):
the field sort the artifact records. -/
theorem proj_iota_level_refines {pers rst lst fuel ty o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_iota_level pers rst fuel ty = ok o) :
    Sim₀ (Option.map absLIdx) pers lst o
      (projIotaLevel (absU fuel) (absEIdx ty)) :=
  Lockstep.LS.toSim₀ (proj_iota_level_ls hrel hinv fuel ty) h

/-! ## The occurrence test -/

open ConRon.Refine2.Lockstep in
@[lockstep] theorem occurs_seen_spec {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashSet EIdx} (hs : HSetRel rm ls) (h' : arena.handle.EIdx) :
    LSP (frontend.proj_rec.occurs_seen rm h') (fun v => v = ls.contains (absEIdx h')) :=
  fun _ h => occurs_seen_refines hs h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem occurs_record_spec {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashSet EIdx} (hs : HSetRel rm ls) (h' : arena.handle.EIdx) :
    LSP (frontend.proj_rec.occurs_record rm h') (fun m' => HSetRel m' (ls.insert (absEIdx h'))) :=
  fun _ h => occurs_record_refines hs h

attribute [local lockstep_inline] frontend.proj_rec.occurs_const_node
  frontend.proj_rec.occurs_const_two

/-- The port's `if b` on a `Bool` the twin matches on (`match (b, seen) with
| (false, seen) => …`), in its negative arm: `b` is `false`, substituted. -/
local macro "ls_bool_false" : tactic => `(tactic| (
  rename_i hcx; revert hcx; simp only [Bool.not_eq_true]; intro hcx; subst hcx; dsimp only))

open ConRon.Refine2.Lockstep in
/-- **`occurs_const_go` refines `occursConstGo`** (`ProjRec.lean:141-186`):
does the constant `n` occur in the DAG under `h`, each node visited once.  The
port's two splits (`occurs_const_node`, `occurs_const_two`) are unfolded in
place. -/
theorem occurs_const_go_aux (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (n : arena.handle.NIdx) (seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      (ls : Std.HashSet EIdx) (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = N → HSetRel seen ls → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => a.1 = b.1 ∧ HSetRel a.2 b.2)
        (frontend.proj_rec.occurs_const_go pers st n seen fuel h) st lst
        (occursConstGo (absNIdx n) ls N (absEIdx h)) := by
  induction N with
  | zero =>
    intro pers st lst n seen ls fuel h hn hs hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.occurs_const_go, occursConstGo, if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst n seen ls fuel h hn hs hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.occurs_const_go, occursConstGo, if_neg (by scalar_tac)]
    -- the twin's `match (b, seen) with | (false, seen) => …` at the port's
    -- `if b` (the negative arm): the Bool is `false`, the match reduces.  The
    -- step is taken before the zip's next one (since the tactic's round-2
    -- twin-`if` rules, a zip step at that undecided `match` does not stop).
    repeat (first | ls_bool_false | lockstep_step)

/-! ## The telescope helpers -/

/-- Under a binder tag the whole `view` is the binder projection: the twin's
`view` reads `viewBind` there (`EStore.view`'s first arm). -/
theorem view_of_bind_tag {st : EStore} {i : EIdx} (hb : ETag.isBind i.tag = true) :
    st.view i = (st.viewBind i).map fun p => eBindView i.tag p.1 p.2.1 p.2.2 := by
  simp only [EStore.view, hb, if_true]
  cases st.viewBind i with
  | none => rfl
  | some p => obtain ⟨ty, b, m⟩ := p; rfl

/-- **`lam_body` refines `lamBody`** (`ProjRec.lean:200-205`).  Round 3's D1:
the port reads the tag before the store and answers `h` itself off the `lam`
tag; the twin does too since task #97-T2-LOCKSTEP lane Frontend. -/
theorem lam_body_refines {pers rst lst fuel h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.lam_body pers rst fuel h' = ok o) :
    SimRE absEIdx lst o (lamBody (absU fuel) (absEIdx h')) := by
  suffices H : ∀ (n : Nat) (fuel : Std.U64) (h' : arena.handle.EIdx) {o}, fuel.val = n →
      frontend.proj_rec.lam_body pers rst fuel h' = ok o →
      SimRE absEIdx lst o (lamBody (absU fuel) (absEIdx h')) from H _ fuel h' rfl h
  intro n
  induction n with
  | zero =>
    intro fuel h' o hn h
    rw [frontend.proj_rec.lam_body] at h
    rw [if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl))] at h
    obtain ⟨sl, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases fail_run h
    rw [show absU fuel = 0 from hn]
    exact AErrSim.internal rfl
  | succ k ih =>
    intro fuel h' o hn h
    rw [frontend.proj_rec.lam_body] at h
    rw [if_neg (by intro hc; rw [hc] at hn; simp at hn)] at h
    obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have htag := eidx_tag_abs ht
    rw [show absU fuel = k + 1 from hn, lamBody]
    by_cases hc : t = arena.handle.ETAG_LAM
    · subst hc
      rw [if_pos rfl] at h
      have hlam : (absEIdx h').tag = ETag.lam := by rw [htag, etag_lam_abs]
      have hbind : ETag.isBind (absEIdx h').tag = true := by rw [hlam]; decide
      obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hvbr : (Arena.viewBind (absEIdx h')).run lst = Except.ok (q.map absBindM, lst) :=
        view_bind_run₀ hrel hbind hq
      rw [if_pos (by rw [hlam]; rfl)]
      unfold SimRE
      rw [am_run_bind', hvbr]
      cases q with
      | none =>
        rw [arena.monad.fail_dangling_e] at h
        obtain ⟨sl, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases fail_run h
        exact AErrSim.internal rfl
      | some p =>
        obtain ⟨ty, b, m⟩ := p
        simp only at h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = k := by
          have := (ConRon.Refine.Nat.usub_val hi1).2
          rw [this, hn]; rfl
        have := ih i1 b hi1v h
        simp only [Option.map_some, absBindM, except_ok_bind]
        rw [show absU i1 = k from hi1v] at this
        exact this
    · rw [if_neg hc] at h
      obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      have hne : ((absEIdx h').tag == ETag.lam) = false := by
        rw [htag, ← etag_lam_abs]
        simpa using fun he' => hc (absU32_inj he')
      rw [if_neg (by rw [hne]; simp)]
      show Except.ok _ = _
      rw [dupId_eidx _ _ he]

/-! ### Condition correspondences this file adds (`lockstep_simp`, an extension point) -/

@[lockstep_simp] theorem absU32_beq_const' (t : Std.U32) :
    (absU32 t == ETag.const) = decide (t = arena.handle.ETAG_CONST) := by
  rw [← etag_const_abs]
  by_cases h : t = arena.handle.ETAG_CONST
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_CONST := fun hc => h (absU32_inj hc)
    simp [h, this]

attribute [lockstep_simp] etag_const_abs etag_sort_abs

/-! ### `strip_pis_all`, lockstep (round 3) -/

/-- `absBinderPairs` is the ExprOps lane's `absBinderL` (`Tactic/Prims.lean`'s
`cons_binder_spec` speaks of the latter). -/
@[lockstep_simp] theorem absBinderPairs_eq (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    absBinderPairs v = ExprOps.absBinderL v := rfl

open ConRon.Refine2.Lockstep in
theorem strip_pis_all_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = (absBinderPairs a.1, absEIdx a.2))
        (frontend.proj_rec.strip_pis_all pers st fuel h) st lst
        (stripPisAll n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.strip_pis_all, stripPisAll, if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.strip_pis_all, stripPisAll, if_neg (by scalar_tac)]
    lockstep


/-! ### The binder telescope's data are well formed (Rust-side, kind 1)

`intern_e_lam_wf_ls` needs `PropWhenWF` of the datum the port re-interns.  A
telescope `strip_pis_all` / `strip_lams` answer is read out of the store, whose
binder data are well formed (`view_bind_meta_wf`, from `AStateInv`). -/

/-- The binder telescope's data are well formed. -/
def BindersWF (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) : Prop :=
  ∀ p ∈ bs.val, ConRon.Refine.PropWhenWF p.2.pw

theorem binder_copy_from_val (xs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    ∀ (n : Nat) (i : Std.Usize) (out r : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
      xs.val.length - i.val = n →
      arena.expr_ops.binder_copy_from xs i out = ok r → r.val = out.val ++ xs.val.drop i.val := by
  intro n
  induction n with
  | zero =>
    intro i out r hn h
    rw [arena.expr_ops.binder_copy_from.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
  | succ k ih =>
    intro i out r hn h
    rw [arena.expr_ops.binder_copy_from.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    have hxi : i.val < xs.val.length := by omega
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, bm⟩ := p
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm1, hbm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hpv⟩ := ExprOps.vecIndexAt hp
    have hee : e1 = e := dupId_eidx e e1 he1
    have hbb : bm1 = bm := ConRon.Refine.Expr.binder_meta_dup_eq hbm1
    have hov : out1.val = out.val ++ [(e1, bm1)] := ConRon.Refine.vec_push_val hout1
    have hi2v : i2.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
    rw [ih i2 out1 r (by omega) h, hi2v, hov, hee, hbb, List.drop_eq_getElem_cons hxi, hpv]
    simp

theorem cons_binder_val {ty : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    {xs r : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (h : arena.expr_ops.cons_binder ty m xs = ok r) : r.val = (ty, m) :: xs.val := by
  rw [arena.expr_ops.cons_binder] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hee : e = ty := dupId_eidx ty e he
  have hbb : bm = m := ConRon.Refine.Expr.binder_meta_dup_eq hbm
  have hov : out.val = [(e, bm)] := ConRon.Refine.push_new_val hout
  rw [binder_copy_from_val xs _ 0#usize out r rfl h, hov, hee, hbb]
  simp

theorem strip_pis_all_wf {pers st} (hinv : AStateInv pers st) :
    ∀ (n : Nat) (fuel : Std.U64) (h : arena.handle.EIdx) p, fuel.val = n →
      frontend.proj_rec.strip_pis_all pers st fuel h = ok (.Ok p) → BindersWF p.1 := by
  intro n
  induction n with
  | zero =>
    intro fuel h p hn hr
    rw [frontend.proj_rec.strip_pis_all, if_pos (by scalar_tac)] at hr
    obtain ⟨sl, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    obtain ⟨v, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    cases fail_run hr
  | succ k ih =>
    intro fuel h p hn hr
    rw [frontend.proj_rec.strip_pis_all, if_neg (by scalar_tac)] at hr
    obtain ⟨t, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    split at hr
    · obtain ⟨o, ho, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
      cases o with
      | none =>
        simp only at hr
        rw [arena.monad.fail_dangling_e] at hr
        obtain ⟨sl, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        obtain ⟨v, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        cases fail_run hr
      | some q =>
        obtain ⟨ty, b, m⟩ := q
        simp only at hr
        have hm := Lockstep.view_bind_meta_wf hinv ho
        obtain ⟨i1, hi1, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        obtain ⟨r, hrr, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        cases r with
        | Err _ => cases Result.ok_injective hr
        | Ok q =>
          obtain ⟨v, e⟩ := q
          simp only at hr
          obtain ⟨v1, hv1, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
          cases Result.ok_injective hr
          have hi1v : i1.val = k := by
            have := (ConRon.Refine.Nat.usub_val hi1).2; rw [this, hn]; rfl
          have ihv := ih i1 b (v, e) hi1v hrr
          intro x hx
          rw [cons_binder_val hv1] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hm
          · exact ihv x hx
    · obtain ⟨e, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
      cases Result.ok_injective hr
      intro x hx
      simp only [alloc.vec.Vec.new] at hx
      cases hx

open ConRon.Refine2.Lockstep in
/-- A Rust-only fact about the answer joins the relation. -/
theorem LSR.and_rust {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {P : α → Prop} {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : LSR pers R m st lst x) (hP : ∀ a, m = ok (.Ok a) → P a) :
    LSR pers (fun a b => P a ∧ R a b) m st lst x := by
  intro o ho
  have := h o ho
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := this
    exact ⟨b, lst', hx, ⟨hP a ho, hR⟩, h1, h2⟩

open ConRon.Refine2.Lockstep in
/-- `strip_pis_all` against `stripPisAll`, the telescope's data well formed. -/
@[lockstep] theorem strip_pis_all_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => BindersWF a.1 ∧ b = (absBinderPairs a.1, absEIdx a.2))
      (frontend.proj_rec.strip_pis_all pers st fuel h) st lst
      (stripPisAll (absU fuel) (absEIdx h)) :=
  LSR.and_rust (strip_pis_all_aux _ fuel h rfl hrel hinv)
    (fun a ha => strip_pis_all_wf hinv _ fuel h a rfl ha)

open ConRon.Refine2.Lockstep in
/-- `get_app_args_ls` / `head_is`: the port's `view_const_name`. -/
@[lockstep] theorem view_const_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absNIdx a) (arena.monad.view_const_name pers st h) st lst
      (Arena.viewConstName (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewConstName (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by
      have := view_const_name_run₀ hrel hr
      have h2 : (Except.ok (lst.store.viewConstName (absEIdx h), lst) :
          Except Arena.CheckError _) = _ := this
      simp only [Except.ok.injEq, Prod.mk.injEq] at h2
      exact h2.1)
    hrel hinv

open ConRon.Refine2.Lockstep in
@[lockstep] theorem head_is_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (t : arena.handle.NIdx) (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a) (frontend.proj_rec.head_is pers st fuel t e) st lst
      (headIs (absU fuel) (absNIdx t) (absEIdx e)) := by
  apply LSR.of_LS
  rw [frontend.proj_rec.head_is, headIs]
  lockstep

/-! ### `mk_lams`, lockstep (round 3)

A binder datum the port re-interns must be well formed (`intern_e_lam_wf_ls`'s
premise, a Rust-input fact); the telescope's data are, being read out of the
store (`view_bind_meta_wf`), so the statement carries it as a premise on `bs`. -/

open ConRon.Refine2.Lockstep in
@[lockstep] theorem binder_meta_dup_spec (m : kernel.expr.BinderMeta) :
    LSP (kernel.expr.binder_meta_dup m) (fun m' => m' = m) :=
  fun _ h => ConRon.Refine.Expr.binder_meta_dup_eq h

theorem absBinderPairsFrom_nil (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Std.Usize) (hi : bs.val.length ≤ i.val) : absBinderPairsFrom bs i = [] := by
  simp only [absBinderPairsFrom]
  rw [List.drop_eq_nil_of_le hi]; rfl

theorem absBinderPairsFrom_cons (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Std.Usize) (hi : i.val < bs.val.length) :
    absBinderPairsFrom bs i =
      (absEIdx bs.val[i.val].1, ConRon.Refine.absBinderMeta bs.val[i.val].2) ::
        (bs.val.drop (i.val + 1)).map
          (fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)) := by
  simp only [absBinderPairsFrom]
  rw [List.drop_eq_getElem_cons hi]
  rfl

open ConRon.Refine2.Lockstep in
theorem mk_lams_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (i : Std.Usize)
      (body : arena.handle.EIdx),
      bs.val.length - i.val = n → BindersWF bs → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a) (frontend.proj_rec.mk_lams_from pers st bs i body) lst
        (mkLams (absBinderPairsFrom bs i) (absEIdx body)) := by
  induction n with
  | zero =>
    intro pers st lst bs i body hn hwf hrel hinv
    rw [frontend.proj_rec.mk_lams_from, absBinderPairsFrom_nil bs i (by omega), mkLams,
      if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst bs i body hn hwf hrel hinv
    have hi : i.val < bs.val.length := by omega
    have hpw : ConRon.Refine.PropWhenWF bs.val[i.val].2.pw := hwf _ (List.getElem_mem hi)
    rw [frontend.proj_rec.mk_lams_from, absBinderPairsFrom_cons bs i hi, mkLams,
      if_neg (by scalar_tac)]
    lockstep

/-- **`mk_lams_from`** — the cursor companion of `mk_lams`.  The twin conses
on the way OUT, so the cursor recurses to the end of the list and interns
outward from there. -/
theorem mk_lams_from_refines {pers rst lst bs i body o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst) (hwf : BindersWF bs)
    (h : frontend.proj_rec.mk_lams_from pers rst bs i body = ok o) :
    Sim₀ absEIdx pers lst o
      (mkLams (absBinderPairsFrom bs i) (absEIdx body)) :=
  Lockstep.LS.toSim₀ (mk_lams_from_aux _ bs i body rfl hwf hrel hinv) h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem mk_lams_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (body : arena.handle.EIdx)
    (hwf : BindersWF bs) :
    LS pers (fun a b => b = absEIdx a) (frontend.proj_rec.mk_lams pers st bs body) lst
      (mkLams (absBinderPairs bs) (absEIdx body)) := by
  have := mk_lams_from_aux _ bs 0#usize body rfl hwf hrel hinv
  rw [frontend.proj_rec.mk_lams]
  simpa [absBinderPairsFrom, absBinderPairs] using this

/-- **`mk_lams` refines `mkLams`** (`ProjRec.lean:221-228`). -/
theorem mk_lams_refines {pers rst lst bs body o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst) (hwf : BindersWF bs)
    (h : frontend.proj_rec.mk_lams pers rst bs body = ok o) :
    Sim₀ absEIdx pers lst o
      (mkLams (absBinderPairs bs) (absEIdx body)) :=
  Lockstep.LS.toSim₀ (mk_lams_ls hrel hinv bs body hwf) h

theorem absEIdxLFrom_nil (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (hi : args.val.length ≤ i.val) : absEIdxLFrom args i = [] := by
  simp only [absEIdxLFrom]
  rw [List.drop_eq_nil_of_le hi]; rfl

theorem absEIdxLFrom_cons (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (hi : i.val < args.val.length) :
    absEIdxLFrom args i = absEIdx args.val[i.val] :: (args.val.drop (i.val + 1)).map absEIdx := by
  simp only [absEIdxLFrom]
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem absNIdxLFrom_nil (ns : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize)
    (hi : ns.val.length ≤ i.val) : absNIdxLFrom ns i = [] := by
  simp only [absNIdxLFrom]
  rw [List.drop_eq_nil_of_le hi]; rfl

theorem absNIdxLFrom_cons (ns : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize)
    (hi : i.val < ns.val.length) :
    absNIdxLFrom ns i = absNIdx ns.val[i.val] :: (ns.val.drop (i.val + 1)).map absNIdx := by
  simp only [absNIdxLFrom]
  rw [List.drop_eq_getElem_cons hi]
  rfl

attribute [local lockstep_simp] absEIdxLFrom absNIdxLFrom

open ConRon.Refine2.Lockstep in
theorem inst_pis_open_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (e : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx)
      (i : Std.Usize),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = Option.map absEIdx a)
        (frontend.proj_rec.inst_pis_open_from pers st fuel e args i) lst
        (instPisOpen (absU fuel) (absEIdx e) (absEIdxLFrom args i)) := by
  induction n with
  | zero =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [frontend.proj_rec.inst_pis_open_from, absEIdxLFrom_nil args i (by omega), instPisOpen,
      if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [frontend.proj_rec.inst_pis_open_from, absEIdxLFrom_cons args i (by omega), instPisOpen,
      if_neg (by scalar_tac)]
    lockstep

/-- **`inst_pis_open_from`** — the cursor companion of `inst_pis_open`. -/
theorem inst_pis_open_from_refines {pers rst lst fuel e args i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.inst_pis_open_from pers rst fuel e args i = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (instPisOpen (absU fuel) (absEIdx e) (absEIdxLFrom args i)) :=
  Lockstep.LS.toSim₀ (inst_pis_open_from_aux _ fuel e args i rfl hrel hinv) h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem inst_pis_open_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (e : arena.handle.EIdx)
    (args : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (frontend.proj_rec.inst_pis_open pers st fuel e args) lst
      (instPisOpen (absU fuel) (absEIdx e) (absEIdxL args)) := by
  have := inst_pis_open_from_aux _ fuel e args 0#usize rfl hrel hinv
  rw [frontend.proj_rec.inst_pis_open]
  simpa [absEIdxLFrom, absEIdxL] using this

/-- **`inst_pis_open` refines `instPisOpen`** (`ProjRec.lean:232-243`). -/
theorem inst_pis_open_refines {pers rst lst fuel e args o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.inst_pis_open pers rst fuel e args = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (instPisOpen (absU fuel) (absEIdx e) (absEIdxL args)) :=
  Lockstep.LS.toSim₀ (inst_pis_open_ls hrel hinv fuel e args) h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem cons_lidx_spec (l : arena.handle.LIdx) (us : alloc.vec.Vec arena.handle.LIdx) :
    LSP (frontend.proj_rec.cons_lidx l us)
      (fun v => v.val.map absLIdx = absLIdx l :: us.val.map absLIdx) :=
  fun _ h => cons_lidx_refines h

open ConRon.Refine2.Lockstep in
theorem intern_param_levels_from_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (ns : alloc.vec.Vec arena.handle.NIdx) (i : Std.Usize),
      ns.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.val.map absLIdx)
        (frontend.proj_rec.intern_param_levels_from pers st ns i) lst
        (projRecValue.internParamLevels (absNIdxLFrom ns i)) := by
  induction n with
  | zero =>
    intro pers st lst ns i hn hrel hinv
    rw [frontend.proj_rec.intern_param_levels_from, absNIdxLFrom_nil ns i (by omega),
      projRecValue.internParamLevels, if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst ns i hn hrel hinv
    rw [frontend.proj_rec.intern_param_levels_from, absNIdxLFrom_cons ns i (by omega),
      projRecValue.internParamLevels, if_neg (by scalar_tac)]
    lockstep

/-- **`intern_param_levels_from`** — the cursor companion. -/
theorem intern_param_levels_from_refines {pers rst lst ns i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.intern_param_levels_from pers rst ns i = ok o) :
    Sim₀ (fun v => v.val.map absLIdx) pers lst o
      (projRecValue.internParamLevels (absNIdxLFrom ns i)) :=
  Lockstep.LS.toSim₀ (intern_param_levels_from_aux _ ns i rfl hrel hinv) h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem intern_param_levels_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ns : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = a.val.map absLIdx)
      (frontend.proj_rec.intern_param_levels pers st ns) lst
      (projRecValue.internParamLevels (absNIdxL ns)) := by
  have := intern_param_levels_from_aux _ ns 0#usize rfl hrel hinv
  rw [frontend.proj_rec.intern_param_levels]
  simpa [absNIdxLFrom, absNIdxL] using this

/-- **`intern_param_levels` refines `internParamLevels`**. -/
theorem intern_param_levels_refines {pers rst lst ns o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.intern_param_levels pers rst ns = ok o) :
    Sim₀ (fun v => v.val.map absLIdx) pers lst o
      (projRecValue.internParamLevels (absNIdxL ns)) :=
  Lockstep.LS.toSim₀ (intern_param_levels_ls hrel hinv ns) h

/-! ## The two binder bodies -/

/-- The twin's `match bs with | [(d, m)] => … | bs => …` at a list that is not
a singleton. -/
theorem match_single_ne {γ : Type} (l : List (EIdx × ConLeche.BinderMeta))
    (hl : l.length ≠ 1) (f : EIdx → ConLeche.BinderMeta → γ)
    (g : List (EIdx × ConLeche.BinderMeta) → γ) :
    (match l with | [(d, m)] => f d m | bs => g bs) = g l := by
  match l, hl with
  | [], _ => rfl
  | [_], hl => simp at hl
  | _ :: _ :: _, _ => rfl

open ConRon.Refine2.Lockstep in
@[lockstep] theorem mk_proj_motive_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pb : frontend.proj_rec.ProjBuild) (fuel : Std.U64)
    (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (hwf : BindersWF bs) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (frontend.proj_rec.mk_proj_motive_at pers st pb fuel bs) lst
      (mkProjMotiveAt (absProjBuild pb) (absU fuel) (absBinderPairs bs)) := by
  rw [frontend.proj_rec.mk_proj_motive_at]
  by_cases hl : bs.val.length = 1
  · obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hl
    obtain ⟨e, bm⟩ := p
    have hpw : ConRon.Refine.PropWhenWF bm.pw := hwf (e, bm) (by simp [hp])
    have habs : absBinderPairs bs = [(absEIdx e, ConRon.Refine.absBinderMeta bm)] := by
      simp [absBinderPairs, hp]
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) bs 0#usize
        = ok (e, bm) := by
      rw [vec_index_ok_eq bs 0#usize (by simp [hp])]
      simp [hp]
    rw [habs, mkProjMotiveAt, if_neg (by scalar_tac), hidx, bind_tc_ok]
    refine LSR.bind (head_is_ls hrel hinv fuel pb.t e) (by simp [absProjBuild])
      (fun _ => by lockstep_errarm) (fun a b lst1 hR hrel1 hinv1 => ?_)
    subst hR
    cases b <;> simp only [Bool.false_eq_true, if_true, if_false, reduceIte] <;> lockstep
  · rw [mkProjMotiveAt.eq_2 _ _ _ (fun d m hd => hl (by
        have := congrArg List.length hd; simpa [absBinderPairs] using this)),
      if_pos (by scalar_tac)]
    lockstep

/-- **`mk_proj_motive_at`** — the port's split under the domain's view. -/
theorem mk_proj_motive_at_refines {pers rst lst pb fuel bs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst) (hwf : BindersWF bs)
    (h : frontend.proj_rec.mk_proj_motive_at pers rst pb fuel bs = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMotiveAt (absProjBuild pb) (absU fuel) (absBinderPairs bs)) :=
  Lockstep.LS.toSim₀ (mk_proj_motive_at_ls hrel hinv pb fuel bs hwf) h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem mk_proj_motive_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pb : frontend.proj_rec.ProjBuild) (fuel : Std.U64)
    (dom : arena.handle.EIdx) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (frontend.proj_rec.mk_proj_motive pers st pb fuel dom) lst
      (mkProjMotive (absProjBuild pb) (absU fuel) (absEIdx dom)) := by
  rw [frontend.proj_rec.mk_proj_motive, mkProjMotive]
  lockstep

/-- **`mk_proj_motive` refines `mkProjMotive`** (`ProjRec.lean:277-293`). -/
theorem mk_proj_motive_refines {pers rst lst pb fuel dom o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_proj_motive pers rst pb fuel dom = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMotive (absProjBuild pb) (absU fuel) (absEIdx dom)) :=
  Lockstep.LS.toSim₀ (mk_proj_motive_ls hrel hinv pb fuel dom) h

open ConRon.Refine2.Lockstep in
/-- `usize as u64`: a widening, so the value is kept. -/
@[lockstep] theorem usize_cast_u64_spec (i : Std.Usize) :
    LSP (lift (UScalar.cast .U64 i)) (fun r : Std.U64 => r.val = i.val) := by
  intro r h
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have := i.hBounds
  simp only [UScalarTy.numBits] at this ⊢
  cases System.Platform.numBits_eq with
  | inl h => rw [h] at this; omega
  | inr h => rw [h] at this; omega

open ConRon.Refine2.Lockstep in
@[lockstep] theorem mk_proj_minor_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pb : frontend.proj_rec.ProjBuild) (fuel : Std.U64)
    (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (major : arena.handle.EIdx)
    (hwf : BindersWF bs) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (frontend.proj_rec.mk_proj_minor_at pers st pb fuel bs major) lst
      (mkProjMinorAt (absProjBuild pb) (absU fuel) (absBinderPairs bs) (absEIdx major)) := by
  rw [frontend.proj_rec.mk_proj_minor_at, mkProjMinorAt]
  refine LSR.bind (head_is_ls hrel hinv fuel pb.ctor major) (by simp [absProjBuild])
    (fun _ => by lockstep_errarm) (fun a b lst1 hR hrel1 hinv1 => ?_)
  subst hR
  have hlen : (absBinderPairs bs).length = bs.val.length := by simp [absBinderPairs]
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false, reduceIte]
  · lockstep
  · by_cases hi : (absProjBuild pb).i < (absBinderPairs bs).length
    · rw [if_pos hi]
      have hi' : pb.i.val < bs.val.length := by simpa [absProjBuild, hlen] using hi
      have hl' : (alloc.vec.Vec.len bs).val = bs.val.length := by simp
      lockstep
    · rw [if_neg hi]
      have hi' : ¬ pb.i.val < bs.val.length := by simpa [absProjBuild, hlen] using hi
      have hl' : (alloc.vec.Vec.len bs).val = bs.val.length := by simp
      lockstep_step
      rw [if_pos (by scalar_tac)]
      lockstep

/-- **`mk_proj_minor_at`** — the port's split under the domain's view. -/
theorem mk_proj_minor_at_refines {pers rst lst pb fuel bs major o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst) (hwf : BindersWF bs)
    (h : frontend.proj_rec.mk_proj_minor_at pers rst pb fuel bs major = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMinorAt (absProjBuild pb) (absU fuel) (absBinderPairs bs)
        (absEIdx major)) :=
  Lockstep.LS.toSim₀ (mk_proj_minor_at_ls hrel hinv pb fuel bs major hwf) h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem mk_proj_minor_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pb : frontend.proj_rec.ProjBuild) (fuel : Std.U64)
    (dom : arena.handle.EIdx) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (frontend.proj_rec.mk_proj_minor pers st pb fuel dom) lst
      (mkProjMinor (absProjBuild pb) (absU fuel) (absEIdx dom)) := by
  rw [frontend.proj_rec.mk_proj_minor, mkProjMinor]
  refine LSR.bind (strip_pis_all_ls hrel hinv fuel dom) rfl
    (fun _ => by lockstep_errarm) (fun a b lst1 hR hrel1 hinv1 => ?_)
  obtain ⟨hwf, rfl⟩ := hR
  obtain ⟨v, e⟩ := a
  refine LSR.bind (ExprOps.get_app_args_ls hrel1 hinv1 fuel e) rfl
    (fun _ => by lockstep_errarm) (fun args b lst2 hR hrel2 hinv2 => ?_)
  subst hR
  by_cases hnil : args.val = []
  · have hl0 : (alloc.vec.Vec.len args).val = 0 := by simp [hnil]
    have hlast : (ExprOps.absEIdxList args).getLast? = none := by
      simp [ExprOps.absEIdxList, hnil]
    simp only [hlast]
    rw [if_pos (by scalar_tac)]
    lockstep
  · have hpos : 0 < args.val.length := List.length_pos_iff.mpr hnil
    have hlast : (ExprOps.absEIdxList args).getLast? =
        some (absEIdx (args.val[args.val.length - 1]'(by omega))) := by
      simp [ExprOps.absEIdxList, List.getLast?_eq_getElem?, List.getElem?_map,
        List.getElem?_eq_getElem (show args.val.length - 1 < args.val.length by omega)]
    simp only [hlast]
    rw [if_neg (by scalar_tac)]
    lockstep

/-- **`mk_proj_minor` refines `mkProjMinor`** (`ProjRec.lean:297-310`). -/
theorem mk_proj_minor_refines {pers rst lst pb fuel dom o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_proj_minor pers rst pb fuel dom = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMinor (absProjBuild pb) (absU fuel) (absEIdx dom)) :=
  Lockstep.LS.toSim₀ (mk_proj_minor_ls hrel hinv pb fuel dom) h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem cons_eidx_spec (a : arena.handle.EIdx) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.expr_ops.cons_eidx a xs) (fun r => absEIdxL r = absEIdx a :: absEIdxL xs) :=
  fun _ h => by simpa [ExprOps.absEIdxL, absEIdxL] using ExprOps.cons_eidx_refines h

open ConRon.Refine2.Lockstep in
/-- `build_binders` against `buildBinders`, by induction on the count.  The
port's `build_binders_at` (the `.forallE` arm, split off for rule 5) is
unfolded in place: it takes the count BEFORE the decrement, so it has no
statement of its own against the twin's arm (which takes the count after). -/
theorem build_binders_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (kind : frontend.proj_rec.ProjBinderKind) (pb : frontend.proj_rec.ProjBuild)
      (fuel k : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = Option.map (fun p => (absEIdxL p.1, absEIdx p.2)) a)
        (frontend.proj_rec.build_binders pers st kind pb fuel k h) lst
        (buildBinders (absProjBinderKind kind) (absProjBuild pb) (absU fuel) n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst kind pb fuel k h hn hrel hinv
    rw [frontend.proj_rec.build_binders, buildBinders, if_pos (by scalar_tac)]
    lockstep
  | succ m ih =>
    intro pers st lst kind pb fuel k h hn hrel hinv
    rw [frontend.proj_rec.build_binders, buildBinders, if_neg (by scalar_tac)]
    cases kind <;>
    · simp only [frontend.proj_rec.build_binders_at, absProjBinderKind]
      lockstep

open ConRon.Refine2.Lockstep in
@[lockstep] theorem build_binders_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (kind : frontend.proj_rec.ProjBinderKind)
    (pb : frontend.proj_rec.ProjBuild) (fuel k : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = Option.map (fun p => (absEIdxL p.1, absEIdx p.2)) a)
      (frontend.proj_rec.build_binders pers st kind pb fuel k h) lst
      (buildBinders (absProjBinderKind kind) (absProjBuild pb) (absU fuel) (absU k)
        (absEIdx h)) :=
  build_binders_aux _ kind pb fuel k h rfl hrel hinv

/-- **`build_binders` refines `buildBinders`** (`ProjRec.lean:314-339`).  The
recursion is on `k`, as the twin's is: a motive or minor count is never
large, so this is not a `Vec` cursor. -/
theorem build_binders_refines {pers rst lst kind pb fuel k h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.build_binders pers rst kind pb fuel k h' = ok o) :
    Sim₀ (Option.map fun p => (absEIdxL p.1, absEIdx p.2)) pers lst o
      (buildBinders (absProjBinderKind kind) (absProjBuild pb) (absU fuel)
        (absU k) (absEIdx h')) :=
  Lockstep.LS.toSim₀ (build_binders_ls hrel hinv kind pb fuel k h') h

/-! ## The rewrite itself

`projRecValue` is one 48-line `do` block on the twin's side and six functions
on the port's, split at the twin's own `let` boundaries (P4c's arrangement for
this shape).  The five splits are stated against the twin's arm inline; the
entry point is stated against the twin. -/



open ConRon.Refine2.Lockstep in
@[lockstep] theorem one_lidx_spec (l : arena.handle.LIdx) :
    LSP (frontend.proj_rec.one_lidx l) (fun v => v.val.map absLIdx = [absLIdx l]) :=
  fun _ h => one_lidx_refines h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem append_eidx_spec (out xs : alloc.vec.Vec arena.handle.EIdx) :
    LSP (frontend.proj_rec.append_eidx out xs)
      (fun v => absEIdxL v = absEIdxL out ++ absEIdxL xs) :=
  fun _ h => append_eidx_refines h

theorem bvar_zero_contra₁ {bv : BitVec UScalarTy.U64.numBits}
    (h1 : (UScalar.mk bv : Std.U64) = UScalar.mk (BitVec.ofNat _ 0))
    (h2 : ENodeView.bvar (UScalar.mk bv : Std.U64).val = ENodeView.bvar 0 → False) : False :=
  h2 (by rw [h1]; rfl)

theorem bvar_zero_contra₂ {bv : BitVec UScalarTy.U64.numBits}
    (h1 : (UScalar.mk bv : Std.U64) = UScalar.mk (BitVec.ofNat _ 0) → False)
    (h2 : ENodeView.bvar (UScalar.mk bv : Std.U64).val = ENodeView.bvar 0) : False := by
  apply h1
  injection h2 with h2
  exact UScalar.eq_of_val_eq (by rw [h2]; rfl)

theorem strip_lams_wf {pers st} (hinv : AStateInv pers st) :
    ∀ (n : Nat) (k : Std.U64) (h : arena.handle.EIdx) p, k.val = n →
      arena.expr_ops.strip_lams pers st k h = ok (.Ok (some p)) → BindersWF p.1 := by
  intro n
  induction n with
  | zero =>
    intro k h p hn hr
    rw [arena.expr_ops.strip_lams, if_pos (by scalar_tac)] at hr
    obtain ⟨e, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    cases Result.ok_injective hr
    intro x hx
    simp only [alloc.vec.Vec.new] at hx
    cases hx
  | succ k' ih =>
    intro k h p hn hr
    rw [arena.expr_ops.strip_lams, if_neg (by scalar_tac)] at hr
    obtain ⟨t, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    split at hr
    · obtain ⟨o, ho, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
      cases o with
      | none =>
        simp only at hr
        rw [arena.monad.fail_dangling_e] at hr
        obtain ⟨sl, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        obtain ⟨v, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        cases fail_run hr
      | some q =>
        obtain ⟨ty, b, m⟩ := q
        simp only at hr
        have hm := Lockstep.view_bind_meta_wf hinv ho
        obtain ⟨i1, hi1, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        obtain ⟨r, hrr, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
        cases r with
        | Err _ => cases Result.ok_injective hr
        | Ok q =>
          cases q with
          | none => cases Result.ok_injective hr
          | some q =>
            obtain ⟨v, e⟩ := q
            simp only at hr
            obtain ⟨v1, hv1, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
            cases Result.ok_injective hr
            have hi1v : i1.val = k' := by
              have := (ConRon.Refine.Nat.usub_val hi1).2; rw [this, hn]; rfl
            have ihv := ih i1 b (v, e) hi1v hrr
            intro x hx
            rw [cons_binder_val hv1] at hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hm
            · exact ihv x hx
    · cases Result.ok_injective hr

open ConRon.Refine2.Lockstep in
/-- `strip_lams` (the ExprOps lane's) with the telescope's data well formed. -/
theorem strip_lams_wls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => (∀ p, a = some p → BindersWF p.1) ∧ b = ExprOps.absStrip a)
      (arena.expr_ops.strip_lams pers st k h) st lst (stripLams (absU k) (absEIdx h)) :=
  LSR.and_rust (ExprOps.strip_lams_ls hrel hinv k h)
    (fun a ha p hp => by subst hp; exact strip_lams_wf hinv _ k h p rfl ha)

theorem absBinders_eq (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    ExprOps.absBinders v = absBinderPairs v := rfl

attribute [local lockstep_inline] frontend.proj_rec.proj_rec_value_ty
  frontend.proj_rec.proj_rec_value_at frontend.proj_rec.proj_rec_value_binders
  frontend.proj_rec.proj_rec_value_major frontend.proj_rec.proj_rec_value_app

open ConRon.Refine2.Lockstep in
/-- **`proj_rec_value` against `projRecValue`**, lockstep: the port's five
splits are unfolded in place (`lockstep_inline`), the twin is its one block. -/
@[lockstep] theorem proj_rec_value_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (o' : frontend.types.ProjRecOwner)
    (l : arena.handle.LIdx) (ty val : arena.handle.EIdx) (i : Std.U64) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (frontend.proj_rec.proj_rec_value pers st fuel o' l ty val i) lst
      (projRecValue (absU fuel) (absProjRecOwner o') (absLIdx l) (absEIdx ty)
        (absEIdx val) (absU i)) := by
  rw [frontend.proj_rec.proj_rec_value, projRecValue]
  refine LSP.bind (uscalar_add o'.n_p 1#u64) (fun i1 hi1 => ?_)
  refine LSR.bind (strip_lams_wls hrel hinv i1 val) (by simp [hi1, absProjRecOwner])
    (fun _ => by lockstep_errarm) (fun a b lst1 hR hrel1 hinv1 => ?_)
  obtain ⟨hwf, rfl⟩ := hR
  cases a with
  | none => simp only [ExprOps.absStrip, Option.map_none]; lockstep
  | some p =>
  obtain ⟨lbs, body⟩ := p
  have hwf' : BindersWF lbs := hwf _ rfl
  simp only [ExprOps.absStrip, Option.map_some, absBinders_eq]
  -- Thirteen zip steps reach the port's `match i4 with | 0#uscalar => …`,
  -- which splits the scalar into its bit-vector, which the twin's `match .bvar
  -- ↑i4 with | .bvar 0 => …` does not see: split the twin's match and close
  -- the crossed arms.  Then the port's three tests (`eq2`, `!=`, `≥`) against
  -- the twin's one combined `||` test, decided explicitly: since the tactic's
  -- round-2 twin-`if` rules, the zip does not stop at an undecided twin test.
  iterate 13 lockstep_step
  on_goal 2 =>
    split
    all_goals try (exfalso; exact bvar_zero_contra₁ (by assumption) (by assumption))
    all_goals try (exfalso; exact bvar_zero_contra₂ (by assumption) (by assumption))
    on_goal 1 =>
      iterate 3 lockstep_step
      on_goal 2 =>
        rename_i hb
        have hfi := ‹¬(_ != _) = true›
        simp only [beq_iff_eq, bne_iff_ne, ne_eq, Decidable.not_not] at hb hfi
        lockstep_step
        · rw [if_pos (by simp [absProjRecOwner, hb, hfi]; scalar_tac)]
          lockstep
        · rw [if_neg (by simp [absProjRecOwner, hb, hfi]; scalar_tac)]
          lockstep
      all_goals
        rw [if_pos (by
          first
          | (have h1 := ‹¬(_ == _) = true›
             simp only [beq_iff_eq] at h1
             simp [absProjRecOwner, bne_iff_ne, h1])
          | (have h1 := ‹(_ != _) = true›
             simp only [bne_iff_ne, ne_eq] at h1
             have h2 : ¬ (UScalar.val _ = UScalar.val _) := fun h => h1 (UScalar.eq_of_val_eq h)
             simp [absProjRecOwner, bne_iff_ne, h2]))]
        lockstep
    -- the port's other scalars: the twin's match, split, is at its `_` arm
    all_goals
      split
      all_goals first
        | (exfalso; exact bvar_zero_contra₁ (by assumption) (by assumption))
        | (exfalso; exact bvar_zero_contra₂ (by assumption) (by assumption))
        | lockstep
  all_goals lockstep

/-- **`proj_rec_value` refines `projRecValue`** (`ProjRec.lean:343-403`) —
**the rewrite**, and one of the tier's named deliverables. -/
theorem proj_rec_value_refines {pers rst lst fuel o' l ty val i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_value pers rst fuel o' l ty val i = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRecValue (absU fuel) (absProjRecOwner o') (absLIdx l) (absEIdx ty)
        (absEIdx val) (absU i)) :=
  Lockstep.LS.toSim₀ (proj_rec_value_ls hrel hinv fuel o' l ty val i) h

/-! ## The owner census -/

open ConRon.Refine2.Lockstep in
/-- The visited set starts empty.  Not `@[lockstep]`: `Tactic/Prims.lean`'s
`hashmap2_new_eidx_spec` (the ExprOps memos' relations) is filed under the same
Rust head, so `occurs_const_fast` takes this one by hand. -/
theorem hashmap2_new_hset_spec :
    LSP (ron.hashmap2.HashMap2.new arena.handle.EIdx Bool)
      (fun m => HSetRel m (∅ : Std.HashSet EIdx)) := by
  intro m h
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) h
  exact ⟨fun k => by rw [hnone k]; simp, hinv⟩

open ConRon.Refine2.Lockstep in
@[lockstep] theorem occurs_const_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx)
    {seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {ls : Std.HashSet EIdx}
    (hs : HSetRel seen ls) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => a.1 = b.1 ∧ HSetRel a.2 b.2)
      (frontend.proj_rec.occurs_const_go pers st n seen fuel h) st lst
      (occursConstGo (absNIdx n) ls (absU fuel) (absEIdx h)) :=
  occurs_const_go_aux _ n seen ls fuel h rfl hs hrel hinv

open ConRon.Refine2.Lockstep in
@[lockstep] theorem occurs_const_fast_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (n : arena.handle.NIdx) (h : arena.handle.EIdx) :
    LSR pers (fun a b => a = b) (frontend.proj_rec.occurs_const_fast pers st fuel n h) st lst
      (occursConstFast (absU fuel) (absNIdx n) (absEIdx h)) := by
  apply LSR.of_LS
  rw [frontend.proj_rec.occurs_const_fast, occursConstFast]
  refine LS.rust_assoc (LSP.bind hashmap2_new_hset_spec (fun m hm => ?_))
  lockstep

open ConRon.Refine2.Lockstep in
theorem occurs_any_of_from_aux (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (ns : alloc.vec.Vec arena.handle.NIdx) (d : arena.handle.EIdx)
      (i : Std.Usize),
      ns.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => a = b) (frontend.proj_rec.occurs_any_of_from pers st fuel ns d i)
        st lst (occursAnyOf (absU fuel) (absNIdxLFrom ns i) (absEIdx d)) := by
  induction N with
  | zero =>
    intro pers st lst fuel ns d i hn hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.occurs_any_of_from, absNIdxLFrom_nil ns i (by omega), occursAnyOf,
      if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst fuel ns d i hn hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.occurs_any_of_from, absNIdxLFrom_cons ns i (by omega), occursAnyOf,
      if_neg (by scalar_tac)]
    lockstep

open ConRon.Refine2.Lockstep in
@[lockstep] theorem occurs_any_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (ns : alloc.vec.Vec arena.handle.NIdx)
    (d : arena.handle.EIdx) :
    LSR pers (fun a b => a = b) (frontend.proj_rec.occurs_any_of pers st fuel ns d) st lst
      (occursAnyOf (absU fuel) (absNIdxL ns) (absEIdx d)) := by
  have := occurs_any_of_from_aux _ fuel ns d 0#usize rfl hrel hinv
  rw [frontend.proj_rec.occurs_any_of]
  simpa [absNIdxLFrom, absNIdxL] using this

open ConRon.Refine2.Lockstep in
theorem doms_mention_any_from_aux (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (ns : alloc.vec.Vec arena.handle.NIdx)
      (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (i : Std.Usize),
      bs.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => a = b) (frontend.proj_rec.doms_mention_any_from pers st fuel ns bs i)
        st lst (domsMentionAny (absU fuel) (absNIdxL ns) (absBinderPairsFrom bs i)) := by
  induction N with
  | zero =>
    intro pers st lst fuel ns bs i hn hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.doms_mention_any_from, absBinderPairsFrom_nil bs i (by omega),
      domsMentionAny, if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst fuel ns bs i hn hrel hinv
    apply LSR.of_LS
    have hi : i.val < bs.val.length := by omega
    rw [frontend.proj_rec.doms_mention_any_from, absBinderPairsFrom_cons bs i hi,
      domsMentionAny, if_neg (by scalar_tac), vec_index_ok_eq bs i hi, bind_tc_ok]
    rcases hx : bs.val[i.val] with ⟨e, m⟩
    try dsimp only
    lockstep

open ConRon.Refine2.Lockstep in
@[lockstep] theorem doms_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (ns : alloc.vec.Vec arena.handle.NIdx)
    (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    LSR pers (fun a b => a = b) (frontend.proj_rec.doms_mention_any pers st fuel ns bs) st lst
      (domsMentionAny (absU fuel) (absNIdxL ns) (absBinderPairs bs)) := by
  have := doms_mention_any_from_aux _ fuel ns bs 0#usize rfl hrel hinv
  rw [frontend.proj_rec.doms_mention_any]
  simpa [absBinderPairsFrom, absBinderPairs] using this

theorem absProjCtorRecLFrom_nil (v : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx))
    (i : Std.Usize) (hi : v.val.length ≤ i.val) : absProjCtorRecLFrom v i = [] := by
  simp only [absProjCtorRecLFrom]; rw [List.drop_eq_nil_of_le hi]; rfl

theorem absProjCtorRecLFrom_cons (v : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx))
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absProjCtorRecLFrom v i = absProjCtorRec v.val[i.val] :: (v.val.drop (i.val + 1)).map absProjCtorRec := by
  simp only [absProjCtorRecLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

attribute [local lockstep_simp] absProjCtorRec

open ConRon.Refine2.Lockstep in
theorem ctors_mention_block_from_aux (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (ns : alloc.vec.Vec arena.handle.NIdx)
      (ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)) (i : Std.Usize),
      ctors.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => a = b)
        (frontend.proj_rec.ctors_mention_block_from pers st fuel ns ctors i)
        st lst (ctorsMentionBlock (absU fuel) (absNIdxL ns) (absProjCtorRecLFrom ctors i)) := by
  induction N with
  | zero =>
    intro pers st lst fuel ns ctors i hn hrel hinv
    apply LSR.of_LS
    rw [frontend.proj_rec.ctors_mention_block_from, absProjCtorRecLFrom_nil ctors i (by omega),
      ctorsMentionBlock, if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst fuel ns ctors i hn hrel hinv
    apply LSR.of_LS
    have hi : i.val < ctors.val.length := by omega
    rw [frontend.proj_rec.ctors_mention_block_from, absProjCtorRecLFrom_cons ctors i hi,
      ctorsMentionBlock, if_neg (by scalar_tac), vec_index_ok_eq ctors i hi, bind_tc_ok]
    rcases hx : ctors.val[i.val] with ⟨c, nf, e⟩
    try dsimp only
    lockstep

open ConRon.Refine2.Lockstep in
@[lockstep] theorem ctors_mention_block_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (ns : alloc.vec.Vec arena.handle.NIdx)
    (ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)) :
    LSR pers (fun a b => a = b) (frontend.proj_rec.ctors_mention_block pers st fuel ns ctors)
      st lst (ctorsMentionBlock (absU fuel) (absNIdxL ns) (absProjCtorRecL ctors)) := by
  have := ctors_mention_block_from_aux _ fuel ns ctors 0#usize rfl hrel hinv
  rw [frontend.proj_rec.ctors_mention_block]
  simpa [absProjCtorRecLFrom, absProjCtorRecL] using this

/-- **`find_ctor_rec_from`** — the cursor companion.  Deviation 2: the port
answers the INDEX of the record the twin finds. -/
theorem find_ctor_rec_from_refines {ctors c} :
    ∀ (N : Nat) (i : Std.Usize) {o}, ctors.val.length - i.val = N →
      frontend.proj_rec.find_ctor_rec_from ctors c i = ok o →
      (o = none ∧ findCtorRec (absNIdx c) (absProjCtorRecLFrom ctors i) = none) ∨
      (∃ j : Std.Usize, ∃ hj : j.val < ctors.val.length, o = some j ∧
        findCtorRec (absNIdx c) (absProjCtorRecLFrom ctors i) =
          some (absProjCtorRec ctors.val[j.val])) := by
  intro N
  induction N with
  | zero =>
    intro i o hn h
    rw [frontend.proj_rec.find_ctor_rec_from, if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    left
    refine ⟨rfl, ?_⟩
    simp only [absProjCtorRecLFrom]
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    intro i o hn h
    have hi : i.val < ctors.val.length := by omega
    rw [frontend.proj_rec.find_ctor_rec_from, if_neg (by scalar_tac),
      vec_index_ok_eq ctors i hi, bind_tc_ok] at h
    rcases hx : ctors.val[i.val] with ⟨n1, nf, e⟩
    rw [hx] at h
    change (do
      let b ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 n1 c
      if b = true then ok (some i) else do
        let i2 ← i + 1#usize
        frontend.proj_rec.find_ctor_rec_from ctors c i2) = ok o at h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b = (absNIdx n1 == absNIdx c) := nidx_eq2_abs hb
    have hcons : absProjCtorRecLFrom ctors i =
        absProjCtorRec (n1, nf, e) :: absProjCtorRecLFrom ctors ⟨i.val + 1, by scalar_tac⟩ := by
      simp only [absProjCtorRecLFrom]
      rw [List.drop_eq_getElem_cons hi, hx]; rfl
    split at h
    · rename_i hbt
      cases Result.ok_injective h
      right
      refine ⟨i, hi, rfl, ?_⟩
      have : ((absProjCtorRec (n1, nf, e)).1 == absNIdx c) = true := by
        show (absNIdx n1 == absNIdx c) = true
        rw [← hbv]; exact hbt
      rw [hcons, findCtorRec, if_pos this, hx]
    · rename_i hbt
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
      have hnf : ((absProjCtorRec (n1, nf, e)).1 == absNIdx c) = false := by
        show (absNIdx n1 == absNIdx c) = false
        rw [← hbv]; simpa using hbt
      have hrest : absProjCtorRecLFrom ctors ⟨i.val + 1, by scalar_tac⟩ =
          absProjCtorRecLFrom ctors i2 := by
        simp only [absProjCtorRecLFrom, hi2v]; rfl
      rw [hcons, findCtorRec, hnf, if_neg (by simp), hrest]
      exact ih i2 (by omega) h

theorem find_ctor_rec_refines {ctors c o}
    (h : frontend.proj_rec.find_ctor_rec ctors c = ok o) :
    (o = none ∧ findCtorRec (absNIdx c) (absProjCtorRecL ctors) = none) ∨
      (∃ j : Std.Usize, ∃ hj : j.val < ctors.val.length, o = some j ∧
        findCtorRec (absNIdx c) (absProjCtorRecL ctors) =
          some (absProjCtorRec ctors.val[j.val])) := by
  rw [frontend.proj_rec.find_ctor_rec] at h
  have := find_ctor_rec_from_refines _ 0#usize rfl h
  simpa [absProjCtorRecLFrom, absProjCtorRecL] using this

/-- **`find_rec_rec_from`** — the cursor companion. -/
theorem find_rec_rec_from_refines {recs n} :
    ∀ (N : Nat) (i : Std.Usize) {o}, recs.val.length - i.val = N →
      frontend.proj_rec.find_rec_rec_from recs n i = ok o →
      (o = none ∧ findRecRec (absNIdx n) (absProjRecRecLFrom recs i) = none) ∨
      (∃ j : Std.Usize, ∃ hj : j.val < recs.val.length, o = some j ∧
        findRecRec (absNIdx n) (absProjRecRecLFrom recs i) =
          some (absProjRecRec recs.val[j.val])) := by
  intro N
  induction N with
  | zero =>
    intro i o hn h
    rw [frontend.proj_rec.find_rec_rec_from, if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    left
    refine ⟨rfl, ?_⟩
    simp only [absProjRecRecLFrom]
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    intro i o hn h
    have hi : i.val < recs.val.length := by omega
    rw [frontend.proj_rec.find_rec_rec_from, if_neg (by scalar_tac),
      vec_index_ok_eq recs i hi, bind_tc_ok] at h
    rcases hx : recs.val[i.val] with ⟨n1, lps, e, a, b⟩
    rw [hx] at h
    change (do
      let b ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 n1 n
      if b = true then ok (some i) else do
        let i2 ← i + 1#usize
        frontend.proj_rec.find_rec_rec_from recs n i2) = ok o at h
    obtain ⟨bb, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : bb = (absNIdx n1 == absNIdx n) := nidx_eq2_abs hb
    have hcons : absProjRecRecLFrom recs i =
        absProjRecRec (n1, lps, e, a, b) ::
          absProjRecRecLFrom recs ⟨i.val + 1, by scalar_tac⟩ := by
      simp only [absProjRecRecLFrom]
      rw [List.drop_eq_getElem_cons hi, hx]; rfl
    split at h
    · rename_i hbt
      cases Result.ok_injective h
      right
      refine ⟨i, hi, rfl, ?_⟩
      have : ((absProjRecRec (n1, lps, e, a, b)).1 == absNIdx n) = true := by
        show (absNIdx n1 == absNIdx n) = true
        rw [← hbv]; exact hbt
      rw [hcons, findRecRec, if_pos this, hx]
    · rename_i hbt
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
      have hnf : ((absProjRecRec (n1, lps, e, a, b)).1 == absNIdx n) = false := by
        show (absNIdx n1 == absNIdx n) = false
        rw [← hbv]; simpa using hbt
      have hrest : absProjRecRecLFrom recs ⟨i.val + 1, by scalar_tac⟩ =
          absProjRecRecLFrom recs i2 := by
        simp only [absProjRecRecLFrom, hi2v]; rfl
      rw [hcons, findRecRec, hnf, if_neg (by simp), hrest]
      exact ih i2 (by omega) h

theorem find_rec_rec_refines {recs n o}
    (h : frontend.proj_rec.find_rec_rec recs n = ok o) :
    (o = none ∧ findRecRec (absNIdx n) (absProjRecRecL recs) = none) ∨
      (∃ j : Std.Usize, ∃ hj : j.val < recs.val.length, o = some j ∧
        findRecRec (absNIdx n) (absProjRecRecL recs) =
          some (absProjRecRec recs.val[j.val])) := by
  rw [frontend.proj_rec.find_rec_rec] at h
  have := find_rec_rec_from_refines _ 0#usize rfl h
  simpa [absProjRecRecLFrom, absProjRecRecL] using this

open ConRon.Refine2.Lockstep in
@[lockstep] theorem read_level_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LS pers (fun a b => ConRon.Refine.LevelWF a ∧ b = ConRon.Refine.absLevel a)
      (arena.monad.read_level_m pers st h) lst (Arena.readLevelM (absLIdx h)) := by
  intro o st' hm
  have hS := read_level_m_run₀ hrel hinv hm
  have hW := (read_level_m_wf hinv hm).1
  cases o with
  | Err e => exact hS
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := hS
    exact ⟨_, lst', hx, ⟨hW a rfl, rfl⟩, h1, h2⟩

open ConRon.Refine2.Lockstep in
@[lockstep] theorem level_zero_spec :
    LSP kernel.level.zero
      (fun z => ConRon.Refine.LevelWF z ∧ ConRon.Refine.absLevel z = ConLeche.Level.zero) :=
  fun _ h => ⟨ConRon.Refine.Level.zero_wf' h, ConRon.Refine.Level.zero_refines h⟩

open ConRon.Refine2.Lockstep in
@[lockstep] theorem level_is_equiv_spec {a b : kernel.level.Level}
    (ha : ConRon.Refine.LevelWF a) (hb : ConRon.Refine.LevelWF b) :
    LSP (kernel.level.is_equiv a b)
      (fun o => o = ConLeche.Level.isEquiv (ConRon.Refine.absLevel a) (ConRon.Refine.absLevel b)) :=
  fun _ h => (ConRon.Refine.Level.is_equiv_refines ha hb h).symm

open ConRon.Refine2.Lockstep in
/-- `find_ctor_rec`: the port's index names the record the twin's `findCtorRec`
finds (a `TwinEq` the twin side is rewritten with). -/
@[lockstep] theorem find_ctor_rec_spec
    (ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx))
    (c : arena.handle.NIdx) :
    LSP (frontend.proj_rec.find_ctor_rec ctors c)
      (fun o => (∀ j, o = some j → j.val < ctors.val.length) ∧
        TwinEq (findCtorRec (absNIdx c) (absProjCtorRecL ctors))
          (o.bind fun j => (absProjCtorRecL ctors)[j.val]?)) := by
  intro o h
  rcases find_ctor_rec_refines h with ⟨ho, hn⟩ | ⟨j, hj, ho, hs⟩
  · subst ho; exact ⟨fun _ h => (by cases h), hn⟩
  · subst ho
    refine ⟨fun j' h' => (by cases h'; exact hj), ?_⟩
    show _ = _
    rw [hs]
    simp [absProjCtorRecL, hj]

open ConRon.Refine2.Lockstep in
@[lockstep] theorem find_rec_rec_spec
    (recs : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64))
    (n : arena.handle.NIdx) :
    LSP (frontend.proj_rec.find_rec_rec recs n)
      (fun o => (∀ j, o = some j → j.val < recs.val.length) ∧
        TwinEq (findRecRec (absNIdx n) (absProjRecRecL recs))
          (o.bind fun j => (absProjRecRecL recs)[j.val]?)) := by
  intro o h
  rcases find_rec_rec_refines h with ⟨ho, hn⟩ | ⟨j, hj, ho, hs⟩
  · subst ho; exact ⟨fun _ h => (by cases h), hn⟩
  · subst ho
    refine ⟨fun j' h' => (by cases h'; exact hj), ?_⟩
    show _ = _
    rw [hs]
    simp [absProjRecRecL, hj]

open ConRon.Refine2.Lockstep in
/-- The port's `T.rec` component: `intern_n_node` at `Str n v` with `v` the
code points of `M_REC`, against the twin's `internNNode (.str n "rec")`. -/
@[lockstep] theorem intern_rec_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (v : alloc.vec.Vec Std.U32)
    (sl : Slice Std.U32) (hsl : lift (Std.Array.to_slice frontend.proj_rec.M_REC) = ok sl)
    (hv : kernel.core_types.code_points sl = ok v) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_n_node pers st (.Str n v)) lst
      (Arena.internNNode (.str (absNIdx n) "rec")) := by
  have hvv := lit_cps hsl hv
  have hwf : ConRon.Refine.StrWF v := by
    intro c hc; rw [hvv] at hc
    simp only [frontend.proj_rec.M_REC, Std.Array.make] at hc
    revert c; decide
  have ha : absNNodeView (.Str n v) = .str (absNIdx n) "rec" := by
    simp only [absNNodeView, ConRon.Refine.absString, hvv, frontend.proj_rec.M_REC,
      Std.Array.make]
    rfl
  rw [← ha]
  exact LS.ofSim₀ fun _ h => intern_n_node_run₀ hrel hinv (.Str n v) hwf h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem nidx_vec_dup_spec' (ns : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.env.nidx_vec_dup ns) (fun r => r.val = ns.val) :=
  fun _ h => nidx_vec_dup_val h

theorem candidates_from_loop_val (tail : alloc.vec.Vec frontend.types.ProjRecOwner) :
    ∀ (k : Nat) (out : alloc.vec.Vec frontend.types.ProjRecOwner) (j : Std.Usize) r,
      tail.val.length - j.val = k →
      frontend.proj_rec.proj_rec_candidates_from_loop tail out (alloc.vec.Vec.len tail) j = ok r →
      absProjRecOwnerL r = absProjRecOwnerL out ++ (tail.val.drop j.val).map absProjRecOwner := by
  intro k
  induction k with
  | zero =>
    intro out j r hk h
    rw [frontend.proj_rec.proj_rec_candidates_from_loop, if_neg (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ k ih =>
    intro out j r hk h
    have hj : j.val < tail.val.length := by omega
    rw [frontend.proj_rec.proj_rec_candidates_from_loop, if_pos (by scalar_tac),
      vec_index_ok_eq tail j hj, bind_tc_ok] at h
    obtain ⟨p1, hp1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hj1v : j1.val = j.val + 1 := (ConRon.Refine.Nat.uadd_val hj1).trans (by simp)
    rw [ih o1 j1 r (by omega) h, hj1v]
    simp only [absProjRecOwnerL, ConRon.Refine.vec_push_val ho1, List.map_append, List.map_cons,
      List.map_nil, proj_rec_owner_dup_refines hp1, List.append_assoc, List.singleton_append,
      List.drop_eq_getElem_cons hj]

open ConRon.Refine2.Lockstep in
@[lockstep] theorem candidates_from_loop_spec (tail out : alloc.vec.Vec frontend.types.ProjRecOwner) :
    LSP (frontend.proj_rec.proj_rec_candidates_from_loop tail out (alloc.vec.Vec.len tail) 0#usize)
      (fun r => absProjRecOwnerL r = absProjRecOwnerL out ++ absProjRecOwnerL tail) := by
  intro r h
  have := candidates_from_loop_val tail _ out 0#usize r rfl h
  simpa [absProjRecOwnerL] using this

attribute [local lockstep_inline] frontend.proj_rec.proj_rec_candidate_at
  frontend.proj_rec.proj_rec_candidate_rec

theorem absProjTypeRecLFrom_nil (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool))
    (i : Std.Usize) (hi : v.val.length ≤ i.val) : absProjTypeRecLFrom v i = [] := by
  simp only [absProjTypeRecLFrom]; rw [List.drop_eq_nil_of_le hi]; rfl

theorem absProjTypeRecLFrom_cons (v : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool))
    (i : Std.Usize) (hi : i.val < v.val.length) :
    absProjTypeRecLFrom v i = absProjTypeRec v.val[i.val] ::
      (v.val.drop (i.val + 1)).map absProjTypeRec := by
  simp only [absProjTypeRecLFrom]; rw [List.drop_eq_getElem_cons hi]; rfl

/- **`ls_subst_bne`**: a port test `x != c` it failed (`¬(x != c) = true`, `x` a
local) is `x = c`; substituted, the twin's tests on `x` fold (the tag
correspondences are `lockstep_simp`).  Found by its shape, not `‹…›`, whose
`assumption` unfolds every hypothesis. -/
open Lean Elab Tactic Meta in
elab "ls_subst_bne" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isAppOfArity ``Not 1 do continue
    let e := t.appArg!
    unless e.isAppOfArity ``Eq 3 && (e.getArg! 2).isConstOf ``Bool.true do continue
    let b := e.getArg! 1
    unless b.isAppOfArity ``bne 4 && (b.getArg! 2).isFVar do continue
    let stx ← Term.exprToSyntax (mkFVar d.fvarId)
    evalTactic (← `(tactic| (have h := $stx
                             simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
                             subst h)))
    return
  throwError "ls_subst_bne: no failed `!=` test on a local"

/- **`ls_view_sort`**: the twin's `view h` where the port read `view_sort` under
a tag test it passed (`Idx.tag h = absU32 ETAG_SORT` in context):
`LS.twin_view_sort`. -/
open Lean Elab Tactic Meta in
elab "ls_view_sort" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isAppOfArity ``Eq 3 do continue
    let r := t.getArg! 2
    unless r.isAppOfArity ``ConRon.Refine2.absU32 1 && (r.getArg! 0).isConstOf ``arena.handle.ETAG_SORT do
      continue
    let stx ← Term.exprToSyntax (mkFVar d.fvarId)
    evalTactic (← `(tactic| apply Lockstep.LS.twin_view_sort (by rw [$stx:term, etag_sort_abs])))
    return
  throwError "ls_view_sort: no sort tag fact"

/- **`ls_ctor_record`**: the twin's `findCtorRec` answer, cased on by the zip
(`(some j).bind (fun j => (absProjCtorRecL ctors)[j]?) = some v`), is the
port's `ctors[j]`: substituted, and that record split into its fields. -/
open Lean Elab Tactic Meta in
elab "ls_ctor_record" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isAppOfArity ``Eq 3 do continue
    let l := t.getArg! 1
    let r := t.getArg! 2
    unless l.isAppOfArity ``Option.bind 4 && r.isAppOfArity ``Option.some 2 do continue
    let s := l.getArg! 2
    unless s.isAppOfArity ``Option.some 2 do continue
    let some cl := (l.getArg! 3).find? fun e => e.isAppOfArity ``absProjCtorRecL 1 | continue
    let cs ← Term.exprToSyntax (cl.getArg! 0)
    let j := s.getArg! 1
    let v := r.getArg! 1
    unless j.isFVar && v.isFVar do continue
    let hs ← Term.exprToSyntax (mkFVar d.fvarId)
    let js ← Term.exprToSyntax j
    evalTactic (← `(tactic| (
      have hd := $hs
      have hjb : ($js).val < ($cs).val.length := by
        have := congrArg Option.isSome hd
        simpa [absProjCtorRecL] using this
      simp only [Option.bind_some, absProjCtorRecL, List.getElem?_map,
        List.getElem?_eq_getElem hjb, Option.map_some, Option.some.injEq] at hd
      subst hd
      generalize ($cs).val[($js).val]'hjb = rc
      rcases rc with ⟨c1, nf1, e1⟩
      dsimp only [absProjCtorRec])))
    return
  throwError "ls_ctor_record: none"

-- the zip's many small steps over the census's four branches exceed the default budget
set_option maxHeartbeats 1000000 in
open ConRon.Refine2.Lockstep in
theorem proj_rec_candidates_from_aux (fuel : Nat) (N : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx))
      (recs : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
        arena.handle.EIdx × Std.U64 × Std.U64))
      (types : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
        arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool))
      (i : Std.Usize),
      types.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absProjRecOwnerL a)
        (frontend.proj_rec.proj_rec_candidates_from pers st ctors recs types i) lst
        (projRecCandidates fuel (absProjCtorRecL ctors) (absProjRecRecL recs)
          (absProjTypeRecLFrom types i)) := by
  induction N with
  | zero =>
    intro pers st lst ctors recs types i hn hrel hinv
    rw [frontend.proj_rec.proj_rec_candidates_from, absProjTypeRecLFrom_nil types i (by omega),
      projRecCandidates, if_pos (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro pers st lst ctors recs types i hn hrel hinv
    have hi : i.val < types.val.length := by omega
    rw [frontend.proj_rec.proj_rec_candidates_from, absProjTypeRecLFrom_cons types i hi,
      if_neg (by scalar_tac)]
    rw [vec_index_ok_eq types i hi]
    simp only [bind_tc_ok]
    rcases hx : types.val[i.val] with ⟨tn, lps, tty, nP, nI, cs, isRec⟩
    simp only [hx, absProjTypeRec, projRecCandidates]
    by_cases hl : cs.val.length = 1
    · obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hl
      have hcs : List.map absNIdx cs.val = [absNIdx c0] := by simp [hc0]
      have hidx0 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) cs 0#usize
          = ok c0 := by
        rw [vec_index_ok_eq cs 0#usize (by simp [hc0])]; simp [hc0]
      simp only [hcs]
      have hidxL : Lockstep.LSP (alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice arena.handle.NIdx) cs 0#usize)
          (fun x => x = c0) := fun x hx => by rw [hidx0] at hx; exact (Result.ok_injective hx).symm
      -- The zip, with this proof's own moves: a failed `!=` test substituted,
      -- the sort view.  It
      -- stops at the port's reads of the records `find_rec_rec` / `find_ctor_rec`
      -- located (`recs[j1]`, `ctors[jc]`), which the twin cased on: each is
      -- substituted and split into its fields, and the zip goes on.
      repeat' (first | ls_subst_bne | ls_view_sort | lockstep_step)
      all_goals
        rename_i j1 _ _ w _ hd
        simp only [Option.bind_some, absProjRecRecL, List.getElem?_map,
          List.getElem?_eq_getElem w, Option.map_some, Option.some.injEq] at hd
        subst hd
        generalize recs.val[j1.val]'w = rr
        rcases rr with ⟨n3, v4, e, i1, i2⟩
        dsimp only [absProjRecRec]
        repeat' (first | ls_subst_bne | lockstep_step)
      all_goals
        ls_ctor_record
        repeat' (first | ls_subst_bne | lockstep_step)
    · lockstep
      all_goals
        split
        · rename_i heq
          exact absurd (by simpa using congrArg List.length heq) hl
        · lockstep

open ConRon.Refine2.Lockstep in
@[lockstep] theorem proj_rec_candidates_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Nat)
    (ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx))
    (recs : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64))
    (types : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool)) :
    LS pers (fun a b => b = absProjRecOwnerL a)
      (frontend.proj_rec.proj_rec_candidates pers st ctors recs types) lst
      (projRecCandidates fuel (absProjCtorRecL ctors) (absProjRecRecL recs)
        (absProjTypeRecL types)) := by
  have := proj_rec_candidates_from_aux fuel _ ctors recs types 0#usize rfl hrel hinv
  rw [frontend.proj_rec.proj_rec_candidates]
  simpa [absProjTypeRecLFrom, absProjTypeRecL] using this

open ConRon.Refine2.Lockstep in
@[lockstep] theorem type_names_spec
    (types : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool)) :
    LSP (frontend.proj_rec.type_names types)
      (fun v => absNIdxL v = (absProjTypeRecL types).map (·.1)) :=
  fun _ h => type_names_refines h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem any_is_rec_spec
    (types : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool)) :
    LSP (frontend.proj_rec.any_is_rec types)
      (fun v => v = (absProjTypeRecL types).any (·.2.2.2.2.2.2)) :=
  fun _ h => any_is_rec_refines h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem declared_num_params_spec
    (types : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool)) :
    LSP (frontend.proj_rec.declared_num_params types)
      (fun v => absU v = (((absProjTypeRecL types).head?).map (·.2.2.2.1)).getD 0) :=
  fun _ h => declared_num_params_refines h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem struct_parts_core_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = Option.map absStructParts a)
      (arena.inductives.struct_parts.struct_parts_core pers st block) lst
      (structPartsCore? (absICIL block)) :=
  LS.ofSim₀ fun _ h => struct_parts_core_refines hrel hinv h

open ConRon.Refine2.Lockstep in
@[lockstep] theorem native_parts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n_pd : Std.U64) (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = Option.map absNativeParts a)
      (arena.inductives.native_parts.native_parts pers st n_pd block) lst
      (nativeParts? (absU n_pd) (absICIL block)) :=
  LS.ofSim₀ fun _ h => native_parts_refines hrel hinv h

/- The twin's `direct && !recursive` once the port has fixed `recursive`:
Boolean constant folding on the twin side (an extension of `lockstep_simp`,
local to the census). -/
attribute [local lockstep_simp] Bool.true_or Bool.false_or Bool.not_true Bool.not_false
  Bool.and_false Bool.and_true

open ConRon.Refine2.Lockstep in
/-- **`proj_rec_owners` refines `projRecOwners`** (`ProjRec.lean:498-517`) —
the owner census; the port's `proj_rec_owners_guard` (called on a non-empty
candidate list only, which is where the twin runs its guard) inline. -/
@[lockstep] theorem proj_rec_owners_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (block : alloc.vec.Vec arena.env.IConstantInfo)
    (types : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64 × (alloc.vec.Vec arena.handle.NIdx) × Bool))
    (ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx))
    (recs : alloc.vec.Vec (arena.handle.NIdx × (alloc.vec.Vec arena.handle.NIdx) ×
      arena.handle.EIdx × Std.U64 × Std.U64)) :
    LS pers (fun a b => b = absProjRecOwnerL a)
      (frontend.proj_rec.proj_rec_owners pers st fuel block types ctors recs) lst
      (projRecOwners (absU fuel) (absICIL block) (absProjTypeRecL types)
        (absProjCtorRecL ctors) (absProjRecRecL recs)) := by
  rw [frontend.proj_rec.proj_rec_owners, projRecOwners]
  refine LS.bind (proj_rec_candidates_ls hrel hinv (absU fuel) ctors recs types) rfl
    (fun _ _ => by lockstep_errarm) (fun a b st1 lst1 hR hrel1 hinv1 => ?_)
  subst hR
  by_cases hnil : a.val = []
  · have : absProjRecOwnerL a = [] := by simp [absProjRecOwnerL, hnil]
    have hl0 : (alloc.vec.Vec.len a).val = 0 := by simp [hnil]
    rw [this]
    lockstep
  · obtain ⟨o0, os, hos⟩ := List.exists_cons_of_ne_nil hnil
    have : absProjRecOwnerL a = absProjRecOwner o0 :: os.map absProjRecOwner := by
      simp [absProjRecOwnerL, hos]
    have hl0 : (alloc.vec.Vec.len a).val ≠ 0 := by simp [hos]
    rw [this]
    simp only [frontend.proj_rec.proj_rec_owners_guard]
    rw [← this]
    -- a port branch its own `false` rules out closes at once (the zip would
    -- otherwise walk it against the twin's other arm); the twin's `direct &&
    -- !recursive` folds by the local Boolean `lockstep_simp` above
    repeat' (first | exact absurd ‹false = true› Bool.false_ne_true | lockstep_step)

/-- **`proj_rec_owners` refines `projRecOwners`** (`ProjRec.lean:498-517`) —
the owner census, and one of the tier's named deliverables. -/
theorem proj_rec_owners_refines {pers rst lst fuel block types ctors recs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_owners pers rst fuel block types ctors recs
      = ok o) :
    Sim₀ absProjRecOwnerL pers lst o
      (projRecOwners (absU fuel) (absICIL block) (absProjTypeRecL types)
        (absProjCtorRecL ctors) (absProjRecRecL recs)) :=
  Lockstep.LS.toSim₀ (proj_rec_owners_ls hrel hinv fuel block types ctors recs) h

#print axioms mk_lams_ls
#print axioms proj_rec_value_refines
#print axioms build_binders_refines
#print axioms mk_proj_minor_refines
end ConRon.Refine2.Frontend
