/-
# `ConRon.Refine2.Inv` — the Rust-side invariant of the arena state

**Deliverable 1 of task #97 P5, part 2.**  What the Rust state must satisfy
for a refinement lemma to say anything: the `ron::hashmap2` table invariant
on each of the eighteen cons tables and the twenty-seven memo and cache
tables, the key restriction `KeysOk` that makes their `Eq2` dictionary exact,
and nothing else — see `Refine2/AbsStore.lean`'s note on why the capacity
invariant round 2 predicted is not among them.

## The two per-key-type obligations

`Refine/HashMap2.lean`'s operations are stated against two hypotheses about
the port's own dictionaries, and this file discharges both once per key type:

* **`Eq2Fwd Eq2Inst P`** — "`eq2` never lies about `P`-keys".  Fourteen of the
  eighteen node records are handles and scalars through and through, so their
  `eq2` is a chain of `u32`/`u64` comparisons and `P` is `True`.  The other
  four carry a value with a CACHED WORD beside it (`StrNode`'s code points,
  `ListNode`'s handle vector, `LitNode`'s `Literal`, `BMNode`'s `PropWhen`)
  and go through `kernel::name::str_eq`, `arena::store::lidx_vec_eq`,
  `kernel::expr::literal_beq` and `kernel::prop_when::beq`, whose exactness
  is `Refine/{Name,Expr,PropWhen}.lean`'s and holds on well-formed values
  only — which is exactly what `RelOn P` was built for.
* **`DupId DupInst`** — "`dup2` is the identity".  On a handle it is
  `ok self`, so all five are `rfl`-level.
-/
import ConRon.Refine2.AbsStore

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (StrWF LiteralWF PropWhenWF)
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun)

/-! ## `Eq2Fwd` from a decision equivalence

Every `eq2` below is read the same way: it returns `true` exactly on equal
records.  `Eq2Fwd`'s conclusion is `c = decide (a = b)`, which that
equivalence gives in two lines — stated once here rather than at each of the
eighteen. -/

theorem eq2Fwd_of_iff {K : Type} [DecidableEq K] {I : ron.hashmap.Eq2 K}
    {P : K → Prop}
    (h : ∀ a b c, P a → P b → I.eq2 a b = ok c → (c = true ↔ a = b)) :
    Eq2Fwd I P := by
  intro a b c ha hb hc
  have hi := h a b c ha hb hc
  by_cases hab : a = b
  · rw [hi.mpr hab, decide_eq_true hab]
  · have hcf : c = false := by
      cases c with
      | false => rfl
      | true => exact absurd (hi.mp rfl) hab
    rw [hcf, decide_eq_false hab]

/-! ### The fourteen handle-and-scalar records

`eq2` is a chain of `u32`/`u64` comparisons and the record is determined by
its fields, so each is the helper above after the two records are taken apart
— one `simp only` on the generated `eq2` and one `grind`, fourteen times. -/

theorem anon_eq2 :
    Eq2Fwd arena.store.AnonNode.Insts.Con_ron_coreRonHashmapEq2 AnonNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  simp only [arena.store.AnonNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem str_eq2 :
    Eq2Fwd arena.store.StrNode.Insts.Con_ron_coreRonHashmapEq2 StrNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w⟩, s⟩ := a; obtain ⟨⟨w'⟩, s'⟩ := b
  simp only [arena.store.StrNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  split at h
  · rename_i hw
    subst hw
    constructor
    · intro hc
      subst hc
      simp [ConRon.Refine.Name.str_eq_eq h]
    · intro he
      have hs : s = s' := by
        have := (arena.store.StrNode.mk.injEq _ _ _ _).mp he
        exact this.2
      subst hs
      rw [ConRon.Refine.Name.str_eq_refl] at h
      simpa using h.symm
  · rename_i hw
    simp only [Result.ok.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    intro he
    exact hw ((arena.handle.NIdx.mk.injEq _ _).mp
      ((arena.store.StrNode.mk.injEq _ _ _ _).mp he).1)

theorem num_eq2 :
    Eq2Fwd arena.store.NumNode.Insts.Con_ron_coreRonHashmapEq2 NumNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨pw⟩, n⟩ := a; obtain ⟨⟨pw'⟩, n'⟩ := b
  simp only [arena.store.NumNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem zero_eq2 :
    Eq2Fwd arena.store.ZeroNode.Insts.Con_ron_coreRonHashmapEq2 ZeroNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  simp only [arena.store.ZeroNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem succ_eq2 :
    Eq2Fwd arena.store.SuccNode.Insts.Con_ron_coreRonHashmapEq2 SuccNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w⟩⟩ := a; obtain ⟨⟨w'⟩⟩ := b
  simp only [arena.store.SuccNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem binl_eq2 :
    Eq2Fwd arena.store.BinLNode.Insts.Con_ron_coreRonHashmapEq2 BinLNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, ⟨w4⟩⟩ := b
  simp only [arena.store.BinLNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem param_eq2 :
    Eq2Fwd arena.store.ParamNode.Insts.Con_ron_coreRonHashmapEq2 ParamNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w⟩⟩ := a; obtain ⟨⟨w'⟩⟩ := b
  simp only [arena.store.ParamNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem bvar_eq2 :
    Eq2Fwd arena.store.BVarNode.Insts.Con_ron_coreRonHashmapEq2 BVarNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨i⟩ := a; obtain ⟨i'⟩ := b
  simp only [arena.store.BVarNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem fvar_eq2 :
    Eq2Fwd arena.store.FVarNode.Insts.Con_ron_coreRonHashmapEq2 FVarNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨i, ⟨w⟩⟩ := a; obtain ⟨i', ⟨w'⟩⟩ := b
  simp only [arena.store.FVarNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem sort_eq2 :
    Eq2Fwd arena.store.SortNode.Insts.Con_ron_coreRonHashmapEq2 SortNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w⟩⟩ := a; obtain ⟨⟨w'⟩⟩ := b
  simp only [arena.store.SortNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem const_eq2 :
    Eq2Fwd arena.store.ConstNode.Insts.Con_ron_coreRonHashmapEq2 ConstNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, ⟨w4⟩⟩ := b
  simp only [arena.store.ConstNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem app_eq2 :
    Eq2Fwd arena.store.AppNode.Insts.Con_ron_coreRonHashmapEq2 AppNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, ⟨w4⟩⟩ := b
  simp only [arena.store.AppNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem bind_eq2 :
    Eq2Fwd arena.store.BindNode.Insts.Con_ron_coreRonHashmapEq2 BindNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩, ⟨w3⟩⟩ := a; obtain ⟨⟨w4⟩, ⟨w5⟩, ⟨w6⟩⟩ := b
  simp only [arena.store.BindNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem let_eq2 :
    Eq2Fwd arena.store.LetNode.Insts.Con_ron_coreRonHashmapEq2 LetNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩, ⟨w3⟩⟩ := a; obtain ⟨⟨w4⟩, ⟨w5⟩, ⟨w6⟩⟩ := b
  simp only [arena.store.LetNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem proj_eq2 :
    Eq2Fwd arena.store.ProjNode.Insts.Con_ron_coreRonHashmapEq2 ProjNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, i, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, i', ⟨w4⟩⟩ := b
  simp only [arena.store.ProjNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

/-! ### The two records that carry a cached word

`LitNode`'s `Literal` and `BMNode`'s `PropWhen` both hold a hash beside the
value, so `literal_beq`/`prop_when::beq` decide equality of the ABSTRACTED
value and `Refine/Expr.lean`'s `absLiteral_inj` / `Refine/PropWhen.lean`'s
`absPropWhen_injective` turn that into equality of the record — under the WF
predicate, which is why `TblRel` is `RelOn` and not `Rel`. -/

theorem lit_eq2 :
    Eq2Fwd arena.store.LitNode.Insts.Con_ron_coreRonHashmapEq2 LitNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c ha hb h
  obtain ⟨la⟩ := a; obtain ⟨lb⟩ := b
  simp only [arena.store.LitNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [ConRon.Refine.Expr.literal_beq_refines ha hb h]
  constructor
  · intro hc
    have hl := ConRon.Refine.Expr.absLiteral_inj ha hb (of_decide_eq_true hc)
    simpa using hl
  · intro he
    have hl : la = lb := ((arena.store.LitNode.mk.injEq _ _).mp he)
    simp [hl]

theorem bm_eq2 :
    Eq2Fwd arena.store.BMNode.Insts.Con_ron_coreRonHashmapEq2 BMNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c ha hb h
  obtain ⟨pa⟩ := a; obtain ⟨pb⟩ := b
  simp only [arena.store.BMNode.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [ConRon.Refine.PropWhen.beq_iff (ConRon.Refine.PropWhen.wf_shape ha)
    (ConRon.Refine.PropWhen.wf_shape hb) h]
  constructor
  · intro hc
    have hp := ConRon.Refine.PropWhen.absPropWhen_injective ha hb hc
    simpa using hp
  · intro he
    have hp : pa = pb := ((arena.store.BMNode.mk.injEq _ _).mp he)
    simp [hp]

/-! ### `ListNode`: the handle vector compared element by element

`arena::store::lidx_vec_eq` is the one `eq2` that walks a `Vec`, so it is the
one that needs an induction rather than a `grind`: the length test, then
`lidx_vec_eq_from`'s cursor recursion, which is `List.drop` at the cursor on
both sides.  The measure is the `Vec`'s own length, as every index recursion
of the tier is (`Refine/Scalars.lean`'s note). -/

theorem lidx_vec_eq_from_iff {a b : alloc.vec.Vec arena.handle.LIdx}
    (hlen : a.val.length = b.val.length) :
    ∀ (k : Nat) (i : Std.Usize) (c : Bool), a.val.length ≤ i.val + k →
      arena.store.lidx_vec_eq_from a b i = ok c →
      (c = true ↔ a.val.drop i.val = b.val.drop i.val) := by
  intro k
  induction k with
  | zero =>
    intro i c hk h
    rw [arena.store.lidx_vec_eq_from.eq_def] at h
    simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac), Result.ok.injEq] at h
    subst h
    have h1 : a.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    have h2 : b.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [h1, h2]
  | succ k ih =>
    intro i c hk h
    rw [arena.store.lidx_vec_eq_from.eq_def] at h
    simp only [] at h
    by_cases hp : i.val ≥ a.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac), Result.ok.injEq] at h
      subst h
      have h1 : a.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
      have h2 : b.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
      simp [h1, h2]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
      have hai : i.val < a.val.length := by omega
      have hbi : i.val < b.val.length := by omega
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := a.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := ConRon.Refine.usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec a i hai)
      obtain ⟨z, hz, hzv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b i hbi)
      subst hyv; subst hzv
      simp only [alloc.vec.Vec.index_slice_index, ConRon.Refine.bind_eq_ok_iff,
        hy, hz, hw, Result.ok.injEq, exists_eq_left'] at h
      split at h
      · rename_i hwe
        have hel : a.val[i.val] = b.val[i.val] := by
          cases hea : a.val[i.val] with
          | mk wa =>
            cases heb : b.val[i.val] with
            | mk wb =>
              rw [hea, heb] at hwe
              simpa using hwe
        simp only [bind_tc_ok] at h
        have hih := ih w c (by omega) h
        rw [hwv] at hih
        rw [hih]
        constructor
        · intro hd
          rw [List.drop_eq_getElem_cons hai, List.drop_eq_getElem_cons hbi, hel, hd]
        · intro hd
          rw [List.drop_eq_getElem_cons hai, List.drop_eq_getElem_cons hbi] at hd
          exact ((List.cons.injEq _ _ _ _).mp hd).2
      · rename_i hwe
        simp only [Result.ok.injEq] at h
        subst h
        have hne : a.val[i.val] ≠ b.val[i.val] := by
          intro hc; exact hwe (by rw [hc])
        simp only [Bool.false_eq_true, false_iff]
        intro hd
        rw [List.drop_eq_getElem_cons hai, List.drop_eq_getElem_cons hbi] at hd
        exact hne ((List.cons.injEq _ _ _ _).mp hd).1

theorem list_eq2 :
    Eq2Fwd arena.store.ListNode.Insts.Con_ron_coreRonHashmapEq2 ListNodeWF := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨ua⟩ := a; obtain ⟨ub⟩ := b
  simp only [arena.store.ListNode.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.store.lidx_vec_eq] at h
  split at h
  · rename_i hne
    simp only [Result.ok.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    intro he
    have hu : ua = ub := (arena.store.ListNode.mk.injEq _ _).mp he
    rw [hu] at hne
    simp at hne
  · rename_i heq
    have hlen : ua.val.length = ub.val.length := by scalar_tac
    have hz0 : ((0#usize : Std.Usize)).val = 0 := by simp
    have hih := lidx_vec_eq_from_iff hlen ua.val.length 0#usize c (by simp [hz0]) h
    rw [hz0, List.drop_zero, List.drop_zero] at hih
    rw [hih]
    constructor
    · intro hu
      have : ua = ub := alloc.vec.Vec.ext _ _ hu
      simp [this]
    · intro he
      have hu : ua = ub := (arena.store.ListNode.mk.injEq _ _).mp he
      rw [hu]

/-! ## `dup2` is the identity, on all five handle kinds and on the records -/

theorem dupId_eidx : DupId arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

theorem dupId_nidx : DupId arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

theorem dupId_lidx : DupId arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

theorem dupId_lsidx : DupId arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

theorem dupId_bmidx : DupId arena.handle.BMIdx.Insts.Con_ron_coreRonHashmapDup := by
  intro a b h; exact (Result.ok_injective h).symm

/-! ## One table, and one tier

`TblInv` is `Refine/HashMap2.lean`'s `Inv` on the cons table plus the key
restriction; `TblRel` (`Refine2/AbsStore.lean`) is the abstraction.  The two
are apart for the reason `RefineOld/State.lean` kept `StateRel` and `StateWF`
apart: a refinement lemma's hypothesis is the pair, and its conclusion
re-establishes the pair, but the two say different things and are proved by
different lemmas. -/

structure TblInv {A I D : Type} [DecidableEq A] (hA : ron.hashmap.Hashable A)
    (P : A → Prop) (rt : arena.store.Tbl A I D) : Prop where
  inv : Inv hA rt.cons
  keys : KeysOk P rt.cons
  /-- **Every record in the NODE column is well formed too** (task #97-P5-2).
  `keys` says it of the cons table; this says it of the array, and the two
  are separate because `Tbl.node` reads the array and not the table.  It is
  what the binder datum's `hasParams` needs: `prop_when::has_params` refines
  `PropWhen.hasParams` only on a `WFShape` value (`Refine/PropWhen.lean`'s
  `has_params_shape`), and that bit is OBSERVED — it is `derOfBind`'s `pm`,
  hence the parent word's `lpOfData`.  `push` re-establishes it from the
  caller's own `P a`, so it costs one line per writing lemma. -/
  nodesP : ∀ p ∈ rt.rows.val, P p.1

structure NTablesInv (rt : arena.store.NTables) : Prop where
  anons : TblInv arena.store.AnonNode.Insts.Con_ron_coreRonHashmapHashable
    AnonNodeWF rt.anons
  strs : TblInv arena.store.StrNode.Insts.Con_ron_coreRonHashmapHashable
    StrNodeWF rt.strs
  nums : TblInv arena.store.NumNode.Insts.Con_ron_coreRonHashmapHashable
    NumNodeWF rt.nums

structure LTablesInv (rt : arena.store.LTables) : Prop where
  zeros : TblInv arena.store.ZeroNode.Insts.Con_ron_coreRonHashmapHashable
    ZeroNodeWF rt.zeros
  succs : TblInv arena.store.SuccNode.Insts.Con_ron_coreRonHashmapHashable
    SuccNodeWF rt.succs
  maxs : TblInv arena.store.BinLNode.Insts.Con_ron_coreRonHashmapHashable
    BinLNodeWF rt.maxs
  imaxs : TblInv arena.store.BinLNode.Insts.Con_ron_coreRonHashmapHashable
    BinLNodeWF rt.imaxs
  params : TblInv arena.store.ParamNode.Insts.Con_ron_coreRonHashmapHashable
    ParamNodeWF rt.params

structure LsTablesInv (rt : arena.store.LsTables) : Prop where
  lists : TblInv arena.store.ListNode.Insts.Con_ron_coreRonHashmapHashable
    ListNodeWF rt.lists

structure ETablesInv (rt : arena.store.ETables) : Prop where
  bvars : TblInv arena.store.BVarNode.Insts.Con_ron_coreRonHashmapHashable
    BVarNodeWF rt.bvars
  fvars : TblInv arena.store.FVarNode.Insts.Con_ron_coreRonHashmapHashable
    FVarNodeWF rt.fvars
  sorts : TblInv arena.store.SortNode.Insts.Con_ron_coreRonHashmapHashable
    SortNodeWF rt.sorts
  consts : TblInv arena.store.ConstNode.Insts.Con_ron_coreRonHashmapHashable
    ConstNodeWF rt.consts
  apps : TblInv arena.store.AppNode.Insts.Con_ron_coreRonHashmapHashable
    AppNodeWF rt.apps
  lams : TblInv arena.store.BindNode.Insts.Con_ron_coreRonHashmapHashable
    BindNodeWF rt.lams
  foralls : TblInv arena.store.BindNode.Insts.Con_ron_coreRonHashmapHashable
    BindNodeWF rt.foralls
  lets : TblInv arena.store.LetNode.Insts.Con_ron_coreRonHashmapHashable
    LetNodeWF rt.lets
  lits : TblInv arena.store.LitNode.Insts.Con_ron_coreRonHashmapHashable
    LitNodeWF rt.lits
  projs : TblInv arena.store.ProjNode.Insts.Con_ron_coreRonHashmapHashable
    ProjNodeWF rt.projs
  bms : TblInv arena.store.BMNode.Insts.Con_ron_coreRonHashmapHashable
    BMNodeWF rt.bms

/-! ## The four stores, and the persistent tier

The tier the persistent reads actually go to is `Refine2/AbsStore.lean`'s
`rPersE` and its three siblings, so the invariant is stated on that and not on
the store's own `pers` field: what a read consults is what must be well
formed.

**`frz` — a store read through a frozen tier is scratch-on** (task
#98-FREEZE).  A frozen store — the only kind the Rust reads through a frozen
tier (`freeze` hands the tier out and turns the scratch tier on; a worker's
store is built frozen) — has its scratch tier on, so an ordinary intern
appends to the scratch tier; with the scratch tier off, the reader is the
empty stand-in and the intern appends to the store's OWN tables, which is what
the relation's persistent arm then reads.  Only the implication is carried:
the promotion's view of a frozen store as an owned one read through a
stand-in (`Refine2/Promote/Glue.lean`) has its scratch tier on.  Because the
reader is fixed for a whole bracket or worker and every step keeps the
scratch flag, the lockstep proofs carry it for free.  A representation fact
about the Rust state and its reader. -/

structure NStoreInv (pers : arena.store.PersTier) (rs : arena.store.NStore) :
    Prop where
  perst : NTablesInv (rPersN pers rs)
  scrt : NTablesInv rs.scr
  frz : pers.frozen = true → rs.scratch_on = true

structure LStoreInv (pers : arena.store.PersTier) (rs : arena.store.LStore) :
    Prop where
  ns : NStoreInv pers rs.ns
  perst : LTablesInv (rPersL pers rs)
  scrt : LTablesInv rs.scr
  frz : pers.frozen = true → rs.scratch_on = true

structure LsStoreInv (pers : arena.store.PersTier) (rs : arena.store.LsStore) :
    Prop where
  lvl : LStoreInv pers rs.ls
  perst : LsTablesInv (rPersLs pers rs)
  scrt : LsTablesInv rs.scr
  frz : pers.frozen = true → rs.scratch_on = true

/-- The Rust-side invariant of the whole arena. -/
structure StoreInv (pers : arena.store.PersTier) (rs : arena.store.EStore) :
    Prop where
  lss : LsStoreInv pers rs.lss
  perst : ETablesInv (rPersE pers rs)
  scrt : ETablesInv rs.scr
  frz : pers.frozen = true → rs.scratch_on = true

/-! ### The relation and the invariant at another tier with the same tables

A promotion grows ONE table of the tier (task #98-FREEZE); the stores that
read the other three are related, and well formed, exactly as before. -/

theorem NStoreRel.tier_congr {p p' : arena.store.PersTier} {rs ls}
    (h : NStoreRel p rs ls) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n) :
    NStoreRel p' rs ls :=
  ⟨by unfold rPersN; rw [hf, hn]; exact h.perst, h.scrt, h.scratchOn⟩

theorem LStoreRel.tier_congr {p p' : arena.store.PersTier} {rs ls}
    (h : LStoreRel p rs ls) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n)
    (hl : p'.l = p.l) : LStoreRel p' rs ls :=
  ⟨h.ns.tier_congr hf hn, by unfold rPersL; rw [hf, hl]; exact h.perst, h.scrt,
    h.scratchOn⟩

theorem LsStoreRel.tier_congr {p p' : arena.store.PersTier} {rs ls}
    (h : LsStoreRel p rs ls) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n)
    (hl : p'.l = p.l) (hls : p'.ls = p.ls) : LsStoreRel p' rs ls :=
  ⟨h.lvl.tier_congr hf hn hl, by unfold rPersLs; rw [hf, hls]; exact h.perst, h.scrt,
    h.scratchOn⟩

theorem StoreRel.tier_congr {p p' : arena.store.PersTier} {rs ls}
    (h : StoreRel p rs ls) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n)
    (hl : p'.l = p.l) (hls : p'.ls = p.ls) (he : p'.e = p.e) : StoreRel p' rs ls :=
  ⟨h.lss.tier_congr hf hn hl hls, by unfold rPersE; rw [hf, he]; exact h.perst, h.scrt,
    h.scratchOn⟩

theorem NStoreInv.tier_congr {p p' : arena.store.PersTier} {rs}
    (h : NStoreInv p rs) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n) :
    NStoreInv p' rs :=
  ⟨by unfold rPersN; rw [hf, hn]; exact h.perst, h.scrt, by rw [hf]; exact h.frz⟩

theorem LStoreInv.tier_congr {p p' : arena.store.PersTier} {rs}
    (h : LStoreInv p rs) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n)
    (hl : p'.l = p.l) : LStoreInv p' rs :=
  ⟨h.ns.tier_congr hf hn, by unfold rPersL; rw [hf, hl]; exact h.perst, h.scrt,
    by rw [hf]; exact h.frz⟩

theorem LsStoreInv.tier_congr {p p' : arena.store.PersTier} {rs}
    (h : LsStoreInv p rs) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n)
    (hl : p'.l = p.l) (hls : p'.ls = p.ls) : LsStoreInv p' rs :=
  ⟨h.lvl.tier_congr hf hn hl, by unfold rPersLs; rw [hf, hls]; exact h.perst, h.scrt,
    by rw [hf]; exact h.frz⟩

theorem StoreInv.tier_congr {p p' : arena.store.PersTier} {rs}
    (h : StoreInv p rs) (hf : p'.frozen = p.frozen) (hn : p'.n = p.n)
    (hl : p'.l = p.l) (hls : p'.ls = p.ls) (he : p'.e = p.e) : StoreInv p' rs :=
  ⟨h.lss.tier_congr hf hn hl hls, by unfold rPersE; rw [hf, he]; exact h.perst, h.scrt,
    by rw [hf]; exact h.frz⟩

set_option hygiene false in
/-- **The `frz` field of a rebuilt store invariant** (task #98-FREEZE): a
rebuilt store keeps the flags of the store it was rebuilt from (`hinv.frz` at
the matching depth), or sets them itself (the implication is then `rfl` or
vacuous). -/
macro "frz_tac" : tactic => `(tactic| first
  | assumption
  | exact hinv.frz | exact hinv.lss.frz | exact hinv.lss.lvl.frz | exact hinv.lss.lvl.ns.frz
  | exact hinv.lvl.frz | exact hinv.lvl.ns.frz | exact hinv.ns.frz
  | exact hinv.store.frz | exact hinv.store.lss.frz | exact hinv.store.lss.lvl.frz
  | exact hinv.store.lss.lvl.ns.frz
  | exact hinv1.frz | exact hinv1.lss.frz | exact hinv1.lss.lvl.frz | exact hinv1.lss.lvl.ns.frz
  | exact hinvS.frz | exact hinv0.frz
  | (intro hfrz; first | rfl | (simp at hfrz; done) | (simp_all; done)))

/-! ## Axiom census

The eighteen `Eq2Fwd` obligations and the `lidx_vec_eq` induction, at the
three standard axioms.  `Classical.choice` is there for the eighteen
`DecidableEq` instances of `Refine2/AbsStore.lean` (whose note says why
nothing is lost by them) and for nothing else. -/

/-- info: 'ConRon.Refine2.app_eq2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms app_eq2

/-- info: 'ConRon.Refine2.bind_eq2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bind_eq2

/-- info: 'ConRon.Refine2.lit_eq2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lit_eq2

/-- info: 'ConRon.Refine2.bm_eq2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bm_eq2

/-- info: 'ConRon.Refine2.list_eq2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms list_eq2

/-- info: 'ConRon.Refine2.str_eq2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms str_eq2


end ConRon.Refine2
