/-
# `ConRon.Refine2.Core.LS.PrimsF` — region F's primitive pairs

Task #97-P5-Core round 5, region F (the `defeq` loop).  The `@[lockstep]`
pairs the `defeq` bodies need that no other file has: the three pin reads the
literal arms test against (restated over `AStateRel₀` from
`Refine2/Checker/Pins.lean`, whose proofs read only `hrel.pins`), and the
Rust-only scalar steps of the literal and binder arms.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PF

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## The pin table, over `AStateRel₀` -/

/-- `Refine2/Checker/Pins.lean`'s `pin_at_refines`, over `AStateRel₀` (it reads
only `hrel.pins`). -/
theorem pin_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (i : Std.Usize) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_at st i) st lst (pinAt (absSz i)) := by
  intro o hrun
  rw [arena.pins.pin_at] at hrun
  have hnames := hrel.pins.names
  have hlen : lst.pins.names.size = st.pins.names.val.length := by
    have h := congrArg List.length hnames
    simpa using h
  have hrun2 : (Arena.pinAt (absSz i)).run lst
      = (if h : absSz i < lst.pins.names.size
         then Except.ok (lst.pins.names[absSz i], lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : absSz i < lst.pins.names.size
    · rw [dif_pos h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, dif_pos h]
    · rw [dif_neg h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, dif_neg h,
        Arena.fail, throwThe, MonadExceptOf.throw,
        Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hge =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 : core.result.Result.Err (T := arena.handle.NIdx)
        (kernel.core_types.CheckError.Internal cps) = o := Result.ok_injective hrun
    subst h2
    have hnl : ¬ (absSz i < lst.pins.names.size) := by
      rw [hlen]
      have hle : st.pins.names.val.length ≤ i.val := by scalar_tac
      show ¬ (i.val < st.pins.names.val.length)
      omega
    exact AErrSim.internal (s := "arena: reserved-name pins not interned")
      (by rw [hrun2, dif_neg hnl])
  case isFalse hlt =>
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : core.result.Result.Ok n1 = o := Result.ok_injective hrun
    subst h2
    rw [dupId_nidx _ _ hn1]
    obtain ⟨hlt2, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn
    have hlt3 : absSz i < lst.pins.names.size := by rw [hlen]; exact hlt2
    refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
    show (Arena.pinAt (absSz i)).run lst = _
    rw [hrun2, dif_pos hlt3]
    have hi : lst.pins.names.toList[absSz i]? =
        (st.pins.names.val.map absNIdx)[absSz i]? := by rw [hnames]
    simp only [List.getElem?_map, Array.getElem?_toList] at hi
    have hsome : lst.pins.names[absSz i]? = some (absNIdx st.pins.names.val[absSz i]) := by
      simpa [hlt2] using hi
    rw [Array.getElem?_eq_getElem hlt3] at hsome
    rw [Option.some_inj.mp hsome]

@[lockstep] theorem pin_nat_zero_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_zero st) st lst pinNatZero := by
  have h := pin_at_ls hrel hinv arena.pins.PIN_NAT_ZERO
  have hc : absSz arena.pins.PIN_NAT_ZERO = Arena.PIN_NAT_ZERO := by
    show (arena.pins.PIN_NAT_ZERO).val = _
    rw [arena.pins.PIN_NAT_ZERO]; rfl
  rw [hc] at h
  rw [arena.pins.pin_nat_zero]; exact h

@[lockstep] theorem pin_nat_succ_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_succ st) st lst pinNatSucc := by
  have h := pin_at_ls hrel hinv arena.pins.PIN_NAT_SUCC
  have hc : absSz arena.pins.PIN_NAT_SUCC = Arena.PIN_NAT_SUCC := by
    show (arena.pins.PIN_NAT_SUCC).val = _
    rw [arena.pins.PIN_NAT_SUCC]; rfl
  rw [hc] at h
  rw [arena.pins.pin_nat_succ]; exact h

@[lockstep] theorem pin_string_of_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_string_of_list st) st lst
      pinStringOfList := by
  have h := pin_at_ls hrel hinv arena.pins.PIN_STRING_OF_LIST
  have hc : absSz arena.pins.PIN_STRING_OF_LIST = Arena.PIN_STRING_OF_LIST := by
    show (arena.pins.PIN_STRING_OF_LIST).val = _
    rw [arena.pins.PIN_STRING_OF_LIST]; rfl
  rw [hc] at h
  rw [arena.pins.pin_string_of_list]; exact h

/-! ## The `const` projection -/

attribute [lockstep_simp] absConstT

/-- `arena::monad::view_const` against `Arena.viewConst` — the typed
projection a tag-guarded `view` becomes (`LS.twin_view_const`). -/
@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a) (arena.monad.view_const pers st h) st lst
      (Arena.viewConst (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewConst (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_const] at hr; exact estore_view_const_abs hrel.store hr)
    hrel hinv

/-! ## Handle equality: the port's `eq2` is the twin's `==`/`=`

Every handle kind is a word; `eq2` compares the words, and the abstraction is
injective.  The conclusions are in `decide` form, and the twin's `==` on a
handle (a `LawfulBEq`) is `decide` by `idx_beq_decide`. -/

@[lockstep_simp] theorem idx_beq_decide {k : IdxKind} (a b : Idx k) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

private theorem word_decide {k : IdxKind} {α : Type} (w : α → Std.U32)
    (A : α → Idx k) (hA : ∀ x, A x = ⟨absU32 (w x)⟩) (a b : α) :
    decide (w a = w b) = decide (A a = A b) := by
  simp only [decide_eq_decide, hA]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg Idx.word h
    exact absU32_inj this

@[lockstep] theorem eidx_eq2_ls (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absEIdx a = absEIdx b)) := by
  intro r h
  rw [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.EIdx.word absEIdx (fun _ => rfl) a b

@[lockstep] theorem nidx_eq2_ls (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absNIdx a = absNIdx b)) := by
  intro r h
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.NIdx.word absNIdx (fun _ => rfl) a b

@[lockstep] theorem lsidx_eq2_ls (a b : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absLsIdx a = absLsIdx b)) := by
  intro r h
  rw [arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.LsIdx.word absLsIdx (fun _ => rfl) a b

@[lockstep] theorem bmidx_eq2_ls (a b : arena.handle.BMIdx) :
    LSP (arena.handle.BMIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absBMIdx a = absBMIdx b)) := by
  intro r h
  rw [arena.handle.BMIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.BMIdx.word absBMIdx (fun _ => rfl) a b

/-! ## Tag tests in `bne` form

The peel tests tags with `!=` on both sides (`ta != b.tag`, `ta !=
ETAG_LAM`); these put the two in the same `decide` form. -/

@[lockstep_simp] theorem absU32_bne (x y : Std.U32) :
    (absU32 x != absU32 y) = !(decide (x = y)) := by
  by_cases h : x = y
  · subst h; simp
  · have : absU32 x ≠ absU32 y := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem u32_bne (x y : Std.U32) : (x != y) = !(decide (x = y)) := by
  by_cases h : x = y <;> simp [h]

attribute [lockstep_simp] ETag.isBind Bool.or_eq_true Bool.not_eq_true' Bool.not_true

/-! ## Spine lengths -/

@[lockstep_simp] theorem absEIdxList_length' (v : alloc.vec.Vec arena.handle.EIdx) :
    (ExprOps.absEIdxList v).length = v.val.length := by
  simp [ExprOps.absEIdxList]

@[lockstep_simp] theorem vec_len_eq_iff {α : Type} (v w : alloc.vec.Vec α) :
    (v.len = w.len) = (v.val.length = w.val.length) := by
  apply propext
  constructor
  · intro h
    have := congrArg UScalar.val h
    simpa [alloc.vec.Vec.len_val] using this
  · intro h
    apply Aeneas.Std.UScalar.eq_imp
    simpa [alloc.vec.Vec.len_val] using h

/-! ## The check mode -/

@[lockstep] theorem verified_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m) (fun r => r = (ConRon.Refine.absMode m).verifiedChecks) :=
  by
  intro r h
  cases m <;> (rw [kernel.env.verified_checks] at h; cases Result.ok_injective h; rfl)

/-! ## Interns — pending the foundation's intern slice -/

@[lockstep] theorem intern_e_fvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.U64) (ty : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_fvar pers st i ty) lst
      (Arena.internFVarE (absU i) (absEIdx ty)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

@[lockstep] theorem intern_e_lit_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (l : kernel.expr.Literal) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_lit pers st l) lst
      (Arena.internE (.lit (ConRon.Refine.absLiteral l))) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

/-! ## Literals and binder data: exact comparisons on well-formed values -/

/-- `==` at a type whose `BEq` is its `DecidableEq` (`ConLeche.Literal`,
`ConLeche.PropWhen`) is `decide`. -/
@[lockstep_simp] theorem beq_of_decEq {α : Type} [DecidableEq α] (a b : α) :
    (@BEq.beq α instBEqOfDecidableEq a b) = decide (a = b) := rfl

@[lockstep] theorem arc_deref_ls {T : Type} (A : Type) (x : alloc.sync.Arc T) :
    LSP (alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x) (fun y => y = x) :=
  fun _ h => (Result.ok_injective h).symm

@[lockstep] theorem nat_is_zero_ls (n : ron.nat.Nat) (hn : ConRon.Refine.Nat.NatWF n) :
    LSP (ron.nat.is_zero n) (fun b => b = decide (ConRon.Refine.Nat.toNat n = 0)) :=
  fun _ h => ConRon.Refine.Nat.is_zero_refines hn h

@[lockstep] theorem nat_pred_ls (n : ron.nat.Nat) (hn : ConRon.Refine.Nat.NatWF n) :
    LSP (ron.nat.pred n)
      (fun c => ConRon.Refine.Nat.NatWF c ∧
        ConRon.Refine.Nat.toNat c = ConRon.Refine.Nat.toNat n - 1) :=
  fun _ h => let r := ConRon.Refine.Nat.pred_refines hn h; ⟨r.2, r.1⟩

@[lockstep] theorem nat_clone_ls (n : ron.nat.Nat) :
    LSP (ron.nat.clone n)
      (fun m => m.limbs.val = n.limbs.val ∧
        ConRon.Refine.Nat.toNat m = ConRon.Refine.Nat.toNat n) :=
  fun _ h => ConRon.Refine.Nat.clone_refines h

theorem natWF_of_limbs {m n : ron.nat.Nat} (h : m.limbs.val = n.limbs.val)
    (hn : ConRon.Refine.Nat.NatWF n) : ConRon.Refine.Nat.NatWF m := by
  unfold ConRon.Refine.Nat.NatWF; rw [h]; exact hn

@[lockstep] theorem literal_nat_ls (k : ron.nat.Nat) :
    LSP (kernel.expr.literal_nat k) (fun l => l = .NatVal k) := by
  intro l h
  rw [kernel.expr.literal_nat, ConRon.Refine.ptr_new_eq, bind_tc_ok] at h
  exact (Result.ok_injective h).symm

@[lockstep] theorem str_copy_ls (v : alloc.vec.Vec Std.U32) :
    LSP (kernel.expr.str_copy v) (fun r => r = v) :=
  fun _ h => ConRon.Refine.Expr.str_copy_eq h

@[lockstep] theorem literal_beq_ls (a b : kernel.expr.Literal)
    (ha : ConRon.Refine.LiteralWF a) (hb : ConRon.Refine.LiteralWF b) :
    LSP (kernel.expr.literal_beq a b)
      (fun c => c = decide (ConRon.Refine.absLiteral a = ConRon.Refine.absLiteral b)) :=
  fun _ h => ConRon.Refine.Expr.literal_beq_refines ha hb h

@[lockstep] theorem prop_when_beq_ls (a b : kernel.prop_when.PropWhen)
    (ha : ConRon.Refine.PropWhenWF a) (hb : ConRon.Refine.PropWhenWF b) :
    LSP (kernel.prop_when.beq a b)
      (fun c => c = decide (ConRon.Refine.absPropWhen a = ConRon.Refine.absPropWhen b)) := by
  intro c h
  have := ConRon.Refine.PropWhen.beq_iff (ConRon.Refine.PropWhen.wf_shape ha)
    (ConRon.Refine.PropWhen.wf_shape hb) h
  cases c <;> simp_all

/-! ## What a `view` read: a well-formed node

The port's `view` returns a node whose literal payload and binder datum are
well formed (`StoreInv`'s node columns, `tbl_node_wf`).  The `defeq` arms
compare literals (`literal_beq`, `nat::is_zero`) and binder data
(`prop_when::beq`), which are exact only on well-formed values, so the
`defeq` proofs use `view_wf_ls` (a local hypothesis, tried before the global
`view_ls`), which carries `ENodeViewWF` in its relation. -/

theorem etables_get_bm_wf {rt} (hinv : ETablesInv rt) {i : arena.handle.BMIdx}
    {o : Option kernel.expr.BinderMeta}
    (h : arena.store.ETables.get_bm rt i = ok o) :
    ∀ m, o = some m → ConRon.Refine.PropWhenWF m.pw := by
  rw [arena.store.ETables.get_bm] at h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hw := tbl_node_wf hinv.bms hp
  cases hpc : p with
  | none =>
    rw [hpc] at h; intro m hm; rw [← Result.ok_injective h] at hm; simp at hm
  | some r =>
    rw [hpc] at h
    obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    intro m hm
    rw [← Result.ok_injective h] at hm
    cases Option.some.inj hm
    rw [kernel.expr.binder_meta] at hbm
    cases Result.ok_injective hbm
    show ConRon.Refine.PropWhenWF pw
    rw [ConRon.Refine.PropWhen.dup_eq hpw]
    exact hw r hpc

theorem estore_view_bm_wf {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.BMIdx}
    {o : Option kernel.expr.BinderMeta}
    (h : arena.store.EStore.view_bm rs pers i = ok o) :
    ∀ m, o = some m → ConRon.Refine.PropWhenWF m.pw := by
  rw [arena.store.EStore.view_bm] at h
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · rw [arena.store.EStore.pers_get_bm] at h
    have hp := hinv.perst
    rw [rPersE] at hp
    split at h <;> rename_i hs
    · rw [if_pos hs] at hp; exact etables_get_bm_wf hp h
    · rw [if_neg hs] at hp; exact etables_get_bm_wf hp h
  · split at h
    · exact etables_get_bm_wf hinv.scrt h
    · intro m hm; rw [← Result.ok_injective h] at hm; simp at hm

theorem etables_get_wf {rt} (hinv : ETablesInv rt) {i : arena.handle.EIdx}
    {o : Option arena.store.ENodeView}
    (h : arena.store.ETables.get rt i = ok o) :
    ∀ v, o = some v → ENodeViewWF v := by
  rw [arena.store.ETables.get] at h
  intro v hv
  repeat' (first
    | (split at h)
    | (obtain ⟨_, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h))
  all_goals (first
    | (rw [← Result.ok_injective h] at hv; simp at hv; done)
    | (rw [← Result.ok_injective h] at hv; cases Option.some.inj hv; trivial)
    | skip)
  -- the literal arm: the node column's record is well formed
  rename_i r hn _ w hd
  rw [← Result.ok_injective h] at hv
  cases Option.some.inj hv
  show ConRon.Refine.LiteralWF w
  rw [ConRon.Refine.Expr.literal_dup_eq hd]
  exact tbl_node_wf hinv.lits hn r rfl

theorem estore_view_bind_wf {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.EIdx}
    {o : Option (arena.handle.EIdx × arena.handle.EIdx × kernel.expr.BinderMeta)}
    (h : arena.store.EStore.view_bind rs pers i = ok o) :
    ∀ t, o = some t → ConRon.Refine.PropWhenWF t.2.2.pw := by
  rw [arena.store.EStore.view_bind] at h
  obtain ⟨q, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  intro t ht
  cases q with
  | none => rw [← Result.ok_injective h] at ht; simp at ht
  | some q =>
    obtain ⟨e, e1, b⟩ := q
    obtain ⟨o1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases o1 with
    | none => rw [← Result.ok_injective h] at ht; simp at ht
    | some m =>
      rw [← Result.ok_injective h] at ht
      cases Option.some.inj ht
      exact estore_view_bm_wf hinv h1 m rfl

theorem estore_view_wf {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.EIdx}
    {o : Option arena.store.ENodeView}
    (h : arena.store.EStore.view rs pers i = ok o) :
    ∀ v, o = some v → ENodeViewWF v := by
  rw [arena.store.EStore.view] at h
  obtain ⟨t, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bb, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    intro v hv
    cases q with
    | none => rw [← Result.ok_injective h] at hv; simp at hv
    | some q =>
      obtain ⟨e, e1, m⟩ := q
      have hm := estore_view_bind_wf hinv hq _ rfl
      obtain ⟨ev, hev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h] at hv
      cases Option.some.inj hv
      rw [arena.store.e_bind_view] at hev
      split at hev <;> (cases Result.ok_injective hev; exact hm)
  · obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h
    · rw [arena.store.EStore.pers_get] at h
      have hp := hinv.perst
      rw [rPersE] at hp
      split at h <;> rename_i hs
      · rw [if_pos hs] at hp; exact etables_get_wf hp h
      · rw [if_neg hs] at hp; exact etables_get_wf hp h
    · split at h
      · exact etables_get_wf hinv.scrt h
      · intro v hv; rw [← Result.ok_injective h] at hv; simp at hv

attribute [lockstep_simp] ENodeViewWF

/-- `arena::monad::view` against `Arena.view`, carrying the port's own
representation fact about what it read: the viewed node is well formed
(`StoreInv`'s node columns) — what the `defeq` arms' literal and binder-datum
comparisons need to be exact. -/
theorem view_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => ENodeViewWF a ∧ b = absENodeView a) (arena.monad.view pers st h) st lst
      (Arena.view (absEIdx h)) := by
  intro o hrun
  have hv := view_ls hrel hinv h o hrun
  cases o with
  | Err e => exact hv
  | Ok v =>
    obtain ⟨b, lst', h1, h2, h3, h4⟩ := hv
    refine ⟨b, lst', h1, ⟨?_, h2⟩, h3, h4⟩
    rw [arena.monad.view] at hrun
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases q with
    | none =>
      obtain ⟨s, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [arena.monad.fail] at hrun
      cases Result.ok_injective hrun
    | some v' =>
      cases Result.ok_injective hrun
      exact estore_view_wf hinv.store hq v rfl

end ConRon.Refine2.Lockstep.PF
