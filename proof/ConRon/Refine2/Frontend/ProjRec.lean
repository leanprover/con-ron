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

## `sorry` count in this file: 55
-/
import ConRon.Refine2.Frontend.Spec

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
    absProjRecOwner o' = absProjRecOwner o := by sorry

/-- **`cps_starts_with`** — `String.startsWith` on code points. -/
theorem cps_starts_with_refines {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32}
    {v : Bool} (h : frontend.proj_rec.cps_starts_with s lit = ok v) :
    v = (lit.val.map (fun c => c.val)).isPrefixOf (s.val.map (fun c => c.val)) := by
  sorry

/-- **`one_lidx`** — the singleton level list. -/
theorem one_lidx_refines {l v} (h : frontend.proj_rec.one_lidx l = ok v) :
    v.val.map absLIdx = [absLIdx l] := by sorry

/-- **`cons_lidx`** — the twin's `l :: us`. -/
theorem cons_lidx_refines {l us v} (h : frontend.proj_rec.cons_lidx l us = ok v) :
    v.val.map absLIdx = absLIdx l :: us.val.map absLIdx := by sorry

/-- **`append_eidx`** — the twin's `out ++ xs`. -/
theorem append_eidx_refines {out xs v}
    (h : frontend.proj_rec.append_eidx out xs = ok v) :
    absEIdxL v = absEIdxL out ++ absEIdxL xs := by sorry

/-- **`type_names`** — the block's type-former names, `types.map (·.1)`. -/
theorem type_names_refines {types v}
    (h : frontend.proj_rec.type_names types = ok v) :
    absNIdxL v = (absProjTypeRecL types).map (·.1) := by sorry

/-- **`any_is_rec`** — `types.any (·.2.2.2.2.2.2)`. -/
theorem any_is_rec_refines {types v}
    (h : frontend.proj_rec.any_is_rec types = ok v) :
    v = (absProjTypeRecL types).any (·.2.2.2.2.2.2) := by sorry

/-- **`declared_num_params`** — the first type record's parameter count, `0`
at an empty block: the twin's `(types.head?.map (·.2.2.2.1)).getD 0`. -/
theorem declared_num_params_refines {types v}
    (h : frontend.proj_rec.declared_num_params types = ok v) :
    absU v = (((absProjTypeRecL types).head?).map (·.2.2.2.1)).getD 0 := by sorry

/-- **`occurs_record`** — the visited set's insert. -/
theorem occurs_record_refines {rm ls h' m'} (hs : HSetRel rm ls)
    (h : frontend.proj_rec.occurs_record rm h' = ok m') :
    HSetRel m' (ls.insert (absEIdx h')) := by sorry

/-- **`occurs_seen`** — the visited set's probe. -/
theorem occurs_seen_refines {rm ls h' v} (hs : HSetRel rm ls)
    (h : frontend.proj_rec.occurs_seen rm h' = ok v) :
    v = ls.contains (absEIdx h') := by sorry

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

/-- **`is_proj_iota_pre`** — the port's split of the two inner `viewN`s
(extraction rule 5: the outer view's loan must be dead where the next is
taken).  No twin; stated against `isProjIotaName`'s inner test. -/
theorem is_proj_iota_pre_refines {pers rst lst p1 o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.is_proj_iota_pre pers rst p1 = ok o) :
    SimRE id lst o (do
      match ← viewN (absNIdx p1) with
      | .str p s => pure (s == "iota" && (← viewN p) matches .str _ _)
      | _ => pure false) := by sorry

/-- **`is_proj_iota_name` refines `isProjIotaName`** (`ProjRec.lean:85-97`). -/
theorem is_proj_iota_name_refines {pers rst lst n o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.is_proj_iota_name pers rst n = ok o) :
    SimRE id lst o (isProjIotaName (absNIdx n)) := by sorry

/-- **`proj_iota_level_at`** — the port's split at the resolved view of the
artifact's type (rule 5: the `.const` arm interns `Eq`). -/
theorem proj_iota_level_at_refines {pers rst lst n us o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_iota_level_at pers rst n us = ok o) :
    Sim₀ (Option.map absLIdx) pers lst o
      (do
        let eqN ← internName ConLeche.eqName
        if absNIdx n == eqN then
          pure ((← viewLs (absLsIdx us)).head?)
        else pure none) := by sorry

/-- **`proj_iota_level` refines `projIotaLevel`** (`ProjRec.lean:100-112`):
the field sort the artifact records. -/
theorem proj_iota_level_refines {pers rst lst fuel ty o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_iota_level pers rst fuel ty = ok o) :
    Sim₀ (Option.map absLIdx) pers lst o
      (projIotaLevel (absU fuel) (absEIdx ty)) := by sorry

/-! ## The occurrence test -/

/-- **`occurs_const_go` refines `occursConstGo`** (`ProjRec.lean:141-186`):
does the constant `n` occur in the DAG under `h`, each node visited once. -/
theorem occurs_const_go_refines {pers rst lst n seen ls fuel h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.proj_rec.occurs_const_go pers rst n seen fuel h' = ok o) :
    OOut lst o (occursConstGo (absNIdx n) ls (absU fuel) (absEIdx h')) := by sorry

/-- **`occurs_const_node`** — the port's split at a resolved view. -/
theorem occurs_const_node_refines {pers rst lst n seen ls fuel h' v o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.proj_rec.occurs_const_node pers rst n seen fuel h' v = ok o) :
    OOut lst o (occursConstGo (absNIdx n) ls (absU fuel + 1) (absEIdx h')) := by
  sorry

/-- **`occurs_const_two`** — the twin's four identical two-child `match`
nests, as one function. -/
theorem occurs_const_two_refines {pers rst lst n seen ls fuel h' x y o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.proj_rec.occurs_const_two pers rst n seen fuel h' x y = ok o) :
    OOut lst o (do
      let (b, s) ← occursConstGo (absNIdx n) ls (absU fuel) (absEIdx x)
      if b then pure (true, s)
      else occursConstGo (absNIdx n) s (absU fuel) (absEIdx y)) := by sorry

/-- **`occurs_const_fast` refines `occursConstFast`** (`ProjRec.lean:192-196`). -/
theorem occurs_const_fast_refines {pers rst lst fuel n h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.occurs_const_fast pers rst fuel n h' = ok o) :
    SimRE id lst o (occursConstFast (absU fuel) (absNIdx n) (absEIdx h')) := by
  sorry

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
      have hqa : lst.store.viewBind (absEIdx h') = q.map absBindM := by
        have := view_bind_run₀ hrel hbind hq
        have h2 : (Except.ok (lst.store.viewBind (absEIdx h'), lst) :
            Except Arena.CheckError _) = Except.ok (q.map absBindM, lst) := this
        simp only [Except.ok.injEq, Prod.mk.injEq] at h2
        exact h2.1
      have hv := view_of_bind_tag (st := lst.store) hbind
      rw [hqa, hlam] at hv
      rw [if_pos (by rw [hlam]; rfl)]
      show SimRE absEIdx lst o (Arena.view (absEIdx h') >>= _)
      unfold SimRE
      have hvr : (Arena.view (absEIdx h')).run lst = (match lst.store.view (absEIdx h') with
          | some v => Except.ok (v, lst)
          | none => Except.error (.internal "arena: dangling expression handle")) := by
        show ((match lst.store.view (absEIdx h') with
          | some v => (pure v : AM ENodeView)
          | none => Arena.fail (.internal "arena: dangling expression handle")).run lst) = _
        cases lst.store.view (absEIdx h') <;> rfl
      rw [am_run_bind', hvr, hv]
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
        simp only [Option.map_some, absBindM, eBindView, beq_self_eq_true, if_true,
          except_ok_bind]
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

/-- **`strip_pis_all` refines `stripPisAll`** (`ProjRec.lean:209-217`). -/
theorem strip_pis_all_refines {pers rst lst fuel h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.strip_pis_all pers rst fuel h' = ok o) :
    SimRE (fun p => (absBinderPairs p.1, absEIdx p.2)) lst o
      (stripPisAll (absU fuel) (absEIdx h')) := by sorry

/-- **`mk_lams_from`** — the cursor companion of `mk_lams`.  The twin conses
on the way OUT, so the cursor recurses to the end of the list and interns
outward from there. -/
theorem mk_lams_from_refines {pers rst lst bs i body o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_lams_from pers rst bs i body = ok o) :
    Sim₀ absEIdx pers lst o
      (mkLams (absBinderPairsFrom bs i) (absEIdx body)) := by sorry

/-- **`mk_lams` refines `mkLams`** (`ProjRec.lean:221-228`). -/
theorem mk_lams_refines {pers rst lst bs body o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_lams pers rst bs body = ok o) :
    Sim₀ absEIdx pers lst o
      (mkLams (absBinderPairs bs) (absEIdx body)) := by sorry

/-- **`inst_pis_open_from`** — the cursor companion of `inst_pis_open`. -/
theorem inst_pis_open_from_refines {pers rst lst fuel e args i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.inst_pis_open_from pers rst fuel e args i = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (instPisOpen (absU fuel) (absEIdx e) (absEIdxLFrom args i)) := by sorry

/-- **`inst_pis_open` refines `instPisOpen`** (`ProjRec.lean:232-243`). -/
theorem inst_pis_open_refines {pers rst lst fuel e args o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.inst_pis_open pers rst fuel e args = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (instPisOpen (absU fuel) (absEIdx e) (absEIdxL args)) := by sorry

/-- **`intern_param_levels_from`** — the cursor companion. -/
theorem intern_param_levels_from_refines {pers rst lst ns i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.intern_param_levels_from pers rst ns i = ok o) :
    Sim₀ (fun v => v.val.map absLIdx) pers lst o
      (projRecValue.internParamLevels (absNIdxLFrom ns i)) := by sorry

/-- **`intern_param_levels` refines `internParamLevels`**. -/
theorem intern_param_levels_refines {pers rst lst ns o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.intern_param_levels pers rst ns = ok o) :
    Sim₀ (fun v => v.val.map absLIdx) pers lst o
      (projRecValue.internParamLevels (absNIdxL ns)) := by sorry

/-- **`head_is` refines `headIs`** (`ProjRec.lean:267-273`). -/
theorem head_is_refines {pers rst lst fuel t e o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.head_is pers rst fuel t e = ok o) :
    SimRE id lst o (headIs (absU fuel) (absNIdx t) (absEIdx e)) := by sorry

/-! ## The two binder bodies -/

/-- **`mk_proj_motive_at`** — the port's split under the domain's view. -/
theorem mk_proj_motive_at_refines {pers rst lst pb fuel bs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_proj_motive_at pers rst pb fuel bs = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMotiveAt (absProjBuild pb) (absU fuel) (absBinderPairs bs)) := by
  sorry

/-- **`mk_proj_motive` refines `mkProjMotive`** (`ProjRec.lean:277-293`). -/
theorem mk_proj_motive_refines {pers rst lst pb fuel dom o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_proj_motive pers rst pb fuel dom = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMotive (absProjBuild pb) (absU fuel) (absEIdx dom)) := by sorry

/-- **`mk_proj_minor_at`** — the port's split under the domain's view. -/
theorem mk_proj_minor_at_refines {pers rst lst pb fuel bs major o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_proj_minor_at pers rst pb fuel bs major = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMinorAt (absProjBuild pb) (absU fuel) (absBinderPairs bs)
        (absEIdx major)) := by sorry

/-- **`mk_proj_minor` refines `mkProjMinor`** (`ProjRec.lean:297-310`). -/
theorem mk_proj_minor_refines {pers rst lst pb fuel dom o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.mk_proj_minor pers rst pb fuel dom = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (mkProjMinor (absProjBuild pb) (absU fuel) (absEIdx dom)) := by sorry

/-- **`build_binders_at`** — the port's split under the peeled binder. -/
theorem build_binders_at_refines {pers rst lst kind pb fuel k dom body o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.build_binders_at pers rst kind pb fuel k dom body
      = ok o) :
    Sim₀ (Option.map fun p => (absEIdxL p.1, absEIdx p.2)) pers lst o
      (buildBindersAt (absProjBinderKind kind) (absProjBuild pb) (absU fuel)
        (absU k) (absEIdx dom) (absEIdx body)) := by sorry

/-- **`build_binders` refines `buildBinders`** (`ProjRec.lean:314-339`).  The
recursion is on `k`, as the twin's is: a motive or minor count is never
large, so this is not a `Vec` cursor. -/
theorem build_binders_refines {pers rst lst kind pb fuel k h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.build_binders pers rst kind pb fuel k h' = ok o) :
    Sim₀ (Option.map fun p => (absEIdxL p.1, absEIdx p.2)) pers lst o
      (buildBinders (absProjBinderKind kind) (absProjBuild pb) (absU fuel)
        (absU k) (absEIdx h')) := by sorry

/-! ## The rewrite itself

`projRecValue` is one 48-line `do` block on the twin's side and six functions
on the port's, split at the twin's own `let` boundaries (P4c's arrangement for
this shape).  The five splits are stated against the twin's arm inline; the
entry point is stated against the twin. -/

/-- **`proj_rec_value_app`** — the recursor application, once the parameters,
motives and minors are built. -/
theorem proj_rec_value_app_refines {pers rst lst o' lbs us params motives minors o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_value_app pers rst o' lbs us params motives
      minors = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRecValueApp (absProjRecOwner o') (absBinderPairs lbs) (absLsIdx us)
        (absEIdxL params) (absEIdxL motives) (absEIdxL minors)) := by sorry

/-- **`proj_rec_value_major`** — the major premise and the application above
it. -/
theorem proj_rec_value_major_refines
    {pers rst lst fuel o' lbs us params motives minors rty3 o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_value_major pers rst fuel o' lbs us params
      motives minors rty3 = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRecValueMajor (absU fuel) (absProjRecOwner o') (absBinderPairs lbs)
        (absLsIdx us) (absEIdxL params) (absEIdxL motives) (absEIdxL minors)
        (absEIdx rty3)) := by sorry

/-- **`proj_rec_value_binders`** — the motive and the minors. -/
theorem proj_rec_value_binders_refines
    {pers rst lst fuel o' l r i lbs us params rty1 o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_value_binders pers rst fuel o' l r i lbs us
      params rty1 = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRecValueBinders (absU fuel) (absProjRecOwner o') (absLIdx l)
        (absEIdx r) (absU i) (absBinderPairs lbs) (absLsIdx us)
        (absEIdxL params) (absEIdx rty1)) := by sorry

/-- **`proj_rec_value_at`** — the universe arguments and the recursor's type
at the chosen elimination level. -/
theorem proj_rec_value_at_refines {pers rst lst fuel o' l r i lbs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_value_at pers rst fuel o' l r i lbs = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRecValueAt (absU fuel) (absProjRecOwner o') (absLIdx l) (absEIdx r)
        (absU i) (absBinderPairs lbs)) := by sorry

/-- **`proj_rec_value_ty`** — the projection's own codomain, stripped. -/
theorem proj_rec_value_ty_refines {pers rst lst fuel o' l ty i lbs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_value_ty pers rst fuel o' l ty i lbs = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRecValueTy (absU fuel) (absProjRecOwner o') (absLIdx l) (absEIdx ty)
        (absU i) (absBinderPairs lbs)) := by sorry

/-- **`proj_rec_value` refines `projRecValue`** (`ProjRec.lean:343-403`) —
**the rewrite**, and one of the tier's named deliverables. -/
theorem proj_rec_value_refines {pers rst lst fuel o' l ty val i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_value pers rst fuel o' l ty val i = ok o) :
    Sim₀ (Option.map absEIdx) pers lst o
      (projRecValue (absU fuel) (absProjRecOwner o') (absLIdx l) (absEIdx ty)
        (absEIdx val) (absU i)) := by sorry

/-! ## The owner census -/

/-- **`occurs_any_of_from`** — the cursor companion. -/
theorem occurs_any_of_from_refines {pers rst lst fuel ns d i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.occurs_any_of_from pers rst fuel ns d i = ok o) :
    SimRE id lst o (occursAnyOf (absU fuel) (absNIdxLFrom ns i) (absEIdx d)) := by
  sorry

/-- **`occurs_any_of` refines `occursAnyOf`** (`ProjRec.lean:407-412`). -/
theorem occurs_any_of_refines {pers rst lst fuel ns d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.occurs_any_of pers rst fuel ns d = ok o) :
    SimRE id lst o (occursAnyOf (absU fuel) (absNIdxL ns) (absEIdx d)) := by sorry

/-- **`doms_mention_any_from`** — the cursor companion. -/
theorem doms_mention_any_from_refines {pers rst lst fuel ns bs i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.doms_mention_any_from pers rst fuel ns bs i = ok o) :
    SimRE id lst o
      (domsMentionAny (absU fuel) (absNIdxL ns) (absBinderPairsFrom bs i)) := by
  sorry

/-- **`doms_mention_any` refines `domsMentionAny`** (`ProjRec.lean:416-421`). -/
theorem doms_mention_any_refines {pers rst lst fuel ns bs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.doms_mention_any pers rst fuel ns bs = ok o) :
    SimRE id lst o
      (domsMentionAny (absU fuel) (absNIdxL ns) (absBinderPairs bs)) := by sorry

/-- **`ctors_mention_block_from`** — the cursor companion. -/
theorem ctors_mention_block_from_refines {pers rst lst fuel ns ctors i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.ctors_mention_block_from pers rst fuel ns ctors i
      = ok o) :
    SimRE id lst o
      (ctorsMentionBlock (absU fuel) (absNIdxL ns)
        (absProjCtorRecLFrom ctors i)) := by sorry

/-- **`ctors_mention_block` refines `ctorsMentionBlock`**
(`ProjRec.lean:425-432`). -/
theorem ctors_mention_block_refines {pers rst lst fuel ns ctors o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.ctors_mention_block pers rst fuel ns ctors = ok o) :
    SimRE id lst o
      (ctorsMentionBlock (absU fuel) (absNIdxL ns) (absProjCtorRecL ctors)) := by
  sorry

/-- **`find_ctor_rec_from`** — the cursor companion.  Deviation 2: the port
answers the INDEX. -/
theorem find_ctor_rec_from_refines {ctors c i o}
    (h : frontend.proj_rec.find_ctor_rec_from ctors c i = ok o) :
    o.map (fun j => (absProjCtorRecL ctors)[j.val]?) =
      (findCtorRec (absNIdx c) (absProjCtorRecLFrom ctors i)).map some := by sorry

/-- **`find_ctor_rec` refines `findCtorRec`** (`ProjRec.lean:435-437`). -/
theorem find_ctor_rec_refines {ctors c o}
    (h : frontend.proj_rec.find_ctor_rec ctors c = ok o) :
    o.bind (fun j => (absProjCtorRecL ctors)[j.val]?) =
      findCtorRec (absNIdx c) (absProjCtorRecL ctors) := by sorry

/-- **`find_rec_rec_from`** — the cursor companion. -/
theorem find_rec_rec_from_refines {recs n i o}
    (h : frontend.proj_rec.find_rec_rec_from recs n i = ok o) :
    o.map (fun j => (absProjRecRecL recs)[j.val]?) =
      (findRecRec (absNIdx n) (absProjRecRecLFrom recs i)).map some := by sorry

/-- **`find_rec_rec` refines `findRecRec`** (`ProjRec.lean:441-445`). -/
theorem find_rec_rec_refines {recs n o}
    (h : frontend.proj_rec.find_rec_rec recs n = ok o) :
    o.bind (fun j => (absProjRecRecL recs)[j.val]?) =
      findRecRec (absNIdx n) (absProjRecRecL recs) := by sorry

/-- **`proj_rec_candidate_rec`** — the port's split at the found recursor
record. -/
theorem proj_rec_candidate_rec_refines {pers rst lst ctors recs t o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_candidate_rec pers rst ctors recs t = ok o) :
    Sim₀ (Option.map absProjRecOwner) pers lst o
      (projRecCandidateRec (absProjCtorRecL ctors) (absProjRecRecL recs)
        (absProjTypeRec t)) := by sorry

/-- **`proj_rec_candidate_at`** — one type record's candidacy. -/
theorem proj_rec_candidate_at_refines {pers rst lst ctors recs t o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_candidate_at pers rst ctors recs t = ok o) :
    Sim₀ (Option.map absProjRecOwner) pers lst o
      (projRecCandidateAt (absProjCtorRecL ctors) (absProjRecRecL recs)
        (absProjTypeRec t)) := by sorry

/-- **`proj_rec_candidates_from`** — the cursor companion. -/
theorem proj_rec_candidates_from_refines {pers rst lst ctors recs types i fuel o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_candidates_from pers rst ctors recs types i
      = ok o) :
    Sim₀ absProjRecOwnerL pers lst o
      (projRecCandidates fuel (absProjCtorRecL ctors) (absProjRecRecL recs)
        (absProjTypeRecLFrom types i)) := by sorry

/-- **`proj_rec_candidates` refines `projRecCandidates`**
(`ProjRec.lean:452-494`).  Deviation 3: the twin's `fuel` is dead, so the
statement holds at ANY fuel. -/
theorem proj_rec_candidates_refines {pers rst lst ctors recs types fuel o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_candidates pers rst ctors recs types = ok o) :
    Sim₀ absProjRecOwnerL pers lst o
      (projRecCandidates fuel (absProjCtorRecL ctors) (absProjRecRecL recs)
        (absProjTypeRecL types)) := by sorry

/-- **`proj_rec_owners_guard`** — the two delegated block recognisers
(`structPartsCore?`, `nativeParts?`) and the recursive test, in the twin's own
CHEAP ORDER (deviation 3 of `ProjRec.lean`: the candidates first, the
recognisers only when there is a candidate to serve). -/
theorem proj_rec_owners_guard_refines {pers rst lst fuel block types ctors owners o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_owners_guard pers rst fuel block types ctors
      owners = ok o) :
    Sim₀ absProjRecOwnerL pers lst o
      (projRecOwnersGuard (absU fuel) (absICIL block) (absProjTypeRecL types)
        (absProjCtorRecL ctors) (absProjRecOwnerL owners)) := by sorry

/-- **`proj_rec_owners` refines `projRecOwners`** (`ProjRec.lean:498-517`) —
the owner census, and one of the tier's named deliverables. -/
theorem proj_rec_owners_refines {pers rst lst fuel block types ctors recs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.proj_rec.proj_rec_owners pers rst fuel block types ctors recs
      = ok o) :
    Sim₀ absProjRecOwnerL pers lst o
      (projRecOwners (absU fuel) (absICIL block) (absProjTypeRecL types)
        (absProjCtorRecL ctors) (absProjRecRecL recs)) := by sorry

end ConRon.Refine2.Frontend
