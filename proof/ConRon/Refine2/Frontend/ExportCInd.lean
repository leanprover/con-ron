/-
# `ConRon.Refine2.Frontend.ExportCInd` — the inductive record

**Task #97-P5-Frontend**, the second of `frontend/export_c.rs`'s three files:
`validate_ind_d` (the half of an inductive record's processing that reads the
state and changes nothing) and `install_ind_d` (the half that changes it), and
their twenty-five helpers.

## Why this is twenty-seven functions against the twin's two

`validateIndD` is one 100-line `do` block with **two `for`/`mut` loops** and
eleven verdicts; `installIndD` is one 60-line block.  Aeneas copies the code
AFTER a loop into every exit of it, so each loop is its own function whose
tail is one line (`export_c.rs`'s own note, and `con_ron_core`'s arrangement
before it).  Eleven of the twenty-seven are message builders, and their
statements are in `Refine2/Frontend/ExportC.lean`, as explicit no-claims.

**The eleven verdicts are what this tier must not weaken.**  DESIGN §8.3:
*"names are compared for inequality throughout the checker"*, and the parse's
redundant-field checks are the reason a contradicted `numFields` or a
duplicated constructor name is a REJECT and not an accept.  Task #97e part 1
measured them: 23 of the 60 fixtures the arena agreed on at that point were
`validateIndD` rejects.  So `validate_ind_d_refines` is the load-bearing
statement of this file and the helpers exist to feed it.

## What the helper statements are stated against

Eleven of the helpers are PURE or read only the index tables, and their
statement is an equation against the twin's own expression, written inline —
`any_ty_unsafe` is `tys.any (·.isUnsafe)`, `flatten_listed` is
`listed.flatten`, and so on.  The four `check_*` ones and the two `order_*`
ones are the two `for` loops' bodies and have no twin expression of their own;
they are stated against a named reading in the doc comment and **their
transcriptions are what `Refine2/Frontend/Spec.lean` still owes** — the one
group of this tier where the statement is about the port's own arm rather
than about a twin clause.  DESIGN.md's section lists them.

## `sorry` count in this file: 25
-/
import ConRon.Refine2.Frontend.ExportC
import ConRon.Refine2.Frontend.SpecInd

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IdTable NameRec LevelRec ExprRec PwRec CVRec HintsRec RuleRec
  IndTypeRec IndCtorRec IndRecRec DeclRec LineRec)

/-! ## The block's own fields -/

/-- **`any_ty_unsafe`** — the twin's `tys.any (·.isUnsafe)`: an `unsafe
inductive` is DECLINED, not an error. -/
theorem any_ty_unsafe_refines {tys v}
    (h : frontend.export_c.any_ty_unsafe tys = ok v) :
    v = (absIndTypeRecs tys).any (·.isUnsafe) := by sorry

/-- **`any_ty_nested`** — the twin's `tys.any (·.numNested != 0)`, the flag
that turns the recursor checks off. -/
theorem any_ty_nested_refines {tys v}
    (h : frontend.export_c.any_ty_nested tys = ok v) :
    v = (absIndTypeRecs tys).any (·.numNested != 0) := by sorry

/-- **`all_num_params`** — the twin's `nPs.all (· == nPd)`: the declared
parameter count is well defined for the block exactly when its type records
agree on it. -/
theorem all_num_params_refines {tys n_pd v}
    (h : frontend.export_c.all_num_params tys n_pd = ok v) :
    v = ((absIndTypeRecs tys).map (·.numParams)).all (· == absU n_pd) := by sorry

/-- **`ty_names_of`** — the twin's `tys.mapM fun t => st.name t.cv.name`. -/
theorem ty_names_of_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ty_names_of rsd tys = ok o) :
    SimLR absNIdxL lst o
      ((absIndTypeRecs tys).mapM fun t => lsd.name t.cv.name) := by
  rw [frontend.export_c.ty_names_of] at h
  exact simLR_cursor0 (absX := absIndTypeRec) (xs := tys)
    (loop := fun out i =>
      frontend.export_c.ty_names_of_loop rsd tys out (alloc.vec.Vec.len tys) i)
    (fun out i o hn h => by
      rw [frontend.export_c.ty_names_of_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len tys by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.ty_names_of_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len tys by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨r, by rw [vec_index_eq hi hx]; exact st_name_refines hd hr, ?_⟩
      cases r with
      | Err e => exact Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩
      | Ok y =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        exact Or.inr ⟨y, out1, i1, rfl, e1, e2, h⟩)
    rfl h

/-- **`ty_types_of`** — the twin's `tys.mapM fun t => getDeclD st t.cv.type`. -/
theorem ty_types_of_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ty_types_of rsd tys = ok o) :
    SimLR absEIdxL lst o
      ((absIndTypeRecs tys).mapM fun t => getDeclD lsd t.cv.type) := by
  rw [frontend.export_c.ty_types_of] at h
  exact simLR_cursor0 (absX := absIndTypeRec) (xs := tys)
    (loop := fun out i =>
      frontend.export_c.ty_types_of_loop rsd tys out (alloc.vec.Vec.len tys) i)
    (fun out i o hn h => by
      rw [frontend.export_c.ty_types_of_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len tys by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.ty_types_of_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len tys by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨r, by rw [vec_index_eq hi hx]; exact get_decl_d_refines hd hr, ?_⟩
      cases r with
      | Err e => exact Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩
      | Ok y =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        exact Or.inr ⟨y, out1, i1, rfl, e1, e2, h⟩)
    rfl h

/-- **`listed_ctors_of`** — the twin's `tys.mapM fun t => t.ctors.mapM
st.name`. -/
theorem listed_ctors_of_refines {rsd lsd lst tys o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.listed_ctors_of rsd tys = ok o) :
    SimLR (fun v => v.val.map absNIdxL) lst o
      ((absIndTypeRecs tys).mapM fun t => t.ctors.mapM lsd.name) := by
  rw [frontend.export_c.listed_ctors_of] at h
  exact simLR_cursor0 (absY := absNIdxL) (absX := absIndTypeRec) (xs := tys)
    (loop := fun out i =>
      frontend.export_c.listed_ctors_of_loop rsd tys out (alloc.vec.Vec.len tys) i)
    (fun out i o hn h => by
      rw [frontend.export_c.listed_ctors_of_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len tys by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.listed_ctors_of_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len tys by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨r, by rw [vec_index_eq hi hx]; exact st_names_refines hd hr, ?_⟩
      cases r with
      | Err e => exact Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩
      | Ok y =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        exact Or.inr ⟨y, out1, i1, rfl, e1, e2, h⟩)
    rfl h

/-- **`ctor_names_of`** — the twin's `cts.mapM fun c => st.name c.cv.name`. -/
theorem ctor_names_of_refines {rsd lsd lst cts o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ctor_names_of rsd cts = ok o) :
    SimLR absNIdxL lst o
      ((absIndCtorRecs cts).mapM fun c => lsd.name c.cv.name) := by
  rw [frontend.export_c.ctor_names_of] at h
  exact simLR_cursor0 (absX := absIndCtorRec) (xs := cts)
    (loop := fun out i =>
      frontend.export_c.ctor_names_of_loop rsd cts out (alloc.vec.Vec.len cts) i)
    (fun out i o hn h => by
      rw [frontend.export_c.ctor_names_of_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len cts by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.ctor_names_of_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len cts by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨r, by rw [vec_index_eq hi hx]; exact st_name_refines hd hr, ?_⟩
      cases r with
      | Err e => exact Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩
      | Ok y =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        exact Or.inr ⟨y, out1, i1, rfl, e1, e2, h⟩)
    rfl h

/-- **`flatten_listed`** — the twin's `listed.flatten`. -/
theorem flatten_listed_refines {listed v}
    (h : frontend.export_c.flatten_listed listed = ok v) :
    absNIdxL v = (listed.val.map absNIdxL).flatten := by sorry

/-- **`names_have_dup`** — the twin's `flat.Nodup`, complemented.  The port's
algorithm is a handle-keyed SET PASS and not the quadratic scan, because
Aeneas answers *"Returns inside of nested loops are not supported yet"* to the
obvious spelling (extraction rule 4); the two decide the same predicate, which
is what this says. -/
theorem names_have_dup_refines {flat v}
    (h : frontend.export_c.names_have_dup flat = ok v) :
    v = !(absNIdxL flat).Nodup := by sorry

/-- **`ctor_index_of`** — the twin's `ctorNames.foldl` into `ctorIx`.  Task
#87 §20's port bug — *"`ctor_index_of` was first-wins"* — is a fact about the
`Expr`-tree port that this statement is what would catch again: the twin's
fold is LAST-wins, because `Std.HashMap.insert` overwrites. -/
theorem ctor_index_of_refines {ns m}
    (h : frontend.export_c.ctor_index_of ns = ok m) :
    NameIdxRel m
      ((((absNIdxL ns).foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
        (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0))).1) := by sorry

/-- **`show_name`** — a handle read back for a message.  The port's readback
is `denoteN`'s (`env::read_name`); messages are never compared, so what is
claimed is that it succeeds, and fails, exactly where the twin's `readName`
does — at the state it started in. -/
theorem show_name_refines {pers rst lst h' o}
    (hrel : AStateRel₀ pers rst lst) (_hinv : AStateInv pers rst)
    (h : frontend.export_c.show_name pers rst.store h' = ok o) :
    SimLR (fun _ => ()) lst o ((fun _ => ()) <$> readName (absNIdx h')) := by
  rw [frontend.export_c.show_name] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hR := env_read_name_abs hrel.store hr
  have hrun : ∀ x, denoteN lst.store.ns (absNIdx h') = x →
      (((fun _ => ()) <$> readName (absNIdx h')) : AM Unit).run lst =
        match x with
        | some _ => .ok ((), lst)
        | none => .error (.internal "arena: dangling name handle") := by
    rintro x rfl
    unfold readName
    show StateT.run ((fun _ => ()) <$> ((match denoteN lst.store.ns (absNIdx h') with
      | some x => pure x
      | none => Arena.fail (.internal "arena: dangling name handle")) : AM ConLeche.Name)) lst = _
    cases denoteN lst.store.ns (absNIdx h') <;> rfl
  cases hdn : denoteN lst.store.ns (absNIdx h') with
  | none =>
    rw [hdn] at hR
    obtain ⟨e, rfl, hek⟩ := hR
    obtain ⟨e', rfl, hk'⟩ := fail_refines h
    exact AErrSim.mk (hrun _ hdn) (by rw [hk', hek]; rfl)
  | some x =>
    rw [hdn] at hR
    obtain ⟨y, rfl, -⟩ := hR
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    exact hrun _ hdn

/-! ## The verdict-carrying pieces (ruling F12)

`validateIndD`'s loop bodies can `return` a verdict; the port's return it
through `LineErr::Verdict`.  `SimLV A V` is `SimLR` with that third arm: a
port verdict is a twin run that answers, at the state it started in, with a
value `V` classifies as a verdict of the same kind.  Its twin sides are
`Refine2/Frontend/SpecInd.lean`'s transcriptions, and `validateIndD_unfold`
(definitional) composes them into `validateIndD`. -/

/-- A loop state's verdict, if it carries one. -/
def vOfOpt : Option VRes → Option RecordVerdict
  | some (.inl v) => some v
  | _ => none

/-- **A verdict-carrying port reader against its twin.** -/
def SimLV {α β : Type} (A : α → β) (V : β → Option RecordVerdict) (lst : AState)
    (o : core.result.Result α frontend.export_c.LineErr) (x : AM β) : Prop :=
  match o with
  | .Ok r => x.run lst = .ok (A r, lst)
  | .Err (.Err ce) => AErrSim ce (x.run lst)
  | .Err (.Verdict vd) => ∃ b lv, x.run lst = .ok (b, lst) ∧ V b = some lv ∧
      lVerdictKind lv = absVerdictKind vd

theorem SimLV.bind {α β γ δ : Type} {A : α → β} {V : β → Option RecordVerdict}
    {B : δ → γ} {lst : AState} {r : core.result.Result δ frontend.export_c.LineErr}
    {x : AM γ} {f : γ → AM β} {o}
    (hx : SimLR B lst r x) (hk : ∀ v, r = .Ok v → SimLV A V lst o (f (B v)))
    (herr : ∀ e, r = .Err e → o = .Err e) : SimLV A V lst o (x >>= f) := by
  cases r with
  | Ok v =>
    have h1 := hk v rfl
    simp only [SimLR] at hx
    have e : (x >>= f).run lst = (f (B v)).run lst := by rw [am_run_bind', hx]; rfl
    unfold SimLV at h1 ⊢
    rw [e]; exact h1
  | Err e =>
    obtain rfl := herr e rfl
    simp only [SimLR] at hx
    cases e with
    | Verdict _ => exact hx.elim
    | Err ce =>
      show AErrSim ce _
      rw [am_run_bind']; exact AErrSim.bind hx _

/-- A message's name read: `show_name` against the twin's `readName`, whose
value the verdict's text only uses. -/
theorem SimLV.bind_name {α β γ : Type} {A : α → β} {V : β → Option RecordVerdict}
    {lst : AState} {r : core.result.Result (alloc.vec.Vec Std.U32) frontend.export_c.LineErr}
    {m : AM γ} {f : γ → AM β} {o}
    (hx : SimLR (fun _ => ()) lst r ((fun _ => ()) <$> m))
    (hk : ∀ v, r = .Ok v → ∀ a, SimLV A V lst o (f a))
    (herr : ∀ e, r = .Err e → o = .Err e) : SimLV A V lst o (m >>= f) := by
  have hmap : ((fun _ => ()) <$> m).run lst = (m.run lst) >>= fun p => pure ((), p.2) := rfl
  cases r with
  | Ok v =>
    simp only [SimLR] at hx
    rw [hmap] at hx
    cases hm : m.run lst with
    | error le => rw [hm] at hx; cases hx
    | ok p =>
      rw [hm] at hx
      obtain ⟨a, s⟩ := p
      have hs : s = lst := by
        have : (Except.ok ((), s) : Except Arena.CheckError _) = .ok ((), lst) := hx
        cases this; rfl
      subst hs
      have h1 := hk v rfl a
      have e : (m >>= f).run s = (f a).run s := by rw [am_run_bind', hm]; rfl
      unfold SimLV at h1 ⊢
      rw [e]; exact h1
  | Err e =>
    obtain rfl := herr e rfl
    simp only [SimLR] at hx
    cases e with
    | Verdict _ => exact hx.elim
    | Err ce =>
      show AErrSim ce _
      refine AErrSim.trans hx fun le hle => ?_
      rw [hmap] at hle
      rw [am_run_bind']
      cases hm : m.run lst with
      | error le' => rw [hm] at hle; cases hle; rfl
      | ok p => rw [hm] at hle; cases hle

/-- `export_c::invalid` is an `invalid` verdict. -/
theorem invalid_ok {T : Type} {v o} (h : frontend.export_c.invalid T v = ok o) :
    o = .Err (.Verdict (.Invalid v)) := by
  rw [frontend.export_c.invalid] at h
  exact (Result.ok_injective h).symm

/-- A message builder, then `invalid`: an `invalid` verdict. -/
theorem msg_invalid_ok {T X : Type} {m : Result X} {k : X → alloc.vec.Vec Std.U32} {o}
    (h : (do let v ← m; frontend.export_c.invalid T (k v)) = ok o) :
    ∃ v, o = .Err (.Verdict (.Invalid v)) := by
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨_, invalid_ok h⟩

/-- The twin answering with an `invalid` verdict. -/
theorem SimLV.invalid {α β : Type} {A : α → β} {V : β → Option RecordVerdict}
    {lst : AState} {b : β} {s : String} (hV : V b = some (.invalid s)) (w) :
    SimLV A V lst (.Err (.Verdict (.Invalid w))) (pure b) :=
  ⟨b, _, rfl, hV, rfl⟩

/-! ## The first `for` loop: the constructors in the block's own order -/

/-- A verdict-carrying check, then its continuation: the check passing runs
the continuation at `none`; a verdict `b` is handed on as one. -/
theorem SimLV.bind_check {β : Type} {A : α → β} {V : β → Option RecordVerdict}
    {lst : AState} {r : core.result.Result Unit frontend.export_c.LineErr}
    {x : AM (Option VRes)} {f : Option VRes → AM β} {o}
    (hx : SimLV (fun _ => none) vOfOpt lst r x)
    (hok : r = .Ok () → SimLV A V lst o (f none))
    (hv : ∀ b lv, vOfOpt b = some lv → ∃ b', (f b).run lst = .ok (b', lst) ∧ V b' = some lv)
    (herr : ∀ e, r = .Err e → o = .Err e) :
    SimLV A V lst o (x >>= f) := by
  cases r with
  | Ok u =>
    have h1 := hok rfl
    have hx' : x.run lst = .ok (none, lst) := hx
    have e : (x >>= f).run lst = (f none).run lst := by rw [am_run_bind', hx']; rfl
    unfold SimLV at h1 ⊢
    rw [e]; exact h1
  | Err e =>
    obtain rfl := herr e rfl
    cases e with
    | Err ce =>
      have hx' : AErrSim ce (x.run lst) := hx
      show AErrSim ce _
      rw [am_run_bind']; exact AErrSim.bind hx' _
    | Verdict vd =>
      obtain ⟨b, lv, hb, hV, hk⟩ := hx
      obtain ⟨b', hb', hV'⟩ := hv b lv hV
      refine ⟨b', lv, ?_, hV', hk⟩
      rw [am_run_bind', hb]; exact hb'

/-- A verdict-carrying piece, then its continuation, at any result shape. -/
theorem SimLV.bind_lv {α β γ δ : Type} {A : α → β} {V : β → Option RecordVerdict}
    {A1 : δ → γ} {V1 : γ → Option RecordVerdict}
    {lst : AState} {r : core.result.Result δ frontend.export_c.LineErr}
    {x : AM γ} {f : γ → AM β} {o}
    (hx : SimLV A1 V1 lst r x)
    (hok : ∀ w, r = .Ok w → SimLV A V lst o (f (A1 w)))
    (hv : ∀ b lv, V1 b = some lv → ∃ b', (f b).run lst = .ok (b', lst) ∧ V b' = some lv)
    (herr : ∀ e, r = .Err e → o = .Err e) :
    SimLV A V lst o (x >>= f) := by
  cases r with
  | Ok w =>
    have h1 := hok w rfl
    have hx' : x.run lst = .ok (A1 w, lst) := hx
    have e : (x >>= f).run lst = (f (A1 w)).run lst := by rw [am_run_bind', hx']; rfl
    unfold SimLV at h1 ⊢
    rw [e]; exact h1
  | Err e =>
    obtain rfl := herr e rfl
    cases e with
    | Err ce =>
      have hx' : AErrSim ce (x.run lst) := hx
      show AErrSim ce _
      rw [am_run_bind']; exact AErrSim.bind hx' _
    | Verdict vd =>
      obtain ⟨b, lv, hb, hV, hk⟩ := hx
      obtain ⟨b', hb', hV'⟩ := hv b lv hV
      refine ⟨b', lv, ?_, hV', hk⟩
      rw [am_run_bind', hb]; exact hb'

/-- A zipped cursor at a live position. -/
theorem zip_drop_cons {X Y : Type} {l1 : List X} {l2 : List Y} {i : Nat}
    (h1 : i < l1.length) (h2 : i < l2.length) :
    (l1.zip l2).drop i = (l1[i], l2[i]) :: (l1.zip l2).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp [List.getElem_zip]

/-- `(absNIdxL ns).drop i` at a live cursor. -/
theorem absNIdxL_drop_cons {ns : alloc.vec.Vec arena.handle.NIdx} {i : Nat}
    (hi : i < ns.val.length) :
    (absNIdxL ns).drop i = absNIdx (ns.val[i]'hi) :: (absNIdxL ns).drop (i + 1) := by
  simp only [absNIdxL, ← List.map_drop, List.drop_eq_getElem_cons hi, List.map_cons]

-- `check_one_ctor`'s `numFields` tail, which Aeneas copies into each of its
-- four `cidx`/`induct` arms.
set_option hygiene false in
local macro "ctor_fields_tail" : tactic => `(tactic| (
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine SimLV.bind (get_decl_d_refines hd hr) (fun v hv => ?_)
    (fun e he => by subst he; exact (Result.ok_injective h).symm)
  subst hv
  obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine SimLV.bind (ind_pi_tele_len_refines hrel hinv hr1) (fun v1 hv1 => ?_)
    (fun e he => by subst he; exact (Result.ok_injective h).symm)
  subst hv1
  obtain ⟨i, hi', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hiv := ConRon.Refine.Nat.uadd_val hi'
  by_cases hne : (i != v1) = true
  · rw [if_pos hne] at h
    have hne' : ¬ (absU n_pd + absU64 c.num_fields == absU v1) = true := by
      simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv] at hne
      simp only [absU, absU64, beq_iff_eq]; omega
    rw [if_neg hne']
    obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine SimLV.bind_name (show_name_refines hrel hinv hr2) (fun v2 hv2 a => ?_)
      (fun e he => by subst he; exact (Result.ok_injective h).symm)
    subst hv2
    obtain ⟨_, rfl⟩ := msg_invalid_ok h
    exact SimLV.invalid (by rfl) _
  · rw [if_neg hne] at h
    cases Result.ok_injective h
    have heq : (absU n_pd + absU64 c.num_fields == absU v1) = true := by
      simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv, Classical.not_not] at hne
      simp only [absU, absU64, beq_iff_eq]; omega
    rw [if_pos heq]
    rfl))

-- `check_one_ctor`'s `induct` check, ending in its `numFields` tail.
set_option hygiene false in
local macro "ctor_induct" : tactic => `(tactic| (
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine SimLV.bind (st_name_refines hd hr) (fun v hv => ?_)
    (fun e he => by subst he; exact (Result.ok_injective h).symm)
  subst hv
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [nidx_eq2_abs hb] at h
  by_cases hbt : (absNIdx v == absNIdx t) = true
  · rw [if_pos hbt] at h
    rw [if_pos hbt]
    try simp only [pure_bind]
    ctor_fields_tail
  · rw [if_neg hbt] at h
    rw [if_neg hbt]
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine SimLV.bind_name (show_name_refines hrel hinv hr1) (fun v1 hv1 a1 => ?_)
      (fun e he => by subst he; exact (Result.ok_injective h).symm)
    subst hv1
    obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine SimLV.bind_name (show_name_refines hrel hinv hr2) (fun v2 hv2 a2 => ?_)
      (fun e he => by subst he; exact (Result.ok_injective h).symm)
    subst hv2
    obtain ⟨r3, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine SimLV.bind_name (show_name_refines hrel hinv hr3) (fun v3 hv3 a3 => ?_)
      (fun e he => by subst he; exact (Result.ok_injective h).symm)
    subst hv3
    obtain ⟨_, rfl⟩ := msg_invalid_ok h
    exact SimLV.invalid (by rfl) _))

-- `check_one_ctor`'s `cidx` check; leaves the passing arm.
set_option hygiene false in
local macro "ctor_cidx" : tactic => `(tactic| (
  by_cases hcj : (ci != j) = true
  case pos =>
    rw [if_pos hcj] at h
    have hne : ¬ (absU64 ci == absU j) = true := by
      simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv] at hcj
      simpa [absU64, absU] using hcj
    rw [if_neg hne]
    obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine SimLV.bind_name (show_name_refines hrel hinv hr) (fun v hv a => ?_)
      (fun e he => by subst he; exact (Result.ok_injective h).symm)
    subst hv
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine SimLV.bind_name (show_name_refines hrel hinv hr1) (fun v1 hv1 a1 => ?_)
      (fun e he => by subst he; exact (Result.ok_injective h).symm)
    subst hv1
    obtain ⟨_, rfl⟩ := msg_invalid_ok h
    exact SimLV.invalid (by rfl) _
  rw [if_neg hcj] at h
  have heq : (absU64 ci == absU j) = true := by
    simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv, Classical.not_not] at hcj
    simpa [absU64, absU] using hcj
  rw [if_pos heq]
  try simp only [pure_bind]))

/-- **`check_one_ctor`** — the three redundant-field checks at one
constructor, against `checkOneCtorD`: `cidx` names its position, `induct`
names its type former, and `numParams + numFields` is the constructor type's
own Π-telescope length.  Each failing check is an `invalid` verdict on both
sides. -/
theorem check_one_ctor_refines {pers rst lst rsd lsd fuel n t c j n_pd o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd)
    (h : frontend.export_c.check_one_ctor pers rst.store fuel rsd n t c j n_pd
      = ok o) :
    SimLV (fun _ => none) vOfOpt lst o
      (checkOneCtorD lsd (absU fuel) (absNIdx t) (absNIdx n) (absIndCtorRec c)
        (absU j) (absU n_pd)) := by
  rw [frontend.export_c.check_one_ctor] at h
  unfold checkOneCtorD
  cases hc : c.cidx with
  | none =>
    cases hi : c.induct with
    | none =>
      simp only [hc, hi, absIndCtorRec, Option.map, pure_bind] at h ⊢
      ctor_fields_tail
    | some iw =>
      simp only [hc, hi, absIndCtorRec, Option.map, pure_bind] at h ⊢
      ctor_induct
  | some ci =>
    cases hi : c.induct with
    | none =>
      simp only [hc, hi, absIndCtorRec, Option.map, pure_bind] at h ⊢
      ctor_cidx
      ctor_fields_tail
    | some iw =>
      simp only [hc, hi, absIndCtorRec, Option.map, pure_bind] at h ⊢
      ctor_cidx
      ctor_induct

/-- **`order_type_ctors`** — the inner `for n in ns` loop at one type former,
against `orderTypeCtorsD` from position `0`.  `hix` is `ctor_index_of`'s
range: every index the table holds is a constructor record's. -/
theorem order_type_ctors_refines
    {pers rst lst rsd lsd fuel t ns cts ctor_ix lm n_pd out o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hx : NameIdxRel ctor_ix lm)
    (hix : ∀ (x : NIdx) k, lm[x]? = some k → k < cts.val.length)
    (h : frontend.export_c.order_type_ctors pers rst.store fuel rsd t ns cts
      ctor_ix n_pd out = ok o) :
    SimLV (fun v => ⟨none, (absNIdxL ns).length, (absIndCtorRecs v).toArray⟩)
      (fun b => vOfOpt b.1) lst o
      (orderTypeCtorsD lsd (absU fuel) (absNIdx t) lm (absIndCtorRecs cts).toArray
        (absU n_pd) (absNIdxL ns) 0 (absIndCtorRecs out).toArray) := by
  rw [frontend.export_c.order_type_ctors] at h
  have H : ∀ (k : Nat) out (j : Std.U64) (i : Std.Usize) o, ns.val.length - i.val = k →
      i.val ≤ ns.val.length → j.val = i.val →
      frontend.export_c.order_type_ctors_loop pers rst.store fuel rsd t ns cts ctor_ix n_pd
        out (alloc.vec.Vec.len ns) j i = ok o →
      SimLV (fun v => ⟨none, (absNIdxL ns).length, (absIndCtorRecs v).toArray⟩)
        (fun b => vOfOpt b.1) lst o
        (forIn ((absNIdxL ns).drop i.val)
          (⟨none, j.val, (absIndCtorRecs out).toArray⟩ :
            MProd (Option VRes) (MProd Nat (Array IndCtorRec)))
          fun n r => orderCtorStepD lsd (absU fuel) (absNIdx t) lm
            (absIndCtorRecs cts).toArray (absU n_pd) n r.2.1 r.2.2) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro out j i o hk hil hj h
      rw [frontend.export_c.order_type_ctors_loop.eq_def] at h
      by_cases hi : i < alloc.vec.Vec.len ns
      · rw [if_pos hi] at h
        have hi' : i.val < ns.val.length := by scalar_tac
        obtain ⟨nm, hnm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hnm' := vec_index_eq hi' hnm
        obtain ⟨og, hog, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hget : og.map absU = lm[absNIdx nm]? := by
          have hr' := nidx_get hx.2 hog
          rw [← hx.1 nm trivial, ← hr']
        rw [absNIdxL_drop_cons hi', List.forIn_cons, orderCtorStepD_eq, hnm']
        cases og with
        | none =>
          rw [← hget]
          simp only [Option.map, bind_assoc, pure_bind]
          obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          refine SimLV.bind_name (show_name_refines hrel hinv hr) (fun v hv a => ?_)
            (fun e he => by subst he; exact (Result.ok_injective h).symm)
          subst hv
          obtain ⟨_, rfl⟩ := msg_invalid_ok h
          exact SimLV.invalid (by rfl) _
        | some kk =>
          rw [← hget]
          simp only [Option.map]
          have hkk : kk.val < cts.val.length := hix _ _ hget.symm
          obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hk1v : k1.val = kk.val := by
            simp only [lift, Result.ok.injEq] at hk1
            subst hk1
            exact u64_cast_usize_val' cts.property hkk
          have hk1l : ¬ k1 ≥ alloc.vec.Vec.len cts := by scalar_tac
          rw [if_neg hk1l] at h
          have hA : (absIndCtorRecs cts).toArray[absU kk]? =
              some (absIndCtorRec (cts.val[k1.val]'(by omega))) := by
            simp only [absIndCtorRecs, List.getElem?_toArray, List.getElem?_map, absU,
              ← hk1v, List.getElem?_eq_getElem (show k1.val < cts.val.length by omega),
              Option.map]
          rw [hA]
          simp only [bind_assoc]
          obtain ⟨icr, hicr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hicr' := vec_index_eq (show k1.val < cts.val.length by omega) hicr
          rw [hicr']
          obtain ⟨rc, hrc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          refine SimLV.bind_check (check_one_ctor_refines hrel hinv hd hrc)
            (fun hok => ?_) (fun b lv hb => ?_)
            (fun e he => by subst he; exact (Result.ok_injective h).symm)
          · subst hok
            simp only [pure_bind]
            obtain ⟨icr1, hicr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨e1, e2⟩ := cursor_push hout1 hi2
            have hj1v := ConRon.Refine.Nat.uadd_val hj1
            have hR := ih (ns.val.length - i2.val) (by omega) out1 j1 i2 o rfl (by omega)
              (by simp at hj1v; omega) h
            rw [e2] at hR
            have ea : (absIndCtorRecs out1).toArray =
                (absIndCtorRecs out).toArray.push (absIndCtorRec icr) := by
              simp only [absIndCtorRecs, e1, List.map_append, List.map_cons, List.map_nil,
                ind_ctor_rec_dup_refines hicr1, List.push_toArray]
            rw [ea, show j1.val = j.val + 1 by simp at hj1v; omega] at hR
            exact hR
          · rcases b with _ | (lv' | _) <;> simp only [vOfOpt, reduceCtorEq, Option.some.injEq] at hb
            subst hb
            exact ⟨_, rfl, rfl⟩
      · rw [if_neg hi] at h
        cases Result.ok_injective h
        have hlen : i.val = ns.val.length := by scalar_tac
        rw [hlen, List.drop_eq_nil_of_le (by simp [absNIdxL]), List.forIn_nil]
        show Except.ok _ = _
        rw [hj, hlen]; simp [absNIdxL]
  have := H _ out 0#u64 0#usize o rfl (by simp) rfl h
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at this
  exact this

/-- **`order_block_ctors`** — the outer `for tn in tyNames.zip listed` loop,
against `orderBlockCtorsD`: the constructors in the block's own order. -/
theorem order_block_ctors_refines
    {pers rst lst rsd lsd fuel ty_names listed cts ctor_ix lm n_pd o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hx : NameIdxRel ctor_ix lm)
    (hix : ∀ (x : NIdx) k, lm[x]? = some k → k < cts.val.length)
    (h : frontend.export_c.order_block_ctors pers rst.store fuel rsd ty_names
      listed cts ctor_ix n_pd = ok o) :
    SimLV (fun v => ⟨none, (absIndCtorRecs v).toArray⟩) (fun b => vOfOpt b.1) lst o
      (orderBlockCtorsD lsd (absU fuel) lm (absIndCtorRecs cts).toArray (absU n_pd)
        ((absNIdxL ty_names).zip (listed.val.map absNIdxL)) #[]) := by
  rw [frontend.export_c.order_block_ctors] at h
  have H : ∀ (k : Nat) out (i : Std.Usize) o, ty_names.val.length - i.val = k →
      frontend.export_c.order_block_ctors_loop pers rst.store fuel rsd ty_names listed cts
        ctor_ix n_pd out (alloc.vec.Vec.len ty_names) i = ok o →
      SimLV (fun v => ⟨none, (absIndCtorRecs v).toArray⟩) (fun b => vOfOpt b.1) lst o
        (forIn (((absNIdxL ty_names).zip (listed.val.map absNIdxL)).drop i.val)
          (⟨none, (absIndCtorRecs out).toArray⟩ : MProd (Option VRes) (Array IndCtorRec))
          fun tn r => orderBlockStepD lsd (absU fuel) lm (absIndCtorRecs cts).toArray
            (absU n_pd) tn r.2) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro out i o hk h
      rw [frontend.export_c.order_block_ctors_loop.eq_def] at h
      by_cases hi : i < alloc.vec.Vec.len ty_names
      · rw [if_pos hi] at h
        have hi' : i.val < ty_names.val.length := by scalar_tac
        obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hn1' := vec_index_eq hi' hn1
        obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hl' : i.val < listed.val.length := by
          have := vec_index_some hv
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at this
          cases this
        have hv' := vec_index_eq hl' hv
        rw [zip_drop_cons (by simp [absNIdxL]; omega) (by simp; omega), List.forIn_cons]
        simp only [absNIdxL, List.getElem_map, hn1', hv', orderBlockStepD, bind_assoc]
        obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        refine SimLV.bind_lv (order_type_ctors_refines hrel hinv hd hx hix hr)
          (fun w hw => ?_) (fun b lv hb => ?_) (fun e he => by
            subst he; exact (Result.ok_injective h).symm)
        · subst hw
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi1v := ConRon.Refine.Nat.uadd_val hi1
          have hR := ih (ty_names.val.length - i1.val) (by simp at hi1v; omega) w i1 o rfl h
          rw [show i1.val = i.val + 1 by simp at hi1v; omega] at hR
          simp only [pure_bind]
          exact hR
        · obtain ⟨b1, j', ord⟩ := b
          rcases b1 with _ | (lv' | _) <;> simp only [vOfOpt, reduceCtorEq, Option.some.injEq] at hb
          subst hb
          exact ⟨_, rfl, rfl⟩
      · rw [if_neg hi] at h
        cases Result.ok_injective h
        rw [List.drop_eq_nil_of_le (by simp [absNIdxL]; scalar_tac), List.forIn_nil]
        rfl
  have := H _ (alloc.vec.Vec.new _) 0#usize o rfl h
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at this
  exact this

/-! ## The K flag and the recursor records -/

/-- **`k_expected_of`** — official's `is_K_target`, against `kExpectedOfD`: a
single type former with a single constructor of zero fields whose result sort
is `Prop`. -/
theorem k_expected_of_refines {pers rst lst fuel ty_types listed cts o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.k_expected_of pers rst.store fuel ty_types listed cts
      = ok o) :
    SimLR id lst o
      (kExpectedOfD (absU fuel) (absEIdxL ty_types) (listed.val.map absNIdxL)
        (absIndCtorRecs cts)) := by sorry

/-- A Rust `CheckError` reader, then a verdict-carrying continuation. -/
theorem SimLV.bind_re {α β γ δ : Type} {A : α → β} {V : β → Option RecordVerdict}
    {B : δ → γ} {lst : AState} {r : core.result.Result δ kernel.core_types.CheckError}
    {x : AM γ} {f : γ → AM β} {o}
    (hx : SimRE B lst r x) (hk : ∀ v, r = .Ok v → SimLV A V lst o (f (B v)))
    (herr : ∀ e, r = .Err e → ∃ e', o = .Err (.Err e') ∧ absAErrKind e' = absAErrKind e) :
    SimLV A V lst o (x >>= f) := by
  cases r with
  | Ok v =>
    have h1 := hk v rfl
    have hx' : x.run lst = .ok (B v, lst) := hx
    have e : (x >>= f).run lst = (f (B v)).run lst := by rw [am_run_bind', hx']; rfl
    unfold SimLV at h1 ⊢
    rw [e]; exact h1
  | Err e =>
    obtain ⟨e', rfl, hk'⟩ := herr e rfl
    have hx' : AErrSim e (x.run lst) := hx
    show AErrSim e' _
    rw [am_run_bind']
    exact AErrSim.bind (fun k hk2 => hx' k (by rw [← hk', hk2])) _

/-- `env::view_n` — the store's name view, `denoteN`'s one step. -/
theorem env_view_n_run {pers rst lst} (hrel : AStateRel₀ pers rst lst)
    {h : arena.handle.NIdx} {o}
    (hrun : arena.env.view_n pers rst.store h = ok o) :
    SimRE absNNodeView lst o (viewN (absNIdx h)) := by
  rw [arena.env.view_n] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ns] at hn
  have hn2 : n = rst.store.lss.ls.ns := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hview := nstore_view_abs hrel.store.lss.lvl.ns hv
  have hrunl : (viewN (absNIdx h)).run lst
      = match lst.store.ns.view (absNIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling name handle") := by
    show (match lst.store.ns.view (absNIdx h) with
          | some v => (pure v : AM _)
          | none => Arena.fail (.internal "arena: dangling name handle")).run lst = _
    cases lst.store.ns.view (absNIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨ce, hce, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    rw [hvc] at hview
    show AErrSim ce _
    rw [hrunl, EStore.ns, hview]
    exact AErrSim.mk rfl (by rw [env_dangling_name_kind hce]; rfl)
  | some w =>
    rw [hvc] at hrun
    cases Result.ok_injective hrun
    rw [hvc] at hview
    show _ = _
    rw [hrunl, EStore.ns, hview]
    rfl

/-- **`env::pi_sort_tele_len` refines `piSortTeleLen?`** — the Π-telescope
length of a type ending in a sort, `none` elsewhere.  A leaf of this tier. -/
theorem env_pi_sort_tele_len_run {pers rst lst fuel h' o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : arena.env.pi_sort_tele_len pers rst.store fuel h' = ok o) :
    SimRE (Option.map absU) lst o (piSortTeleLen? (absU fuel) (absEIdx h')) := by sorry

theorem char_ofNat_eq_of_ne {n : Nat} {c : Char} (h : Char.ofNat n = c) (hc : c.toNat ≠ 0) :
    n = c.toNat := by
  unfold Char.ofNat at h
  split at h
  · subst h; rfl
  · subst h; simp at hc

/-- A spelling reads back as `"rec"` exactly when it IS `rec`: `absString`
sends an invalid code point to `'\0'`, which is none of the three, so no
well-formedness is needed here. -/
theorem absString_eq_rec {s : alloc.vec.Vec Std.U32} :
    ConRon.Refine.absString s = "rec" ↔ s.val = [114#u32, 101#u32, 99#u32] := by
  constructor
  · intro h
    have h2 := congrArg String.toList h
    have hr : "rec".toList = ['r', 'e', 'c'] := by decide
    simp only [ConRon.Refine.absString, String.toList_ofList, hr] at h2
    generalize s.val = l at h2 ⊢
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
        List.nil_eq] at h2
    obtain ⟨ha, hb, hc, -⟩ := h2
    have ea := char_ofNat_eq_of_ne ha (by decide)
    have eb := char_ofNat_eq_of_ne hb (by decide)
    have ec := char_ofNat_eq_of_ne hc (by decide)
    simp only [List.cons.injEq, and_true, UScalar.eq_equiv]
    exact ⟨ea, eb, ec⟩
  · intro h
    simp only [ConRon.Refine.absString, h]
    decide

/-- `check_one_rec`'s `last == "rec"`. -/
theorem cps_beq_rec {last : alloc.vec.Vec Std.U32} {sl b}
    (hs : lift (Array.to_slice frontend.export_c.check_one_rec.R_REC) = ok sl)
    (h : frontend.text.cps_beq last sl = ok b) :
    (b = true ↔ ConRon.Refine.absString last = "rec") := by
  rw [cps_beq_val h, absString_eq_rec]
  simp only [lift, Result.ok.injEq] at hs
  subst hs
  unfold frontend.export_c.check_one_rec.R_REC
  rfl

/-- **`check_rec_indices`** — `numIndices` of `T.rec` is what is left of `T`'s
own telescope once the parameters are peeled; against `checkRecIndicesD`.
`hlen`: the two per-type lists are `tys`'s own, of one length. -/
theorem check_rec_indices_refines
    {pers rst lst fuel rn t_pre num_indices ty_names ty_types n_pd o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hlen : ty_names.val.length = ty_types.val.length)
    (h : frontend.export_c.check_rec_indices pers rst.store fuel rn t_pre
      num_indices ty_names ty_types n_pd = ok o) :
    SimLV (fun _ => ⟨none, PUnit.unit⟩) (fun b => vOfOpt b.1) lst o
      (checkRecIndicesD (absU fuel) (absNIdx rn) (absNIdx t_pre) (absU num_indices)
        (absU n_pd) ((absNIdxL ty_names).zip (absEIdxL ty_types))) := by
  rw [frontend.export_c.check_rec_indices] at h
  have H : ∀ (k : Nat) (i : Std.Usize) o, ty_names.val.length - i.val = k →
      frontend.export_c.check_rec_indices_loop pers rst.store fuel rn t_pre num_indices
        ty_names ty_types n_pd (alloc.vec.Vec.len ty_names) i = ok o →
      SimLV (fun _ => ⟨none, PUnit.unit⟩) (fun b => vOfOpt b.1) lst o
        (forIn (((absNIdxL ty_names).zip (absEIdxL ty_types)).drop i.val)
          (⟨none, PUnit.unit⟩ : MProd (Option VRes) PUnit)
          fun tt _ => recIndexStepD (absU fuel) (absNIdx rn) (absNIdx t_pre)
            (absU num_indices) (absU n_pd) tt) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i o hk h
      rw [frontend.export_c.check_rec_indices_loop.eq_def] at h
      by_cases hi : i < alloc.vec.Vec.len ty_names
      · rw [if_pos hi] at h
        have hi' : i.val < ty_names.val.length := by scalar_tac
        have hnext : ∀ i1 : Std.Usize, i + 1#usize = ok i1 →
            frontend.export_c.check_rec_indices_loop pers rst.store fuel rn t_pre num_indices
              ty_names ty_types n_pd (alloc.vec.Vec.len ty_names) i1 = ok o →
            SimLV (fun _ => ⟨none, PUnit.unit⟩) (fun b => vOfOpt b.1) lst o
              (forIn (((absNIdxL ty_names).zip (absEIdxL ty_types)).drop (i.val + 1))
                (⟨none, PUnit.unit⟩ : MProd (Option VRes) PUnit)
                fun tt _ => recIndexStepD (absU fuel) (absNIdx rn) (absNIdx t_pre)
                  (absU num_indices) (absU n_pd) tt) := by
          intro i1 hi1 h
          have hi1v := ConRon.Refine.Nat.uadd_val hi1
          have hR := ih (ty_names.val.length - i1.val) (by simp at hi1v; omega) i1 o rfl h
          rwa [show i1.val = i.val + 1 by simp at hi1v; omega] at hR
        obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hn1' := vec_index_eq hi' hn1
        rw [zip_drop_cons (by simp [absNIdxL]; omega) (by simp [absEIdxL]; omega),
          List.forIn_cons]
        simp only [absNIdxL, absEIdxL, List.getElem_map, hn1', recIndexStepD]
        obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [nidx_eq2_abs hb] at h
        by_cases hbt : (absNIdx n1 == absNIdx t_pre) = true
        · rw [if_pos hbt] at h
          rw [if_pos hbt]
          obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have he' := vec_index_eq (by omega) he
          rw [he']
          simp only [bind_assoc]
          obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          refine SimLV.bind_re (env_pi_sort_tele_len_run hrel hinv hr) (fun v hv => ?_)
            (fun e he => by subst he; exact fail_refines h)
          subst hv
          cases v with
          | none =>
            simp only [Option.map, pure_bind]
            obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            exact hnext i1 hi1 h
          | some kk =>
            simp only [Option.map]
            obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            have hi1v := ConRon.Refine.Nat.uadd_val hi1
            by_cases hne : (i1 != kk) = true
            · rw [if_pos hne] at h
              have hne' : ¬ (absU n_pd + absU num_indices == absU kk) = true := by
                simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv] at hne
                simp only [absU, beq_iff_eq]; omega
              rw [if_neg hne']
              simp only [bind_assoc, pure_bind]
              obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
              refine SimLV.bind_name (show_name_refines hrel hinv hr1) (fun v1 hv1 a1 => ?_)
                (fun e he => by subst he; exact (Result.ok_injective h).symm)
              subst hv1
              obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
              refine SimLV.bind_name (show_name_refines hrel hinv hr2) (fun v2 hv2 a2 => ?_)
                (fun e he => by subst he; exact (Result.ok_injective h).symm)
              subst hv2
              obtain ⟨i2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
              obtain ⟨_, rfl⟩ := msg_invalid_ok h
              exact SimLV.invalid (by rfl) _
            · rw [if_neg hne] at h
              have heq : (absU n_pd + absU num_indices == absU kk) = true := by
                simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv, Classical.not_not] at hne
                simp only [absU, beq_iff_eq]; omega
              rw [if_pos heq]
              simp only [pure_bind]
              obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
              exact hnext i2 hi2 h
        · rw [if_neg hbt] at h
          rw [if_neg hbt]
          simp only [pure_bind]
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          exact hnext i1 hi1 h
      · rw [if_neg hi] at h
        cases Result.ok_injective h
        rw [List.drop_eq_nil_of_le (by simp [absNIdxL, absEIdxL]; scalar_tac), List.forIn_nil]
        rfl
  have := H _ 0#usize o rfl h
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at this
  exact this

-- One of `check_one_rec`'s count checks, at the Rust field `X` against `Y`;
-- leaves the passing arm.
set_option hygiene false in
local macro "rec_count" x:term "," y:term : tactic => `(tactic| (
  by_cases hne : ($x != $y) = true
  case pos =>
    rw [if_pos hne] at h
    have hne' : ¬ (absU64 $x == absU $y) = true := by
      simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv] at hne
      simpa [absU64, absU] using hne
    rw [if_neg hne']
    obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine SimLV.bind_name (show_name_refines hrel hinv hr2) (fun v2 hv2 a2 => ?_)
      (fun e he => by subst he; exact (Result.ok_injective h).symm)
    subst hv2
    obtain ⟨_, rfl⟩ := msg_invalid_ok h
    exact SimLV.invalid (by rfl) _
  rw [if_neg hne] at h
  have heq : (absU64 $x == absU $y) = true := by
    simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv, Classical.not_not] at hne
    simpa [absU64, absU] using hne
  rw [if_pos heq]))

-- `check_one_rec`'s `T.rec` tail: the name's view, then `check_rec_indices`.
set_option hygiene false in
local macro "rec_view_tail" : tactic => `(tactic| (
  obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine SimLV.bind_re (env_view_n_run hrel hr2) (fun nv hnv => ?_)
    (fun e he => by subst he; exact fail_refines h)
  subst hnv
  cases nv with
  | Anonymous => cases Result.ok_injective h; rfl
  | Num a b => cases Result.ok_injective h; rfl
  | Str tp last =>
    obtain ⟨sl, hsl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbr := cps_beq_rec hsl hb
    simp only [absNNodeView]
    split
    · rename_i T heq
      injection heq with hT hs
      subst hT
      rw [if_pos (hbr.mpr hs)] at h
      refine SimLV.bind_lv (check_rec_indices_refines hrel hinv hlen h)
        (fun w hw => by subst hw; rfl) (fun b lv hb => ⟨_, rfl, hb⟩) (fun e he => he)
    · rename_i hnot
      have hbf : ¬ b = true := fun hbt => hnot _ (by rw [hbr.mp hbt])
      rw [if_neg hbf] at h
      cases Result.ok_injective h
      rfl))

/-- **`check_one_rec`** — the four count checks, the K flag and the indices
at one recursor record, against `checkOneRecD`. -/
theorem check_one_rec_refines
    {pers rst lst rsd lsd fuel r ty_names ty_types n_pd n_types n_ctors k_exp o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hlen : ty_names.val.length = ty_types.val.length)
    (h : frontend.export_c.check_one_rec pers rst.store fuel rsd r ty_names
      ty_types n_pd n_types n_ctors k_exp = ok o) :
    SimLV (fun _ => none) vOfOpt lst o
      (checkOneRecD lsd (absU fuel) (absNIdxL ty_names) (absEIdxL ty_types) (absU n_pd)
        (absU n_types) (absU n_ctors) k_exp (absIndRecRec r)) := by
  rw [frontend.export_c.check_one_rec] at h
  unfold checkOneRecD
  simp only [absIndRecRec]
  obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine SimLV.bind (st_name_refines hd hr1) (fun v hv => ?_)
    (fun e he => by subst he; exact (Result.ok_injective h).symm)
  subst hv
  dsimp only at h
  simp only [pure_bind]
  rec_count r.num_params, n_pd
  rec_count r.num_motives, n_types
  rec_count r.num_minors, n_ctors
  cases k_exp with
  | none => rec_view_tail
  | some kE =>
    dsimp only at h ⊢
    by_cases hk : (r.k != kE) = true
    case pos =>
      rw [if_pos hk] at h
      have hk' : ¬ (r.k == kE) = true := by simpa using hk
      rw [if_neg hk']
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine SimLV.bind_name (show_name_refines hrel hinv hr2) (fun v2 hv2 a2 => ?_)
        (fun e he => by subst he; exact (Result.ok_injective h).symm)
      subst hv2
      obtain ⟨_, rfl⟩ := msg_invalid_ok h
      exact SimLV.invalid (by rfl) _
    rw [if_neg hk] at h
    have hk' : (r.k == kE) = true := by simpa using hk
    rw [if_pos hk']
    rec_view_tail

/-- **`check_rec_records`** — the `for r in rcs` loop, against
`checkRecRecordsD` (the caller skips it at a nested block, as the twin's
`if nested then [] else rcs` does). -/
theorem check_rec_records_refines
    {pers rst lst rsd lsd fuel rcs ty_names ty_types n_pd n_types n_ctors k_exp o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hlen : ty_names.val.length = ty_types.val.length)
    (h : frontend.export_c.check_rec_records pers rst.store fuel rsd rcs ty_names
      ty_types n_pd n_types n_ctors k_exp = ok o) :
    SimLV (fun _ => ⟨none, PUnit.unit⟩) (fun b => vOfOpt b.1) lst o
      (checkRecRecordsD lsd (absU fuel) (absNIdxL ty_names) (absEIdxL ty_types) (absU n_pd)
        (absU n_types) (absU n_ctors) k_exp (absIndRecRecs rcs)) := by
  rw [frontend.export_c.check_rec_records] at h
  have H : ∀ (k : Nat) (i : Std.Usize) o, rcs.val.length - i.val = k →
      frontend.export_c.check_rec_records_loop pers rst.store fuel rsd rcs ty_names ty_types
        n_pd n_types n_ctors k_exp (alloc.vec.Vec.len rcs) i = ok o →
      SimLV (fun _ => ⟨none, PUnit.unit⟩) (fun b => vOfOpt b.1) lst o
        (forIn ((absIndRecRecs rcs).drop i.val)
          (⟨none, PUnit.unit⟩ : MProd (Option VRes) PUnit)
          fun r _ => recStepD lsd (absU fuel) (absNIdxL ty_names) (absEIdxL ty_types)
            (absU n_pd) (absU n_types) (absU n_ctors) k_exp r) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i o hk h
      rw [frontend.export_c.check_rec_records_loop.eq_def] at h
      by_cases hi : i < alloc.vec.Vec.len rcs
      · rw [if_pos hi] at h
        have hi' : i.val < rcs.val.length := by scalar_tac
        obtain ⟨irr, hirr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hirr' := vec_index_eq hi' hirr
        rw [show (absIndRecRecs rcs).drop i.val =
            absIndRecRec (rcs.val[i.val]'hi') :: (absIndRecRecs rcs).drop (i.val + 1) by
          simp only [absIndRecRecs, ← List.map_drop, List.drop_eq_getElem_cons hi',
            List.map_cons],
          List.forIn_cons, recStepD_eq, hirr']
        simp only [bind_assoc]
        obtain ⟨rc, hrc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        refine SimLV.bind_check (check_one_rec_refines hrel hinv hd hlen hrc)
          (fun hok => ?_) (fun b lv hb => ?_)
          (fun e he => by subst he; exact (Result.ok_injective h).symm)
        · subst hok
          simp only [pure_bind]
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi1v := ConRon.Refine.Nat.uadd_val hi1
          have hR := ih (rcs.val.length - i1.val) (by simp at hi1v; omega) i1 o rfl h
          rwa [show i1.val = i.val + 1 by simp at hi1v; omega] at hR
        · rcases b with _ | (lv' | _) <;> simp only [vOfOpt, reduceCtorEq, Option.some.injEq] at hb
          subst hb
          exact ⟨_, rfl, rfl⟩
      · rw [if_neg hi] at h
        cases Result.ok_injective h
        rw [List.drop_eq_nil_of_le (by simp [absIndRecRecs]; scalar_tac), List.forIn_nil]
        rfl
  have := H _ 0#usize o rfl h
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at this
  exact this

/-- **`validate_ind_d` refines `validateIndD`** (`ExportC.lean:442-539`) — the
load-bearing statement of this file: the eleven verdicts, at the same kind and
in the same order.

A READER on both sides: the port takes the store by shared reference and
returns no state, and every twin call it makes (`st.name`, `getDeclD`,
`storeFuel`, `view`, `viewN`, `readName`, `readLevel`, `indPiTeleLen`,
`piResult`, `piSortTeleLen?`) reads.  So the two answering arms end at the
state they started in — task #97-P5-Front round 2 strengthened them from
`∃ lst'`, which left `process_line_core_d`'s `ind` arm no `AStateRel` for
`install_ind_d` and no `Ext` for its verdict. -/
theorem validate_ind_d_refines {pers rst lst rsd lsd tys cts rcs o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.validate_ind_d pers rst.store rsd tys cts rcs = ok o) :
    (∀ v, o = .Ok v →
      (validateIndD lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
          (absIndRecRecs rcs)).run lst
        = .ok (.inr (absIndCtorRecs v.1, absU v.2), lst)) ∧
    (∀ e, o = .Err e →
      (∀ ce, e = .Err ce → AErrSim ce
        ((validateIndD lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
          (absIndRecRecs rcs)).run lst)) ∧
      (∀ vd, e = .Verdict vd → ∃ lv,
        (validateIndD lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
          (absIndRecRecs rcs)).run lst = .ok (.inl lv, lst) ∧
        lVerdictKind lv = absVerdictKind vd)) := by sorry

/-! ## The block's constants -/

/-- `arena::env::i_ind_caps_default` is the twin's `{}`. -/
theorem i_ind_caps_default_abs {ic : arena.env.IIndCaps}
    (h : arena.env.i_ind_caps_default = ok ic) : absIIndCaps ic = {} := by
  rw [arena.env.i_ind_caps_default] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [arena.handle.NIdx.of_word] at hn
  cases Result.ok_injective hn
  have hpwv := ConRon.Refine.PropWhen.if_all_zero_refines
    (by intro x hx; simp [alloc.vec.Vec.new] at hx) hpw
  simp only [absIIndCaps, hpwv]
  rfl

/-- **`ind_block_types`** — the twin's `tys.mapM` into `IConstantInfo.indInfo`. -/
theorem ind_block_types_refines {rsd lsd lst tys out o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_types rsd tys out = ok o) :
    SimLR absICIL lst o
      (do
        let ts ← (absIndTypeRecs tys).mapM fun t => do
          pure (IConstantInfo.indInfo (← parseCVD lsd t.cv) {})
        pure (absICIL out ++ ts)) := by
  rw [frontend.export_c.ind_block_types] at h
  have H := simLR_cursor (absY := absIConstantInfo) (absX := absIndTypeRec) (xs := tys)
    (lst := lst) (G := fun t => do pure (IConstantInfo.indInfo (← parseCVD lsd t.cv) {}))
    (loop := fun out i =>
      frontend.export_c.ind_block_types_loop rsd tys out (alloc.vec.Vec.len tys) i)
    (fun out i o hn h => by
      rw [frontend.export_c.ind_block_types_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len tys by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.ind_block_types_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len tys by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [vec_index_eq hi hx]
      have hC := parse_cv_d_refines (lst := lst) hd hr
      cases r with
      | Err e =>
        exact ⟨.Err e, SimLR.bind_err hC, Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
      | Ok cv =>
        obtain ⟨ic, hic, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        refine ⟨.Ok _, SimLR.bind_ok hC ?_, Or.inr ⟨_, out1, i1, rfl, e1, e2, h⟩⟩
        show Except.ok _ = _
        simp only [absIConstantInfo, i_ind_caps_default_abs hic])
    out 0#usize o h
  rw [show absICIL = fun v : alloc.vec.Vec arena.env.IConstantInfo =>
    v.val.map absIConstantInfo from rfl]
  simpa [show ((0#usize : Std.Usize)).val = 0 by rfl, absIndTypeRecs, absIndCtorRecs,
    absIndRecRecs] using H

/-- **`ind_block_ctors`** — the twin's `cts.mapM` into
`IConstantInfo.ctorInfo`. -/
theorem ind_block_ctors_refines {rsd lsd lst cts out o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_ctors rsd cts out = ok o) :
    SimLR absICIL lst o
      (do
        let cs ← (absIndCtorRecs cts).mapM fun c => do
          pure (IConstantInfo.ctorInfo (← parseCVD lsd c.cv) c.numParams c.numFields)
        pure (absICIL out ++ cs)) := by
  rw [frontend.export_c.ind_block_ctors] at h
  have H := simLR_cursor (absY := absIConstantInfo) (absX := absIndCtorRec) (xs := cts)
    (lst := lst)
    (G := fun c => do pure (IConstantInfo.ctorInfo (← parseCVD lsd c.cv) c.numParams c.numFields))
    (loop := fun out i =>
      frontend.export_c.ind_block_ctors_loop rsd cts out (alloc.vec.Vec.len cts) i)
    (fun out i o hn h => by
      rw [frontend.export_c.ind_block_ctors_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len cts by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.ind_block_ctors_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len cts by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [vec_index_eq hi hx]
      have hC := parse_cv_d_refines (lst := lst) hd hr
      cases r with
      | Err e =>
        exact ⟨.Err e, SimLR.bind_err hC, Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
      | Ok cv =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, e2⟩ := cursor_push hout1 hi1
        refine ⟨.Ok _, ?_, Or.inr ⟨_, out1, i1, rfl, e1, e2, h⟩⟩
        exact SimLR.bind_ok hC rfl)
    out 0#usize o h
  rw [show absICIL = fun v : alloc.vec.Vec arena.env.IConstantInfo =>
    v.val.map absIConstantInfo from rfl]
  simpa [show ((0#usize : Std.Usize)).val = 0 by rfl, absIndTypeRecs, absIndCtorRecs,
    absIndRecRecs] using H

/-- **`ind_block_recs`** — the twin's `rcs.mapM` into `IConstantInfo.recInfo`. -/
theorem ind_block_recs_refines {rsd lsd lst rcs out o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_recs rsd rcs out = ok o) :
    SimLR absICIL lst o
      (do
        let rs ← (absIndRecRecs rcs).mapM fun r => do
          let rules ← r.rules.mapM (parseRuleD lsd)
          pure (IConstantInfo.recInfo (← parseCVD lsd r.cv)
            (r.numParams + r.numMotives + r.numMinors + r.numIndices)
            (r.numParams + r.numMotives + r.numMinors) rules)
        pure (absICIL out ++ rs)) := by
  rw [frontend.export_c.ind_block_recs] at h
  have H := simLR_cursor (absY := absIConstantInfo) (absX := absIndRecRec) (xs := rcs)
    (lst := lst)
    (G := fun r => do
          let rules ← r.rules.mapM (parseRuleD lsd)
          pure (IConstantInfo.recInfo (← parseCVD lsd r.cv)
            (r.numParams + r.numMotives + r.numMinors + r.numIndices)
            (r.numParams + r.numMotives + r.numMinors) rules))
    (loop := fun out i =>
      frontend.export_c.ind_block_recs_loop rsd rcs out (alloc.vec.Vec.len rcs) i)
    (fun out i o hn h => by
      rw [frontend.export_c.ind_block_recs_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len rcs by scalar_tac)] at h
      exact (Result.ok_injective h).symm)
    (fun out i o hi h => by
      rw [frontend.export_c.ind_block_recs_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len rcs by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [vec_index_eq hi hx]
      have hN := parse_rules_d_refines (lst := lst) hd hr
      cases r with
      | Err e =>
        exact ⟨.Err e, SimLR.bind_err hN, Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
      | Ok v =>
        obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hC := parse_cv_d_refines (lst := lst) hd hr1
        cases r1 with
        | Err e =>
          exact ⟨.Err e, SimLR.bind_ok hN (SimLR.bind_err hC),
            Or.inl ⟨e, rfl, (Result.ok_injective h).symm⟩⟩
        | Ok cv =>
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨e1, e2⟩ := cursor_push hout1 hi5
          refine ⟨.Ok _, SimLR.bind_ok hN (SimLR.bind_ok hC ?_),
            Or.inr ⟨_, out1, i5, rfl, e1, e2, h⟩⟩
          show Except.ok _ = _
          have v1 := ConRon.Refine.Nat.uadd_val hi1
          have v2 := ConRon.Refine.Nat.uadd_val hi2
          have v3 := ConRon.Refine.Nat.uadd_val hi3
          have v4 := ConRon.Refine.Nat.uadd_val hi4
          simp only [absIConstantInfo, absIndRecRec, absU, absU64, v1, v2, v3, v4]
          rfl)
    out 0#usize o h
  rw [show absICIL = fun v : alloc.vec.Vec arena.env.IConstantInfo =>
    v.val.map absIConstantInfo from rfl]
  simpa [show ((0#usize : Std.Usize)).val = 0 by rfl, absIndTypeRecs, absIndCtorRecs,
    absIndRecRecs] using H

/-- An accumulating reader, then another: the twin's `pre ++ cs ++ rs` from the
two halves' own `SimLR`s (the second stated at the first's answer). -/
theorem SimLR.seq_append {Y β : Type} {A : alloc.vec.Vec Y → List β} {lst : AState}
    {r1 o : core.result.Result (alloc.vec.Vec Y) frontend.export_c.LineErr}
    {pre : List β} {M N : AM (List β)}
    (h1 : SimLR A lst r1 (do let cs ← M; pure (pre ++ cs)))
    (h2 : ∀ b2, r1 = .Ok b2 → SimLR A lst o (do let rs ← N; pure (A b2 ++ rs)))
    (herr : ∀ e, r1 = .Err e → o = .Err e) :
    SimLR A lst o (do let cs ← M; let rs ← N; pure (pre ++ cs ++ rs)) := by
  cases r1 with
  | Err e =>
    obtain rfl := herr e rfl
    simp only [SimLR] at h1 ⊢
    rw [am_run_bind'] at h1 ⊢
    cases hM : M.run lst with
    | error le => rw [hM] at h1; exact h1
    | ok p =>
      rw [hM] at h1
      cases e with
      | Verdict v => exact h1.elim
      | Err ce =>
        intro k hk
        obtain ⟨le, hle, -⟩ := h1 k hk
        cases hle
  | Ok b2 =>
    have h2' := h2 b2 rfl
    simp only [SimLR] at h1
    rw [am_run_bind'] at h1
    cases hM : M.run lst with
    | error le => rw [hM] at h1; cases h1
    | ok p =>
      rw [hM] at h1
      obtain ⟨cs, lst1⟩ := p
      have h1' : (Except.ok (pre ++ cs, lst1) : Except Arena.CheckError _) =
          Except.ok (A b2, lst) := h1
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1'
      obtain ⟨hA, rfl⟩ := h1'
      have hrun : ((do let cs ← M; let rs ← N; pure (pre ++ cs ++ rs)) : AM _).run lst1
          = ((do let rs ← N; pure (A b2 ++ rs)) : AM _).run lst1 := by
        rw [am_run_bind', hM]
        show ((do let rs ← N; pure (pre ++ cs ++ rs)) : AM _).run lst1 = _
        rw [← hA]
      cases o with
      | Ok w => show _ = _; rw [hrun]; exact h2'
      | Err e => show ALineErrSim e _; rw [hrun]; exact h2'

/-- **`ind_block_of`** — the twin's `types ++ ctors ++ recs`. -/
theorem ind_block_of_refines {rsd lsd lst tys cts rcs o} (hd : StateDRel rsd lsd)
    (h : frontend.export_c.ind_block_of rsd tys cts rcs = ok o) :
    SimLR absICIL lst o
      (do
        let ts ← (absIndTypeRecs tys).mapM fun t => do
          pure (IConstantInfo.indInfo (← parseCVD lsd t.cv) {})
        let cs ← (absIndCtorRecs cts).mapM fun c => do
          pure (IConstantInfo.ctorInfo (← parseCVD lsd c.cv) c.numParams c.numFields)
        let rs ← (absIndRecRecs rcs).mapM fun r => do
          let rules ← r.rules.mapM (parseRuleD lsd)
          pure (IConstantInfo.recInfo (← parseCVD lsd r.cv)
            (r.numParams + r.numMotives + r.numMinors + r.numIndices)
            (r.numParams + r.numMotives + r.numMinors) rules)
        pure (ts ++ cs ++ rs)) := by
  rw [frontend.export_c.ind_block_of] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := ind_block_types_refines (lst := lst) hd hr
  have e0 : absICIL (alloc.vec.Vec.new arena.env.IConstantInfo) = [] := rfl
  rw [e0] at h1
  simp only [List.nil_append, bind_pure] at h1
  cases r with
  | Err e => cases Result.ok_injective h; exact SimLR.bind_err h1
  | Ok b =>
    refine SimLR.bind_ok h1 ?_
    obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 := ind_block_ctors_refines (lst := lst) hd hr1
    refine SimLR.seq_append h2 (fun b2 hb2 => ?_) (fun e he => ?_)
    · subst hb2
      exact ind_block_recs_refines hd h
    · subst he
      exact (Result.ok_injective h).symm

/-- **`note_ind_blocks`** — the twin's `b.types.foldl` into `indBlocks`.  The
port copies the block per member type name where con-leche shares one value
(§8.5 has no `ron::ptr`); a block is shape data and the copy is on the parse
path only. -/
theorem note_ind_blocks_refines {rsd lsd b rsd'} (hd : StateDRel rsd lsd)
    (hi : StateDInv rsd)
    (h : frontend.export_c.note_ind_blocks rsd b = ok rsd') :
    StateDRel rsd'
      { lsd with indBlocks := (absBlockRec b).types.foldl
                   (fun m t => m.insert t.cv.name (absBlockRec b)) lsd.indBlocks } ∧
      StateDInv rsd' := by sorry

/-! ## The install and the modeller seam -/

/-- **`quot_kind_of`** — the quotient record's `kind` spelling, against the
twin's four-way `match`.  Needs `StrWF`: `absString` sends an invalid code
point to `'\0'`, so without it the port's `text::cps_beq` against `"type"` can
disagree with the twin's `String` match IN THE REJECTING DIRECTION (task #87
§8's `DeclRecStrWF` finding). -/
theorem quot_kind_of_refines {k o} (hs : ConRon.Refine.StrWF k)
    (h : frontend.export_c.quot_kind_of k = ok o) :
    o.map ConRon.Refine.absQuotKind =
      (match ConRon.Refine.absString k with
       | "type" => some ConLeche.QuotKind.type
       | "ctor" => some ConLeche.QuotKind.ctor
       | "lift" => some ConLeche.QuotKind.lift
       | "ind" => some ConLeche.QuotKind.ind
       | _ => none) := by
  rw [frontend.export_c.quot_kind_of] at h
  simp only [lift, bind_tc_ok] at h
  have tst : ∀ {n : Std.Usize} (K : Std.Array Std.U32 n) (L : List Std.U32) (w : String),
      K.to_slice.val = L → (∀ c ∈ L, Nat.isValidChar c.val) →
      String.ofList (L.map fun c => Char.ofNat c.val) = w →
      ∀ b, frontend.text.cps_beq k K.to_slice = ok b →
        (b = true ↔ ConRon.Refine.absString k = w) := by
    intro n K L w hK hL hw b hb
    rw [cps_beq_str hs (by rw [hK]; exact hL) hb, hK, hw]
  have eT := tst frontend.export_c.quot_kind_of.K_TYPE [116#u32, 121#u32, 112#u32, 101#u32]
    "type" (by unfold frontend.export_c.quot_kind_of.K_TYPE; rfl) (by decide) rfl
  have eC := tst frontend.export_c.quot_kind_of.K_CTOR [99#u32, 116#u32, 111#u32, 114#u32]
    "ctor" (by unfold frontend.export_c.quot_kind_of.K_CTOR; rfl) (by decide) rfl
  have eL := tst frontend.export_c.quot_kind_of.K_LIFT [108#u32, 105#u32, 102#u32, 116#u32]
    "lift" (by unfold frontend.export_c.quot_kind_of.K_LIFT; rfl) (by decide) rfl
  have eI := tst frontend.export_c.quot_kind_of.K_IND [105#u32, 110#u32, 100#u32]
    "ind" (by unfold frontend.export_c.quot_kind_of.K_IND; rfl) (by decide) rfl
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hT := eT _ hb
  split at h
  · rename_i hb1
    cases Result.ok_injective h
    rw [hT.mp hb1]; rfl
  · rename_i hb1
    have nT : ConRon.Refine.absString k ≠ "type" := fun e => hb1 (hT.mpr e)
    obtain ⟨b1, hb1', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hC := eC _ hb1'
    split at h
    · rename_i hc
      cases Result.ok_injective h
      rw [hC.mp hc]; rfl
    · rename_i hc
      have nC : ConRon.Refine.absString k ≠ "ctor" := fun e => hc (hC.mpr e)
      obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hL := eL _ hb2
      split at h
      · rename_i hl
        cases Result.ok_injective h
        rw [hL.mp hl]; rfl
      · rename_i hl
        have nL : ConRon.Refine.absString k ≠ "lift" := fun e => hl (hL.mpr e)
        obtain ⟨b3, hb3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hI := eI _ hb3
        split at h
        · rename_i hi
          cases Result.ok_injective h
          rw [hI.mp hi]; rfl
        · rename_i hi
          have nI : ConRon.Refine.absString k ≠ "ind" := fun e => hi (hI.mpr e)
          cases Result.ok_injective h
          split <;> simp_all

/-- **`install_gen`** — the modeller arm of `installIndD`, split for the
loop-exit reason.  It is where `ModellerRefines` is consumed: the port's
`m.generate` against the twin's `md.generate`, at `state_model_ctx`'s
context. -/
theorem install_gen_refines {G : Type} {inst : frontend.types.Modeller G} {m : G}
    {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd block n_pd t0 b o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.install_gen inst pers m rst rsd block n_pd t0 b = ok o) :
    SimDV pers lst o
      (installGen lmd lsd (absICIL block) (absU n_pd) (absNIdx t0)
        (absBlockRec b)) := by sorry

/-- The tail of `install_ind_d` past `T0`: the block record, the table write,
and the modeller or the push. -/
theorem install_ind_tail {G : Type} {inst : frontend.types.Modeller G} {m : G}
    {lmd : Arena.Frontend.Modeller} {pers rst2 lst2 st1 lsd1 tys cts rcs v n_pd t0 o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel₀ pers rst2 lst2) (hinv : AStateInv pers rst2)
    (hd : StateDRel st1 lsd1) (hi : StateDInv st1)
    (h : (do
      let r2 ← frontend.export_c.block_rec_of st1 tys cts rcs
      match r2 with
      | core.result.Result.Ok v1 =>
        let st2 ← frontend.export_c.note_ind_blocks st1 v1
        if st2.in_model
        then
          let b ← frontend.types.wants v1
          if b
          then frontend.export_c.install_gen inst pers m rst2 st2 v n_pd t0 v1
          else
            let (r3, e, st3) ← frontend.export_c.push_decl pers rst2.store st2
                (arena.env.IDeclaration.IndDecl v n_pd)
            ok (r3, { rst2 with store := e }, st3)
        else
          let (r3, e, st3) ← frontend.export_c.push_decl pers rst2.store st2
              (arena.env.IDeclaration.IndDecl v n_pd)
          ok (r3, { rst2 with store := e }, st3)
      | core.result.Result.Err e => ok (core.result.Result.Err e, rst2, st1)) = ok o) :
    SimDV pers lst2 o (do
      let b ← blockRecOf lsd1 (absIndTypeRecs tys) (absIndCtorRecs cts) (absIndRecRecs rcs)
      let st := noteIndBlocks lsd1 b
      if st.inModel && wants b then installGen lmd st (absICIL v) (absU n_pd) (absNIdx t0) b
      else return .inl (← pushDecl st (.indDecl (absICIL v) (absU n_pd)))) := by
  obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hBR := block_rec_of_refines (lst := lst2) hd hr2
  cases r2 with
  | Err e =>
    cases Result.ok_injective h
    exact SimDV.of_bind hBR (am_run_bind' _ _ _)
  | Ok v1 =>
    refine SimDV.bind_ok hBR ?_
    obtain ⟨st2, hst2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hd2, hi2⟩ := note_ind_blocks_refines hd hi hst2
    have hIM : (noteIndBlocks lsd1 (absBlockRec v1)).inModel = st2.in_model := hd2.inModel
    have push : ∀ {o}, (do
        let (r3, e, st3) ← frontend.export_c.push_decl pers rst2.store st2
            (arena.env.IDeclaration.IndDecl v n_pd)
        ok (r3, { rst2 with store := e }, st3)) = ok o →
        SimDV pers lst2 o (do
          pure (Sum.inl (← pushDecl (noteIndBlocks lsd1 (absBlockRec v1))
            (.indDecl (absICIL v) (absU n_pd))))) := by
      intro o h
      obtain ⟨⟨r3, e, st3⟩, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      exact SimD.toSimDV_inl (push_decl_refines hrel hinv hd2 hi2 hp)
    by_cases him : st2.in_model = true
    · rw [if_pos him] at h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hw := wants_refines hb
      by_cases hbt : b = true
      · rw [if_pos hbt] at h
        have hc : ((noteIndBlocks lsd1 (absBlockRec v1)).inModel && wants (absBlockRec v1))
            = true := by rw [hIM, ← hw, him, hbt]; rfl
        simp only [hc, if_true]
        exact install_gen_refines hmr hrel hinv hd2 hi2 h
      · rw [if_neg hbt] at h
        have hc : ((noteIndBlocks lsd1 (absBlockRec v1)).inModel && wants (absBlockRec v1))
            = false := by
          rw [hIM, ← hw, him]; simpa using hbt
        simp only [hc, Bool.false_eq_true, if_false]
        exact push h
    · rw [if_neg him] at h
      have hc : ((noteIndBlocks lsd1 (absBlockRec v1)).inModel && wants (absBlockRec v1))
          = false := by
        rw [hIM]; simp only [Bool.not_eq_true] at him; rw [him]; rfl
      simp only [hc, Bool.false_eq_true, if_false]
      exact push h

/-- **`install_ind_d` refines `installIndD`** (`ExportC.lean:549-594`) — every
change to the state a validated inductive record makes. -/
theorem install_ind_d_refines {G : Type} {inst : frontend.types.Modeller G} {m : G}
    {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd tys cts rcs n_pd o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.install_ind_d inst pers m rst rsd tys cts rcs n_pd
      = ok o) :
    SimDV pers lst o
      (installIndD lmd lsd (absIndTypeRecs tys) (absIndCtorRecs cts)
        (absIndRecRecs rcs) (absU n_pd)) := by
  rw [installIndD_unfold]
  rw [frontend.export_c.install_ind_d] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hB := ind_block_of_refines (lst := lst) hd hr
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact SimDV.of_bind hB (am_run_bind' _ _ _)
  | Ok v =>
    refine SimDV.bind_ok (show (indBlockOf lsd _ _ _).run lst = _ from hB) ?_
    obtain ⟨⟨r1, ar1, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hR := register_proj_owners_refines hrel hinv hd hi h1
    cases r1 with
    | Err e =>
      cases Result.ok_injective h
      exact SimDV.of_bind hR (am_run_bind' _ _ _)
    | Ok u =>
      obtain ⟨lsd1, lst1, hx1, hd1, hi1, hrel1, hinv1⟩ := hR
      refine SimDV.bind_ok hx1 ?_
      rcases ConRon.Refine.HashMap2.ite_eq_ok h with ⟨hlen, h⟩ | ⟨hlen, h⟩
      · have hnil : (absICIL v).head? = none := by
          have : v.val.length = 0 := by scalar_tac
          simp [absICIL, List.length_eq_zero_iff.mp this]
        obtain ⟨⟨r2, e⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hN := ConRon.Refine2.intern_n_node_run₀ hrel1 hinv1 .Anonymous trivial
          (o := (r2, { ar1 with store := e }))
          (by rw [arena.monad.intern_n_node, h2]; simp only [bind_tc_ok]; rfl)
        simp only [hnil]
        rw [show Arena.internNNode NNodeView.anonymous
            = Arena.internNNode (absNNodeView arena.store.NNodeView.Anonymous) from rfl]
        cases r2 with
        | Err e2 =>
          obtain ⟨r3, hr3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases Result.ok_injective h
          obtain ⟨e', rfl, hk⟩ := fail_refines hr3
          show AErrSim e' _
          rw [am_run_bind']
          exact AErrSim.of_kind (AErrSim.bind (Sim₀.apply_err hN) _) hk
        | Ok h0 =>
          obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hN
          refine SimDV.bind_ok hx2 ?_
          exact install_ind_tail hmr hrel2 hinv2 hd1 hi1 h
      · obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨t0, ht0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hhd : (absICIL v).head? = some (absIConstantInfo ii) := by
          have h1 := vec_index_some hii
          simp only [show ((0#usize : Std.Usize)).val = 0 from rfl] at h1
          simp only [absICIL, List.head?_map]
          rw [List.head?_eq_getElem?, h1]; rfl
        simp only [hhd]
        refine SimDV.bind_ok (a := absNIdx t0) (by rw [i_constant_info_name_abs ht0]; rfl) ?_
        exact install_ind_tail hmr hrel1 hinv1 hd1 hi1 h

end ConRon.Refine2.Frontend
