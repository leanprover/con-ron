/-
# `ConRon.Refine2.Frontend.Olean.Files` — where a module's files are

**Task #142, Theorem 2.**  `olean/files.rs`'s lookup of a module's root against the twin's
`holdsRoot`, `rootHits`, `rootAt` and `findModule`, and one file's read against `readPartOr`.  A
function that reaches a file read claims its accept (`FsRel`).

`one_each`, `real_seen`, `dirs_text`, `olean_failed`, `part_failed` carry no theorem: they
build the messages of failures, and a message is not compared.
-/
import ConRon.Refine2.Frontend.Olean.ModFilesRel
import ConRon.Refine2.Frontend.Olean.Region

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.files
open frontend.olean.region (part_of_bytes)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Refine (absString absName StrWF NameWF vec_push_val)
open ConRon.Refine2.Lockstep (LSP)
open ConRon.Refine2 (AErrKind absAErrKind)
open Arena.Frontend.Olean (holdsRoot rootHits rootAt findModule)

/-! ## The relations -/

theorem vec_len_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.len v).val = v.val.length := by
  simp

/-- A location, as upstream's. -/
def absLocated (l : Located) : ConLeche.Frontend.Olean.Located :=
  ⟨⟨absString l.dir⟩⟩

/-- A directory, as the twin's. -/
abbrev absDir (d : alloc.vec.Vec Std.U32) : System.FilePath := ⟨absString d⟩

/-- `Err` at kind `internal`, whatever precedes it. -/
macro "internal_tail" h:ident " as " p:rcasesPat : tactic => `(tactic|
  (obtain $p:rcasesPat := (show LSP _ (fun o => ∃ e, o = .Err e ∧ absAErrKind e = some .internal) from by err_tail) _ $h:ident))

/-! ## The literals -/

theorem abs_olean_lit {M : Std.Array Std.U32 5#usize} {s v}
    (hM : (Std.Array.to_slice M).val.map (fun c => Char.ofNat c.val) = ['o', 'l', 'e', 'a', 'n'])
    (hs : lift (Std.Array.to_slice M) = ok s) (hv : kernel.core_types.code_points s = ok v) :
    absString v = "olean" := by
  cases Result.ok_injective (show ok _ = ok s from hs)
  have ev := ConRon.Refine.code_points_val hv
  rw [absString, ev, hM]

theorem abs_server_lit {M : Std.Array Std.U32 12#usize} {s v}
    (hM : (Std.Array.to_slice M).val.map (fun c => Char.ofNat c.val) =
      ['o', 'l', 'e', 'a', 'n', '.', 's', 'e', 'r', 'v', 'e', 'r'])
    (hs : lift (Std.Array.to_slice M) = ok s) (hv : kernel.core_types.code_points s = ok v) :
    absString v = "olean.server" := by
  cases Result.ok_injective (show ok _ = ok s from hs)
  have ev := ConRon.Refine.code_points_val hv
  rw [absString, ev, hM]

theorem abs_private_lit {M : Std.Array Std.U32 13#usize} {s v}
    (hM : (Std.Array.to_slice M).val.map (fun c => Char.ofNat c.val) =
      ['o', 'l', 'e', 'a', 'n', '.', 'p', 'r', 'i', 'v', 'a', 't', 'e'])
    (hs : lift (Std.Array.to_slice M) = ok s) (hv : kernel.core_types.code_points s = ok v) :
    absString v = "olean.private" := by
  cases Result.ok_injective (show ok _ = ok s from hs)
  have ev := ConRon.Refine.code_points_val hv
  rw [absString, ev, hM]

/-- Whatever precedes it, a tail that ends in an `Err`. -/
macro "err_any" : tactic => `(tactic| (
  repeat' first
    | exact fun _ h => ⟨_, (Result.ok_injective h).symm⟩
    | (refine ConRon.Refine2.Lockstep.LSP.bind_eq fun _ _ => ?_)))

theorem not_ok_of_err {α : Type} {m : Result (core.result.Result α kernel.core_types.CheckError)} {a}
    (hm : LSP m (fun o => ∃ e, o = .Err e)) : m ≠ ok (.Ok a) := by
  intro h
  obtain ⟨_, he⟩ := hm _ h
  cases he

/-! ## A name's root -/

/-- **`name_root` is `Name.root`.** -/
theorem name_root_eq : ∀ (n : kernel.name.Name) {r : kernel.name.Name},
    name_root n = ok r → absName r = (absName n).root
  | .mk (.mk h k), r, hr => by
    rw [name_root] at hr
    simp only [ConRon.Refine.bind_arc_deref] at hr
    cases k with
    | Anonymous =>
      rw [ConRon.Refine.Name.anonymous_refines hr]
      simp [ConLeche.Name.root]
    | Str p s =>
      obtain ⟨⟨h', k'⟩⟩ := p
      cases k' with
      | Anonymous =>
        peel hr as n1, hn1
        peel hr as v, hv
        rw [ConRon.Refine.Name.mk_str_refines hr, ConRon.Refine.Name.anonymous_refines hn1,
          ConRon.Refine.Expr.str_copy_eq hv]
        simp [ConLeche.Name.root]
      | Str p' s' =>
        rw [name_root_eq _ hr]
        simp [ConLeche.Name.root]
      | Num p' k'' =>
        rw [name_root_eq _ hr]
        simp [ConLeche.Name.root]
    | Num p j =>
      obtain ⟨⟨h', k'⟩⟩ := p
      cases k' with
      | Anonymous =>
        peel hr as n1, hn1
        rw [ConRon.Refine.Name.mk_num_refines hr, ConRon.Refine.Name.anonymous_refines hn1]
        simp [ConLeche.Name.root]
      | Str p' s' =>
        rw [name_root_eq _ hr]
        simp [ConLeche.Name.root]
      | Num p' k'' =>
        rw [name_root_eq _ hr]
        simp [ConLeche.Name.root]

/-! ## `mod_file`'s side of a request -/

theorem mod_file_name {pers ar d m e p} (h : mod_file pers ar d m e = ok (.Ok p)) :
    ∃ n, arena.env.read_name pers ar m = ok (.Ok n) := by
  rw [mod_file] at h
  peel h as r, hr
  cases r with
  | Ok n => exact ⟨n, hr⟩
  | Err e => cases Result.ok_injective h

theorem pathRel_of {pers ar m n} {d e p : alloc.vec.Vec Std.U32}
    (hn : arena.env.read_name pers ar m = ok (.Ok n)) (h : mod_file pers ar d m e = ok (.Ok p)) :
    PathRel p (ConLeche.Frontend.Olean.modFile ⟨absString d⟩ (absName n) (absString e)) := by
  rw [mod_file, hn] at h
  simp only [bind_ok] at h
  peel h as v, hv
  cases Result.ok_injective h
  exact Or.inl ⟨d, n, e, hv, rfl⟩

/-! ## The search -/

section search

variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pers : arena.store.PersTier} {ar : arena.store.EStore} {m : arena.handle.NIdx}
  {n : kernel.name.Name}

/-- **`holds_root`'s accept is the twin's `holdsRoot`.** -/
theorem holds_root_ok {r : kernel.name.Name} {d : alloc.vec.Vec Std.U32} {b : Bool}
    (hfs : FsRel inst fsv fs) (h : holds_root inst fsv r d = ok (.Ok b)) :
    holdsRoot fs (absName r) (absDir d) = .ok b := by
  rw [holds_root] at h
  peel h as v, hv
  have hrel1 : PathRel v (ConLeche.Frontend.Olean.modDir (absDir d) (absName r)) :=
    Or.inr (Or.inl ⟨d, r, hv, rfl⟩)
  peel h as r1, hr1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok b1 =>
    have e1 := hfs.isDir hrel1 b1 hr1
    dsimp only at h
    by_cases hb : b1 = true
    · rw [ite_eq_left hb] at h
      cases Result.ok_injective h
      subst hb
      simp only [holdsRoot, e1]
      rfl
    · rw [ite_eq_right hb] at h
      peel h as s0, hs0
      peel h as v1, hv1
      have ev : absString v1 = "olean" := abs_olean_lit (by unfold holds_root.M; decide) hs0 hv1
      peel h as v2, hv2
      have hrel2 : PathRel v2 (ConLeche.Frontend.Olean.modFile (absDir d) (absName r) "olean") :=
        Or.inl ⟨d, r, v1, hv2, by rw [ev]⟩
      have e2 := hfs.pathExists hrel2 b h
      have hb' : b1 = false := by simpa using hb
      subst hb'
      simp only [holdsRoot, e1, e2]
      rfl

/-- The twin's step over one search-path directory. -/
@[reducible] def heldStep (fs : Arena.Frontend.Olean.OleanFs) (r : ConLeche.Name)
    (d : System.FilePath) : Except String (System.FilePath × Bool) := do
  return (d, ← holdsRoot fs r d)

theorem root_dirs_loop_ok {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {r : kernel.name.Name}
    (hfs : FsRel inst fsv fs) (out : alloc.vec.Vec (alloc.vec.Vec Std.U32)) (i : Std.Usize) {o}
    (h : root_dirs_loop inst fsv sp r out i = ok (.Ok o)) :
    ∃ held, ((absSearchPath sp).drop i.val).mapM (heldStep fs (absName r)) = .ok held ∧
      o.val.map absDir = out.val.map absDir ++ (held.filter (·.2)).map (·.1) := by
  rw [root_dirs_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len sp
  · rw [ite_eq_left hlt] at h
    peel h as v, hv
    obtain ⟨hi, rfl⟩ := vec_index_eq hv
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok b =>
      have e1 := holds_root_ok hfs hr1
      dsimp only at h
      peel h as out1, ho1
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have eo : out1.val.map absDir = out.val.map absDir ++
          (if b then [absDir sp.val[i.val]] else []) := by
        by_cases hb : b = true
        · rw [ite_eq_left hb] at ho1
          peel ho1 as c, hc
          rw [vec_push_val ho1, ConRon.Refine.Expr.str_copy_eq hc]
          simp [hb]
        · rw [ite_eq_right hb] at ho1
          cases Result.ok_injective ho1
          simp [hb]
      obtain ⟨held, hh, e⟩ := root_dirs_loop_ok hfs out1 i2 h
      rw [hi2v] at hh
      refine ⟨(absDir sp.val[i.val], b) :: held, ?_, ?_⟩
      · have hd : (absSearchPath sp).drop i.val =
            absDir sp.val[i.val] :: (absSearchPath sp).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa [absSearchPath] using hi)]
          simp [absSearchPath]
        rw [hd, List.mapM_cons]
        simp only [heldStep, e1] at hh ⊢
        rw [hh]
        rfl
      · rw [e, eo]
        by_cases hb : b = true <;> simp [hb]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : sp.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len sp).val := hlt
      rw [vec_len_val] at this; omega
    refine ⟨[], ?_, by simp⟩
    rw [List.drop_of_length_le (by simpa [absSearchPath] using hle)]
    rfl
termination_by sp.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len sp).val := hlt
  rw [vec_len_val] at this
  omega

/-- The twin's real path of one directory holding the root. -/
@[reducible] def realStep (fs : Arena.Frontend.Olean.OleanFs) (d : System.FilePath) :
    Except String (System.FilePath × System.FilePath) := do
  return (d, ← fs.realPath d)

theorem real_paths_loop_ok {hits : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (hfs : FsRel inst fsv fs) (out : alloc.vec.Vec (alloc.vec.Vec Std.U32)) (i : Std.Usize) {o}
    (hw : ∀ x ∈ out.val, StrWF x)
    (h : real_paths_loop inst fsv hits out i = ok (.Ok o)) :
    ∃ ys, ((hits.val.map absDir).drop i.val).mapM (realStep fs) = .ok ys ∧
      o.val.map absDir = out.val.map absDir ++ ys.map (·.2) ∧
      ys.map (·.1) = (hits.val.map absDir).drop i.val ∧ ∀ x ∈ o.val, StrWF x := by
  rw [real_paths_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len hits
  · rw [ite_eq_left hlt] at h
    peel h as v, hv
    obtain ⟨hi, rfl⟩ := vec_index_eq hv
    peel h as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective h
    | Ok rp =>
      obtain ⟨e1, hwr⟩ := hfs.realPath (Or.inr (Or.inr rfl)) rp hr1
      dsimp only at h
      peel h as out1, ho1
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have ev := vec_push_val ho1
      have hw1 : ∀ x ∈ out1.val, StrWF x := by
        rw [ev]; intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hw x hx
        · rw [List.mem_singleton.mp hx]; exact hwr
      obtain ⟨ys, hys, e2, e3, hw2⟩ := real_paths_loop_ok hfs out1 i2 hw1 h
      rw [hi2v] at hys e3
      have hd : (hits.val.map absDir).drop i.val =
          absDir hits.val[i.val] :: (hits.val.map absDir).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hi)]
        simp
      refine ⟨(absDir hits.val[i.val], absDir rp) :: ys, ?_, ?_, ?_, hw2⟩
      · rw [hd, List.mapM_cons]
        simp only [realStep, e1] at hys ⊢
        rw [hys]
        rfl
      · rw [e2, ev]; simp
      · rw [hd]; simp [e3]
  · rw [ite_eq_right hlt] at h
    cases Result.ok_injective h
    have hle : hits.val.length ≤ i.val := by
      have : ¬ i.val < (alloc.vec.Vec.len hits).val := hlt
      rw [vec_len_val] at this; omega
    refine ⟨[], ?_, by simp, ?_, hw⟩
    · rw [List.drop_of_length_le (by simpa using hle)]; rfl
    · rw [List.drop_of_length_le (by simpa using hle)]; rfl
termination_by hits.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len hits).val := hlt
  rw [vec_len_val] at this
  omega

theorem all_same_loop_eq {reals : alloc.vec.Vec (alloc.vec.Vec Std.U32)} (i : Std.Usize)
    (hw : ∀ x ∈ reals.val, StrWF x) (h : all_same_loop reals i = ok true) :
    ∀ (j : Nat) (hj : j < reals.val.length), i.val ≤ j → (hz : 0 < reals.val.length) →
      absString reals.val[j] = absString reals.val[0] := by
  rw [all_same_loop] at h
  by_cases hlt : i < alloc.vec.Vec.len reals
  · rw [ite_eq_left hlt] at h
    peel h as v, hv
    obtain ⟨hi, rfl⟩ := vec_index_eq hv
    peel h as v1, hv1
    obtain ⟨h0, rfl⟩ := vec_index_eq hv1
    peel h as b, hb
    have eb := ConRon.Refine.Name.str_eq_refines (hw _ (List.getElem_mem hi))
      (hw _ (List.getElem_mem h0)) hb
    by_cases hc : b = true
    · rw [ite_eq_left hc] at h
      peel h as i2, hi2
      have hi2v : i2.val = i.val + 1 := by rw [ConRon.Refine.Nat.uadd_val hi2]; rfl
      have ih := all_same_loop_eq i2 hw h
      intro j hj hij hz
      rcases Nat.lt_or_ge j (i.val + 1) with hl | hl
      · have : j = i.val := by omega
        subst this
        rw [hc] at eb
        exact of_decide_eq_true eb.symm
      · exact ih j hj (by omega) hz
    · rw [ite_eq_right hc] at h
      cases Result.ok_injective h
  · intro j hj hij hz
    have : ¬ i.val < (alloc.vec.Vec.len reals).val := hlt
    rw [vec_len_val] at this; omega
termination_by reals.val.length - i.val
decreasing_by
  have : i.val < (alloc.vec.Vec.len reals).val := hlt
  rw [vec_len_val] at this
  omega

/-- Upstream's `oneEach` of directories of one real path keeps the first. -/
theorem oneEach_same {d x : System.FilePath} {rest : List (System.FilePath × System.FilePath)}
    (h : ∀ y ∈ rest, y.2 = x) : ConLeche.Frontend.Olean.oneEach ((d, x) :: rest) = [d] := by
  unfold ConLeche.Frontend.Olean.oneEach
  suffices hs : ∀ (l : List (System.FilePath × System.FilePath)), (∀ y ∈ l, y.2 = x) →
      l.foldl (fun (acc : Array (System.FilePath × System.FilePath)) d =>
        if acc.any (·.2 == d.2) then acc else acc.push d) #[(d, x)] = #[(d, x)] by
    simp only [List.foldl_cons]
    have e0 : (if (#[] : Array (System.FilePath × System.FilePath)).any (·.2 == x) then #[]
        else (#[] : Array (System.FilePath × System.FilePath)).push (d, x)) = #[(d, x)] := by simp
    simp only [e0]
    rw [hs rest h]
    rfl
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y l ih =>
    intro hl
    simp only [List.foldl_cons]
    have hy : y.2 = x := hl y List.mem_cons_self
    have e : (if (#[(d, x)] : Array _).any (·.2 == y.2) then #[(d, x)] else #[(d, x)].push y) =
        #[(d, x)] := by simp [hy]
    rw [e]
    exact ih fun z hz => hl z (List.mem_cons_of_mem _ hz)

/-- **`root_hits`' directory is the twin's `rootHits`'.** -/
theorem root_hits_ok {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {r : kernel.name.Name}
    {d : alloc.vec.Vec Std.U32} (hfs : FsRel inst fsv fs)
    (h : root_hits inst fsv sp r = ok (.Ok (.Dir d))) :
    rootHits fs (absSearchPath sp) (absName r) = .ok (.dir (absDir d)) := by
  rw [root_hits] at h
  peel h as r1, hr1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok hits =>
    obtain ⟨held, hh, e⟩ := root_dirs_loop_ok hfs _ _ hr1
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hh
    have e' : (held.filter (·.2)).map (·.1) = hits.val.map absDir := by rw [e]; rfl
    dsimp only at h
    have hR : rootHits fs (absSearchPath sp) (absName r) =
        (match (held.filter (·.2)).map (·.1) with
          | [] => .ok .missing
          | [d] => .ok (.dir d)
          | hits@(d :: _) => do
            match ConLeche.Frontend.Olean.oneEach (← hits.mapM (realStep fs)) with
            | [_] => return .dir d
            | locs => return .twice locs) := by
      simp only [rootHits, hh]
      rfl
    rw [hR, e']
    by_cases h0 : alloc.vec.Vec.len hits = 0#usize
    · rw [ite_eq_left h0] at h
      cases Result.ok_injective h
    rw [ite_eq_right h0] at h
    have hne : hits.val ≠ [] := by
      intro he; apply h0; apply UScalar.eq_of_val_eq; rw [vec_len_val, he]; rfl
    by_cases h1 : alloc.vec.Vec.len hits = 1#usize
    · rw [ite_eq_left h1] at h
      peel h as v, hv
      obtain ⟨hi, rfl⟩ := vec_index_eq hv
      peel h as v1, hv1
      cases Result.ok_injective h
      rw [ConRon.Refine.Expr.str_copy_eq hv1]
      have hl : hits.val.length = 1 := by
        have := congrArg UScalar.val h1
        rw [vec_len_val] at this; simpa using this
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
      have h0 : hits.val[(0#usize : Std.Usize).val] = x := by simp [hx]
      rw [h0, hx]
      rfl
    rw [ite_eq_right h1] at h
    peel h as r2, hr2
    cases r2 with
    | Err e => cases Result.ok_injective h
    | Ok reals =>
      obtain ⟨ys, hys, e2, e3, hw⟩ := real_paths_loop_ok hfs _ _ (by simp) hr2
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hys e3
      simp only [alloc.vec.Vec.with_capacity] at e2
      dsimp only at h
      peel h as b, hb
      by_cases hc : b = true
      · rw [ite_eq_left hc] at h
        peel h as v, hv
        obtain ⟨hi, rfl⟩ := vec_index_eq hv
        peel h as v1, hv1
        cases Result.ok_injective h
        rw [ConRon.Refine.Expr.str_copy_eq hv1]
        subst hc
        have hsame := all_same_loop_eq 1#usize hw hb
        have hlen : 2 ≤ hits.val.length := by
          have h1' : hits.val.length ≠ 1 := by
            intro he; apply h1; apply UScalar.eq_of_val_eq; rw [vec_len_val, he]; rfl
          have := List.length_pos_of_ne_nil hne
          omega
        have hrl : reals.val.length = hits.val.length := by
          have := congrArg List.length e2
          have h3 := congrArg List.length e3
          simp at this h3
          omega
        obtain ⟨x, y, rest, hm⟩ : ∃ x y rest, hits.val = x :: y :: rest := by
          match hits.val, hlen with
          | x :: y :: rest, _ => exact ⟨x, y, rest, rfl⟩
        have h0 : hits.val[(0#usize : Std.Usize).val] = x := by simp [hm]
        rw [h0, hm]
        rw [hm] at e3 hys
        simp only [List.map_cons] at hys ⊢
        rw [hys]
        obtain ⟨z, zs, hy⟩ : ∃ z zs, ys = z :: zs := by
          match ys, e3 with
          | z :: zs, _ => exact ⟨z, zs, rfl⟩
        rw [hy] at e3 ⊢
        simp only [List.map_cons, List.cons.injEq] at e3
        obtain ⟨hz1, hzs⟩ := e3
        obtain ⟨z1, z2⟩ := z
        simp only at hz1
        subst hz1
        have hz : 0 < reals.val.length := by omega
        have hrz : reals.val.map absDir = z2 :: zs.map (·.2) := by rw [e2, hy]; rfl
        have hall' : ∀ q ∈ reals.val.map absDir, q = absDir reals.val[0] := by
          intro q hq
          obtain ⟨j, hj, hqj⟩ := List.getElem_of_mem hq
          rw [← hqj, List.getElem_map]
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · subst h0; rfl
          · simp only [absDir]
            rw [hsame j (by simpa using hj) (by simp; omega) hz]
        have hz2 : z2 = absDir reals.val[0] := hall' z2 (by rw [hrz]; exact List.mem_cons_self)
        have hall : ∀ w ∈ zs, w.2 = z2 := by
          intro w hw'
          rw [hz2]
          exact hall' w.2 (by rw [hrz]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hw'))
        simp only [Bind.bind, Except.bind]
        rw [oneEach_same hall]
        rfl
      · rw [ite_eq_right hc] at h
        peel h as v, hv
        cases Result.ok_injective h

/-- **`root_at`'s directory is the twin's `rootAt`'.** -/
theorem root_at_ok {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {r : kernel.name.Name}
    {d : alloc.vec.Vec Std.U32} (hfs : FsRel inst fsv fs)
    (h : root_at inst fsv sp r = ok (.Dir d)) :
    rootAt fs (absSearchPath sp) (absName r) = .dir (absDir d) := by
  rw [root_at] at h
  peel h as r1, hr1
  cases r1 with
  | Ok a =>
    cases Result.ok_injective h
    simp only [rootAt, root_hits_ok hfs hr1]
  | Err e => cases Result.ok_injective h

/-- `located_of`'s accept: the root's directory. -/
theorem located_of_ok {mt rt : alloc.vec.Vec Std.U32} {a : RootAt} {l : Located}
    (h : located_of mt rt a = ok (.Ok l)) : a = .Dir l.dir := by
  rw [located_of] at h
  peel h as s0, -
  peel h as v0, -
  peel h as pre, -
  cases a with
  | Dir d =>
    cases Result.ok_injective h
    rfl
  | Missing => exact absurd h (not_ok_of_err (by err_any))
  | Twice ds => exact absurd h (not_ok_of_err (by err_any))
  | Failed e => exact absurd h (not_ok_of_err (by err_any))

/-- **`root_hits`' `Missing` is the twin's `rootHits`'.** -/
theorem root_hits_missing {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {r : kernel.name.Name}
    (hfs : FsRel inst fsv fs) (h : root_hits inst fsv sp r = ok (.Ok .Missing)) :
    rootHits fs (absSearchPath sp) (absName r) = .ok .missing := by
  rw [root_hits] at h
  peel h as r1, hr1
  cases r1 with
  | Err e => cases Result.ok_injective h
  | Ok hits =>
    obtain ⟨held, hh, e⟩ := root_dirs_loop_ok hfs _ _ hr1
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hh
    have e' : (held.filter (·.2)).map (·.1) = hits.val.map absDir := by rw [e]; rfl
    dsimp only at h
    have hR : rootHits fs (absSearchPath sp) (absName r) =
        (match (held.filter (·.2)).map (·.1) with
          | [] => .ok .missing
          | [d] => .ok (.dir d)
          | hits@(d :: _) => do
            match ConLeche.Frontend.Olean.oneEach (← hits.mapM (realStep fs)) with
            | [_] => return .dir d
            | locs => return .twice locs) := by
      simp only [rootHits, hh]
      rfl
    rw [hR, e']
    by_cases h0 : alloc.vec.Vec.len hits = 0#usize
    · have he : hits.val = [] := by
        have := congrArg UScalar.val h0
        rw [vec_len_val] at this
        exact List.eq_nil_of_length_eq_zero (by simpa using this)
      rw [he]
      rfl
    rw [ite_eq_right h0] at h
    by_cases h1 : alloc.vec.Vec.len hits = 1#usize
    · rw [ite_eq_left h1] at h
      peel h as v, -
      peel h as v1, -
      cases Result.ok_injective h
    rw [ite_eq_right h1] at h
    peel h as r2, -
    cases r2 with
    | Err e => cases Result.ok_injective h
    | Ok reals =>
      dsimp only at h
      peel h as b, -
      by_cases hc : b = true
      · rw [ite_eq_left hc] at h
        peel h as v, -
        peel h as v1, -
        cases Result.ok_injective h
      · rw [ite_eq_right hc] at h
        peel h as v, -
        cases Result.ok_injective h

/-- **`root_at`'s `Missing` is the twin's `rootAt`'.** -/
theorem root_at_missing {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {r : kernel.name.Name}
    (hfs : FsRel inst fsv fs) (h : root_at inst fsv sp r = ok .Missing) :
    rootAt fs (absSearchPath sp) (absName r) = .missing := by
  rw [root_at] at h
  peel h as r1, hr1
  cases r1 with
  | Ok a =>
    cases Result.ok_injective h
    simp only [rootAt, root_hits_missing hfs hr1]
  | Err e => cases Result.ok_injective h

/-- **`look_at`'s directory is the twin's `lookAt`'**: the path's, or where the path holds no
directory of the root, the fallback's. -/
theorem look_at_ok {path fallback : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {r : kernel.name.Name}
    {d : alloc.vec.Vec Std.U32} (hfs : FsRel inst fsv fs)
    (h : look_at inst fsv path fallback r = ok (.Dir d)) :
    Arena.Frontend.Olean.lookAt fs (absSearchPath path) (absSearchPath fallback) (absName r) =
      .dir (absDir d) := by
  rw [look_at] at h
  peel h as a, ha
  rw [look_next.eq_def] at h
  simp only [Arena.Frontend.Olean.lookAt]
  cases a with
  | Dir d' =>
    cases Result.ok_injective h
    rw [root_at_ok hfs ha]
    rfl
  | Missing =>
    rw [root_at_missing hfs ha]
    exact root_at_ok hfs h
  | Twice ds => cases Result.ok_injective h
  | Failed e => cases Result.ok_injective h

/-- **`find_module`'s accept is the twin's `findModule`.** -/
theorem find_module_ok {sp : frontend.olean.files.Roots} {l} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : find_module inst fsv pers ar sp m = ok (.Ok l)) :
    findModule fs (absRoots sp) (absName n) = .ok (absLocated l) := by
  rw [find_module] at h
  peel h as r, hr
  rw [hn] at hr
  cases Result.ok_injective hr
  dsimp only at h
  peel h as r1, hr1
  peel h as a, ha
  peel h as v, -
  peel h as v1, -
  have e1 := located_of_ok h
  subst e1
  have e2 := look_at_ok hfs ha
  rw [name_root_eq _ hr1] at e2
  simp only [findModule, absRoots, e2, ConLeche.Frontend.Olean.locatedOf]
  rfl

/-- **`read_part_at`'s accept is the twin's `readPartOr`**, whatever the failure's reason, and
what `part_of_bytes` leaves true. -/
theorem read_part_at_ok {loc : Located} {ext : alloc.vec.Vec Std.U32} {olean : Bool}
    {pt : frontend.olean.region.Part} (hfs : FsRel inst fsv fs)
    (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : read_part_at inst fsv pers ar loc m ext olean = ok (.Ok pt)) (absent : Unit → Arena.CheckError) :
    Arena.Frontend.Olean.readPartOr fs
        (ConLeche.Frontend.Olean.modFile (absDir loc.dir) (absName n) (absString ext)) absent =
      .ok (absPart pt) ∧ PartFits pt := by
  rw [read_part_at] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok p =>
    have hrel := pathRel_of hn hr
    dsimp only at h
    peel h as r1, hr1
    cases r1 with
    | Err e =>
      dsimp only at h
      split at h <;> (peel h as ce, -; cases Result.ok_injective h)
    | Ok b =>
      have e1 := hfs.readBinFile hrel b hr1
      obtain ⟨e2, -, hf⟩ := part_of_bytes_eq
        (ConLeche.Frontend.Olean.modFile (absDir loc.dir) (absName n) (absString ext)).toString h
      refine ⟨?_, hf⟩
      simp only [Arena.Frontend.Olean.readPartOr, e1, e2]

/-- **`path_exists_at`'s accept is the twin's `pathExistsE`.** -/
theorem path_exists_at_ok {loc : Located} {ext : alloc.vec.Vec Std.U32} {b : Bool}
    (hfs : FsRel inst fsv fs) (hn : arena.env.read_name pers ar m = ok (.Ok n))
    (h : path_exists_at inst fsv pers ar loc m ext = ok (.Ok b)) :
    Arena.Frontend.Olean.pathExistsE fs
      (ConLeche.Frontend.Olean.modFile (absDir loc.dir) (absName n) (absString ext)) = .ok b := by
  rw [path_exists_at] at h
  peel h as r, hr
  cases r with
  | Err e => cases Result.ok_injective h
  | Ok p =>
    have hrel := pathRel_of hn hr
    dsimp only at h
    peel h as r1, hr1
    cases r1 with
    | Err e =>
      dsimp only at h
      peel h as ce, -
      cases Result.ok_injective h
    | Ok b1 =>
      cases Result.ok_injective h
      simp only [Arena.Frontend.Olean.pathExistsE, hfs.pathExists hrel _ hr1]

end search

end ConRon.Refine2.Frontend.Olean
