/-
# `ConRon.Refine2.Checker.Leaves` — leaf statements the checker's base needs from tiers above it

Task #97-T2-LOCKSTEP lane Checker Base/Top, at the coordinator's ruling: a
statement `Checker/Base.lean` consumes but whose tier sits ABOVE it in the
module graph is moved down here, unchanged (proof or `sorry` and all), and
its old module imports this one.  So far:

* `mentions_const_refines`/`_ls` (from `Inductives/StructParts.lean`):
  `unresolved_consts_error`'s walk, proved here (round 2) by fuel induction
  with `mc_probe` and the arm statements it replaced.
* `env_pi_sort_tele_len_run` (from `Frontend/ExportCInd.lean`), with its two
  helpers `env_view_e_run`/`view_bind_run` (from `Frontend/ExportC.lean`):
  `ind_params_ok`'s leaf.
-/
import ConRon.Refine2.Checker.KnotHyp

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## `mentions_const`: `unresolved_consts_error`'s walk

The walk threads its memo INSIDE the `Result` (`Result<(bool, memo)>`), which
is the shape the tactic zips: a fuel induction, each case one `lockstep`, with
the node dispatch `mentions_const_node` unfolded in place against the twin's
inner `match`.  The Inductives tier's arm statements (`mentions_const_go`/
`_node`, `mc_probe`, all `sorry` and used by nothing else) moved here with
it and are proved. -/

/-- `mc_probe` ⊑ `memo[h]?`. -/
theorem mc_probe_refines {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {k : arena.handle.EIdx} {o}
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.inductives.struct_parts.mc_probe rm k = ok o) :
    o = lm[absEIdx k]? := by
  rw [arena.inductives.struct_parts.mc_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hmr, hminv⟩ := hm
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hminv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hmr k trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Bool) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some v =>
    rw [hrc] at hrun
    have h2 : some v = o := Result.ok_injective hrun
    subst h2
    rfl

open Lockstep in
@[lockstep] theorem mc_probe_twin
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {k : arena.handle.EIdx}
    (hm : ExprOps.LMemoRel rm lm) :
    LSP (arena.inductives.struct_parts.mc_probe rm k) (fun o => TwinEq (lm[absEIdx k]?) (o)) :=
  fun o h => (mc_probe_refines hm h).symm

open Lockstep in
/-- `mentions_const_go` ⊑ `mentionsConstGo`, by induction on the fuel. -/
theorem mentions_const_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (t : arena.handle.NIdx) (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      (lm : Std.HashMap EIdx Bool) (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → ExprOps.LMemoRel rm lm →
      LS pers (fun a b => ∃ m', ExprOps.LMemoRel a.2 m' ∧ b = (a.1, m'))
        (arena.inductives.struct_parts.mentions_const_go pers st t rm fuel h) lst
        (mentionsConstGo (absNIdx t) lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst t rm lm fuel h hn hrel hinv hm
    rw [arena.inductives.struct_parts.mentions_const_go, mentionsConstGo]
    lockstep
  | succ m ih =>
    intro pers st lst t rm lm fuel h hn hrel hinv hm
    rw [arena.inductives.struct_parts.mentions_const_go, mentionsConstGo]
    unfold arena.inductives.struct_parts.mentions_const_node
    lockstep
    -- the `.proj` arm: the port tested `s.eq2(t)` first (false here), the twin
    -- reads `s == T || b`
    all_goals
      simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_or]
      exact LS.pure ⟨_, hP, rfl⟩ hrel hinv

open Lockstep in
@[lockstep] theorem mentions_const_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t : arena.handle.NIdx)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => ∃ m', ExprOps.LMemoRel a.2 m' ∧ b = (a.1, m'))
      (arena.inductives.struct_parts.mentions_const_go pers st t rm fuel h) lst
      (mentionsConstGo (absNIdx t) lm (absU fuel) (absEIdx h)) :=
  mentions_const_go_aux _ t rm lm fuel h rfl hrel hinv hm

open Lockstep in
/-- `mentions_const` ⊑ `mentionsConst` — one memoised walk from the empty
memo. -/
@[lockstep] theorem mentions_const_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_parts.mentions_const pers st t e) lst
      (mentionsConst (absNIdx t) (absEIdx e)) := by
  rw [arena.inductives.struct_parts.mentions_const, mentionsConst]
  lockstep

theorem mentions_const_refines {pers st lst} {t : arena.handle.NIdx}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.struct_parts.mentions_const pers st t e = ok o) :
    Sim₀ id pers lst o
      (mentionsConst (absNIdx t) (absEIdx e)) :=
  Lockstep.LS.toSim₀ (mentions_const_ls hrel hinv) hrun

end ConRon.Refine2

namespace ConRon.Refine2.Frontend

open ConRon.Arena

/-- `env::view_e` — the store's expression view. -/
theorem env_view_e_run {pers rst lst} (hrel : AStateRel₀ pers rst lst)
    {h : arena.handle.EIdx} {o}
    (hrun : arena.env.view_e pers rst.store h = ok o) :
    SimRE absENodeView lst o (view (absEIdx h)) := by
  rw [arena.env.view_e] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hqa := estore_view_abs hrel.store hq
  have hrunL : (view (absEIdx h)).run lst
      = (match lst.store.view (absEIdx h) with
         | some v => Except.ok (v, lst)
         | none => Except.error (Arena.CheckError.internal
             "arena: dangling expression handle")) := by
    show (match lst.store.view (absEIdx h) with
          | some v => (pure v : AM _)
          | none => Arena.fail (.internal "arena: dangling expression handle")).run lst = _
    cases lst.store.view (absEIdx h) <;> rfl
  cases q with
  | none =>
    obtain ⟨_, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨_, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨ce, hce, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [kernel.core_types.internal] at hce
    cases Result.ok_injective hce
    cases Result.ok_injective hrun
    show AErrSim _ _
    rw [hrunL, hqa]
    exact AErrSim.internal rfl
  | some w =>
    cases Result.ok_injective hrun
    show _ = _
    rw [hrunL, hqa]
    rfl

/-- A twin `view` step at a known answer. -/
theorem view_bind_run {β : Type} {lst : AState} {h : EIdx} {v : ENodeView}
    (hv : (view h).run lst = .ok (v, lst)) (f : ENodeView → AM β) :
    (view h >>= f).run lst = (f v).run lst := by
  rw [am_run_bind', hv]; rfl

/-- **`env::pi_sort_tele_len` refines `piSortTeleLen?`** — the Π-telescope
length of a type ending in a sort, `none` elsewhere.  A leaf of this tier. -/
theorem env_pi_sort_tele_len_run {pers rst lst fuel h' o}
    (hrel : AStateRel₀ pers rst lst) (_hinv : AStateInv pers rst)
    (h : arena.env.pi_sort_tele_len pers rst.store fuel h' = ok o) :
    SimRE (Option.map absU) lst o (piSortTeleLen? (absU fuel) (absEIdx h')) := by
  have H : ∀ (k : Nat) (fuel : Std.U64) (cur : arena.handle.EIdx) o, fuel.val = k →
      arena.env.pi_sort_tele_len pers rst.store fuel cur = ok o →
      SimRE (Option.map absU) lst o (piSortTeleLen? k (absEIdx cur)) := by
    intro k
    induction k with
    | zero =>
      intro fuel cur o hk h
      rw [arena.env.pi_sort_tele_len] at h
      rw [if_pos (by scalar_tac)] at h
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [kernel.core_types.internal] at hce
      cases Result.ok_injective hce
      cases Result.ok_injective h
      exact AErrSim.internal rfl
    | succ k ih =>
      intro fuel cur o hk h
      rw [arena.env.pi_sort_tele_len] at h
      rw [if_neg (by scalar_tac)] at h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hV := env_view_e_run hrel hr
      simp only [piSortTeleLen?]
      cases r with
      | Err e =>
        cases Result.ok_injective h
        show AErrSim _ _
        rw [am_run_bind']
        exact AErrSim.bind hV _
      | Ok ev =>
        have hV' : (view (absEIdx cur)).run lst = .ok (absENodeView ev, lst) := hV
        cases ev with
        | ForallE ty b m =>
          obtain ⟨f1, hf1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hf1v := (ConRon.Refine.Nat.usub_val hf1).2
          obtain ⟨r1, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hR := ih f1 b r1 (by simp at hf1v; omega) hr1
          cases r1 with
          | Err e =>
            cases Result.ok_injective h
            show AErrSim _ _
            rw [view_bind_run hV']
            simp only [absENodeView]
            rw [am_run_bind']
            exact AErrSim.bind hR _
          | Ok ov =>
            have hR' : (piSortTeleLen? k (absEIdx b)).run lst = .ok (ov.map absU, lst) := hR
            cases ov with
            | none =>
              cases Result.ok_injective h
              show _ = _
              rw [view_bind_run hV']
              simp only [absENodeView]
              rw [am_run_bind', hR']
              rfl
            | some n =>
              obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
              cases Result.ok_injective h
              have := ConRon.Refine.Nat.uadd_val hn1
              show _ = _
              rw [view_bind_run hV']
              simp only [absENodeView]
              rw [am_run_bind', hR']
              show Except.ok _ = _
              simp only [Option.map, absU, this]
              rfl
        | «Sort» s => cases Result.ok_injective h; show _ = _; rw [view_bind_run hV']; rfl
        | _ =>
          all_goals (cases Result.ok_injective h; show _ = _; rw [view_bind_run hV']; rfl)
  exact H _ fuel h' o rfl h

end ConRon.Refine2.Frontend
