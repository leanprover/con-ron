/-
# `ConRon.Bridge.Inductives.XFreeIota` — the ι reading rule keeps the scratch flag (task #166)

`XFree` (`Bridge/Inductives/Install.lean`: "the expression store's scratch flag is unchanged")
for the twin's `recsRead` and every walk under it: the hash-consing interns (`internE`, which
appends to the tier the flag names and never sets it), the memo probes and records (which write
`memos` or `caches` only), the rebuilding walks (`liftLooseBVarsFast`, `instantiate1Fast`,
`instantiateLiftFast`, `instLPFast`, one fuel induction each over their arms), and the reading of
a recursor's rules.  Nothing under `recsRead` opens or drops the scratch tier.
-/
module

public import ConRon.Bridge.Inductives.Install
public import ConRon.Arena.Inductives.IotaRead
import all Init.Data.List.Control

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## Runs that leave the store alone -/

theorem XFree.failDanglingE' {α : Type} : XFree (failDanglingE : AM α) := XFree.fail _
theorem XFree.failDanglingLs {α : Type} : XFree (failDanglingLs : AM α) := XFree.fail _

theorem XFree.derivedE (h : EIdx) : XFree (Arena.derivedE h) := by unfold Arena.derivedE; xfree_auto
theorem XFree.viewBVar (h : EIdx) : XFree (Arena.viewBVar h) := by unfold Arena.viewBVar; xfree_auto
theorem XFree.viewSort (h : EIdx) : XFree (Arena.viewSort h) := by unfold Arena.viewSort; xfree_auto
theorem XFree.viewLsLen (h : LsIdx) : XFree (Arena.viewLsLen h) := by
  unfold Arena.viewLsLen; xfree_auto
theorem XFree.viewL (h : LIdx) : XFree (Arena.viewL h) := by unfold Arena.viewL; xfree_auto

/-! ## The memo tables and the readback caches -/

theorem XFree.liftGet (k : EIdx × Nat) : XFree (Arena.liftGet k) := by unfold Arena.liftGet; xfree_auto
theorem XFree.liftSet (k : EIdx × Nat) (r : EIdx) : XFree (Arena.liftSet k r) := by
  unfold Arena.liftSet
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.liftClear : XFree Arena.liftClear := by
  unfold Arena.liftClear
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.inst1Get (k : EIdx × Nat) : XFree (Arena.inst1Get k) := by
  unfold Arena.inst1Get; xfree_auto
theorem XFree.inst1Set (k : EIdx × Nat) (r : EIdx) : XFree (Arena.inst1Set k r) := by
  unfold Arena.inst1Set
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.inst1Clear : XFree Arena.inst1Clear := by
  unfold Arena.inst1Clear
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.inst1LGet (k : EIdx × Nat) : XFree (Arena.inst1LGet k) := by
  unfold Arena.inst1LGet; xfree_auto
theorem XFree.inst1LSet (k : EIdx × Nat) (r : EIdx) : XFree (Arena.inst1LSet k r) := by
  unfold Arena.inst1LSet
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.inst1LClear : XFree Arena.inst1LClear := by
  unfold Arena.inst1LClear
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.instLPGet (k : EIdx × Nat) : XFree (Arena.instLPGet k) := by
  unfold Arena.instLPGet; xfree_auto
theorem XFree.instLPSet (k : EIdx × Nat) (r : EIdx) : XFree (Arena.instLPSet k r) := by
  unfold Arena.instLPSet
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.instLPClear : XFree Arena.instLPClear := by
  unfold Arena.instLPClear
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.instLPLGet (h : LIdx) : XFree (Arena.instLPLGet h) := by
  unfold Arena.instLPLGet; xfree_auto
theorem XFree.instLPLSet (h r : LIdx) : XFree (Arena.instLPLSet h r) := by
  unfold Arena.instLPLSet
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.instLPLsGet (h : LsIdx) : XFree (Arena.instLPLsGet h) := by
  unfold Arena.instLPLsGet; xfree_auto
theorem XFree.instLPLsSet (h r : LsIdx) : XFree (Arena.instLPLsSet h r) := by
  unfold Arena.instLPLsSet
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.bvarBGet (k : EIdx) : XFree (Arena.bvarBGet k) := by unfold Arena.bvarBGet; xfree_auto
theorem XFree.bvarBSet (k : EIdx) (r : Nat) : XFree (Arena.bvarBSet k r) := by
  unfold Arena.bvarBSet
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]
theorem XFree.bvarBClear : XFree Arena.bvarBClear := by
  unfold Arena.bvarBClear
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  dsimp only at h2
  rw [AM.set_ok h2]

theorem XFree.readLevelM (h : LIdx) : XFree (Arena.readLevelM h) := by
  unfold Arena.readLevelM
  intro s s' x hr
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨ht, hs1⟩ := AM.get_ok h1
  rw [ht, hs1] at h2
  cases hc : s.caches.readLC[h]? with
  | some l => simp only [hc] at h2; obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  | none =>
    simp only [hc] at h2
    cases hd : denoteL s.store.ls h with
    | none => simp only [hd] at h2; exact absurd h2 (fun h => AM.fail_ok h)
    | some l =>
      simp only [hd] at h2
      obtain ⟨_, _, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨-, rfl⟩ := AM.pure_ok h4
      rw [AM.set_ok h3]

theorem XFree.readNameM (h : NIdx) : XFree (Arena.readNameM h) := by
  unfold Arena.readNameM
  intro s s' x hr
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨ht, hs1⟩ := AM.get_ok h1
  rw [ht, hs1] at h2
  cases hc : s.caches.readNC[h]? with
  | some l => simp only [hc] at h2; obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  | none =>
    simp only [hc] at h2
    cases hd : denoteN s.store.ns h with
    | none => simp only [hd] at h2; exact absurd h2 (fun h => AM.fail_ok h)
    | some l =>
      simp only [hd] at h2
      obtain ⟨_, _, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨-, rfl⟩ := AM.pure_ok h4
      rw [AM.set_ok h3]

theorem XFree.readLevelsM (h : LsIdx) : XFree (Arena.readLevelsM h) := by
  unfold Arena.readLevelsM
  intro s s' x hr
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨ht, hs1⟩ := AM.get_ok h1
  rw [ht, hs1] at h2
  cases hc : s.caches.readLsC[h]? with
  | some l => simp only [hc] at h2; obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  | none =>
    simp only [hc] at h2
    cases hd : denoteLs s.store.lss h with
    | none => simp only [hd] at h2; exact absurd h2 (fun h => AM.fail_ok h)
    | some l =>
      simp only [hd] at h2
      obtain ⟨_, _, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨-, rfl⟩ := AM.pure_ok h4
      rw [AM.set_ok h3]

theorem XFree.readNamesM : ∀ (hs : List NIdx), XFree (Arena.readNamesM hs)
  | [] => by unfold Arena.readNamesM; exact XFree.pure _
  | h :: hs => by
    have ih := XFree.readNamesM hs
    have hr := XFree.readNameM
    unfold Arena.readNamesM; xfree_auto

/-! ## The interns -/

theorem EStore.intern_scr (st : EStore) (v : ENodeView) :
    (st.intern v).1.scratchOn = st.scratchOn := by
  unfold EStore.intern
  dsimp only
  repeat (first | rfl | split)

theorem EStore.internBind_scr (st : EStore) (tag : UInt32) (ty b : EIdx) :
    (st.internBind tag ty b).1.scratchOn = st.scratchOn := by
  unfold EStore.internBind
  dsimp only
  repeat (first | rfl | split)

theorem XFree.internNodeE (v : ENodeView) : XFree (Arena.internNodeE v) := by
  unfold Arena.internNodeE
  intro s s' r hr
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨ht, hs1⟩ := AM.get_ok h1
  rw [ht, hs1] at h2
  cases hf : s.store.find? v with
  | some x => simp only [hf] at h2; obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  | none =>
    simp only [hf] at h2
    split at h2 <;> split at h2
    all_goals first
      | (obtain ⟨_, s₂, k, z⟩ := AM.bind_ok h2
         obtain ⟨-, rfl⟩ := AM.pure_ok z
         rw [AM.set_ok k]
         exact (EStore.intern_scr _ _))
      | exact absurd h2 (fun h => AM.fail_ok h)

theorem XFree.internLamE (ty b : EIdx) : XFree (Arena.internLamE ty b) := by
  unfold Arena.internLamE
  intro s s' r hr
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨ht, hs1⟩ := AM.get_ok h1
  rw [ht, hs1] at h2
  cases hf : s.store.findBind ETag.lam ty b with
  | some x => simp only [hf] at h2; obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  | none =>
    simp only [hf] at h2
    split at h2 <;> split at h2
    all_goals first
      | (obtain ⟨_, s₂, k, z⟩ := AM.bind_ok h2
         obtain ⟨-, rfl⟩ := AM.pure_ok z
         rw [AM.set_ok k]
         exact (EStore.internBind_scr _ _ _ _))
      | exact absurd h2 (fun h => AM.fail_ok h)

theorem XFree.internForallEE (ty b : EIdx) : XFree (Arena.internForallEE ty b) := by
  unfold Arena.internForallEE
  intro s s' r hr
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨ht, hs1⟩ := AM.get_ok h1
  rw [ht, hs1] at h2
  cases hf : s.store.findBind ETag.forallE ty b with
  | some x => simp only [hf] at h2; obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  | none =>
    simp only [hf] at h2
    split at h2 <;> split at h2
    all_goals first
      | (obtain ⟨_, s₂, k, z⟩ := AM.bind_ok h2
         obtain ⟨-, rfl⟩ := AM.pure_ok z
         rw [AM.set_ok k]
         exact (EStore.internBind_scr _ _ _ _))
      | exact absurd h2 (fun h => AM.fail_ok h)

theorem XFree.internE (v : ENodeView) : XFree (Arena.internE v) := by
  cases v <;> unfold Arena.internE <;>
    first | exact XFree.internNodeE _ | exact XFree.internLamE _ _ | exact XFree.internForallEE _ _
theorem XFree.internBVarE (i : Nat) : XFree (Arena.internBVarE i) := XFree.internE _
theorem XFree.internSortE (u : LIdx) : XFree (Arena.internSortE u) := XFree.internE _

theorem XFree.internName : ∀ (n : ConLeche.Name), XFree (Arena.internName n)
  | .anonymous => by unfold Arena.internName; exact XFree.internNNode _
  | .str p _ => by
    have ih := XFree.internName p
    unfold Arena.internName
    exact XFree.bind ih (fun _ => XFree.internNNode _)
  | .num p _ => by
    have ih := XFree.internName p
    unfold Arena.internName
    exact XFree.bind ih (fun _ => XFree.internNNode _)

theorem XFree.internLevel : ∀ (l : Level), XFree (Arena.internLevel l)
  | .zero => by unfold Arena.internLevel; exact XFree.internLNode _
  | .succ u => by
    have ih := XFree.internLevel u
    unfold Arena.internLevel; exact XFree.bind ih (fun _ => XFree.internLNode _)
  | .max u v => by
    have ih := XFree.internLevel u; have iv := XFree.internLevel v
    unfold Arena.internLevel
    exact XFree.bind ih (fun _ => XFree.bind iv (fun _ => XFree.internLNode _))
  | .imax u v => by
    have ih := XFree.internLevel u; have iv := XFree.internLevel v
    unfold Arena.internLevel
    exact XFree.bind ih (fun _ => XFree.bind iv (fun _ => XFree.internLNode _))
  | .param n => by
    unfold Arena.internLevel; exact XFree.bind (XFree.internName n) (fun _ => XFree.internLNode _)

theorem XFree.internLevelList : ∀ (us : List Level), XFree (Arena.internLevelList us)
  | [] => by unfold Arena.internLevelList; exact XFree.pure _
  | u :: us => by
    unfold Arena.internLevelList
    exact XFree.bind (XFree.internLevel u) (fun _ =>
      XFree.bind (XFree.internLevelList us) (fun _ => XFree.pure _))

theorem XFree.internLevels (us : List Level) : XFree (Arena.internLevels us) := by
  unfold Arena.internLevels
  exact XFree.bind (XFree.internLevelList us) (fun _ => XFree.internLsNode _)

/-! ## The expression constructors' entries and the projections -/

theorem XFree.internAppE (f a : EIdx) : XFree (Arena.internAppE f a) := XFree.internE _
theorem XFree.internLetEE (ty v b : EIdx) : XFree (Arena.internLetEE ty v b) := XFree.internE _
theorem XFree.internProjE (n : NIdx) (i : Nat) (e : EIdx) : XFree (Arena.internProjE n i e) :=
  XFree.internE _
theorem XFree.internBindE (tag : UInt32) (ty b : EIdx) : XFree (Arena.internBindE tag ty b) := by
  unfold Arena.internBindE
  split
  · exact XFree.internLamE _ _
  · exact XFree.internForallEE _ _
theorem XFree.viewLet (h : EIdx) : XFree (Arena.viewLet h) := by unfold Arena.viewLet; xfree_auto
theorem XFree.viewProj (h : EIdx) : XFree (Arena.viewProj h) := by unfold Arena.viewProj; xfree_auto

/-- The rebuilding walks' leaves: a rebuild either answers the handle or interns. -/
macro "xfree_rebuilt" : tactic => `(tactic| (split <;> first
  | exact XFree.pure _ | exact XFree.internE _ | exact XFree.internLamE _ _
  | exact XFree.internForallEE _ _ | exact XFree.internBindE _ _ _))

theorem XFree.internRebuiltFVar (h : EIdx) (b : Bool) (i : Nat) (t : EIdx) :
    XFree (Arena.internRebuiltFVar h b i t) := by unfold Arena.internRebuiltFVar; xfree_rebuilt
theorem XFree.internRebuiltSort (h : EIdx) (b : Bool) (u : LIdx) :
    XFree (Arena.internRebuiltSort h b u) := by unfold Arena.internRebuiltSort; xfree_rebuilt
theorem XFree.internRebuiltConst (h : EIdx) (b : Bool) (n : NIdx) (us : LsIdx) :
    XFree (Arena.internRebuiltConst h b n us) := by unfold Arena.internRebuiltConst; xfree_rebuilt
theorem XFree.internRebuiltApp (h : EIdx) (b : Bool) (f a : EIdx) :
    XFree (Arena.internRebuiltApp h b f a) := by unfold Arena.internRebuiltApp; xfree_rebuilt
theorem XFree.internRebuiltLam (h : EIdx) (b : Bool) (ty x : EIdx) :
    XFree (Arena.internRebuiltLam h b ty x) := by unfold Arena.internRebuiltLam; xfree_rebuilt
theorem XFree.internRebuiltForallE (h : EIdx) (b : Bool) (ty x : EIdx) :
    XFree (Arena.internRebuiltForallE h b ty x) := by
  unfold Arena.internRebuiltForallE; xfree_rebuilt
theorem XFree.internRebuiltLetE (h : EIdx) (b : Bool) (ty v x : EIdx) :
    XFree (Arena.internRebuiltLetE h b ty v x) := by unfold Arena.internRebuiltLetE; xfree_rebuilt
theorem XFree.internRebuiltProj (h : EIdx) (b : Bool) (n : NIdx) (i : Nat) (e : EIdx) :
    XFree (Arena.internRebuiltProj h b n i e) := by unfold Arena.internRebuiltProj; xfree_rebuilt

/-- One of the named lemmas, applied at reducible transparency. -/
syntax "xfree_try" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| xfree_try []) => `(tactic| fail)
  | `(tactic| xfree_try [$h:ident]) => `(tactic| with_reducible apply $h)
  | `(tactic| xfree_try [$h:ident, $hs:ident,*]) =>
    `(tactic| first | (with_reducible apply $h) | xfree_try [$hs,*])

/-- The rebuilding walks' steps: every leaf a lemma above or one of the named ones. -/
syntax "xfree_walk" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| xfree_walk [$hs,*]) => `(tactic| repeat (first
    | (with_reducible exact XFree.pure _)
    | (with_reducible exact XFree.fail _)
    | (with_reducible exact XFree.failDanglingE')
    | (with_reducible exact XFree.failDanglingLs)
    | (with_reducible exact XFree.get)
    | (with_reducible exact XFree.internE _)
    | (with_reducible exact XFree.internAppE _ _)
    | (with_reducible exact XFree.internLetEE _ _ _)
    | (with_reducible exact XFree.internProjE _ _ _)
    | (with_reducible exact XFree.internBindE _ _ _)
    | (with_reducible exact XFree.internBVarE _)
    | (with_reducible exact XFree.internSortE _)
    | (with_reducible exact XFree.internLamE _ _)
    | (with_reducible exact XFree.internForallEE _ _)
    | (with_reducible exact XFree.derivedE _)
    | (with_reducible exact XFree.view' _)
    | (with_reducible exact XFree.viewApp _)
    | (with_reducible exact XFree.viewBind _)
    | (with_reducible exact XFree.viewLet _)
    | (with_reducible exact XFree.viewProj _)
    | (with_reducible exact XFree.viewBVar _)
    | (with_reducible exact XFree.viewSort _)
    | (with_reducible exact XFree.viewConst _)
    | (with_reducible exact XFree.viewLsLen _)
    | (with_reducible exact XFree.viewL _)
    | xfree_try [$hs,*]
    | (with_reducible refine XFree.bind ?_ (fun _ => ?_))
    | (dsimp only)
    | split))

/-! ## `liftLooseBVars` -/

theorem XFree.liftGo (amount : Nat) :
    ∀ (fuel : Nat) (h : EIdx) (c : Nat), XFree (Arena.liftLooseBVarsGo amount fuel h c) := by
  intro fuel
  induction fuel with
  | zero => intro h c; rw [Arena.liftLooseBVarsGo_zero]; exact XFree.fail _
  | succ fuel ih =>
    intro h c
    have g := XFree.liftGet; have st := XFree.liftSet
    have a1 : ∀ h c a b, XFree (Arena.liftArmApp amount fuel h c a b) := by
      intro h c a b; rw [Arena.liftArmApp]; xfree_walk [ih, g, st]
    have a2 : ∀ h c a b, XFree (Arena.liftArmLam amount fuel h c a b) := by
      intro h c a b; rw [Arena.liftArmLam]; xfree_walk [ih, g, st, a1]
    have a3 : ∀ h c a b, XFree (Arena.liftArmForallE amount fuel h c a b) := by
      intro h c a b; rw [Arena.liftArmForallE]; xfree_walk [ih, g, st, a1, a2]
    have a4 : ∀ h c a b e, XFree (Arena.liftArmLet amount fuel h c a b e) := by
      intro h c a b e; rw [Arena.liftArmLet]; xfree_walk [ih, g, st, a1, a2, a3]
    have a5 : ∀ h c n i e, XFree (Arena.liftArmProj amount fuel h c n i e) := by
      intro h c n i e; rw [Arena.liftArmProj]; xfree_walk [ih, g, st, a1, a2, a3, a4]
    rw [Arena.liftLooseBVarsGo_succ]; xfree_walk [ih, g, st, a1, a2, a3, a4, a5]

theorem XFree.liftLooseBVarsFast (fuel amount c : Nat) (e : EIdx) :
    XFree (Arena.liftLooseBVarsFast fuel amount c e) := by
  have hx1 := XFree.liftGo amount; have hx2 := XFree.liftClear
  unfold Arena.liftLooseBVarsFast; xfree_walk [hx1, hx2]

/-! ## `instantiate1` -/

theorem XFree.inst1Go (v : EIdx) :
    ∀ (fuel : Nat) (h : EIdx) (d : Nat), XFree (Arena.instantiate1Go v fuel h d) := by
  intro fuel
  induction fuel with
  | zero => intro h d; rw [Arena.instantiate1Go_zero]; exact XFree.fail _
  | succ fuel ih =>
    intro h d
    have g := XFree.inst1Get; have st := XFree.inst1Set
    have a0 : ∀ h d, XFree (Arena.instantiate1ArmBVar v h d) := by
      intro h d; unfold Arena.instantiate1ArmBVar; xfree_walk [ih, g, st]
    have a1 : ∀ h d, XFree (Arena.instantiate1ArmApp v fuel h d) := by
      intro h d; rw [Arena.instantiate1ArmApp]; xfree_walk [ih, g, st, a0]
    have a2 : ∀ h d, XFree (Arena.instantiate1ArmBind v fuel h d) := by
      intro h d; rw [Arena.instantiate1ArmBind]; xfree_walk [ih, g, st, a0, a1]
    have a3 : ∀ h d, XFree (Arena.instantiate1ArmLet v fuel h d) := by
      intro h d; rw [Arena.instantiate1ArmLet]; xfree_walk [ih, g, st, a0, a1, a2]
    have a4 : ∀ h d, XFree (Arena.instantiate1ArmProj v fuel h d) := by
      intro h d; rw [Arena.instantiate1ArmProj]; xfree_walk [ih, g, st, a0, a1, a2, a3]
    rw [Arena.instantiate1Go_succ]; xfree_walk [ih, g, st, a0, a1, a2, a3, a4]

theorem XFree.instantiate1Fast (fuel : Nat) (e v : EIdx) (d : Nat) :
    XFree (Arena.instantiate1Fast fuel e v d) := by
  have hx1 := XFree.inst1Go v; have hx2 := XFree.inst1Clear
  unfold Arena.instantiate1Fast; xfree_walk [hx1, hx2]

/-! ## The loose-bound-variable bound -/

theorem XFree.bvarBoundGo : ∀ (fuel : Nat) (h : EIdx), XFree (Arena.bvarBoundGo fuel h) := by
  intro fuel
  induction fuel with
  | zero => intro h; rw [Arena.bvarBoundGo_zero]; exact XFree.fail _
  | succ fuel ih =>
    intro h
    have g := XFree.bvarBGet; have st := XFree.bvarBSet
    have a1 : ∀ f a, XFree (Arena.bvarBoundArmApp fuel f a) := by
      intro f a; rw [Arena.bvarBoundArmApp]; xfree_walk [ih, g, st]
    have a2 : ∀ t b, XFree (Arena.bvarBoundArmBind fuel t b) := by
      intro t b; rw [Arena.bvarBoundArmBind]; xfree_walk [ih, g, st, a1]
    have a3 : ∀ t v b, XFree (Arena.bvarBoundArmLet fuel t v b) := by
      intro t v b; rw [Arena.bvarBoundArmLet]; xfree_walk [ih, g, st, a1, a2]
    rw [Arena.bvarBoundGo_succ]; xfree_walk [ih, g, st, a1, a2, a3]

theorem XFree.bvarB (fuel : Nat) (e : EIdx) : XFree (Arena.bvarB fuel e) := by
  have hx1 := XFree.bvarBoundGo; have hx2 := XFree.bvarBClear
  have hm : ∀ fuel e, XFree (Arena.bvarBoundMemo fuel e) := by
    intro fuel e; unfold Arena.bvarBoundMemo; xfree_walk [hx1, hx2]
  unfold Arena.bvarB; xfree_walk [hx1, hx2, hm]

/-! ## `instantiateLift` -/

theorem XFree.instLiftGo (vs : Array EIdx) :
    ∀ (fuel : Nat) (h : EIdx) (d : Nat), XFree (Arena.instantiateLiftGo vs fuel h d) := by
  intro fuel
  induction fuel with
  | zero => intro h d; rw [Arena.instantiateLiftGo_zero]; exact XFree.fail _
  | succ fuel ih =>
    intro h d
    have g := XFree.inst1LGet; have st := XFree.inst1LSet
    have lf := XFree.liftLooseBVarsFast; have bb := XFree.bvarB
    have a1 : ∀ h d f a, XFree (Arena.instLiftArmApp vs fuel h d f a) := by
      intro h d f a; rw [Arena.instLiftArmApp]; xfree_walk [ih, g, st, lf, bb]
    have a2 : ∀ h d t b, XFree (Arena.instLiftArmLam vs fuel h d t b) := by
      intro h d t b; rw [Arena.instLiftArmLam]; xfree_walk [ih, g, st, lf, bb, a1]
    have a3 : ∀ h d t b, XFree (Arena.instLiftArmForallE vs fuel h d t b) := by
      intro h d t b; rw [Arena.instLiftArmForallE]; xfree_walk [ih, g, st, lf, bb, a1, a2]
    have a4 : ∀ h d t v b, XFree (Arena.instLiftArmLet vs fuel h d t v b) := by
      intro h d t v b; rw [Arena.instLiftArmLet]; xfree_walk [ih, g, st, lf, bb, a1, a2, a3]
    have a5 : ∀ h d n i e, XFree (Arena.instLiftArmProj vs fuel h d n i e) := by
      intro h d n i e; rw [Arena.instLiftArmProj]; xfree_walk [ih, g, st, lf, bb, a1, a2, a3, a4]
    rw [Arena.instantiateLiftGo_succ]; xfree_walk [ih, g, st, lf, bb, a1, a2, a3, a4, a5]

theorem XFree.instantiateLiftFast (fuel : Nat) (e : EIdx) (vs : Array EIdx) (d : Nat) :
    XFree (Arena.instantiateLiftFast fuel e vs d) := by
  have hx1 := XFree.instLiftGo vs; have hx2 := XFree.inst1LClear
  unfold Arena.instantiateLiftFast; xfree_walk [hx1, hx2]

/-! ## `instantiateLevelParams` -/

theorem XFree.substLMemoAt (ks : List ConLeche.Name) (us : List Level) (u : LIdx) :
    XFree (Arena.substLMemoAt ks us u) := by
  have hx1 := XFree.instLPLGet; have hx2 := XFree.instLPLSet; have hx3 := XFree.readLevelM
  have hx4 := XFree.internLevel
  unfold Arena.substLMemoAt; xfree_walk [hx1, hx2, hx3, hx4]

theorem XFree.substLsMemoAt (ks : List ConLeche.Name) (us : List Level) (vs : LsIdx) :
    XFree (Arena.substLsMemoAt ks us vs) := by
  have hx1 := XFree.instLPLsGet; have hx2 := XFree.instLPLsSet; have hx3 := XFree.readLevelsM
  have hx4 := XFree.internLevels
  unfold Arena.substLsMemoAt; xfree_walk [hx1, hx2, hx3, hx4]

theorem XFree.instLPGo (ks : List ConLeche.Name) (us : List Level) :
    ∀ (fuel : Nat) (h : EIdx), XFree (Arena.instLPGo ks us fuel h) := by
  intro fuel
  induction fuel with
  | zero => intro h; rw [Arena.instLPGo_zero]; exact XFree.fail _
  | succ fuel ih =>
    intro h
    have g := XFree.instLPGet; have st := XFree.instLPSet
    have sl := XFree.substLMemoAt ks us; have sls := XFree.substLsMemoAt ks us
    have r1 := XFree.internRebuiltFVar; have r2 := XFree.internRebuiltSort
    have r3 := XFree.internRebuiltConst; have r4 := XFree.internRebuiltApp
    have r5 := XFree.internRebuiltLam; have r6 := XFree.internRebuiltForallE
    have r7 := XFree.internRebuiltLetE; have r8 := XFree.internRebuiltProj
    have a0 : ∀ h i t, XFree (Arena.instLPArmFVar ks us fuel h i t) := by
      intro h i t; rw [Arena.instLPArmFVar]; xfree_walk [ih, g, st, sl, sls, r1, r2, r3, r4, r5, r6, r7, r8]
    have a1 : ∀ h f a, XFree (Arena.instLPArmApp ks us fuel h f a) := by
      intro h f a; rw [Arena.instLPArmApp]; xfree_walk [ih, g, st, sl, sls, r1, r2, r3, r4, r5, r6, r7, r8, a0]
    have a2 : ∀ h t b, XFree (Arena.instLPArmLam ks us fuel h t b) := by
      intro h t b; rw [Arena.instLPArmLam]; xfree_walk [ih, g, st, sl, sls, r1, r2, r3, r4, r5, r6, r7, r8, a0, a1]
    have a3 : ∀ h t b, XFree (Arena.instLPArmForallE ks us fuel h t b) := by
      intro h t b; rw [Arena.instLPArmForallE]; xfree_walk [ih, g, st, sl, sls, r1, r2, r3, r4, r5, r6, r7, r8, a0, a1, a2]
    have a4 : ∀ h t v b, XFree (Arena.instLPArmLet ks us fuel h t v b) := by
      intro h t v b; rw [Arena.instLPArmLet]; xfree_walk [ih, g, st, sl, sls, r1, r2, r3, r4, r5, r6, r7, r8, a0, a1, a2, a3]
    have a5 : ∀ h n i e, XFree (Arena.instLPArmProj ks us fuel h n i e) := by
      intro h n i e; rw [Arena.instLPArmProj]; xfree_walk [ih, g, st, sl, sls, r1, r2, r3, r4, r5, r6, r7, r8, a0, a1, a2, a3, a4]
    rw [Arena.instLPGo_succ]; xfree_walk [ih, g, st, sl, sls, r1, r2, r3, r4, r5, r6, r7, r8, a0, a1, a2, a3, a4, a5]

theorem XFree.instLPFast (fuel : Nat) (ks : List NIdx) (us : LsIdx) (e : EIdx) :
    XFree (Arena.instLPFast fuel ks us e) := by
  have hx1 := XFree.instLPGo; have hx2 := XFree.instLPClear
  have hx3 := XFree.readNamesM; have hx4 := XFree.readLevelsM
  unfold Arena.instLPFast; xfree_walk [hx1, hx2, hx3, hx4]

/-! ## The spine walks -/

theorem XFree.getAppArgs : ∀ (fuel : Nat) (h : EIdx), XFree (Arena.getAppArgs fuel h)
  | 0, _ => by unfold Arena.getAppArgs; exact XFree.fail _
  | fuel + 1, h => by
    have ih := XFree.getAppArgs fuel
    unfold Arena.getAppArgs; xfree_walk [ih]

theorem XFree.piResult : ∀ (fuel : Nat) (h : EIdx), XFree (Arena.piResult fuel h)
  | 0, _ => by unfold Arena.piResult; exact XFree.fail _
  | fuel + 1, h => by
    have ih := XFree.piResult fuel
    unfold Arena.piResult; xfree_walk [ih]

theorem XFree.exprGetD (xs : List EIdx) (i : Nat) : XFree (Arena.exprGetD xs i) := by
  unfold Arena.exprGetD; xfree_walk []

theorem XFree.exprDropVars : ∀ (n : Nat) (e : EIdx), XFree (Arena.exprDropVars n e)
  | 0, _ => by unfold Arena.exprDropVars; exact XFree.pure _
  | n + 1, e => by
    have ih := XFree.exprDropVars n
    have hx1 := XFree.zeroLevel; have hx2 := XFree.instantiate1Fast
    unfold Arena.exprDropVars; xfree_walk [ih, hx1, hx2]

/-! ## The recursor's own type -/

theorem XFree.piTele : ∀ (fuel : Nat) (h : EIdx), XFree (Arena.piTele fuel h)
  | 0, _ => by unfold Arena.piTele; exact XFree.fail _
  | fuel + 1, h => by
    have ih := XFree.piTele fuel
    unfold Arena.piTele; xfree_walk [ih]

theorem XFree.motiveLevel? (pre : List EIdx) (nIdx : Nat) (body : EIdx) :
    XFree (Arena.motiveLevel? pre nIdx body) := by
  have ga := XFree.getAppFn; have gd := XFree.exprGetD; have pr := XFree.piResult
  unfold Arena.motiveLevel?; xfree_walk [ga, gd, pr]

theorem XFree.iotaFrame (cv : IConstantVal) (mI rP : Nat) : XFree (Arena.iotaFrame cv mI rP) := by
  have sp := XFree.stripPis; have ml := XFree.motiveLevel?
  unfold Arena.iotaFrame; xfree_walk [sp, ml]

theorem XFree.isMinorAt (pre : List EIdx) (mot q : Nat) : XFree (Arena.isMinorAt pre mot q) := by
  have ga := XFree.getAppFn; have gd := XFree.exprGetD; have pt := XFree.piTele
  unfold Arena.isMinorAt; xfree_walk [ga, gd, pt]

theorem XFree.minorsFrom (pre : List EIdx) (mot q : Nat) : XFree (Arena.minorsFrom pre mot q) := by
  rw [Arena.minorsFrom]
  split
  · rename_i hq
    have ih := XFree.minorsFrom pre mot (q + 1)
    have im := XFree.isMinorAt pre mot
    xfree_walk [ih, im]
  · exact XFree.pure _
termination_by pre.length - q

theorem XFree.iotaRecMajor (pre doms : List EIdx) (nIdx rP k : Nat) :
    XFree (Arena.iotaRecMajor pre doms nIdx rP k) := by
  have mf := XFree.minorsFrom; have gd := XFree.exprGetD; have ga := XFree.getAppFn
  have gr := XFree.getAppArgs
  have dv : ∀ (l : List EIdx), XFree (l.mapM (Arena.exprDropVars nIdx)) :=
    XFree.mapM (XFree.exprDropVars nIdx)
  unfold Arena.iotaRecMajor; xfree_walk [mf, gd, ga, gr, dv]

theorem XFree.iotaRecOf (cv : IConstantVal) (mI rP : Nat) : XFree (Arena.iotaRecOf cv mI rP) := by
  have fr := XFree.iotaFrame; have ga := XFree.getAppFn; have rm := XFree.iotaRecMajor
  unfold Arena.iotaRecOf; xfree_walk [fr, ga, rm]

theorem XFree.liftFieldDoms (amt : Nat) :
    ∀ (ds : List EIdx) (j : Nat), XFree (Arena.liftFieldDoms amt ds j)
  | [], _ => by unfold Arena.liftFieldDoms; exact XFree.pure _
  | d :: ds, j => by
    have ih := XFree.liftFieldDoms amt ds; have lf := XFree.liftLooseBVarsFast
    unfold Arena.liftFieldDoms; xfree_walk [ih, lf]

theorem XFree.liftIdxArgs (amt nT nF : Nat) :
    ∀ (as : List EIdx), XFree (Arena.liftIdxArgs amt nT nF as)
  | [] => by unfold Arena.liftIdxArgs; exact XFree.pure _
  | a :: as => by
    have ih := XFree.liftIdxArgs amt nT nF as; have lf := XFree.liftLooseBVarsFast
    have dv := XFree.exprDropVars
    unfold Arena.liftIdxArgs; xfree_walk [ih, lf, dv]

theorem XFree.iotaPartsOfAt (rr : IotaRec) (rP nIdx i : Nat) (rl : IRecRule) :
    XFree (Arena.iotaPartsOfAt rr rP nIdx i rl) := by
  have gd := XFree.exprGetD; have sp := XFree.stripPis; have fd := XFree.liftFieldDoms
  have pt := XFree.piTele; have gr := XFree.getAppArgs; have ia := XFree.liftIdxArgs
  unfold Arena.iotaPartsOfAt; xfree_walk [gd, sp, fd, pt, gr, ia]

/-! ## The constructor's reading -/

theorem XFree.ctorLevelsAt (rl : IRecRule) (lps : List NIdx) :
    XFree (Arena.ctorLevelsAt rl lps) := by
  have il := XFree.internLsNode; have pl := XFree.paramLevels
  unfold Arena.ctorLevelsAt; xfree_walk [il, pl]

theorem XFree.iotaBVars (rP n i : Nat) : XFree (Arena.iotaBVars rP n i) := by
  rw [Arena.iotaBVars]
  split
  · rename_i hi
    have ih := XFree.iotaBVars rP n (i + 1)
    xfree_walk [ih]
  · exact XFree.pure _
termination_by n - i

theorem XFree.iotaParamsAt (rl : IRecRule) (rP cnP : Nat) : XFree (Arena.iotaParamsAt rl rP cnP) := by
  have ib := XFree.iotaBVars
  unfold Arena.iotaParamsAt; xfree_walk [ib]

theorem XFree.iotaPartsAtBody (cnP mI rP : Nat) (rl : IRecRule) (lvls : LsIdx)
    (params pd : List EIdx) (b : EIdx) :
    XFree (Arena.iotaPartsAtBody cnP mI rP rl lvls params pd b) := by
  have il := XFree.instantiateLiftFast; have sp := XFree.stripPis; have gr := XFree.getAppArgs
  unfold Arena.iotaPartsAtBody; xfree_walk [il, sp, gr]

theorem XFree.iotaPartsAt (cvj : IConstantVal) (cnP mI rP : Nat) (rl : IRecRule) :
    XFree (Arena.iotaPartsAt cvj cnP mI rP rl) := by
  have cl := XFree.ctorLevelsAt; have ip := XFree.iotaParamsAt; have lp := XFree.instLPFast
  have sp := XFree.stripPis; have pb := XFree.iotaPartsAtBody
  unfold Arena.iotaPartsAt; xfree_walk [cl, ip, lp, sp, pb]

/-! ## The checker's rule -/

theorem XFree.lvlEq : ∀ (fuel : Nat) (a b : EIdx), XFree (Arena.lvlEq fuel a b)
  | 0, _, _ => by unfold Arena.lvlEq; exact XFree.fail _
  | fuel + 1, a, b => by
    have ih := XFree.lvlEq fuel; have rl := XFree.readLevelM; have rls := XFree.readLevelsM
    unfold Arena.lvlEq; xfree_walk [ih, rl, rls]

theorem XFree.topName (s : String) : XFree (Arena.topName s) := by
  have nn := XFree.internNNode
  unfold Arena.topName; xfree_walk [nn]

theorem XFree.annWitness (fe : IFEnv) (D : EIdx) : XFree (Arena.annWitness fe D) := by
  have nn := XFree.internNNode
  unfold Arena.annWitness; xfree_walk [nn]

theorem XFree.annIdentBody (fe : IFEnv) (p p' : NIdx) (arity : Nat) (b : EIdx) :
    XFree (Arena.annIdentBody fe p p' arity b) := by
  have aw := XFree.annWitness fe
  unfold Arena.annIdentBody; xfree_walk [aw]

theorem XFree.annIdentVal (fe : IFEnv) (lps : List NIdx) (arity : Nat) (v : EIdx) :
    XFree (Arena.annIdentVal fe lps arity v) := by
  have ab := XFree.annIdentBody fe
  unfold Arena.annIdentVal; xfree_walk [ab]

theorem XFree.annIdent (fe : IFEnv) (n : NIdx) (arity : Nat) : XFree (Arena.annIdent fe n arity) := by
  have av := XFree.annIdentVal fe
  unfold Arena.annIdent; xfree_walk [av]

theorem XFree.annEq (fe : IFEnv) : ∀ (fuel : Nat) (a b : EIdx), XFree (Arena.annEq fe fuel a b)
  | 0, _, _ => by unfold Arena.annEq; exact XFree.fail _
  | fuel + 1, a, b => by
    have ih := XFree.annEq fe fuel; have le := XFree.lvlEq; have tn := XFree.topName
    have ai := XFree.annIdent fe
    unfold Arena.annEq; xfree_walk [ih, le, tn, ai]

theorem XFree.listLvlEq : ∀ (as bs : List EIdx), XFree (Arena.listLvlEq as bs)
  | [], [] => by unfold Arena.listLvlEq; exact XFree.pure _
  | [], _ :: _ => by unfold Arena.listLvlEq; exact XFree.pure _
  | _ :: _, [] => by unfold Arena.listLvlEq; exact XFree.pure _
  | a :: as, b :: bs => by
    have ih := XFree.listLvlEq as bs; have le := XFree.lvlEq
    unfold Arena.listLvlEq; xfree_walk [ih, le]

theorem XFree.listAnnEq (fe : IFEnv) : ∀ (as bs : List EIdx), XFree (Arena.listAnnEq fe as bs)
  | [], [] => by unfold Arena.listAnnEq; exact XFree.pure _
  | [], _ :: _ => by unfold Arena.listAnnEq; exact XFree.pure _
  | _ :: _, [] => by unfold Arena.listAnnEq; exact XFree.pure _
  | a :: as, b :: bs => by
    have ih := XFree.listAnnEq fe as bs; have ae := XFree.annEq fe
    unfold Arena.listAnnEq; xfree_walk [ih, ae]

theorem XFree.paramsAnnEq (fe : IFEnv) (cnP : Nat) (cv : IConstantVal) (pd : List EIdx) :
    XFree (Arena.paramsAnnEq fe cnP cv pd) := by
  have sp := XFree.stripPis; have la := XFree.listAnnEq fe
  unfold Arena.paramsAnnEq; xfree_walk [sp, la]

theorem XFree.iotaPartsRel (fe : IFEnv) (cnP : Nat) (cv : IConstantVal) (rl : IRecRule)
    (p' p : IIotaParts) (pd : List EIdx) : XFree (Arena.iotaPartsRel fe cnP cv rl p' p pd) := by
  have ll := XFree.listLvlEq; have pa := XFree.paramsAnnEq fe; have la := XFree.listAnnEq fe
  unfold Arena.iotaPartsRel; xfree_walk [ll, pa, la]

theorem XFree.ruleReads (fe : IFEnv) (cv : IConstantVal) (rr : Option IotaRec) (mI rP i : Nat)
    (rl : IRecRule) : XFree (Arena.ruleReads fe cv rr mI rP i rl) := by
  have po := XFree.iotaPartsOfAt; have pa := XFree.iotaPartsAt; have pr := XFree.iotaPartsRel fe
  unfold Arena.ruleReads; xfree_walk [po, pa, pr]

theorem XFree.rulesRead (fe : IFEnv) (cv : IConstantVal) (rr : Option IotaRec) (mI rP : Nat) :
    ∀ (rules : List IRecRule) (i : Nat), XFree (Arena.rulesRead fe cv rr mI rP rules i)
  | [], _ => by unfold Arena.rulesRead; exact XFree.pure _
  | rl :: rest, i => by
    have ih := XFree.rulesRead fe cv rr mI rP rest; have rr' := XFree.ruleReads fe cv rr mI rP
    unfold Arena.rulesRead; xfree_walk [ih, rr']

theorem XFree.recReads (fe : IFEnv) (ci : IConstantInfo) : XFree (Arena.recReads fe ci) := by
  have ro := XFree.iotaRecOf; have rs := XFree.rulesRead fe
  unfold Arena.recReads; xfree_walk [ro, rs]

/-- **The ι reading rule keeps the scratch flag**: every recursor's rules read, the scratch
tier neither opened nor dropped. -/
theorem XFree.recsRead (fe : IFEnv) : ∀ (l : List IConstantInfo), XFree (Arena.recsRead fe l)
  | [] => by unfold Arena.recsRead; exact XFree.pure _
  | ci :: rest => by
    have ih := XFree.recsRead fe rest; have rr := XFree.recReads fe
    unfold Arena.recsRead; xfree_walk [ih, rr]

end ConRon.Bridge.Inductives
