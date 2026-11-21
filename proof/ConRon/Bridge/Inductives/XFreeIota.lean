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

/-- con-leche: none — a run whose answer state has the store it started with. -/
theorem XFree.of_store {α : Type} {c : AM α}
    (h : ∀ (s s' : AState) (r : α), c s = .ok (r, s') → s'.store = s.store) : XFree c :=
  fun s s' r hr => by rw [h s s' r hr]

theorem XFree.failDanglingE' {α : Type} : XFree (failDanglingE : AM α) := XFree.fail _
theorem XFree.failDanglingLs {α : Type} : XFree (failDanglingLs : AM α) := XFree.fail _

theorem XFree.derivedE (h : EIdx) : XFree (Arena.derivedE h) := by unfold Arena.derivedE; xfree_auto
theorem XFree.viewBVar (h : EIdx) : XFree (Arena.viewBVar h) := by unfold Arena.viewBVar; xfree_auto
theorem XFree.viewSort (h : EIdx) : XFree (Arena.viewSort h) := by unfold Arena.viewSort; xfree_auto
theorem XFree.viewLsLen (h : LsIdx) : XFree (Arena.viewLsLen h) := by
  unfold Arena.viewLsLen; xfree_auto
theorem XFree.viewL (h : LIdx) : XFree (Arena.viewL h) := by unfold Arena.viewL; xfree_auto

/-! ## The memo tables and the readback caches -/

/-- The state read, a state with its memos or caches rewritten set. -/
macro "xfree_set" : tactic => `(tactic| (intro s s' x h;
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h; obtain ⟨rfl, rfl⟩ := AM.get_ok h1;
  dsimp only at h2; rw [AM.set_ok h2]))

theorem XFree.liftGet (k : EIdx × Nat) : XFree (Arena.liftGet k) := by unfold Arena.liftGet; xfree_auto
theorem XFree.liftSet (k : EIdx × Nat) (r : EIdx) : XFree (Arena.liftSet k r) := by
  unfold Arena.liftSet; xfree_set
theorem XFree.liftClear : XFree Arena.liftClear := by unfold Arena.liftClear; xfree_set
theorem XFree.inst1Get (k : EIdx × Nat) : XFree (Arena.inst1Get k) := by
  unfold Arena.inst1Get; xfree_auto
theorem XFree.inst1Set (k : EIdx × Nat) (r : EIdx) : XFree (Arena.inst1Set k r) := by
  unfold Arena.inst1Set; xfree_set
theorem XFree.inst1Clear : XFree Arena.inst1Clear := by unfold Arena.inst1Clear; xfree_set
theorem XFree.inst1LGet (k : EIdx × Nat) : XFree (Arena.inst1LGet k) := by
  unfold Arena.inst1LGet; xfree_auto
theorem XFree.inst1LSet (k : EIdx × Nat) (r : EIdx) : XFree (Arena.inst1LSet k r) := by
  unfold Arena.inst1LSet; xfree_set
theorem XFree.inst1LClear : XFree Arena.inst1LClear := by unfold Arena.inst1LClear; xfree_set
theorem XFree.instLPGet (k : EIdx × Nat) : XFree (Arena.instLPGet k) := by
  unfold Arena.instLPGet; xfree_auto
theorem XFree.instLPSet (k : EIdx × Nat) (r : EIdx) : XFree (Arena.instLPSet k r) := by
  unfold Arena.instLPSet; xfree_set
theorem XFree.instLPClear : XFree Arena.instLPClear := by unfold Arena.instLPClear; xfree_set
theorem XFree.instLPLGet (h : LIdx) : XFree (Arena.instLPLGet h) := by
  unfold Arena.instLPLGet; xfree_auto
theorem XFree.instLPLSet (h r : LIdx) : XFree (Arena.instLPLSet h r) := by
  unfold Arena.instLPLSet; xfree_set
theorem XFree.instLPLsGet (h : LsIdx) : XFree (Arena.instLPLsGet h) := by
  unfold Arena.instLPLsGet; xfree_auto
theorem XFree.instLPLsSet (h r : LsIdx) : XFree (Arena.instLPLsSet h r) := by
  unfold Arena.instLPLsSet; xfree_set
theorem XFree.bvarBGet (k : EIdx) : XFree (Arena.bvarBGet k) := by unfold Arena.bvarBGet; xfree_auto
theorem XFree.bvarBSet (k : EIdx) (r : Nat) : XFree (Arena.bvarBSet k r) := by
  unfold Arena.bvarBSet; xfree_set
theorem XFree.bvarBClear : XFree Arena.bvarBClear := by unfold Arena.bvarBClear; xfree_set

/-- A memoised readback: a hit answers, a miss reads the store and records the row. -/
macro "xfree_read" : tactic => `(tactic| (intro s s' x h;
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h; obtain ⟨rfl, rfl⟩ := AM.get_ok h1;
  split at h2
  · obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  · split at h2
    · exact absurd h2 (fun h => AM.fail_ok h)
    · dsimp only at h2
      obtain ⟨_, _, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨-, rfl⟩ := AM.pure_ok h4
      rw [AM.set_ok h3]))

theorem XFree.readLevelM (h : LIdx) : XFree (Arena.readLevelM h) := by
  unfold Arena.readLevelM; xfree_read
theorem XFree.readNameM (h : NIdx) : XFree (Arena.readNameM h) := by
  unfold Arena.readNameM; xfree_read
theorem XFree.readLevelsM (h : LsIdx) : XFree (Arena.readLevelsM h) := by
  unfold Arena.readLevelsM
  intro s s' x h
  obtain ⟨_, _, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  split at h2
  · obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  · split at h2
    · exact absurd h2 (fun h => AM.fail_ok h)
    · dsimp only at h2
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
  repeat (first | rfl | split)

theorem EStore.internBind_scr (st : EStore) (tag : UInt32) (ty b : EIdx) :
    (st.internBind tag ty b).1.scratchOn = st.scratchOn := by
  unfold EStore.internBind
  repeat (first | rfl | split)

/-- An intern of the expression store: the state read, a probe, the store's own intern set. -/
macro "xfree_internE" lem:term : tactic => `(tactic| (intro s s' r h;
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok h; obtain ⟨rfl, rfl⟩ := AM.get_ok h1;
  split at h2
  · obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl
  · dsimp only at h2
    split at h2
    · repeat (first | split at h2 | skip)
      all_goals first
        | (obtain ⟨_, s₂, k, z⟩ := AM.bind_ok h2
           obtain ⟨-, rfl⟩ := AM.pure_ok z
           rw [AM.set_ok k]
           exact $lem)
        | exact absurd h2 (fun h => AM.fail_ok h)
    · exact absurd h2 (fun h => AM.fail_ok h)))

theorem XFree.internNodeE (v : ENodeView) : XFree (Arena.internNodeE v) := by
  unfold Arena.internNodeE; xfree_internE (EStore.intern_scr _ _)
theorem XFree.internLamE (ty b : EIdx) : XFree (Arena.internLamE ty b) := by
  unfold Arena.internLamE; xfree_internE (EStore.internBind_scr _ _ _ _)
theorem XFree.internForallEE (ty b : EIdx) : XFree (Arena.internForallEE ty b) := by
  unfold Arena.internForallEE; xfree_internE (EStore.internBind_scr _ _ _ _)
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

end ConRon.Bridge.Inductives
