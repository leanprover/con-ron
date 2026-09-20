/-
# The P2s spike: the mini arena, for experiments C and D

Experiments C and D price **Theorem 2** — the refinement of the extracted
Rust by the Lean model — and the one-layer alternative.  Doing that against
task #97a's real `EStore` would mean building an abstraction that produces
all ten constructor arrays, the cons tables, the derived words and the rank
witness, and proving `StoreWF` of it: that is P4a's job, not a spike's.

So the spike carries a **mini arena**: three constructors (`bvar`, `app`,
`lam`), one tier, hash-consing by linear scan, a `Vec` memo — exactly what
`crates/arena-spike/src/lib.rs` implements, and exactly the part of the store
API `instantiate1` touches.  Two layers, same as the real thing:

* `MState` + `instantiate1M` — the (B)-shaped Lean twin (this module);
* `Generated.State` + `Generated.instantiate1` — the Aeneas model of the Rust
  (`Spike/Generated/*.lean`, produced by `scripts/extract-spike.sh`).

`denoteM` is the denotation into con-leche's `Expr`, so the same three
statements are available as in the real tower:

* **C1** `ExpC.lean` — the Rust model refines the twin (no `Expr` anywhere);
* **C2** `ExpC.lean` — the twin refines con-leche's `instantiate1` (the
  `mvcgen` recipe of experiment A, at three constructors);
* **D**  `ExpD.lean` — the Rust model refines con-leche's `instantiate1`
  *directly*, in one induction.
-/
import ConRon.Arena.Spike.Twins

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false

/-! ## The mini arena -/

/-- con-leche: none — `crates/arena-spike/src/lib.rs:16` TAG_BVAR. -/
def mTagBvar : UInt32 := 0
/-- con-leche: none — `crates/arena-spike/src/lib.rs:18` TAG_APP. -/
def mTagApp : UInt32 := 1
/-- con-leche: none — `crates/arena-spike/src/lib.rs:20` TAG_LAM. -/
def mTagLam : UInt32 := 2
/-- con-leche: none — `crates/arena-spike/src/lib.rs:23` IDX_CAP. -/
def mIdxCap : UInt32 := 268435456

/-- con-leche: none — `crates/arena-spike/src/lib.rs:27` mk. -/
def mMk (tag idx : UInt32) : UInt32 := tag * mIdxCap + idx
/-- con-leche: none — `crates/arena-spike/src/lib.rs:32` tag_of. -/
def mTagOf (h : UInt32) : UInt32 := h / mIdxCap
/-- con-leche: none — `crates/arena-spike/src/lib.rs:37` idx_of. -/
def mIdxOf (h : UInt32) : UInt32 := h % mIdxCap

/-- con-leche: ConLeche/Cached/CoreC.lean:120 CState — the mini state:
three per-constructor arrays and the memo, mirroring
`crates/arena-spike/src/lib.rs:65` State field for field. -/
structure MState where
  bvars : Array UInt32
  apps : Array (UInt32 × UInt32)
  lams : Array (UInt32 × UInt32)
  memo : Array (UInt32 × UInt32 × UInt32)

/-- con-leche: none — the empty mini arena. -/
def MState.empty : MState := ⟨#[], #[], #[], #[]⟩

/-- con-leche: none — `crates/arena-spike/src/lib.rs:92` view_bvar. -/
def MState.viewBvar (st : MState) (h : UInt32) : Option UInt32 :=
  if mTagOf h = mTagBvar then st.bvars[(mIdxOf h).toNat]? else none

/-- con-leche: none — `crates/arena-spike/src/lib.rs:106` view_app. -/
def MState.viewApp (st : MState) (h : UInt32) : Option (UInt32 × UInt32) :=
  if mTagOf h = mTagApp then st.apps[(mIdxOf h).toNat]? else none

/-- con-leche: none — `crates/arena-spike/src/lib.rs:120` view_lam. -/
def MState.viewLam (st : MState) (h : UInt32) : Option (UInt32 × UInt32) :=
  if mTagOf h = mTagLam then st.lams[(mIdxOf h).toNat]? else none

/-! ## The denotation

Fuel-indexed on the total node count, exactly as `denoteE` is
(`ConRon/Arena/Denote.lean`'s decision, repeated here so the mini layer
carries no extra idea). -/

/-- con-leche: none — the number of nodes in the mini arena. -/
def MState.nodeCount (st : MState) : Nat := st.bvars.size + st.apps.size + st.lams.size

/-- con-leche: ConLeche/Kernel/Expr.lean:344 Expr — the fuel-indexed readback
of a mini handle. -/
def denoteMAux (st : MState) : Nat → UInt32 → Option Expr
  | 0, _ => none
  | f + 1, h =>
    if mTagOf h = mTagBvar then (st.viewBvar h).map (fun i => .bvar i.toNat)
    else if mTagOf h = mTagApp then
      match st.viewApp h with
      | none => none
      | some (a, b) => opt2 Expr.app (denoteMAux st f a) (denoteMAux st f b)
    else if mTagOf h = mTagLam then
      match st.viewLam h with
      | none => none
      | some (a, b) =>
        opt2 (fun x y => Expr.lam x y default) (denoteMAux st f a) (denoteMAux st f b)
    else none

/-- con-leche: ConLeche/Kernel/Expr.lean:344 Expr — the readback. -/
def denoteM (st : MState) (h : UInt32) : Option Expr :=
  denoteMAux st (st.nodeCount + 1) h

/-! ## The twin

`MM` is `AM` over `MState`: the monad §8.4 fixes, at the mini state. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:170 CheckCM — the mini monad. -/
abbrev MM := StateT MState (Except CheckError)

/-- con-leche: ConLeche/Kernel/Core.lean:62 CheckError — the mini failure. -/
def mfail {α : Type} (e : CheckError) : MM α := throwThe CheckError e

/-- con-leche: none — `crates/arena-spike/src/lib.rs:135` find_bvar_from. -/
def mFindBvarFrom (st : MState) (k : UInt32) : Nat → Option UInt32
  | i =>
    if h : i < st.bvars.size then
      if st.bvars[i] = k then some (mMk mTagBvar (UInt32.ofNat i))
      else mFindBvarFrom st k (i + 1)
    else none
  termination_by i => st.bvars.size - i

/-- con-leche: none — `crates/arena-spike/src/lib.rs:153` find_app_from. -/
def mFindAppFrom (st : MState) (f a : UInt32) : Nat → Option UInt32
  | i =>
    if h : i < st.apps.size then
      if st.apps[i].1 = f && st.apps[i].2 = a then some (mMk mTagApp (UInt32.ofNat i))
      else mFindAppFrom st f a (i + 1)
    else none
  termination_by i => st.apps.size - i

/-- con-leche: none — `crates/arena-spike/src/lib.rs:172` find_lam_from. -/
def mFindLamFrom (st : MState) (ty b : UInt32) : Nat → Option UInt32
  | i =>
    if h : i < st.lams.size then
      if st.lams[i].1 = ty && st.lams[i].2 = b then some (mMk mTagLam (UInt32.ofNat i))
      else mFindLamFrom st ty b (i + 1)
    else none
  termination_by i => st.lams.size - i

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern —
`crates/arena-spike/src/lib.rs:191` intern_bvar. -/
def mInternBvar (k : UInt32) : MM UInt32 := do
  let st ← get
  match mFindBvarFrom st k 0 with
  | some h => pure h
  | none =>
    if st.bvars.size < mIdxCap.toNat then
      let arr := st.bvars
      let st := { st with bvars := #[] }
      set { st with bvars := arr.push k }
      pure (mMk mTagBvar (UInt32.ofNat arr.size))
    else mfail (.internal "arena-spike: bvar array full")

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern —
`crates/arena-spike/src/lib.rs:206` intern_app. -/
def mInternApp (f a : UInt32) : MM UInt32 := do
  let st ← get
  match mFindAppFrom st f a 0 with
  | some h => pure h
  | none =>
    if st.apps.size < mIdxCap.toNat then
      let arr := st.apps
      let st := { st with apps := #[] }
      set { st with apps := arr.push (f, a) }
      pure (mMk mTagApp (UInt32.ofNat arr.size))
    else mfail (.internal "arena-spike: app array full")

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern —
`crates/arena-spike/src/lib.rs:221` intern_lam. -/
def mInternLam (ty b : UInt32) : MM UInt32 := do
  let st ← get
  match mFindLamFrom st ty b 0 with
  | some h => pure h
  | none =>
    if st.lams.size < mIdxCap.toNat then
      let arr := st.lams
      let st := { st with lams := #[] }
      set { st with lams := arr.push (ty, b) }
      pure (mMk mTagLam (UInt32.ofNat arr.size))
    else mfail (.internal "arena-spike: lam array full")

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go —
`crates/arena-spike/src/lib.rs:243` memo_get_from. -/
def mMemoGetFrom (st : MState) (h d : UInt32) : Nat → Option UInt32
  | i =>
    if hi : i < st.memo.size then
      if st.memo[i].1 = h && st.memo[i].2.1 = d then some st.memo[i].2.2
      else mMemoGetFrom st h d (i + 1)
    else none
  termination_by i => st.memo.size - i

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go —
`crates/arena-spike/src/lib.rs:262` memo_set. -/
def mMemoSet (h d r : UInt32) : MM Unit := do
  let st ← get
  let arr := st.memo
  let st := { st with memo := #[] }
  set { st with memo := arr.push (h, d, r) }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1, `:81`
instantiate1Go — **the mini twin**, `crates/arena-spike/src/lib.rs:275`
instantiate1, clause for clause. -/
def mInstantiate1 (v : UInt32) : Nat → UInt32 → UInt32 → MM UInt32
  | 0, _, _ => mfail (.internal "fuel exhausted: instantiate1")
  | fuel + 1, h, d => do
    let st ← get
    let tag := mTagOf h
    if tag = mTagBvar then
      match st.viewBvar h with
      | none => mfail (.internal "arena-spike: dangling handle")
      | some i =>
        if i = d then pure v
        else if d < i then mInternBvar (i - 1)
        else pure h
    else if tag = mTagApp then
      match st.viewApp h with
      | none => mfail (.internal "arena-spike: dangling handle")
      | some (f, a) =>
        match mMemoGetFrom st h d 0 with
        | some r => pure r
        | none => do
          let f' ← mInstantiate1 v fuel f d
          let a' ← mInstantiate1 v fuel a d
          let r ← mInternApp f' a'
          mMemoSet h d r
          pure r
    else if tag = mTagLam then
      match st.viewLam h with
      | none => mfail (.internal "arena-spike: dangling handle")
      | some (ty, b) =>
        match mMemoGetFrom st h d 0 with
        | some r => pure r
        | none => do
          let t' ← mInstantiate1 v fuel ty d
          let b' ← mInstantiate1 v fuel b (d + 1)
          let r ← mInternLam t' b'
          mMemoSet h d r
          pure r
    else mfail (.internal "arena-spike: bad tag")

end ConRon.Arena.Spike
