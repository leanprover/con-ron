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

/-! ## The mini arena

Handles are `Nat` and the arrays are `List`s: the Lean twin is written in
Lean-natural types, and the *abstraction* (`ExpCD.lean`) is where `Std.U32`
becomes `Nat` and `alloc.vec.Vec` becomes `List`.  That is the same division
of labour DESIGN §8.4 asks for at full scale — (B) is Rust-*shaped*, not
Rust-*typed*. -/

/-- con-leche: none — `crates/arena-spike/src/lib.rs:16` TAG_BVAR. -/
def mTagBvar : Nat := 0
/-- con-leche: none — `crates/arena-spike/src/lib.rs:18` TAG_APP. -/
def mTagApp : Nat := 1
/-- con-leche: none — `crates/arena-spike/src/lib.rs:20` TAG_LAM. -/
def mTagLam : Nat := 2
/-- con-leche: none — `crates/arena-spike/src/lib.rs:23` IDX_CAP. -/
def mIdxCap : Nat := 268435456

/-- con-leche: none — `crates/arena-spike/src/lib.rs:27` mk. -/
def mMk (tag idx : Nat) : Nat := tag * mIdxCap + idx
/-- con-leche: none — `crates/arena-spike/src/lib.rs:32` tag_of. -/
def mTagOf (h : Nat) : Nat := h / mIdxCap
/-- con-leche: none — `crates/arena-spike/src/lib.rs:37` idx_of. -/
def mIdxOf (h : Nat) : Nat := h % mIdxCap

/-- con-leche: ConLeche/Cached/CoreC.lean:120 CState — the mini state:
three per-constructor arrays and the memo, mirroring
`crates/arena-spike/src/lib.rs:65` State field for field. -/
structure MState where
  bvars : List Nat
  apps : List (Nat × Nat)
  lams : List (Nat × Nat)
  memo : List (Nat × Nat × Nat)

/-- con-leche: none — the empty mini arena. -/
def MState.empty : MState := ⟨[], [], [], []⟩

/-- con-leche: none — `crates/arena-spike/src/lib.rs:92` view_bvar. -/
def MState.viewBvar (st : MState) (h : Nat) : Option Nat :=
  if mTagOf h = mTagBvar then st.bvars[mIdxOf h]? else none

/-- con-leche: none — `crates/arena-spike/src/lib.rs:106` view_app. -/
def MState.viewApp (st : MState) (h : Nat) : Option (Nat × Nat) :=
  if mTagOf h = mTagApp then st.apps[mIdxOf h]? else none

/-- con-leche: none — `crates/arena-spike/src/lib.rs:120` view_lam. -/
def MState.viewLam (st : MState) (h : Nat) : Option (Nat × Nat) :=
  if mTagOf h = mTagLam then st.lams[mIdxOf h]? else none

/-! ## The denotation

Fuel-indexed on the total node count, exactly as `denoteE` is
(`ConRon/Arena/Denote.lean`'s decision, repeated here so the mini layer
carries no extra idea). -/

/-- con-leche: none — the number of nodes in the mini arena. -/
def MState.nodeCount (st : MState) : Nat :=
  st.bvars.length + st.apps.length + st.lams.length

/-- con-leche: ConLeche/Kernel/Expr.lean:344 Expr — the fuel-indexed readback
of a mini handle. -/
def denoteMAux (st : MState) : Nat → Nat → Option Expr
  | 0, _ => none
  | f + 1, h =>
    if mTagOf h = mTagBvar then (st.viewBvar h).map Expr.bvar
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
def denoteM (st : MState) (h : Nat) : Option Expr :=
  denoteMAux st (st.nodeCount + 1) h

/-! ## The twin

`MM` is `AM` over `MState`: the monad §8.4 fixes, at the mini state. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:170 CheckCM — the mini monad. -/
abbrev MM := StateT MState (Except CheckError)

/-- con-leche: ConLeche/Kernel/Core.lean:62 CheckError — the mini failure. -/
def mfail {α : Type} (e : CheckError) : MM α := throwThe CheckError e

/-- con-leche: none — the cons-table probe, shared by the three
constructors: `crates/arena-spike/src/lib.rs:135` find_bvar_from and its two
siblings are this function at three element types.  Structural on the list
(the Rust is an index-carrying recursion over the same list, which
`-loops-to-rec` turns into the same shape). -/
def listFindIdx {α : Type} [BEq α] (l : List α) (k : α) (i : Nat) : Option Nat :=
  match l with
  | [] => none
  | x :: rest => if x == k then some i else listFindIdx rest k (i + 1)

/-- con-leche: none — `crates/arena-spike/src/lib.rs:148` find_bvar. -/
def mFindBvar (st : MState) (k : Nat) : Option Nat :=
  (listFindIdx st.bvars k 0).map (mMk mTagBvar)

/-- con-leche: none — `crates/arena-spike/src/lib.rs:166` find_app. -/
def mFindApp (st : MState) (f a : Nat) : Option Nat :=
  (listFindIdx st.apps (f, a) 0).map (mMk mTagApp)

/-- con-leche: none — `crates/arena-spike/src/lib.rs:185` find_lam. -/
def mFindLam (st : MState) (ty b : Nat) : Option Nat :=
  (listFindIdx st.lams (ty, b) 0).map (mMk mTagLam)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go —
`crates/arena-spike/src/lib.rs:253` memo_get. -/
def mMemoGet (st : MState) (h d : Nat) : Option Nat :=
  match listFindIdx (st.memo.map (fun e => (e.1, e.2.1))) (h, d) 0 with
  | none => none
  | some i => (st.memo[i]?).map (fun e => e.2.2)

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern —
`crates/arena-spike/src/lib.rs:191` intern_bvar. -/
def mInternBvar (k : Nat) : MM Nat := do
  let st ← get
  match mFindBvar st k with
  | some h => pure h
  | none =>
    if st.bvars.length < mIdxCap then
      let arr := st.bvars
      let st := { st with bvars := [] }
      set { st with bvars := arr ++ [k] }
      pure (mMk mTagBvar arr.length)
    else mfail (.internal "arena-spike: bvar array full")

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern —
`crates/arena-spike/src/lib.rs:206` intern_app. -/
def mInternApp (f a : Nat) : MM Nat := do
  let st ← get
  match mFindApp st f a with
  | some h => pure h
  | none =>
    if st.apps.length < mIdxCap then
      let arr := st.apps
      let st := { st with apps := [] }
      set { st with apps := arr ++ [(f, a)] }
      pure (mMk mTagApp arr.length)
    else mfail (.internal "arena-spike: app array full")

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern —
`crates/arena-spike/src/lib.rs:221` intern_lam. -/
def mInternLam (ty b : Nat) : MM Nat := do
  let st ← get
  match mFindLam st ty b with
  | some h => pure h
  | none =>
    if st.lams.length < mIdxCap then
      let arr := st.lams
      let st := { st with lams := [] }
      set { st with lams := arr ++ [(ty, b)] }
      pure (mMk mTagLam arr.length)
    else mfail (.internal "arena-spike: lam array full")

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go —
`crates/arena-spike/src/lib.rs:262` memo_set. -/
def mMemoSet (h d r : Nat) : MM Unit := do
  let st ← get
  let arr := st.memo
  let st := { st with memo := [] }
  set { st with memo := arr ++ [(h, d, r)] }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1, `:81`
instantiate1Go — **the mini twin**, `crates/arena-spike/src/lib.rs:275`
instantiate1, clause for clause. -/
def mInstantiate1 (v : Nat) : Nat → Nat → Nat → MM Nat
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
        match mMemoGet st h d with
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
        match mMemoGet st h d with
        | some r => pure r
        | none => do
          let t' ← mInstantiate1 v fuel ty d
          let b' ← mInstantiate1 v fuel b (d + 1)
          let r ← mInternLam t' b'
          mMemoSet h d r
          pure r
    else mfail (.internal "arena-spike: bad tag")

end ConRon.Arena.Spike
