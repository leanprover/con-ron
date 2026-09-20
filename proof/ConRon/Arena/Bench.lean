/-
# `con-ron-arena-bench` — the `ExprOps` micro-benchmark (task #97 P2b)

The performance phase comes before the proofs now, so the memo and cutoff
choices of `ExprOps.lean` have to be measurable from the day they are made.
This is that measurement, at module scope: build a large term in the arena
and run `instantiate1` / `abstract1` / `instantiateLevelParams` over it,
printing wall time per operation.

    lake -C proof build con-ron-arena-bench
    proof/.lake/build/bin/con-ron-arena-bench

Three shapes, because they separate three different costs:

* **the spine** `((… ((bvar 1) x) x) …) x`, 50 000 `app` nodes deep — a term
  with no sharing at all, so a walk over it does 50 000 interns and the memo
  never hits.  This is the *worst* case for the memo (it pays for a table it
  never reads) and the honest baseline for "what does one pass cost".
* **the telescope** `∀ ty, ∀ ty, … (bvar 10000)`, 10 000 binders — the shape
  `openPisAtFvars` walks one binder at a time (con-leche's task #215: the
  reason `instantiate1` is memoized at all), and the shape whose cursor moves
  under every binder.
* **the DAG tower** `t₀ = bvar 1`, `t_{k+1} = app t_k t_k`, k = 24 — 25 arena
  nodes denoting a tree of 2^24 = 16.7 M nodes.  **This is the measurement
  the memo exists for.**  A walk without a memo is 2^24 steps; with one it is
  25.  If the memo is ever removed this benchmark goes from milliseconds to
  never finishing, which is a more useful regression test than any assertion.

Every operation is run on a store built once, and the `…Fast` entries clear
their memo before and after, so the numbers are per-call and comparable.

This module is NOT part of `lean_lib ConRonArena` (it is an executable root),
and it is the only file under `Arena/` that does `IO`.
-/
import ConRon.Arena.ExprOps

namespace ConRon.Arena.Bench

open ConLeche ConRon.Arena

/-- con-leche: none — benchmark scaffolding: the fuel every run uses.  The
deepest shape is 50 000 nodes, so 200 000 is a comfortable margin and no run
below ever reaches it. -/
def benchFuel : Nat := 200000

/-- con-leche: none — benchmark scaffolding: build a left-nested application
spine of `n` `app` nodes over a fixed argument.  Structural on `n`. -/
def mkSpine (arg : EIdx) : Nat → EIdx → AM EIdx
  | 0, acc => pure acc
  | n + 1, acc => do
    let acc' ← internE (.app acc arg)
    mkSpine arg n acc'

/-- con-leche: none — benchmark scaffolding: build a `∀`-telescope of `n`
binders over a fixed domain, innermost body first. -/
def mkTele (dom : EIdx) : Nat → EIdx → AM EIdx
  | 0, body => pure body
  | n + 1, body => do
    let body' ← internE (.forallE dom body ⟨.never⟩)
    mkTele dom n body'

/-- con-leche: none — benchmark scaffolding: the DAG tower
`t_{k+1} = app t_k t_k`.  `k` arena nodes, `2^k` tree nodes. -/
def mkTower : Nat → EIdx → AM EIdx
  | 0, t => pure t
  | k + 1, t => do
    let t' ← internE (.app t t)
    mkTower k t'

/-- con-leche: none — benchmark scaffolding: the arena the runs share, and
the handles they name. -/
structure Fixture where
  spine : EIdx
  plain : EIdx
  tele : EIdx
  peel : EIdx
  tower : EIdx
  sub : EIdx
  fv : EIdx
  uName : NIdx
  usZero : LsIdx

/-- con-leche: none — benchmark scaffolding: build the three shapes.

The shapes are chosen so that no cutoff fires at the root, which is the
point: a benchmark whose subject the `bvarB`/`fvarB` test answers in `O(1)`
measures the cutoff and nothing else.  The spine's head is `bvar 1` and its
argument an `fvar`, so both the loose-bvar bound and the fvar range are
positive; the telescope's body is `bvar n`, so after `n` binders its bound is
exactly 1; the tower's leaf is `bvar 1`. -/
def build (spineN teleN towerK : Nat) : AM Fixture := do
  let anon ← internNNode .anonymous
  let uName ← internNNode (.str anon "u")
  let zero ← internLNode .zero
  let pu ← internLNode (.param uName)
  let usZero ← internLsNode [zero]
  let s0 ← internE (.sort zero)
  let su ← internE (.sort pu)
  let fv ← internE (.fvar 0 su)
  let b1 ← internE (.bvar 1)
  let spine ← mkSpine fv spineN b1
  let plain ← mkSpine s0 spineN b1
  let bn ← internE (.bvar teleN)
  let tele ← mkTele su teleN bn
  let bp ← internE (.bvar 1000)
  let peel ← mkTele s0 1000 bp
  let tower ← mkTower towerK b1
  let sub ← internE (.const uName usZero)
  pure { spine, plain, tele, peel, tower, sub, fv, uName, usZero }

/-- con-leche: none — benchmark scaffolding: **con-leche's task #215
workload**, the one that made `instantiate1` memoized in the first place:
`openPisAtFvars` opens a `∀`-telescope ONE BINDER AT A TIME, so a telescope
of `n` binders costs `n` instantiations over a body that is still `O(n)`
wide.  This is the loop, written as explicit tail recursion over the binder
count (no `for`, no `mut`; DESIGN §8.4). -/
def peelPis (fuel : Nat) (arg : EIdx) : Nat → EIdx → AM Nat
  | 0, h => pure h.word.toNat
  | n + 1, h => do
    match ← view h with
    | .forallE _ body _ => do
      let b ← instantiate1Fast fuel body arg 0
      peelPis fuel arg n b
    | _ => pure h.word.toNat

/-- con-leche: none — benchmark scaffolding: run one `AM` action against a
mutable reference holding the state, time it, and print. -/
def timed (label : String) (st : IO.Ref AState) (act : AM Nat) : IO Unit := do
  let s ← st.get
  let t0 ← IO.monoNanosNow
  match act.run s with
  | .ok (n, s') =>
    let t1 ← IO.monoNanosNow
    st.set s'
    let ms := (t1 - t0).toFloat / 1000000.0
    IO.println s!"  {label}: {ms} ms   (result {n})"
  | .error _ =>
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0).toFloat / 1000000.0
    IO.println s!"  {label}: FAILED after {ms} ms"

/-- con-leche: none — benchmark scaffolding: the store's node count, so that
every timed line also reports how much the arena grew. -/
def nodes (st : IO.Ref AState) : IO Nat := do
  let s ← st.get
  pure s.store.nodeCount

/-- con-leche: none — the benchmark. -/
def main (_args : List String) : IO UInt32 := do
  let spineN := 50000
  let teleN := 10000
  let towerK := 24
  IO.println s!"con-ron arena ExprOps micro-benchmark"
  IO.println s!"  spine {spineN} apps, telescope {teleN} binders, DAG tower 2^{towerK}"
  let t0 ← IO.monoNanosNow
  match (build spineN teleN towerK).run (AState.init EStore.empty) with
  | .error _ => IO.println "build FAILED"; pure 1
  | .ok (fx, s0) => do
    let t1 ← IO.monoNanosNow
    IO.println s!"  intern (all three shapes): {(t1 - t0).toFloat / 1000000.0} ms, {s0.store.nodeCount} nodes"
    let st ← IO.mkRef s0
    IO.println "the spine (no sharing: the memo never hits)"
    timed "instantiate1Fast  " st (do
      let r ← instantiate1Fast benchFuel fx.spine fx.sub 1; pure r.word.toNat)
    timed "abstract1Fast     " st (do
      let r ← abstract1Fast benchFuel fx.spine 0 0; pure r.word.toNat)
    timed "instLPFast        " st (do
      let r ← instLPFast benchFuel [fx.uName] fx.usZero fx.spine; pure r.word.toNat)
    timed "bvarBoundMemo     " st (bvarBoundMemo benchFuel fx.spine)
    timed "sizeB             " st (sizeB benchFuel fx.spine)
    IO.println s!"  arena now {← nodes st} nodes"
    IO.println "the telescope (the cursor moves under every binder)"
    timed "instantiate1Fast  " st (do
      let r ← instantiate1Fast benchFuel fx.tele fx.sub 0; pure r.word.toNat)
    timed "abstract1Fast     " st (do
      let r ← abstract1Fast benchFuel fx.tele 0 0; pure r.word.toNat)
    timed "instLPFast        " st (do
      let r ← instLPFast benchFuel [fx.uName] fx.usZero fx.tele; pure r.word.toNat)
    timed "liftLooseBVarsFast" st (do
      let r ← liftLooseBVarsFast benchFuel 1 0 fx.tele; pure r.word.toNat)
    IO.println s!"  arena now {← nodes st} nodes"
    IO.println s!"the DAG tower ({towerK} arena nodes, 2^{towerK} tree nodes)"
    IO.println "  -- without the memo every one of these is exponential"
    timed "instantiate1Fast  " st (do
      let r ← instantiate1Fast benchFuel fx.tower fx.sub 1; pure r.word.toNat)
    timed "instantiate1LiftF " st (do
      let r ← instantiate1LiftFast benchFuel fx.tower fx.sub 1; pure r.word.toNat)
    timed "instLPFast        " st (do
      let r ← instLPFast benchFuel [fx.uName] fx.usZero fx.tower; pure r.word.toNat)
    timed "bvarBoundMemo     " st (bvarBoundMemo benchFuel fx.tower)
    IO.println s!"  arena now {← nodes st} nodes"
    IO.println "con-leche's task #215 workload: peel a 1000-binder telescope"
    IO.println "  one binder at a time (`openPisAtFvars`) -- 1000 instantiations"
    timed "peelPis x1000     " st (peelPis benchFuel fx.fv 1000 fx.peel)
    IO.println s!"  arena now {← nodes st} nodes"
    IO.println "the cutoffs (the subject is answered without a walk)"
    timed "instantiate1 (cut)" st (do
      let r ← instantiate1Fast benchFuel fx.tele fx.sub 5000; pure r.word.toNat)
    timed "abstract1    (cut)" st (do
      let r ← abstract1Fast benchFuel fx.plain 7 0; pure r.word.toNat)
    timed "instLP       (cut)" st (do
      let r ← instLPFast benchFuel [fx.uName] fx.usZero fx.plain; pure r.word.toNat)
    IO.println "the same three on a subject the cutoff does NOT answer"
    timed "instantiate1 (run)" st (do
      let r ← instantiate1Fast benchFuel fx.plain fx.sub 1; pure r.word.toNat)
    timed "abstract1    (run)" st (do
      let r ← abstract1Fast benchFuel fx.spine 0 0; pure r.word.toNat)
    timed "instLP       (run)" st (do
      let r ← instLPFast benchFuel [fx.uName] fx.usZero fx.spine; pure r.word.toNat)
    pure 0

end ConRon.Arena.Bench

/-- con-leche: none — the executable's entry point. -/
def main (args : List String) : IO UInt32 := ConRon.Arena.Bench.main args
