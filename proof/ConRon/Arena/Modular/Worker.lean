/-
# `ConRon.Arena.Modular.Worker` — a worker's reads and its own records (task #166)

The twin of `frontend/modular/worker.rs`: the type a worker's phases 1–4 build.
-/
module

public import ConRon.Arena.Modular.Reach
public import ConRon.Arena.Frontend.Olean.Records

@[expose] public section

namespace ConRon.Arena.Modular

open ConLeche
open ConRon.Arena.Frontend.Olean
open ConLeche.Frontend.Olean (Expo)

/-- con-leche: ConLeche/Driver/Worker.lean:271-289 WorkerRead
**What a worker has read and checked before its jobs.** -/
structure WorkerRead where
  home : Loaded
  expo : Array Expo
  reads : WorkerReads
  emitted : Array IDeclaration
  own : Array IDeclaration
  reach : Reach
  hoisted : Array NIdx
  values : ValueCache

end ConRon.Arena.Modular
