#!/usr/bin/env python3
"""Task #63, route A(1): the *table lookup* cost of a kernel-evaluated
reference decoder.

`ConRon.Dump.parsePins` resolves every `E`/`N` record's operand ids against
the table of nodes decoded so far: 26 512 lookups into a table that grows to
26 512.  With the table a `List` that is O(n) per lookup, which is the term
the whole closed computation is dominated by.  This file measures both
candidates in the kernel at size N:

  list   -- table as a `List Nat`, lookup by index recursion
  trie   -- table as a binary trie on the key's bits (GMP `%`/`/` on `Nat`)

Usage: gentable.py <list|trie> <N> <outfile>
"""
import sys

HEAD = """set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 10

def keys : List Nat := [%s]
"""

LIST = """
def lget : Nat -> List Nat -> Nat
  | _, [] => 0
  | 0, v :: _ => v
  | Nat.succ n, _ :: r => lget n r

def lsum : List Nat -> List Nat -> Nat
  | [], _ => 0
  | k :: r, tb => lget k tb + lsum r tb

theorem t : lsum keys keys = %d := by rfl
"""

TRIE = """
inductive T where
  | nil
  | node (v : Nat) (l r : T)

def ins (f k v : Nat) (t : T) : T :=
  match f with
  | 0 => T.node v T.nil T.nil
  | Nat.succ f' =>
    match t with
    | T.nil =>
      if k %% 2 == 0 then T.node 0 (ins f' (k / 2) v T.nil) T.nil
      else T.node 0 T.nil (ins f' (k / 2) v T.nil)
    | T.node w l r =>
      if k %% 2 == 0 then T.node w (ins f' (k / 2) v l) r
      else T.node w l (ins f' (k / 2) v r)

def get (f k : Nat) (t : T) : Nat :=
  match f with
  | 0 => match t with | T.nil => 0 | T.node v _ _ => v
  | Nat.succ f' =>
    match t with
    | T.nil => 0
    | T.node _ l r => if k %% 2 == 0 then get f' (k / 2) l else get f' (k / 2) r

def build : List Nat -> T -> T
  | [], t => t
  | k :: r, t => build r (ins 20 k k t)

def tsum : List Nat -> T -> Nat
  | [], _ => 0
  | k :: r, t => get 20 k t + tsum r t

theorem t : tsum keys (build keys T.nil) = %d := by rfl
"""

if __name__ == "__main__":
    kind, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    ks = ", ".join(str(i) for i in range(n))
    total = n * (n - 1) // 2
    open(out, "w").write(HEAD % ks + (LIST if kind == "list" else TRIE) % total)
