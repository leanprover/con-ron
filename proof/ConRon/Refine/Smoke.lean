/-
End-to-end smoke test for the extraction pipeline (task #12, P2 of §5).

It proves the task-#5 lemma shape against the *generated crate code*
(`ConRon.Generated`, produced by `scripts/extract.sh` from
`crates/con-ron-core`) rather than against the task-#3 spike, reusing the
spike's `Abs.lean` definitions with `level_name.` renamed to
`ConRon.Generated.` and nothing else changed.  That is the claim
`ConRon/Refine/README.md` makes: the spike's conventions port to the
generated names by renaming alone.

Deliberately small.  The real abstraction tier (`Abs.lean`, `NameWF`,
`LevelWF` and the 27 lemmas of task #5) is P3.1.
-/
import ConRon.Generated
import ConLeche.Kernel.Level

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine

/-! ## Monadic plumbing, adapted from `ConRon/Spike/LevelName/Refine.lean`

The three `Rc` lemmas are `rfl` because `ConRon/Generated/FunsExternal.lean`
models `Rc::new`/`Rc::deref` as the identity (DESIGN.md §3.2). -/

@[local simp] theorem bind_eq_ok_iff {α β : Type} {e : Result α} {f : α → Result β} {v : β} :
    ((do let x ← e; f x) = ok v) ↔ ∃ y, e = ok y ∧ f y = ok v := by
  constructor
  · cases e with
    | ret r => intro h; exact ⟨r, rfl, by simpa using h⟩
    | vis i k => intro h; simp at h
    | div => intro h; simp at h
  · rintro ⟨y, rfl, h⟩; simpa using h

@[local simp] theorem rc_new_eq {T : Type} (x : T) : alloc.rc.Rc.new x = ok x := rfl

@[local simp] theorem rc_deref_eq {T : Type} (A : Type) (x : T) :
    alloc.rc.Rc.Insts.CoreOpsDerefDeref.deref A x = ok x := rfl

/-! ## The abstraction functions, adapted from `ConRon/Spike/LevelName/Abs.lean` -/

/-- A port-side string (`Vec<u32>` of code points, DESIGN.md §3.3) as a Lean
`String`. -/
def absString (s : alloc.vec.Vec Std.U32) : String :=
  String.ofList (s.val.map fun c => Char.ofNat c.val)

/- `ConLeche/Kernel/Name.lean:34` -- the Rust `Name` tree as a `ConLeche.Name`. -/
mutual

def absName : kernel.name.Name → ConLeche.Name
  | .mk nd => absNameNode nd

def absNameNode : kernel.name.NameNode → ConLeche.Name
  | .mk _hash k => absNameKind k

def absNameKind : kernel.name.NameKind → ConLeche.Name
  | .Anonymous => .anonymous
  | .Str pre s => .str (absName pre) (absString s)
  | .Num pre n => .num (absName pre) n.val

end

/- `ConLeche/Kernel/Expr.lean:40` -- the Rust `Level` tree as a
`ConLeche.Level`. -/
mutual

def absLevel : kernel.level.Level → ConLeche.Level
  | .mk nd => absLevelNode nd

def absLevelNode : kernel.level.LevelNode → ConLeche.Level
  | .mk _hash k => absLevelKind k

def absLevelKind : kernel.level.LevelKind → ConLeche.Level
  | .Zero => .zero
  | .Succ u => .succ (absLevel u)
  | .Max u v => .max (absLevel u) (absLevel v)
  | .Imax u v => .imax (absLevel u) (absLevel v)
  | .Param n => .param (absName n)

end

/-! ## Two refinement lemmas, in the task-#5 shape

Exact result on success: the Rust function returns `ok u`, and `abs u` is
exactly what con-leche's constructor builds on the abstracted arguments.
Nothing is claimed when the Rust side fails. -/

/-- `ConLeche/Kernel/Expr.lean` -- `level::zero` refines `Level.zero`. -/
theorem level_zero_refines {u : kernel.level.Level} (h : kernel.level.zero = ok u) :
    absLevel u = ConLeche.Level.zero := by
  simp [kernel.level.zero] at h
  subst h
  rw [absLevel, absLevelNode, absLevelKind]

/-- `ConLeche/Kernel/Expr.lean` -- `level::succ` refines `Level.succ`.  This is
the one that goes through the hash plumbing (`level.hash_data`, `mix_hash`)
and the `Rc` model, so it exercises the whole generated pipeline. -/
theorem level_succ_refines {a u : kernel.level.Level} (h : kernel.level.succ a = ok u) :
    absLevel u = ConLeche.Level.succ (absLevel a) := by
  simp [kernel.level.succ, kernel.level.hash_data] at h
  obtain ⟨_, _, rfl⟩ := h
  rw [absLevel, absLevelNode, absLevelKind]

end ConRon.Refine
