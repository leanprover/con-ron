/-
The abstraction tier of the refinement proof (DESIGN.md §1, §3.2, §3.5;
P3.1 of §5): the functions that map the Aeneas model of `crates/con-ron-core`
onto con-leche's own `ConLeche.Name`, `ConLeche.Level` and
`ConLeche.PropWhen`, the well-formedness predicates that pin the stored
derived data, and the monadic plumbing every `ConRon/Refine/*.lean` file
shares.

Ported at task #17 from `ConRon/Spike/LevelName/{Abs,Refine}.lean` (tasks #3
and #5), which stays where it is as recorded evidence; the only change to the
`Name`/`Level` halves is the namespace (`level_name.` → `ConRon.Generated.`,
i.e. nothing, since this file `open`s `ConRon.Generated`).  `absPropWhen` and
`PropWhenWF` are new.

What the abstractions forget, in the order DESIGN.md §3.3 lists it:
* the `Arc` indirection -- `alloc.sync.Arc T` *is* `T` in the model
  (`ConRon/Generated/TypesExternal.lean`), so there is nothing to peel;
* the cached hash word (`NameNode.hash`, `LevelNode.hash`): con-leche keeps it
  in a `@[computed_field]`, which is a function of the value and invisible to
  every statement, so `abs` simply drops it;
* the machine-word representations: a string is a `Vec<u32>` of code points in
  the port and a `String` in con-leche; `Name.num`'s index is a `u64` there and
  a `Nat` here.
-/
import ConRon.Generated
import ConRon.Refine.Nat
import ConRon.Refine.SimpSets
import ConLeche.Kernel.Level
import ConLeche.Kernel.Env
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-! ## Monadic plumbing

The local `simp` set of task #5, verbatim.  With it, `rw [f.eq_def] at h;
simp at h` turns an entire Rust function body into a nest of existentials and
disjunctions in one step, `if`/`match` splits included.  The four `Arc` lemmas
are `rfl` because `ConRon/Generated/FunsExternal.lean` models
`Arc::new`/`deref`/`clone` as the identity and `Arc::ptr_eq` as `false`
(DESIGN.md §3.2). -/

@[simp] theorem bind_eq_ok_iff {α β : Type} {e : Result α} {f : α → Result β} {v : β} :
    ((do let x ← e; f x) = ok v) ↔ ∃ y, e = ok y ∧ f y = ok v := by
  constructor
  · cases e with
    | ret r => intro h; exact ⟨r, rfl, by simpa using h⟩
    | vis i k => intro h; simp at h
    | div => intro h; simp at h
  · rintro ⟨y, rfl, h⟩; simpa using h

@[simp] theorem lift_eq {α : Type} (x : α) : Aeneas.Std.lift x = ok x := rfl

@[simp] theorem arc_new_eq {T : Type} (x : T) : alloc.sync.Arc.new x = ok x := rfl
@[simp] theorem arc_deref_eq {T : Type} (A : Type) (x : T) :
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x = ok x := rfl
@[simp] theorem arc_clone_eq {T A : Type} (i : core.alloc.AllocatorClone A) (x : T) :
    alloc.sync.Arc.Insts.CoreCloneClone.clone i x = ok x := rfl
@[simp] theorem arc_ptr_eq_eq {T : Type} (A : Type) (x y : T) :
    alloc.sync.Arc.ptr_eq (T := T) A x y = ok false := rfl

/- The crate names its shared pointer once, as `ron::ptr::P` (task #44), so
that the concrete counted pointer behind it is a one-line choice.  The three
wrappers Charon sees are each one call to the external above, hence each is
the same identity (`ptr_eq`: the same `false`); the generated code calls
*these*, and these three `simp` lemmas are what make the handle invisible to
the proofs exactly as before the alias existed (`deref` is not wrapped, so
`arc_deref_eq` above is still the one doing the work). -/
@[simp] theorem ptr_new_eq {T : Type} (x : T) : ron.ptr.new x = ok x := rfl
@[simp] theorem ptr_clone_eq {T : Type} (x : T) : ron.ptr.clone x = ok x := rfl
@[simp] theorem ptr_ptr_eq_eq {T : Type} (x y : T) :
    ron.ptr.ptr_eq (T := T) x y = ok false := rfl

@[simp] theorem level_dup_eq (u : level.Level) : level.dup u = ok u := by
  cases u; simp [level.dup]

@[simp] theorem name_dup_eq (n : name.Name) : name.dup n = ok n := by
  cases n; simp [name.dup]

/-! ## The Rust-side normaliser (task #70's tuned idiom, landed at task #71)

`rust_norm h` peels a Rust success hypothesis `h : f args = ok v`
deterministically — head reduction, then one `∃`/`∧` layer, `match`/`if`
split, bind inversion, pair destructuring, until nothing changes — leaving one
goal per reachable success path with plain equations in context; `rust_grind`
closes each with `grind` at the one budget task #70 fixed for every lemma.
Together with the attribute-registered lemma sets they are the whole idiom:

```lean
⟨shape step⟩ ; rust_norm h ; all_goals rust_grind
```

`Refine/README.md` §"Writing a new refinement lemma" is the recipe and says
what a `use` lemma must look like; `Refine/AUTOMATION.md` is the study that
measured all of it (tasks #69/#70) and `Refine/Automation/Study.lean` the six
worked examples.  **The idiom is for new leaf, memo-walk and knot-arm
refinement lemmas only** (DESIGN.md §3's ruling of 2026-09-13): the existing
hand proofs are not rewritten, and `HashMap`/`Nat`, `Pins*` and `Ind*` are out
of its scope.

The two sets `Refine/SimpSets.lean` registers are populated here with the
plumbing above; later files add their own (`ExprOps.binder_meta_eq`,
`BasisTables`'s `expr_dup_eq`). -/

attribute [rust_reduce, rust_invert] arc_deref_eq bind_tc_ok lift_eq ptr_new_eq ptr_clone_eq
  arc_new_eq arc_clone_eq name_dup_eq level_dup_eq
  name.NameNode.hash._simpLemma_ name.NameNode.kind._simpLemma_ name.Name._0._simpLemma_
  level.LevelNode.hash._simpLemma_ level.LevelNode.kind._simpLemma_ level.Level._0._simpLemma_
  expr.ExprNode.data._simpLemma_ expr.ExprNode.kind._simpLemma_ expr.Expr._0._simpLemma_

attribute [rust_invert] bind_eq_ok_iff Result.ok.injEq Prod.mk.injEq Prod.exists
  uncurry_apply_pair core.result.Result.Ok.injEq false_and and_false exists_false true_and
  and_true exists_eq_left exists_eq_right Option.some.injEq

/-- The head of every generated body, reduced in one pre-order step: `let en ←
Arc::deref e._0; …` is `… e._0 …`.  (`arc_deref_eq` alone is a post-order
rewrite, so `simp` would visit all the dead arms of the `match` first — task
#70 measured that as the single largest cost of the untuned normaliser.) -/
theorem bind_arc_deref {T β : Type} (A : Type) (x : T) (f : T → Result β) :
    (do let y ← alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x; f y) = f x := by
  rw [arc_deref_eq, bind_tc_ok]

open Lean Elab Tactic Meta in
/-- Destructure every local hypothesis whose type is syntactically a pair: the
`let (n, n1) := val` a Rust `Some((n, n1))` pattern produces is a
one-alternative `match` that neither `split` nor `simp` opens while `val` is a
variable.  Fails when there is nothing to do, so that it can sit last in a
`first`.  (Not `obtain ⟨_, _⟩ := ‹_ × _›`: elaborating that unifies every
hypothesis type with `?a × ?b` and unfolds the `Wrappers`/`Spec` predicates on
the way — a `whnf` timeout.) -/
elab "rust_pairs" : tactic => do
  let g ← getMainGoal
  let mut fvs : Array FVarId := #[]
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Prod 2 then fvs := fvs.push d.fvarId
  if fvs.isEmpty then throwError "rust_pairs: no pair in the context"
  let mut g := g
  for fv in fvs do
    let subgoals ← g.cases fv
    match subgoals with
    | #[sg] => g := sg.mvarId
    | _ => throwError "rust_pairs: unexpected number of goals"
  replaceMainGoal [g]

/-- The normaliser: the head reduced in **pre-order** (`↓`), then the cheap
peel first and `simp` only on a hypothesis that changed shape. -/
syntax "rust_norm " ident : tactic
macro_rules
  | `(tactic| rust_norm $h) => `(tactic| (
      try simp only [↓bind_arc_deref, ↓expr.Expr._0._simpLemma_, ↓expr.ExprNode.kind._simpLemma_,
        ↓level.Level._0._simpLemma_, ↓level.LevelNode.kind._simpLemma_,
        ↓name.Name._0._simpLemma_, ↓name.NameNode.kind._simpLemma_, rust_reduce] at $h:ident
      repeat' (first
        | (obtain ⟨_, $h⟩ := $h)
        | (split at $h:ident)
        | (simp only [rust_invert, reduceCtorEq, ↓existsAndEq] at $h:ident)
        | rust_pairs)))

/-- The closing call, one fixed configuration for every lemma: `ematch := 12`
because the Option-monad plumbing of a leaf needs more than the default five
rounds once the splits are done outside, `gen := 24` because a two-wrapper arm
needs one more term generation than the default eight.  A lemma that needs
more says so with the `[limit]` line in its `grind` diagnostics, and raising
this default is the answer — not a per-lemma override. -/
macro "rust_grind" : tactic => `(tactic| grind (ematch := 12) (gen := 24))

/-- `i + 1` on a `usize` index, in the forward `= ok` form the refinement
proofs use. -/
theorem usize_add_ok {i : Std.Usize} (h : i.val + 1 ≤ Std.Usize.max) :
    ∃ w : Std.Usize, i + 1#usize = ok w ∧ w.val = i.val + 1 := by
  obtain ⟨w, h1, h2⟩ :=
    WP.spec_imp_exists (Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
  exact ⟨w, h1, by scalar_tac⟩

/-- `i - 1` on a `usize` index, in the forward `= ok` form the refinement
proofs use.  The companion of `usize_add_ok` for the *downward* index
recursions — the ones that read a `Vec` from the back (`env::find_from` and
`env::env_of_from` since task #50, `core_k::str_lit_cons_from`). -/
theorem usize_sub_ok {i : Std.Usize} (h : 1 ≤ i.val) :
    ∃ w : Std.Usize, i - 1#usize = ok w ∧ w.val = i.val - 1 := by
  obtain ⟨w, h1, h2⟩ :=
    WP.spec_imp_exists (Std.Usize.sub_spec (x := i) (y := 1#usize) (by scalar_tac))
  exact ⟨w, h1, by scalar_tac⟩

/-- The list a downward index recursion peels: `l.take (i+1)` read back to
front is `l[i]` followed by `l.take i` read back to front.  This is the shape
every lemma about `Env.consts` needs, because the port stores that list
reversed (`absEnv`) and scans it from the back. -/
theorem list_take_reverse_cons {α : Type} {l : List α} {i : Nat}
    (h : i < l.length) :
    (l.take (i + 1)).reverse = l[i] :: (l.take i).reverse := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  simp

/-- Pushing onto the empty vector — the port's spelling of a one-element list
(`name::singleton`, `level::singleton`, `prop_when::to_list`'s `Two` arm). -/
theorem vec_singleton {α : Type} (x : α) :
    ∃ w : alloc.vec.Vec α, alloc.vec.Vec.push (alloc.vec.Vec.new α) x = ok w ∧ w.val = [x] := by
  obtain ⟨w, h1, h2⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new α) x (by simp; scalar_tac))
  exact ⟨w, h1, by simpa using h2⟩

/-- `vec_singleton` keyed on the Rust equation, which is the form a `grind`
`use` lemma needs (`Refine/README.md`, the first keying rule). -/
theorem push_new_val {α : Type} {x : α} {w : alloc.vec.Vec α}
    (h : alloc.vec.Vec.push (alloc.vec.Vec.new α) x = ok w) : w.val = [x] := by
  obtain ⟨w', h', hv⟩ := vec_singleton x
  cases Result.ok_injective (h.symm.trans h'); exact hv

/-- `Vec::push` when it succeeds: the model's vector really is the list with
the element appended. -/
theorem vec_push_val {α : Type} {v w : alloc.vec.Vec α} {x : α}
    (h : alloc.vec.Vec.push v x = ok w) : w.val = v.val ++ [x] := by
  rw [alloc.vec.Vec.push.eq_def] at h
  simp only [] at h
  split at h
  · simp only [Result.ok.injEq] at h
    subst h; simp
  · simp at h

/-! ## Decidable equality of the generated key types

`ron::HashMap`'s abstract map (`ConRon/Refine/HashMap.lean`) is a partial
*function* `toFun : HashMap K V → K → Option V`, and its definition — like
`Inv` and `Eq2Fwd` — needs `DecidableEq K`.  For the memo tables' concrete key
types the instance has to be supplied, and `deriving instance DecidableEq`
cannot: `name.Name`/`level.Level`/`expr.Expr` are three-type mutual inductives
whose recursive occurrences sit behind the `@[reducible] def alloc.sync.Arc`
of DESIGN.md §3.2, and the deriving handler does not look through it
("failed to synthesize `Decidable (a = b)`").

They are therefore the classical instances.  **Nothing is lost and nothing is
executed**: every occurrence is inside a `Prop` (`decide (a = b)` in `Eq2Fwd`,
the `if k' = k` of `lookupK`), the port's *own* decision procedure is
`name::beq`/`expr::beq` and is what the refinement lemmas are about, and
`Classical.choice` is already one of the three axioms the tier's census
allows. -/

noncomputable instance : DecidableEq name.Name := Classical.decEq _
noncomputable instance : DecidableEq level.Level := Classical.decEq _
noncomputable instance : DecidableEq expr.Expr := Classical.decEq _
noncomputable instance : DecidableEq prop_when.PropWhen := Classical.decEq _

/-! ## The abstraction functions -/

/-- A port-side string (`Vec<u32>` of code points, DESIGN.md §3.3) as a Lean
`String`.  `Char.ofNat` sends a value that is not a valid code point to
`'\0'`; the port only ever stores code points that came from a `String`, so on
the image of the parser this is a bijection (`StrWF` below is that side
condition, `absString_inj` in `ConRon/Refine/Name.lean` the bijection). -/
def absString (s : alloc.vec.Vec Std.U32) : String :=
  String.ofList (s.val.map fun c => Char.ofNat c.val)

/- `ConLeche/Kernel/Name.lean:34` -- the Rust `Name` tree as a `ConLeche.Name`. -/
mutual

def absName : name.Name → ConLeche.Name
  | .mk nd => absNameNode nd

def absNameNode : name.NameNode → ConLeche.Name
  | .mk _hash k => absNameKind k

def absNameKind : name.NameKind → ConLeche.Name
  | .Anonymous => .anonymous
  | .Str pre s => .str (absName pre) (absString s)
  | .Num pre n => .num (absName pre) n.val

end

/- `ConLeche/Kernel/Expr.lean:40` -- the Rust `Level` tree as a
`ConLeche.Level`. -/
mutual

def absLevel : level.Level → ConLeche.Level
  | .mk nd => absLevelNode nd

def absLevelNode : level.LevelNode → ConLeche.Level
  | .mk _hash k => absLevelKind k

def absLevelKind : level.LevelKind → ConLeche.Level
  | .Zero => .zero
  | .Succ u => .succ (absLevel u)
  | .Max u v => .max (absLevel u) (absLevel v)
  | .Imax u v => .imax (absLevel u) (absLevel v)
  | .Param n => .param (absName n)

end

/-- A `Vec<Level>` (the port's stand-in for a `List Level`, DESIGN.md §3.4) as
a `List ConLeche.Level`. -/
def absLevels (us : alloc.vec.Vec level.Level) : List ConLeche.Level :=
  us.val.map absLevel

/-- `Expr.const`'s level list, in the canonical three-constructor shape
`crates/con-ron-core/src/kernel/levels.rs` gives it (task #93), as a
`List ConLeche.Level`.

The port's `Levels` is a *representation* of the `List Level` con-leche's
`Expr.const` carries, chosen so that the empty and singleton lists — which
the task-#93 census says almost every constant reference carries — need no
heap block: `Zero` is the empty list, `One u` the singleton, and `Many`
holds two or more behind a `P` handle, which §3.2's model erases (so
`Many`'s argument *is* the `Vec<Level>` and this arm is `absLevels`).

The name is `absConstLevels` and not `absLevels` because `absLevels` is the
`Vec<Level>` abstraction above, which the port still uses wherever a level
list is *not* a constant's: `IndSpec`'s `Nested`, a `ProjTable`'s `guards`,
`IndAbs`'s `sortss`, and every `Vec<Level>` parameter of the kernel walks. -/
def absConstLevels : levels.Levels → List ConLeche.Level
  | .Zero => []
  | .One u => [absLevel u]
  | .Many us => absLevels us

/-- A `Vec<Name>` as a `List ConLeche.Name`. -/
def absNames (ns : alloc.vec.Vec name.Name) : List ConLeche.Name :=
  ns.val.map absName

/-- `prop_when::Ordering` is the port's own three-value enum (task #9, item 9);
Lean's is core's `Ordering`. -/
def absOrdering : prop_when.Ordering → Ordering
  | .Lt => .lt
  | .Eq => .eq
  | .Gt => .gt

/-- `ConLeche/Kernel/PropWhen.lean:386-415` -- the Rust `PropWhen` as a
`ConLeche.PropWhen`, at the level of the representation.

con-leche's datum is *sealed*: `PropWhenRepr` is a `private inductive`, and
`PropWhen` is a one-field structure whose constructor *and* field are
`private`, so nothing outside `PropWhen.lean` can build or match one.  The
abstraction therefore goes through the public smart constructors `never` and
`ifAllZero` — which is enough, because those two name every value of the type
(`casesZ`, `PropWhen.lean:645-661`).  **No `import all` is needed** (the
documented escape con-leche's own proofs use): the five Rust constructors map
onto the two Lean producers — `Never` onto `never`, `Always` onto
`ifAllZero []`, `One`/`Two`/`Many` onto `ifAllZero` of their parameter list.
`ifAllZero` normalizes, so this is well defined for *any* Rust datum, well
formed or not; `PropWhenWF` is what makes it *injective*.

Since task #90 `Two`'s and `Many`'s payloads sit behind a `P` handle, which
DESIGN.md §3.2's model erases: `Two`'s argument *is* the pair `Name × Name`
and `Many`'s *is* the `Vec<Name>`, so the two arms read them directly. -/
def absPropWhenRepr : prop_when.PropWhenRepr → ConLeche.PropWhen
  | .Never => .never
  | .Always => .ifAllZero []
  | .One p => .ifAllZero [absName p]
  | .Two pq => .ifAllZero [absName pq.1, absName pq.2]
  | .Many ps => .ifAllZero (absNames ps)

/-- The datum, through its (Rust-private, Lean-private) representation. -/
def absPropWhen (pw : prop_when.PropWhen) : ConLeche.PropWhen :=
  absPropWhenRepr pw.repr

/-- `ConLeche/Kernel/Expr.lean:108-112` -- the two literals.  `natVal`'s `Nat`
is the crate's own bignum (`ConRon/Refine/Nat.lean`'s `toNat`) and `strVal`'s
`String` a `Vec<u32>` of code points (DESIGN.md §3.3). -/
def absLiteral : expr.Literal → ConLeche.Literal
  | .NatVal n => .natVal (Nat.toNat n)
  | .StrVal s => .strVal (absString s)

/-- `ConLeche/Kernel/Expr.lean:93-104` -- the one datum a binder carries. -/
def absBinderMeta (m : expr.BinderMeta) : ConLeche.BinderMeta :=
  { pw := absPropWhen m.pw }

/- `ConLeche/Kernel/Expr.lean:285-403` -- the Rust `Expr` tree as a
`ConLeche.Expr`.  The `@[computed_field] data` word is *dropped*: it is a
function of the value on the con-leche side, and `ExprWF` below is what pins
the port's stored word to it (`ConRon/Refine/Expr.lean`'s `wf_data`). -/
mutual

def absExpr : expr.Expr → ConLeche.Expr
  | .mk nd => absExprNode nd

def absExprNode : expr.ExprNode → ConLeche.Expr
  | .mk _data k => absExprKind k

def absExprKind : expr.ExprKind → ConLeche.Expr
  | .Bvar i => .bvar i.val
  | .Fvar idx ty => .fvar idx.val (absExpr ty)
  | .«Sort» u => .sort (absLevel u)
  | .Const n us => .const (absName n) (absConstLevels us)
  | .App f a => .app (absExpr f) (absExpr a)
  | .Lam ty b m => .lam (absExpr ty) (absExpr b) (absBinderMeta m)
  | .ForallE ty b m => .forallE (absExpr ty) (absExpr b) (absBinderMeta m)
  | .LetE ty v b => .letE (absExpr ty) (absExpr v) (absExpr b)
  | .Lit l => .lit (absLiteral l)
  | .Proj s i e => .proj (absName s) i.val (absExpr e)

end

/-- A `Vec<Expr>` as a `List ConLeche.Expr`. -/
def absExprs (es : alloc.vec.Vec expr.Expr) : List ConLeche.Expr :=
  es.val.map absExpr

@[simp] theorem absName_mk (h : Std.U64) (k : name.NameKind) :
    absName (.mk (.mk h k)) = absNameKind k := by rw [absName, absNameNode]

@[simp] theorem absLevel_mk (h : Std.U64) (k : level.LevelKind) :
    absLevel (.mk (.mk h k)) = absLevelKind k := by rw [absLevel, absLevelNode]

@[simp] theorem absPropWhen_mk (r : prop_when.PropWhenRepr) :
    absPropWhen (.mk r) = absPropWhenRepr r := rfl

@[simp] theorem absExpr_mk (d : Std.U64) (k : expr.ExprKind) :
    absExpr (.mk (.mk d k)) = absExprKind k := by rw [absExpr, absExprNode]

attribute [simp] absNameKind absLevelKind absPropWhenRepr absExprKind absLiteral
attribute [simp] absBinderMeta

/-! ## Smart-constructor shapes

Every `*_inv` lemma says what node the port's smart constructor built; they
are what `NameWF`/`LevelWF` derivations are inverted with. -/

theorem name_anonymous_inv {n} (h : name.anonymous = ok n) :
    n = .mk (.mk 1723#u64 .Anonymous) := by
  simp [name.anonymous] at h; exact h.symm

theorem mk_str_inv {pre s n} (h : name.mk_str pre s = ok n) :
    ∃ hh, n = .mk (.mk hh (.Str pre s)) := by
  simp [name.mk_str, name.hash_data] at h
  obtain ⟨y1, h1, y2, h2, y3, h3, rfl⟩ := h
  exact ⟨y3, rfl⟩

theorem mk_num_inv {pre m n} (h : name.mk_num pre m = ok n) :
    ∃ hh, n = .mk (.mk hh (.Num pre m)) := by
  simp [name.mk_num, name.hash_data, name.nat_hash] at h
  obtain ⟨y1, h1, y3, h3, rfl⟩ := h
  exact ⟨y3, rfl⟩

theorem level_zero_inv {u} (h : level.zero = ok u) : u = .mk (.mk 1#u64 .Zero) := by
  simp [level.zero] at h; exact h.symm

theorem level_succ_inv {a u} (h : level.succ a = ok u) :
    ∃ hh, u = .mk (.mk hh (.Succ a)) := by
  simp [level.succ, level.hash_data] at h
  obtain ⟨y, hy, rfl⟩ := h; exact ⟨y, rfl⟩

theorem level_max_inv {a b u} (h : level.max a b = ok u) :
    ∃ hh, u = .mk (.mk hh (.Max a b)) := by
  simp [level.max, level.hash_data] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := h; exact ⟨z, rfl⟩

theorem level_imax_inv {a b u} (h : level.imax a b = ok u) :
    ∃ hh, u = .mk (.mk hh (.Imax a b)) := by
  simp [level.imax, level.hash_data] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := h; exact ⟨z, rfl⟩

theorem level_param_inv {n u} (h : level.param n = ok u) :
    ∃ hh, u = .mk (.mk hh (.Param n)) := by
  simp [level.param, name.hash_data] at h
  obtain ⟨y, hy, rfl⟩ := h; exact ⟨y, rfl⟩

/-! ## The well-formedness predicates

DESIGN.md §3.5, as amended at task #5: a `*WF` predicate is an **inductive**
one whose constructors are the port's own smart constructors.  It says "this
node is what the smart constructor built", which pins the stored hash word to
the children without any proof ever naming a hash formula, makes the
constructor-preservation lemmas *literally the constructors*, and gives
injectivity of `abs` from the fact that a smart constructor is a function.

`StrWF` is the one clause no equation supplies: every code point stored in a
`Str` node is a valid `Char`, without which `absString` is not injective. -/

def StrWF (s : alloc.vec.Vec Std.U32) : Prop := ∀ c ∈ s.val, Nat.isValidChar c.val

inductive NameWF : name.Name → Prop where
  | anonymous {n} : name.anonymous = ok n → NameWF n
  | str {pre s n} : NameWF pre → StrWF s → name.mk_str pre s = ok n → NameWF n
  | num {pre m n} : NameWF pre → name.mk_num pre m = ok n → NameWF n

inductive LevelWF : level.Level → Prop where
  | zero {u} : level.zero = ok u → LevelWF u
  | succ {a u} : LevelWF a → level.succ a = ok u → LevelWF u
  | max {a b u} : LevelWF a → LevelWF b → level.max a b = ok u → LevelWF u
  | imax {a b u} : LevelWF a → LevelWF b → level.imax a b = ok u → LevelWF u
  | param {n u} : NameWF n → level.param n = ok u → LevelWF u

/-- A `Vec<Name>` all of whose entries are well formed. -/
def NamesWF (ns : alloc.vec.Vec name.Name) : Prop := ∀ n ∈ ns.val, NameWF n

/-- `ConLeche/Kernel/PropWhen.lean:360-384` -- the canonical-form invariant of
the sealed datum, in the same shape as `NameWF`/`LevelWF`.

con-leche's `PropWhenRepr` carries it as proof *fields* (`two p q` needs
`p < q`, `many ps` needs `PropWhen.Sorted ps ∧ 2 < ps.length`), which Charon
erases (task #9, item 3); here they come back as the four smart constructors
that are the port's only way in — `prop_when::never`, `prop_when::if_all_zero`,
`prop_when::inter` and `prop_when::bind_z` (the module's whole set of public
producers; `of_sorted`/`two_prime` are Rust-private).  Canonical sortedness by
the port's own `prop_when::name_cmp` is therefore not *stated* but *derived*:
`ConRon/Refine/PropWhen.lean`'s `wf_shape` turns a `PropWhenWF` derivation
into the invariant `WFShape` — well-formed names, a strictly ascending
abstracted parameter list, and a `Many` that really holds more than two
names — and that is what makes `to_list` and `beq` exact.

The `bind_z` constructor quantifies over the dictionary type `F`: the port's
stand-in for `bindZ`'s function argument (task #9, pattern 1). -/
inductive PropWhenWF : prop_when.PropWhen → Prop where
  | never {pw} : prop_when.never = ok pw → PropWhenWF pw
  | if_all_zero {ps pw} : NamesWF ps → prop_when.if_all_zero ps = ok pw → PropWhenWF pw
  | inter {a b pw} : PropWhenWF a → PropWhenWF b → prop_when.inter a b = ok pw → PropWhenWF pw
  | bind_z {F : Type} {inst : prop_when.NameToPw F} {f : F} {pw c} :
      (∀ n, NameWF n → ∀ r, inst.apply f n = ok r → PropWhenWF r) →
      PropWhenWF pw → prop_when.bind_z inst f pw = ok c → PropWhenWF c

/-- A `Vec<Level>` all of whose entries are well formed. -/
def LevelsWF (us : alloc.vec.Vec level.Level) : Prop := ∀ u ∈ us.val, LevelWF u

/-- A `Levels` (task #93) that is well formed: its levels are, **and it is in
the canonical form `levels::of_vec` builds** — `Many` never holds a list
shorter than two, so the constructor is a function of the length.

That second clause is what the port's own code depends on and what this
predicate exists to carry: `levels::len` reads the length off the
constructor, and `expr::const_levels_beq`, `state_c::is_equiv_list_c_m` and
`levels::head_d` all answer on a constructor mismatch without looking
inside.  Without it `Many ⟨[u]⟩` and `One u` would abstract to the same list
and compare unequal, and `absConstLevels` would not be injective.  It is the
same shape of obligation `PropWhenWF` carries for `prop_when`'s sealed
five-constructor representation (task #90). -/
def ConstLevelsWF : levels.Levels → Prop
  | .Zero => True
  | .One u => LevelWF u
  | .Many us => LevelsWF us ∧ 2 ≤ us.val.length

/-- A binder datum is well formed when its `PropWhen` is. -/
def BinderMetaWF (m : expr.BinderMeta) : Prop := PropWhenWF m.pw

/-- A literal is well formed when its payload is: the bignum normalised
(`ron::nat`'s invariant), the string a sequence of valid code points. -/
def LiteralWF : expr.Literal → Prop
  | .NatVal n => Nat.NatWF n
  | .StrVal s => StrWF s

/-- `ConLeche/Kernel/Expr.lean:285-403` -- the hereditary invariant of the
packed `data` word, in the task-#5 shape: an **inductive** predicate whose
constructors are the port's own smart constructors, one per `Expr`
constructor (`mk_const` is spelled with the prefix because `const` is a Rust
keyword; `mk_bvar` is `bvar`, its pool not being ported -- task #11).  It says
"this node is what the smart constructor built", which pins the stored word to
the children without any proof naming a hash formula; `ConRon/Refine/Expr.lean`
turns it into the *statement* the readers need (`wf_data`: the observed bits of
the port's word are con-leche's `bvarBRaw`/`fvarBRaw`/`hasLP`) and into
injectivity of `absExpr`, which is what makes `beq` exact. -/
inductive ExprWF : expr.Expr → Prop where
  | bvar {i e} : expr.bvar i = ok e → ExprWF e
  | fvar {idx ty e} : ExprWF ty → expr.fvar idx ty = ok e → ExprWF e
  | sort {u e} : LevelWF u → expr.sort u = ok e → ExprWF e
  | mk_const {n us e} : NameWF n → LevelsWF us → expr.mk_const n us = ok e → ExprWF e
  | app {f a e} : ExprWF f → ExprWF a → expr.app f a = ok e → ExprWF e
  | lam {ty b m e} : ExprWF ty → ExprWF b → BinderMetaWF m →
      expr.lam ty b m = ok e → ExprWF e
  | forall_e {ty b m e} : ExprWF ty → ExprWF b → BinderMetaWF m →
      expr.forall_e ty b m = ok e → ExprWF e
  | let_e {ty v b e} : ExprWF ty → ExprWF v → ExprWF b →
      expr.let_e ty v b = ok e → ExprWF e
  | lit {l e} : LiteralWF l → expr.lit l = ok e → ExprWF e
  | proj {s i x e} : NameWF s → ExprWF x → expr.proj s i x = ok e → ExprWF e

/-- A `Vec<Expr>` all of whose entries are well formed. -/
def ExprsWF (es : alloc.vec.Vec expr.Expr) : Prop := ∀ e ∈ es.val, ExprWF e

/-! ## Structural induction principles

Aeneas's `partial_fixpoint` definitions give no induction principle of their
own, so **every structural refinement is an induction on the argument, not on
the function** — either on one of these two recursors or on the `LevelWF`
derivation when the proof needs the WF hypotheses in step.  They skip the `Arc`
and the node layer of the port's three-type mutual inductive. -/

/-- Structural induction on the port's `Level` tree. -/
@[elab_as_elim] theorem Level.ind' {motive : level.Level → Prop}
    (zero : ∀ h, motive (.mk (.mk h .Zero)))
    (succ : ∀ h u, motive u → motive (.mk (.mk h (.Succ u))))
    (max : ∀ h u v, motive u → motive v → motive (.mk (.mk h (.Max u v))))
    (imax : ∀ h u v, motive u → motive v → motive (.mk (.mk h (.Imax u v))))
    (param : ∀ h n, motive (.mk (.mk h (.Param n)))) :
    ∀ u, motive u :=
  fun u => level.Level.rec
    (motive_1 := fun k => ∀ h, motive (.mk (.mk h k)))
    (motive_2 := fun nd => motive (.mk nd))
    (motive_3 := motive)
    zero (fun a ha h => succ h a ha) (fun a b ha hb h => max h a b ha hb)
    (fun a b ha hb h => imax h a b ha hb) (fun n h => param h n)
    (fun h _k hk => hk h) (fun _ hnd => hnd) u

/-- Structural induction on the port's `Name` tree. -/
@[elab_as_elim] theorem Name.ind' {motive : name.Name → Prop}
    (anonymous : ∀ h, motive (.mk (.mk h .Anonymous)))
    (str : ∀ h pre s, motive pre → motive (.mk (.mk h (.Str pre s))))
    (num : ∀ h pre m, motive pre → motive (.mk (.mk h (.Num pre m)))) :
    ∀ n, motive n :=
  fun n => name.Name.rec
    (motive_1 := fun k => ∀ h, motive (.mk (.mk h k)))
    (motive_2 := fun nd => motive (.mk nd))
    (motive_3 := motive)
    anonymous (fun p s hp h => str h p s hp) (fun p m hp h => num h p m hp)
    (fun h _k hk => hk h) (fun _ hnd => hnd) n

/-! ## The environment records (task #46)

`kernel::env`'s seven stored-constant records, its two little enums and the
environment itself.  These came here from `ConRon/Refine/BasisTables.lean`'s
temporary `T22` namespace (task #22 wrote them there because `Abs.lean` had
nothing above `Expr` yet, and said so in a note); the `T22` namespace is gone
and this is the one copy.

None of them carries derived data, so none needs a smart constructor: a
record's abstraction is its fields' abstractions, and its well-formedness
(below) is its fields' well-formedness.  The one asymmetry `abs` has to see is
`ProjTable`: con-leche's `bodies` is an `Array Expr` while its `guards` is a
`List Level`, and the port has a `Vec` for both (task #10, surprise 8).  The
`P` around a stored `ConstantInfo` (task #34's sharing) is invisible:
`alloc.sync.Arc T` *is* `T` in the model, so `absConstantInfos` reads
`Vec (P ConstantInfo)` exactly as it reads `Vec ConstantInfo`. -/

/-- `ConLeche/Kernel/Env.lean:197` — `ConstantVal` (the port's `ty` is the
Lean's `type`; `type` is a Rust keyword). -/
def absConstantVal (cv : env.ConstantVal) : ConLeche.ConstantVal :=
  ⟨absName cv.name, absNames cv.level_params, absExpr cv.ty⟩

/-- `ConLeche/Kernel/Env.lean:315` — `ReducibilityHint`. -/
def absHint : env.ReducibilityHint → ConLeche.ReducibilityHint
  | .Opaque => .opaque
  | .Abbrev => .abbrev
  | .Regular h => .regular h.val

/-- `ConLeche/Kernel/Env.lean:243` — `RecRuleFire`. -/
def absFire : env.RecRuleFire → ConLeche.RecRuleFire
  | .Inert => .inert
  | .Plain => .plain
  | .Nested us es => .nested (absLevels us) (absExprs es)

/-- `ConLeche/Kernel/Env.lean:259` — `RecRule`. -/
def absRecRule (r : env.RecRule) : ConLeche.RecRule where
  ctor := absName r.ctor
  nfields := r.nfields.val
  ctorParams := r.ctor_params.val
  fire := absFire r.fire
  rhs := absExpr r.rhs
  k := r.k
  eta := r.eta
  paramsBlind := r.params_blind

/-- A `Vec<RecRule>` as the Lean's `List RecRule` (`recInfo`'s `rules`). -/
def absRecRules (rs : alloc.vec.Vec env.RecRule) : List ConLeche.RecRule :=
  rs.val.map absRecRule

/-- `ConLeche/Kernel/Env.lean:362` — `IndCaps`. -/
def absIndCaps (c : env.IndCaps) : ConLeche.IndCaps where
  eta := c.eta
  etaCtor := absName c.eta_ctor
  etaParams := c.eta_params.val
  etaFields := c.eta_fields.val
  unitlike := c.unitlike
  unitParams := c.unit_params.val
  ruleK := c.rule_k
  sortZ := absPropWhen c.sort_z

/-- `ConLeche/Kernel/Env.lean:411` — `ProjTable`.  The Lean's `bodies` is an
`Array Expr` while its `guards` is a `List Level`; the port has a `Vec` for
both (task #10, surprise 8), so only this abstraction sees the asymmetry. -/
def absProjTable (t : env.ProjTable) : ConLeche.ProjTable where
  structName := absName t.struct_name
  levelParams := absNames t.level_params
  numParams := t.num_params.val
  ctor := absName t.ctor
  numFields := t.num_fields.val
  structSort := absLevel t.struct_sort
  bodies := (absExprs t.bodies).toArray
  guards := absLevels t.guards
  off := t.off.val

/-- `ConLeche/Kernel/Env.lean:447` — `ProjEntry`, the per-field view of a
table (what `env::find_proj` and `fenv::find_proj` return). -/
def absProjEntry (e : env.ProjEntry) : ConLeche.ProjEntry where
  structName := absName e.struct_name
  idx := e.idx.val
  levelParams := absNames e.level_params
  numParams := e.num_params.val
  ctor := absName e.ctor
  numFields := e.num_fields.val
  body := absExpr e.body
  fieldSort := absLevel e.field_sort
  structSort := absLevel e.struct_sort
  off := e.off.val

/-- `ConLeche/Kernel/Env.lean:471` — `ConstantInfo`. -/
def absConstantInfo : env.ConstantInfo → ConLeche.ConstantInfo
  | .AxiomInfo cv => .axiomInfo (absConstantVal cv)
  | .DefnInfo cv v h => .defnInfo (absConstantVal cv) (absExpr v) (absHint h)
  | .ThmInfo cv v => .thmInfo (absConstantVal cv) (absExpr v)
  | .IndInfo cv c => .indInfo (absConstantVal cv) (absIndCaps c)
  | .CtorInfo cv np nf => .ctorInfo (absConstantVal cv) np.val nf.val
  | .RecInfo cv mi rp rs =>
    .recInfo (absConstantVal cv) mi.val rp.val (rs.val.map absRecRule)
  | .ProjInfo t => .projInfo (absProjTable t)

/-- A `Vec<ConstantInfo>` as a `List ConLeche.ConstantInfo`.  Also the reading
of `Env.consts`' `Vec<P<ConstantInfo>>`: `P` is the identity in the model. -/
def absConstantInfos (cs : alloc.vec.Vec env.ConstantInfo) :
    List ConLeche.ConstantInfo :=
  cs.val.map absConstantInfo

/-- `ConLeche/Kernel/Env.lean:627` — `Env`.  A *function*, not a relation:
`Env.consts` is a list on both sides — but the port stores it **reversed**,
oldest first (`env.rs`'s `Env` deviation, task #50: a push at the back is
`Vec::push`, so no function of the port calls `Vec::insert`, whose Aeneas model
is an overwrite).  So the abstraction reverses it back, and every statement
about the environment reads the same as it did when the orders agreed. -/
def absEnv (e : env.Env) : ConLeche.Env := ⟨(absConstantInfos e.consts).reverse⟩

/-- `ConLeche/Kernel/Env.lean:69` — `CheckMode`. -/
def absMode : env.CheckMode → ConLeche.CheckMode
  | .Verified => .verified
  | .Trusted => .trusted

/-- `ConLeche/Kernel/Env.lean:352` — `BasisKind`. -/
def absBasisKind : env.BasisKind → ConLeche.BasisKind
  | .EqK => .eqK
  | .NatK => .natK
  | .PunitK => .punitK
  | .EmptyK => .emptyK
  | .FalseK => .falseK
  | .QuotK => .quotK

/-- `ConLeche/Kernel/Env.lean` — `QuotKind`, which of the quotient package's
constants a `#QUOT` record declares (con-leche task #293). -/
def absQuotKind : env.QuotKind → ConLeche.QuotKind
  | .Type => .type
  | .Ctor => .ctor
  | .Lift => .lift
  | .Ind => .ind
  | .Sound => .sound

/-- `ConLeche/Kernel/Env.lean` — `Declaration`, a declaration presented to
the checker.  Since con-leche's task #285 this is the *only* declaration
record: the cached tier's `DeclC` twin is gone on both sides. -/
def absDeclaration : env.Declaration → ConLeche.Declaration
  | .AxiomDecl cv => .axiomDecl (absConstantVal cv)
  | .DefnDecl cv v h => .defnDecl (absConstantVal cv) (absExpr v) (absHint h)
  | .ThmDecl cv v => .thmDecl (absConstantVal cv) (absExpr v)
  | .OpaqueDecl cv v => .opaqueDecl (absConstantVal cv) (absExpr v)
  | .BasisDecl k => .basisDecl (absBasisKind k)
  | .IndDecl block nP => .indDecl (absConstantInfos block) nP.val
  | .QuotDecl k cv => .quotDecl (absQuotKind k) (absConstantVal cv)

/- These are deliberately **not** in the plumbing `simp` set: task #22's
`BasisTables.lean` drives its 192-node `step*` proof with `simp only
[absBasisKind]` and friends at the end, and a global `simp` attribute makes
those calls no-ops ("`simp` made no progress").  Each client unfolds the one it
needs by name. -/

/-! ## Well-formedness of the environment records (task #46)

Hereditary, in the task-#17 style: a record is well formed when its fields
are.  There is no *inductive* predicate to write here — that shape belongs to
types with derived data (`Name`, `Level`, `Expr`, `PropWhen`), whose stored
hash word a smart constructor pins; none of `env`'s records has any, so the
predicate is the conjunction of its fields' and is what makes
`absConstantInfo` injective (`ConRon/Refine/Env.lean`'s
`absConstantInfo_injective`) and hence the `*_beq` family exact.

`ReducibilityHint` and `BasisKind` carry only machine words and need no
clause; `CheckMode` likewise. -/

/-- `ConstantVal`: a well-formed name, level-parameter list and type. -/
def ConstantValWF (cv : env.ConstantVal) : Prop :=
  NameWF cv.name ∧ NamesWF cv.level_params ∧ ExprWF cv.ty

/-- `RecRuleFire`: `.nested`'s stored level and pin lists. -/
def RecRuleFireWF : env.RecRuleFire → Prop
  | .Inert => True
  | .Plain => True
  | .Nested us es => LevelsWF us ∧ ExprsWF es

/-- `RecRule`: the constructor name, the firing mode and the right-hand side
(the five counters and bits are machine words). -/
def RecRuleWF (r : env.RecRule) : Prop :=
  NameWF r.ctor ∧ RecRuleFireWF r.fire ∧ ExprWF r.rhs

/-- A `Vec<RecRule>` all of whose entries are well formed. -/
def RecRulesWF (rs : alloc.vec.Vec env.RecRule) : Prop := ∀ r ∈ rs.val, RecRuleWF r

/-- `IndCaps`: the η constructor's name and the result-sort zero-ness datum. -/
def IndCapsWF (c : env.IndCaps) : Prop :=
  NameWF c.eta_ctor ∧ PropWhenWF c.sort_z

/-- `ProjTable`: every stored name, the structure's sort, the field bodies and
the per-field guard levels. -/
def ProjTableWF (t : env.ProjTable) : Prop :=
  NameWF t.struct_name ∧ NamesWF t.level_params ∧ NameWF t.ctor ∧
  LevelWF t.struct_sort ∧ ExprsWF t.bodies ∧ LevelsWF t.guards

/-- `ProjEntry`: the per-field view's own fields. -/
def ProjEntryWF (e : env.ProjEntry) : Prop :=
  NameWF e.struct_name ∧ NamesWF e.level_params ∧ NameWF e.ctor ∧
  ExprWF e.body ∧ LevelWF e.field_sort ∧ LevelWF e.struct_sort

/-- `ConstantInfo`: the hereditary invariant of a stored constant, one clause
per constructor in the cited field order. -/
def ConstantInfoWF : env.ConstantInfo → Prop
  | .AxiomInfo cv => ConstantValWF cv
  | .DefnInfo cv v _ => ConstantValWF cv ∧ ExprWF v
  | .ThmInfo cv v => ConstantValWF cv ∧ ExprWF v
  | .IndInfo cv c => ConstantValWF cv ∧ IndCapsWF c
  | .CtorInfo cv _ _ => ConstantValWF cv
  | .RecInfo cv _ _ rs => ConstantValWF cv ∧ RecRulesWF rs
  | .ProjInfo t => ProjTableWF t

/-- A `Vec<ConstantInfo>` — or a `Vec<P<ConstantInfo>>`, the same type in the
model — all of whose entries are well formed. -/
def ConstantInfosWF (cs : alloc.vec.Vec env.ConstantInfo) : Prop :=
  ∀ c ∈ cs.val, ConstantInfoWF c

/-- `Env`: every stored constant is well formed.  This is the invariant the
checker's fold maintains (`fenv::push` extends it by one constant) and what
every lookup hands its caller. -/
def EnvWF (e : env.Env) : Prop := ConstantInfosWF e.consts

/-- `Declaration`: the hereditary invariant of a presented declaration. -/
def DeclarationWF : env.Declaration → Prop
  | .AxiomDecl cv => ConstantValWF cv
  | .DefnDecl cv v _ => ConstantValWF cv ∧ ExprWF v
  | .ThmDecl cv v => ConstantValWF cv ∧ ExprWF v
  | .OpaqueDecl cv v => ConstantValWF cv ∧ ExprWF v
  | .BasisDecl _ => True
  | .IndDecl block _ => ConstantInfosWF block
  | .QuotDecl _ cv => ConstantValWF cv

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The file's own theorems are the smart-constructor shapes and the `Arc`/`Vec`
plumbing; nothing here reaches past Lean's own three axioms. -/

/--
info: 'ConRon.Refine.mk_str_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mk_str_inv

/--
info: 'ConRon.Refine.level_param_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms level_param_inv

/--
info: 'ConRon.Refine.vec_push_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms vec_push_val

/-! ## The automation shapes (task #69's `AUTOMATION.md`, adopted by task #67)

`Refine/AUTOMATION.md` measured what it takes to replace a hand proof by

```
⟨one shape line per constructor⟩ ; rust_inv h ; all_goals grind [⟨lemma set⟩]
```

**The idiom itself is not adopted** — the maintainer is diagnosing its ~5×
elaboration cost first (task #70), and task #67's re-proofs stay in the
existing hand style: forward from `= ok`, `bind_eq_ok_iff`, the arms' `Sim`
shapes.  What *is* carried here is the one prerequisite that costs nothing
because it is purely additive: a conclusion about a run stated as a predicate
on the run result rather than an existential, which is what `grind` needs
(it negates `∃ lst', P lst'` into a `∀` whose body never meets what it
derives about `g.run lst`).

`RunOk`/`RunErr` are those predicates.  The tower's `Out`/`ErrSim`/`Sim` keep
their existential statements, so nothing that consumes or proves them changes;
what is new is an *introduction* form (`ErrSim.ofRunErr` here, `Out.ofRun` and
`Sim.ofRun` in `State.lean`/`Core/Arms/Shape.lean`) that leaves a
`RunOk`/`RunErr` goal, for whoever takes task #70's answer up. -/

/-- A successful run, as a predicate on the result: no witness to find. -/
def RunOk {ε β σ : Type} (x : Except ε (β × σ)) (P : β → σ → Prop) : Prop :=
  match x with
  | .ok (v, s) => P v s
  | .error _ => False

@[simp] theorem RunOk_ok {ε β σ : Type} (v : β) (s : σ) (P : β → σ → Prop) :
    RunOk (ε := ε) (.ok (v, s)) P ↔ P v s := Iff.rfl

@[simp] theorem RunOk_error {ε β σ : Type} (e : ε) (P : β → σ → Prop) :
    RunOk (β := β) (σ := σ) (.error e) P ↔ False := Iff.rfl

/-- A thrown run, as a predicate on the error: the failure half's twin of
`RunOk`. -/
def RunErr {ε β : Type} (x : Except ε β) (P : ε → Prop) : Prop :=
  match x with
  | .ok _ => False
  | .error e => P e

@[simp] theorem RunErr_error {ε β : Type} (e : ε) (P : ε → Prop) :
    RunErr (β := β) (.error e) P ↔ P e := Iff.rfl

@[simp] theorem RunErr_ok {ε β : Type} (v : β) (P : ε → Prop) :
    RunErr (ε := ε) (.ok v) P ↔ False := Iff.rfl

/-- The con-leche monad plumbing as **unconditional** equations, which is what
`grind` needs: a conditional rewrite whose right-hand side has variables
outside its pattern (`x.run lst = ok (a, lst') → (x >>= f).run lst = …`) never
fires. -/
theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = Except.error e := rfl

/-! ## Errors: the kind, which is what a refinement lemma compares

DESIGN.md §3's ruling of 2026-09-13 (task #67): every refinement lemma is
stated over the **full outcome** — a Rust `Ok` is con-leche's `ok` at the
abstracted value, a Rust `Err` at one of the three *mirrored* constructors is
con-leche's `error` at the same kind, and a Rust `Err` at the port's own
`Native` (`kernel/core_types.rs`, the note on `CheckError`) claims nothing.

Messages are never compared (§3.1: *"the same error kinds (message strings
need not match — the theorem never reads them)"*), which is what makes this
statable at all: the port carries `Vec<u32>` code points where con-leche
carries a `String`, and the two differ deliberately — `checkDivModPinLoop`'s
accumulated reasons, for one, are not ported (`kernel::checker`'s module note
2).  So the comparison is between *tags*. -/

/-- con-leche's `CheckError` (`ConLeche/Kernel/Core.lean:47-51`) without its
messages: the three kinds a refinement lemma can claim. -/
inductive ErrKind where
  | notImplemented
  | invalid
  | internal
  deriving DecidableEq, Repr

/-- con-leche's error, as its kind. -/
def lErrKind : ConLeche.CheckError → ErrKind
  | .notImplemented _ => .notImplemented
  | .invalid _ => .invalid
  | .internal _ => .internal

/-- **The port's error, as the con-leche kind it stands for.**  The three
mirrored constructors are the cited ones; `Native` is the port's own decline
and abstracts to *nothing*, which is how "claims nothing about this run" is
spelled (`ErrSim` below quantifies over `absErrKind e = some k`). -/
def absErrKind : kernel.core_types.CheckError → Option ErrKind
  | .NotImplemented _ => some .notImplemented
  | .Invalid _ => some .invalid
  | .Internal _ => some .internal
  | .Native _ => none

@[simp] theorem absErrKind_notImplemented (m) :
    absErrKind (.NotImplemented m) = some .notImplemented := rfl
@[simp] theorem absErrKind_invalid (m) : absErrKind (.Invalid m) = some .invalid := rfl
@[simp] theorem absErrKind_internal (m) : absErrKind (.Internal m) = some .internal := rfl
@[simp] theorem absErrKind_native (m) : absErrKind (.Native m) = none := rfl

/-- **What a Rust error claims about con-leche's outcome**: that con-leche
throws too, at the same kind.  A `Native` error claims nothing, because
`absErrKind` sends it to `none` and the hypothesis is then unsatisfiable —
so the two halves of the ruling are one definition, and a lemma about a
`Native` site is discharged by `ErrSim.native` without ever naming the
con-leche side.

It is stated over the *`Except`* the con-leche side ends in, so that the same
notion serves the pure tier (`CheckM β = Except CheckError β`), the cached
tier (`(g : CheckCM β).run lst : Except CheckError (β × CState)`) and
everything in between. -/
def ErrSim {γ : Type} (e : kernel.core_types.CheckError)
    (x : Except ConLeche.CheckError γ) : Prop :=
  ∀ k, absErrKind e = some k → ∃ le, x = .error le ∧ lErrKind le = k

/-- The port's own failure claims nothing. -/
theorem ErrSim.native {γ : Type} {x : Except ConLeche.CheckError γ} (m) :
    ErrSim (.Native m) x := by
  intro k hk; simp at hk

/-- The mirrored case: con-leche throws, at the kind the port's error
abstracts to. -/
theorem ErrSim.mk {γ : Type} {e : kernel.core_types.CheckError}
    {x : Except ConLeche.CheckError γ} {le : ConLeche.CheckError}
    (hx : x = .error le) (hk : absErrKind e = some (lErrKind le)) :
    ErrSim e x := by
  intro k hk'; exact ⟨le, hx, by rw [hk] at hk'; exact Option.some_injective _ hk'⟩

theorem ErrSim.notImplemented {γ : Type} {x : Except ConLeche.CheckError γ} {m s}
    (hx : x = .error (.notImplemented s)) : ErrSim (.NotImplemented m) x :=
  ErrSim.mk hx rfl

theorem ErrSim.invalid {γ : Type} {x : Except ConLeche.CheckError γ} {m s}
    (hx : x = .error (.invalid s)) : ErrSim (.Invalid m) x :=
  ErrSim.mk hx rfl

theorem ErrSim.internal {γ : Type} {x : Except ConLeche.CheckError γ} {m s}
    (hx : x = .error (.internal s)) : ErrSim (.Internal m) x :=
  ErrSim.mk hx rfl

/-- **Error propagation through a bind**, the move every arm makes: a
sub-computation that threw makes the whole throw, on both sides.  This is
what keeps the error half of a full-outcome proof to a line per bind. -/
theorem ErrSim.bind {γ δ : Type} {e : kernel.core_types.CheckError}
    {x : Except ConLeche.CheckError γ} (h : ErrSim e x)
    (f : γ → Except ConLeche.CheckError δ) : ErrSim e (x >>= f) := by
  intro k hk
  obtain ⟨le, hx, hle⟩ := h k hk
  exact ⟨le, by rw [hx]; rfl, hle⟩

/-- The same, for a con-leche action's `run` in the state monad: `x` is the
sub-action's run, `f` what the rest of the `do` block does with its value and
state. -/
theorem ErrSim.bind_run {γ δ σ : Type} {e : kernel.core_types.CheckError}
    {x : Except ConLeche.CheckError (γ × σ)} (h : ErrSim e x)
    (f : γ × σ → Except ConLeche.CheckError δ) : ErrSim e (x >>= f) :=
  h.bind f

/-- A failure the con-leche side has no counterpart for claims nothing.  This
is the form the leaves use: a Rust-only guard inside a *total* con-leche
function (`natOpResult` answers an `Option`, it does not throw) is discharged
by showing the error is `Native`, with no con-leche side named at all. -/
theorem ErrSim.of_none {γ : Type} {e : kernel.core_types.CheckError}
    {x : Except ConLeche.CheckError γ} (h : absErrKind e = none) : ErrSim e x := by
  intro k hk; rw [h] at hk; simp at hk

/-- `ErrSim` in `RunErr` form: the introduction rule a `grind` proof of a
failure half wants, since `ErrSim` itself ends in an existential
(`AUTOMATION.md`). -/
theorem ErrSim.ofRunErr {γ : Type} {e : kernel.core_types.CheckError}
    {x : Except ConLeche.CheckError γ}
    (h : ∀ k, absErrKind e = some k → RunErr x (fun le => lErrKind le = k)) :
    ErrSim e x := by
  intro k hk
  have hx := h k hk
  revert hx
  cases hxx : x with
  | ok v => intro hx; exact hx.elim
  | error le => intro hx; exact ⟨le, rfl, hx⟩

/-- **The full outcome, in the pure tier.**  `CheckM β = Except CheckError β`:
a Rust `Ok` is con-leche's `ok` at the abstracted value, a Rust `Err` is
`ErrSim`.  The cached tier's twin, which also relates the two states, is
`Refine/State.lean`'s `Out`. -/
def OutP {α β : Type} (A : α → β) (WF : α → Prop)
    (o : core.result.Result α kernel.core_types.CheckError)
    (x : Except ConLeche.CheckError β) : Prop :=
  match o with
  | .Ok r => x = .ok (A r) ∧ WF r
  | .Err e => ErrSim e x

theorem OutP.ok {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {x : Except ConLeche.CheckError β} (hx : x = .ok (A r)) (hwf : WF r) :
    OutP A WF (.Ok r) x := ⟨hx, hwf⟩

theorem OutP.err {α β : Type} {A : α → β} {WF : α → Prop}
    {e : kernel.core_types.CheckError} {x : Except ConLeche.CheckError β}
    (h : ErrSim e x) : OutP A WF (.Err e) x := h

/-- **`ErrSim` transported forward**: whatever con-leche throws at `x`, it
throws at `y` too.  This is the wrapper/caller move — a memo wrapper throws
exactly what its body threw, a `do` block throws exactly what its first
failing step threw — where `ErrSim.bind` is the special case in which `y` is
literally `x >>= f`. -/
theorem ErrSim.trans {γ δ : Type} {e : kernel.core_types.CheckError}
    {x : Except ConLeche.CheckError γ} {y : Except ConLeche.CheckError δ}
    (h : ErrSim e x) (hxy : ∀ le, x = .error le → y = .error le) : ErrSim e y := by
  intro k hk
  obtain ⟨le, hx, hk'⟩ := h k hk
  exact ⟨le, hxy le hx, hk'⟩

/-- `ErrSim` transported along an equation on the con-leche side, which is how
a lemma proved against an unfolded body is used against the folded one. -/
theorem ErrSim.of_eq {γ : Type} {e : kernel.core_types.CheckError}
    {x y : Except ConLeche.CheckError γ} (h : ErrSim e x) (hxy : y = x) :
    ErrSim e y := by rw [hxy]; exact h

end ConRon.Refine
