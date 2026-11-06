/-
# `ConRon.Arena.Frontend.Olean.Sparse` — the sparse decoder (task #142)

The twin of `olean/sparse.rs`.  The kid table (`kidTable`), the read-only `Table`
and `lookup` are upstream's own: shapes, field numbers and a generic table.  The memo
and the frontier hold handles, by location.  A read may be handed a frontier
(`Frontier`): values read earlier, which it takes instead of visiting what lies
below them (`frontierExpr`, upstream task #481).
-/
module

public import ConLeche.Frontend.Olean.Sparse
public import ConRon.Arena.Frontend.Olean.Spec

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF kName kLevel kExpr kLevels kidTable Table Table.get lookup)

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:92-98 SM
A sparse decoder's memo: the values read so far, by location, one map per kind. -/
structure SM where
  names : Std.HashMap Nat NIdx := {}
  levels : Std.HashMap Nat LIdx := {}
  lists : Std.HashMap Nat LsIdx := {}
  exprs : Std.HashMap Nat EIdx := {}

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:100-105 SM.has
Does the memo hold the object at `g` as kind `k`. -/
def SM.has (st : SM) (k : UInt8) (g : Nat) : Bool :=
  if k = kName then st.names.contains g
  else if k = kLevel then st.levels.contains g
  else if k = kLevels then st.lists.contains g
  else st.exprs.contains g

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:132-138 Frontier
**Values read earlier, by kind and location**, read-only: which objects it holds is
a matter of speed alone.  Its handles are the load's.  The tables are upstream's
`Table`, representation-free. -/
structure Frontier where
  names : Table NIdx := {}
  levels : Table LIdx := {}
  lists : Table LsIdx := {}
  exprs : Table EIdx := {}

instance : Inhabited Frontier := ⟨{}⟩

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:142-147 Frontier.has
Does the frontier hold the object at `g` as kind `k`. -/
def Frontier.has (b : Frontier) (k : UInt8) (g : Nat) : Bool :=
  if k = kName then (b.names.get g).isSome
  else if k = kLevel then (b.levels.get g).isSome
  else if k = kLevels then (b.lists.get g).isSome
  else (b.exprs.get g).isSome

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:149-151 SM.holds
Does the read hold the object at `g` as kind `k`: its memo or the frontier. -/
@[inline] def SM.holds (st : SM) (b : Frontier) (k : UInt8) (g : Nat) : Bool :=
  st.has k g || b.has k g

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:159-177 SM.buildIn
The memo over a frontier as the node functions' `sub` (upstream's `lookup`, per
kind; the Rust's `SMIn`). -/
@[inline] def SM.subIn (st : SM) (b : Frontier) : Sub where
  name c := lookup st.names b.names c
  level c := lookup st.levels b.levels c
  levels c := lookup st.lists b.lists c
  expr c := lookup st.exprs b.exprs c

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:159-177 SM.buildIn
**The object at `g`, read as kind `k`**, by the node function, its kids' values from
the memo or the frontier, and added to the memo. -/
def SM.buildIn (pk : OleanPins) (r : Region) (b : Frontier) (k : UInt8) (g : Nat) (st : SM) :
    AM (Option SM) := do
  if k = kName then
    pure ((← nameNode pk r g (st.subIn b)).map fun v => { st with names := st.names.insert g v })
  else if k = kLevel then
    pure ((← levelNode pk r g (st.subIn b)).map fun v => { st with levels := st.levels.insert g v })
  else if k = kLevels then
    pure ((← levelsNode pk r g (st.subIn b)).map fun v => { st with lists := st.lists.insert g v })
  else
    pure ((← exprNode pk r g (st.subIn b)).map fun v => { st with exprs := st.exprs.insert g v })

set_option linter.unusedVariables false in
mutual
/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:184-197 sGo
**The object at `g` read as kind `k`, into the memo**: nothing to do if the memo or
the frontier holds it; else its kids, then the object itself. -/
def sGo (pk : OleanPins) (r : Region) (b : Frontier) (k : UInt8) (g : Nat) (st : SM) :
    AM (Option SM) := do
  if st.holds b k g then pure (some st)
  else if r.fits g then
    match kidTable k (r.tag g) (r.nobjs g) with
    | none => pure none
    | some fs =>
      match ← kidsGo pk r b g fs st with
      | some st => SM.buildIn pk r b k g st
      | none => pure none
  else pure none
termination_by (g, 1, 0)

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:199-214 kidsGo
The kids the fields `fs` of the object at `g` lead to, into the memo. -/
def kidsGo (pk : OleanPins) (r : Region) (b : Frontier) (g : Nat) :
    List (Nat × UInt8 × Bool) → SM → AM (Option SM)
  | [], st => pure (some st)
  | (i, k', nil) :: fs, st =>
    if nil && r.fld g i == 1 then kidsGo pk r b g fs st
    else match hd : r.down g (r.fld g i) with
      | some c => do
        match ← sGo pk r b k' c st with
        | some st => kidsGo pk r b g fs st
        | none => pure none
      | none => pure none
termination_by fs => (g, 0, fs.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; apply Prod.Lex.right; simp)
    | (apply Prod.Lex.left; exact ConLeche.Frontend.Olean.Region.down_lt hd)
end

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:219-221 frontierExpr
**The `Expr` at location `c`**, read with a memo of its own over a frontier. -/
def frontierExpr (pk : OleanPins) (r : Region) (b : Frontier) (c : Nat) : AM (Option EIdx) := do
  match ← sGo pk r b kExpr c {} with
  | some st => pure (lookup st.exprs b.exprs c)
  | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:223-228 sparseNameP
**The `Name` a pointer stands for**, read sparsely. -/
def sparseNameP (pk : OleanPins) (r : Region) (v : UInt64) : AM (Option NIdx) := do
  if v == 1 then pure (some pk.anon)
  else match r.loc v with
    | some c =>
      match ← sGo pk r {} kName c {} with
      | some st => pure (lookup st.names ({} : Frontier).names c)
      | none => pure none
    | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:230-234 sparseExprP
**The `Expr` a pointer stands for**, read sparsely. -/
def sparseExprP (pk : OleanPins) (r : Region) (v : UInt64) : AM (Option EIdx) := do
  match r.loc v with
  | some c => frontierExpr pk r {} c
  | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:236-239 sparseEntry
**A constant's names and expressions, read sparsely**: each root with a memo of its
own. -/
def sparseEntry (pk : OleanPins) (r : Region) (sk : CEntryF UInt64 UInt64) :
    AM (Option (CEntryF NIdx EIdx)) :=
  entryMap ⟨sparseNameP pk r, sparseExprP pk r⟩ sk

end ConRon.Arena.Frontend.Olean
