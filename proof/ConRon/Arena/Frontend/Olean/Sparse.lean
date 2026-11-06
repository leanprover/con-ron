/-
# `ConRon.Arena.Frontend.Olean.Sparse` — the sparse decoder (task #142)

The twin of `olean/sparse.rs`.  The kid table (`kidTable`) is upstream's own: shapes
and field numbers.  The memo holds handles, by location.
-/
module

public import ConLeche.Frontend.Olean.Sparse
public import ConRon.Arena.Frontend.Olean.Spec

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF kName kLevel kExpr kLevels kidTable)

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

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:99-112 SM.build
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Sparse.SM.sub_bridge, then delete this line
The memo's values as the node functions' `sub`. -/
@[inline] def SM.sub (st : SM) : Sub where
  name c := st.names[c]?
  level c := st.levels[c]?
  levels c := st.lists[c]?
  expr c := st.exprs[c]?

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:99-112 SM.build
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Sparse.SM.build_bridge, then delete this line
**The object at `g`, read as kind `k`**, by the node function, its kids' values from
the memo, and added to it. -/
def SM.build (pk : OleanPins) (r : Region) (k : UInt8) (g : Nat) (st : SM) : AM (Option SM) := do
  if k = kName then
    pure ((← nameNode pk r g st.sub).map fun v => { st with names := st.names.insert g v })
  else if k = kLevel then
    pure ((← levelNode pk r g st.sub).map fun v => { st with levels := st.levels.insert g v })
  else if k = kLevels then
    pure ((← levelsNode pk r g st.sub).map fun v => { st with lists := st.lists.insert g v })
  else
    pure ((← exprNode pk r g st.sub).map fun v => { st with exprs := st.exprs.insert g v })

set_option linter.unusedVariables false in
mutual
/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:184-197 sGo
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Sparse.sGo_bridge, then delete this line
**The object at `g` read as kind `k`, into the memo**: nothing to do if it is there;
else its kids, then the object itself. -/
def sGo (pk : OleanPins) (r : Region) (k : UInt8) (g : Nat) (st : SM) : AM (Option SM) := do
  if st.has k g then pure (some st)
  else if r.fits g then
    match kidTable k (r.tag g) (r.nobjs g) with
    | none => pure none
    | some fs =>
      match ← kidsGo pk r g fs st with
      | some st => SM.build pk r k g st
      | none => pure none
  else pure none
termination_by (g, 1, 0)

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:199-214 kidsGo
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Sparse.kidsGo_bridge, then delete this line
The kids the fields `fs` of the object at `g` lead to, into the memo. -/
def kidsGo (pk : OleanPins) (r : Region) (g : Nat) :
    List (Nat × UInt8 × Bool) → SM → AM (Option SM)
  | [], st => pure (some st)
  | (i, k', nil) :: fs, st =>
    if nil && r.fld g i == 1 then kidsGo pk r g fs st
    else match hd : r.down g (r.fld g i) with
      | some c => do
        match ← sGo pk r k' c st with
        | some st => kidsGo pk r g fs st
        | none => pure none
      | none => pure none
termination_by fs => (g, 0, fs.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; apply Prod.Lex.right; simp)
    | (apply Prod.Lex.left; exact ConLeche.Frontend.Olean.Region.down_lt hd)
end

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:223-228 sparseNameP
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Sparse.sparseNameP_bridge, then delete this line
**The `Name` a pointer stands for**, read sparsely. -/
def sparseNameP (pk : OleanPins) (r : Region) (v : UInt64) : AM (Option NIdx) := do
  if v == 1 then pure (some pk.anon)
  else match r.loc v with
    | some c =>
      match ← sGo pk r kName c {} with
      | some st => pure st.names[c]?
      | none => pure none
    | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:230-234 sparseExprP
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Sparse.sparseExprP_bridge, then delete this line
**The `Expr` a pointer stands for**, read sparsely. -/
def sparseExprP (pk : OleanPins) (r : Region) (v : UInt64) : AM (Option EIdx) := do
  match r.loc v with
  | some c =>
    match ← sGo pk r kExpr c {} with
    | some st => pure st.exprs[c]?
    | none => pure none
  | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:236-239 sparseEntry
**A constant's names and expressions, read sparsely**: each root with a memo of its
own. -/
def sparseEntry (pk : OleanPins) (r : Region) (sk : CEntryF UInt64 UInt64) :
    AM (Option (CEntryF NIdx EIdx)) :=
  entryMap ⟨sparseNameP pk r, sparseExprP pk r⟩ sk

end ConRon.Arena.Frontend.Olean
