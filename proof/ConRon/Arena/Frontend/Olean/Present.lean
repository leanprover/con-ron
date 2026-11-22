/-
# `ConRon.Arena.Frontend.Olean.Present` — an imported constant as a context record (task #166)

The twin of `olean/present.rs`: a constant's read from a part of a view with one memo per part
(`entryWith`, `stmtWith`), and a constant as its record (`recordOfEntry`).
-/
module

public import ConLeche.Frontend.Olean.Present
public import ConRon.Arena.Frontend.Olean.Group

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF CKindF constSkel kName kExpr)

/-- con-leche: ConLeche/Frontend/Olean/Present.lean:25-30 entryWith
**The constant at location `c`, read with the part's memo**, which it extends. -/
def entryWith (pk : OleanPins) (r : Region) (st : SM) (c : Nat) :
    AM (SM × Option (CEntryF NIdx EIdx)) := do
  match constSkel r c with
  | none => pure (st, none)
  | some sk =>
    skelFits sk
    let st ← memoRoots pk r st sk
    pure (st, ← entryMap (memoRead pk r st) sk)

/-- con-leche: ConLeche/Frontend/Olean/Present.lean:32-42 stmtWith
**The statement and the kind of the constant at location `c`**, its kind's expressions left
out, read with the part's memo: a theorem's value is never read. -/
def stmtWith (pk : OleanPins) (r : Region) (st : SM) (c : Nat) :
    AM (SM × Option (StmtRec × CKindF NIdx Unit)) := do
  match constSkel r c with
  | none => pure (st, none)
  | some sk =>
    skelFits sk
    let st ← memoAddAll pk r kName st (sk.name :: sk.levelParams)
    let st ← memoAdd pk r kExpr st sk.type
    let rd := memoRead pk r st
    let r' ← (do
      let n ← OptionT.mk (rd.rdName sk.name)
      let lps ← sk.levelParams.mapM (m := OptionT AM) fun v => OptionT.mk (rd.rdName v)
      let ty ← OptionT.mk (rd.rdExpr sk.type)
      let k ← OptionT.mk (kindNames rd sk.kind)
      pure ((⟨n, lps, ty⟩ : StmtRec), k) : OptionT AM (StmtRec × CKindF NIdx Unit)).run
    pure (st, r')

/-- con-leche: ConLeche/Frontend/Olean/Present.lean:46-53 recordOfEntry
**One constant's record**, through the stream reader's builder (`Emit.one`, `declsOf`). -/
def recordOfEntry (c : CEntryF NIdx EIdx) : AM IDeclaration := do
  match ← declsOf (({} : Emit).one { c }) with
  | .error (e, _) => fail e
  | .ok ds =>
    match ds.decls.toList with
    | [d] => pure d
    | _ => fail (.internal s!"the constant {← readName c.name}: {ds.decls.size} records")

end ConRon.Arena.Frontend.Olean
