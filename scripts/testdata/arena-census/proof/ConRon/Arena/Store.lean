/-!
The store's NAMESPACES, which are why a census row is keyed by the QUALIFIED
name: `dropScratch` is declared twice here (once in `NStore`, once in
`EStore`) and `find?` twice, and `viewApp` is a THIRD twin whose leaf
`Monad.lean` also uses.  Round 1 collapsed all of that into one row each.
-/

namespace ConRon.Arena

namespace Tbl

/-- The cons-table probe. -/
def find? (t : Tbl) (a : α) : Option ι := none

end Tbl

namespace NStore

/-- Drop the scratch tier.  The FIRST `dropScratch` of this file. -/
def dropScratch (st : NStore) : NStore := st

end NStore

namespace EStore

/-- The store-level `app` projection, which is NOT `Monad.lean`'s wrapper of
the same leaf: `viewApp_spec` is that one's, `EStore.viewApp_spec` is this
one's. -/
def viewApp (st : EStore) (i : EIdx) : Option (EIdx × EIdx) := none

/-- Drop the scratch tier.  The SECOND `dropScratch`. -/
def dropScratch (st : EStore) : EStore := st

/-- Probe both tiers, persistent first. -/
def find? (st : EStore) (v : ENodeView) : Option EIdx := none

/-- The `bvar` arm of the derived-word dispatch, whose Theorem 2 is the
up-to-`derObsE` shape `_obs`. -/
def derOfBVar (st : EStore) (i : Nat) : UInt64 := 0

end EStore

end ConRon.Arena
