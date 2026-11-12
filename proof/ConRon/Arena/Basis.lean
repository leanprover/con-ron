/-
# `ConRon.Arena.Basis` — the pinned basis blocks, over handles

The twin of `ConLeche/Kernel/Basis.lean` and the Rust twin of `arena::basis`:
the constants of the five pinned blocks (`Eq`, `Nat`, `Empty`, `False`,
`Quot`), a pin at a stream's level-parameter names (`IConstantInfo.atLps`),
the block's comparison with its pin (`pinListOk`), the name test that says a
record is a pinned block's (`basisNameHit`), the reserved names' check run
after a declaration's own checks (`basisNamesOk`, `basisNamesError`), what a
quotient record stores (`quotAt`), and the fold's `And` pin
(`andPinOk`): a record that declares `And`, `And.intro` or `And.rec` and is
not the toolchain's block is rejected.

**The pins are con-leche's values, interned** (`Arena/Intern.lean`'s module
note).  `ConLeche/Kernel/Basis/{Names,Builder,Empty,Eq,False,Nat,Quot}.lean`
are pure `Expr` and `ConstantInfo` data, hand-written against the toolchain's
`Init.Prelude`; DESIGN §8.7's ruling is that (B) imports con-leche's
representation-free data rather than copying it.  What IS a twin here is the
renaming, the comparisons and the recognisers.

**`beqP` is `==`.**  con-leche compares with its pointer-first `…beqP`
(`Kernel/Canon.lean`); over handles that is the derived `DecidableEq`
(interning is injective), which the Rust spells out (`arena::canon`'s
`i_constant_info_beq` and siblings) because Rust has no derive.
-/
module

public import ConRon.Arena.Intern
public import ConRon.Arena.Canon
public import ConRon.Arena.CheckerBase

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Basis.lean:39-45 BasisKind.decls — the
constants of one basis block, in install order, interned. -/
def BasisKind.decls (k : BasisKind) : AM (List IConstantInfo) :=
  internCIList (ConLeche.BasisKind.decls k)

/-- con-leche: ConLeche/Kernel/Basis/Nat.lean:24-26 natA — the pinned `Nat`
type former, interned: its `ConstantVal` is the comparand of `reduceElemOk`'s
`ConstantVal.matchesPin`. -/
def natA : AM IConstantInfo :=
  internCI ConLeche.natA

/-! ## A pin at a stream's level-parameter names -/

/-- con-leche: ConLeche/Kernel/Basis.lean:54-56 ConstantVal.atLps — a
constant's common data at other level-parameter names: the type with the old
names replaced positionally. -/
def IConstantVal.atLps (cv : IConstantVal) (ps : List NIdx) : AM IConstantVal := do
  let us ← paramLevels ps
  let ty ← instLPFast coreWalkFuel cv.levelParams us cv.type
  pure ⟨cv.name, ps, ty⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:58-61 RecRuleFire.atLps — a firing
mode at other level-parameter names: the `.levels` comparands substituted,
every other mode as it is. -/
def IRecRuleFire.atLps (lps : List ConLeche.Name) (us : List Level) :
    IRecRuleFire → AM IRecRuleFire
  | .levels lvls => do pure (.levels (← substLevelsAt lps us lvls))
  | f => pure f

/-- con-leche: ConLeche/Kernel/Basis.lean:63-79 ConstantInfo.atLps — the
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Basis.rulesAtLps_bridge, then delete this line
`.recInfo` arm's `rules.map`: each rule's right-hand side and firing mode at
the new names (`lpsH`/`us` as handles for `instantiateLevelParams`,
`lpsT`/`usT` read back for `Level.subst`). -/
def rulesAtLps (lpsH : List NIdx) (us : LsIdx) (lpsT : List ConLeche.Name)
    (usT : List Level) : List IRecRule → AM (List IRecRule)
  | [] => pure []
  | r :: rs => do
    let rhs ← instLPFast coreWalkFuel lpsH us r.rhs
    let fire ← r.fire.atLps lpsT usT
    let rest ← rulesAtLps lpsH us lpsT usT rs
    pure ({ ctor := r.ctor, nfields := r.nfields, fire, rhs } :: rest)

/-- con-leche: ConLeche/Kernel/Basis.lean:63-79 ConstantInfo.atLps — **a stored
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Basis.IConstantInfo.atLps_bridge, then delete this line
constant at other level-parameter names**: its type, a definition's value, its
rules' right-hand sides and firing modes renamed; nothing else. -/
def IConstantInfo.atLps (ci : IConstantInfo) (ps : List NIdx) : AM IConstantInfo := do
  match ci with
  | .axiomInfo cv => pure (.axiomInfo (← cv.atLps ps))
  | .defnInfo cv v h => do
    let cv2 ← cv.atLps ps
    let us ← paramLevels ps
    let v2 ← instLPFast coreWalkFuel cv.levelParams us v
    pure (.defnInfo cv2 v2 h)
  | .thmInfo cv => pure (.thmInfo (← cv.atLps ps))
  | .indInfo cv caps => pure (.indInfo (← cv.atLps ps) caps)
  | .ctorInfo cv nP nF => pure (.ctorInfo (← cv.atLps ps) nP nF)
  | .recInfo cv mI rP isK rules => do
    let cv2 ← cv.atLps ps
    let us ← paramLevels ps
    let lpsT ← readNamesM cv.levelParams
    let psT ← readNamesM ps
    let rules2 ← rulesAtLps cv.levelParams us lpsT (psT.map Level.param) rules
    pure (.recInfo cv2 mI rP isK rules2)

/-- con-leche: ConLeche/Kernel/Basis.lean:81-85 pinAgrees — a record against
the pin at the record's own names: what the record writes.  An inductive
record has no capabilities to compare. -/
def pinAgrees : IConstantInfo → IConstantInfo → Bool
  | .indInfo v _, .indInfo v' _ => v == v'
  | c, c' => c == c'

/-- con-leche: ConLeche/Kernel/Basis.lean:87-92 pinCopyOk — **is the record the
pin, up to its level-parameter names?**  Distinct names, as many as the pin's;
the renaming is computed only when both hold. -/
def pinCopyOk (ci pin : IConstantInfo) : AM Bool := do
  let ps := ci.toConstantVal.levelParams
  if nameNodup ps && ps.length == pin.toConstantVal.levelParams.length then
    pure (pinAgrees ci (← pin.atLps ps))
  else pure false

/-- con-leche: ConLeche/Kernel/Basis.lean:94-99 pinLinkOk — **what a recursor's
rule reads off its constructor's parameters**, by name: the constructor's
parameters at the recursor's names, compared on read-back levels. -/
def pinLinkOk (R Rp C Cp : List NIdx) : AM Bool := do
  let rT ← readNamesM R
  let rpT ← readNamesM Rp
  let cT ← readNamesM C
  let cpT ← readNamesM Cp
  pure (cT.map Level.param ==
    cpT.map fun p => Level.subst rpT (rT.map Level.param) (.param p))

/-- con-leche: ConLeche/Kernel/Basis.lean:101-103 constNamed? — the constant of
a list by name. -/
def constNamed? (cs : List IConstantInfo) (n : NIdx) : Option IConstantInfo :=
  cs.find? fun c => c.name == n

/-- con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk — the cited
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Basis.rulesLinkOk_bridge, then delete this line
`rules.all`: each of the pin's rules' constructors, found in both lists,
linked as the pin links it. -/
def rulesLinkOk (block pins : List IConstantInfo) (R Rp : List NIdx) :
    List IRecRule → AM Bool
  | [] => pure true
  | rl :: rls => do
    match constNamed? block rl.ctor, constNamed? pins rl.ctor with
    | some C, some Cp =>
      if ← pinLinkOk R Rp C.toConstantVal.levelParams Cp.toConstantVal.levelParams then
        rulesLinkOk block pins R Rp rls
      else pure false
    | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk — the cited
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Basis.blockLinkOkAt_bridge, then delete this line
`match c, p with`, one pair. -/
def blockLinkOkAt (block pins : List IConstantInfo) (former : List NIdx) :
    IConstantInfo → IConstantInfo → AM Bool
  | .ctorInfo cv _ _, _ => pure (cv.levelParams == former)
  | .recInfo cv .., .recInfo cvp _ _ _ rules =>
    rulesLinkOk block pins cv.levelParams cvp.levelParams rules
  | _, _ => pure true

/-- con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk — the cited
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Basis.blockLinksOkGo_bridge, then delete this line
`(List.zip block pins).all`, as a recursion over the pairs. -/
def blockLinksOkGo (block pins : List IConstantInfo) (former : List NIdx) :
    List IConstantInfo → List IConstantInfo → AM Bool
  | c :: cs, p :: ps => do
    if ← blockLinkOkAt block pins former c p then blockLinksOkGo block pins former cs ps
    else pure false
  | _, _ => pure true

/-- con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk — the stream's
-- con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove Basis.blockLinksOk_bridge, then delete this line
recursor links its rules' constructors as the pin's does (`pinLinkOk`), and a
constructor carries its former's names. -/
def blockLinksOk (block pins : List IConstantInfo) : AM Bool :=
  let former := (block.head?.map (·.toConstantVal.levelParams)).getD []
  blockLinksOkGo block pins former block pins

/-- con-leche: ConLeche/Kernel/Canon.lean:291-295 listBeqBy
con-leche: ConLeche/Kernel/Basis.lean:121-123 pinListOk — the cited
`listBeqBy pinCopyOk block pins`, at the one function it is applied to. -/
def pinCopiesOk : List IConstantInfo → List IConstantInfo → AM Bool
  | [], [] => pure true
  | c :: cs, p :: ps => do
    if ← pinCopyOk c p then pinCopiesOk cs ps else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Basis.lean:121-123 pinListOk — **the block's
comparison with its pin** (the check phase's). -/
def pinListOk (block pins : List IConstantInfo) : AM Bool := do
  if ← pinCopiesOk block pins then blockLinksOk block pins else pure false

/-! ## Recognising a pinned block in a stream record -/

/-- con-leche: none — `block.map (·.name)`; `IConstantInfo.name` is pure. -/
def blockNames (block : List IConstantInfo) : List NIdx :=
  block.map (·.name)

/-- con-leche: ConLeche/Kernel/Basis.lean:133-136 basisNameHit — the cited
`List.find?` over the four kinds. -/
def basisNameHitGo (block : List IConstantInfo) : List BasisKind → AM (Option BasisKind)
  | [] => pure none
  | k :: ks => do
    let pinned ← ConRon.Arena.BasisKind.decls k
    if blockNames pinned == blockNames block then pure (some k)
    else basisNameHitGo block ks

/-- con-leche: ConLeche/Kernel/Basis.lean:133-136 basisNameHit — **the pinned
block a record declares**, by its members' names.  `.quotK` is not among the
kinds tried (a quotient arrives as five one-constant records). -/
def basisNameHit (block : List IConstantInfo) : AM (Option BasisKind) :=
  basisNameHitGo block [BasisKind.eqK, .natK, .emptyK, .falseK]

/-! ## The reserved names -/

/-- con-leche: ConLeche/Kernel/Basis.lean:138-151 basisNamesOk — the
one-constant arms' test, `!reservedBasisNames.contains cv.name`. -/
def basisNameUnreserved (n : NIdx) : AM Bool := do
  let rs ← reservedBasisNames
  pure !(rs.contains n)

/-- con-leche: ConLeche/Kernel/Basis.lean:138-151 basisNamesOk — **the reserved
names' check**, the one place the checker sets the basis names apart.  It runs
after a declaration's own checks, which treat a basis block as any other
block: a block under one of the pinned blocks' names must be that block, up to
its level-parameter names (`pinListOk`), and no other declaration may take a
reserved name.  `Quot.sound` and the quotient records are compared with their
own pins, so they pass here. -/
def basisNamesOk : IDeclaration → AM Bool
  | .indDecl block _ => do
    match ← basisNameHit block with
    | some kind => pinListOk block (← ConRon.Arena.BasisKind.decls kind)
    | none => do
      let rs ← reservedBasisNames
      pure (block.all fun c => !rs.contains c.name)
  | .axiomDecl cv => do
    if cv.name == (← pinQuotSound) then pure true else basisNameUnreserved cv.name
  | .quotDecl _ _ => pure true
  | .defnDecl cv _ _ => basisNameUnreserved cv.name
  | .thmDecl cv _ => basisNameUnreserved cv.name
  | .opaqueDecl cv _ => basisNameUnreserved cv.name

/-- con-leche: ConLeche/Kernel/Basis.lean:153-161 basisNamesError — **what a
failed `basisNamesOk` reports**: a block under a pinned block's names that is
not the pin, a reserved name in another block, or a one-constant declaration at
a reserved name; all invalid input.  The messages drop con-leche's interpolated
names (§3.1). -/
def basisNamesError : IDeclaration → AM CheckError
  | .indDecl block _ => do
    match ← basisNameHit block with
    | some _ => pure (.invalid "reserved basis name: the block is not the pinned one")
    | none => pure (.invalid "reserved basis name in the block of")
  | _ => pure (.invalid "reserved basis name")

/-- con-leche: ConLeche/Kernel/Basis.lean:163-165 quotPin — the pinned quotient
package's constant at a slot. -/
def quotPin (k : QuotKind) : AM IConstantInfo := do
  let blk ← ConRon.Arena.BasisKind.decls .quotK
  pure (blk.getD k.slot default)

/-- con-leche: ConLeche/Kernel/Basis.lean:167-170 quotAt — **what a quotient
record stores**: its slot's pin at the names it declares. -/
def quotAt (k : QuotKind) (cv : IConstantVal) : AM IConstantInfo := do
  (← quotPin k).atLps cv.levelParams

/-- con-leche: ConLeche/Kernel/Basis.lean:172-178 quotPinHit — **the
quotient-pin match**: the record is the pinned package's constant at the slot
it declares itself at, up to its level-parameter names: distinct, as many as
the pin's. -/
def quotPinHit (k : QuotKind) (cv : IConstantVal) : AM Bool := do
  let pcv := (← quotPin k).toConstantVal
  if nameNodup cv.levelParams && cv.levelParams.length == pcv.levelParams.length then
    pure (cv == (← pcv.atLps cv.levelParams))
  else pure false

/-- con-leche: ConLeche/Kernel/Basis.lean:180-192 quotPredsOk — **what a
quotient record's slot needs stored before it**: the constants its type
mentions.  The cited `find?` argument is the index `fe`. -/
def quotPredsOk (fe : IFEnv) (k : QuotKind) : AM Bool := do
  let hasEq := (fe.find? (← pinEq)).isSome
  let hasQ := (fe.find? (← pinQuot)).isSome
  let hasM := (fe.find? (← pinQuotMk)).isSome
  pure (match k with
    | .type => hasEq
    | .ctor => hasQ
    | .lift => hasEq && hasQ && hasM
    | .ind => hasQ && hasM
    | .sound => hasEq && hasQ && hasM)

/-! ## The pinned `And` (con-leche's ANDPIN) -/

/-- con-leche: ConLeche/Kernel/Basis/And.lean:94-95 andPin — the pinned `And`
block, interned: `BasisKind.decls`'s shape for the one pinned block that is
recognised and never installed from literals. -/
def andPinDecls : AM (List IConstantInfo) :=
  internCIList ConLeche.andPin

/-- con-leche: ConLeche/Kernel/Basis/And.lean:97-99 andPinNames — the names
the pinned `And` block declares, as handles, off the reserved-name table: three
slot reads, no interning. -/
def andPinNameHs : AM (List NIdx) := do
  let a ← pinAnd
  let i ← pinAndIntro
  let r ← pinAndRec
  pure [a, i, r]

/-- con-leche: ConLeche/Kernel/Basis.lean:206-214 andPinOk — the `.indDecl`
arm's `block.any fun c => andPinNames.contains c.name`, over handles (a name
comparison is a handle comparison, `denoteN` being injective). -/
def blockAndNamed (hs : List NIdx) : List IConstantInfo → Bool
  | [] => false
  | c :: cs => hs.contains c.name || blockAndNamed hs cs

/-- con-leche: ConLeche/Kernel/Basis.lean:206-214 andPinOk — the arm of every
one-constant record: it may not declare one of the pinned `And` block's
names. -/
def andPinNameFree (n : NIdx) : AM Bool := do
  let hs ← andPinNameHs
  pure !(hs.contains n)

/-- con-leche: ConLeche/Kernel/Basis.lean:206-214 andPinOk — **the `And` pin's
test**: the record declares none of the pinned `And` block's names, or it IS
that block — two parameters, and equal to `andPin` up to `ConstantInfo.canon`
(`canonEqList`).  Only a block that declares one of the three names gets that
far. -/
def andPinOk : IDeclaration → AM Bool
  | .indDecl block nP => do
    let hs ← andPinNameHs
    if blockAndNamed hs block then
      if nP == 2 then do
        let pinned ← andPinDecls
        canonEqList block pinned
      else pure false
    else pure true
  | .axiomDecl cv => andPinNameFree cv.name
  | .defnDecl cv _ _ => andPinNameFree cv.name
  | .thmDecl cv _ => andPinNameFree cv.name
  | .opaqueDecl cv _ => andPinNameFree cv.name
  | .quotDecl _ cv => andPinNameFree cv.name

end ConRon.Arena
