/-
# `ConRon.Bridge.Frontend.Builders` — con-leche's record builders, as the parse ran them before task #329

con-leche task #329 (the lookup interface of its parallel rounds parse)
rewrote `ConLeche/Frontend/ExportC.lean`'s record semantics as BUILDERS over
three table lookups (`nameOfF`, `levelOfF`, `exprOfF`, `pwOfF`, `cvOfF`,
`ruleOfF`, `validateIndF`, `indBlockOfF`, `declOfF`, over an `Lk` record),
and the serial parse's steps as those builders at the state's own tables
(`StateD.lk`).  The computation did not move — the twin's
`Arena/Frontend/ExportC.lean` and the Rust keep their own functions — and
this module is the proof of that: the state-reading spellings the parse had
at con-leche `67f04630`, verbatim (namespace `Prev`), and one equation per
function between them and the builders the parse runs now.  Theorem 1's
frontend tier (`Lines.lean`) is stated against con-leche's current functions
and reaches the old spellings only through these equations (con-ron task
#117).
-/
import ConLeche.Frontend.ExportC

namespace ConRon.Bridge.Frontend.Prev

set_option autoImplicit false
-- con-leche's own elaboration options (the project sets the other `do`
-- elaborator, `proof/lakefile.toml`): the copies must elaborate to the terms
-- con-leche's did
set_option backward.do.legacy false
set_option backward.isDefEq.respectTransparency true

open ConLeche ConLeche.Frontend

/-- Declaration-level expression lookup: the table read.

The frontend tree-size budget that used to sit here was **retired at
task #215**: every consumer it bounded is now either name-selected (the
basis-pin match) or a memoized DAG walk (`Expr.renameConsts`,
`Expr.instantiate1`; `@[csimp]` in `ConLeche/Kernel/ExprOps.lean`), and
the adversarial DAG-tower fixtures in `tests/e2e` are the standing
gate in its place — a limit told a user "no", a fixture tells *us*
which walker regressed. -/
def getDeclD (st : StateD) (i : Nat) : M Expr :=
  st.expr i

/-- The `pw` datum over the direct name table. -/
def parsePwD (st : StateD) : PwRec → M PropWhen
  | .never => pure .never
  | .ifAllZero ns => do pure (.ifAllZero (← ns.mapM st.name))

/-- A name-table entry: the name value is built directly. -/
def parseNameEntryD (st : StateD) (i : Nat) : NameRec → M StateD
  | .str pre s => do
    let p ← st.name pre
    st.freshName i
    pure { st with names := st.names.insert i (Name.str p s) }
  | .num pre n => do
    let p ← st.name pre
    st.freshName i
    pure { st with names := st.names.insert i (Name.num p n) }

/-- A level-table entry. -/
def parseLevelEntryD (st : StateD) (i : Nat) (r : LevelRec) : M StateD := do
  st.freshLevel i
  let l ← match r with
    | .succ u => do pure (Level.succ (← st.level u))
    | .max a b => do pure (Level.max (← st.level a) (← st.level b))
    | .imax a b => do pure (Level.imax (← st.level a) (← st.level b))
    | .param n => do pure (Level.param (← st.name n))
  pure { st with levels := st.levels.insert i l }

/-- An expression-table entry: build the `Expr` node from the
children's table values (the derived fields are the compiler's, task
#172 B3a).

Binder names are display data the official kernel's equality and hash
ignore; ours are `.anonymous` on every parsed binder (task #203,
beside the `.default` annotation of task #142), so `==` is
α-equivalence downstream.  The `name` field is still required to be
present and well-formed (the recogniser reads it), it is just not
resolved. -/
def parseExprEntryD (st : StateD) (i : Nat) (r : ExprRec) : M StateD := do
  st.freshExpr i
  let e ← match r with
    | .bvar k => pure (Expr.mkBvar k)
    | .sort u => do pure (Expr.mkSort (← st.level u))
    | .const n us => do
      let nm ← st.name n
      let ls ← us.mapM st.level
      pure (Expr.mkConst nm ls)
    | .app f a => do pure (Expr.mkApp (← st.expr f) (← st.expr a))
    | .lam ty bd pw => do
      pure (Expr.mkLam (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
    | .forallE ty bd pw => do
      pure (Expr.mkForallE (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
    | .letE ty vl bd => do
      pure (Expr.mkLetE (← st.expr ty) (← st.expr vl) (← st.expr bd))
    | .proj tn ix s => do
      pure (Expr.mkProj (← st.name tn) ix (← st.expr s))
    | .natVal n => pure (Expr.mkLit (.natVal n))
    | .strVal s => pure (Expr.mkLit (.strVal s))
  pure { st with exprs := st.exprs.insert i e }

/-! ## Declaration records -/

/-- A declaration's common data; the type stays `Expr`. -/
def parseCVD (st : StateD) (cv : CVRec) : M ConstantVal := do
  let name ← st.name cv.name
  let ty ← getDeclD st cv.type
  pure { name := name
         levelParams := ← cv.levelParams.mapM st.name
         type := ty }

/-- One recursor rule of an inductive record, resolved. -/
def parseRuleD (st : StateD) (ru : RuleRec) : M RecRule := do
  pure (RecRule.mk (← st.name ru.ctor) ru.nfields 0 .inert
    (← getDeclD st ru.rhs) false false false)

/-- **An inductive record, validated** (tasks #217, #228, #271): the
half of the record's processing that reads the state and changes
nothing — the verdict, or the block's constructors in the block's own
order with the declared parameter count.  Split from `installIndD`
below at task #290 so that a proof about what the parse does to its
state need not look here at all. -/
def validateIndD (st : @& StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) : M (RecordVerdict ⊕ (List IndCtorRec × Nat)) := do
  -- TASK #217 (audit follow-up 6): an `unsafe inductive` is DECLINED,
  -- not an error.  The official kernel admits unsafe blocks (it skips
  -- positivity for them); we support no unsafe declaration at all, and
  -- unsafe axioms/opaques/definitions already decline positively.
  if tys.any (·.isUnsafe) then
    return .inl (.declined "unsafe inductive declaration")
  -- TASK #228 — THE DECLARED PARAMETER COUNT.  Official's replay
  -- hands `add_inductive` the `numParams` of ONE inductive record of
  -- the block (`Declaration.inductDecl lparams nparams types`,
  -- `Lean4Checker/Replay.lean`) and checks every former and every
  -- constructor against it; which record that is, is the name order
  -- of the replay's walk.  So the count is well defined for the
  -- block exactly when its type records AGREE on it — as every
  -- record a real export writes does, `add_inductive` storing one
  -- `m_nparams` in every member's `InductiveVal`.  A block whose
  -- records disagree has no declared count this checker could hold
  -- official to, and is positively declined here rather than checked
  -- against a count official might not have chosen.
  let nPs := tys.map (·.numParams)
  let nPd := nPs.head?.getD 0
  unless nPs.all (· == nPd) do
    return .inl (.declined "inductive block whose type records disagree on numParams")
  -- TASK #271 (issues #5 and #7) — THE BLOCK'S REDUNDANT FIELDS.
  -- Official's replay hands `add_inductive` the type formers, the
  -- constructors and the parameter count; the kernel then GENERATES
  -- the constructors and the recursors, and the replay compares each
  -- exported CONSTRUCTOR and RECURSOR record with the generated one
  -- structurally (`checkPostponedConstructors`,
  -- `checkPostponedRecursors`, `Lean4Checker/Replay.lean`) — a
  -- mismatch is "Invalid constructor" / "Invalid recursor", a
  -- REJECT.  An exported INDUCTIVE record is never compared with the
  -- generated `InductiveVal`, so its `numIndices`, `numNested`,
  -- `isRec`, `isReflexive` and `all` are not input official reads and
  -- are not checked here either (the `numParams` half official DOES
  -- read is task #228's, just above).  What is read of a type record
  -- is its `ctors` list: it groups the constructor records into the
  -- block, and it IS the block's constructor order (issue #5 — the
  -- `cidx` field is the redundant copy, not the other way round).
  -- These are consistency checks between the stream's own fields, so
  -- they live here, in the parse, and their verdict is `.invalid`:
  -- the fold never sees such a block.
  let tyNames ← tys.mapM fun t => st.name t.cv.name
  let tyTypes ← tys.mapM fun t => getDeclD st t.cv.type
  let listed ← tys.mapM fun t => t.ctors.mapM st.name
  let ctorNames ← cts.mapM fun c => st.name c.cv.name
  let flat := listed.flatten
  unless flat.Nodup do
    return .inl (.invalid "duplicate constructor name in an inductive type's ctors")
  unless flat.length == cts.length do
    return .inl (.invalid s!"the inductive block lists {flat.length} constructors \
      and carries {cts.length} constructor records")
  let ctorIx : Std.HashMap Name Nat :=
    (ctorNames.foldl (fun (mi : Std.HashMap Name Nat × Nat) n =>
      (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1
  let ctsA := cts.toArray
  -- the constructors IN THE BLOCK'S OWN ORDER, `types[].ctors` in
  -- type order (issue #5): a record array in another order is the
  -- same block, and the recursor generated from it is the same one
  let mut ordered : Array IndCtorRec := #[]
  for tn in tyNames.zip listed do
    let (T, ns) := tn
    let mut j := 0
    for n in ns do
      let some k := ctorIx[n]? | return .inl (.invalid s!"No such constructor {n}")
      let some c := ctsA[k]? | return .inl (.invalid s!"No such constructor {n}")
      if let some ci := c.cidx then
        unless ci == j do
          return .inl (.invalid s!"constructor {n} declares cidx {ci}; it is \
            constructor {j} of {T}")
      if let some iw := c.induct then
        let iwn ← st.name iw
        unless iwn == T do
          return .inl (.invalid s!"constructor {n} declares induct {iwn}; it is \
            a constructor of {T}")
      -- `numFields`: official counts the constructor's own Π binders
      -- without reducing (`check_constructors` walks `is_pi`) and
      -- stores the count past the parameters, so a record that
      -- declares another number is not the generated constructor.
      -- Before this, a count too LARGE declined at the field
      -- telescope (arena `ctor-num-fields`) and a count too small was
      -- caught later, by the constructor's result type, if at all.
      let cty ← getDeclD st c.cv.type
      unless nPd + c.numFields == indPiTeleLen cty do
        return .inl (.invalid s!"constructor {n} declares {c.numFields} fields at \
          {nPd} parameters; its type has {indPiTeleLen cty} binders")
      ordered := ordered.push c
      j := j + 1
  let cts := ordered.toList
  -- The recursor records: the counts and the K flag the GENERATED
  -- recursor carries.  `numParams + numMotives + numMinors` and the
  -- major-premise index are compared with the block at the install
  -- (the recursor stage), which leaves a compensating pair of lies
  -- open; the individual counts are here.
  --
  -- NOT at a NESTED block.  The kernel specialises a nested block
  -- into a mutual one with a mimic type per nested occurrence, and
  -- the recursors it generates — `T.rec`, `T.rec_1`, … — are the
  -- SPECIALISED block's: their motives and minor premises count the
  -- mimics too, so the declared block's own type and constructor
  -- counts are not what they carry (measured: `ind_nest_inf`'s
  -- `InfNest.rec` declares two motives at one declared type).
  -- `numNested` is a field of the type record, which official never
  -- compares; reading it here only ever WEAKENS these checks, never
  -- rejects on it.
  let nested := tys.any (·.numNested != 0)
  let nTypes := tys.length
  let nCtors := cts.length
  -- official's `is_K_target`: the block is a `Prop`, has ONE type
  -- with ONE constructor, and that constructor takes only the
  -- parameters.  At a former whose declared type is not a syntactic
  -- Π-telescope ending in a sort (task #195) the sort cannot be read
  -- here and the flag is left to the install.
  let kExpected? : Option Bool :=
    match tyTypes, listed, cts with
    | [ty], [[_]], [c] =>
      match ty.piResult with
      | .sort s => some (c.numFields == 0 && Level.isEquiv s .zero == some true)
      | _ => none
    | _, _, _ => some false
  for r in (if nested then [] else rcs) do
    let rn ← st.name r.cv.name
    unless r.numParams == nPd do
      return .inl (.invalid s!"recursor {rn} declares {r.numParams} parameters; \
        the block declares {nPd}")
    unless r.numMotives == nTypes do
      return .inl (.invalid s!"recursor {rn} declares {r.numMotives} motives; \
        the block has {nTypes} inductive types")
    unless r.numMinors == nCtors do
      return .inl (.invalid s!"recursor {rn} declares {r.numMinors} minor premises; \
        the block has {nCtors} constructors")
    if let some kE := kExpected? then
      unless r.k == kE do
        return .inl (.invalid s!"recursor {rn} declares k := {r.k}; the generated \
          recursor of this block is{if kE then "" else " not"} K-like")
    -- `numIndices` of `T.rec` is what is left of `T`'s own telescope
    -- once the parameters are peeled; unreadable at a former declared
    -- at a definition, and then not checked
    if let .str T "rec" := rn then
      for tt in tyNames.zip tyTypes do
        if tt.1 == T then
          if let some n := tt.2.piSortTeleLen? then
            unless nPd + r.numIndices == n do
              return .inl (.invalid s!"recursor {rn} declares {r.numIndices} indices; \
                {T} has {n - nPd} at {nPd} parameters")
  return .inr (cts, nPd)

/-- **An inductive record, installed**: the block's constants, pushed
as one `indDecl`.  Every change to the state a validated inductive
record makes is here. -/
def installIndD (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (nPd : Nat) : M StateD := do
  let types ← tys.mapM fun t => do
    pure (ConstantInfo.indInfo (← parseCVD st t.cv) {})
  let ctors ← cts.mapM fun c => do
    pure (ConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields)
  let recs ← rcs.mapM fun r => do
    let rules ← r.rules.mapM (parseRuleD st)
    pure (ConstantInfo.recInfo (← parseCVD st r.cv)
      (r.numParams + r.numMotives + r.numMinors + r.numIndices)
      (r.numParams + r.numMotives + r.numMinors) rules)
  let block := types ++ ctors ++ recs
  -- **EVERY BLOCK IS AN `indDecl`** (task #293): the basis-pin match
  -- that used to stand here — a name pre-filter (task #215) and then
  -- `canonEqList` against the five pinned blocks — is
  -- `preparePrelude`'s (`ConLeche/Frontend/Prepare.lean`), which
  -- retags a matching block to its `basisDecl` kind before the fold
  -- sees it.  A block under a pinned name that does NOT match keeps
  -- its `indDecl` form and is rejected by the fold's reserved-name
  -- check, exactly as before.
  return pushDecl st (.indDecl block nPd)

/-- The record's own semantics: the declaration kinds, producing
`Declaration` records.  Every branch, guard and error string is the one the
`Lean.Json` reader this replaced had (task #256); only the reads
changed, from key lookups in a DOM to fields of a syntax record. -/
def processLineCoreD (st : StateD) (d : DeclRec) : M (StateD ⊕ RecordVerdict) := do
  match d with
  | .ax cvr isUnsafe =>
    let cvp ← parseCVD st cvr
    if isUnsafe then
      return .inr (.declined "unsafe axiom")
    -- **`Quot.sound` is the FOLD's** (task #293): the axiom record is
    -- forwarded like any other, and the fold compares it with the
    -- pinned soundness axiom (`checkDecl`'s `.axiomDecl` arm) — the
    -- decline on a mismatch was the parser's and is not any more.
    return .inl (pushDecl st (.axiomDecl cvp))
  | .defn cvr value hints safety =>
    let cvp ← parseCVD st cvr
    match safety with
    | "safe" =>
      let vl ← getDeclD st value
      let h : ReducibilityHint := match hints with
        | .«abbrev» => .«abbrev»
        | .«opaque» => .«opaque»
        | .regular n => .regular n
      return .inl (pushDecl st (.defnDecl cvp vl h))
    | s => return .inr (.declined s!"definition with safety '{s}'")
  | .thm cvr value =>
    let cvp ← parseCVD st cvr
    let vl ← getDeclD st value
    return .inl (pushDecl st (.thmDecl cvp vl))
  | .opaq cvr value isUnsafe =>
    let cvp ← parseCVD st cvr
    if isUnsafe then
      return .inr (.declined "unsafe opaque declaration")
    let vl ← getDeclD st value
    return .inl (pushDecl st (.opaqueDecl cvp vl))
  | .quot cvr kind =>
    -- **ONE RECORD PER `#QUOT` LINE** (task #293): the file declares
    -- the quotient package as four records, and the decoder emits four
    -- — the constant as the file declares it, at the kind the file
    -- declares it at.  The comparison with the pinned block
    -- (`preparePrelude`, which retags a matching record to
    -- `basisDecl .quotK`) and the decline on a mismatch (the fold's
    -- `.quotDecl` arm) are not the parser's any more.
    let cv ← parseCVD st cvr
    let qk ← match kind with
      | "type" => pure QuotKind.type
      | "ctor" => pure QuotKind.ctor
      | "lift" => pure QuotKind.lift
      | "ind" => pure QuotKind.ind
      | k => throw s!"unknown quotient kind '{k}'"
    return .inl (pushDecl st (.quotDecl qk cv))
  | .ind tys cts rcs =>
    match ← validateIndD st tys cts rcs with
    | .inl v => pure (.inr v)
    | .inr (cts, nPd) => return .inl (← installIndD st tys cts rcs nPd)

/-! ## The equations: what the parse runs now is the old spelling -/

theorem getDeclD_eq (st : StateD) (i : Nat) : getDeclD st i = st.expr i := rfl

theorem parsePwD_eq (st : StateD) (r : PwRec) :
    parsePwD st r = pwOfF st.name st.level st.expr r := by
  cases r <;> rfl

theorem parseNameEntryD_eq (st : StateD) (i : Nat) (r : NameRec) :
    ConLeche.Frontend.parseNameEntryD st i r = parseNameEntryD st i r := by
  cases r <;>
    simp only [ConLeche.Frontend.parseNameEntryD, parseNameEntryD, nameOf, nameOfF,
      StateD.lk, bind_assoc, pure_bind]

theorem parseLevelEntryD_eq (st : StateD) (i : Nat) (r : LevelRec) :
    ConLeche.Frontend.parseLevelEntryD st i r = parseLevelEntryD st i r := by
  cases r <;>
    simp only [ConLeche.Frontend.parseLevelEntryD, parseLevelEntryD, levelOf, levelOfF,
      StateD.lk, bind_assoc, pure_bind]

theorem parseExprEntryD_eq (st : StateD) (i : Nat) (r : ExprRec) :
    ConLeche.Frontend.parseExprEntryD st i r = parseExprEntryD st i r := by
  cases r <;>
    simp only [ConLeche.Frontend.parseExprEntryD, parseExprEntryD, exprOf, exprOfF,
      StateD.lk, bind_assoc, pure_bind, ← parsePwD_eq]

theorem parseCVD_eq (st : StateD) (cv : CVRec) :
    parseCVD st cv = cvOfF st.name st.level st.expr cv := rfl

theorem parseRuleD_fn (st : StateD) :
    parseRuleD st = ruleOfF st.name st.level st.expr := rfl

theorem validateIndD_eq (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) :
    validateIndD st tys cts rcs = validateIndF st.name st.level st.expr tys cts rcs :=
  rfl

theorem installIndD_eq (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (nPd : Nat) :
    installIndD st tys cts rcs nPd =
      (indBlockOfF st.name st.level st.expr tys cts rcs nPd >>= fun d =>
        pure (pushDecl st d)) := by
  simp only [installIndD, indBlockOfF, ← parseCVD_eq, ← parseRuleD_fn, bind_assoc,
    pure_bind]

theorem processLineCoreD_eq (st : StateD) (d : DeclRec) :
    ConLeche.Frontend.processLineCoreD st d = processLineCoreD st d := by
  cases d <;>
    simp only [ConLeche.Frontend.processLineCoreD, processLineCoreD, declOf, declOfF,
      StateD.lk, ← parseCVD_eq, ← getDeclD_eq, ← validateIndD_eq, installIndD_eq,
      bind_assoc, pure_bind] <;>
    refine bind_congr fun x => ?_ <;>
    (try split) <;>
    simp only [bind_assoc, pure_bind]
  all_goals (cases ‹HintsRec› <;> rfl)

end ConRon.Bridge.Frontend.Prev
