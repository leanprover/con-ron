/-
Every byte `ConRon.Refine.PinsDec` accepts is ASCII (task #64).

`ConRon/Refine/Pins.lean`'s statement is about `absText t`, and `absText` is a
UTF-8 *decode*: to turn a byte suffix into a character suffix at all, the text
has to be ASCII.  It is — every byte the decoder looks at it either compares to
a fixed value (`32`, `10`, `92`, `59`, a record letter) or bounds into
`33 … 126` — but that is a fact about the *program*, not about the format, so
it has to be proved.

Proving it over the Aeneas model would be a second walk over fifty functions.
Proving it over `PinsDec` is one `Consumes` predicate and one lemma per reader,
which is what this file is: `Consumes bs r` says that every byte of `bs` is
either still to be read (it is a byte of `r`) or ASCII, every reader preserves
it, and the pass consumes the *whole* text (`runFooter` insists the remainder
is empty), so `decode_ascii` gets ASCII for all of `bs`.
-/
import ConRon.Refine.PinsDec

namespace ConRon.Refine.PinsDec

open ConLeche

/-! ## The predicate

The "what has been read so far was ASCII" invariant, stated as a `∀` and not
as the `∃ pre, bs = pre ++ r ∧ …` one might write first: `refl`, `trans` and
`cons` are then one-line terms, and each is all a reader's lemma needs. -/

/-- Every byte of `bs` is either a byte of `bs`'s remainder `r` or ASCII. -/
def Consumes (bs r : Bytes) : Prop := ∀ b ∈ bs, b ∈ r ∨ b < 128

theorem Consumes.refl (bs : Bytes) : Consumes bs bs := fun _ h => Or.inl h

theorem Consumes.trans {a b c : Bytes} (h1 : Consumes a b) (h2 : Consumes b c) :
    Consumes a c := fun x hx => (h1 x hx).elim (h2 x) Or.inr

/-- Reading one ASCII byte. -/
theorem Consumes.cons {b : Nat} {bs r : Bytes} (hb : b < 128)
    (h : Consumes bs r) : Consumes (b :: bs) r := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inr hb
  · exact h x hx

/-- Nothing left to read: the invariant is the conclusion. -/
theorem Consumes.ascii {bs : Bytes} (h : Consumes bs []) : ∀ b ∈ bs, b < 128 := by
  intro b hb
  rcases h b hb with hb' | hb'
  · exact absurd hb' (by simp)
  · exact hb'

/-! ## The two tactics

Every reader is a chain of `match … with | none => none | some … => …` over
the previous one, so every proof below is the same two steps: `crush` splits
the chain and throws away the arms that fail, leaving one equation per step in
the context, and `consumes` (below, once the steps' lemmas exist) folds those
equations with `Consumes.trans`.  `byte_lt` is for the one byte a record
dispatch compares to a literal rather than passing to a reader. -/

/-- Split every `match`/`if` of a decoder equation `h : f … = some …`,
discharging the arms that return `none`, and read off the result equation. -/
macro "crush" h:ident : tactic => `(tactic|
  ((repeat' (first
      | contradiction
      | split at $h:ident
      | dsimp only at $h:ident)) <;>
    (try (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident
          first
            | (obtain ⟨-, hr⟩ := $h:ident; subst hr)
            | subst $h:ident))))

/-- The record and sub-kind letters: a byte the dispatch compared to a literal
is ASCII. -/
macro "byte_lt" : tactic => `(tactic|
  first
    | omega
    | (simp only [Bool.or_eq_true, decide_eq_true_eq] at *; omega))

/-! ## Bytes and scalars -/

theorem lt128_of_isDigit {b : Nat} (h : isDigit b = true) : b < 128 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem lt128_of_hexDigit {b : Nat} (h : hexDigit b ≠ 16) : b < 128 := by
  rw [hexDigit] at h
  split at h
  · rename_i hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    omega
  · split at h
    · rename_i hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      omega
    · exact absurd rfl h

theorem afterSpace_consumes {bs r : Bytes} (h : afterSpace bs = some r) :
    Consumes bs r := by
  unfold afterSpace at h
  crush h
  exact Consumes.cons (by omega) (Consumes.refl _)

theorem afterNewline_consumes {bs r : Bytes} (h : afterNewline bs = some r) :
    Consumes bs r := by
  unfold afterNewline at h
  crush h
  exact Consumes.cons (by omega) (Consumes.refl _)

theorem readNatFrom_consumes : ∀ (bs : Bytes) {acc n : Nat} {r : Bytes},
    readNatFrom bs acc = some (n, r) → Consumes bs r := by
  intro bs
  induction bs with
  | nil => intro acc n r h; rw [readNatFrom] at h; exact absurd h (by simp)
  | cons b bs ih =>
    intro acc n r h
    rw [readNatFrom] at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · exact Consumes.cons (lt128_of_isDigit (by assumption)) (ih h)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact Consumes.refl _
      · exact absurd h (by simp)

theorem readNat_consumes {bs : Bytes} {n : Nat} {r : Bytes}
    (h : readNat bs = some (n, r)) : Consumes bs r := by
  rw [readNat] at h
  split at h
  · exact readNatFrom_consumes _ h
  · exact absurd h (by simp)

theorem readIndex_consumes {bs : Bytes} {n : Nat} {r : Bytes}
    (h : readIndex bs = some (n, r)) : Consumes bs r := by
  rw [readIndex] at h
  exact readNat_consumes h

theorem readBigNatFrom_consumes : ∀ (bs : Bytes) {acc n : Nat} {r : Bytes},
    readBigNatFrom bs acc = some (n, r) → Consumes bs r := by
  intro bs
  induction bs with
  | nil => intro acc n r h; rw [readBigNatFrom] at h; exact absurd h (by simp)
  | cons b bs ih =>
    intro acc n r h
    rw [readBigNatFrom] at h
    split at h
    · exact Consumes.cons (lt128_of_isDigit (by assumption)) (ih h)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact Consumes.refl _
      · exact absurd h (by simp)

theorem readBigNat_consumes {bs : Bytes} {n : Nat} {r : Bytes}
    (h : readBigNat bs = some (n, r)) : Consumes bs r := by
  rw [readBigNat] at h
  split at h
  · exact readBigNatFrom_consumes _ h
  · exact absurd h (by simp)

theorem expectId_consumes {bs : Bytes} {want : Nat} {r : Bytes}
    (h : expectId bs want = some r) : Consumes bs r := by
  rw [expectId] at h
  crush h
  exact readIndex_consumes (by assumption)

/-! ## Strings -/

theorem unescapeFrom_consumes : ∀ (bs : Bytes) {v : Nat} {e : Bool}
    {out s : List Nat} {r : Bytes},
    unescapeFrom bs v e out = some (s, r) → Consumes bs r := by
  intro bs
  induction bs with
  | nil => intro v e out s r h; rw [unescapeFrom] at h; exact absurd h (by simp)
  | cons b bs ih =>
    intro v e out s r h
    rw [unescapeFrom] at h
    split at h
    · -- `b` is a space or a newline: the field ends here
      split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact Consumes.refl _
    · split at h
      · -- inside an escape
        split at h
        · -- the closing `;`
          split at h
          · exact Consumes.cons (by omega) (ih h)
          · exact absurd h (by simp)
        · -- a hex digit
          dsimp only at h
          split at h
          · exact absurd h (by simp)
          · rename_i hd
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hd
            exact Consumes.cons (lt128_of_hexDigit fun hh => hd (Or.inl hh)) (ih h)
      · split at h
        · -- the opening `\`
          exact Consumes.cons (by omega) (ih h)
        · split at h
          · exact absurd h (by simp)
          · -- a literal character, bounded into `33 … 126`
            rename_i hb
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or,
              Nat.not_lt] at hb
            exact Consumes.cons (by omega) (ih h)

theorem readString_consumes {bs : Bytes} {s : List Nat} {r : Bytes}
    (h : readString bs = some (s, r)) : Consumes bs r := by
  rw [readString] at h
  crush h
  exact Consumes.trans (readIndex_consumes (by assumption))
    (Consumes.trans (afterSpace_consumes (by assumption))
      (unescapeFrom_consumes _ (by assumption)))

/-! ## Backward references -/

theorem nameRef_consumes {bs : Bytes} {tb : Tables} {n : Name} {r : Bytes}
    (h : nameRef bs tb = some (n, r)) : Consumes bs r := by
  rw [nameRef] at h
  crush h
  exact readIndex_consumes (by assumption)

theorem levelRef_consumes {bs : Bytes} {tb : Tables} {u : Level} {r : Bytes}
    (h : levelRef bs tb = some (u, r)) : Consumes bs r := by
  rw [levelRef] at h
  crush h
  exact readIndex_consumes (by assumption)

theorem pwRef_consumes {bs : Bytes} {tb : Tables} {p : PropWhen} {r : Bytes}
    (h : pwRef bs tb = some (p, r)) : Consumes bs r := by
  rw [pwRef] at h
  crush h
  exact readIndex_consumes (by assumption)

theorem exprRef_consumes {bs : Bytes} {tb : Tables} {e : Expr} {r : Bytes}
    (h : exprRef bs tb = some (e, r)) : Consumes bs r := by
  rw [exprRef] at h
  crush h
  exact readIndex_consumes (by assumption)

/-! ## The counted lists -/

theorem nameListFrom_consumes : ∀ (k : Nat) {bs : Bytes} {tb : Tables}
    {out ns : List Name} {r : Bytes},
    nameListFrom bs tb k out = some (ns, r) → Consumes bs r := by
  intro k
  induction k with
  | zero =>
    intro bs tb out ns r h
    rw [nameListFrom] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Consumes.refl _
  | succ k ih =>
    intro bs tb out ns r h
    rw [nameListFrom] at h
    crush h
    exact Consumes.trans (afterSpace_consumes (by assumption))
      (Consumes.trans (nameRef_consumes (by assumption)) (ih (by assumption)))

theorem nameList_consumes {bs : Bytes} {tb : Tables} {ns : List Name} {r : Bytes}
    (h : nameList bs tb = some (ns, r)) : Consumes bs r := by
  rw [nameList] at h
  crush h
  exact Consumes.trans (readIndex_consumes (by assumption))
    (nameListFrom_consumes _ (by assumption))

theorem levelListFrom_consumes : ∀ (k : Nat) {bs : Bytes} {tb : Tables}
    {out us : List Level} {r : Bytes},
    levelListFrom bs tb k out = some (us, r) → Consumes bs r := by
  intro k
  induction k with
  | zero =>
    intro bs tb out us r h
    rw [levelListFrom] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Consumes.refl _
  | succ k ih =>
    intro bs tb out us r h
    rw [levelListFrom] at h
    crush h
    exact Consumes.trans (afterSpace_consumes (by assumption))
      (Consumes.trans (levelRef_consumes (by assumption)) (ih (by assumption)))

theorem levelList_consumes {bs : Bytes} {tb : Tables} {us : List Level}
    {r : Bytes} (h : levelList bs tb = some (us, r)) : Consumes bs r := by
  rw [levelList] at h
  crush h
  exact Consumes.trans (readIndex_consumes (by assumption))
    (levelListFrom_consumes _ (by assumption))

theorem exprListFrom_consumes : ∀ (k : Nat) {bs : Bytes} {tb : Tables}
    {out es : List Expr} {r : Bytes},
    exprListFrom bs tb k out = some (es, r) → Consumes bs r := by
  intro k
  induction k with
  | zero =>
    intro bs tb out es r h
    rw [exprListFrom] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Consumes.refl _
  | succ k ih =>
    intro bs tb out es r h
    rw [exprListFrom] at h
    crush h
    exact Consumes.trans (afterSpace_consumes (by assumption))
      (Consumes.trans (exprRef_consumes (by assumption)) (ih (by assumption)))

theorem exprList_consumes {bs : Bytes} {tb : Tables} {es : List Expr} {r : Bytes}
    (h : exprList bs tb = some (es, r)) : Consumes bs r := by
  rw [exprList] at h
  crush h
  exact Consumes.trans (readIndex_consumes (by assumption))
    (exprListFrom_consumes _ (by assumption))

theorem pinsEightFrom_consumes : ∀ (k : Nat) {bs : Bytes} {tb : Tables}
    {out es : List Expr} {r : Bytes},
    pinsEightFrom bs tb k out = some (es, r) → Consumes bs r := by
  intro k
  induction k with
  | zero =>
    intro bs tb out es r h
    rw [pinsEightFrom] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Consumes.refl _
  | succ k ih =>
    intro bs tb out es r h
    rw [pinsEightFrom] at h
    crush h
    exact Consumes.trans (afterSpace_consumes (by assumption))
      (Consumes.trans (exprRef_consumes (by assumption)) (ih (by assumption)))

theorem pinsEight_consumes {bs : Bytes} {tb : Tables} {es : List Expr}
    {r : Bytes} (h : pinsEight bs tb = some (es, r)) : Consumes bs r := by
  rw [pinsEight] at h
  exact pinsEightFrom_consumes _ h

theorem proofsEightFrom_consumes : ∀ (k : Nat) {bs : Bytes} {tb : Tables}
    {out ess : List (List Expr)} {r : Bytes},
    proofsEightFrom bs tb k out = some (ess, r) → Consumes bs r := by
  intro k
  induction k with
  | zero =>
    intro bs tb out ess r h
    rw [proofsEightFrom] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Consumes.refl _
  | succ k ih =>
    intro bs tb out ess r h
    rw [proofsEightFrom] at h
    crush h
    exact Consumes.trans (afterSpace_consumes (by assumption))
      (Consumes.trans (exprList_consumes (by assumption)) (ih (by assumption)))

theorem proofsEight_consumes {bs : Bytes} {tb : Tables} {ess : List (List Expr)}
    {r : Bytes} (h : proofsEight bs tb = some (ess, r)) : Consumes bs r := by
  rw [proofsEight] at h
  exact proofsEightFrom_consumes _ h

/-! ## Composing the readers

Every record below is a straight chain of the readers above, so its proof is
`crush` followed by a `Consumes.trans` fold over the equations `crush` left in
the context.  The fold is greedy and deterministic — at each point exactly one
hypothesis reads the byte string the goal is still at — which is why this is a
`repeat` over `refine`s rather than a `solve_by_elim`: the search version has
to guess `Consumes.trans`' middle and does not terminate in practice. -/

/-- Fold the chain of reader equations in the context into the goal's
`Consumes`. -/
macro "consumes" : tactic => `(tactic|
  repeat (first
    | exact Consumes.refl _
    | refine Consumes.trans (afterSpace_consumes (by assumption)) ?_
    | refine Consumes.trans (afterNewline_consumes (by assumption)) ?_
    | refine Consumes.trans (readNat_consumes (by assumption)) ?_
    | refine Consumes.trans (readIndex_consumes (by assumption)) ?_
    | refine Consumes.trans (readBigNat_consumes (by assumption)) ?_
    | refine Consumes.trans (expectId_consumes (by assumption)) ?_
    | refine Consumes.trans (readString_consumes (by assumption)) ?_
    | refine Consumes.trans (nameRef_consumes (by assumption)) ?_
    | refine Consumes.trans (levelRef_consumes (by assumption)) ?_
    | refine Consumes.trans (pwRef_consumes (by assumption)) ?_
    | refine Consumes.trans (exprRef_consumes (by assumption)) ?_
    | refine Consumes.trans (nameList_consumes (by assumption)) ?_
    | refine Consumes.trans (levelList_consumes (by assumption)) ?_
    | refine Consumes.trans (exprList_consumes (by assumption)) ?_
    | refine Consumes.trans (pinsEight_consumes (by assumption)) ?_
    | refine Consumes.trans (proofsEight_consumes (by assumption)) ?_))

/-! ## The records -/

theorem recordNameStr_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordNameStr bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordNameStr] at h
  crush h
  consumes

theorem recordNameNum_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordNameNum bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordNameNum] at h
  crush h
  consumes

theorem recordName_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordName bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordName] at h
  crush h
  all_goals
    refine Consumes.trans (expectId_consumes (by assumption)) ?_
    refine Consumes.trans (afterSpace_consumes (by assumption)) ?_
    refine Consumes.cons (by byte_lt) ?_
    first
      | exact recordNameStr_consumes (by assumption)
      | exact recordNameNum_consumes (by assumption)
      | consumes

theorem recordLevelSucc_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordLevelSucc bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordLevelSucc] at h
  crush h
  consumes

theorem recordLevelBinop_consumes {bs : Bytes} {tb tb' : Tables} {isMax : Bool}
    {r : Bytes} (h : recordLevelBinop bs tb isMax = some (tb', r)) :
    Consumes bs r := by
  rw [recordLevelBinop] at h
  crush h
  consumes

theorem recordLevelParam_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordLevelParam bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordLevelParam] at h
  crush h
  consumes

theorem recordLevel_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordLevel bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordLevel] at h
  crush h
  all_goals
    refine Consumes.trans (expectId_consumes (by assumption)) ?_
    refine Consumes.trans (afterSpace_consumes (by assumption)) ?_
    refine Consumes.cons (by byte_lt) ?_
    first
      | exact recordLevelSucc_consumes (by assumption)
      | exact recordLevelBinop_consumes (by assumption)
      | exact recordLevelParam_consumes (by assumption)
      | consumes

theorem recordPwZero_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordPwZero bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordPwZero] at h
  crush h
  consumes

theorem recordPw_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordPw bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordPw] at h
  crush h
  all_goals
    refine Consumes.trans (expectId_consumes (by assumption)) ?_
    refine Consumes.trans (afterSpace_consumes (by assumption)) ?_
    refine Consumes.cons (by byte_lt) ?_
    first
      | exact recordPwZero_consumes (by assumption)
      | consumes

theorem recordExprBvar_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprBvar bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprBvar] at h
  crush h
  consumes

theorem recordExprFvar_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprFvar bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprFvar] at h
  crush h
  consumes

theorem recordExprSort_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprSort bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprSort] at h
  crush h
  consumes

theorem recordExprConst_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprConst bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprConst] at h
  crush h
  consumes

theorem recordExprApp_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprApp bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprApp] at h
  crush h
  consumes

theorem recordExprBinder_consumes {bs : Bytes} {tb tb' : Tables} {isLam : Bool}
    {r : Bytes} (h : recordExprBinder bs tb isLam = some (tb', r)) :
    Consumes bs r := by
  rw [recordExprBinder] at h
  crush h
  consumes

theorem recordExprLet_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprLet bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprLet] at h
  crush h
  consumes

theorem recordExprNatLit_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprNatLit bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprNatLit] at h
  crush h
  consumes

theorem recordExprStrLit_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprStrLit bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprStrLit] at h
  crush h
  consumes

theorem recordExprProj_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExprProj bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExprProj] at h
  crush h
  consumes

theorem recordExpr_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordExpr bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordExpr] at h
  crush h
  all_goals
    refine Consumes.trans (expectId_consumes (by assumption)) ?_
    refine Consumes.trans (afterSpace_consumes (by assumption)) ?_
    refine Consumes.cons (by byte_lt) ?_
    first
      | exact recordExprBvar_consumes (by assumption)
      | exact recordExprFvar_consumes (by assumption)
      | exact recordExprSort_consumes (by assumption)
      | exact recordExprConst_consumes (by assumption)
      | exact recordExprApp_consumes (by assumption)
      | exact recordExprBinder_consumes (by assumption)
      | exact recordExprLet_consumes (by assumption)
      | exact recordExprNatLit_consumes (by assumption)
      | exact recordExprStrLit_consumes (by assumption)
      | exact recordExprProj_consumes (by assumption)
      | consumes

theorem recordPinSet_consumes {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordPinSet bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordPinSet] at h
  crush h
  consumes

/-! ## The pass -/

theorem recordStep_consumes {k : Nat} {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordStep k bs tb = some (tb', r)) : Consumes bs r := by
  rw [recordStep] at h
  crush h
  all_goals
    first
      | exact recordName_consumes (by assumption)
      | exact recordLevel_consumes (by assumption)
      | exact recordPw_consumes (by assumption)
      | exact recordExpr_consumes (by assumption)
      | exact recordPinSet_consumes (by assumption)

/-- A record letter the dispatch accepted is one of `N L W E S`. -/
theorem recordStep_letter {k : Nat} {bs : Bytes} {tb tb' : Tables} {r : Bytes}
    (h : recordStep k bs tb = some (tb', r)) : k < 128 := by
  rw [recordStep] at h
  repeat' (first
    | omega
    | split at h
    | contradiction)

theorem runFooter_consumes {bs : Bytes} {tb : Tables} {ps : List NatOpPinSet}
    (h : runFooter bs tb = some ps) : Consumes bs [] := by
  unfold runFooter at h
  crush h
  rename_i hcond
  simp only [ne_eq, Bool.or_eq_true, decide_eq_true_eq, not_or,
    Decidable.not_not] at hcond
  obtain ⟨hr, -⟩ := hcond
  subst hr
  exact Consumes.cons (by omega) (Consumes.cons (by omega) (by consumes))

theorem runRecords_consumes : ∀ (f : Nat) {bs : Bytes} {tb : Tables}
    {ps : List NatOpPinSet}, runRecords f bs tb = some ps → Consumes bs [] := by
  intro f
  induction f with
  | zero =>
    intro bs tb ps h
    rw [runRecords] at h
    exact absurd h (by simp)
  | succ f ih =>
    intro bs tb ps h
    cases bs with
    | nil => rw [runRecords] at h; exact absurd h (by simp)
    | cons k bs =>
      rw [runRecords] at h
      split at h
      · exact Consumes.cons (by omega) (runFooter_consumes h)
      · crush h
        refine Consumes.cons (recordStep_letter (by assumption)) ?_
        exact Consumes.trans (afterSpace_consumes (by assumption))
          (Consumes.trans (recordStep_consumes (by assumption))
            (ih (by assumption)))

/-! ## The header, and the whole text -/

theorem startsWith_consumes : ∀ (p : Bytes), (∀ b ∈ p, b < 128) →
    ∀ {bs : Bytes}, startsWith bs p = true → Consumes bs (bs.drop p.length) := by
  intro p
  induction p with
  | nil => intro _ bs _; simpa using Consumes.refl bs
  | cons c p ih =>
    intro hp bs h
    cases bs with
    | nil => rw [startsWith] at h; exact absurd h (by simp)
    | cons b bs =>
      rw [startsWith] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h2⟩ := h
      have hrec := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h2
      simpa only [List.length_cons, List.drop_succ_cons] using
        Consumes.cons (hp b (by simp)) hrec

/-- **The whole text is ASCII.**  What `Refine/PinsSplit.lean` needs to read
`absText` as a character list. -/
theorem decode_ascii {bs : Bytes} {ps : List ConLeche.NatOpPinSet}
    (h : decode bs = some ps) : ∀ b ∈ bs, b < 128 := by
  rw [decode] at h
  split at h
  · exact Consumes.ascii
      ((startsWith_consumes headerBytes (by decide) (by assumption)).trans
        (runRecords_consumes _ h))
  · exact absurd h (by simp)

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/-- info: 'ConRon.Refine.PinsDec.decode_ascii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_ascii

end ConRon.Refine.PinsDec
