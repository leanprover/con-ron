/-
# `ConRon.Bridge.Checker.Basis` — the pinned blocks and the axiom installs

Three things that share a shape: they compare a stream record against a
BUILD-TIME literal and install the literal, not the record.

* `Arena/Basis.lean` — `BasisKind.decls` / `declsA` (the six pinned blocks in
  raw and annotated form), `basisPinHit`, `quotPinHit`;
* `Arena/StdAxioms.lean` — `propext`, `Classical.choice`, the `Iff` and
  `Nonempty` families;
* `Arena/TrustAxioms.lean` — `Lean.trustCompiler`, the two `reduce*` opaques
  and the two `ofReduce*` axioms.

**Why all three are one module of the bridge.**  Each arena definition is
`internCI`/`internCV`/`internExpr` of the corresponding con-leche VALUE
(`Arena/Intern.lean`), so each one's bridge theorem is one instance of the
frontend tier's intern exactness — `denoteCI st (internCI c) = some c` — and
nothing else.  There is no algorithm to mirror: the literal is the same
literal, and the only question is whether interning it preserves its meaning.

**What DOES have content** is `checkBasisDecl`, because it is the one place
the environment grows by a whole block at once: `installBasisDecls` pushes six
or seven constants in one step, so `Pushed` is a six-fold `Pushed.push` and
the `k` the fold's promotion computes is the block's length.  That is the only
place in the checker where a step installs more than one constant outside the
inductive route, and the fold's counter arithmetic has to survive it.
-/
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Frontend.Shared

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The interned literals -/

/-- con-leche: ConLeche/Kernel/Basis.lean:41-66 BasisKind.decls — the raw
pinned block denotes con-leche's.

**PROVED** (task #97-P3-Checker round 7): `Frontend.internCIList_sstep` at a
fresh memo.  One line of import and three of proof — the frontend round's
`IStepS` family is stated without a scratch flag and without the `Pers…`
conjuncts, which is exactly what a caller inside the per-declaration bracket
can use and all this statement asks for. -/
theorem BasisKind.decls_run {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s) (hrun : BasisKind.decls k s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      Frontend.denoteCIList s'.store r = some k.decls := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -, -⟩ :=
    Frontend.internCIList_sstep (ConLeche.BasisKind.decls k) hok
      (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep.ok, hstep.ext, hstep.caches, hstep.pins, hden⟩

/-- con-leche: ConLeche/Kernel/BasisA.lean:51-57 BasisKind.declsA — the
ANNOTATED pinned block denotes con-leche's.  This is the one the install
puts in the environment.

**PROVED** (task #97-P3-Checker round 7): as `BasisKind.decls_run`. -/
theorem BasisKind.declsA_run {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s)
    (hrun : BasisKind.declsA k s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      Frontend.denoteCIList s'.store r = some k.declsA := by
  simp only [ConRon.Arena.BasisKind.declsA, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -, -⟩ :=
    Frontend.internCIList_sstep (ConLeche.BasisKind.declsA k) hok
      (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep.ok, hstep.ext, hstep.caches, hstep.pins, hden⟩

/-- con-leche: none — the same walk's fourth conjunct, kept as its own
theorem so that `BasisKind.decls_run`'s conclusion stays the five clauses its
consumers read: every member of the interned block is rightly named, which is
what `toConstantVal_sstep` asks of a `.projInfo` member (there is none, but
the theorem below does not know that). -/
theorem BasisKind.decls_proj {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s)
    (hrun : BasisKind.decls k s = .ok (r, s')) :
    ∀ ci ∈ r, Frontend.CIProjNamed s'.store ci := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨-, -, -, hnamed⟩ :=
    Frontend.internCIList_sstep (ConLeche.BasisKind.decls k) hok
      (Frontend.EMemoOK.empty s.store) hgo
  exact hnamed

/-! ## The common data of a pinned constant

`IConstantInfo.toConstantVal` is pure on six of its seven arms and interns a
`Sort 1` on the seventh (`Arena/Env.lean`: `denoteProjTable` drops
`tableName`, so the table's common data is rebuilt rather than stored).  That
makes it the tier's FIFTH `.projInfo` site, and it is stated here in the
scratch-agnostic frame — `Frontend.IStepS`, not `IStep` — because every
consumer of it inside the checker (`quotPinHit`, `natOpGuard`) runs inside the
per-declaration bracket, where the scratch tier is open and no `hoff` exists.
`Bridge/Frontend/Lines.lean`'s `toConstantVal_run` is the same theorem at the
parse's own frame, where `hoff` is available and the `Pers…` half is wanted. -/

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
**the common data of a stored constant denotes con-leche's**, with no
assumption about the scratch tier. -/
theorem toConstantVal_sstep {s s' : AState} (hok : StateOK s)
    {ci : IConstantInfo} {c : ConstantInfo}
    (hn : Frontend.CIProjNamed s.store ci)
    (hd : Frontend.denoteCI s.store ci = some c) {v : IConstantVal}
    (hrun : IConstantInfo.toConstantVal ci s = .ok (v, s')) :
    Frontend.IStepS s s' ∧
      Frontend.denoteCV s'.store v = some c.toConstantVal := by
  have hpure : ∀ (w : IConstantVal) (cw : ConstantVal),
      Frontend.denoteCV s.store w = some cw →
      (pure w : AM IConstantVal) s = .ok (v, s') →
      Frontend.IStepS s s' ∧ Frontend.denoteCV s'.store v = some cw := by
    intro w cw hw hr
    obtain ⟨hvv, hss⟩ := AM.pure_ok hr
    subst hvv; subst hss
    exact ⟨Frontend.IStepS.refl hok, hw⟩
  cases ci with
  | axiomInfo w =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    exact hpure w cw hw hrun
  | ctorInfo w nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cw, hw, rfl⟩ := hd
    exact hpure w cw hw hrun
  | defnInfo w e hh =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | thmInfo w e =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases he : denoteE s.store e with
      | none => rw [hw, he] at hd; simp at hd
      | some x =>
        rw [hw, he] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | indInfo w cps =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases hc : Frontend.denoteCaps s.store cps with
      | none => rw [hw, hc] at hd; simp at hd
      | some x =>
        rw [hw, hc] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | recInfo w mI rP rs =>
    simp only [Frontend.denoteCI] at hd
    cases hw : Frontend.denoteCV s.store w with
    | none => rw [hw] at hd; simp at hd
    | some cw =>
      cases hr : Frontend.denoteRules s.store rs with
      | none => rw [hw, hr] at hd; simp at hd
      | some x =>
        rw [hw, hr] at hd
        obtain rfl := Option.some.inj hd
        exact hpure w cw hw hrun
  | projInfo tbl =>
    obtain ⟨sn, hsn, htn⟩ := hn tbl rfl
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨pt, hpt, rfl⟩ := hd
    have hlps : Frontend.denoteNList s.store.ns tbl.levelParams
        = some pt.levelParams ∧ pt.structName = sn := by
      simp only [Frontend.denoteProjTable, hsn] at hpt
      cases hl : Frontend.denoteNList s.store.ns tbl.levelParams with
      | none => rw [hl] at hpt; simp at hpt
      | some lps =>
        cases hc : denoteN s.store.ns tbl.ctor with
        | none => rw [hl, hc] at hpt; simp at hpt
        | some cn =>
          cases hss : denoteL s.store.ls tbl.structSort with
          | none => rw [hl, hc, hss] at hpt; simp at hpt
          | some ss =>
            cases hbs : Frontend.denoteEArray s.store tbl.bodies with
            | none => rw [hl, hc, hss, hbs] at hpt; simp at hpt
            | some bs =>
              cases hgs : denoteLList s.store.ls tbl.guards with
              | none => rw [hl, hc, hss, hbs, hgs] at hpt; simp at hpt
              | some gs =>
                rw [hl, hc, hss, hbs, hgs] at hpt
                obtain rfl := Option.some.inj hpt
                exact ⟨rfl, rfl⟩
    obtain ⟨hdlps, hstruct⟩ := hlps
    rw [ConRon.Arena.IConstantInfo.toConstantVal] at hrun
    obtain ⟨z, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdz⟩ :=
      Frontend.internLNode_sstep hok
        ⟨by intro c hc; simp only [LNodeView.lchildren] at hc; exact absurd hc (by simp),
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h1
    have hdz' : denoteL s₁.store.ls z = some .zero := by
      rw [hdz]; rfl
    obtain ⟨one, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdo⟩ :=
      Frontend.internLNode_sstep hstep1.ok
        ⟨by intro c hc
            simp only [LNodeView.lchildren, List.mem_singleton] at hc
            subst hc; exact lview_isSome_of_denote hdz',
         by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩ h2
    have hdo' : denoteL s₂.store.ls one = some (.succ .zero) := by
      rw [hdo]
      simp only [denoteLView, denoteL_ext hdz' hstep2.ext, Option.map_some]
    obtain ⟨ty, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hstep3, hdty⟩ :=
      Frontend.internE_sstep hstep2.ok (viewOK_sort (lview_isSome_of_denote hdo')) h3
    have hdty' : denoteE s₃.store ty = some (.sort (.succ .zero)) := by
      rw [hdty]
      simp only [denoteEView, denoteL_ext hdo' hstep3.ext, Option.map_some]
    have hx : Ext s.store s₃.store :=
      (hstep1.ext.trans hstep2.ext).trans hstep3.ext
    obtain ⟨hvv, hss⟩ := AM.pure_ok hrest3
    subst hss; subst hvv
    refine ⟨(hstep1.trans hstep2).trans hstep3, ?_⟩
    simp only [Frontend.denoteCV, ConstantInfo.toConstantVal, hstruct,
      denoteN_ext htn hx, denoteNListE_ext hx _ _ hdlps, hdty']

/-! ## `Arena/Intern.lean`'s fresh-memo wrappers, in run form

`Arena/StdAxioms.lean` and `Arena/TrustAxioms.lean` are one line each — the
con-leche constant, interned at a fresh memo — so their bridges are one
instance apiece of the frontend tier's intern exactness.  These three are that
instance, in the scratch-agnostic frame: `basisPinHit` and the axiom shape
tests all run inside the per-declaration bracket. -/

/-- con-leche: none — `Arena.internCI` (a fresh memo) denotes its argument. -/
theorem internCI_fresh {c : ConstantInfo} {ci : IConstantInfo} {s s' : AState}
    (hok : StateOK s) (hrun : ConRon.Arena.internCI c s = .ok (ci, s')) :
    Frontend.IStepS s s' ∧ Frontend.denoteCI s'.store ci = some c ∧
      Frontend.CIProjNamed s'.store ci := by
  simp only [ConRon.Arena.internCI] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, x⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -, hnamed⟩ :=
    Frontend.internCI_sstep hok (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep, hden, hnamed⟩

/-- con-leche: none — `Arena.internCV` (a fresh memo) denotes its argument. -/
theorem internCV_fresh {c : ConstantVal} {cv : IConstantVal} {s s' : AState}
    (hok : StateOK s) (hrun : ConRon.Arena.internCV c s = .ok (cv, s')) :
    Frontend.IStepS s s' ∧ Frontend.denoteCV s'.store cv = some c := by
  simp only [ConRon.Arena.internCV] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, x⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hden, -⟩ :=
    Frontend.internCV_sstep hok (Frontend.EMemoOK.empty s.store) hgo
  exact ⟨hstep, hden⟩

/-! ## No pinned block declares a projection table

Six of the seven `IConstantInfo` constructors need nothing of the tier's
standing `.projInfo` hypothesis; the seventh is a projection table, and **no
basis block contains one** — a table never occurs in parsed input, and the six
pinned blocks are `axiomInfo`/`defnInfo`/`indInfo`/`ctorInfo`/`recInfo` only.
That is a fact about con-leche's data and `decide` settles it on six blocks of
at most five constants, so every `.projInfo` obligation of the install below
is discharged rather than carried. -/

/-- con-leche: ConLeche/Kernel/BasisA.lean:51-57 BasisKind.declsA — no member
of an annotated pinned block is a projection table. -/
theorem basis_declsA_no_proj (k : BasisKind) :
    ∀ x ∈ ConLeche.BasisKind.declsA k, x.isTowerEntry = false := by
  cases k <;> decide

/-- con-leche: ConLeche/Kernel/Basis.lean:41-46 BasisKind.decls — the same of
the RAW block, which `basisPinHit` compares against. -/
theorem basis_decls_no_proj (k : BasisKind) :
    ∀ x ∈ ConLeche.BasisKind.decls k, x.isTowerEntry = false := by
  cases k <;> decide

/-- con-leche: none — a handle whose denotation is not a table is not a
table: `Frontend.denoteCI` preserves the constructor. -/
theorem ci_ne_proj_of_denote {st : EStore} {ci : IConstantInfo}
    {c : ConstantInfo} (hd : Frontend.denoteCI st ci = some c)
    (hc : c.isTowerEntry = false) : ∀ t, ci ≠ .projInfo t := by
  intro t ht
  subst ht
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
  obtain ⟨pt, -, rfl⟩ := hd
  simp [ConstantInfo.isTowerEntry] at hc

/-! ## The recognisers -/

/-- con-leche: none — **the block's name handles denote the block's names**,
with no `.projInfo` hypothesis: the clause `denoteCI_name_of` needs at a
projection table is replaced by the *denotation's* own shape, which every
consumer below can check on con-leche's side. -/
theorem denoteCIList_names {st : EStore} :
    ∀ (cs : List IConstantInfo) (zs : List ConstantInfo),
      Frontend.denoteCIList st cs = some zs →
      (∀ x ∈ zs, x.isTowerEntry = false) →
      Frontend.denoteNList st.ns (blockNames cs) = some (zs.map (·.name)) := by
  intro cs
  induction cs with
  | nil =>
    intro zs h _
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro zs h hnt
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteCIList_cons h
    have hn := denoteCI_name_of
      (fun t ht => absurd ht (ci_ne_proj_of_denote hx (hnt x (by simp)) t)) hx
    have hih := ih xs hxs (fun y hy => hnt y (List.mem_cons_of_mem _ hy))
    simp only [ConRon.Arena.blockNames] at hih
    simp only [ConRon.Arena.blockNames, List.map_cons, Frontend.denoteNList,
      hn, hih]

/-- con-leche: none — is this name a `.num` node?  `ConstantInfo.projTableName`
always is (`(T.str "projTable").num 0`) and **no pinned basis constant is**,
which is what rules a projection table out of a block whose names match a
pin's. -/
def nameIsNum : ConLeche.Name → Bool
  | .num _ _ => true
  | _ => false

/-- con-leche: ConLeche/Kernel/Basis.lean:41-46 BasisKind.decls — no pinned
name is a `.num` node. -/
theorem basis_decls_name_not_num (k : BasisKind) :
    ∀ x ∈ ConLeche.BasisKind.decls k, nameIsNum x.name = false := by
  cases k <;> decide

/-- con-leche: ConLeche/Kernel/Env.lean:630-634 projTableName — a projection
table's name always is. -/
theorem nameIsNum_projTable (T : ConLeche.Name) :
    nameIsNum (ConLeche.projTableName T) = true := rfl

/-- con-leche: ConLeche/Kernel/Canon.lean:250-252 ConstantInfo.canon — the
canonical form renames level parameters and nothing else, so it cannot turn a
projection table into a term or back. -/
theorem canon_isTowerEntry (x : ConstantInfo) :
    (ConLeche.ConstantInfo.canon x).isTowerEntry = x.isTowerEntry := by
  cases x <;> rfl

/-- con-leche: none — **a block whose NAMES are a pin's holds no projection
table**: a table's name is a `.num` node and no pinned name is. -/
theorem noTable_of_names {b : List ConstantInfo} {k : BasisKind}
    (h : ((ConLeche.BasisKind.decls k).map (·.name) == b.map (·.name)) = true) :
    ∀ x ∈ b, x.isTowerEntry = false := by
  intro x hx
  have hm : x.name ∈ (ConLeche.BasisKind.decls k).map (·.name) := by
    rw [(by simpa using h : (ConLeche.BasisKind.decls k).map (·.name)
      = b.map (·.name))]
    exact List.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hm
  cases x with
  | projInfo t =>
    exact absurd (hyx ▸ basis_decls_name_not_num k y hy)
      (by simp [ConstantInfo.name, ConstantInfo.toConstantVal,
        nameIsNum_projTable])
  | _ => rfl

/-- con-leche: none — **a block whose CANONICAL FORMS are a pin's holds no
projection table**, for the same reason one step further back:
`ConstantInfo.canon` preserves the constructor. -/
theorem noTable_of_canon {b : List ConstantInfo} {k : BasisKind}
    (h : ConLeche.canonEqList b (ConLeche.BasisKind.decls k) = true) :
    ∀ x ∈ b, x.isTowerEntry = false := by
  intro x hx
  have hmaps : b.map ConLeche.ConstantInfo.canon
      = (ConLeche.BasisKind.decls k).map ConLeche.ConstantInfo.canon := by
    simpa [ConLeche.canonEqList] using h
  have hm : ConLeche.ConstantInfo.canon x
      ∈ (ConLeche.BasisKind.decls k).map ConLeche.ConstantInfo.canon := by
    rw [← hmaps]; exact List.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hm
  rw [← canon_isTowerEntry x, ← hyx, canon_isTowerEntry]
  exact basis_decls_no_proj k y hy

/-- con-leche: ConLeche/Kernel/Basis.lean:68-75 basisPinHit — the search, kind
by kind.  con-leche's `find?`-then-`filter` and the arena's explicit recursion
are the same answer: the first kind whose NAMES match decides, and the
canonical comparison then keeps or drops it.

**The statement takes no `.projInfo` hypothesis, and that is the round's
finding about this theorem.**  The obvious route — `denoteCI_name_of` at every
member of the incoming block — would ask for `CIProjNamed` of a STREAM record,
and that clause travels through `checkDecl_bridge_ind`, `checkDecl_bridge`,
`checkDeclStep_bridge` and the fold all the way to `Arena.model_exists`.  It
is not needed: a block that matches a pin — by names or by canonical forms —
can hold no projection table at all, because a table's name is a `.num` node
(`projTableName T = (T.str "projTable").num 0`) and no pinned name is.  So the
`.projInfo` case is DISCHARGED inside the theorem instead of hypothesised
above it. -/
theorem basisPinHitGo_run {block : List IConstantInfo} {b : List ConstantInfo} :
    ∀ (ks : List BasisKind) {r : Option BasisKind} {s s' : AState},
      StateOK s →
      Frontend.denoteCIList s.store block = some b →
      basisPinHitGo block ks s = .ok (r, s') →
      StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
        s'.pins = s.pins ∧
        r = (ks.find? fun k =>
              (ConLeche.BasisKind.decls k).map (·.name) == b.map (·.name)).filter
              fun k => ConLeche.canonEqList b (ConLeche.BasisKind.decls k) := by
  intro ks
  induction ks with
  | nil =>
    intro r s s' hok _ hrun
    simp only [ConRon.Arena.basisPinHitGo] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨hok, Ext.refl _, rfl, rfl, by simp⟩
  | cons k ks ih =>
    intro r s s' hok hb hrun
    simp only [ConRon.Arena.basisPinHitGo] at hrun
    obtain ⟨pinned, s₁, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hok1, hx1, hc1, hp1, hdp⟩ := BasisKind.decls_run hok g1
    have hb1 := denoteCIList_mono hx1 _ _ hb
    have hnA : Frontend.denoteNList s₁.store.ns (blockNames pinned)
        = some ((ConLeche.BasisKind.decls k).map (·.name)) :=
      denoteCIList_names pinned _ hdp (basis_decls_no_proj k)
    have hblock : (∀ x ∈ b, x.isTowerEntry = false) →
        Frontend.denoteNList s₁.store.ns (blockNames block)
          = some (b.map (·.name)) :=
      fun h => denoteCIList_names block _ hb1 h
    rcases AM.ite_ok k1 with ⟨hy, k2⟩ | ⟨hn, k2⟩
    · -- the handle lists agree: this kind decides, whatever con-leche's
      -- name test says
      have hbn : blockNames pinned = blockNames block := by simpa using hy
      have hsame : (∀ x ∈ b, x.isTowerEntry = false) →
          ((ConLeche.BasisKind.decls k).map (·.name) == b.map (·.name))
            = true := by
        intro hnt
        have h1 := hblock hnt
        rw [← hbn, hnA] at h1
        simpa using Option.some.inj h1
      obtain ⟨c0, s₂, g2, k3⟩ := AM.bind_ok k2
      obtain ⟨hok2, hx2, hc2, hp2, he⟩ :=
        canonEqList_run hok1
          (fun t t' _ hb' => by
            obtain ⟨y, hy1, hy2⟩ := denoteCIList_mem pinned _ hdp _ hb'
            simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hy2
            obtain ⟨pt, -, rfl⟩ := hy2
            exact absurd (basis_decls_no_proj k _ hy1)
              (by simp [ConstantInfo.isTowerEntry]))
          hb1 hdp g2
      rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        refine ⟨hok2, hx1.trans hx2, by rw [hc2, hc1], by rw [hp2, hp1], ?_⟩
        have hQ : ConLeche.canonEqList b (ConLeche.BasisKind.decls k) = true := by
          rw [← he]; simpa using hc
        have hP := hsame (noTable_of_canon hQ)
        simp [List.find?_cons, hP, Option.filter, hQ]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        refine ⟨hok2, hx1.trans hx2, by rw [hc2, hc1], by rw [hp2, hp1], ?_⟩
        have hQ : ConLeche.canonEqList b (ConLeche.BasisKind.decls k) = false := by
          rw [← he]; simpa using hc
        by_cases hPk : ((ConLeche.BasisKind.decls k).map (·.name)
            == b.map (·.name)) = true
        · simp [List.find?_cons, hPk, Option.filter, hQ]
        · -- no later kind can match either: one that did would make THIS
          -- kind's name test pass
          cases hf : (k :: ks).find? (fun k' =>
              (ConLeche.BasisKind.decls k').map (·.name) == b.map (·.name)) with
          | none => simp [hf]
          | some k' =>
            cases hQ' : ConLeche.canonEqList b (ConLeche.BasisKind.decls k') with
            | false => simp [hf, Option.filter, hQ']
            | true =>
              exact absurd (hsame (noTable_of_canon hQ')) hPk
    · -- the handle lists differ, and so do the names: on to the next kind
      have hbn : blockNames pinned ≠ blockNames block := by simpa using hn
      have hP : ((ConLeche.BasisKind.decls k).map (·.name)
          == b.map (·.name)) = false := by
        cases hpk : ((ConLeche.BasisKind.decls k).map (·.name)
            == b.map (·.name)) with
        | false => rfl
        | true =>
          refine absurd (denoteNList_inj hok1.wf _ _ _ hnA ?_) hbn
          have h1 := hblock (noTable_of_names hpk)
          rw [(by simpa using hpk : (ConLeche.BasisKind.decls k).map (·.name)
            = b.map (·.name))]
          exact h1
      obtain ⟨hok2, hx2, hc2, hp2, he⟩ := ih hok1 hb1 k2
      refine ⟨hok2, hx1.trans hx2, by rw [hc2, hc1], by rw [hp2, hp1], ?_⟩
      rw [he]
      simp [List.find?_cons, hP]

/-- con-leche: ConLeche/Kernel/Basis.lean:68-75 basisPinHit — **the
recogniser**: a stream block under a pinned name that matches the pin.  The
arena's answer is con-leche's at the denoted block.

**PROVED** (task #97-P3-Checker round 7), and at the statement round 1 wrote:
no `.projInfo` hypothesis, see `basisPinHitGo_run`.  It is what `checkDecl`'s
`.indDecl` arm needs before it may hand the block to `IndSpec`. -/
theorem basisPinHit_run {block : List IConstantInfo} {b : List ConstantInfo}
    {r : Option BasisKind} {s s' : AState} (hok : StateOK s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : basisPinHit block s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.basisPinHit b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := basisPinHitGo_run _ hok hb hrun
  exact ⟨h1, h2, h3, h4, by rw [h5]; rfl⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:77-84 quotPinHit — the quotient
package's four-record recogniser.

**PROVED** (task #97-P3-Checker round 7): `BasisKind.decls_run` for the pinned
block, `toConstantVal_sstep` at the slot `QuotKind.slot` names, and
`IConstantVal.canonEq_run`.  The `none` arm of the slot read is unreachable —
the quotient block has five members and `slot` is below five. -/
theorem quotPinHit_run {k : QuotKind} {cv : IConstantVal} {c : ConstantVal}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : quotPinHit k cv s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.quotPinHit k c := by
  simp only [ConRon.Arena.quotPinHit] at hrun
  obtain ⟨blk, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hok1, hx1, hc1, hp1, hden1⟩ := BasisKind.decls_run hok hgo
  have hnamed := BasisKind.decls_proj hok hgo
  have hlen : blk.length = (ConLeche.BasisKind.decls .quotK).length :=
    denoteCIList_length blk _ hden1
  have hslot : k.slot < blk.length := by
    rw [hlen]; cases k <;> decide
  cases hb : blk[k.slot]? with
  | none =>
    exact absurd (List.getElem?_eq_none_iff.mp hb) (by omega)
  | some ci =>
    rw [hb] at hrest
    simp only [] at hrest
    obtain ⟨pcv, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨x, hx, hdci⟩ := denoteCIList_get blk _ k.slot ci hden1 hb
    have hmem : ci ∈ blk := by
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hb
      exact he ▸ List.getElem_mem hlt
    obtain ⟨hstep2, hdpcv⟩ :=
      toConstantVal_sstep hok1 (hnamed ci hmem) hdci h2
    obtain ⟨hok3, hx3, hc3, hp3, he⟩ :=
      IConstantVal.canonEq_run hstep2.ok
        (denoteCV_ext (denoteCV_ext hcv hx1) hstep2.ext) hdpcv hrest2
    refine ⟨hok3, (hx1.trans hstep2.ext).trans hx3, ?_, ?_, ?_⟩
    · rw [hc3, hstep2.caches, hc1]
    · rw [hp3, hstep2.pins, hp1]
    · rw [he]
      have hgetD : (ConLeche.BasisKind.decls .quotK).getD k.slot
          (.axiomInfo default) = x := by
        rw [List.getD_eq_getElem?_getD, hx]; rfl
      simp only [ConLeche.quotPinHit, hgetD]

/-! ## The install -/

/-- con-leche: ConLeche/Kernel/Checker.lean:27-30 installBasisDecl — one
pinned constant, duplicate-checked.

**PROVED** (task #97-P3-Checker round 4), and **the statement gained
`hproj`** — the `.projInfo` clause round 2 §8 item 5 and round 3 §3.1 both
stopped at.  The duplicate test gives `fe.find? ci.name = none`; turning that
into con-leche's `env.find? c.name = none` through `IFEnvOK.miss` needs

    denoteN s.store.ns ci.name = some c.name

and that is `Bridge/StateOK.lean`'s `denoteCI_name_of`, whose `.projInfo` arm
takes `IProjTableOK` (`Frontend.denoteProjTable` drops `tableName`, so nothing
in the denotation ties the index's key to the recomputed name).  Six of the
seven constructors need nothing; `hproj` is what the seventh costs, and it is
the SAME hypothesis `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` already
takes at the same gap.  Free at the one call site: `checkBasisDecl` installs a
pinned block, which contains no `.projInfo` (a table never occurs in parsed
input, and the six basis blocks are `axiomInfo`/`defnInfo`/`indInfo`/
`ctorInfo`/`recInfo` only). -/
theorem installBasisDecl_bridge {μ : CheckMode} {_F : Nat} {env : Env}
    {fe fe' : IFEnv} {ci : IConstantInfo} {c : ConstantInfo} {s s' : AState}
    (hok : FoldOK μ env fe s) (hci : Frontend.denoteCI s.store ci = some c)
    (hproj : ∀ t, ci = .projInfo t → IProjTableOK s.store t)
    (hrun : installBasisDecl fe ci s = .ok (fe', s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env', denoteFEnv s'.store fe' = some env' ∧
        ConLeche.installBasisDecl (m := CheckM) env c = .ok env' := by
  simp only [Arena.installBasisDecl] at hrun
  obtain ⟨hdup, r1⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.fail_any) hrun
  replace r1 := AM.pure_bind_ok r1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
  have hfind : fe.find? ci.name = none := by
    cases hf : fe.find? ci.name with
    | none => rfl
    | some d => rw [hf] at hdup; exact absurd hdup (by simp)
  have hnm := denoteCI_name_of (fun t ht => (hproj t ht).toNamed) hci
  have hfindP : env.find? c.name = none :=
    IFEnvOK.miss hok.check.state hok.check.ienv hnm hfind
  refine ⟨hok.check.state, Ext.refl _, rfl, hok.coh.push ci, Pushed.push _ _,
    ⟨c :: env.consts⟩, denoteFEnv_push hok.denote hci, ?_⟩
  simp only [ConLeche.installBasisDecl, hfindP, Option.isNone_none, if_true,
    bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:27-30 installBasisDecl — **the
block, one constant at a time**, against con-leche's `foldlM`.

The hypotheses are the four facts `installBasisDecl_bridge` actually reads —
`StateOK`, `IFEnvOK`, `IFEnvCoh`, `denoteFEnv` — and NOT `FoldOK`: the fold
cannot carry `FoldOK`, because `EnvWF` of the extended environment would ask
for `ConstWF` of a basis constant and nothing in the install establishes one
(round 6 §1's debt, which the basis route never pays and never needs).  So
the step is `IFEnvOK.push`, `IFEnvCoh.push` and `denoteFEnv_push`, and the
`.projInfo` premise of the first is discharged by `basis_declsA_no_proj`
rather than carried. -/
theorem installBasisDecls_bridge :
    ∀ (cis : List IConstantInfo) (xs : List ConstantInfo) {env : Env}
      {fe fe' : IFEnv} {s s' : AState},
      StateOK s → IFEnvOK env fe s → IFEnvCoh fe →
      denoteFEnv s.store fe = some env →
      Frontend.denoteCIList s.store cis = some xs →
      (∀ x ∈ xs, x.isTowerEntry = false) →
      installBasisDecls fe cis s = .ok (fe', s') →
      s' = s ∧ IFEnvCoh fe' ∧ Pushed fe fe' ∧
        ∃ env', denoteFEnv s'.store fe' = some env' ∧ IFEnvOK env' fe' s' ∧
          xs.foldlM (ConLeche.installBasisDecl (m := CheckM)) env = .ok env' := by
  intro cis
  induction cis with
  | nil =>
    intro xs env fe fe' s s' hst hie hcoh hden hcs _ hrun
    simp only [Frontend.denoteCIList, Option.some.injEq] at hcs
    subst hcs
    simp only [ConRon.Arena.installBasisDecls] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, hcoh, Pushed.refl _, env, hden, hie, rfl⟩
  | cons a as ih =>
    intro xs env fe fe' s s' hst hie hcoh hden hcs hnpx hrun
    obtain ⟨x, xt, hx, hxt, rfl⟩ := denoteCIList_cons hcs
    simp only [ConRon.Arena.installBasisDecls] at hrun
    obtain ⟨fe1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    simp only [ConRon.Arena.installBasisDecl] at h1
    obtain ⟨hdup, r1⟩ := AM.dunless_ok
      (AM.Never.bind fun _ => AM.Never.fail_any) h1
    replace r1 := AM.pure_bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
    have hne := ci_ne_proj_of_denote hx (hnpx x (by simp))
    have hfind : fe.find? a.name = none := by
      cases hf : fe.find? a.name with
      | none => rfl
      | some d => rw [hf] at hdup; exact absurd hdup (by simp)
    have hnm := denoteCI_name_of (fun t ht => absurd ht (hne t)) hx
    have hfindP : env.find? x.name = none := IFEnvOK.miss hst hie hnm hfind
    obtain ⟨rfl, hcoh', hpu', env', hden', hie', hfold⟩ :=
      ih xt hst (hie.push hst hcoh hne hx) (hcoh.push a)
        (denoteFEnv_push hden hx) hxt
        (fun y hy => hnpx y (List.mem_cons_of_mem _ hy)) hrest
    refine ⟨rfl, hcoh', (Pushed.push fe a).trans hpu', env', hden', hie', ?_⟩
    simp only [List.foldlM_cons, ConLeche.installBasisDecl, hfindP,
      Option.isNone_none, if_true, bind, Except.bind, pure, Except.pure]
    exact hfold

/-- con-leche: ConLeche/Kernel/Checker.lean:427-437 checkBasisDecl —
**install the pinned basis block**, the three records that reach it sharing
one body.  `Pushed` here is the block's length, which is the one place outside
the inductive route where a step installs more than one constant.

**PROVED** (task #97-P3-Checker round 7): `BasisKind.declsA_run`, then
`installBasisDecls_bridge`, with the `.quotK` precondition (`fe.find? eqName =
some eqA`) read through `IFEnvOK.hit` at the freshly interned `ConLeche.eqA`
— `internCI_fresh` plus `pinAt_run`, and `denoteN`/`denoteCI` being functions
is what identifies the two sides. -/
theorem checkBasisDecl_bridge {μ : CheckMode} {F : Nat} {env : Env}
    {fe fe' : IFEnv} {kind : BasisKind} {s s' : AState}
    (hok : FoldOK μ env fe s)
    (hrun : checkBasisDecl fe kind s = .ok (fe', s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env', denoteFEnv s'.store fe' = some env' ∧
        ConLeche.checkBasisDecl (m := CheckM) env kind = .ok env' := by
  have tail : ∀ (s₀ : AState), StateOK s₀ → Ext s.store s₀.store →
      s₀.pins = s.pins →
      (ConRon.Arena.BasisKind.declsA kind >>= fun d =>
        ConRon.Arena.installBasisDecls fe d) s₀ = .ok (fe', s') →
      StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
        IFEnvCoh fe' ∧ Pushed fe fe' ∧
        ∃ env', denoteFEnv s'.store fe' = some env' ∧
          (ConLeche.BasisKind.declsA kind).foldlM
            (ConLeche.installBasisDecl (m := CheckM)) env = .ok env' := by
    intro s₀ hst0 hx0 hp0 hr
    obtain ⟨d, s₁, hd, hrest⟩ := AM.bind_ok hr
    obtain ⟨hok1, hx1, hc1, hp1, hden1⟩ := BasisKind.declsA_run hst0 hd
    obtain ⟨hss, hcoh', hpu', env', hden', -, hfold⟩ :=
      installBasisDecls_bridge d _ hok1
        (hok.check.ienv.mono (hx0.trans hx1)) hok.coh
        (denoteFEnv_mono (hx0.trans hx1) hok.denote) hden1
        (basis_declsA_no_proj kind) hrest
    subst hss
    exact ⟨hok1, hx0.trans hx1, by rw [hp1, hp0], hcoh', hpu', env', hden',
      hfold⟩
  simp only [ConRon.Arena.checkBasisDecl] at hrun
  rcases AM.ite_ok hrun with ⟨hq, hr1⟩ | ⟨hq, hr1⟩
  · -- the quotient block: the pinned `Eq` basis must be stored
    obtain rfl : kind = BasisKind.quotK := by simpa using hq
    obtain ⟨en, sA, g1, r1⟩ := AM.bind_ok hr1
    obtain ⟨rfl, hden⟩ :=
      pinAt_run (x := ConLeche.eqName) hok.check.pins rfl g1
    obtain ⟨a, sB, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨hstepB, hdenA, -⟩ := internCI_fresh hok.check.state g2
    obtain ⟨hfe, r3⟩ := AM.dunless_ok AM.Never.fail_any r2
    replace r3 := AM.pure_bind_ok r3
    have hfindEq : env.find? ConLeche.eqName = some ConLeche.eqA := by
      obtain ⟨nm, c0, hd1, hd2, he⟩ :=
        (hok.check.ienv.mono hstepB.ext).hit en a (by simpa using hfe)
      rw [denoteN_ext hden hstepB.ext] at hd1
      obtain rfl := Option.some.inj hd1
      rw [hdenA] at hd2
      obtain rfl := Option.some.inj hd2
      exact he
    obtain ⟨h1, h2, h3, h4, h5, env', h6, h7⟩ :=
      tail sB hstepB.ok hstepB.ext hstepB.pins r3
    refine ⟨h1, h2, h3, h4, h5, env', h6, ?_⟩
    simp only [ConLeche.checkBasisDecl, hfindEq, if_true, bind, Except.bind,
      pure, Except.pure]
    exact h7
  · -- every other block installs directly
    have hqn : kind ≠ BasisKind.quotK := by simpa using hq
    replace hr1 := AM.pure_bind_ok hr1
    obtain ⟨h1, h2, h3, h4, h5, env', h6, h7⟩ :=
      tail s hok.check.state (Ext.refl _) rfl hr1
    refine ⟨h1, h2, h3, h4, h5, env', h6, ?_⟩
    simp only [ConLeche.checkBasisDecl, if_neg hqn, bind, Except.bind,
      pure, Except.pure]
    exact h7

/-! ## The axiom shapes

`stdAxiomOk`, `trustCompilerOk` and `ofReduceAxOk` (`Arena/DeclCheck.lean`)
are the `.axiomDecl` arm's four environment tests.  Each reads the environment
index and compares an interned literal, so each is `IFEnvOK` plus one intern
exactness; none of them calls the core — which is why each concludes
`s'.caches = s.caches` (task #97-P3-Checker-2: the arm needs it to rebuild
`CheckOK` after the test). -/

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (stdAxiomOk) — the standard
axioms' environment shape test is con-leche's.

`sorry`: `IFEnvOK` at the `Iff`/`Nonempty` family lookups and
`IConstantVal.matchesPin` through `erasePwEq`.  Task #97-P3-Checker's sorry
list, item 16. -/
theorem stdAxiomOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : stdAxiomOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.stdAxiomOk env c := by
  sorry

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (trustCompilerOk) — the
`Lean.trustCompiler` environment shape test is con-leche's.

`sorry`: `IFEnvOK` at the `True`/`True.intro` lookups and
`IConstantVal.matchesPin` through `erasePwEq`, exactly as `stdAxiomOk_run`.
Task #97-P3-Checker's sorry list, item 16. -/
theorem trustCompilerOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : trustCompilerOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.trustCompilerOk env c := by
  sorry

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (ofReduceAxOk) — the
`Lean.ofReduceNat`/`ofReduceBool` environment shape test is con-leche's.

`sorry`: `ofReduceOp`'s handle comparison, then `IFEnvOK` at the pinned `Eq`
basis and at `reduceElemOk` / `reduceStoredOk`.  Task #97-P3-Checker's sorry
list, item 16. -/
theorem ofReduceAxOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : ofReduceAxOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.ofReduceAxOk env c := by
  sorry

end ConRon.Bridge

