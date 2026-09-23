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

/-! ## The pin shape comparison

`Arena.erasePwEq` is con-leche's `Expr.erasePwEq` — the `@[csimp]` lockstep
twin of `matchesPin`'s `erasePw … == erasePw …` — descended on two handles.
As `Canon.lean`'s `canonExprEq_run` does for `canonExprEqFast`, the bridge
targets the lockstep twin and takes con-leche's word (`Expr.erasePwEq_eq`)
for its agreement with the rebuild.  The walk only READS the store, so its
frame is `s' = s`. -/

/-- con-leche: none — a handle comparison IS the comparison of the two
denotations, at any readback that is injective. -/
theorem beq_of_denote_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β]
    [LawfulBEq β] {d : α → Option β}
    (hinj : ∀ {i j : α} {x : β}, d i = some x → d j = some x → i = j)
    {i j : α} {x y : β} (hi : d i = some x) (hj : d j = some y) :
    (i == j) = (x == y) := by
  cases hb : (x == y) with
  | true =>
    obtain rfl := eq_of_beq hb
    exact beq_iff_eq.mpr (hinj hi hj)
  | false =>
    cases hb' : (i == j) with
    | false => rfl
    | true =>
      obtain rfl := eq_of_beq hb'
      rw [hi] at hj
      obtain rfl := Option.some.inj hj
      simp at hb

/-- con-leche: none — `if c then m else pure false` answers `c && B` when `m`
answers `B` and leaves the state alone. -/
private theorem ite_and_run {c : Bool} {m : AM Bool} {B r : Bool}
    {s s' : AState}
    (hm : ∀ {r' : Bool} {s'' : AState}, m s = .ok (r', s'') → s'' = s ∧ r' = B)
    (h : (if c = true then m else pure false) s = .ok (r, s')) :
    s' = s ∧ r = (c && B) := by
  rcases AM.ite_ok h with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨rfl, rfl⟩ := hm k; simp [hc]
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    simp only [Bool.not_eq_true] at hc
    simp [hc]

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:139-153 Expr.erasePwEq — **the
lockstep shape comparison is con-leche's**, arm for arm.  The bridge is to the
lockstep twin and not to `erasePw a = erasePw b`: con-leche proves the two
equivalent itself (`Expr.erasePwEq_eq`). -/
theorem erasePwEq_run :
    ∀ (fuel : Nat) {a b : EIdx} {x y : Expr} {r : Bool} {s s' : AState},
      StoreWF s.store → denoteE s.store a = some x →
      denoteE s.store b = some y →
      Arena.erasePwEq fuel a b s = .ok (r, s') →
      s' = s ∧ r = ConLeche.Expr.erasePwEq x y := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b x y r s s' _ _ _ hrun
    exact absurd hrun (AM.Never.fail _ _ _ _)
  | succ fuel ih =>
    intro a b x y r s s' hwf hx hy hrun
    have hwf' := hwf
    obtain ⟨rk, hrk⟩ := hwf'
    simp only [Arena.erasePwEq] at hrun
    obtain ⟨va, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hva⟩ := viewE_run g1
    obtain ⟨vb, s2, g2, k2⟩ := AM.bind_ok k1
    obtain ⟨rfl, hvb⟩ := viewE_run g2
    cases va <;> cases vb
    all_goals first
      | obtain rfl := denote_bvar_inv hwf hva hx
      | obtain ⟨xT, rfl, hxT⟩ := denote_fvar_inv hwf hva hx
      | obtain ⟨xU, rfl, hxU⟩ := denote_sort_inv hwf hva hx
      | obtain ⟨xN, xL, rfl, hxN, hxL⟩ := denote_const_inv hwf hva hx
      | obtain ⟨xF, xA, rfl, hxF, hxA⟩ := denote_app_inv hwf hva hx
      | obtain ⟨xT, xB, rfl, hxT, hxB⟩ := denote_lam_inv hwf hva hx
      | obtain ⟨xT, xB, rfl, hxT, hxB⟩ := denote_forallE_inv hwf hva hx
      | obtain ⟨xT, xW, xB, rfl, hxT, hxW, hxB⟩ := denote_letE_inv hwf hva hx
      | obtain rfl := denote_lit_inv hwf hva hx
      | obtain ⟨xN, xE, rfl, hxN, hxE⟩ := denote_proj_inv hwf hva hx
    all_goals first
      | obtain rfl := denote_bvar_inv hwf hvb hy
      | obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
      | obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
      | obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
      | obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
      | obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
      | obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
      | obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
      | obtain rfl := denote_lit_inv hwf hvb hy
      | obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
         refine ⟨rfl, ?_⟩
         simp [ConLeche.Expr.erasePwEq]
         done)
      | skip
    case fvar.fvar =>
      obtain ⟨rfl, he⟩ := ite_and_run (fun h => ih hwf hxT hyT h) k2
      exact ⟨rfl, by simp only [ConLeche.Expr.erasePwEq, he]⟩
    case sort.sort =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨rfl, by
        simp only [ConLeche.Expr.erasePwEq,
          beq_of_denote_inj (fun h1 h2 => denoteL_inj hrk.lsWF h1 h2) hxU hyU]⟩
    case const.const =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨rfl, by
        simp only [ConLeche.Expr.erasePwEq,
          beq_of_denote_inj (fun h1 h2 => denoteN_inj hrk.nsWF h1 h2) hxN hyN,
          beq_of_denote_inj (fun h1 h2 => denoteLs_inj hrk.lss h1 h2) hxL hyL]⟩
    case app.app =>
      obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨rfl, rfl⟩ := ih hwf hxF hyF g3
      obtain ⟨rfl, he⟩ := ite_and_run (fun h => ih hwf hxA hyA h) k3
      exact ⟨rfl, by simp only [ConLeche.Expr.erasePwEq, he]⟩
    case lam.lam =>
      obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨rfl, rfl⟩ := ih hwf hxT hyT g3
      obtain ⟨rfl, he⟩ := ite_and_run (fun h => ih hwf hxB hyB h) k3
      exact ⟨rfl, by simp only [ConLeche.Expr.erasePwEq, he]⟩
    case forallE.forallE =>
      obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨rfl, rfl⟩ := ih hwf hxT hyT g3
      obtain ⟨rfl, he⟩ := ite_and_run (fun h => ih hwf hxB hyB h) k3
      exact ⟨rfl, by simp only [ConLeche.Expr.erasePwEq, he]⟩
    case letE.letE =>
      obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨rfl, rfl⟩ := ih hwf hxT hyT g3
      rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
      · obtain ⟨c2, s4, g4, k5⟩ := AM.bind_ok k4
        obtain ⟨rfl, rfl⟩ := ih hwf hxW hyW g4
        obtain ⟨rfl, he⟩ := ite_and_run (fun h => ih hwf hxB hyB h) k5
        exact ⟨rfl, by simp only [ConLeche.Expr.erasePwEq, he, hc, Bool.true_and]⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        simp only [Bool.not_eq_true] at hc
        exact ⟨rfl, by simp only [ConLeche.Expr.erasePwEq, hc, Bool.false_and]⟩
    case proj.proj =>
      have hsn := beq_of_denote_inj (fun h1 h2 => denoteN_inj hrk.nsWF h1 h2) hxN hyN
      obtain ⟨rfl, he⟩ := ite_and_run (fun h => ih hwf hxE hyE h) k2
      exact ⟨rfl, by simp only [ConLeche.Expr.erasePwEq, he, hsn, Bool.and_assoc]⟩

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:197-201 ConstantVal.matchesPinFast
— **the pin comparison is con-leche's**, at the lockstep twin, and hence (by
con-leche's own `@[csimp]` equation) at `matchesPin` itself. -/
theorem matchesPin_run {cv pin : IConstantVal} {c p : ConstantVal}
    {r : Bool} {s s' : AState} (hwf : StoreWF s.store)
    (hc : Frontend.denoteCV s.store cv = some c)
    (hp : Frontend.denoteCV s.store pin = some p)
    (hrun : IConstantVal.matchesPin cv pin s = .ok (r, s')) :
    s' = s ∧ r = ConLeche.ConstantVal.matchesPin c p := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  obtain ⟨hcn, hcl, hct⟩ := denoteCV_inv hc
  obtain ⟨hpn, hpl, hpt⟩ := denoteCV_inv hp
  have e1 := beq_of_denote_inj (fun h1 h2 => denoteN_inj hrk.nsWF h1 h2) hcn hpn
  have e2 := beq_of_denote_inj
    (fun h1 h2 => denoteNList_inj hwf _ _ _ h1 h2) hcl hpl
  rw [ConLeche.ConstantVal.matchesPin_eq_matchesPinFast]
  simp only [IConstantVal.matchesPin] at hrun
  rcases AM.ite_ok hrun with ⟨hq, k⟩ | ⟨hq, k⟩
  · obtain ⟨rfl, rfl⟩ := erasePwEq_run _ hwf hct hpt k
    simp only [Bool.and_eq_true, e1, e2, beq_iff_eq] at hq
    refine ⟨rfl, ?_⟩
    simp [ConLeche.ConstantVal.matchesPinFast, hq.1, hq.2]
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    refine ⟨rfl, ?_⟩
    simp only [Bool.and_eq_true, e1, e2, beq_iff_eq, not_and] at hq
    by_cases h1 : c.name = p.name
    · simp [ConLeche.ConstantVal.matchesPinFast, h1, hq h1]
    · simp [ConLeche.ConstantVal.matchesPinFast, h1]

/-! ## The shape tests' frame

Every shape test below is a `Bool`-valued chain of pin reads, fresh-memo
interns, index lookups and `matchesPin`s, and every link of it is a
scratch-agnostic step (`Frontend.IStepS`).  `RunsB m s b` says exactly that of
a whole chain: every success of `m` at `s` is such a step and answers `b`.  The
combinators below follow the arena's `do`-blocks link by link, so each test is
its own `do`-block read top to bottom, and con-leche's `&&`-chain is the `b`. -/

/-- con-leche: none — every success of `m` at `s` is a scratch-agnostic step
answering `b`. -/
def RunsB (m : AM Bool) (s : AState) (b : Bool) : Prop :=
  ∀ (r : Bool) (s' : AState), m s = .ok (r, s') → Frontend.IStepS s s' ∧ r = b

theorem RunsB.ret {s : AState} (hok : StateOK s) {b : Bool} :
    RunsB (Pure.pure b) s b := by
  intro r s' h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h
  exact ⟨Frontend.IStepS.refl hok, rfl⟩

theorem RunsB.bind {α : Type} {m : AM α} {k : α → AM Bool} {s : AState}
    {b : Bool}
    (h : ∀ {a : α} {s₁ : AState}, m s = .ok (a, s₁) →
      Frontend.IStepS s s₁ ∧ RunsB (k a) s₁ b) :
    RunsB (m >>= k) s b := by
  intro r s' hr
  obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok hr
  obtain ⟨hs1, hk⟩ := h h1
  obtain ⟨hs2, rfl⟩ := hk _ _ h2
  exact ⟨hs1.trans hs2, rfl⟩

/-- a `Bool` answered by a step, then bound. -/
theorem RunsB.bindB {m : AM Bool} {k : Bool → AM Bool} {s : AState}
    {A b : Bool}
    (hm : RunsB m s A)
    (hk : ∀ {s₁ : AState}, Frontend.IStepS s s₁ → RunsB (k A) s₁ b) :
    RunsB (m >>= k) s b :=
  RunsB.bind fun h1 => by
    obtain ⟨hs, rfl⟩ := hm _ _ h1
    exact ⟨hs, hk hs⟩

theorem RunsB.ite {c c' : Prop} [Decidable c] [Decidable c'] {X Y : AM Bool}
    {s : AState} {b1 b2 : Bool} (hc : c ↔ c')
    (h1 : c → RunsB X s b1) (h2 : ¬ c → RunsB Y s b2) :
    RunsB (if c then X else Y) s (if c' then b1 else b2) := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact h1 h
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact h2 h

/-- con-leche: none — a known view, read. -/
theorem view_run_of_some {h : EIdx} {s : AState} {v : ENodeView}
    (hv : s.store.view h = some v) : view h s = .ok (v, s) := by
  simp only [view, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.bind, Except.pure, hv]

/-- con-leche: none — **the tag-first twin's test** (task #97-P5-Core round 4):
`if h.tag == t then (view h >>= f) else e` runs as `view h >>= f` at a handle
whose view is known, because on the `else` side the continuation's catch-all
arm IS `e`. -/
theorem RunsB.tagView {h : EIdx} {t : UInt32} {v : ENodeView}
    {f : ENodeView → AM Bool} {e : AM Bool} {s : AState} {b : Bool}
    (hv : s.store.view h = some v) (he : v.tagOf ≠ t → f v = e)
    (hk : RunsB (view h >>= f) s b) :
    RunsB (if h.tag == t then (view h >>= f) else e) s b := by
  by_cases ht : (h.tag == t) = true
  · rw [if_pos ht]; exact hk
  · rw [if_neg ht]
    have hne : v.tagOf ≠ t := by rw [← EStore.tagOf_of_view hv]; simpa using ht
    intro r s' hrun
    apply hk r s'
    have hb : (view h >>= f) s = f v s := by
      show StateT.bind (view h) f s = _
      simp only [StateT.bind, view_run_of_some hv]; rfl
    rw [hb, he hne]; exact hrun

/-- a guard: `if c then pure false else Y` is `D && B` when `c` is `!D`. -/
theorem RunsB.guard {c D B : Bool} {Y : AM Bool} {s : AState}
    (hok : StateOK s) (hc : c = !D) (hY : D = true → RunsB Y s B) :
    RunsB (if c then pure false else Y) s (D && B) := by
  cases D with
  | false =>
    subst hc
    simp only [Bool.not_false, if_true, Bool.false_and]
    exact RunsB.ret hok
  | true =>
    subst hc
    simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
    exact hY rfl

/-- con-leche: none — the index answers what the environment answers, as one
disjunction a `match` on both sides can be read off. -/
def FindRel (st : EStore) (x : Option IConstantInfo) (y : Option ConstantInfo) :
    Prop :=
  (x = none ∧ y = none) ∨
    ∃ ci c, x = some ci ∧ y = some c ∧ Frontend.denoteCI st ci = some c

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `IFEnvOK`'s two halves at
one handle. -/
theorem IFEnvOK.findRel {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) :
    FindRel s.store (fe.find? n) (env.find? nm) := by
  cases hf : fe.find? n with
  | none => exact Or.inl ⟨rfl, h.miss hok hd hf⟩
  | some ci =>
    obtain ⟨nm', c, h1, h2, h3⟩ := h.hit n ci hf
    rw [hd] at h1
    obtain rfl := Option.some.inj h1
    exact Or.inr ⟨ci, c, rfl, h3, h2⟩

/-- con-leche: none — `FindRel` survives an extension of the store. -/
theorem FindRel.mono {st st' : EStore} {x : Option IConstantInfo}
    {y : Option ConstantInfo} (h : FindRel st x y) (hx : Ext st st') :
    FindRel st' x y := by
  rcases h with h | ⟨ci, c, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨ci, c, h1, h2, denoteCI_ext h3 hx⟩

theorem RunsB.matchInd {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.indInfo cvI _) => K cvI | _ => pure false) s
      ((match (generalizing := false) y with | some (.indInfo cvI _) => L cvI | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci with
    | indInfo v cap =>
      obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      exact hK v v' hv
    | axiomInfo v =>
      obtain ⟨v', rfl, -⟩ := denoteCI_axiom_inv hd; exact RunsB.ret hok
    | ctorInfo v nP nF =>
      obtain ⟨v', rfl, -⟩ := denoteCI_ctor_inv hd; exact RunsB.ret hok
    | defnInfo v e hh =>
      obtain ⟨v', x, rfl, -⟩ := denoteCI_defn_inv hd; exact RunsB.ret hok
    | thmInfo v e =>
      obtain ⟨v', x, rfl, -⟩ := denoteCI_thm_inv hd; exact RunsB.ret hok
    | recInfo v mI rP rs =>
      obtain ⟨v', x, rfl, -⟩ := denoteCI_rec_inv hd; exact RunsB.ret hok
    | projInfo t =>
      obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd; exact RunsB.ret hok

/-- The index lookups of the shape tests, one per constructor pattern. -/
theorem RunsB.matchAxiom {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.axiomInfo cv) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.axiomInfo cv) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
      | obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip

theorem RunsB.matchCtor0 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.ctorInfo cv 0 0) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.ctorInfo cv 0 0) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
      | obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i nP nF
      rcases nP with _ | nP <;> rcases nF with _ | nF <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchCtor1 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.ctorInfo cv 1 1) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.ctorInfo cv 1 1) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
      | obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i nP nF
      rcases nP with _ | _ | nP <;> rcases nF with _ | _ | nF <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchCtor2 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.ctorInfo cv 2 2) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.ctorInfo cv 2 2) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
      | obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i nP nF
      rcases nP with _ | _ | _ | nP <;> rcases nF with _ | _ | _ | nF <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchRec3 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.recInfo cv 3 3 _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.recInfo cv 3 3 _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
      | obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i mI rP rs
      rcases mI with _ | _ | _ | _ | mI <;> rcases rP with _ | _ | _ | _ | rP <;>
        first | exact RunsB.ret hok | exact hK _ _ hv

theorem RunsB.matchRec4 {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.recInfo cv 4 4 _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.recInfo cv 4 4 _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
      | obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip
    all_goals
      rename_i mI rP rs
      rcases mI with _ | _ | _ | _ | _ | mI <;> rcases rP with _ | _ | _ | _ | _ | rP <;>
        first | exact RunsB.ret hok | exact hK _ _ hv


/-- A stored constant compared against a freshly interned `ConstantVal` pin,
then continued. -/
theorem RunsB.pinCV {P : ConstantVal} {v : IConstantVal} {v' : ConstantVal}
    {k : Bool → AM Bool} {s : AState} {b : Bool} (hst : StateOK s)
    (hv : Frontend.denoteCV s.store v = some v')
    (hk : ∀ {s₁ : AState}, Frontend.IStepS s s₁ →
      RunsB (k (ConLeche.ConstantVal.matchesPin v' P)) s₁ b) :
    RunsB (internCV P >>= fun p => IConstantVal.matchesPin v p >>= k) s b := by
  refine RunsB.bind fun {p s₁} g1 => ?_
  obtain ⟨hs1, hp⟩ := internCV_fresh hst g1
  refine ⟨hs1, RunsB.bindB (fun _ _ h => ?_) fun hs3 => hk (hs1.trans hs3)⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs1.ok.wf (denoteCV_ext hv hs1.ext) hp h
  exact ⟨Frontend.IStepS.refl hs1.ok, rfl⟩

/-- The same, as the last link of a chain. -/
theorem RunsB.pinCVLast {P : ConstantVal} {v : IConstantVal} {v' : ConstantVal}
    {s : AState} (hst : StateOK s)
    (hv : Frontend.denoteCV s.store v = some v') :
    RunsB (internCV P >>= fun p => IConstantVal.matchesPin v p) s
      (ConLeche.ConstantVal.matchesPin v' P) := by
  refine RunsB.bind fun {p s₁} g1 => ?_
  obtain ⟨hs1, hp⟩ := internCV_fresh hst g1
  refine ⟨hs1, fun _ _ h => ?_⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs1.ok.wf (denoteCV_ext hv hs1.ext) hp h
  exact ⟨Frontend.IStepS.refl hs1.ok, rfl⟩

/-- A stored constant compared against the common data of a freshly interned
`ConstantInfo` pin, then continued. -/
theorem RunsB.pinCI {P : ConstantInfo} {v : IConstantVal} {v' : ConstantVal}
    {k : Bool → AM Bool} {s : AState} {b : Bool} (hst : StateOK s)
    (hv : Frontend.denoteCV s.store v = some v')
    (hk : ∀ {s₁ : AState}, Frontend.IStepS s s₁ →
      RunsB (k (ConLeche.ConstantVal.matchesPin v' P.toConstantVal)) s₁ b) :
    RunsB (internCI P >>= fun a => IConstantInfo.toConstantVal a >>= fun p =>
      IConstantVal.matchesPin v p >>= k) s b := by
  refine RunsB.bind fun {a s₁} g1 => ?_
  obtain ⟨hs1, ha, hna⟩ := internCI_fresh hst g1
  refine ⟨hs1, RunsB.bind fun {p s₂} g2 => ?_⟩
  obtain ⟨hs2, hp⟩ := toConstantVal_sstep hs1.ok hna ha g2
  refine ⟨hs2, RunsB.bindB (fun _ _ h => ?_) fun hs3 => hk ((hs1.trans hs2).trans hs3)⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs2.ok.wf
    (denoteCV_ext hv (hs1.ext.trans hs2.ext)) hp h
  exact ⟨Frontend.IStepS.refl hs2.ok, rfl⟩

/-- A pinned name read off the table, then continued. -/
theorem RunsB.pin {i : Nat} {x : ConLeche.Name} {k : NIdx → AM Bool}
    {s : AState} {b : Bool} (hst : StateOK s) (hp : PinsOK s)
    (hx : pinNames[i]? = some x)
    (hk : ∀ n, denoteN s.store.ns n = some x → RunsB (k n) s b) :
    RunsB (pinAt i >>= k) s b := by
  refine RunsB.bind fun {n s₁} g1 => ?_
  obtain ⟨rfl, d1⟩ := pinAt_run hp hx g1
  exact ⟨Frontend.IStepS.refl hst, hk n d1⟩

/-- con-leche: none — `Frontend.denoteCV` is injective. -/
theorem denoteCV_inj {st : EStore} (hwf : StoreWF st) {v w : IConstantVal}
    {c : ConstantVal} (hv : Frontend.denoteCV st v = some c)
    (hw : Frontend.denoteCV st w = some c) : v = w := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  obtain ⟨h1, h2, h3⟩ := denoteCV_inv hv
  obtain ⟨g1, g2, g3⟩ := denoteCV_inv hw
  cases v; cases w
  simp only at h1 h2 h3 g1 g2 g3
  rw [denoteN_inj hrk.nsWF h1 g1, denoteNList_inj hwf _ _ _ h2 g2,
    denoteE_inj hwf h3 g3]

/-- con-leche: none — `Frontend.denoteCI` is injective at an inductive (it is
NOT injective at a projection table, whose `tableName` it drops). -/
theorem denoteCI_inj_ind {st : EStore} (hwf : StoreWF st) {ci ci' : IConstantInfo}
    {cv : ConstantVal} {d : IndCaps}
    (h : Frontend.denoteCI st ci = some (.indInfo cv d))
    (h' : Frontend.denoteCI st ci' = some (.indInfo cv d)) : ci = ci' := by
  have hwf' := hwf
  obtain ⟨rk, hrk⟩ := hwf'
  have key : ∀ {x : IConstantInfo}, Frontend.denoteCI st x = some (.indInfo cv d) →
      ∃ v cap, x = .indInfo v cap ∧ Frontend.denoteCV st v = some cv ∧
        Frontend.denoteCaps st cap = some d := by
    intro x hx
    cases x with
    | indInfo v cap =>
      obtain ⟨cv', d', he, hv, hc⟩ := denoteCI_ind_inv hx
      cases he
      exact ⟨v, cap, rfl, hv, hc⟩
    | axiomInfo v => obtain ⟨_, he, _⟩ := denoteCI_axiom_inv hx; cases he
    | ctorInfo v _ _ => obtain ⟨_, he, _⟩ := denoteCI_ctor_inv hx; cases he
    | defnInfo v _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_defn_inv hx; cases he
    | thmInfo v _ => obtain ⟨_, _, he, _⟩ := denoteCI_thm_inv hx; cases he
    | recInfo v _ _ _ => obtain ⟨_, _, he, _⟩ := denoteCI_rec_inv hx; cases he
    | projInfo t => obtain ⟨_, he, _⟩ := denoteCI_proj_inv hx; cases he
  obtain ⟨v, cap, rfl, hv, hc⟩ := key h
  obtain ⟨w, cap', rfl, hw, hc'⟩ := key h'
  obtain rfl := denoteCV_inj hwf hv hw
  congr 1
  simp only [Frontend.denoteCaps] at hc hc'
  cases he : denoteN st.ns cap.etaCtor with
  | none => rw [he] at hc; simp at hc
  | some ct =>
    cases he' : denoteN st.ns cap'.etaCtor with
    | none => rw [he'] at hc'; simp at hc'
    | some ct' =>
      rw [he] at hc; rw [he'] at hc'
      rw [← hc'] at hc
      simp only [Option.some.injEq, IndCaps.mk.injEq] at hc
      obtain ⟨e1, rfl, e3, e4, e5, e6, e7, e8⟩ := hc
      have := denoteN_inj hrk.nsWF he he'
      cases cap; cases cap'
      simp_all

/-- con-leche: none — the index's equality test against a pinned inductive
IS con-leche's `env.find? nm = some P`. -/
theorem IFEnvOK.find_beq_ind {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) {a : IConstantInfo}
    {cv : ConstantVal} {d : IndCaps}
    (ha : Frontend.denoteCI s.store a = some (.indInfo cv d)) :
    (fe.find? n == some a) = decide (env.find? nm = some (.indInfo cv d)) := by
  rcases h.findRel hok hd with ⟨h1, h2⟩ | ⟨ci, c, h1, h2, h3⟩
  · rw [h1, h2]; simp
  · rw [h1, h2]
    by_cases hc : ci = a
    · subst hc
      rw [h3] at ha
      simp [Option.some.inj ha]
    · have : c ≠ .indInfo cv d := by
        rintro rfl
        exact hc (denoteCI_inj_ind hok.wf h3 ha)
      simp [hc, this]

/-- A stored constant compared against a pin some step computes, as the last
link of a chain. -/
theorem RunsB.pinLastOf {m : AM IConstantVal} {P : ConstantVal}
    {v : IConstantVal} {v' : ConstantVal} {s : AState}
    (hv : Frontend.denoteCV s.store v = some v')
    (hm : ∀ {p : IConstantVal} {s₁ : AState}, m s = .ok (p, s₁) →
      Frontend.IStepS s s₁ ∧ Frontend.denoteCV s₁.store p = some P) :
    RunsB (m >>= fun p => IConstantVal.matchesPin v p) s
      (ConLeche.ConstantVal.matchesPin v' P) := by
  refine RunsB.bind fun {p s₁} g1 => ?_
  obtain ⟨hs1, hp⟩ := hm g1
  refine ⟨hs1, fun _ _ h => ?_⟩
  obtain ⟨rfl, rfl⟩ := matchesPin_run hs1.ok.wf (denoteCV_ext hv hs1.ext) hp h
  exact ⟨Frontend.IStepS.refl hs1.ok, rfl⟩

theorem RunsB.and_true {m : AM Bool} {s : AState} {b : Bool}
    (h : RunsB m s (b && true)) : RunsB m s b := by
  rwa [Bool.and_true] at h

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:75-77 ofReduceOp — the reduce
operation an `ofReduce*` axiom speaks about, a handle comparison here. -/
theorem ofReduceOp_run {n c : NIdx} {nm : ConLeche.Name} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hd : denoteN s.store.ns n = some nm)
    (hrun : Arena.ofReduceOp n s = .ok (c, s')) :
    s' = s ∧ denoteN s.store.ns c = some (ConLeche.ofReduceOp nm) := by
  simp only [Arena.ofReduceOp] at hrun
  obtain ⟨orn, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.ofReduceNatName) hp (by rfl) g1
  have hiff := beq_handle_iff hst.wf hd d1
  rcases AM.ite_ok r1 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.reduceNatName) hp (by rfl) k
    refine ⟨rfl, ?_⟩
    rw [d2, ConLeche.ofReduceOp, if_pos (hiff.mp hc)]
  · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.reduceBoolName) hp (by rfl) k
    refine ⟨rfl, ?_⟩
    rw [d2, ConLeche.ofReduceOp, if_neg (fun h => hc (hiff.mpr h))]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:148-150 reduceOpCvA — the
annotated pinned type of a reduce operation, interned. -/
theorem reduceOpCvA_run {cH : NIdx} {cn : ConLeche.Name} {v : IConstantVal}
    {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hd : denoteN s.store.ns cH = some cn)
    (hrun : Arena.reduceOpCvA cH s = .ok (v, s')) :
    Frontend.IStepS s s' ∧
      Frontend.denoteCV s'.store v = some (ConLeche.reduceOpCvA cn) := by
  simp only [Arena.reduceOpCvA] at hrun
  obtain ⟨rn, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.reduceNatName) hp (by rfl) g1
  have hiff := beq_handle_iff hst.wf hd d1
  rcases AM.ite_ok r1 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.reduceOpCvA, if_pos (hiff.mp hc)]
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.reduceOpCvA, if_neg (fun h => hc (hiff.mpr h))]

/-- The RAW pin an `ofReduce*` axiom is matched against — what the twin's
`ofReducePinA` interns (`Arena/TrustAxioms.lean`: task #97-P5-Top round 2,
ruling (a)).  con-leche's `ofReducePinA` is the annotated one. -/
def ofReducePinRaw (n : ConLeche.Name) : ConstantVal :=
  if n = ConLeche.ofReduceNatName then ConLeche.ofReduceRaw ConLeche.ofReduceNatName
  else ConLeche.ofReduceRaw ConLeche.ofReduceBoolName

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:152-154 ofReducePinA — the
pin an `ofReduce*` axiom is matched against, interned: the RAW one
(`ofReducePinRaw`), since task #97-P5-Top round 2's ruling (a);
`ofReducePinA_matchesPin_raw` is why the verdict is con-leche's. -/
theorem ofReducePinA_run {nH : NIdx} {nm : ConLeche.Name} {v : IConstantVal}
    {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hd : denoteN s.store.ns nH = some nm)
    (hrun : Arena.ofReducePinA nH s = .ok (v, s')) :
    Frontend.IStepS s s' ∧
      Frontend.denoteCV s'.store v = some (ofReducePinRaw nm) := by
  simp only [Arena.ofReducePinA] at hrun
  obtain ⟨rn, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.ofReduceNatName) hp (by rfl) g1
  have hiff := beq_handle_iff hst.wf hd d1
  rcases AM.ite_ok r1 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ofReducePinRaw, if_pos (hiff.mp hc)]
  · obtain ⟨hs, hv⟩ := internCV_fresh hst k
    refine ⟨hs, ?_⟩
    rw [hv, ofReducePinRaw, if_neg (fun h => hc (hiff.mpr h))]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:179-186 reduceElemOk — the
element inductive's shape test is con-leche's. -/
theorem reduceElemOk_run {env : Env} {fe : IFEnv} {cH : NIdx}
    {cn : ConLeche.Name} {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env fe s) (hd : denoteN s.store.ns cH = some cn) :
    RunsB (Arena.reduceElemOk fe cH) s (ConLeche.reduceElemOk env cn) := by
  unfold Arena.reduceElemOk ConLeche.reduceElemOk
  refine RunsB.pin hst hp (x := ConLeche.reduceNatName) (by rfl) fun rn drn => ?_
  refine RunsB.ite (beq_handle_iff hst.wf hd drn) (fun _ => ?_) (fun _ => ?_)
  · refine RunsB.pin hst hp (x := ConLeche.natName) (by rfl) fun nn dnn => ?_
    refine RunsB.bind fun {na s1} g1 => ?_
    obtain ⟨hs1, hna, -⟩ := internCI_fresh hst g1
    obtain ⟨cvN, dN, hN⟩ : ∃ cv d, ConLeche.natA = .indInfo cv d := ⟨_, _, rfl⟩
    rw [hN] at hna ⊢
    refine ⟨hs1, ?_⟩
    rw [← (hie.mono hs1.ext).find_beq_ind hs1.ok (denoteN_ext dnn hs1.ext) hna]
    exact RunsB.ret hs1.ok
  · refine RunsB.pin hst hp (x := ConLeche.boolName) (by rfl) fun bn dbn => ?_
    refine RunsB.and_true
      (RunsB.matchInd hst (hie.findRel hst dbn) fun v v' hv => ?_)
    rw [Bool.and_true]
    exact RunsB.pinCVLast hst hv

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:171-177 reduceStoredOk — the
stored reduce operation's shape test is con-leche's. -/
theorem reduceStoredOk_run {env : Env} {fe : IFEnv} {cH : NIdx}
    {cn : ConLeche.Name} {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env fe s) (hd : denoteN s.store.ns cH = some cn) :
    RunsB (Arena.reduceStoredOk fe cH) s (ConLeche.reduceStoredOk env cn) := by
  unfold Arena.reduceStoredOk ConLeche.reduceStoredOk
  refine RunsB.and_true
    (RunsB.matchAxiom hst (hie.findRel hst hd) fun v v' hv => ?_)
  rw [Bool.and_true]
  exact RunsB.pinLastOf hv fun h => reduceOpCvA_run hst hp hd h

theorem RunsB.matchDefn {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    {K : IConstantVal → AM Bool} {L : ConstantVal → Bool} {R : Bool}
    (hK : ∀ v v', Frontend.denoteCV s.store v = some v' →
      RunsB (K v) s (L v' && R)) :
    RunsB (match (generalizing := false) x with | some (.defnInfo cv _ _) => K cv | _ => pure false) s
      ((match (generalizing := false) y with | some (.defnInfo cv _ _) => L cv | _ => false) && R) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · cases ci
    all_goals first
      | obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_axiom_inv hd
      | obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_defn_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_thm_inv hd
      | obtain ⟨v', x, rfl, hv, -⟩ := denoteCI_rec_inv hd
      | obtain ⟨T, rfl, -⟩ := denoteCI_proj_inv hd
    all_goals first
      | exact RunsB.ret hok
      | exact hK _ _ hv
      | skip

/-- The dual guard: `if c then Y else pure false` is `D && B` when `c` is
`D`. -/
theorem RunsB.guardT {c D B : Bool} {Y : AM Bool} {s : AState}
    (hok : StateOK s) (hc : c = D) (hY : D = true → RunsB Y s B) :
    RunsB (if c then Y else pure false) s (D && B) := by
  subst hc
  cases c with
  | false =>
    simp only [Bool.false_eq_true, if_false, Bool.false_and]
    exact RunsB.ret hok
  | true =>
    simp only [if_true, Bool.true_and]
    exact hY rfl

/-- A stored constant's level parameters, read through
`IConstantInfo.toConstantVal` (whose `.projInfo` arm interns, so the stored
table must be rightly named). -/
theorem RunsB.matchLps {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    (hpn : ∀ ci, x = some ci → Frontend.CIProjNamed s.store ci) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv ← ci.toConstantVal
          pure cv.levelParams.isEmpty
        | none => pure false) s
      (match (generalizing := false) y with
        | some ci => ci.toConstantVal.levelParams.isEmpty
        | none => false) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (hpn ci rfl) hd g1
    refine ⟨hs1, ?_⟩
    obtain ⟨-, hl, -⟩ := denoteCV_inv hv
    have hlen := denoteNList_length _ _ hl
    have he : v.levelParams.isEmpty = c.toConstantVal.levelParams.isEmpty := by
      cases h1 : v.levelParams <;> cases h2 : c.toConstantVal.levelParams <;>
        simp_all
    rw [he]
    exact RunsB.ret hs1.ok

/-- `RunsB.matchLps` where the `do`-elaborator has pushed the continuation
into both arms as a join point (`let okT ← match …; rest`). -/
theorem RunsB.matchLpsJP {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    (hpn : ∀ ci, x = some ci → Frontend.CIProjNamed s.store ci)
    {jp : Bool → AM Bool} {B : Bool}
    (hjp : ∀ {s₁ : AState}, Frontend.IStepS s s₁ →
      RunsB (jp (match (generalizing := false) y with
        | some ci => ci.toConstantVal.levelParams.isEmpty
        | none => false)) s₁ B) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv ← ci.toConstantVal
          let y ← pure cv.levelParams.isEmpty
          jp y
        | none => do
          let y ← pure false
          jp y) s B := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · refine RunsB.bind fun {b s₁} g1 => ?_
    obtain ⟨rfl, rfl⟩ := AM.pure_ok g1
    exact ⟨Frontend.IStepS.refl hok, hjp (Frontend.IStepS.refl hok)⟩
  · refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (hpn ci rfl) hd g1
    refine ⟨hs1, RunsB.bind fun {b s₂} g2 => ?_⟩
    obtain ⟨rfl, rfl⟩ := AM.pure_ok g2
    refine ⟨Frontend.IStepS.refl hs1.ok, ?_⟩
    obtain ⟨-, hl, -⟩ := denoteCV_inv hv
    have hlen := denoteNList_length _ _ hl
    have he : v.levelParams.isEmpty = c.toConstantVal.levelParams.isEmpty := by
      cases h1 : v.levelParams <;> cases h2 : c.toConstantVal.levelParams <;>
        simp_all
    rw [he]
    exact hjp hs1

/-- `natOpCod`'s `Bool` lookup: the stored `Bool`'s level parameters and type,
read through `IConstantInfo.toConstantVal`, against the pinned `Sort 1`. -/
theorem RunsB.matchCod {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hp : PinsOK s) (hxy : FindRel s.store x y)
    (hpn : ∀ ci, x = some ci → Frontend.CIProjNamed s.store ci) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv ← ci.toConstantVal
          let s1 ← sortOne
          pure (cv.levelParams.isEmpty && cv.type == s1)
        | none => pure false) s
      (match (generalizing := false) y with
        | some ci => ci.toConstantVal.levelParams.isEmpty &&
            ci.toConstantVal.type == .sort (.succ .zero)
        | none => false) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (hpn ci rfl) hd g1
    refine ⟨hs1, RunsB.bind fun {e s₂} g2 => ?_⟩
    obtain ⟨rfl, he⟩ := AM.of_run (P := fun t => t = s₁)
      (Q := fun r t => t = s₁ ∧ denoteE s₁.store r = some (.sort (.succ .zero)))
      rfl g2 (pinSortOne_spec s₁ (hp.mono hs1.ext hs1.pins))
    refine ⟨Frontend.IStepS.refl hs1.ok, ?_⟩
    obtain ⟨-, hl, hty⟩ := denoteCV_inv hv
    have hlen := denoteNList_length _ _ hl
    have h1 : v.levelParams.isEmpty = c.toConstantVal.levelParams.isEmpty := by
      cases h1 : v.levelParams <;> cases h2 : c.toConstantVal.levelParams <;>
        simp_all
    have h2 : (v.type == e) = (c.toConstantVal.type == .sort (.succ .zero)) :=
      beq_of_denote_inj (fun h1 h2 => denoteE_inj hs1.ok.wf h1 h2) hty he
    rw [h1, h2]
    exact RunsB.ret hs1.ok

/-- con-leche: none — a pin read leaves the state alone, at any slot. -/
theorem pinAt_state {i : Nat} {n : NIdx} {s s' : AState} (hp : PinsOK s)
    (hr : pinAt i s = .ok (n, s')) : s' = s :=
  (AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ ∀ y, pinNames[i]? = some y →
      denoteN s.store.ns r = some y) rfl hr (pinAt_spec s i hp)).1

/-! ## The axiom shapes

`stdAxiomOk`, `trustCompilerOk` and `ofReduceAxOk` (`Arena/DeclCheck.lean`)
are the `.axiomDecl` arm's four environment tests.  Each reads the environment
index and compares an interned literal, so each is `IFEnvOK` plus one intern
exactness; none of them calls the core — which is why each concludes
`s'.caches = s.caches` (task #97-P3-Checker-2: the arm needs it to rebuild
`CheckOK` after the test). -/

/-! ### The raw pins are con-leche's annotated ones, to `matchesPin`

Task #97-P5-Top round 2, ruling (a): the twin interns and compares the RAW
standard-axiom and `ofReduce*` pins, as the port does, where con-leche compares
against the annotated ones.  Annotation writes only the binders' `pw` datum,
and `matchesPin` compares types up to `erasePw`, so each pair gives the same
verdict — by `rfl` on the erased types (the old campaign's
`Refine/StdAxioms.lean` / `Refine/TrustAxioms.lean` facts, restated here
because `Bridge` does not import `Refine`). -/

/-- Two pins that agree on name, level parameters and `erasePw` of the type are
the same pin as far as `ConstantVal.matchesPin` can tell. -/
theorem matchesPin_congr {p q : ConstantVal} (hn : p.name = q.name)
    (hl : p.levelParams = q.levelParams) (ht : p.type.erasePw = q.type.erasePw)
    (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv p = ConLeche.ConstantVal.matchesPin cv q := by
  simp [ConLeche.ConstantVal.matchesPin, hn, hl, ht]

theorem iffA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.iffA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.iffRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
theorem iffIntroA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.iffIntroA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.iffIntroRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
theorem iffRecA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.iffRecA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.iffRecRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
theorem nonemptyA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
theorem nonemptyIntroA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyIntroA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyIntroRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
theorem nonemptyRecA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyRecA.toConstantVal
      = ConLeche.ConstantVal.matchesPin cv ConLeche.nonemptyRecRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
theorem propextA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.propextA
      = ConLeche.ConstantVal.matchesPin cv ConLeche.propextRaw :=
  matchesPin_congr rfl rfl rfl cv
theorem choiceA_matchesPin_raw (cv : ConstantVal) :
    ConLeche.ConstantVal.matchesPin cv ConLeche.choiceA
      = ConLeche.ConstantVal.matchesPin cv ConLeche.choiceRaw :=
  matchesPin_congr rfl rfl rfl cv

/-- `ofReducePinA` and its raw twin (`ConLeche/Kernel/TrustAxioms.lean:143-146`,
the `#annotate_pins` command): the three binders' `pw` differ, `erasePw`
erases exactly that. -/
theorem ofReducePinA_matchesPin_raw (cv : ConstantVal) (n : ConLeche.Name) :
    ConLeche.ConstantVal.matchesPin cv (ConLeche.ofReducePinA n)
      = ConLeche.ConstantVal.matchesPin cv (ofReducePinRaw n) := by
  rw [ConLeche.ofReducePinA, ofReducePinRaw]
  split
  · exact matchesPin_congr rfl rfl rfl cv
  · exact matchesPin_congr rfl rfl rfl cv

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (stdAxiomOk) — the standard
axioms' environment shape test is con-leche's.

**PROVED** (task #97-P3-Checker round 8): the `do`-block read link by link
through the `RunsB` combinators — `pinAt_run` per pinned name, `IFEnvOK.findRel`
per index lookup, `matchesPin_run` (hence `erasePwEq_run`) per shape
comparison, and `IFEnvOK.find_beq_ind` for the `Eq` basis test. -/
theorem stdAxiomOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : stdAxiomOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.stdAxiomOk env c := by
  have hst := hok.check.state
  suffices h : RunsB (stdAxiomOk fe cvA) s (ConLeche.stdAxiomOk env c) by
    obtain ⟨hs, rfl⟩ := h _ _ hrun
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have tr : ∀ {t : AState}, Frontend.IStepS s t →
      StateOK t ∧ PinsOK t ∧ IFEnvOK env fe t ∧
        Frontend.denoteCV t.store cvA = some c := fun ht =>
    ⟨ht.ok, hok.check.pins.mono ht.ext ht.pins, hok.check.ienv.mono ht.ext,
      denoteCV_ext hcv ht.ext⟩
  have hnm := (denoteCV_inv hcv).1
  simp only [ConLeche.stdAxiomOk, Bool.and_assoc, iffA_matchesPin_raw,
    iffIntroA_matchesPin_raw, iffRecA_matchesPin_raw, nonemptyA_matchesPin_raw,
    nonemptyIntroA_matchesPin_raw, nonemptyRecA_matchesPin_raw,
    propextA_matchesPin_raw, choiceA_matchesPin_raw]
  unfold Arena.stdAxiomOk
  obtain ⟨hst0, hp0, hie0, -⟩ := tr (Frontend.IStepS.refl hst)
  refine RunsB.pin hst hp0 (x := ConLeche.propextName) (by rfl) fun pn dpn => ?_
  refine RunsB.pin hst hp0 (x := ConLeche.choiceName) (by rfl) fun cn dcn => ?_
  refine RunsB.ite (beq_handle_iff hst.wf hnm dpn) (fun _ => ?_) (fun _ => ?_)
  · -- `propext`, over the pinned `Eq` basis and the `Iff` family
    refine RunsB.pin hst hp0 (x := ConLeche.eqName) (by rfl) fun en den => ?_
    refine RunsB.bind fun {ea s1} g1 => ?_
    obtain ⟨hs1, hea, -⟩ := internCI_fresh hst g1
    refine ⟨hs1, ?_⟩
    obtain ⟨st1, hp1, hie1, -⟩ := tr hs1
    obtain ⟨cvE, dE, hE⟩ : ∃ cv d, ConLeche.eqA = .indInfo cv d := ⟨_, _, rfl⟩
    rw [hE] at hea ⊢
    refine RunsB.guard st1 (by
      simp only [bne, hie1.find_beq_ind st1 (denoteN_ext den hs1.ext) hea]) fun _ => ?_
    refine RunsB.pin st1 hp1 (x := ConLeche.iffName) (by rfl) fun n2 d2 => ?_
    refine RunsB.matchInd st1 (hie1.findRel st1 d2) fun v v' hv => ?_
    refine RunsB.pinCI st1 hv fun {s3} hs3 => ?_
    obtain ⟨st3, hp3, hie3, -⟩ := tr (hs1.trans hs3)
    refine RunsB.guard st3 (by simp) fun _ => ?_
    refine RunsB.pin st3 hp3 (x := ConLeche.iffIntroName) (by rfl) fun n4 d4 => ?_
    refine RunsB.matchCtor2 st3 (hie3.findRel st3 d4) fun w w' hw => ?_
    refine RunsB.pinCI st3 hw fun {s5} hs5 => ?_
    obtain ⟨st5, hp5, hie5, -⟩ := tr ((hs1.trans hs3).trans hs5)
    refine RunsB.guard st5 (by simp) fun _ => ?_
    refine RunsB.pin st5 hp5 (x := ConLeche.iffRecName) (by rfl) fun n6 d6 => ?_
    refine RunsB.matchRec4 st5 (hie5.findRel st5 d6) fun u u' hu => ?_
    refine RunsB.pinCI st5 hu fun {s7} hs7 => ?_
    obtain ⟨st7, -, -, hcv7⟩ := tr (((hs1.trans hs3).trans hs5).trans hs7)
    refine RunsB.guard st7 (by simp) fun _ => ?_
    exact RunsB.pinCVLast st7 hcv7
  · refine RunsB.ite (beq_handle_iff hst.wf hnm dcn) (fun _ => ?_)
      (fun _ => RunsB.ret hst)
    -- `Classical.choice`, over the `Nonempty` family
    refine RunsB.pin hst hp0 (x := ConLeche.nonemptyName) (by rfl) fun n2 d2 => ?_
    refine RunsB.matchInd hst (hie0.findRel hst d2) fun v v' hv => ?_
    refine RunsB.pinCI hst hv fun {s3} hs3 => ?_
    obtain ⟨st3, hp3, hie3, -⟩ := tr hs3
    refine RunsB.guard st3 (by simp) fun _ => ?_
    refine RunsB.pin st3 hp3 (x := ConLeche.nonemptyIntroName) (by rfl) fun n4 d4 => ?_
    refine RunsB.matchCtor1 st3 (hie3.findRel st3 d4) fun w w' hw => ?_
    refine RunsB.pinCI st3 hw fun {s5} hs5 => ?_
    obtain ⟨st5, hp5, hie5, -⟩ := tr (hs3.trans hs5)
    refine RunsB.guard st5 (by simp) fun _ => ?_
    refine RunsB.pin st5 hp5 (x := ConLeche.nonemptyRecName) (by rfl) fun n6 d6 => ?_
    refine RunsB.matchRec3 st5 (hie5.findRel st5 d6) fun u u' hu => ?_
    refine RunsB.pinCI st5 hu fun {s7} hs7 => ?_
    obtain ⟨st7, -, -, hcv7⟩ := tr ((hs3.trans hs5).trans hs7)
    refine RunsB.guard st7 (by simp) fun _ => ?_
    exact RunsB.pinCVLast st7 hcv7

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (trustCompilerOk) — the
`Lean.trustCompiler` environment shape test is con-leche's.

**PROVED** (task #97-P3-Checker round 8): exactly as `stdAxiomOk_run`. -/
theorem trustCompilerOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : trustCompilerOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.trustCompilerOk env c := by
  have hst := hok.check.state
  suffices h : RunsB (trustCompilerOk fe cvA) s (ConLeche.trustCompilerOk env c) by
    obtain ⟨hs, rfl⟩ := h _ _ hrun
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have hie := hok.check.ienv
  simp only [ConLeche.trustCompilerOk, Bool.and_assoc]
  unfold Arena.trustCompilerOk
  refine RunsB.pin hst hok.check.pins (x := ConLeche.trueName) (by rfl) fun n1 d1 => ?_
  refine RunsB.matchInd hst (hie.findRel hst d1) fun v v' hv => ?_
  refine RunsB.pinCV hst hv fun {s2} hs2 => ?_
  refine RunsB.guard hs2.ok (by simp) fun _ => ?_
  refine RunsB.pin hs2.ok (hok.check.pins.mono hs2.ext hs2.pins) (x := ConLeche.trueIntroName)
    (by rfl) fun n2 d2 => ?_
  refine RunsB.matchCtor0 hs2.ok ((hie.mono hs2.ext).findRel hs2.ok d2)
    fun w w' hw => ?_
  refine RunsB.pinCV hs2.ok hw fun {s3} hs3 => ?_
  refine RunsB.guard hs3.ok (by simp) fun _ => ?_
  exact RunsB.pinCVLast hs3.ok (denoteCV_ext hcv (hs2.ext.trans hs3.ext))

/-- con-leche: ConLeche/Kernel/DeclCheck.lean (ofReduceAxOk) — the
`Lean.ofReduceNat`/`ofReduceBool` environment shape test is con-leche's.

**PROVED** (task #97-P3-Checker round 8): `ofReduceOp_run`, the `Eq` basis
test, then `reduceElemOk_run` / `reduceStoredOk_run` and the pinned type. -/
theorem ofReduceAxOk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cvA : IConstantVal} {c : ConstantVal} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cvA = some c)
    (hrun : ofReduceAxOk fe cvA s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      r = ConLeche.ofReduceAxOk env c := by
  have hst := hok.check.state
  suffices h : RunsB (ofReduceAxOk fe cvA) s (ConLeche.ofReduceAxOk env c) by
    obtain ⟨hs, rfl⟩ := h _ _ hrun
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have tr : ∀ {t : AState}, Frontend.IStepS s t →
      StateOK t ∧ PinsOK t ∧ IFEnvOK env fe t ∧
        Frontend.denoteCV t.store cvA = some c := fun ht =>
    ⟨ht.ok, hok.check.pins.mono ht.ext ht.pins, hok.check.ienv.mono ht.ext,
      denoteCV_ext hcv ht.ext⟩
  have hnm := (denoteCV_inv hcv).1
  simp only [ConLeche.ofReduceAxOk, Bool.and_assoc, ofReducePinA_matchesPin_raw]
  unfold Arena.ofReduceAxOk
  obtain ⟨-, hp0, -, -⟩ := tr (Frontend.IStepS.refl hst)
  refine RunsB.bind fun {cH s0} g0 => ?_
  obtain ⟨rfl, dc⟩ := ofReduceOp_run hst hp0 hnm g0
  refine ⟨Frontend.IStepS.refl hst, ?_⟩
  refine RunsB.pin hst hp0 (x := ConLeche.eqName) (by rfl) fun en den => ?_
  refine RunsB.bind fun {ea s1} g1 => ?_
  obtain ⟨hs1, hea, -⟩ := internCI_fresh hst g1
  refine ⟨hs1, ?_⟩
  obtain ⟨st1, hp1, hie1, -⟩ := tr hs1
  obtain ⟨cvE, dE, hE⟩ : ∃ cv d, ConLeche.eqA = .indInfo cv d := ⟨_, _, rfl⟩
  rw [hE] at hea ⊢
  refine RunsB.guard st1 (by
    simp only [bne, hie1.find_beq_ind st1 (denoteN_ext den hs1.ext) hea]) fun _ => ?_
  refine RunsB.bindB (reduceElemOk_run st1 hp1 hie1 (denoteN_ext dc hs1.ext))
    fun {s2} hs2 => ?_
  obtain ⟨st2, hp2, hie2, -⟩ := tr (hs1.trans hs2)
  refine RunsB.guard st2 (by simp) fun _ => ?_
  refine RunsB.bindB
    (reduceStoredOk_run st2 hp2 hie2 (denoteN_ext dc (hs1.trans hs2).ext))
    fun {s3} hs3 => ?_
  obtain ⟨st3, hp3, -, hcv3⟩ := tr ((hs1.trans hs2).trans hs3)
  refine RunsB.guard st3 (by simp) fun _ => ?_
  exact RunsB.pinLastOf hcv3 fun h =>
    ofReducePinA_run st3 hp3 (denoteCV_inv hcv3).1 h

end ConRon.Bridge

