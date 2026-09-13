/-
The build-time table generator (DESIGN.md §4, §5 P1.5, task #22).

con-leche builds two families of static tables while it *elaborates*: the
annotated basis blocks (`ConLeche.BasisKind.declsA`, computed by
`#annotate_basis` from the raw pins) and the Nat-op pin variants
(`ConLeche.natOpPinSets`, spliced from `pins/<toolchain>.json`).  The Rust
core cannot compute either — it has no elaborator and no `Array Expr`
global — so the values are *generated as Rust source* that rebuilds them
with the crate's own smart constructors.

This module is the emitter: it turns a con-leche value into a Rust function
body, interning `Name`/`Level`/`PropWhen`/`Expr` so that the term DAG stays
a DAG (one `let` per distinct node, in dependency order — the same
worklist order `ConRon/Dump/Pins.lean` emits its records in), and spelling
every node as a call to the port's smart constructor.  The refinement proof
then reads the generated Lean model (`abs` of a chain of constructor calls)
and compares it to con-leche's value; see
`proof/ConRon/Refine/BasisTables.lean`.

Nothing here is a theorem: this is a porting tool, like `ConRon/Dump/*`.
`ConRon/Gen/Main.lean` is the `con-ron-gen-tables` executable that writes
the file.
-/
import ConLeche.Kernel.BasisA

namespace ConRon.Gen

open ConLeche

/-! ## The emitter state

One interning table per id space, exactly as `ConRon/Dump/Pins.lean`'s
`WState`: `Name`, `Level`, `PropWhen` and `Expr` are interned by *value*
(that is what keeps the DAG a DAG), and the records above them are merely
numbered.  The value stored is the Rust local the node was bound to. -/
structure GSt where
  /-- The emitted body lines of the function being written, in order. -/
  out : Array String := #[]
  names : Std.HashMap Name String := {}
  levels : Std.HashMap Level String := {}
  pws : Std.HashMap PropWhen String := {}
  exprs : Std.HashMap Expr String := {}
  /-- Counters for the locals that are not interned (strings, vectors,
  records): one per prefix. -/
  fresh : Std.HashMap String Nat := {}

abbrev G := StateM GSt

/-- A literal `{` / `}`: Lean's interpolated strings have no brace escape,
and Rust struct literals are full of them. -/
def lb : String := "{"
def rb : String := "}"

/-- Emit one body line (function bodies are indented by four spaces). -/
def line (s : String) : G Unit :=
  modify fun st => { st with out := st.out.push ("    " ++ s) }

/-- A fresh local named `<pfx><n>`. -/
def freshName (pfx : String) : G String := do
  let st ← get
  let k := st.fresh.getD pfx 0
  set { st with fresh := st.fresh.insert pfx (k + 1) }
  return s!"{pfx}{k}"

/-- `let <pfx><n> = <rhs>;`, returning the local's name. -/
def bind (pfx : String) (rhs : String) : G String := do
  let v ← freshName pfx
  line s!"let {v} = {rhs};"
  return v

/-! ## Strings

A port-side string is a `Vec<u32>` of code points (DESIGN.md §3.3), built
by pushes: the Aeneas subset has no `vec!` and no loops (§3.4). -/

/-- A string rendered as a Rust end-of-line comment, when it is safe to put
one there (printable ASCII, no `*/`); otherwise nothing. -/
def strComment (s : String) : String :=
  if s.all (fun c => c.toNat ≥ 0x20 && c.toNat ≤ 0x7e && c ≠ '"' && c ≠ '\\') then
    "  // \"" ++ s ++ "\""
  else ""

/-- Emit a `Vec<u32>` holding `s`'s code points; return its local. -/
def gStr (s : String) : G String := do
  let v ← freshName "s"
  let cs := s.toList
  if cs.isEmpty then
    line s!"let {v}: Vec<u32> = Vec::new();"
  else
    line s!"let mut {v}: Vec<u32> = Vec::new();{strComment s}"
    cs.forM fun c => line s!"{v}.push({c.toNat});"
  return v

/-! ## Names, levels, the zero-ness datum -/

/-- Emit a name (and, first, its prefix); return its local. -/
partial def gName (n : Name) : G String := do
  match (← get).names[n]? with
  | some v => return v
  | none =>
    let rhs ← match n with
      | .anonymous => pure "name::anonymous()"
      | .str p s => do
        let pv ← gName p
        let sv ← gStr s
        pure s!"name::mk_str(name::dup(&{pv}), {sv})"
      | .num p k => do
        let pv ← gName p
        pure s!"name::mk_num(name::dup(&{pv}), {k})"
    let v ← bind "n" rhs
    modify fun st => { st with names := st.names.insert n v }
    return v

/-- Emit a level; return its local. -/
partial def gLevel (u : Level) : G String := do
  match (← get).levels[u]? with
  | some v => return v
  | none =>
    let rhs ← match u with
      | .zero => pure "level::zero()"
      | .succ w => do let wv ← gLevel w; pure s!"level::succ(level::dup(&{wv}))"
      | .max a b => do
        let av ← gLevel a; let bv ← gLevel b
        pure s!"level::max(level::dup(&{av}), level::dup(&{bv}))"
      | .imax a b => do
        let av ← gLevel a; let bv ← gLevel b
        pure s!"level::imax(level::dup(&{av}), level::dup(&{bv}))"
      | .param p => do let pv ← gName p; pure s!"level::param(name::dup(&{pv}))"
    let v ← bind "u" rhs
    modify fun st => { st with levels := st.levels.insert u v }
    return v

/-- Emit a `Vec<T>` built by pushes; return its local. -/
def gVec (pfx ty : String) (elems : List String) : G String := do
  let v ← freshName pfx
  if elems.isEmpty then
    line s!"let {v}: Vec<{ty}> = Vec::new();"
  else
    line s!"let mut {v}: Vec<{ty}> = Vec::new();"
    elems.forM fun e => line s!"{v}.push({e});"
  return v

/-- A `Vec<Name>`. -/
def gNameVec (ns : List Name) : G String := do
  let vs ← ns.mapM gName
  gVec "ns" "Name" (vs.map fun v => s!"name::dup(&{v})")

/-- A `Vec<Level>`. -/
def gLevelVec (us : List Level) : G String := do
  let vs ← us.mapM gLevel
  gVec "us" "Level" (vs.map fun v => s!"level::dup(&{v})")

/-- Emit a `PropWhen` through con-leche's own two public producers
(`never` / `ifAllZero`, the only way to name a value of the sealed type);
return its local.

**Not interned**, unlike the other three node kinds: a shared `PropWhen`
local would have to be handed out with `prop_when::dup`, and that
constructor's model is the only one in the port whose totality needs the
whole canonicalisation machinery (`canon`/`merge`/`name_cmp`) — see the
task-#22 log.  Emitting a fresh producer call per use costs a handful of
extra `let`s per block and keeps the refinement proof to the producers
themselves.  The `pws` table is still kept, so the census still reports
how many *distinct* data a block reaches. -/
def gPw (pw : PropWhen) : G String := do
  let rhs ← match pw.toList? with
    | none => pure "prop_when::never()"
    | some ps => do
      let psv ← gNameVec ps
      pure s!"prop_when::if_all_zero({psv})"
  let v ← bind "w" rhs
  modify fun st => { st with pws := st.pws.insert pw v }
  return v

/-- A `BinderMeta`, inline.  Task #38 put the datum behind a handle, so the
port builds one through `expr::binder_meta` rather than with a struct
literal. -/
def gBinderMeta (m : BinderMeta) : G String := do
  let p ← gPw m.pw
  return s!"expr::binder_meta({p})"

/-! ## Expressions

The walk is an explicit worklist, not recursion, for the same reason
`ConRon/Dump/Pins.lean`'s is: the pin blobs reach application spines
thousands of nodes deep and a recursive emitter overflows the stack. -/

/-- The local an already-emitted node was bound to. -/
def eid (e : Expr) : G String := return (← get).exprs.getD e "UNEMITTED"

/-- An unbounded `Nat` literal: `from_u64` when it fits in a word, else the
limb vector `norm` normalises (`ron::Nat` is little-endian base 2^64,
DESIGN.md §3.3). -/
partial def gNatLimbs (n : Nat) (acc : List Nat) : List Nat :=
  if n == 0 then acc.reverse else gNatLimbs (n / 2 ^ 64) (n % 2 ^ 64 :: acc)

def gNat (n : Nat) : G String := do
  if n < 2 ^ 64 then
    return s!"nat::from_u64({n})"
  else
    let limbs := gNatLimbs n []
    let v ← gVec "lm" "u64" (limbs.map fun l => s!"{l}")
    return s!"nat::norm({v})"

/-- Emit one node, all of whose `Expr` children are already emitted. -/
def gEmitExpr (e : Expr) : G Unit := do
  let rhs ← match e with
    | .bvar i => pure s!"expr::mk_bvar({i})"
    | .fvar idx ty => do
      let t ← eid ty
      pure s!"expr::fvar({idx}, expr::dup(&{t}))"
    | .sort u => do let uv ← gLevel u; pure s!"expr::sort(level::dup(&{uv}))"
    | .const n us => do
      let nv ← gName n
      let usv ← gLevelVec us
      pure s!"expr::mk_const(name::dup(&{nv}), {usv})"
    | .app f a => do
      let fv ← eid f; let av ← eid a
      pure s!"expr::app(expr::dup(&{fv}), expr::dup(&{av}))"
    | .lam ty b m => do
      let tv ← eid ty; let bv ← eid b; let mv ← gBinderMeta m
      pure s!"expr::lam(expr::dup(&{tv}), expr::dup(&{bv}), {mv})"
    | .forallE ty b m => do
      let tv ← eid ty; let bv ← eid b; let mv ← gBinderMeta m
      pure s!"expr::forall_e(expr::dup(&{tv}), expr::dup(&{bv}), {mv})"
    | .letE ty val b => do
      let tv ← eid ty; let vv ← eid val; let bv ← eid b
      pure s!"expr::let_e(expr::dup(&{tv}), expr::dup(&{vv}), expr::dup(&{bv}))"
    | .lit (.natVal k) => do
      let kv ← gNat k
      pure s!"expr::lit(expr::literal_nat({kv}))"
    | .lit (.strVal s) => do
      let sv ← gStr s
      pure s!"expr::lit(expr::literal_str({sv}))"
    | .proj sn i s => do
      let nv ← gName sn; let sv ← eid s
      pure s!"expr::proj(name::dup(&{nv}), {i}, expr::dup(&{sv}))"
  let v ← bind "e" rhs
  modify fun st => { st with exprs := st.exprs.insert e v }

/-- `(e, false)` means "visit", `(e, true)` means "children done, emit". -/
partial def gExprGo (stack : Array (Expr × Bool)) : G Unit := do
  if h : 0 < stack.size then
    let (e, done) := stack[stack.size - 1]'(by omega)
    let stack := stack.pop
    if (← get).exprs.contains e then
      gExprGo stack
    else if done then
      gEmitExpr e
      gExprGo stack
    else
      let stack := stack.push (e, true)
      let stack := match e with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => stack
        | .fvar _ ty => stack.push (ty, false)
        | .app f a => (stack.push (f, false)).push (a, false)
        | .lam ty b _ => (stack.push (ty, false)).push (b, false)
        | .forallE ty b _ => (stack.push (ty, false)).push (b, false)
        | .letE ty v b => ((stack.push (ty, false)).push (v, false)).push (b, false)
        | .proj _ _ s => stack.push (s, false)
      gExprGo stack
  else
    return ()

/-- Emit an expression DAG; return the root's local. -/
def gExpr (e : Expr) : G String := do
  gExprGo #[(e, false)]
  eid e

/-- A `Vec<Expr>`. -/
def gExprVec (es : List Expr) : G String := do
  let vs ← es.mapM gExpr
  gVec "es" "Expr" (vs.map fun v => s!"expr::dup(&{v})")

/-! ## The records above expressions -/

def gConstantVal (cv : ConstantVal) : G String := do
  let nv ← gName cv.name
  let lps ← gNameVec cv.levelParams
  let tv ← gExpr cv.type
  bind "cv" s!"ConstantVal {lb} name: name::dup(&{nv}), level_params: {lps}, \
ty: expr::dup(&{tv}) {rb}"

def gIndCaps (c : IndCaps) : G String := do
  let ec ← gName c.etaCtor
  let sz ← gPw c.sortZ
  bind "ic" s!"IndCaps {lb} eta: {c.eta}, eta_ctor: name::dup(&{ec}), \
eta_params: {c.etaParams}, eta_fields: {c.etaFields}, unitlike: {c.unitlike}, \
unit_params: {c.unitParams}, rule_k: {c.ruleK}, sort_z: {sz} {rb}"

def gFire : RecRuleFire → G String
  | .inert => pure "RecRuleFire::Inert"
  | .plain => pure "RecRuleFire::Plain"
  | .nested us es => do
    let usv ← gLevelVec us
    let esv ← gExprVec es
    pure s!"RecRuleFire::Nested({usv}, {esv})"

def gRecRule (r : RecRule) : G String := do
  let cv ← gName r.ctor
  let fv ← gFire r.fire
  let rv ← gExpr r.rhs
  bind "rr" s!"RecRule {lb} ctor: name::dup(&{cv}), nfields: {r.nfields}, \
ctor_params: {r.ctorParams}, fire: {fv}, rhs: expr::dup(&{rv}), k: {r.k}, \
eta: {r.eta}, params_blind: {r.paramsBlind} {rb}"

def gHint : ReducibilityHint → String
  | .opaque => "ReducibilityHint::Opaque"
  | .abbrev => "ReducibilityHint::Abbrev"
  | .regular h => s!"ReducibilityHint::Regular({h})"

def gProjTable (t : ProjTable) : G String := do
  let sn ← gName t.structName
  let lps ← gNameVec t.levelParams
  let ct ← gName t.ctor
  let ss ← gLevel t.structSort
  let bs ← gExprVec t.bodies.toList
  let gs ← gLevelVec t.guards
  bind "pt" s!"ProjTable {lb} struct_name: name::dup(&{sn}), level_params: {lps}, \
num_params: {t.numParams}, ctor: name::dup(&{ct}), num_fields: {t.numFields}, \
struct_sort: level::dup(&{ss}), bodies: {bs}, guards: {gs}, off: {t.off} {rb}"

def gConstantInfo : ConstantInfo → G String
  | .axiomInfo cv => do
    let v ← gConstantVal cv
    bind "ci" s!"ConstantInfo::AxiomInfo({v})"
  | .defnInfo cv val h => do
    let v ← gConstantVal cv
    let vv ← gExpr val
    bind "ci" s!"ConstantInfo::DefnInfo({v}, expr::dup(&{vv}), {gHint h})"
  | .thmInfo cv val => do
    let v ← gConstantVal cv
    let vv ← gExpr val
    bind "ci" s!"ConstantInfo::ThmInfo({v}, expr::dup(&{vv}))"
  | .indInfo cv caps => do
    let v ← gConstantVal cv
    let cc ← gIndCaps caps
    bind "ci" s!"ConstantInfo::IndInfo({v}, {cc})"
  | .ctorInfo cv np idx => do
    let v ← gConstantVal cv
    bind "ci" s!"ConstantInfo::CtorInfo({v}, {np}, {idx})"
  | .recInfo cv np nm rs => do
    let v ← gConstantVal cv
    let rvs ← rs.mapM gRecRule
    let rsv ← gVec "rs" "RecRule" rvs
    bind "ci" s!"ConstantInfo::RecInfo({v}, {np}, {nm}, {rsv})"
  | .projInfo t => do
    let v ← gProjTable t
    bind "ci" s!"ConstantInfo::ProjInfo({v})"

/-! ## Assembling a function -/

/-- Run a body emitter and return its lines. -/
def runBody (act : G Unit) : Array String := (act.run {}).2.out

/-- A `fn <name>() -> Vec<ConstantInfo>` whose body builds `cis`, under the
doc block `doc` (its `/// con-leche:` citations included — task #33). -/
def gDeclsFn (name : String) (doc : Array String) (cis : List ConstantInfo) :
    Array String :=
  let body := runBody do
    let vs ← cis.mapM gConstantInfo
    let out ← gVec "out" "ConstantInfo" vs
    line s!"{out}"
  doc ++ #[s!"pub fn {name}() -> Vec<ConstantInfo> {lb}"] ++ body ++ #["}", ""]

end ConRon.Gen
