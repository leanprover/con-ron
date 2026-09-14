# `ConRon.Refine` — naming rule for the refinement tier

This directory holds the refinement lemmas of DESIGN.md §3.5 / plan phase P3,
stated about the *generated* model of `crates/con-ron-core` rather than about
the task-#3 spike.  `ConRon/Spike/LevelName/` stays where it is: it is task
#3/#5's recorded evidence and is never moved or edited.

## The rule

| thing | where it lives | how it is named |
|---|---|---|
| a ported Rust function `<module>::<fn>` | generated, `ConRon/Generated/Funs.lean` | `ConRon.Generated.<dir>.<module>.<fn>` |
| a ported Rust type `<module>::<Type>` | generated, `ConRon/Generated/Types.lean` | `ConRon.Generated.<module>.<Type>` |
| its refinement lemma | `ConRon/Refine/<Module>.lean` | `ConRon.Refine.<Module>.<fn>_refines` |
| the abstraction function for `<module>::<Type>` | `ConRon/Refine/Abs.lean` (P3) | `abs<Type>` |
| the well-formedness predicate for `<module>::<Type>` | `ConRon/Refine/Abs.lean` (P3) | `<Type>WF` |

`<Module>` is the Rust module name in `UpperCamelCase` (`level` → `Level`,
`prop_when` → `PropWhen`), so `ConRon.Generated.kernel.level.simplify` is refined by
`ConRon.Refine.Level.simplify_refines` in `ConRon/Refine/Level.lean`.  Helper
lemmas that are not *the* refinement of a function keep a descriptive name
(`level_zero_inv`, `str_eq_refl`, …), exactly as in the spike.

Both halves of the name come from `scripts/extract.sh`'s flags and are stable:
`-namespace ConRon.Generated` puts every generated definition in
`ConRon.Generated`, and Aeneas keeps the Rust module path as the prefix of the
definition name (`level.zero`, not `Level.zero`).  A generated name therefore
never collides with a hand-written one.

## The spike's conventions port unchanged

`ConRon/Spike/LevelName/Refine.lean` fixed three conventions (task #5); each
carries over to `ConRon.Generated` by renaming `level_name.` to
`ConRon.Generated.` and nothing else:

* **exact-result refinement on success** — `rust_f x = ok y →
  lean_f (abs x) = abs y` (since task #67 this is the `.Ok` half of the
  full-outcome statement below, and the failure half is no longer empty);
* **`NameWF` / `LevelWF` / `NodeWF` as inductive predicates whose
  constructors are the port's own smart constructors**, which is what pins the
  stored hash word and makes `abs` injective and `beq` exact;
* **`ptr_eq` is `false` in the model**, with `*_beq_refl` reflexivity lemmas
  standing in for the real program's fast path.

The types the predicates are written over are *definitionally the same shape*
in both places (`Name.mk : Arc NameNode → Name`, `NameNode.mk : U64 →
NameKind → NameNode`, the five `LevelKind` constructors), and both sit on the
same hand-written pointer model, so the statements and the proof scripts transfer
verbatim -- `Name.lean` and `Level.lean` are the spike's `Refine.lean` with
`level_name.` dropped and the four `Name` helpers qualified, and nothing
else.  (Task #12's two-lemma `Smoke.lean` was folded into `Level.lean`'s
`zero_refines` / `succ_refines` at task #17 and deleted.)

## The full-outcome convention (task #67, DESIGN.md §3's ruling of 2026-09-13)

Every refinement lemma is stated over the Rust computation's **whole**
outcome, not only its successes.  A Rust function in the checker returns
`Result (core.result.Result α CheckError × CState)`: the outer `Result` is
Aeneas's failure monad (a panic, an overflow, a failed index — *nothing* is
ever claimed about it, since every lemma's hypothesis is `f … = ok …`), and
the inner one is con-leche's `Except`.  The inner outcome is claimed exactly:

| Rust outcome | what the lemma claims about con-leche |
|---|---|
| `.Ok r` | `.ok` at `abs r`, states related, `StateWF`/`WF r` |
| `.Err (.NotImplemented _ \| .Invalid _ \| .Internal _)` | `.error` **at the same kind** — messages are never compared |
| `.Err (.Native _)` | nothing |
| Aeneas `fail`/`div` | nothing |

The vocabulary is in `Abs.lean` and `State.lean`:

* `ErrKind` — con-leche's three constructors without their messages;
  `lErrKind : ConLeche.CheckError → ErrKind`.
* `absErrKind : CheckError → Option ErrKind` — the port's error as the kind it
  stands for, `none` for the port's own `Native`.
* `ErrSim e x : Prop` — *"if the port's error has a kind, con-leche's
  `Except` `x` throws at that kind"*.  `Native` makes it vacuous, which is how
  "claims nothing" is spelled without a second definition.
* `OutP A WF o x` (pure tier, `Abs.lean`) and `Out A WF o st' x`
  (cached tier, `State.lean`) — the two halves as one `match`.
* `Core/Statements.lean`'s `RefinesE`/`RefinesB` and `Core/Arms/Shape.lean`'s
  `Sim`/`SimS` are stated with `Out`.

**Using a lemma is unchanged.**  `SimS.apply`, `Sim.apply`, `RefinesE.ok` and
`RefinesB.ok` have exactly the pre-#67 statements, so a call site that knows
its callee succeeded reads as it did.  What is new is `SimS.apply_err`,
`Sim.apply_err`, `RefinesE.err`, `RefinesB.err`.

**Proving a lemma** adds the error half of each case.  Three moves cover
almost all of it:

1. *a bind whose sub-computation threw* — `…apply_err` gives
   `ErrSim e (sub.run lst)`, and `ErrSim.bind` (or `Out.bind`) carries it
   through the rest of con-leche's `do` block.  One line per bind.
2. *an explicit `throw` arm* — the guard has already been shown to agree in
   the accept direction, so rewrite the con-leche side down to its `throw` and
   close with `ErrSim.invalid` / `.internal` / `.notImplemented`.
3. *a `Native` arm* — `ErrSim.native` (or `ErrSim.of_none`) closes it without
   naming the con-leche side at all.

`SimS.mk'` / `Sim.mk''` split a proof into its two halves where they do not
share a case analysis; where they do (the usual case), intro the outcome `o`
and case on it inside the existing structure.

**The campaign is finished** (task #67 and its continuation, 2026-09-13):
`scripts/progress.py --summary`'s campaign line reads `full-outcome 284 / 284
in scope (100 %), accept-direction left 0`.  Every `*_refines` statement in
this directory that can carry an error arm carries one, and **no port
deviation was found** in the process — all 303 mirrored `CheckError` sites of
DESIGN.md task #67 §1's census are now proved mirrored, and the 31 native ones
still claim nothing.

**A strengthening that turns out false is a port bug.**  The accept direction
could not see a Rust guard that throws where con-leche does not, or that
throws a *different kind*; the full-outcome statement can.  Fix the Rust (as
tasks #58/#61 did) and record it in DESIGN.md — do not weaken the statement.
The port's own failures are exactly the `Native` sites of the census in
DESIGN.md's task #67 section, and adding a new one is a deliberate,
documented accept-direction deviation, not a way out of a proof.

## Writing a new refinement lemma (task #71)

DESIGN.md §3's ruling of 2026-09-13: **the automation infrastructure is
landed, and the idiom is the default for new proofs only.**  Existing hand
proofs are not rewritten — not the full-outcome ones, and not the
accept-direction ones task #67's campaign had still to restate (those got
their failure halves added by hand, accept half kept verbatim; the campaign is
finished and none of the 158 was rewritten with the idiom).

### The idiom, in five lines

```lean
attribute [local grind →] ⟨use lemmas, WF lemmas — Rust equation first⟩
attribute [local grind =] ⟨arm-selection equations, abstraction reductions⟩
attribute [local grind]   ⟨the con-leche definitions to unfold⟩

theorem f_refines … (he : ExprWF e) : Spec e := by
  induction e, he using ExprWF.ind_node <;>   -- the shape step
    (intro …; rw [rust_f.eq_def] at h; rust_norm h; all_goals rust_grind)
```

The shape step is whatever destructures what the generated body matches on: an
`ExprWF.ind_node`/`LevelWF.ind_node`/`NameWF.ind_node` induction for a walk,
`obtain ⟨⟨_, k⟩⟩ := l` for a `Level` leaf (`split` inside `rust_norm` does the
`cases`), `Sim.ofRun` + `unfold` for a knot arm.  Everything after it is the
same two lines in every lemma.

### Where each piece lives

| piece | file |
|---|---|
| `register_simp_attr rust_reduce` / `rust_invert` | `SimpSets.lean` |
| `rust_norm`, `rust_grind`, `rust_pairs`, `bind_arc_deref`, the populated simp sets | `Abs.lean` |
| `RunOk`/`RunErr`, `except_bind_ok`/`except_bind_error`, `push_new_val` | `Abs.lean` |
| `ExprWF.ind_node`, `ExprWF.kids`, the nine `ExprWF.*_kids`, the `*_wf'` reorderings | `Expr.lean` |
| `LevelWF.ind_node`; the children as `LevelWF.{succ,max,imax,param}_inv`; `*_wf'`, `LeqCoreSpec.use`, `subst_use`, `simplify_use` | `Level.lean` |
| `NameWF.ind_node`, `NameWF.str_kids`/`num_kids` | `Name.lean` |
| `hit'` / `set'` (the memo probe and write-back) | `ExprOps.lean` |
| `Sim.ofRun`/`SimS.ofRun`, `run_bind_eq`/`run_pure_eq`, `Wrappers.whnf_use` | `Core/Arms/Shape.lean` |
| the six worked examples, and `rust_inv` (task #69's untuned normaliser) | `Automation/Study.lean` |

`rust_norm h` = one pre-order `simp only` on the head (`↓bind_arc_deref` and
the node projections) with `rust_reduce`, then `repeat' (first | obtain | split
| simp only [rust_invert] | rust_pairs)`; `rust_grind` = `grind (ematch := 12)
(gen := 24)`, one fixed budget for every lemma — a lemma that needs more says
so with the `[limit]` line in its diagnostics, and raising the macro's default
is the answer, not a per-lemma override.

### The three keying rules for a `use` lemma

A lemma given to `grind` with `→` takes its E-matching patterns from its
propositional hypotheses **in order**, so how a `use` lemma is stated is the
whole difference between one instance and quadratic junk.  The failure mode
when one is keyed wrong is a `grind` failure with a multi-screen diagnostic,
not a hint.

1. **The Rust equation first.**  `app_wf hf ha : expr.app f a = ok e → ExprWF
   e` fires at every pair of well-formed terms; `app_wf'`, the same lemma with
   `h : expr.app f a = ok e` first, fires on the node the inverted bind
   produced.  Every `*_wf'`, `*_use` and `Spec.use` in the table above is the
   reordered form.  `grind_pattern` cannot substitute: an `Eq` is not an
   admissible pattern.
2. **The constructor in the equation, for an optional clause.**  A `Spec`
   clause `∀ e, o = some e → …` takes its pattern from its *conclusion* and
   instantiates at every expression in sight but the right one.  State it as a
   `use` lemma keyed on the Rust equation with the constructor in it:
   `nat_op_some_use : nat_op_result c a b = ok (.Ok (some e)) → …`.
3. **Components, not pairs.**  A clause `∀ p, o = some p → NatWF p.1 ∧ …`
   instantiates at the pair and leaves `(fst, snd).1` unreduced; quantify over
   the components instead (`∀ m n, o = some (m, n) → …`).

Two more statement-shape rules, from the same six lemmas:

* **one equation per inlined fragment.**  Where con-leche writes inline what
  the Rust factors into a helper, do not quantify the continuation: state once
  that the con-leche function *is* the helper followed by the continuation
  (`natBinI … = natLitsI … >>= k`, a monad-law `rfl` per branch) and let
  `grind` chain the helper's refinement through it.
* **arm-selection equations without side conditions.**  A con-leche equation
  carrying `(h : ∀ s, r ≠ .succ s)` makes `grind` diverge (the instantiated
  side condition becomes an E-matching theorem of its own).  One
  `rfl`-level specialisation per constructor pair is the fix.
* **a `use` lemma beside every `Spec`**, and a `Spec` beside what it is the
  induction hypothesis of.  An inductive hypothesis given to `grind` as a bare
  local `∀` is E-matched on its *conclusion*, which the abstraction has
  usually already rewritten away.

### Scope

Leaves, memoised walks and knot arms — the simulation proofs whose shape the
study measured.  **Not** `HashMap.lean`/`Nat.lean` (genuinely mathematical,
`omega`/`scalar_tac` heavy), **not** `Pins*` (byte-level decoding), **not**
`Ind*` (list folds).  Untested at the largest arms (`defeq_body_i`), where
`grind`'s per-goal internalisation of a bigger context will cost more.
`Refine/AUTOMATION.md` is the study these rules come from and carries the
measurements; `Refine/Automation/Study.lean` the six worked examples.

## Refining a byte scanner (task #87)

The parser's exactness tier (`Refine/Frontend/Scan*.lean`) is outside the idiom's
scope — it is byte loops and list folds — and it is hand-proved throughout.  Six
mechanics cost an agent a build cycle each and are worth knowing before writing
the next one.

1. **The object skeleton is one induction, not thirty-five.**  con-leche inlines
   the same `{`…`}` member walk into every `scan*Loop`; the port factors it into
   `next_member`.  `Refine/Frontend/ScanObj.lean`'s `memberBody` /
   `MemberStep` / `nextMember_step` abstract it over the Close arm and the key
   dispatch, so a loop owes only its own two arms, and the side condition
   *"this loop **is** `memberBody` at its own arms"* is
   `by rw [scanXLoop.eq_def]; rfl` — really `rfl`, with no massaging.
2. **A helper `def` holding a con-leche `match` must be monomorphic.**  A slot
   that a sub-scanner fills reads
   `match scanX b v with | .err e => .err e | .ok x e => if _hj : i < e then …`.
   A helper **monomorphic in the scrutinee's and the result's type** reuses
   con-leche's own matcher constant and the `rfl` of (1) goes through; made
   polymorphic in either (`{α β : Type} (r : ScanRes β) (K : β → USize →
   ScanRes α)`), it gets a matcher of its own, two matcher constants applied
   to a *stuck* scrutinee do not reduce, `isDefEq` gives up, and the `rfl`
   fails with a sixty-line dump **whose two sides print identically**.
   Writing the `match` out inline always works.  The trap is quiet because a
   `Nat` slot (`natSlot`) has no `match` at all and is happily polymorphic, so
   the commonest slot shape gives no warning.  Measured three ways at task
   #87, after two agents had each lost twenty minutes to it.
3. **`simp only [uncurry_apply_pair] at h` before anything else** in a member
   arm — the port's `let (mem, ni, nw) := p` does not iota-reduce otherwise.
   This is task #85 §8's mechanic 2, now confirmed twice.
4. **Pass `L`/`CL`/`DI` explicitly** to the member-step lemma; leaving them to
   higher-order unification does not work.
5. **`rw [scanLineLoop]` does not work** — that loop's closing arm matches
   `(LinePayload, UInt8)` with overlapping literal patterns, so its equation
   lemmas carry side conditions.  `rw [scanLineLoop.eq_def]` is the one.  Every
   other `scan*Loop` unfolds under its plain name.
6. **A literal constant** (task #86 spelled all 68 of the scanner's keys as
   `[u8; N]`) is read by `lift (Array.to_slice S_X) = ok s`, which gives
   `s.val = S_X.val`; then `simp [global_simps]` computes the byte list and
   `rw [absBytes, hsv]; decide` identifies `absBytes s` with the Lean literal's
   `toUTF8`.  `match_lit_refines`'s "no NUL byte" side condition is
   `by rw [hsv]; decide`.
7. **`b.length` and `b.val.length` are different `omega` atoms.**  The measure
   lemmas conclude in the first and the loop measure is written in the second,
   so `have h : i.val < b.val.length := next_member_lt hres` — a type
   ascription, defeq — is needed or every recursive arm's `omega` fails; and
   because the arms sit under a `first | … | …` the error you are shown is the
   *last* alternative's unrelated one.
8. **`rfl` does not prove `key_beq .KStr .KStr = ok true`** — `Std.U64`'s
   `DecidableEq` does not whnf through `isDefEq`.  `simp [key_beq, key_code]`
   does.
9. After `cases mem with | Key k ks v => …; cases k`, the port hypothesis keeps
   its `match mem with` **unreduced**, so an arm that does not open with a
   `bind_eq_ok_iff` destructuring (an index key, which opens with an `if`)
   rewrites silently *inside* the matcher and the following inversion fails.
   `all_goals (try dsimp only at h)` right after the `cases k` is the fix.

The abstraction vocabulary is `Refine/Frontend/Abs.lean` and the bridge lemmas
between `Std.U8`/`Std.Usize` and `UInt8`/`USize` all live in
`Refine/Frontend/ScanKit.lean`, stated **port-on-the-left**
(`absPos j = skipWs (absBytes b) (absPos i)`); take `.symm` rather than adding
a mirrored duplicate.

## What is here (tasks #17, #20 and #47, P3.3)
## What is here (tasks #17, #20, #22 and #46)

| file | contents |
|---|---|
| `SimpSets.lean` | nothing but `register_simp_attr rust_reduce` / `rust_invert` (task #71); `Abs.lean` and later files populate them |
| `Abs.lean` | the plumbing `simp` set, the task-#71 normaliser (`bind_arc_deref`, `rust_pairs`, `rust_norm`, `rust_grind`, the two populated simp sets), `absString`/`absName`/`absLevel`/`absNames`/`absLevels`/`absOrdering`/`absPropWhen`/`absLiteral`/`absBinderMeta`/`absExpr`, the `*_inv` smart-constructor shapes, `StrWF`/`NameWF`/`LevelWF`/`NamesWF`/`PropWhenWF`/`LevelsWF`/`LiteralWF`/`BinderMetaWF`/`ExprWF`, `Level.ind'`/`Name.ind'`, and `RunOk`/`RunErr` |
| `Name.lean` | `absString`/`absName` injectivity, `str_eq`, `beq`, `contains`, `singleton`, and `NameWF.ind_node`/`*_kids` |
| `Level.lean` | the task-#5 development: `absLevel` injectivity, `beq`, `level_has_param`, `subst`, `is_never_zero`, `simplify`, and the `leq_core`/`rest`/`imax_rules`/`by_cases`/`leq`/`is_equiv` cascade, plus `LevelWF.ind_node` and the equation-first `*_wf'`/`*_use` forms |
| `PropWhen.lean` | `name_cmp` (through `str_compare`/`nat_compare`/`ord_then`), `merge`/`canon`, the smart constructors, `to_list`/`to_list_opt`, `is_never`/`has_params`/`holds`/`params_defined`, `inter`, `bind_z`, `beq`, and (task #20) `absPropWhen`'s injectivity and `beq`'s reflexivity |
| `Nat.lean` | `ron::nat` (task #15), plus (task #20) `cmp`/`beq` reflexivity |
| `HashMap.lean` | `ron::hashmap` (task #16) |
| `Expr.lean` | `kernel::expr` (task #20): the packed word (`pack_bits`, the `*_val` readings, `wf_data`), the ten smart constructors, the three exact accessors, `beq_recursive`, `levels_beq`, the copies, `absExpr`'s injectivity, and `beq`'s reflexivity and exactness; `ExprWF.kids`/`*_kids`/`ind_node` and the equation-first `*_wf'` forms (task #71) |
| `ExprOps.lean` | `kernel::expr_ops`'s **foundation** (tasks #21/#47): the memo facts (`get_mem`, `insert_pres`, `MemoInv` and its `empty`/`hit`/`set`), the two key types and their `KeyExact`, the four owning probes, the shared `Vec`/scalar plumbing and `Vec` copies, and `instantiate1` |
| `ExprOpsFields.lean` | the derived fields: `size_b`/`size_f`, `wscoped_b`, the `bvar_bound`/`fvar_range` spec walks and their memoized twins, the exact accessors `bvar_b`/`fvar_b`, `loose_bvars_bounded`, `has_fvar`, `abstract_range` and `lift_loose_bvars` |
| `ExprOpsSubst.lean` | the substitutions: `instantiate_list` (spec, memoized walk and `*_fast`), `take_exprs`, `abstract1`, `lower_bvars`, `instantiate1_lift` and `inst_pis_at_lift` |
| `ExprOpsSpine.lean` | the spine and the telescopes: `get_app_fn`/`get_app_args`/`mk_app_n`, `pi_result`/`pi_arity`/`result_sort`/`fvar_type_d`, `strip_pis`/`strip_lams`, the `inst_pis_at`/`inst_lams_at`/`inst_spine` cascade and its one-pass `*_f` twins, `rec_rule_plain`, `pis_to_lams`, `replace_pi_body` |
| `ExprOpsMeta.lean` | the metadata: `reset_meta`, `rename_consts`, the `level::zeroness_of`/`level::subst_pw` bridge, `levels_subst`/`instantiate_level_params`, the leaf readers (`is_lam`, `lam_pw`, `forall_pw`, `has_level_param`, `expr_ptr_beq`), `fvar_leaves`, and the `all_level_params_defined` family |

| `BasisTables.lean` | `kernel::basis_tables` (task #22): the generated basis tables are the value they were generated from |
| `HashMapWF.lean` | task #16's deferred `Eq2` generalisation, written for its first client (task #46): the bucket walks and the `Std.HashMap` bridge under a *forward*, key-restricted exactness hypothesis (`Eq2Fwd`) instead of `Eq2Spec` |
| `Env.lean` | `kernel::env` (task #46): the mode accessors, the `Vec` copies and the `*_dup` identities, `rec_rule_parsed`/`ind_caps_default`/`default_expr` (the Lean's field defaults), `proj_table_entry`, `pi_sort_tele_len`, `ind_params_ok`, the reserved names `proj_fn_name`/`proj_table_name`, `abs`'s injectivity on the well-formed records, the whole `*_beq` family exactly, the accessors, and `find`/`find_proj` |
| `FEnv.lean` | `kernel::fenv` (task #46, completed by #50): `FEnvRel`/`FEnvWF`, `mk_fenv_go`/`mk_fenv`, `find`/`find_proj`, `restrict_to`, `dup`, and `push` — `push_refines` was task #46's one `sorry` because the Aeneas model of `Vec::insert` is `List.set`; task #50 removed that call from the port (`Env.consts` is stored reversed) and proved it |
| `State.lean` | `cached::state_c` (task #46): `StateRel`/`StateWF` over the fourteen memo maps (task #61 added `StateRel.instCSize`, the `instC` entry count, and `insert_size_step`), the fresh state, `flushed`, and the memo probe/insert lemmas |
| `StateC.lean` | `cached::state_c`'s **operations** (task #52, CORE_PLAN step 5): the pure `*M` wrappers, the three level memos (`simplify_l_m`, `is_non_zero_l_m`, `is_equiv_l_m`, `is_equiv_list_l_m`), `inst_list_m` with the `instC` entry cap and `InstCSize`, the two `ienv` pointer-identity sites (`stored_ty_idx_m`/`stored_val_idx_m`), the three level-instantiated readers and their `fe.find?` probes, `subst_level_trees`, `flush_c` and `record_c_const` |
| `StateCResolve.lean` | `cached::state_c::consts_resolve_fc` (task #52): the memoized `ExprC` DAG walk of the parsed-index driver, over the call-local memo relation `MemoBOk` |
| `ExprOpsC.lean` | `cached::expr_ops_c`'s **foundation** (task #51): the module note for all four `ExprOpsC*` files, the `O(1)` field reads (`has_fvar`, `loose_bvars_bounded`), the spine readers, `rev_append_exprs`, the two extra memo probes and `leaf_mem` |
| `ExprOpsCSubst.lean` | the cached substitutions (task #51): `instantiate1`, the three-layer `instantiate1Lift` (cutoff, budgeted descent, memoised walk) and the statements of the two bulk walks `instantiateList`/`instantiateRev` |
| `ExprOpsCAbs.lean` | the cached abstractions and level substitution (task #51): `abstract1`, `abstractRange`, `instLevelParams` (the one walk whose probe sits *before* the match) and `ProjEntry.typeAtI` |
| `ExprOpsCGuards.lean` | the cached scope queries, leaf guard, telescopes and definedness (task #51): `wscopedB` proved, and the statements of `fvarLeaves`, `leafGuard`, `instSpine`, `piResidual`, `allLevelParamsDefined` |

| `CoreKBase.lean` | task #49's shared foundation (`CORE_PLAN.md` step 4): `core_types::code_points` and the `str_lit_step`/`num_lit_step` packaging of a pinned name's body, `PinnedName`/`PinnedNames`, the three paired `kernel::env` readings, and `FindAgree`/`FindWF` — the *find-agreement* projection of `FEnv.FEnvRel`/`FEnv.FEnvWF` that `core_k.rs`/`prop_read.rs` read, with the two bridge lemmas |
| `CoreKProj.lean` | the `findProj?` reading over that weaker hypothesis: `find_proj`, and `fenv::tower_slots_all_f`/`rec_slots_all_f` (which `Refine/FEnv.lean` leaves to step 4) |
| `BasisNames.lean` | `kernel::basis_names` (task #49): all 26 pinned names, `rec_of` and `reserved_basis_names` |
| `CoreKNames.lean` | `core_k.rs`'s pinned `Nat`/`Bool` names and name tables (task #49): the eighteen names, `nat_op_names`/`nat_div_mod_names`/`nat_op_wf_names`/`nat_op_deps`, `is_nat_bin_op`, and `nat_to_dec`/`proj_model_name` (`Nat.toString` on a `u64`) |
| `CoreKVec.lean` | `core_k.rs`'s `Vec`/list plumbing (task #49): `drop_exprs`/`append_exprs`/`rev_append_exprs`/`expr_singleton`, `leaf_contains`/`fvar_leaves_subset`, `get_d_expr`/`rules_find`, `pi_residual`, `subst_const0`/`subst_const_all`, `lift_fueled` and the four loop budgets |
| `CoreKLits.lean` | literal reduction (task #49): `nat_lit_to_constructor`, `raw_nat_lit`, `lit_to_ctor_if_nat`, `str_lit_to_constructor`, `succ_of`, the equation table `nat_op_equations` and **`nat_op_result`**, the arithmetic fast path |
| `CoreKSupport.lean` | the literal-support guards (task #49): the `nat_*_ok`/`*_ty_ok` stored-shape family, `nat_lit_supported`, `str_lit_supported`, and the dead `Expr.constsResolve` |
| `CoreKGuards.lean` | `core_k.rs`'s readers, shape guards and owning probes (task #49): `defn_probe`/`ctor_probe`/`ind_probe`/`rec_probe`/`lp_empty`, `is_ctor_app`, `unfoldable_head`, `head_hint`, `is_unit_like_ty`, `same_const_heads`, `pi_result_*`, `caps_never_zero`, the leaf kind tests, `pw_written`, `annot_binder_meta`, `rec_rule_k`, `fire_is_inert`, `str_expansion_fires` and the dead `beta_gate_fires` |
| `CoreKNatOps.lean` | the `Nat`-operation pinning guards (task #49): `nat_op_guard`, `nat_op_stored`/`nat_op_stored_ok`, `nat_op_ty_pinned`, `nat_op_cod`, `bool_stored_ok`, `defn_lp_empty`, `deps_all_stored` |
| `CoreKShapes.lean` | the install-time rule bits and the certificate shape conjunctions (task #49): `struct_eta_shape_ok`, `eta_ctor_shape`, `unit_shape_ok`, the dead `eta_projs*`/`eta_fab_args*`, `proj_entry_fire_ok`, the `And`-rescue slots, `fab_scope_ok`, `rec_rule_k_of`/`rec_rule_eta_of`/`rec_rule_bits`/`proj_fn_rule`, `proj_fire_shape_ok` |
| `CoreKInfer.lean` | the pure inference clauses (task #49): `infer_lit_nat`, `infer_lit_str`, `infer_fvar`, `proj_entry_type_at`, `proj_type_at_checked`, `infer_proj_at`, `annotate_proj_entry` |
| `CoreKPinned.lean` | task #49's closing file: every hypothesis the eleven parallel files import — the pinned names, `NatOpPinned`, `PinnedBasisNames`, `VecFacts`, `EnvFacts`, the four `*Spec`s — discharged from the lemmas that prove them |
| `PropRead.lean` | `kernel::prop_read` (task #49): all eleven readers of the fast prop-ness path, each against the cited Lean instantiated at `lfe.find?` |

## The inductive routes (task #57, `CORE_PLAN.md` step 7)

`kernel::inductives` — the two install routes for an inductive block (task
#25) — refined against `ConLeche/Kernel/Inductives/*.lean` and the cached
drivers of `Cached/CheckerC.lean`.  Every lemma of this group **assumes the
knot** (`Core.KnotSpec mode IndAbs.checkFuelU`, task #55) and reaches the core
only through `IndAbs`'s five operation lemmas.

| file | contents |
|---|---|
| `IndAbs.lean` | the group's foundation: `checkFuelU` (`core_k::check_fuel()` as a value) and its two identities, the record abstractions `absRecFieldKind`/`absRecFieldKinds`/`absKindss`/`absCtors`/`absLevelss`/`absInductiveShape`/`absNativeParts`/`absStructParts` and the *relation* `NativePassRel`, the `*WF` predicates for all four records (all marked "to be unified into `Abs.lean`"), and the five `sharedOpsC` operations `ops_whnf`/`ops_infer`/`ops_annotate`/`ops_defeq`/`ops_ensure_sort` |
| `IndStructParts.lean` | `kernel::inductives::struct_parts` — the structure recogniser, its three `@[csimp]` walkers and the projection-body builder |
| `IndSumParts.lean` | `kernel::inductives::sum_parts` — the block-shape record, its copies (as identities), the member split `sum_split`, and `with_sort`/`rule_prefix`/`major_idx` |
| `IndNativeParts.lean` | `kernel::inductives::native_parts` — the **generated recursor**: every generator against its cited construction, node for node |
| `IndStructInstall.lean` | `kernel::inductives::struct_install` — the binder-domain comparison, the projection table's two guards and the table itself, against the `*F` spelling |
| `IndSumInstall.lean` | `kernel::inductives::sum_install` — the direct route's shared stages, parametric in the `CapsOf` dictionary |
| `IndNativeInstall.lean` | `kernel::inductives::native_install` — the direct route's pass and tail, split at the cached driver's two flush points |
| `IndModeled.lean` | `kernel::inductives::modeled` — the modeled route: the member checks, the recursor group and the projection functions |
| `IndSpec.lean` | `IndRoutesSpec`, the one `Prop` the checker tier (task #56) consumes: the two entry points `check_native_s`/`check_ind_decl_s` against `checkNativeS`/`checkIndDeclSF` |
| `IndC.lean` | `kernel::inductives::inductives_c` — the two routes' cached drivers, i.e. the **flush policy**, `ind_routes_spec` and (task #59) the bridge `ind_routes_spec_of_p` |
| `IndIngredients.lean` | task #59: the tier's **leaf** — the ~38 ingredient `Prop`s task #57's parallel files carried as hypotheses, each discharged from the file that owns it (`CheckerBaseSpec` from `Refine/CheckerBase.lean` under the knot, `structGens` from `Refine/IndStructParts.lean`, the install modules' `*Refines` from their owners) |
| `Scalars.lean` | task #59: the `u64 → usize` index cast in one place — the two cast-value lemmas and the discharges that close `i.val ≤ Std.Usize.max` from the `Vec` a counter came from.  **No platform axiom**: where the bound cannot be discharged it is a hypothesis, because the port's guards compare the *cast* |

## The top of the tower (task #60, `CORE_PLAN.md` steps 7's top and 8)

| file | contents |
|---|---|
| `Installed.lean` | `cached::installed` — **the declaration fold**: `absPendingCheck`/`absPendingChecks`/`PendingCheckWF` (marked "to be unified into `Abs.lean`"), the two install halves and their tails, the four-way phase-A dispatch and its three pushes, `annot_decl_step`, phase B's `check_pending` family with its fresh `CState`, both index recursions, `leanCheckDecls` and **`check_decls_refines`** |
| `Main.lean` | the capstone: `check_decls_verified_refines`, `conron.model_exists` and `conron.no_proof_of_False` from `ConLeche.MainTheorem`'s `model_exists_with`/`no_proof_of_False_with` (the pins-parametric pair, task #74), the primed pair with the knot and the routes discharged, task #75's `conron.model_exists_decoded` / `no_proof_of_False_decoded` — the primed pair at pins the verified decoder returned for *any* byte slice, `hvar` closed by `PinsWF.decode_wf`, the **axiom-free headline** at `[propext, Classical.choice, Quot.sound]` — and the two `_embedded` corollaries, which are that pair's instance at the embedded text.  Each with a `#guard_msgs`-checked axiom census |

### How the tower composes, and what is still owed

Read bottom-up, `check_decls_refines` is the composition of every file above
it, and **five hypotheses survive to it** — the same five that
`Refine/Main.lean`'s general theorems carry, and no others.  Four of them are
discharged in `Refine/Main.lean` itself, so the two `conron.*_embedded`
capstones — the theorems about the binary that ships — carry **the decoded
pins `hp`, the parsed input's well-formedness `hds`, and the run `h`**.  Task
#73 discharged `hds` too, with a runtime validation pass; **task #81 withdrew
that pass** (10 GB of resident memory at Mathlib scale, 4 % of the
instructions).

**Task #85 discharged it for good, one level up.**  `Refine/Main.lean`'s
chunk-level pair (`conron.model_exists_parsed` / `no_proof_of_False_parsed`,
the statement about con-leche's whole four-step pipeline) reads the
well-formedness of its input off the port's own parser and carries no `hds`; the
fold-level capstones keep the row, because a caller who does not go through that
parser still owes it.  What took its place is `hgen`, the second row below —
which is not discharged, and is the residue the maintainer accepted.

| hypothesis | who discharges it |
|---|---|
| `hk : Core.KnotSpec mode IndAbs.checkFuelU` — the six core wrappers and bodies refine `coreKnotI` at `checkFuel` | **task #55** (`Refine/Core/Arms/*`, `Refine/Core/Knot.lean`); `Refine/Core/Statements.lean` is the statement it is proving |
| `hind : IndRoutesSpec mode` — the two inductive install routes agree on an accept | **task #59** (`IndC.ind_routes_spec_of_p`, the recogniser bridge task #57 owed); the tier is `sorry`-free since task #67 fixed `modeled.rs`'s `u64 → usize` casts.  **Discharged at the capstones** by `IndC.ind_routes_spec'` from the knot (task #67 continued)
| `hinde : IndRoutesSpecErr mode` — …and throw at the same kind on a mirrored reject, down the same branch of `nativeParts?` | **task #67 continued** (`IndC.ind_routes_spec_err'` / `ind_routes_spec_err_of_p`).  A sibling `Prop` rather than a `match` inside `IndRoutesSpec`, so that every accept-direction proof stated through the latter stayed verbatim while the two tiers landed independently.  **Discharged at the capstones** the same way
| `hvar : CheckerPins.PinsWF pins` — every node of every pin is what the port's own smart constructor built | **task #66** (`PinsWF.decode_embedded_wf`), for the embedded pins: the same by-construction argument as `hds`, since `ExprWF`'s constructors *are* the port's smart constructors.  The `pins`-parametric theorems keep it, as they must — it is a promise about an argument, and nothing about what the list *abstracts to* implies it: two pin lists can abstract to the same `List NatOpPinSet` with one carrying a stored hash word that makes `expr::beq` inexact (task #58) |
| `hds : ∀ d ∈ ds.val, DeclarationWF d` — the parsed input is well formed | **task #85** (`Frontend.parse_chunks_wf` / `Frontend.prepare_prelude_wf`), by construction: `DeclarationWF` is the task-#5 inductive invariant whose constructors *are* the port's own smart constructors, so a record the parse built satisfies it and the proof is that argument written out.  Task #73 discharged it instead with a runtime validation pass at the entry of `check_decls`; **task #81 withdrew that pass** on the maintainer's ruling — it cost 10 GB of resident memory at Mathlib scale and 4 % of the instructions — and task #84 brought the parser into the verified pipeline, where task #85 could prove it.  **Discharged at `Refine/Main.lean`'s chunk-level pair**; the four fold-level capstones keep it |
| `hgen : Frontend.ModellerWF inst g` — every declaration the modeller generates is well formed | **nobody, and that is the point.**  Task #84's seam makes the parse quantify over `in_model_rec::Modeller`, so the 6 428 lines of `crates/con-ron/src/in_model/` are neither ported nor proved and what the tower asks of them is this one line — the maintainer's ruling of 2026-09-13 (*"leave the modeller unverified if you can; rumors are that upstream can actually get rid of it"*).  Like `hvar`, it is a promise about a function argument; it is what `hds` *became*, and it disappears the day upstream drops the modeller |
A sixth, `hpins : absPins pins = ConLeche.natOpPinSets`, stood between the last
two rows until **task #74** and is **gone, not discharged**.  It said the port's
pin list is the global the pinned con-leche baked into `checkDeclStepC`; the
vendored con-leche takes the pin list as an argument of the fold (its task
#285), so the whole tower is stated at `absPins pins` and no statement anywhere
is about the pins' *value*.  `pins_closed` — the port's one `native_decide` —
existed to discharge it and went with it.

Everything else is *internal* and already discharged where it is used: task
#56's four cross-file `Spec`s in `CheckerPinned.lean`, task #49's in
`CoreKPinned.lean`, and the `FindAgree`/`FindWF` projections in
`CoreKBase.lean`.  **There are no `sorry`s left below the top**: the last of
them closed as task #67's campaign worked up the tower, and every
`#guard_msgs`-pinned `#print axioms` census from `Core/Arms/Arms.lean` to
`Main.lean` now prints con-leche's own three axioms (plus, in the two
`_embedded` capstones alone, the one `toStr` entry Aeneas spends on the
*definition* of every extracted `&str` constant).  `sorryAx` leaving `conron.model_exists` was the P3 gate, and it
is passed.

**Since task #75 that `toStr` entry is not the headline's, either.**
`conron.model_exists_decoded` / `conron.no_proof_of_False_decoded` state the
primed pair for a pin list the verified decoder returned from *some*
`Slice U8` (`hp : kernel.pins_decode.decode text = ok (.Ok pins)`, closing
`hvar` through `PinsWF.decode_wf`), so they carry the decode run and the check
run and nothing else, name no string constant, and their pinned census is
exactly `[propext, Classical.choice, Quot.sound]`.  The two `_embedded`
capstones are their instance at `core.str.Str.as_bytes PINS_TEXT`, and they
alone pay `pins_text.PINS_TEXT._native.decide.ax_1`.  What is left outside the
proof is one fact in the unverified crate: that
`con_ron::driver::pins_for_run` calls the decoder on the embedded text.

## Not yet here

`cached::core_c` (the knot's six wrappers and their bodies): `Refine/Core/`
holds `CORE_PLAN.md` step 6's statements (task #53) and its arms are task #55's.
Task #46's four files are steps 1 and 2, task #51's four `ExprOpsC*` files the
second half of step 3, task #49's twelve `CoreK*`/`BasisNames`/`PropRead` files
step 4, task #52's two `StateC*` files step 5, and task #57's ten `Ind*` files
the second half of step 7; `Refine/Checker.lean` and `Refine/DeclCheck.lean`
(step 7's first half) are task #56's.

## The knot (`Core/`, `CORE_PLAN.md` step 6)

| file | contents |
|---|---|
| `Core/Statements.lean` | the twelve statements as one proposition per fuel: `RefinesE`/`RefinesB`, `Wrappers`, `Bodies`, `KnotSpec` (Fable) |
| `Core/Knot.lean` | task #53's skeleton: `wrappers_zero`, `wrappers_succ`, `knot_induction`, the `memoEI`/`memoBI` run lemmas and the six probe lemmas |
| `Core/Arms/Shape.lean` | task #55's shared shape: `Sim`/`SimS`/`SimP`, the bridges to `RefinesE`/`RefinesB`, the six wrappers at one call site, and `knotV` (the io grade as a flag) |
| `Core/Arms/Bridge.lean` | `StateC`'s two named ingredients (`InstantiateListRefines`, `InstLevelParamsRefines`), discharged from task #54 |
| `Core/Arms/*.lean` | one file per group of `cached/core_c.rs`'s 120-function block, partitioned by which body reaches which helper: `Shared`, `Lits`, `Certs`, `Iota`, `Major`, `App`, `WhnfCore`, `Whnf`, `InferSpine`, `InferTele`, `Infer`, `InferSpineIO`, `InferIO`, `DefEqStruct`, `DefEq`, `Annotate` |
| `Core/Arms/Arms.lean` | the `Deps` discharges, `arms` and `knot_spec`, with the axiom census |

**The knot is closed** (task #61): `#print axioms knot_spec` is
`[propext, Classical.choice, Quot.sound]`, and so is every one of the six
`*_body_sim`.  Task #55 left nineteen `sorry`s across eight of these files —
four port deviations it found, `StateRel`'s missing `instC` entry-count
clause, two packaging cycles of its own fan-out and two unfinished literal
arms; task #61 fixed the Rust where the Rust was wrong, folded `InstCSize`
into `Refine/State.lean`'s `StateRel`, split `WhnfCoreDeps` by the budget and
`DefEqDeps`/`DefEqStructDeps` along the call order, and proved the rest.

## Not yet here

Everything *above* the knot: `Refine/CORE_PLAN.md` steps 7 and 8 — the
declaration fold, phase A and B, and `Refine/Main.lean`'s capstones.  Task #46's four
files are its steps 1 and 2, task #51's four `ExprOpsC*` files the second half
of its step 3, task #49's twelve `CoreK*`/`BasisNames`/`PropRead` files its
step 4, and task #52's two `StateC*` files its step 5; step 6 is the
induction.
(step 7's first half) are task #56's, and task #60's two files above are its
top and step 8.

## The parser's well-formedness tier (`Frontend/`, task #85 phase 1)

Task #84 put the parser into the verified core; this group proves **the one
thing the fold needs of it** — that every `Declaration` it produces is what the
port's own smart constructors built — and so discharges `hds`, the last input
hypothesis of `Refine/Main.lean`.  It is *not* the parser's refinement against
`ConLeche/Frontend` (that is phase 3, and `progress.py`'s parser row stays at
0 % until it lands: the row counts `_refines` lemmas and this tier writes
`_wf` ones).

The whole argument is DESIGN.md §3.5's, the same one `Refine/PinsWF.lean` uses
for the pins: `NameWF`/`LevelWF`/`PropWhenWF`/`ExprWF` are **inductives whose
constructors are the port's smart constructors**, and the parse reaches every
node it stores through exactly one of them — so each lemma is a forward walk
through a generated body applying one constructor per arm, and no proof ever
names a hash formula.

| file | contents |
|---|---|
| `Frontend/Base.lean` | the vocabulary: `MapValsWF` (a `ron::HashMap`'s values, over `HashMap.al_v`, so `ExprOps.get_mem`/`insert_pres` apply with **neither** `Eq2Spec` nor `Inv` — `ExprOps.Compat` is trivial for a key-blind predicate), `IdTableWF`, `StateDWF` (six of `export_c::StateD`'s seventeen fields), `NameRecWF`/`ExprRecWF`/`LineRecWF` (the scanner's one obligation), `ProjRecOwnerWF`, and `ModellerWF` — the residue |
| `Frontend/ScanWF.lean` | the scanner's one obligation: every `Vec<u32>` `scan_line_fwd` hands over as a *string payload* holds valid code points.  One loop invariant on `utf8_decode` — which is why `unescape` validates its bytes at the end rather than as it goes — threaded up through `scan_string` and the record scanners |
| `Frontend/Readers.lean` | the index tables (`scan_types::IdTable`), the state readers (`st_name`/`st_level`/`st_expr`/`st_names`/`st_levels`/`get_decl_d`/`parse_pw_d`), the value builders (`parse_level_rec_d`, `parse_expr_rec_d` — the ten arms where `ExprWF`'s constructors are applied — `parse_cv_d`, `parse_rule_d`), and the three table-entry steps |
| `Frontend/ProjRec.lean` | `frontend::proj_rec`: the projection-function rewrite, the second place on the parse path that *builds* a term.  The recognisers (`occurs_const_fast`, `any_*_mentions`, `find_ctor`, …) return booleans and indices and carry no clause |
| `Frontend/Ind.lean` | the inductive record's install: the block's `ConstantInfo`s, the projection-owner table, the modeller's generated records and the pushes.  `validate_ind_d` and its twenty helpers carry **no** clause — their records are indices and machine words — and neither does `block_rec_of`/`note_ind_blocks`, because a `BlockRec` goes to the modeller and nowhere else |
| `Frontend/Prepare.lean` | `frontend::prepare` and `frontend::nat_op_ground`: two passes that **permute and copy**, so they preserve well-formedness.  Their index computations (the hoist's target map, the prelude's pick plan) carry no clause |
| `Frontend/Chunks.lean` | the top: `proj_rewrite_d`, `process_line_core_d`, `apply_line`, the chunk fold, and the three headlines `parse_bytes_wf`, `parse_chunks_wf` and `builtin_prelude_e_wf` |

## The pins (`Pins*`, tasks #64, #74)

`kernel::pins_decode` — the verified reader of the embedded `con-ron-pins/1`
text (task #43) — against `ConRon.Dump.parsePins`.  (Task #64's *closed
computation*, what the embedded text decodes to, went away at task #74: the
vendored con-leche takes the pin list as an argument of the fold, so no
statement is about the pins' value.)  Eight files, because the two programs do
not have the same shape: the port walks a byte slice with an index,
the reader splits a `String` into lines and each line into space-separated
tokens.

| file | contents |
|---|---|
| `PinsDec.lean` | the **byte-level reference decoder**: `kernel::pins_decode` function for function in Lean, over a `List Nat` *suffix* with `Option` for failure and con-leche values in the tables.  It is the joint the whole proof turns on, and its module note is the map |
| `PinsAbs.lean` | `absText`/`absNatOpPinSet`/`absPins` and the `absText_toStr` bridge (task #43's, moved here), plus `bytesOf` and `absTables` |
| `PinsBytes.lean` | **(A)** the model's scalars, escape and references against `PinsDec`'s: "the model's reader at `(t, i)` is `PinsDec`'s at `bytesFrom t i`" |
| `PinsRecords.lean` | **(A)** the `N`/`L`/`W`/`E` records, one smart-constructor lemma each |
| `PinsRun.lean` | **(A)** the `S` record and the pass, where the byte index becomes `PinsDec.runRecords`' fuel; `decode_refines` is (A)'s product |
| `PinsAscii.lean` | every byte the decoder accepts is ASCII — one `Consumes` predicate and one lemma per reader, which is what makes `absText` (a UTF-8 *decode*) readable character for character without a second walk over the port |
| `PinsSplit.lean` | **(B)** `String.splitOn` at a one-character separator, the two facts the tokenizer bridge rests on, and `absText` on an ASCII text |
| `PinsRead.lean` | **(B)** `PinsDec` against `parsePins`: the line invariant and the field invariant, per reader and per record; `parsePins_of_decode` is (B)'s product |
| `Pins.lean` | the statement: `pins_decode_refines` (proved, no axiom).  Task #64's `pins_closed`, `pins_text_decodes` and `check_decls_pins_refines` are gone — task #74's parametric fold leaves nothing about the embedded text to decide |
| `PinsWF.lean` | **(C)** task #66: the well-formedness invariant `TablesWF` threaded through the record pass, the `StrWF` and `Nat.NatWF` leaves, and `decode_wf`/`decode_embedded_wf` — what discharges `hvar`.  It sits *above* `CheckerPins.lean` in the import order because `PinsWF` is defined there; when that predicate moves into `Abs.lean` this file belongs beside `PinsRun.lean` |

## Where the native-decide axiom lived, and why it is gone

**Nowhere, since task #74.**  No `native_decide` is invoked anywhere under
`proof/`.

It used to live in exactly one lemma, `ConRon.Refine.pins_closed`: that the text
`kernel::pins_text::PINS_TEXT` embeds decodes, under `ConRon.Dump.parsePins`, to
con-leche's own `ConLeche.natOpPinSets` — **one closed computation on static
data**, a fact about two committed constants and about no input the binary will
ever be given.  Task #43 measured why the Lean kernel cannot check it and none
of the three reasons is a matter of patience: the reference decoder is a
well-founded recursion and does not whnf; a 532 KB string literal expands
quadratically in the kernel (27 s for 1 KB, over 300 s for 8 KB); and the
round-trip route needs the same literal equality plus a `Std.HashMap` in the
kernel.  The maintainer's decision (task #64) was to take it by `native_decide`
**as an interim**, and spike #63 was the attempt to remove it by changing the
format.

**Task #74 removed the need instead.**  `pins_closed` existed only to discharge
`hpins : absPins pins = ConLeche.natOpPinSets`, and the vendored con-leche makes
the pin list an argument of the fold (its task #285), so no statement in the
tower is about the pins' value and there is nothing left to compute.
`pins_closed`, `pins_text_decodes`, `check_decls_pins_refines`,
`Installed.check_decls_embedded_refines` and `BasisPins.nat_op_pin_sets_refines`
are all deleted.

**One entry survives in the `_embedded` census, and it is not ours.**
`pins_text.PINS_TEXT._native.decide.ax_1`: Aeneas renders a `&str` constant as
`toStr "…"` and discharges `toStr`'s bound `s.toByteArray.size ≤ U32.max` with
its own default argument `by decide +native` (`Aeneas/Std/String.lean`, whose
own comment says it should not).  Every extracted string constant carries it,
before any proof of ours, **in the constant's definition** — so a theorem whose
statement names the binary's own decode run inherits it through the closure even
though nothing is evaluated.  It is Aeneas's to fix, and `AENEAS_FINDINGS.md`
§3.8 records it.

**The decoder refinement spends nothing at all.**  `pins_decode_refines` is a
theorem about every byte string, so nothing is ever evaluated, and its census is
con-leche's own three axioms.

**Both the general and the embedded capstones are kept** (three pairs since
task #75), and what separates them is now generality, not trust.  `Refine/Main.lean`'s
`conron.model_exists'` / `conron.no_proof_of_False'` are general in `pins` and
say nothing about its value; `conron.model_exists_embedded` /
`conron.no_proof_of_False_embedded` are the same theorems at the pin list the
binary actually folds with (`kernel::pins_decode::decode_embedded()`, what
`con_ron::driver::pins_for_run` passes by default), so they carry neither `hk`
nor `hvar`, and they carry the one `toStr` axiom above.  Between the two sit
task #75's `conron.model_exists_decoded` / `no_proof_of_False_decoded`: the
same theorems for whatever `kernel::pins_decode::decode` returned on *any*
byte slice, which is general enough to name no constant and so spends nothing
beyond con-leche's three, and of which the `_embedded` pair is the instance at
`core.str.Str.as_bytes PINS_TEXT`.  Every one of those
censuses is pinned with `#guard_msgs in #print axioms`, which is what keeps the
boundary honest.

**`hoe` is gone for good.**  Tasks #24/#56/#58 carried two `orElse`
hypotheses to the capstones (`OrElseErrorStateSound`, `OrElseErrorDeclines`,
bundled as `CheckerDecl.DivModOrElse`); task #65 deleted them by making a
thrown pin attempt the verdict, and task #67 — which put the cited recovery
back — **proves** what they assumed rather than restoring them
(`CheckerPins.check_div_mod_pin_at_err` and `State.dup_state_eq`).  The
capstones' hypothesis list is the five rows above and nothing else.

**`hvar` is discharged too, for the embedded pins (task #66).**  It used to be
what the `_embedded` corollaries still owed: they gave the pins' *value* and not
their *well formedness*, and `PinsWF` is `ExprWF` for each of the eight pinned
expressions and each certificate list.  `Refine/PinsWF.lean` closes it the way
DESIGN.md §3.5 fixed at task #5 — the `*WF` predicates are inductives whose
constructors **are** the port's smart constructors, and the decoder reaches
every `Name`, `Level`, `PropWhen` and `Expr` it installs through exactly one of
them, so one invariant `TablesWF` threaded through the record pass does it:

    TablesWF tb → record_* t i tb = ok (.Ok (tb', j)) → TablesWF tb'

with the four backward references reading a well-formed entry out of a
well-formed table and the three counted lists collecting them.  Two leaves are
not table entries and are proved on their own: `StrWF` for a `<string>` field
(through `PinsDec.unescapeFrom`, which only ever appends a code point that
passed its own `isValidChar` guard) and `Nat.NatWF` for a `<bignum>` field, the
file's one fuel induction.  `decode_wf : decode t = ok (.Ok v) → PinsWF v` is
the product, proved for **every** byte slice — nothing is evaluated, so its
census is con-leche's own three axioms, and `decode_embedded_wf` adds only the
`toStr` axiom Aeneas already spends on every extracted `&str`.  So
`conron.model_exists_embedded` / `no_proof_of_False_embedded` carry neither
`hk`, nor `hvar` — and since task #74 there is no `hpins` to carry.
