/-
`kernel::basis_pins` and `kernel::nat_op_pins` (task #56, `CORE_PLAN.md`
step 7).

## What is here

`ConLeche/Kernel/BasisA.lean` is the *annotated* basis, computed while the
module elaborates by `#annotate_basis`.  The port cannot run an elaborator, so
the value is carried as generated Rust source
(`kernel::basis_tables`, task #22) and `Refine/BasisTables.lean` proves that
the generated table **is** `ConLeche.BasisKind.declsA` — which is the only
thing this file needs about it.

Seventeen of the nineteen annotated pins are consumed through
`ConstantVal.matchesPin`, whose type test erases every binder's prop-ness
datum, so the port compares them against the *raw* pins and no table is
involved (task #24's `matchesPin` note).  The remaining two are consumed by an
**exact** `ConstantInfo` equality — `env.find? eqName = some eqA`
(`Kernel/StdAxioms.lean:346`, `Kernel/DeclCheck.lean:243,299,313,744`, …) and
`env.find? natName = some natA` (`Kernel/TrustAxioms.lean:180`,
`Kernel/DeclCheck.lean:290`) — and `kernel/basis_pins.rs` is exactly that
consumer layer: the two pins read off the head of their block, the two
predicates, and the two environment guards.

So the refinement of the six functions is the composition of three facts that
already exist:

* `Refine/BasisTables.lean`'s `basis_decls_a_refines` — the table is
  `BasisKind.declsA`, hence `(declsA .eqK)[0] = eqA` and
  `(declsA .natK)[0] = natA`, which is what `eq_a`/`nat_a` read;
* `Refine/Env.lean`'s `constant_info_beq_refines` — the port's derived
  `ConstantInfo` equality is `decide (· = ·)` on the abstracted constants
  (task #27 checked that the derived structural one is what every kernel site
  spells; `ConstantInfo.canonEq` is the frontend's and never the kernel's);
* `Refine/FEnv.lean`'s `find_refines` — the index probe is `FEnv.find?`.

**The stubs task #24 described are gone.**  That entry says `basis_pins.rs`
answers `false` / the empty block and that task #22 should delete the module.
At the current pin they are *not* stubs: task #27 deleted `basis_pins::decls_a`
(`BasisKind.declsA` is `basis_tables::basis_decls_a`, folded by
`checker::check_basis_decl`) and rewrote the two predicates against the
generated table, and `crates/con-ron-core/tests/basis_install.rs` installs all
six blocks end to end.  What is refined below is therefore the real consumer
layer, not a decline.

## `kernel::nat_op_pins`

Task #24's other stub is also gone, and in a way that moves the statement out
of this file.  `nat_op_pins.rs` declares the `NatOpPinSet` record **and
nothing else** — there is no `nat_op_pin_sets()`: task #31 made the variant
list a *parameter* (Charon OOMs on ~26 500 generated nodes) and task #43 then
embedded it as text in the core, `kernel::pins_text::PINS_TEXT` plus the
verified reader `kernel::pins_decode::decode`.  The record's abstraction
(`absNatOpPinSet`) and the decoder's refinement therefore live in
`Refine/Pins.lean`, and nothing about a table is owed here.

`Refine/Pins.lean`'s `pins_text_decodes` — the closed computation
`parsePins (absText PINS_TEXT) = .ok ConLeche.natOpPinSets` — is open, and
task #43 *measured* why (a `native_decide` axiom already inside Aeneas's `Str`
model, a reference decoder that does not whnf, and quadratic kernel expansion
of a 532 KB literal).  The honest statement here is the one about the
**decoded list**, and it is proved below from that statement and
`pins_decode_refines`: `nat_op_pin_sets_refines`.  It is what `Refine/Pins.lean`
wrote down as `check_decls_pins_refines` and left `sorry`, and it should be
folded back there when that file is next touched.

`sorry` count in this file: 1.
-/
import ConRon.Refine.BasisTables
import ConRon.Refine.BasisNames
import ConRon.Refine.FEnv
import ConRon.Refine.Pins

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel
open ConRon.Refine ConRon.Refine.FEnv

namespace ConRon.Refine.BasisPins

/-! ## The one thing task #22 did not prove about its table

`Refine/BasisTables.lean` proves the table's *value* and deliberately forgets
the hash words (`⦃ _ => True ⦄` on every `mix_hash`), because an equation
between abstractions needs nothing else.  The exact `ConstantInfo` comparison
does need more: `Refine/Env.lean`'s `constant_info_beq_refines` is exact only
on well-formed constants, `ConstantInfoWF` being the inductive-predicate
invariant that pins the stored word.  The table's entries satisfy it — every
node of the generated source is a call to the port's own smart constructor —
but that is a second walk over the same 192 interned nodes, with the `*_inv`
shapes instead of the value specification. -/

/-- The generated basis table's entries are well formed.

`sorry`: needs `Refine/BasisTables.lean`'s `step` tier re-run with a
`⦃ r => abs… ∧ …WF r ⦄` specification per smart constructor instead of the
value-only one — 192 interned nodes, no new idea. -/
theorem basis_decls_a_wf {k : env.BasisKind}
    {v : alloc.vec.Vec env.ConstantInfo}
    (h : basis_tables.basis_decls_a k = ok v) : ConstantInfosWF v := by
  sorry

/-! ## The two pins -/

/-- `Vec::index` at a literal position, as a `getElem?` fact.  (The copy in
`Refine/ExprOps.lean` is `vec_index_getElem?`; that file is not imported
here.) -/
theorem vec_index_get? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- The head of a basis block: `basis_decls_a k` succeeds, and its first entry
abstracts to the head of `BasisKind.declsA (absBasisKind k)` and is well
formed.  This is the shared body of `eq_a_refines`/`nat_a_refines` — the pins
are read off the table rather than spelled a second time, so the install order
`declsA` fixes is what makes them the right constants. -/
theorem block_head {k : env.BasisKind} {block : alloc.vec.Vec env.ConstantInfo}
    {ci : env.ConstantInfo} (hb : basis_tables.basis_decls_a k = ok block)
    (hi : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice env.ConstantInfo)
      block 0#usize = ok ci) :
    (ConLeche.BasisKind.declsA (absBasisKind k))[0]? = some (absConstantInfo ci) ∧
      ConstantInfoWF ci := by
  obtain ⟨v, hv, habs⟩ := WP.spec_imp_exists (basis_decls_a_refines k)
  rw [hb] at hv
  have hvb : v = block := (Result.ok_injective hv).symm
  subst hvb
  have hg : v.val[0]? = some ci := vec_index_get? hi
  refine ⟨?_, basis_decls_a_wf hb ci (List.mem_of_getElem? hg)⟩
  rw [← habs]
  simp only [absConstantInfos, List.getElem?_map, hg, Option.map_some]

/-- `ConLeche/Kernel/BasisA.lean:29-48` — `basis_pins::eq_a` is `eqA`, the
pinned annotated `Eq` type former: the head of the `.eqK` block
(`BasisKind.declsA .eqK = [eqA, eqReflA, eqRecA]`).  `eqA = eqRaw` is a *fact*
and not an assumption (`crates/.../basis_pins.rs`'s note and its
`eq_a_is_annotated` test); nothing below needs it. -/
theorem eq_a_refines {ci : env.ConstantInfo} (h : basis_pins.eq_a = ok ci) :
    absConstantInfo ci = ConLeche.eqA ∧ ConstantInfoWF ci := by
  rw [basis_pins.eq_a] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨block, hb, ci0, hi, hdup⟩ := h
  have hb' : basis_tables.basis_decls_a env.BasisKind.EqK = ok block := hb
  obtain ⟨hhead, hwf⟩ := block_head hb' hi
  rw [Env.constant_info_dup_refines hdup]
  refine ⟨?_, hwf⟩
  simp only [absBasisKind, ConLeche.BasisKind.declsA] at hhead
  exact (Option.some_inj.mp hhead).symm

/-- `ConLeche/Kernel/BasisA.lean:29-48` — `basis_pins::nat_a` is `natA`, the
head of the `.natK` block
(`BasisKind.declsA .natK = [natA, natZeroA, natSuccA, natRecA]`). -/
theorem nat_a_refines {ci : env.ConstantInfo} (h : basis_pins.nat_a = ok ci) :
    absConstantInfo ci = ConLeche.natA ∧ ConstantInfoWF ci := by
  rw [basis_pins.nat_a] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨block, hb, ci0, hi, hdup⟩ := h
  have hb' : basis_tables.basis_decls_a env.BasisKind.NatK = ok block := hb
  obtain ⟨hhead, hwf⟩ := block_head hb' hi
  rw [Env.constant_info_dup_refines hdup]
  refine ⟨?_, hwf⟩
  simp only [absBasisKind, ConLeche.BasisKind.declsA] at hhead
  exact (Option.some_inj.mp hhead).symm

/-! ## The two predicates

`ConstantInfo`'s equality here is the **derived structural one** — task #27
grepped every kernel site and each spells `==` or `decide (… = some eqA)`;
`ConstantInfo.canonEq` (`Frontend/Export.lean:279`), which canonicalises
level-parameter names, belongs to the frontend alone.  `Refine/Env.lean`'s
`constant_info_beq_refines` is that equality, exactly, on well-formed
constants. -/

/-- `ConLeche/Kernel/BasisA.lean:29-48` — `basis_pins::is_pinned_eq_basis` is
the `some ci = some eqA` half of `env.find? eqName = some eqA`: exactly
`decide (ci = eqA)` on the abstracted stored constant. -/
theorem is_pinned_eq_basis_refines {ci : env.ConstantInfo} {b : Bool}
    (hci : ConstantInfoWF ci) (h : basis_pins.is_pinned_eq_basis ci = ok b) :
    b = decide (absConstantInfo ci = ConLeche.eqA) := by
  rw [basis_pins.is_pinned_eq_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pin, hpin, hbeq⟩ := h
  obtain ⟨habs, hwf⟩ := eq_a_refines hpin
  rw [Env.constant_info_beq_refines hci hwf hbeq, habs]

/-- `ConLeche/Kernel/BasisA.lean:29-48` — the same for `Nat`
(`env.find? natName = some natA`, `reduceElemOk`). -/
theorem is_pinned_nat_basis_refines {ci : env.ConstantInfo} {b : Bool}
    (hci : ConstantInfoWF ci) (h : basis_pins.is_pinned_nat_basis ci = ok b) :
    b = decide (absConstantInfo ci = ConLeche.natA) := by
  rw [basis_pins.is_pinned_nat_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨pin, hpin, hbeq⟩ := h
  obtain ⟨habs, hwf⟩ := nat_a_refines hpin
  rw [Env.constant_info_beq_refines hci hwf hbeq, habs]

/-! ## The two environment guards

Stated against the `F`-twin, `FEnv.find?` (task #18's deviation 3: the port
has one environment spelling, the index).  The cited Lean writes the guard
over `Env` at the pure sites and over `FEnv` at the executed ones
(`stdAxiomOk` / `stdAxiomOkF`, `reduceElemOk` / `reduceElemOkF`); the two
agree by `FEnvRel`'s first clause, `absEnv fe.env = lfe.env`. -/

/-- `ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk` /
`ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF` —
**"the pinned `Eq` basis is installed, unmodified"**:
`basis_pins::eq_basis_pinned` is exactly `decide (find? eqName = some eqA)`.
The `None` arm is exact too: `decide (none = some eqA)` is `false`. -/
theorem eq_basis_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (h : basis_pins.eq_basis_pinned fe = ok b) :
    b = decide (lfe.find? ConLeche.eqName = some ConLeche.eqA) := by
  rw [basis_pins.eq_basis_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, hfind, h⟩ := h
  obtain ⟨hname, hnwf⟩ := BasisNames.eq_name_refines hn
  have hf := find_refines hrel hwf hnwf hfind
  rw [hname] at hf
  cases o with
  | none =>
    simp only [Option.map_none] at hf
    rw [← hf]
    simp only [Result.ok.injEq] at h
    simp [← h]
  | some ci =>
    simp only [Option.map_some] at hf
    rw [← hf, is_pinned_eq_basis_refines (find_wf hwf hnwf hfind ci rfl) h]
    simp

/-- `ConLeche/Kernel/TrustAxioms.lean:177-184 reduceElemOk` /
`ConLeche/Kernel/DeclCheck.lean:288-294 reduceElemOkF` — the same for `Nat`:
the element inductive an `ofReduceNat` axiom needs. -/
theorem nat_basis_pinned_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {b : Bool}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (h : basis_pins.nat_basis_pinned fe = ok b) :
    b = decide (lfe.find? ConLeche.natName = some ConLeche.natA) := by
  rw [basis_pins.nat_basis_pinned] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, hfind, h⟩ := h
  obtain ⟨hname, hnwf⟩ := BasisNames.nat_name_refines hn
  have hf := find_refines hrel hwf hnwf hfind
  rw [hname] at hf
  cases o with
  | none =>
    simp only [Option.map_none] at hf
    rw [← hf]
    simp only [Result.ok.injEq] at h
    simp [← h]
  | some ci =>
    simp only [Option.map_some] at hf
    rw [← hf, is_pinned_nat_basis_refines (find_wf hwf hnwf hfind ci rfl) h]
    simp

/-! ## `kernel::nat_op_pins`

The module declares the `NatOpPinSet` record and nothing else (the module
note, and DESIGN.md tasks #31/#43); its abstraction is `Refine/Pins.lean`'s
`absNatOpPinSet`, reused here and not redefined.  What stands where
`nat_op_pin_sets()` would have stood is the statement about the **decoded**
list. -/

/-- `ConLeche/Kernel/NatOpPins.lean:61 natOpPinSets` — the variant list the
binary runs on **is** con-leche's, with no hypothesis about an argument: the
driver hands `check_decls` `pins_decode::decode_embedded()`, and that decodes
the embedded text to `ConLeche.natOpPinSets`, in file order — which is the
order `checkDivModPinLoop` tries the variants in, so the order is part of the
claim.

Proved, from `Refine/Pins.lean`'s `pins_decode_refines` (the decoder refines
`ConRon.Dump.parsePins`) and `pins_text_decodes` (the closed computation,
measured out of reach in this kernel — task #43).  `decode_embedded` is
`decode PINS_TEXT` because Aeneas models `str::as_bytes` as the identity
(`Generated/FunsExternal.lean:72`).  This is `Refine/Pins.lean`'s
`check_decls_pins_refines` with its proof; fold it back there. -/
theorem nat_op_pin_sets_refines {v : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (h : pins_decode.decode_embedded = ok (.Ok v)) :
    absPins v = ConLeche.natOpPinSets := by
  rw [pins_decode.decode_embedded, core.str.Str.as_bytes] at h
  simp only [bind_tc_ok] at h
  have h1 := pins_decode_refines _ _ h
  rw [pins_text_decodes] at h1
  exact (Except.ok.inj h1).symm

end ConRon.Refine.BasisPins
