/-
`ConRon.Refine.FEnv` — the refinement of `crates/con-ron-core/src/kernel/fenv.rs`
against `ConLeche/Kernel/FEnv.lean` (task #46, `Refine/CORE_PLAN.md` step 2).

`FEnv` is the second thing the port cannot abstract by a *function*: its index
is a `ron::HashMap` and con-leche's is a `Std.HashMap`, whose internal layout no
function of ours reproduces.  So the tier's currency here is a **relation**,
`FEnvRel fe lfe`, with three clauses:

* `absEnv fe.env = lfe.env` — an equation, because `Env.consts` is a list on
  both sides and in the same (newest-first) order;
* `fe.visible_below.val = lfe.visibleBelow` — the installation counter bound
  (`u64` in the port, `Nat` in the Lean, DESIGN.md §3.3);
* `HashMap.RelOn NameWF fe.idx lfe.idx absName absIdxEntry` — task #16's
  abstract-map relation, restricted to well-formed keys (`Refine/HashMapWF.lean`
  explains why the restriction is forced).

`find`/`findProj?` agreement is then a *lemma*, not a clause, which is what
con-leche's `coreKnotI_congr` consumes.

`FEnvWF` is the hereditary invariant: the environment is well formed, the index
satisfies `ron::HashMap`'s own `Inv`, its keys are well-formed names and its
stored constants are well-formed records.
-/
import ConRon.Refine.HashMapWF
import ConRon.Refine.Env
import ConLeche.Kernel.FEnv

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.FEnv

/-! ## The index entry, and the key dictionary's exactness -/

/-- `ConLeche/Kernel/FEnv.lean:44-49` — one index entry: the installation
counter (a `u64` in the port, a `Nat` in the Lean) and the stored record (a `P`
in the port, shared with `env.consts`; `P` is the identity in the model). -/
def absIdxEntry (p : Std.U64 × env.ConstantInfo) : Nat × ConLeche.ConstantInfo :=
  (p.1.val, absConstantInfo p.2)

/-- The index's `Eq2` dictionary *is* `name::beq`. -/
theorem name_eq2_eq (a b : name.Name) :
    name.Name.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = name.beq a b := rfl

/-- The index's key dictionary decides equality of the *port's* names on
well-formed ones — `Refine/HashMapWF.lean`'s hypothesis, discharged.  (The
restriction to `NameWF` is not slack: `absName` drops the stored hash word, so
two ill-formed nodes can abstract equally while `beq` separates them.) -/
theorem name_eq2_fwd :
    HashMap.Eq2Fwd name.Name.Insts.Con_ron_coreRonHashmapEq2 NameWF := by
  intro a b c ha hb h
  have h' : name.beq a b = ok c := h
  rw [Name.beq_refines ha hb h']
  exact decide_eq_decide.mpr
    ⟨fun hc => Name.absName_injective ha hb hc, fun hc => by rw [hc]⟩

/-- `absName` is injective on well-formed names, in the shape
`HashMap.Rel_insert_wf` wants it. -/
theorem absName_inj_on : ∀ a b : name.Name, NameWF a → NameWF b →
    absName a = absName b → a = b := fun _ _ ha hb h => Name.absName_injective ha hb h

/-! ## Values in a table

`HashMap.KeysOk` says what the keys are; the index also has to say what the
*values* are, because a lookup hands its caller a stored `ConstantInfo` and the
knot's induction needs it well formed.  Stated over `toFun`, so that
`insert`'s conclusion (`toFun m' = Function.update (toFun m) k (some v)`)
discharges it in one step. -/

/-- Every value the table denotes satisfies `Q`. -/
def ValsOk {K V : Type} [DecidableEq K] (Q : V → Prop)
    (m : ron.hashmap.HashMap K V) : Prop :=
  ∀ k v, HashMap.toFun m k = some v → Q v

/-- An empty table's values are anything. -/
theorem ValsOk_empty {K V : Type} [DecidableEq K] {Q : V → Prop}
    {m : ron.hashmap.HashMap K V} (h : ∀ k, HashMap.toFun m k = none) :
    ValsOk Q m := by intro k v hv; rw [h k] at hv; simp at hv

/-- `insert` adds one value, so `ValsOk` is preserved by a well-formed one. -/
theorem ValsOk_insert {K V : Type} [DecidableEq K] {Q : V → Prop}
    {m m' : ron.hashmap.HashMap K V} {k : K} {v : V} (hm : ValsOk Q m) (hv : Q v)
    (hupd : HashMap.toFun m' = Function.update (HashMap.toFun m) k (some v)) :
    ValsOk Q m' := by
  intro k' v' hv'
  rw [hupd, Function.update_apply] at hv'
  by_cases hk : k' = k
  · rw [if_pos hk] at hv'; rw [← Option.some_inj.mp hv']; exact hv
  · rw [if_neg hk] at hv'; exact hm k' v' hv'

/-! ## The relation and the invariant -/

/-- `ConLeche/Kernel/FEnv.lean:44-49` — the relation of the module note. -/
def FEnvRel (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  absEnv fe.env = lfe.env ∧
  fe.visible_below.val = lfe.visibleBelow ∧
  HashMap.RelOn NameWF fe.idx lfe.idx absName absIdxEntry

/-- The hereditary invariant of an `FEnv`. -/
structure FEnvWF (fe : fenv.FEnv) : Prop where
  env : EnvWF fe.env
  inv : HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable fe.idx
  keys : HashMap.KeysOk NameWF fe.idx
  vals : ValsOk (fun p => ConstantInfoWF p.2) fe.idx

/-! ## The indexed lookup -/

/-- `ConLeche/Kernel/FEnv.lean:72-75` — `fenv::find` refines `FEnv.find?`:
the index probe, bounded by the visibility counter.  This is the lemma
`coreKnotI_congr` consumes: con-leche reads the environment only through
`find?`/`findProj?`, so the relation of the two indices is all a knot needs. -/
theorem find_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option env.ConstantInfo} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (hn : NameWF n) (h : fenv.find fe n = ok o) :
    o.map absConstantInfo = lfe.find? (absName n) := by
  rw [fenv.find] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, hget, h⟩ := h
  have hg := HashMap.Rel_get_wf name_eq2_fwd hwf.inv hwf.keys hrel.2.2 hn hget
  rw [ConLeche.FEnv.find?, ← hg]
  cases e with
  | none => simpa using h.symm
  | some p =>
    obtain ⟨i, a⟩ := p
    -- the pattern-`let` Aeneas emits for the tuple entry: only the *unifier*
    -- sees through it (task #16's hard spot 1), so it goes by ascription
    have h2 : (if i < fe.visible_below then
        (do let ci ← alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref Global a
            ok (some ci))
      else ok none) = ok o := h
    simp only [Option.map_some, absIdxEntry]
    by_cases hlt : i.val < fe.visible_below.val
    · rw [if_pos (show i < fe.visible_below by scalar_tac)] at h2
      rw [if_pos (show i.val < lfe.visibleBelow from hrel.2.1 ▸ hlt)]
      simp only [arc_deref_eq, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h2
      rw [← h2]; rfl
    · rw [if_neg (show ¬ i < fe.visible_below by scalar_tac), Result.ok.injEq] at h2
      rw [if_neg (show ¬ i.val < lfe.visibleBelow from hrel.2.1 ▸ hlt), ← h2]
      rfl

/-- `fenv::find` answers a well-formed stored constant. -/
theorem find_wf {fe : fenv.FEnv} {n : name.Name} {o : Option env.ConstantInfo}
    (hwf : FEnvWF fe) (hn : NameWF n) (h : fenv.find fe n = ok o) :
    ∀ c, o = some c → ConstantInfoWF c := by
  rw [fenv.find] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, hget, h⟩ := h
  have he := HashMap.get_refines_wf name_eq2_fwd hwf.inv hwf.keys hn hget
  cases e with
  | none => intro c hc; rw [← Result.ok_injective h] at hc; simp at hc
  | some p =>
    obtain ⟨i, a⟩ := p
    have h2 : (if i < fe.visible_below then
        (do let ci ← alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref Global a
            ok (some ci))
      else ok none) = ok o := h
    intro c hc
    have hval : ConstantInfoWF a := hwf.vals n (i, a) he.symm
    by_cases hlt : i.val < fe.visible_below.val
    · rw [if_pos (show i < fe.visible_below by scalar_tac)] at h2
      simp only [arc_deref_eq, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h2
      rw [← h2, Option.some.injEq] at hc
      rw [← hc]; exact hval
    · rw [if_neg (show ¬ i < fe.visible_below by scalar_tac), Result.ok.injEq] at h2
      rw [← h2] at hc; simp at hc

/-- `ConLeche/Kernel/FEnv.lean:79-80` — `fenv::restrict_to` refines
`FEnv.restrictTo`: the prefix view of the first `k` installed constants, `O(1)`
in both (the port takes the record by value and returns it, which is what
replaces Lean's persistence; `fenv.rs`'s module note). -/
theorem restrict_to_refines {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv}
    {k : Std.U64} (hrel : FEnvRel fe lfe) (h : fenv.restrict_to fe k = ok fe') :
    FEnvRel fe' (lfe.restrictTo k.val) := by
  rw [fenv.restrict_to, Result.ok.injEq] at h
  obtain ⟨he, hv, hi⟩ := hrel
  rw [← h]
  exact ⟨he, rfl, hi⟩

/-- `restrict_to` preserves the invariant: it touches one field. -/
theorem restrict_to_wf {fe fe' : fenv.FEnv} {k : Std.U64} (hwf : FEnvWF fe)
    (h : fenv.restrict_to fe k = ok fe') : FEnvWF fe' := by
  rw [fenv.restrict_to, Result.ok.injEq] at h
  rw [← h]
  exact ⟨hwf.env, hwf.inv, hwf.keys, hwf.vals⟩

/-! ## The index build -/

/-- `x + y = ok z` on a `u64` in the forward shape. -/
theorem u64_add_val {x y z : Std.U64} (h : x + y = ok z) : z.val = x.val + y.val := by
  have he := Std.UScalar.add_equiv x y
  rw [h] at he
  simpa using he.2.1

/-- The empty table: what `with_capacity` gives, in the four shapes the index
build needs. -/
theorem empty_idx {m : ron.hashmap.HashMap name.Name (Std.U64 × env.ConstantInfo)}
    {c : Std.Usize}
    (h : ron.hashmap.HashMap.with_capacity name.Name (Std.U64 × env.ConstantInfo) c
      = ok m) :
    HashMap.RelOn NameWF m (∅ : Std.HashMap ConLeche.Name (Nat × ConLeche.ConstantInfo))
        absName absIdxEntry ∧
    HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable m ∧
    HashMap.KeysOk NameWF m ∧ ValsOk (fun p => ConstantInfoWF p.2) m := by
  obtain ⟨hinv, hav, htf⟩ := HashMap.with_capacity_refines h
  refine ⟨HashMap.RelOn_empty htf, hinv, ?_, ValsOk_empty htf⟩
  intro p hp
  rw [hav] at hp
  nomatch hp

/-- `ConLeche/Kernel/FEnv.lean:56-60` — `fenv::mk_fenv_go` refines `mkFEnvGo` on
`cs[i..]`: the index is built from the back, so the newest (front) constant is
inserted last and wins, exactly as `List.find?` takes the first match — which is
why the agreement with `Env.find?` needs no freshness assumption.  The counter,
the relation, `ron::HashMap`'s invariant, the keys and the stored values come
out together, because the insertion step needs all five of the previous one. -/
theorem mk_fenv_go_refines {cs : alloc.vec.Vec env.ConstantInfo}
    (hcs : ConstantInfosWF cs) :
    ∀ k : Nat, ∀ (i : Std.Usize) (c : Std.U64)
      (m : ron.hashmap.HashMap name.Name (Std.U64 × env.ConstantInfo)),
      cs.val.length - i.val ≤ k → fenv.mk_fenv_go cs i = ok (c, m) →
      c.val = (ConLeche.mkFEnvGo ((cs.val.drop i.val).map absConstantInfo)).1 ∧
      HashMap.RelOn NameWF m
        (ConLeche.mkFEnvGo ((cs.val.drop i.val).map absConstantInfo)).2
        absName absIdxEntry ∧
      HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable m ∧
      HashMap.KeysOk NameWF m ∧ ValsOk (fun p => ConstantInfoWF p.2) m := by
  have base : ∀ (i : Std.Usize) (c : Std.U64)
      (m : ron.hashmap.HashMap name.Name (Std.U64 × env.ConstantInfo)),
      cs.val.length ≤ i.val → fenv.mk_fenv_go cs i = ok (c, m) →
      c.val = (ConLeche.mkFEnvGo ((cs.val.drop i.val).map absConstantInfo)).1 ∧
      HashMap.RelOn NameWF m
        (ConLeche.mkFEnvGo ((cs.val.drop i.val).map absConstantInfo)).2
        absName absIdxEntry ∧
      HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable m ∧
      HashMap.KeysOk NameWF m ∧ ValsOk (fun p => ConstantInfoWF p.2) m := by
    intro i c m hi h
    rw [fenv.mk_fenv_go.eq_def] at h
    simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨hm, hwc, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrel, hinv, hkeys, hvals⟩ := empty_idx hwc
    have e := Result.ok_injective h
    have ec : c = 0#u64 := (congrArg Prod.fst e).symm
    have em : m = hm := (congrArg Prod.snd e).symm
    rw [List.drop_eq_nil_of_le hi, List.map_nil, ConLeche.mkFEnvGo]
    subst ec; subst em
    exact ⟨rfl, hrel, hinv, hkeys, hvals⟩
  intro k
  induction k with
  | zero => intro i c m hk h; exact base i c m (by omega) h
  | succ k ih =>
    intro i c m hk h
    by_cases hi : cs.val.length ≤ i.val
    · exact base i c m hi h
    rw [fenv.mk_fenv_go.eq_def] at h
    simp only [] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    have hl : i.val < cs.val.length := by omega
    obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
    have hwv : w.val = i.val + 1 := HashMap.uscalar_add_eq hw
    obtain ⟨p, hrec, h⟩ := bind_eq_ok_iff.mp h
    -- the pattern-`let`s Aeneas emits for the two pair results: only the
    -- unifier sees through them (task #16's hard spot 1), so they go by
    -- ascription, with `p.1`/`p.2` in place of the bound pattern variables
    have h3 : (do
        let a ← alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice (alloc.sync.Arc env.ConstantInfo)) cs i
        let ci ← alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref Global a
        let n ← env.constant_info_name ci
        let a1 ← env.constant_info_rc_dup a
        let q ← ron.hashmap.HashMap.insert
          name.Name.Insts.Con_ron_coreRonHashmapHashable
          name.Name.Insts.Con_ron_coreRonHashmapEq2 p.2 n (p.1, a1)
        let i4 ← p.1 + 1#u64
        ok (i4, q.2)) = ok (c, m) := h
    obtain ⟨hc0, hrel0, hinv0, hkeys0, hvals0⟩ := ih w p.1 p.2 (by omega) hrec
    rw [hwv] at hc0 hrel0
    obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hl)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, arc_deref_eq,
      env.constant_info_rc_dup, ptr_clone_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h3
    obtain ⟨n, hn, q, hins, h3⟩ := h3
    have hwfc := hcs _ (List.getElem_mem hl)
    have hnwf : NameWF n := Env.constant_info_name_wf hwfc hn
    obtain ⟨hinv1, -, hupd, hkeys1⟩ :=
      HashMap.insert_refines_wf name_eq2_fwd hinv0 hkeys0 hnwf hins
    obtain ⟨hrel1, -⟩ := HashMap.Rel_insert_wf name_eq2_fwd absName_inj_on hinv0
      hkeys0 hrel0 hnwf hins
    have hvals1 : ValsOk (fun r => ConstantInfoWF r.2) q.2 :=
      ValsOk_insert hvals0 hwfc hupd
    obtain ⟨i4, hi4, e⟩ := h3
    have ec : c = i4 := (congrArg Prod.fst e).symm
    have em : m = q.2 := (congrArg Prod.snd e).symm
    subst ec; subst em
    rw [List.drop_eq_getElem_cons hl, List.map_cons, ConLeche.mkFEnvGo]
    refine ⟨?_, ?_, hinv1, hkeys1, hvals1⟩
    · rw [u64_add_val hi4, hc0]; rfl
    · rw [Env.constant_info_name_refines hn] at hrel1
      rw [show absIdxEntry (p.1, cs.val[i.val]) = (p.1.val, absConstantInfo cs.val[i.val])
        from rfl, hc0] at hrel1
      exact hrel1

/-- `ConLeche/Kernel/FEnv.lean:64-66` — `fenv::mk_fenv` refines `mkFEnv`: the
index of `env`, with nothing hidden (`visibleBelow` is the constant count). -/
theorem mk_fenv_refines {e : env.Env} {fe : fenv.FEnv} (he : EnvWF e)
    (h : fenv.mk_fenv e = ok fe) :
    FEnvRel fe (ConLeche.mkFEnv (absEnv e)) ∧ FEnvWF fe := by
  rw [fenv.mk_fenv] at h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  have h2 : (ok { env := e, idx := p.2, visible_below := p.1 } : Result fenv.FEnv)
      = ok fe := h
  obtain ⟨hc, hrel, hinv, hkeys, hvals⟩ :=
    mk_fenv_go_refines he e.consts.val.length 0#usize p.1 p.2 (by scalar_tac) hgo
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [h0, List.drop_zero] at hc hrel
  rw [← Result.ok_injective h2]
  exact ⟨⟨rfl, hc, hrel⟩, ⟨he, hinv, hkeys, hvals⟩⟩

/-! ## `push`

**`fenv::push`'s `env.consts` clause does not hold of the generated model, and
the fault is in the Aeneas Lean library, not in the port.**  The port's
`consts.insert(0, rc)` is Rust's `Vec::insert`, which shifts and prepends;
`_tmp/aeneas-lean/Aeneas/Std/Vec.lean:167-172` models it as

```lean
def Vec.insert (v) (i) (x) : Result (Vec α) :=
  if i.val < v.length then ok (.from (v.val.set i x) …) else fail arrayOutOfBounds
```

i.e. as `List.set` — an *overwrite*, where Rust inserts.  So the model of
`fenv::push` **replaces** `consts[0]` instead of consing onto the list, and
fails outright on an empty environment (`0 < 0` is false).  The `idx` and
`visible_below` clauses are unaffected and are proved below
(`push_idx_refines`); the `absEnv` clause is *false* of today's model, so
`push_refines` is `sorry` and stays that way until one of:

* the Aeneas library is corrected (`List.set i x` → `List.insertIdx i x`, and
  the guard relaxed from Rust's `i ≤ length`), carried in
  `spikes/toolchain/aeneas-433.patch` — the fix is one line and is owed
  upstream;
* or the port stops using `Vec::insert`.  `env.rs`'s `Env.consts` is
  newest-first only so that `fenv::mk_fenv_go`'s counters can be positions
  counted from the bottom; a push-at-the-back spelling read in reverse would
  avoid the call.  `kernel/checker_base.rs:239,271,275` has the other three
  uses, so a Rust fix is four call sites.

Either way it is a *model* defect that the refinement tier caught, which is
what the tier is for; nothing about the running binary changes. -/

/-- `fenv::push`'s index and counter clauses — the two that hold.  The new entry
gets the next installation counter, so a push is visible to everything checked
after it and to nothing checked before (con-leche task #108). -/
theorem push_idx_refines {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv}
    {ci : env.ConstantInfo} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (hci : ConstantInfoWF ci) (h : fenv.push fe ci = ok fe') :
    fe'.visible_below.val = (lfe.push (absConstantInfo ci)).visibleBelow ∧
    HashMap.RelOn NameWF fe'.idx (lfe.push (absConstantInfo ci)).idx
      absName absIdxEntry ∧
    HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable fe'.idx ∧
    HashMap.KeysOk NameWF fe'.idx ∧
    ValsOk (fun p => ConstantInfoWF p.2) fe'.idx := by
  rw [fenv.push] at h
  simp only [env.constant_info_share, ptr_new_eq, arc_deref_eq,
    env.constant_info_rc_dup, ptr_clone_eq, bind_eq_ok_iff, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨n, hn, q, hins, h⟩ := h
  have hnwf : NameWF n := Env.constant_info_name_wf hci hn
  obtain ⟨hinv1, -, hupd, hkeys1⟩ :=
    HashMap.insert_refines_wf name_eq2_fwd hwf.inv hwf.keys hnwf hins
  obtain ⟨hrel1, -⟩ := HashMap.Rel_insert_wf name_eq2_fwd absName_inj_on hwf.inv
    hwf.keys hrel.2.2 hnwf hins
  have hvals1 : ValsOk (fun r => ConstantInfoWF r.2) q.2 :=
    ValsOk_insert hwf.vals hci hupd
  have h3 : (do
      let consts ← alloc.vec.Vec.insert fe.env.consts 0#usize ci
      let i ← fe.visible_below + 1#u64
      ok { env := { consts := consts }, idx := q.2, visible_below := i }) = ok fe' := h
  obtain ⟨consts, hconsts, h4⟩ := bind_eq_ok_iff.mp h3
  obtain ⟨i, hi, e0⟩ := bind_eq_ok_iff.mp h4
  have e := Result.ok_injective e0
  have eidx : fe'.idx = q.2 := (congrArg (fun z : fenv.FEnv => z.idx) e).symm
  have evb : fe'.visible_below = i :=
    (congrArg (fun z : fenv.FEnv => z.visible_below) e).symm
  rw [eidx, evb]
  refine ⟨?_, ?_, hinv1, hkeys1, hvals1⟩
  · rw [u64_add_val hi, hrel.2.1]; rfl
  · rw [Env.constant_info_name_refines hn] at hrel1
    rw [show absIdxEntry (fe.visible_below, ci)
      = (fe.visible_below.val, absConstantInfo ci) from rfl, hrel.2.1] at hrel1
    exact hrel1

/-- `ConLeche/Kernel/FEnv.lean:87-89` — `fenv::push` refines `FEnv.push`.
**Open, and not merely unproved**: the section note above has the reason — the
`absEnv` clause is *false* of the current Aeneas model of `Vec::insert`. -/
theorem push_refines {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv}
    {ci : env.ConstantInfo} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (hci : ConstantInfoWF ci) (h : fenv.push fe ci = ok fe') :
    FEnvRel fe' (lfe.push (absConstantInfo ci)) ∧ FEnvWF fe' := by
  sorry

/-! ## `dup` -/

/-- `ConLeche/Kernel/FEnv.lean:44-49` — `fenv::dup` is a full copy: the list is
`n` `P` bumps and the index is *rebuilt* by `mk_fenv_go` (`ron::hashmap` has no
iteration API, and the rebuild is the definition of the counters anyway), with
`visible_below` carried over — so the copy of a restricted view is that
restricted view, which is what the conclusion's `restrictTo` says.  The Lean
counterpart is `mkFEnv` of the same environment, not the value the copy came
from: `FEnvRel` constrains the source index only through its abstract map, and
`mkFEnv_push` is what makes the two agree on every reachable `FEnv`. -/
theorem dup_refines {fe fe' : fenv.FEnv} (hwf : FEnvWF fe)
    (h : fenv.dup fe = ok fe') :
    FEnvRel fe'
      ((ConLeche.mkFEnv (absEnv fe.env)).restrictTo fe.visible_below.val) ∧
    FEnvWF fe' := by
  rw [fenv.dup] at h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e2, hdup, h⟩ := bind_eq_ok_iff.mp h
  have h2 : (ok { env := e2, idx := p.2, visible_below := fe.visible_below }
      : Result fenv.FEnv) = ok fe' := h
  obtain ⟨hc, hrel, hinv, hkeys, hvals⟩ :=
    mk_fenv_go_refines hwf.env fe.env.consts.val.length 0#usize p.1 p.2
      (by scalar_tac) hgo
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [h0, List.drop_zero] at hrel
  have hee : e2 = fe.env := Env.env_dup_refines hdup
  rw [← Result.ok_injective h2]
  refine ⟨⟨?_, rfl, ?_⟩, ⟨?_, hinv, hkeys, hvals⟩⟩
  · rw [hee]; rfl
  · exact hrel
  · rw [hee]; exact hwf.env

/-! ## The projection lookup and the slot queries -/

/-- `ConLeche/Kernel/FEnv.lean:92-95` — `fenv::find_proj` refines
`FEnv.findProj?`: the structure's table under `projTableName T`, viewed at field
`i`, and `none` beyond the table's field count. -/
theorem find_proj_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {t : name.Name}
    {i : Std.U64} {o : Option env.ProjEntry} (hrel : FEnvRel fe lfe)
    (hwf : FEnvWF fe) (ht : NameWF t) (h : fenv.find_proj fe t i = ok o) :
    o.map absProjEntry = lfe.findProj? (absName t) i.val := by
  rw [fenv.find_proj] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, oc, hoc, h⟩ := h
  have hnwf := Env.proj_table_name_wf ht hn
  have hfind := find_refines hrel hwf hnwf hoc
  rw [Env.proj_table_name_refines hn] at hfind
  rw [ConLeche.FEnv.findProj?, ← hfind]
  cases oc with
  | none => simpa using h.symm
  | some ci =>
    have hcwf := find_wf hwf hnwf hoc ci rfl
    cases ci <;> simp only [] at h <;>
      simp only [Option.map_some, absConstantInfo] <;>
      try simpa using h.symm
    case ProjInfo tbl =>
      by_cases hlt : i.val < tbl.num_fields.val
      · rw [if_pos (show i < tbl.num_fields by scalar_tac), bind_eq_ok_iff] at h
        obtain ⟨pe, hpe, h⟩ := h
        rw [if_pos (show i.val < (absProjTable tbl).numFields from hlt),
          ← Result.ok_injective h]
        simp only [Option.map_some, Option.some.injEq]
        exact Env.proj_table_entry_refines hpe
      · rw [if_neg (show ¬ i < tbl.num_fields by scalar_tac), Result.ok.injEq] at h
        rw [if_neg (show ¬ i.val < (absProjTable tbl).numFields from hlt), ← h]
        rfl

/-- `ConLeche/Kernel/FEnv.lean:106-110` — `fenv::rec_slot_ok` is the cited
body's one-slot test, `| some (.recInfo _ _ _ _) => true | _ => false`. -/
theorem rec_slot_ok_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {b : Bool} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) (hn : NameWF n)
    (h : fenv.rec_slot_ok fe n = ok b) :
    b = (match lfe.find? (absName n) with
          | some ci => ci.isRecInfo
          | none => false) := by
  rw [fenv.rec_slot_ok] at h
  obtain ⟨oc, hoc, h⟩ := bind_eq_ok_iff.mp h
  have hf := find_refines hrel hwf hn hoc
  rw [← hf]
  cases oc with
  | none => simpa using h.symm
  | some ci => simpa using Env.is_rec_info_refines h

/-! ## What is not here

`fenv::tower_slots_all_f`/`_from` and `fenv::rec_slots_all_f`/`_from` are
`ConLeche/Kernel/Core.lean`'s `towerSlotsAll`/`recSlotsAll` read through the
index (`fenv.rs`'s citations say so), i.e. `(List.range nF).all …`.  Their
refinement is the `List.range'` suffix bookkeeping of a `u64` index recursion
and nothing to do with the relation this file is about, so they go with the rest
of `Core.lean`'s readers in `Refine/CoreK/` (`CORE_PLAN.md` step 4).
`rec_slot_ok_refines` above is the one of the four the relation *does* settle.

`andRescueSlotsF` and the four indexed guard twins (`natLitSupportedF`,
`strLitSupportedF`, `natOpGuardF`, `natOpStoredF`) are not ported yet
(`fenv.rs`'s module note), so they have nothing to refine.

## Axiom census (DESIGN.md §5, the P3 gate)

Lean's own three axioms and no more.  `Classical.choice` appears because the
abstract map `HashMap.toFun` is defined with `DecidableEq` on the port's key
type, which `Refine/Abs.lean` supplies classically (see the note there); nothing
here reaches `ConRon.Generated.kernel.pins_text.PINS_TEXT`, whose string
constant carries a `native_decide` axiom (task #43).  `push_refines` is
deliberately **not** in the census: it is the one `sorry`, and the section note
above says why it is not merely unproved. -/

/--
info: 'ConRon.Refine.FEnv.find_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms find_refines

/--
info: 'ConRon.Refine.FEnv.mk_fenv_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mk_fenv_refines

/--
info: 'ConRon.Refine.FEnv.find_proj_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms find_proj_refines

/--
info: 'ConRon.Refine.FEnv.push_idx_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms push_idx_refines

/--
info: 'ConRon.Refine.FEnv.dup_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms dup_refines

/--
info: 'ConRon.Refine.FEnv.restrict_to_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restrict_to_refines

end ConRon.Refine.FEnv
