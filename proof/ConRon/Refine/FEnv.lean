/-
`ConRon.Refine.FEnv` — the refinement of `crates/con-ron-core/src/kernel/fenv.rs`
against `ConLeche/Kernel/FEnv.lean` (task #46, `Refine/CORE_PLAN.md` step 2).

`FEnv` is the second thing the port cannot abstract by a *function*: its index
is a `ron::HashMap` and con-leche's is a `Std.HashMap`, whose internal layout no
function of ours reproduces.  So the tier's currency here is a **relation**,
`FEnvRel fe lfe`, with three clauses:

* `absEnv fe.env = lfe.env` — an equation, because `Env.consts` is a list on
  both sides (the port stores it reversed, which `absEnv` reverses back: task
  #50);
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

/-! ## The index build

The port builds the index *forward* over `env.consts`, which is the cited list
**reversed** (task #50), threading the table and the counter down; the cited
`mkFEnvGo` recurses over the cited list, i.e. from this `Vec`'s back.  The
invariant that connects them is `absPrefixIdx`: the abstract index of the first
`i` stored constants. -/

/-- `ConLeche/Kernel/FEnv.lean:56-60` — the cited index of the first `i` stored
constants, i.e. of the cited list's `i`-long tail (`consts[..i]` read back to
front).  `mk_fenv_go`'s loop invariant. -/
def absPrefixIdx (cs : alloc.vec.Vec env.ConstantInfo) (i : Nat) :
    Nat × Std.HashMap ConLeche.Name (Nat × ConLeche.ConstantInfo) :=
  ConLeche.mkFEnvGo ((cs.val.take i).reverse.map absConstantInfo)

/-- Nothing installed: the counter is `0` and the table is empty. -/
theorem absPrefixIdx_zero (cs : alloc.vec.Vec env.ConstantInfo) :
    absPrefixIdx cs 0
      = (0, (∅ : Std.HashMap ConLeche.Name (Nat × ConLeche.ConstantInfo))) := by
  rw [absPrefixIdx]
  simp [ConLeche.mkFEnvGo]

/-- One installation: the `i`-th stored constant is the *head* of the cited
list's `(i+1)`-long tail, so it is inserted last and wins. -/
theorem absPrefixIdx_succ {cs : alloc.vec.Vec env.ConstantInfo} {i : Nat}
    (h : i < cs.val.length) :
    absPrefixIdx cs (i + 1) =
      ((absPrefixIdx cs i).1 + 1,
       (absPrefixIdx cs i).2.insert (absConstantInfo cs.val[i]).name
         ((absPrefixIdx cs i).1, absConstantInfo cs.val[i])) := by
  rw [absPrefixIdx, absPrefixIdx, list_take_reverse_cons h, List.map_cons,
    ConLeche.mkFEnvGo]

/-- Everything installed: the whole cited list, which is what `mkFEnv` reads. -/
theorem absPrefixIdx_all (cs : alloc.vec.Vec env.ConstantInfo) :
    absPrefixIdx cs cs.val.length
      = ConLeche.mkFEnvGo (absEnv { consts := cs }).consts := by
  rw [absPrefixIdx, List.take_length, absEnv, absConstantInfos, List.map_reverse]

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

/-- `ConLeche/Kernel/FEnv.lean:56-60` — `fenv::mk_fenv_go` refines `mkFEnvGo`:
the port inserts `cs[i..]` into the table it is given, in increasing `i`, each
constant under its own index as its counter — and since `cs` is the cited list
reversed (task #50), increasing `i` is the cited recursion *unwinding*, so the
newest constant is inserted last and wins, exactly as `List.find?` takes the
first match; the agreement with `Env.find?` needs no freshness assumption.  The
table and the counter are threaded **down**, so this is an accumulator lemma:
the five properties of the table are hypotheses as well as conclusions, because
the insertion step needs all five of the previous one. -/
theorem mk_fenv_go_refines {cs : alloc.vec.Vec env.ConstantInfo}
    (hcs : ConstantInfosWF cs) :
    ∀ k : Nat, ∀ (i : Std.Usize) (c c' : Std.U64)
      (m m' : ron.hashmap.HashMap name.Name (Std.U64 × env.ConstantInfo)),
      cs.val.length - i.val ≤ k → i.val ≤ cs.val.length →
      c.val = (absPrefixIdx cs i.val).1 →
      HashMap.RelOn NameWF m (absPrefixIdx cs i.val).2 absName absIdxEntry →
      HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable m →
      HashMap.KeysOk NameWF m → ValsOk (fun p => ConstantInfoWF p.2) m →
      fenv.mk_fenv_go cs i c m = ok (c', m') →
      c'.val = (absPrefixIdx cs cs.val.length).1 ∧
      HashMap.RelOn NameWF m' (absPrefixIdx cs cs.val.length).2
        absName absIdxEntry ∧
      HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable m' ∧
      HashMap.KeysOk NameWF m' ∧ ValsOk (fun p => ConstantInfoWF p.2) m' := by
  have base : ∀ (i : Std.Usize) (c c' : Std.U64)
      (m m' : ron.hashmap.HashMap name.Name (Std.U64 × env.ConstantInfo)),
      cs.val.length ≤ i.val → i.val ≤ cs.val.length →
      c.val = (absPrefixIdx cs i.val).1 →
      HashMap.RelOn NameWF m (absPrefixIdx cs i.val).2 absName absIdxEntry →
      HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable m →
      HashMap.KeysOk NameWF m → ValsOk (fun p => ConstantInfoWF p.2) m →
      fenv.mk_fenv_go cs i c m = ok (c', m') →
      c'.val = (absPrefixIdx cs cs.val.length).1 ∧
      HashMap.RelOn NameWF m' (absPrefixIdx cs cs.val.length).2
        absName absIdxEntry ∧
      HashMap.Inv name.Name.Insts.Con_ron_coreRonHashmapHashable m' ∧
      HashMap.KeysOk NameWF m' ∧ ValsOk (fun p => ConstantInfoWF p.2) m' := by
    intro i c c' m m' hge hle hc hrel hinv hkeys hvals h
    rw [fenv.mk_fenv_go.eq_def] at h
    simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    have ei : i.val = cs.val.length := by omega
    have ec : c = c' := congrArg Prod.fst h
    have em : m = m' := congrArg Prod.snd h
    subst ec; subst em
    rw [ei] at hc hrel
    exact ⟨hc, hrel, hinv, hkeys, hvals⟩
  intro k
  induction k with
  | zero =>
    intro i c c' m m' hk hle hc hrel hinv hkeys hvals h
    exact base i c c' m m' (by omega) hle hc hrel hinv hkeys hvals h
  | succ k ih =>
    intro i c c' m m' hk hle hc hrel hinv hkeys hvals h
    by_cases hge : cs.val.length ≤ i.val
    · exact base i c c' m m' hge hle hc hrel hinv hkeys hvals h
    rw [fenv.mk_fenv_go.eq_def] at h
    simp only [] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    have hl : i.val < cs.val.length := by omega
    obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hl)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, arc_deref_eq,
      env.constant_info_rc_dup, ptr_clone_eq, bind_eq_ok_iff, Result.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨n, hn, q, hins, h⟩ := h
    -- the pattern-`let` Aeneas emits for the insert's pair result: only the
    -- *unifier* sees through it (task #16's hard spot 1), so it goes by
    -- ascription, with `q.2` in place of the bound pattern variable
    have h3 : (do
        let i2 ← i + 1#usize
        let i3 ← c + 1#u64
        fenv.mk_fenv_go cs i2 i3 q.2) = ok (c', m') := h
    obtain ⟨i2, hi2, h4⟩ := bind_eq_ok_iff.mp h3
    obtain ⟨i3, hi3, h5⟩ := bind_eq_ok_iff.mp h4
    have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
    have hwfc := hcs _ (List.getElem_mem hl)
    have hnwf : NameWF n := Env.constant_info_name_wf hwfc hn
    obtain ⟨hinv1, -, hupd, hkeys1⟩ :=
      HashMap.insert_refines_wf name_eq2_fwd hinv hkeys hnwf hins
    obtain ⟨hrel1, -⟩ := HashMap.Rel_insert_wf name_eq2_fwd absName_inj_on hinv
      hkeys hrel hnwf hins
    have hvals1 : ValsOk (fun r => ConstantInfoWF r.2) q.2 :=
      ValsOk_insert hvals hwfc hupd
    refine ih i2 i3 c' q.2 m' (by omega) (by omega) ?_ ?_ hinv1 hkeys1 hvals1 h5
    · rw [hi2v, absPrefixIdx_succ hl, u64_add_val hi3, hc]; rfl
    · rw [hi2v, absPrefixIdx_succ hl]
      rw [Env.constant_info_name_refines hn] at hrel1
      rw [show absIdxEntry (c, cs.val[i.val]) = (c.val, absConstantInfo cs.val[i.val])
        from rfl, hc] at hrel1
      exact hrel1

/-- `ConLeche/Kernel/FEnv.lean:64-66` — `fenv::mk_fenv` refines `mkFEnv`: the
index of `env`, with nothing hidden (`visibleBelow` is the constant count). -/
theorem mk_fenv_refines {e : env.Env} {fe : fenv.FEnv} (he : EnvWF e)
    (h : fenv.mk_fenv e = ok fe) :
    FEnvRel fe (ConLeche.mkFEnv (absEnv e)) ∧ FEnvWF fe := by
  rw [fenv.mk_fenv] at h
  obtain ⟨hm, hwc, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrel0, hinv0, hkeys0, hvals0⟩ := empty_idx hwc
  -- the pattern-`let` for `mk_fenv_go`'s pair result, by ascription
  have h2 : (do
      let p ← fenv.mk_fenv_go e.consts 0#usize 0#u64 hm
      ok { env := e, idx := p.2, visible_below := p.1 }) = ok fe := h
  obtain ⟨p, hgo, h3⟩ := bind_eq_ok_iff.mp h2
  have hz : (absPrefixIdx e.consts (0#usize : Std.Usize).val)
      = (0, (∅ : Std.HashMap ConLeche.Name (Nat × ConLeche.ConstantInfo))) :=
    absPrefixIdx_zero e.consts
  obtain ⟨hc, hrel, hinv, hkeys, hvals⟩ :=
    mk_fenv_go_refines he e.consts.val.length 0#usize 0#u64 p.1 hm p.2
      (by scalar_tac) (by scalar_tac) (by rw [hz]; rfl) (by rw [hz]; exact hrel0)
      hinv0 hkeys0 hvals0 hgo
  rw [absPrefixIdx_all e.consts] at hc hrel
  rw [← Result.ok_injective h3]
  exact ⟨⟨rfl, hc, hrel⟩, ⟨he, hinv, hkeys, hvals⟩⟩

/-! ## `push`

`ci :: fe.env.consts` is `Vec::push` in the port: `Env.consts` is the cited list
**reversed** (task #50, `env.rs`'s `Env` deviation), so the cons is a push at the
back — `O(1)` amortised, as Lean's is, and modelled exactly
(`Aeneas/Std/Vec.lean:152-159`: `List.concat`).

This is where the tier earned its keep.  Until task #50 the port wrote the cons
as `consts.insert(0, rc)`, i.e. Rust's `Vec::insert`, and
`Aeneas/Std/Vec.lean:167-172` models *that* as `v.val.set i x` — an **overwrite**
where Rust inserts, failing outright at `i = len`.  The `idx` and
`visible_below` clauses were provable (`push_idx_refines` below), the `absEnv`
clause was *false of the model*, and `push_refines` was this tier's one `sorry`
with nothing wrong in the Rust.  The library bug is `AENEAS_FINDINGS.md` §3.9 and
ask #1, and the port's answer is to store the list the other way round: no
function of `crates/con-ron-core` calls `Vec::insert` any more, so no model of
ours depends on that primitive. -/

/-- `fenv::push`'s list clause at the level of the `Vec`: the constant lands at
the **back** of the stored list, which is the front of the cited one. -/
theorem push_consts {fe fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (h : fenv.push fe ci = ok fe') :
    fe'.env.consts.val = fe.env.consts.val ++ [ci] := by
  rw [fenv.push] at h
  simp only [env.constant_info_share, ptr_new_eq, arc_deref_eq,
    env.constant_info_rc_dup, ptr_clone_eq, bind_eq_ok_iff, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨n, hn, q, hins, h⟩ := h
  have h3 : (do
      let consts ← alloc.vec.Vec.push fe.env.consts ci
      let i ← fe.visible_below + 1#u64
      ok { env := { consts := consts }, idx := q.2, visible_below := i }) = ok fe' := h
  obtain ⟨consts, hconsts, h4⟩ := bind_eq_ok_iff.mp h3
  obtain ⟨i, hi, e0⟩ := bind_eq_ok_iff.mp h4
  have e := Result.ok_injective e0
  have ec : fe'.env.consts = consts :=
    (congrArg (fun z : fenv.FEnv => z.env.consts) e).symm
  rw [ec, vec_push_val hconsts]

/-- `fenv::push`'s index and counter clauses.  The new entry gets the next
installation counter, so a push is visible to everything checked after it and to
nothing checked before (con-leche task #108). -/
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
      let consts ← alloc.vec.Vec.push fe.env.consts ci
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

/-- `ConLeche/Kernel/FEnv.lean:87-89` — `fenv::push` refines `FEnv.push`: the
index of the cons-extended environment.  The list clause is `push_consts` read
through `absEnv`, which reverses — so a push at the back *is* the cited cons —
and the other two are `push_idx_refines`. -/
theorem push_refines {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv}
    {ci : env.ConstantInfo} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (hci : ConstantInfoWF ci) (h : fenv.push fe ci = ok fe') :
    FEnvRel fe' (lfe.push (absConstantInfo ci)) ∧ FEnvWF fe' := by
  obtain ⟨hvb, hidx, hinv, hkeys, hvals⟩ := push_idx_refines hrel hwf hci h
  have hlist := push_consts h
  have henv : absEnv fe'.env = (lfe.push (absConstantInfo ci)).env := by
    rw [ConLeche.FEnv.push, ← hrel.1, absEnv, absEnv, absConstantInfos,
      absConstantInfos, hlist]
    simp
  refine ⟨⟨henv, hvb, hidx⟩, ⟨?_, hinv, hkeys, hvals⟩⟩
  intro c hc
  rw [show (fe'.env.consts).val = fe.env.consts.val ++ [ci] from hlist,
    List.mem_append] at hc
  cases hc with
  | inl hc => exact hwf.env c hc
  | inr hc => rw [List.mem_singleton.mp hc]; exact hci

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
  obtain ⟨hm, hwc, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrel0, hinv0, hkeys0, hvals0⟩ := empty_idx hwc
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e2, hdup, h⟩ := bind_eq_ok_iff.mp h
  have h2 : (ok { env := e2, idx := p.2, visible_below := fe.visible_below }
      : Result fenv.FEnv) = ok fe' := h
  have hz : (absPrefixIdx fe.env.consts (0#usize : Std.Usize).val)
      = (0, (∅ : Std.HashMap ConLeche.Name (Nat × ConLeche.ConstantInfo))) :=
    absPrefixIdx_zero fe.env.consts
  obtain ⟨hc, hrel, hinv, hkeys, hvals⟩ :=
    mk_fenv_go_refines hwf.env fe.env.consts.val.length 0#usize 0#u64 p.1 hm p.2
      (by scalar_tac) (by scalar_tac) (by rw [hz]; rfl) (by rw [hz]; exact hrel0)
      hinv0 hkeys0 hvals0 hgo
  rw [absPrefixIdx_all fe.env.consts] at hrel
  have hee : e2 = fe.env := Env.env_dup_refines hdup
  rw [← Result.ok_injective h2]
  refine ⟨⟨?_, rfl, ?_⟩, ⟨?_, hinv, hkeys, hvals⟩⟩
  · rw [hee]; rfl
  · exact hrel
  · rw [hee]; exact hwf.env

/-! ### The bridge the callers of `dup` need (task #59)

`dup_refines` relates the copy to the *canonical* Lean `FEnv` — `mkFEnv` of the
copied environment, restricted to the visibility counter — because that is what
the rebuild computes.  But `ConLeche/Cached/CheckerC.lean`'s stages pass their
own persistent `lfe` across the copy (`checkNativePassS` is the first one), so
what those compositions need is `FEnvRel fe lfe → FEnvRel (dup fe) lfe`.

That is **not** true of an arbitrary `lfe`: `FEnvRel` pins `lfe.idx` only on
the image of the well-formed names, so an `lfe` whose index disagrees with its
own environment is related to `fe` and not to the rebuild.  The missing
ingredient is a property of `fe` alone — that `fe`'s index already *is* the
rebuild of `fe`'s environment — and that is exactly `dup_refines`' own
conclusion, so it is named here and carried:

* `dup` establishes it (`dup_canon`), and so does `mk_fenv` (`mk_fenv_canon`),

which is how every `FEnv` a stage copies was built, so the hypothesis is
discharged at the call sites and nothing is weakened.  (`push` does *not*
preserve it on a **restricted** view: `FEnv.push` stamps the new entry with
`visibleBelow`, while the rebuild stamps it with the constant count, and the
two differ exactly when the view hides something.  The stages that copy an
index copy a `dup`/`mk_fenv` product, so that gap is not in the way.) -/

/-- **The index is the rebuild of the environment.**  Equivalently: `fe` is
related to the canonical Lean `FEnv` of its own environment.  Every `FEnv` the
checker holds has this property — `mk_fenv` and `dup` establish it and `push`
preserves it — and it is what turns `dup_refines`' canonical conclusion into a
statement about the caller's own `lfe`. -/
def FEnvCanon (fe : fenv.FEnv) : Prop :=
  FEnvRel fe ((ConLeche.mkFEnv (absEnv fe.env)).restrictTo fe.visible_below.val)

/-- `dup` establishes `FEnvCanon`: that is `dup_refines` read as a property of
the copy. -/
theorem dup_canon {fe fe' : fenv.FEnv} (hwf : FEnvWF fe)
    (h : fenv.dup fe = ok fe') : FEnvCanon fe' := by
  obtain ⟨hrel, _⟩ := dup_refines hwf h
  have henv : fe'.env = fe.env := by
    rw [fenv.dup] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e2, hdup, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]; exact Env.env_dup_refines hdup
  have hvb : fe'.visible_below = fe.visible_below := by
    rw [fenv.dup] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
  unfold FEnvCanon
  rw [henv, hvb]
  exact hrel

/-- **The bridge**: under `FEnvCanon`, `dup` keeps the caller's own `lfe`.
This is what `native_install`'s `check_native_pass_former` and
`check_native_rec_rules` compose across `fenv::dup`. -/
theorem dup_rel {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv} (hwf : FEnvWF fe)
    (hcan : FEnvCanon fe) (hrel : FEnvRel fe lfe) (h : fenv.dup fe = ok fe') :
    FEnvRel fe' lfe ∧ FEnvWF fe' ∧ FEnvCanon fe' := by
  obtain ⟨hrel', hwf'⟩ := dup_refines hwf h
  refine ⟨⟨?_, ?_, ?_⟩, hwf', dup_canon hwf h⟩
  · rw [hrel'.1]; exact hrel.1
  · rw [hrel'.2.1]; exact hrel.2.1
  · intro k hk
    rw [hrel'.2.2 k hk]
    exact (hcan.2.2 k hk).symm.trans (hrel.2.2 k hk)

/-- The counter `mkFEnvGo` hands out last is the constant count. -/
theorem mkFEnvGo_fst (l : List ConLeche.ConstantInfo) :
    (ConLeche.mkFEnvGo l).1 = l.length := by
  induction l with
  | nil => rfl
  | cons ci cs ih => rw [ConLeche.mkFEnvGo, List.length_cons, ih]

/-- **An unrestricted view**: nothing is hidden, i.e. the visibility counter is
the constant count.  `mk_fenv` and `push` produce one; `restrict_to` is the
only thing that breaks it.  `push_canon` needs it because `FEnv.push` stamps
the new entry with `visibleBelow` while the rebuild stamps it with the count,
and the two agree exactly here. -/
def FEnvFull (fe : fenv.FEnv) : Prop :=
  fe.visible_below.val = fe.env.consts.val.length

/-- `mk_fenv` establishes `FEnvCanon`: it *is* the rebuild, at the full
visibility counter. -/
theorem mk_fenv_canon {e : env.Env} {fe : fenv.FEnv} (he : EnvWF e)
    (h : fenv.mk_fenv e = ok fe) : FEnvCanon fe := by
  obtain ⟨hrel, _⟩ := mk_fenv_refines he h
  have henv : fe.env = e := by
    rw [fenv.mk_fenv] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
  unfold FEnvCanon
  rw [henv]
  refine ⟨hrel.1, ?_, ?_⟩
  · rw [hrel.2.1]; rfl
  · intro k hk; rw [hrel.2.2 k hk]; rfl

/-- `push` preserves `FEnvCanon` **on an unrestricted view**, and keeps it
unrestricted.  `FEnv.push` stamps the new entry with `visibleBelow` and the
rebuild stamps it with the constant count, so the two agree exactly when
nothing is hidden — which is every index the install routes build
(`mk_fenv`/`dup` then a chain of pushes; `restrict_to` is the only thing that
hides, and no install route calls it between a copy and its pushes). -/
theorem push_canon {fe fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (hwf : FEnvWF fe) (hci : ConstantInfoWF ci) (hcan : FEnvCanon fe)
    (hfull : FEnvFull fe) (h : fenv.push fe ci = ok fe') :
    FEnvCanon fe' ∧ FEnvFull fe' := by
  obtain ⟨hrel, _⟩ := push_refines hcan hwf hci h
  have hlist := push_consts h
  have hvb : fe'.visible_below.val = fe.visible_below.val + 1 := by
    have := hrel.2.1
    simpa [ConLeche.FEnv.push, ConLeche.FEnv.restrictTo] using this
  have hfull' : FEnvFull fe' := by
    unfold FEnvFull
    rw [hvb, hlist, List.length_append, List.length_singleton]
    exact congrArg (· + 1) hfull
  refine ⟨?_, hfull'⟩
  -- the canonical Lean `FEnv` of `fe'` *is* the push of `fe`'s canonical one
  have henv : absEnv fe'.env
      = ⟨absConstantInfo ci :: (absEnv fe.env).consts⟩ := by
    rw [absEnv, absEnv, absConstantInfos, absConstantInfos, hlist]; simp
  have hpush : ((ConLeche.mkFEnv (absEnv fe.env)).restrictTo
        fe.visible_below.val).push (absConstantInfo ci)
      = (ConLeche.mkFEnv (absEnv fe'.env)).restrictTo fe'.visible_below.val := by
    rw [ConLeche.FEnv.push, ConLeche.FEnv.restrictTo, ConLeche.FEnv.restrictTo,
      ConLeche.mkFEnv, ConLeche.mkFEnv, henv, hvb]
    have hcount : (absEnv fe.env).consts.length = fe.visible_below.val := by
      rw [absEnv]; simpa [absConstantInfos] using hfull.symm
    simp only [ConLeche.mkFEnvGo, mkFEnvGo_fst, hcount]
  unfold FEnvCanon
  rw [← hpush]
  exact hrel

/-! ### The index key *is* the stored constant's name (task #59)

`ConLeche/Kernel/Env.lean:636` defines `Env.find? env n = env.consts.find?
(·.name == n)`, so a found record's name is the name it was found under.  The
*indexed* reading cannot see that on its own — `FEnv.find?` reads a hash map,
and `FEnvRel` says nothing about which key a value sits at — but the rebuild
`mkFEnvGo` only ever inserts `ci` at `ci.name`, so it holds of every canonical
view.  `modeled::check_proj_iota_body` needs exactly this: it builds the
constructor spine head from the *looked-up* `cvj.name` where `checkProjIotaF`
writes the name it looked up under. -/

/-- `mkFEnvGo` stores each constant under its own name. -/
theorem mkFEnvGo_name : ∀ (l : List ConLeche.ConstantInfo) {n : ConLeche.Name}
    {p : Nat × ConLeche.ConstantInfo},
    (ConLeche.mkFEnvGo l).2[n]? = some p → p.2.name = n := by
  intro l
  induction l with
  | nil => intro n p h; simp [ConLeche.mkFEnvGo] at h
  | cons ci cs ih =>
    intro n p h
    rw [ConLeche.mkFEnvGo] at h
    by_cases hn : ci.name = n
    · rw [Std.HashMap.getElem?_insert] at h
      rw [if_pos (by simp [hn])] at h
      rw [← Option.some_inj.mp h]; exact hn
    · rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun hc => hn hc)] at h
      exact ih h

/-- **A canonical view answers under the name it stores**: what `Env.find?`'s
`(·.name == n)` gives on the list reading, recovered for the index. -/
theorem canon_find_name {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {ci : ConLeche.ConstantInfo} (hcan : FEnvCanon fe) (hrel : FEnvRel fe lfe)
    (hn : NameWF n) (h : lfe.find? (absName n) = some ci) :
    ci.name = absName n := by
  rw [ConLeche.FEnv.find?] at h
  -- the two indices agree at every well-formed name's image
  have hidx : lfe.idx[absName n]?
      = ((ConLeche.mkFEnv (absEnv fe.env)).restrictTo fe.visible_below.val).idx[absName n]? :=
    (hrel.2.2 n hn).symm.trans (hcan.2.2 n hn)
  rw [hidx] at h
  cases hg : (ConLeche.mkFEnv (absEnv fe.env)).idx[absName n]? with
  | none => rw [show ((ConLeche.mkFEnv (absEnv fe.env)).restrictTo
      fe.visible_below.val).idx = (ConLeche.mkFEnv (absEnv fe.env)).idx from rfl, hg] at h
            simp at h
  | some p =>
    rw [show ((ConLeche.mkFEnv (absEnv fe.env)).restrictTo
      fe.visible_below.val).idx = (ConLeche.mkFEnv (absEnv fe.env)).idx from rfl, hg] at h
    have hname : p.2.name = absName n := mkFEnvGo_name _ hg
    obtain ⟨c, cc⟩ := p
    simp only at h hname
    by_cases hlt : c < lfe.visibleBelow
    · rw [if_pos hlt] at h; rw [← Option.some_inj.mp h]; exact hname
    · rw [if_neg hlt] at h; simp at h

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
constant carries a `native_decide` axiom (task #43).  Task #46 left
`push_refines` a `sorry` because it was false of the model of `Vec::insert`;
task #50 removed that call from the port and the lemma is now in the census
with the rest. -/

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
info: 'ConRon.Refine.FEnv.push_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms push_refines

/--
info: 'ConRon.Refine.FEnv.dup_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms dup_refines

/--
info: 'ConRon.Refine.FEnv.dup_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms dup_rel

/--
info: 'ConRon.Refine.FEnv.restrict_to_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restrict_to_refines

end ConRon.Refine.FEnv
