/-
# `ConRon.Bridge.Compare.Model` — a challenge checked with a solution has a model

The model side of `--compare`, at con-leche's own level: no twin, no store.  con-ron's
Theorem 1 gives the solution's accept as con-leche's PURE fold (`checkDeclsPure`) and the
challenge's as a **mixed run** (`MixedRun`): each record either the pure `checkDecl` step
(a record that offers no statement, `justifiable = none`) or the justification route, as
con-leche's `checkRecordC_justified_run` reads it — the statement justified (`justifyWhy`), its
type's front door (`ConstantValRun`), the reserved names' check, its axiom pushed.

con-leche's soundness of the comparison (`Model/Solution.lean`, `Model/Solution/Fold.lean`) is
stated over its CACHED fold (`DeclsRun`), but every step of it is a pure fact once
`checkDeclStepC_run`/`checkRecordC_justified_run` have run.  So the per-step lemmas are reused as
they are (`justStep`, `sharedStep`, `declStep_agrees`, `new_thm_prop`, `new_proof_leaf`, the
renaming and its copy), and the three folds over them are restated here, over the pure fold and
the mixed run: `sideFoldM` (`sideFold`) and `mixed_model` (`solution_envModel_run`); the pure
fold's is upstream's `pureRun_proofs` at `PureRun.of_foldlM`.

`justifyWhy_of_cone` is `justifyWhy_cone`'s converse: a shared cone covering what the type reads
makes the walk accept at con-leche's fuel.  The twin's walk is related to the cone, not to
con-leche's walk, so no fuel relation between the two walks is needed.
-/
module

public import ConLeche.Cached.Justify
public import ConLeche.Verify.Cached.Cone
public import ConLeche.Semantics.DeclRun
public import ConLeche.Kernel.CheckDecl
public import ConLeche.Kernel.Install
public import ConLeche.Model.Solution.Fold
public import ConLeche.Model.Modular.Step
public import ConLeche.Model.Capstone
public import ConLeche.Model.Fold
public import ConLeche.Verify.Cached.PureRun
import ConLeche.Model.Solution
import ConLeche.Model.Solution.Justified
import ConLeche.Model.Modular.Valid
import ConLeche.Model.Modular.Proofs
import ConLeche.Model.DeclsRun
import ConLeche.Model.CopyStmt
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Cached.Mates
import ConLeche.Verify.Cached.Scoped
import ConLeche.Verify.Cached.JustifyBridge
import ConLeche.Verify.EnvBound
import ConLeche.Semantics.DeclWF
import ConLeche.Semantics.Bridge.DeclRun
import ConLeche.Semantics.Bridge.Sound

public section

namespace ConRon.Bridge.Compare

set_option autoImplicit false

open ConLeche ConLeche.Cached ConLeche.Model ConLeche.Model.Modular ConLeche.Model.Solution
open ConLeche.Verify ConLeche.Semantics SetTheory

universe w

/-! ## The mixed run -/

/-- con-leche: ConLeche/Cached/Justify.lean:200-216 checkRecordC
con-leche: ConLeche/Verify/Cached/JustifyBridge.lean:29 checkRecordC_justified_run — **one record's
step of a fold with a solution**, as pure facts: a record that offers no statement accepted by the
pure `checkDecl`, or a record that offers `cv` justified by `JS`, its type's front door run, the
reserved names' check passed, and its axiom pushed. -/
@[expose] def MixedStep (pinsP : List NatOpPinSet) (JS : Solution) (env : Env) (pd : Declaration)
    (env' : Env) : Prop :=
  (justifiable pd = none ∧
    ∃ F, ConLeche.checkDecl .verified (fueledOps .verified F) pinsP env pd = .ok env') ∨
  (∃ cv, justifiable pd = some cv ∧ env' = ⟨.axiomInfo cv :: env.consts, env.tables⟩ ∧
    justifyWhy JS (mkFEnv env) cv = none ∧ basisNamesOk pd = true ∧
    ∃ F, ConstantValRun F env cv cv.type)

/-- con-leche: ConLeche/Cached/Decls.lean:61-67 DeclsRun — **an accepting run of a fold with a
solution**, as pure steps (`MixedStep`). -/
inductive MixedRun (pinsP : List NatOpPinSet) (JS : Solution) :
    List Declaration → Env → Env → Prop where
  | nil (env : Env) : MixedRun pinsP JS [] env env
  | cons {pd : Declaration} {ds : List Declaration} {env env₁ env' : Env}
      (h : MixedStep pinsP JS env pd env₁) (rest : MixedRun pinsP JS ds env₁ env') :
      MixedRun pinsP JS (pd :: ds) env env'

variable {pinsP : List NatOpPinSet} {JS : Solution}

/-- con-leche: none — two runs, one after the other. -/
theorem MixedRun.append {ds ds' : List Declaration} {e e₁ e₂ : Env}
    (h : MixedRun pinsP JS ds e e₁) (h' : MixedRun pinsP JS ds' e₁ e₂) :
    MixedRun pinsP JS (ds ++ ds') e e₂ := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

/-- con-leche: none — a run one step longer. -/
theorem MixedRun.snoc {ds : List Declaration} {pd : Declaration} {e e₁ e₂ : Env}
    (h : MixedRun pinsP JS ds e e₁) (hs : MixedStep pinsP JS e₁ pd e₂) :
    MixedRun pinsP JS (ds ++ [pd]) e e₂ :=
  h.append (.cons hs (.nil _))

/-- con-leche: ConLeche/Verify/Cached/DeclPushes.lean:756 checkRecordC_pushes — **a step pushes
what its record says, at fresh names**: the pure arm by `checkDecl_pushes`/`checkDecl_fresh`,
the justified arm its one axiom (`justifiable_constants`), fresh by its front door. -/
theorem MixedStep.pushes {env env' : Env} {pd : Declaration}
    (h : MixedStep pinsP JS env pd env') :
    env' = env.pushDelta (declConstants pd) (declTables pd) ∧
      ((declConstants pd).map (·.name)).Nodup ∧
      ∀ c ∈ declConstants pd, env.find? c.name = none := by
  rcases h with ⟨-, F, hF⟩ | ⟨cv, hj, rfl, -, -, F, hrun⟩
  · exact ⟨checkDecl_pushes hF, checkDecl_fresh hF⟩
  · obtain ⟨hc, ht⟩ := justifiable_constants hj
    rw [hc, ht]
    refine ⟨rfl, by simp, fun c hc => ?_⟩
    rw [List.mem_singleton] at hc
    subst hc
    exact Option.isNone_iff_eq_none.mp hrun.1

/-- con-leche: ConLeche/Semantics/DeclWF.lean:327 declsRun_envWF — a step keeps the environment
well formed. -/
theorem MixedStep.envWF {env env' : Env} {pd : Declaration} (hw : EnvWF env)
    (h : MixedStep pinsP JS env pd env') : EnvWF env' := by
  rcases h with ⟨-, F, hF⟩ | ⟨cv, -, rfl, -, -, F, hrun⟩
  · exact checkDecl_envWF hw hF
  · exact hrun.envWF_axiom hw

/-- con-leche: ConLeche/Semantics/DeclWF.lean:327 declsRun_envWF — **a run keeps the
environment well formed**. -/
theorem MixedRun.envWF {ds : List Declaration} {env env' : Env}
    (h : MixedRun pinsP JS ds env env') (hw : EnvWF env) : EnvWF env' := by
  induction h with
  | nil => exact hw
  | cons hs _ ih => exact ih (hs.envWF hw)

/-- con-leche: ConLeche/Verify/Cached/Scoped.lean:771 declsRun_scoped — a step keeps the
environment read-scoped. -/
theorem MixedStep.scoped {env env' : Env} {pd : Declaration} (hw : EnvWF env) (hS : Scoped env)
    (h : MixedStep pinsP JS env pd env') : Scoped env' := by
  have hw₁ := h.envWF hw
  rcases h with ⟨-, F, hF⟩ | ⟨cv, hj, rfl, -, -, F, hrun⟩
  · exact checkDecl_scoped hw hS hF
  · obtain ⟨hop, hred⟩ := justifiable_names hj
    exact hS.cons_of hw₁ (fun _ _ _ _ _ he => nomatch he) (fun _ _ he => nomatch he)
      (footprint_of_nil hop hred)

/-! ## The push chain -/

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean:614 checkRecordC_push — **a step pushing
fresh names extends a fresh chain**: its constants fresh, its tables at its formers' names. -/
theorem not_mem_names_of_find_none {E : Env} {n : Name} (h : E.find? n = none) :
    n ∉ E.consts.map (·.name) := by
  intro hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  unfold Env.find? at h
  have := List.find?_eq_none.mp h c hc
  simp at this

theorem pushChain_step {E₀ E : Env} {pd : Declaration}
    (h : PushChain E₀ (mkFEnv E)) (hnd : ((declConstants pd).map (·.name)).Nodup)
    (hfr : ∀ c ∈ declConstants pd, E.find? c.name = none) :
    PushChain E₀ (mkFEnv (E.pushDelta (declConstants pd) (declTables pd))) := by
  obtain ⟨-, ⟨new, hc, hndn, hfrn⟩, hNd, ⟨newQ, hq, hfrq⟩⟩ := h
  have hE : (mkFEnv E).env = E := rfl
  rw [hE] at hc hq hNd
  have hfr₀ : ∀ c ∈ declConstants pd, E₀.find? c.name = none := fun c hcm =>
    PushChain.find?_none ⟨rfl, ⟨new, hc, hndn, hfrn⟩, hNd, ⟨newQ, hq, hfrq⟩⟩
      (by rw [mkFEnv_find?]; exact hfr c hcm)
  have hdisj : ∀ a ∈ (declConstants pd).reverse.map (·.name), a ∉ E.consts.map (·.name) := by
    intro a ha
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp ha
    exact not_mem_names_of_find_none (hfr c (List.mem_reverse.mp hcm))
  have hndr : ((declConstants pd).reverse.map (·.name)).Nodup := by
    rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.mpr hnd
  refine ⟨rfl, ⟨(declConstants pd).reverse ++ new, ?_, ?_, ?_⟩, ?_, ⟨(declTables pd).reverse ++ newQ, ?_, ?_⟩⟩
  · show (declConstants pd).reverse ++ E.consts = _
    rw [hc, List.append_assoc]
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndr, hndn, fun a ha b hb hab => ?_⟩
    subst hab
    apply hdisj a ha
    rw [hc, List.map_append]
    exact List.mem_append_left _ hb
  · intro c hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · exact hfr₀ c (List.mem_reverse.mp hcm)
    · exact hfrn c hcm
  · intro hnd₀
    have hNE := hNd hnd₀
    show ((declConstants pd).reverse ++ E.consts).map (·.name) |>.Nodup
    rw [List.map_append, List.nodup_append]
    exact ⟨hndr, hNE, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
  · show (declTables pd).reverse ++ E.tables = _
    rw [hq, List.append_assoc]
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨cv, caps, hcm, hn⟩ := declTables_former (List.mem_reverse.mp ht)
      rw [← hn]
      exact hfr₀ _ hcm
    · exact hfrq t ht

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean:631 declsRun_chain — **an accepting run is a
fresh chain**. -/
theorem MixedRun.chain {ds : List Declaration} {E₀ env env' : Env}
    (h : MixedRun pinsP JS ds env env') (hp : PushChain E₀ (mkFEnv env)) :
    PushChain E₀ (mkFEnv env') := by
  induction h with
  | nil => exact hp
  | cons hs _ ih =>
    obtain ⟨he, hnd, hfr⟩ := hs.pushes
    rw [he] at ih
    exact ih (pushChain_step hp hnd hfr)

/-! ## The walk's fuel -/

/-- con-leche: none — counting a property over a list: a weaker property true nowhere else and
false at one member where the stronger holds counts strictly fewer. -/
theorem countP_lt {α : Type} {p q : α → Bool} (hle : ∀ a, q a = true → p a = true) {x : α}
    (hx1 : p x = true) (hx2 : q x = false) :
    ∀ {l : List α}, x ∈ l → l.countP q < l.countP p
  | a :: l, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · have hle' : l.countP q ≤ l.countP p := List.countP_mono_left fun a _ h => hle a h
      simp only [List.countP_cons, hx1, hx2, Bool.false_eq_true, ↓reduceIte]
      omega
    · have ih := countP_lt hle hx1 hx2 hm
      simp only [List.countP_cons]
      by_cases hq : q a = true
      · simp [hq, hle a hq]; omega
      · simp only [hq, Bool.false_eq_true, ↓reduceIte]
        split <;> omega

/-- con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo — **the walk over a shared cone
accepts**: when every name of `work` is seen or of a shared cone `T` whose names are keys of the
solution's index `K`, the walk answers `none` at every fuel at least the number of keys not yet
seen.  Each compared name is a key not seen before and leaves the count one smaller. -/
theorem coneGo_none_of_cone (J : Solution) (find : Name → Option ConstantInfo)
    (findT : Name → Option ProjTable) (T : Name → Prop) (hT : ConeClosed J find findT T)
    (K : List Name) (hK : ∀ n ci, J.idx.find? n = some ci → n ∈ K) :
    ∀ (fuel : Nat) (seen : Std.HashSet Name) (work : List Name),
      (∀ n ∈ work, seen.contains n = true ∨ T n) →
      K.countP (fun k => !seen.contains k) ≤ fuel →
      coneGo J find findT fuel seen work = none := by
  intro fuel seen work
  induction fuel, seen, work using coneGo.induct (J := J) (find := find) (findT := findT) with
  | case1 fuel seen =>
    intro _ _
    rw [coneGo.eq_def]
  | case2 fuel seen n work hs ih =>
    intro hw hc
    rw [coneGo.eq_def]
    simp only [hs, ↓reduceIte]
    exact ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hc
  | case3 seen n work hs =>
    intro hw hc
    exfalso
    have hTn : T n := (hw n List.mem_cons_self).resolve_left hs
    obtain ⟨⟨ci, ci', -, hf', -, -⟩, -⟩ := hT n hTn
    have hmem := hK n ci' hf'
    have : 0 < K.countP (fun k => !seen.contains k) :=
      List.countP_pos_iff.mpr ⟨n, hmem, by simpa using hs⟩
    omega
  | case4 seen n work hs fuel ci ci' hf' hf hok ih =>
    intro hw hc
    rw [coneGo.eq_def]
    simp only [hs, hf, hf', hok, Bool.false_eq_true, ↓reduceIte]
    have hTn : T n := (hw n List.mem_cons_self).resolve_left hs
    refine ih (fun x hx => ?_) ?_
    · rcases List.mem_append.mp hx with hx | hx
      · exact .inr ((hT n hTn).2 ci hf x (Array.mem_toList_iff.mp hx))
      · rcases hw x (List.mem_cons_of_mem _ hx) with h | h
        · left; rw [Std.HashSet.contains_insert]; simp [h]
        · exact .inr h
    · have hlt : K.countP (fun k => !(seen.insert n).contains k) <
          K.countP (fun k => !seen.contains k) := by
        refine countP_lt (x := n) (fun a ha => ?_) (by simpa using hs) (by simp) (hK n ci' hf')
        simp only [Bool.not_eq_true', Std.HashSet.contains_insert, Bool.or_eq_false_iff] at ha ⊢
        exact ha.2
      omega
  | case5 seen n work hs fuel ci ci' hf' hf hok =>
    intro hw _
    exfalso
    have hTn : T n := (hw n List.mem_cons_self).resolve_left hs
    obtain ⟨⟨c, c', h1, h2, h3, h4⟩, -⟩ := hT n hTn
    rw [hf] at h1; rw [hf'] at h2
    obtain rfl := Option.some.inj h1
    obtain rfl := Option.some.inj h2
    simp [h3, h4] at hok
  | case6 seen n work hs fuel hne =>
    intro hw _
    exfalso
    have hTn : T n := (hw n List.mem_cons_self).resolve_left hs
    obtain ⟨⟨c, c', h1, h2, -, -⟩, -⟩ := hT n hTn
    exact hne c c' h1 h2

/-- con-leche: ConLeche/Verify/Cached/Cone.lean:113 justifyWhy_cone — **the converse: a
justified statement**.  The solution's constant of `cv`'s name with `cv`'s statement up to level
names, and a shared cone holding everything `cv`'s type reads, make `justifyWhy` accept, where
every name the solution's index finds is a key of its map (as at `mkFEnv`). -/
theorem justifyWhy_of_cone {J : Solution} {fe : FEnv} {cv : ConstantVal}
    (hK : ∀ n ci, J.idx.find? n = some ci → n ∈ J.idx.idx)
    (h : ∃ cS, J.idx.find? cv.name = some cS ∧ sameCvUpToLevels cv cS.toConstantVal = true ∧
      ∃ T : Name → Prop, ConeClosed J fe.find? fe.findTable? T ∧
        ∀ n ∈ (needsGo {} #[] cv.type).2, T n) :
    justifyWhy J fe cv = none := by
  obtain ⟨cS, hf, hs, T, hT, hn⟩ := h
  unfold justifyWhy
  rw [hf]
  simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [coneGo_none_of_cone J fe.find? fe.findTable? T hT J.idx.idx.keys
    (fun n ci h => Std.HashMap.mem_keys.mpr (hK n ci h)) _ _ _
    (fun n hm => .inr (hn n (Array.mem_toList_iff.mp hm))) ?_]
  calc J.idx.idx.keys.countP _ ≤ J.idx.idx.keys.length := List.countP_le_length
    _ = J.idx.idx.size := Std.HashMap.length_keys
    _ ≤ J.idx.idx.size + 1 := Nat.le_succ _

/-- con-leche: ConLeche/Verify/EnvBound.lean:41 mkFEnv_find? — every name a canonical index finds
is a key of its map. -/
theorem mkFEnv_find_mem {E : Env} {n : Name} {ci : ConstantInfo}
    (h : (mkFEnv E).find? n = some ci) : n ∈ (mkFEnv E).idx := by
  rw [mkFEnv_find?] at h
  have : (mkFEnv E).idx[n]? = some ci := by
    show (mkIdxGo E.consts)[n]? = _
    rw [mkIdxGo_getElem?]
    exact h
  exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [this]; rfl)

/-! ## The models -/

section Models

variable {V : Type w} [SetTheory V]

/-- con-leche: ConLeche/Model/Solution/Fold.lean:98 sideFold — **the input's fold, with the
solution**, over the mixed run: a justified record's step is `justStep` at the justified arm's
facts (con-leche's `checkRecordC_justified_run`'s conclusion, which the arm is), any other record's
`declStep_agrees`/`sharedStep` at its pure `checkDecl` (con-leche's `checkDeclStepC_run`'s); the
push chain, the environment, its well-formedness and scoping are the run's own
(`MixedStep.pushes`, `MixedRun.chain`, `MixedStep.envWF`, `MixedStep.scoped`). -/
theorem sideFoldM {envS Ef : Env} (hJ : JS.idx = mkFEnv envS)
    (mS : EnvModelM V (renEnv Ef envS)) (hcovS : LfpCover mS []) (hNS : NatFacts (renEnv Ef envS))
    (hPLS : ProofLeaves V (renEnv Ef envS) mS.base2.acval)
    (htS : ∀ t ∈ envS.tables, envS.findTable? t.structName = some t ∧
      ∃ cv caps, envS.find? t.structName = some (.indInfo cv caps)) :
    ∀ {ds : List Declaration} {E E' : Env},
      MixedRun pinsP JS ds E E' → E' = Ef →
      (∀ pd ∈ ds, ∀ block nP, pd = .indDecl block nP → ∀ b ∈ block, ∀ b' ∈ block,
        b'.name ∈ JS.mates.getD b.name #[]) →
      ∀ {L : List Declaration}, E = streamEnv L → NodupNames E →
      Scoped E → ∀ mp : EnvModelM V E, LfpCover mp [] → NatFacts E →
      (∀ x, (E.find? x).isSome = true → Shared JS Ef x → mp.base2.acval x = mS.base2.acval x) →
      ∃ mq : EnvModelM V Ef, LfpCover mq [] := by
  intro ds E E' hrun
  induction hrun with
  | nil E =>
    intro hq _ L _ _ _ mp hcov _ _
    subst hq
    exact ⟨mp, hcov⟩
  | @cons pd ds E E₁ E' hstep rest ih =>
    intro hq hmat L hL hnd hscE mp hcov hN hagree
    have hwE : EnvWF E := mp.base2.wf
    have hscE₁ : Scoped E₁ := hstep.scoped hwE hscE
    obtain ⟨he₁, hndd, hfrd⟩ := hstep.pushes
    have hch1 : PushChain E (mkFEnv E₁) := by
      rw [he₁]; exact pushChain_step (PushChain.refl E) hndd hfrd
    have hchR : PushChain E₁ (mkFEnv E') := rest.chain (PushChain.refl E₁)
    have hfe₁ : E₁ = streamEnv (L ++ [pd]) := by
      rw [he₁, ← streamEnv_append, hL]; rfl
    have hnd₁ : NodupNames E₁ := hch1.2.2.1 hnd
    have hwf₁ : EnvWF E₁ := hstep.envWF hwE
    have hold₁ : ∀ x, (E.find? x).isSome = true → E₁.find? x = E.find? x :=
      fun x h => pushChain_find_old hch1 h
    have holdR : ∀ x, (E₁.find? x).isSome = true → Ef.find? x = E₁.find? x := fun x h => by
      rw [← hq]; exact pushChain_find_old hchR h
    have hEF : ∀ x ci, E₁.find? x = some ci → Ef.find? x = some ci := by
      intro x ci h
      rw [holdR x (by rw [h]; rfl), h]
    have hEFt : ∀ x, (E₁.find? x).isSome = true → Ef.findTable? x = E₁.findTable? x :=
      fun x h => by rw [← hq]; exact pushChain_table_old hchR h
    have hEE₁ : ∀ x ci, E.find? x = some ci → E₁.find? x = some ci := fun x ci h => by
      rw [hold₁ x (by rw [h]; rfl), h]
    have hEE₁t : ∀ x, (E.find? x).isSome = true → E₁.findTable? x = E.findTable? x :=
      fun x h => pushChain_table_old hch1 h
    -- the new names are the record's
    have hnew : ∀ x, (E₁.find? x).isSome = true → (E.find? x).isSome = false →
        ∃ c ∈ declConstants pd, c.name = x := by
      intro x hx hxo
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      have hm := Env.find?_mem hc
      rw [he₁] at hm
      simp only [Env.pushDelta, List.mem_append, List.mem_reverse] at hm
      rcases hm with hm | hm
      · exact ⟨c, hm, Env.find?_name hc⟩
      · exfalso
        have : (E.find? c.name).isSome = true := find?_isSome_of_mem' hm
        rw [Env.find?_name hc] at this
        rw [this] at hxo; exact nomatch hxo
    have hmat₁ := hmat pd List.mem_cons_self
    have hmatR : ∀ pd ∈ ds, _ := fun pd' h => hmat pd' (List.mem_cons_of_mem _ h)
    have hst : ∀ c ∈ declConstants pd, Ef.find? c.name = some c := by
      intro c hc
      have : E₁.find? c.name = some c := by
        rw [hfe₁]
        exact streamEnv_find?_of_mem (hfe₁ ▸ hnd₁) (List.mem_append_right _ List.mem_cons_self) hc
      exact hEF _ _ this
    rcases hstep with ⟨hj, F, hF⟩ | ⟨cv, hj, hE₁, hwhy, hb, F, hrunV⟩
    · -- a record's own step
      have hrunD := checkDeclRun_ofEnvFactsK hF
      obtain ⟨⟨mReg, hleafReg, hcovReg, -⟩, hNReg⟩ := declStep_agrees mp hcov hN hrunD
      by_cases hsh : ∃ c ∈ declConstants pd, Shared JS Ef c.name
      · obtain ⟨c, hc, hsc⟩ := hsh
        have hall : ∀ x, (E₁.find? x).isSome = true → (E.find? x).isSome = false →
            Shared JS Ef x := by
          intro x hx hxo
          obtain ⟨c', hc', rfl⟩ := hnew x hx hxo
          exact record_shared hmat₁ hst hc hc' hsc
        have htE : ∀ t ∈ E.tables, E.findTable? t.structName = some t ∧
            ∃ cv caps, E.find? t.structName = some (.indInfo cv caps) := by
          subst hL; exact fun t ht => stream_tables_mem hnd ht
        have hnd₁' : NodupNames (streamEnv (L ++ [pd])) := by rw [← hfe₁]; exact hnd₁
        have htC : ∀ t ∈ E₁.tables, E₁.findTable? t.structName = some t ∧
            ∃ cv caps, E₁.find? t.structName = some (.indInfo cv caps) := by
          rw [hfe₁]; exact fun t ht => stream_tables_mem hnd₁' ht
        obtain ⟨mp', hcov', hN', hold', hnew'⟩ := sharedStep (C := E₁) hJ mp hcov hN mS hcovS
          hNS hagree hEE₁ hEE₁t hEF hEFt hall hnd₁ hscE.entryScopedP hscE₁.entryScopedP
          (fun d cv caps h x hx => by subst hL; exact stream_ctors hnd h x hx)
          (fun d cv caps h x hx => by rw [hfe₁] at h ⊢; exact stream_ctors hnd₁' h x hx)
          htC htE htS
        refine ih hq hmatR (L := L ++ [pd]) hfe₁ hnd₁ hscE₁ mp' hcov' hN' fun x hx hsx => ?_
        by_cases hxo : (E.find? x).isSome = true
        · rw [hold' x hxo]; exact hagree x hxo hsx
        · exact hnew' x hx (by simpa using hxo)
      · refine ih hq hmatR (L := L ++ [pd]) hfe₁ hnd₁ hscE₁ mReg hcovReg hNReg
          fun x hx hsx => ?_
        by_cases hxo : (E.find? x).isSome = true
        · rw [hleafReg x hxo]; exact hagree x hxo hsx
        · obtain ⟨c, hc, rfl⟩ := hnew x hx (by simpa using hxo)
          exact absurd ⟨c, hc, hsx⟩ hsh
    · -- the justification route
      subst hE₁
      have hEf : Ef.find? cv.name = some (.axiomInfo cv) := by
        refine hEF _ _ ?_
        show (ConstantInfo.axiomInfo cv :: E.consts).find? (·.name == cv.name) = _
        simp only [List.find?_cons]
        have : (ConstantInfo.axiomInfo cv).name = cv.name := rfl
        simp [this]
      obtain ⟨mp', hrel, hcov', hN', hleaf⟩ := justStep hJ mp hcov hN mS hPLS hagree
        (fun x ci h => hEF x ci (hEE₁ x ci h))
        (fun x h => (hEFt x (by rw [hold₁ x h]; exact h)).trans (hEE₁t x h))
        hj hwhy hb hrunV hwf₁ hEf
      refine ih hq hmatR (L := L ++ [pd]) hfe₁ hnd₁ hscE₁ mp' hcov' hN' fun x hx hsx => ?_
      by_cases hxo : (E.find? x).isSome = true
      · rw [hrel.leaf x hxo]; exact hagree x hxo hsx
      · obtain ⟨c, hc, hcn⟩ := hnew x hx (by simpa using hxo)
        rw [(justifiable_constants hj).1, List.mem_singleton] at hc
        subst hc
        have hx : cv.name = x := hcn
        subst hx
        exact hleaf hsx

/-- con-leche: ConLeche/Model/Solution.lean:37 solution_envModel_run — **a challenge's mixed run,
with an accepted solution, carries a model**: the solution's accept is the PURE fold
(`pureRun_proofs` at `PureRun.of_foldlM`), the challenge's the mixed
run (`sideFoldM` in place of `sideFold`); the renaming and its copy as con-leche's. -/
theorem mixed_model (V : Type w) [SetTheory V] {F : Nat} {dsS rs : List Declaration}
    (hS : ConLeche.checkDeclsPure .verified (fueledOps .verified F) pinsP dsS =
      .ok (streamEnv dsS))
    (hrun : MixedRun pinsP ⟨mkFEnv (streamEnv dsS), recordMates rs.toArray⟩ rs Env.empty
      (streamEnv rs)) :
    Nonempty (EnvModelM V (streamEnv rs)) := by
  have hS' : dsS.foldlM (ConLeche.checkDecl .verified (fueledOps .verified F) pinsP) Env.empty =
      .ok (streamEnv dsS) := hS
  -- the solution's model
  obtain ⟨mS₀, -, hcovS₀, hNS₀, hPLS₀⟩ := pureRun_proofs (V := V) (PureRun.of_foldlM dsS hS')
    (EnvModelM.empty V) lfpCover_empty (EnvModelOk.empty (V := V)).2 (ProofLeaves.empty (V := V) _)
  have hndS : NodupNames (streamEnv dsS) :=
    ((PureRun.of_foldlM dsS hS').chain (PushChain.refl Env.empty)).2.2.1 List.nodup_nil
  have htS : ∀ t ∈ (streamEnv dsS).tables, (streamEnv dsS).findTable? t.structName = some t ∧
      ∃ cv caps, (streamEnv dsS).find? t.structName = some (.indInfo cv caps) :=
    fun t ht => stream_tables_mem hndS ht
  -- the renamed solution's model
  obtain ⟨mS, hac, hcovS⟩ := EnvModelM.copyStmt mS₀ hcovS₀
    (renEnv_copies (Ef := streamEnv rs) hndS) (renEnv_stmt (streamEnv rs) (streamEnv dsS))
  have hNS : NatFacts (renEnv (streamEnv rs) (streamEnv dsS)) :=
    NatFacts.copies (renEnv_copies hndS) hNS₀
  have hPLS : ProofLeaves V (renEnv (streamEnv rs) (streamEnv dsS)) mS.base2.acval := by
    rw [hac]; exact ProofLeaves.copies mS₀ (renEnv_copies hndS) hPLS₀
  obtain ⟨mq, -⟩ := sideFoldM (JS := ⟨mkFEnv (streamEnv dsS), recordMates rs.toArray⟩)
    (envS := streamEnv dsS) (Ef := streamEnv rs) rfl mS hcovS hNS hPLS htS hrun rfl
    (fun pd hpd block nP he b hb b' hb' => by
      subst he; exact recordMates_spec (by simpa using hpd) hb hb')
    (L := []) rfl List.nodup_nil Scoped.empty
    (EnvModelM.empty V) lfpCover_empty (EnvModelOk.empty (V := V)).2 (fun x hx => nomatch hx)
  exact ⟨mq⟩

end Models

end ConRon.Bridge.Compare
