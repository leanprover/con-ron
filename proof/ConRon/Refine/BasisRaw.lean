/-
`kernel::basis_raw`, refined (DESIGN.md §3.5, task #83).

`crates/con-ron-core/src/kernel/basis_raw.rs` is the port of
`vendor/con-leche/ConLeche/Kernel/Basis/{Eq,Nat,PUnit,Empty,False,Quot}.lean`
and of `ConLeche/Kernel/Basis.lean:40-78` — the **raw** pinned basis blocks
(each block exactly as an export carries it, the toolchain's `Init.Prelude`
declaration at the parser's raw binder annotations) plus the two tests that
recognise one in a stream record.

**Why they are in the verified core.**  Until con-leche's task #293 the
pinned-block match was the *parser's*, and this module lived in the unverified
crate beside it.  Task #293 moved the recognition into the fold: the decoder
emits the file's records and nothing else, and it is `check_decl` that
recognises a block as one of the five pins (`basis_pin_hit`) and a `#QUOT`
record — or the `Quot.sound` axiom record — as the pinned quotient package's
(`quot_pin_hit`).  The match is part of the verdict, so the pins and the two
tests are part of what has to be proved.

**Why there are two tables.**  `ConRon/Refine/BasisTables.lean` refines the
*annotated* blocks (`kernel::basis_tables`, con-leche's `BasisKind.declsA`),
which is what an installation stores; the raw pins below are what an incoming
record is MATCHED against.  They are not the same blocks: `canon` resets binder
metadata and `IndCaps` on both sides but compares a recursor rule's
install-computed fields verbatim, and the annotated `Nat.rec` rule carries
`ctorParams = 2`, `fire = .plain`, `k = true`, `paramsBlind = true` where a
parsed one carries the placeholders.

**The method, and why it is not `BasisTables.lean`'s.**  That file proves its
tables *total* — its claim is about a closed term with no caller, so it has to
be, and it pays for it with a `⦃ ⦄` specification tier and one Aeneas `step`
per interned node.  Every function here *has* a caller inside the checker
(`check_decl` reaches `basis_pin_hit` and `quot_pin_hit` with the Rust success
equation in hand), so the tier's ordinary conditional shape — `(h : rust_f … =
ok v) → abs v = lean_f … ∧ vWF v` — is both what the readers need and far
cheaper: Charon emits one flat `do` chain per pin, one bind per builder call,
so each pin is a `simp only [bind_eq_ok_iff]`, one `obtain`, and one lemma per
bind.  Nothing below needs `step`, a heartbeat bump or a `⦃ ⦄`.

Everything is stated against con-leche's own `BasisDSL` helpers
(`ConLeche/Kernel/Basis/Builder.lean`), which the port carries one-to-one in
`kernel::basis_builder`; the DSL's standing deviation stands here too —
`pi`/`piI`/`piA` are one Rust function and `lm`/`lmI` are one, because `Expr`
carries neither a binder name nor a binder info.
-/
import ConRon.Refine.Canon
import ConRon.Refine.BasisNames
import ConLeche.Kernel.Basis

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.BasisRaw

/-! ## The builder (`kernel::basis_builder`, `BasisDSL`)

Each helper is "a `def` whose body is a single `Expr` constructor application",
so each lemma is one smart-constructor refinement and its `*_wf` twin. -/

/-- `BasisDSL.bn`: a top-level (single-component) name. -/
theorem bn_refines {s : alloc.vec.Vec Std.U32} {n : name.Name}
    (hs : StrWF s) (h : basis_builder.bn s = ok n) :
    absName n = ConLeche.BasisDSL.bn (absString s) ∧ NameWF n := by
  rw [basis_builder.bn] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, hmk⟩ := h
  exact ⟨by rw [Name.mk_str_refines hmk, Name.anonymous_refines ha]; rfl,
    NameWF.str (Name.anonymous_wf ha) hs hmk⟩

/-- `BasisDSL.uN` — the universe parameter `u`. -/
theorem u_n_refines {n : name.Name} (h : basis_builder.u_n = ok n) :
    absName n = ConLeche.BasisDSL.uN ∧ NameWF n := by
  simp only [basis_builder.u_n, basis_builder.bn, bind_eq_ok_iff] at h
  obtain ⟨s, hs, v, hv, a, ha, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [117#u32]) (by simp [basis_builder.u_n.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `BasisDSL.vN` — `Quot.lift`'s target sort parameter. -/
theorem v_n_refines {n : name.Name} (h : basis_builder.v_n = ok n) :
    absName n = ConLeche.BasisDSL.vN ∧ NameWF n := by
  simp only [basis_builder.v_n, basis_builder.bn, bind_eq_ok_iff] at h
  obtain ⟨s, hs, v, hv, a, ha, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [118#u32]) (by simp [basis_builder.v_n.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `BasisDSL.u1N` — the motive sort the exporter names for a recursor whose
type former already spends `u`. -/
theorem u1_n_refines {n : name.Name} (h : basis_builder.u1_n = ok n) :
    absName n = ConLeche.BasisDSL.u1N ∧ NameWF n := by
  simp only [basis_builder.u1_n, basis_builder.bn, bind_eq_ok_iff] at h
  obtain ⟨s, hs, v, hv, a, ha, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [117#u32, 95#u32, 49#u32]) (by simp [basis_builder.u1_n.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

theorem u_refines {l : level.Level} (h : basis_builder.u = ok l) :
    absLevel l = ConLeche.BasisDSL.u ∧ LevelWF l := by
  rw [basis_builder.u] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, hp⟩ := h
  obtain ⟨h1, h1wf⟩ := u_n_refines hn
  exact ⟨by rw [Level.param_refines hp, h1]; rfl, LevelWF.param h1wf hp⟩

theorem v_refines {l : level.Level} (h : basis_builder.v = ok l) :
    absLevel l = ConLeche.BasisDSL.v ∧ LevelWF l := by
  rw [basis_builder.v] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, hp⟩ := h
  obtain ⟨h1, h1wf⟩ := v_n_refines hn
  exact ⟨by rw [Level.param_refines hp, h1]; rfl, LevelWF.param h1wf hp⟩

theorem u1_refines {l : level.Level} (h : basis_builder.u1 = ok l) :
    absLevel l = ConLeche.BasisDSL.u1 ∧ LevelWF l := by
  rw [basis_builder.u1] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, hp⟩ := h
  obtain ⟨h1, h1wf⟩ := u1_n_refines hn
  exact ⟨by rw [Level.param_refines hp, h1]; rfl, LevelWF.param h1wf hp⟩

theorem bv_refines {i : Std.U64} {e : expr.Expr} (h : basis_builder.bv i = ok e) :
    absExpr e = ConLeche.BasisDSL.bv i.val ∧ ExprWF e := by
  rw [basis_builder.bv] at h
  exact ⟨by rw [Expr.bvar_refines h]; rfl, Expr.bvar_wf h⟩

theorem srt_refines {u : level.Level} {e : expr.Expr} (hu : LevelWF u)
    (h : basis_builder.srt u = ok e) :
    absExpr e = ConLeche.BasisDSL.srt (absLevel u) ∧ ExprWF e := by
  rw [basis_builder.srt] at h
  exact ⟨by rw [Expr.sort_refines h]; rfl, Expr.sort_wf hu h⟩

theorem prop_refines {e : expr.Expr} (h : basis_builder.prop = ok e) :
    absExpr e = ConLeche.BasisDSL.prop ∧ ExprWF e := by
  rw [basis_builder.prop] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨l, hl, hs⟩ := h
  exact ⟨by rw [Expr.sort_refines hs, Level.zero_refines hl]; rfl,
    Expr.sort_wf (LevelWF.zero hl) hs⟩

theorem type1_refines {e : expr.Expr} (h : basis_builder.type1 = ok e) :
    absExpr e = ConLeche.BasisDSL.type1 ∧ ExprWF e := by
  rw [basis_builder.type1] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨l, hl, l1, hl1, hs⟩ := h
  exact ⟨by rw [Expr.sort_refines hs, Level.succ_refines hl1, Level.zero_refines hl]; rfl,
    Expr.sort_wf (LevelWF.succ (LevelWF.zero hl) hl1) hs⟩

theorem cnst_refines {n : name.Name} {us : alloc.vec.Vec level.Level} {e : expr.Expr}
    (hn : NameWF n) (hus : LevelsWF us) (h : basis_builder.cnst n us = ok e) :
    absExpr e = ConLeche.BasisDSL.cnst (absName n) (absLevels us) ∧ ExprWF e := by
  rw [basis_builder.cnst] at h
  exact ⟨by rw [Expr.mk_const_refines h]; rfl, Expr.mk_const_wf hn hus h⟩

/-- The `⟨.never⟩` binder datum every raw-pin binder carries (the parse
placeholder: "nothing is known about this codomain's prop-ness"). -/
theorem never_meta_refines {m : expr.BinderMeta} (h : basis_builder.never_meta = ok m) :
    absBinderMeta m = ⟨ConLeche.PropWhen.never⟩ ∧ BinderMetaWF m := by
  rw [basis_builder.never_meta] at h
  simp only [bind_eq_ok_iff, ExprOps.binder_meta_eq, Result.ok.injEq] at h
  obtain ⟨pw, hpw, rfl⟩ := h
  exact ⟨by rw [absBinderMeta, PropWhen.never_refines hpw], PropWhen.never_wf hpw⟩

theorem pi_refines {ty bo e : expr.Expr} (hty : ExprWF ty) (hbo : ExprWF bo)
    (h : basis_builder.pi ty bo = ok e) :
    absExpr e = ConLeche.BasisDSL.piA (absExpr ty) (absExpr bo) ∧ ExprWF e := by
  rw [basis_builder.pi] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m, hm, hf⟩ := h
  obtain ⟨hmabs, hmwf⟩ := never_meta_refines hm
  exact ⟨by rw [Expr.forall_e_refines hf, hmabs]; rfl,
    Expr.forall_e_wf hty hbo hmwf hf⟩

theorem lm_refines {ty bo e : expr.Expr} (hty : ExprWF ty) (hbo : ExprWF bo)
    (h : basis_builder.lm ty bo = ok e) :
    absExpr e = ConLeche.BasisDSL.lm "" (absExpr ty) (absExpr bo) ∧ ExprWF e := by
  rw [basis_builder.lm] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m, hm, hf⟩ := h
  obtain ⟨hmabs, hmwf⟩ := never_meta_refines hm
  exact ⟨by rw [Expr.lam_refines hf, hmabs]; rfl, Expr.lam_wf hty hbo hmwf hf⟩

theorem ap2_refines {f a b e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a) (hb : ExprWF b)
    (h : basis_builder.ap2 f a b = ok e) :
    absExpr e = ConLeche.BasisDSL.ap2 (absExpr f) (absExpr a) (absExpr b) ∧ ExprWF e := by
  rw [basis_builder.ap2] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨by rw [Expr.app_refines hy, Expr.app_refines hx]; rfl,
    Expr.app_wf (Expr.app_wf hf ha hx) hb hy⟩

theorem ap3_refines {f a b c e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a)
    (hb : ExprWF b) (hc : ExprWF c) (h : basis_builder.ap3 f a b c = ok e) :
    absExpr e = ConLeche.BasisDSL.ap3 (absExpr f) (absExpr a) (absExpr b) (absExpr c)
      ∧ ExprWF e := by
  rw [basis_builder.ap3] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨x, hx, hy⟩ := h
  obtain ⟨hxabs, hxwf⟩ := ap2_refines hf ha hb hx
  exact ⟨by rw [Expr.app_refines hy, hxabs]; rfl, Expr.app_wf hxwf hc hy⟩

theorem ap4_refines {f a b c d e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a)
    (hb : ExprWF b) (hc : ExprWF c) (hd : ExprWF d)
    (h : basis_builder.ap4 f a b c d = ok e) :
    absExpr e = ConLeche.BasisDSL.ap4 (absExpr f) (absExpr a) (absExpr b) (absExpr c)
      (absExpr d) ∧ ExprWF e := by
  rw [basis_builder.ap4] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨x, hx, hy⟩ := h
  obtain ⟨hxabs, hxwf⟩ := ap3_refines hf ha hb hc hx
  exact ⟨by rw [Expr.app_refines hy, hxabs]; rfl, Expr.app_wf hxwf hd hy⟩

/-- `expr::app` in the pair shape the pins are read in (`Quot.ind`'s body is
the one place a pin applies a single argument). -/
theorem mk_app_refines {f a e : expr.Expr} (hf : ExprWF f) (ha : ExprWF a)
    (h : expr.app f a = ok e) :
    absExpr e = .app (absExpr f) (absExpr a) ∧ ExprWF e :=
  ⟨by rw [Expr.app_refines h], Expr.app_wf hf ha h⟩

/-! ## `vec!` without the macro, `cv` and `rule`

`basis_raw::vec1`…`vec5` spell the `vec![…]` literal out (§3.4); the lemmas
are about the `Vec`'s list, so one family serves `Vec<Name>`, `Vec<Level>`,
`Vec<RecRule>` and `Vec<ConstantInfo>` alike — `absNames`, `absLevels`,
`absRecRules` and `absConstantInfos` are all `List.map` of that list, and
`NamesWF`, `LevelsWF`, `RecRulesWF` and `ConstantInfosWF` are all "every
entry". -/

theorem vec1_refines {T : Type} {W : T → Prop} {a : T} {v : alloc.vec.Vec T}
    (ha : W a) (h : basis_raw.vec1 a = ok v) : v.val = [a] ∧ ∀ x ∈ v.val, W x := by
  rw [basis_raw.vec1] at h
  have hv := push_new_val h
  exact ⟨hv, by rw [hv]; intro x hx; rw [List.mem_singleton.mp hx]; exact ha⟩

theorem vec2_refines {T : Type} {W : T → Prop} {a b : T} {v : alloc.vec.Vec T}
    (ha : W a) (hb : W b) (h : basis_raw.vec2 a b = ok v) :
    v.val = [a, b] ∧ ∀ x ∈ v.val, W x := by
  rw [basis_raw.vec2] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨w, hw, hp⟩ := h
  have hv : v.val = [a, b] := by rw [vec_push_val hp, (vec1_refines ha hw).1]; rfl
  exact ⟨hv, by rw [hv]; intro x hx; rcases List.mem_cons.mp hx with rfl | hx
                · exact ha
                · rw [List.mem_singleton.mp hx]; exact hb⟩

theorem vec3_refines {T : Type} {W : T → Prop} {a b c : T} {v : alloc.vec.Vec T}
    (ha : W a) (hb : W b) (hc : W c) (h : basis_raw.vec3 a b c = ok v) :
    v.val = [a, b, c] ∧ ∀ x ∈ v.val, W x := by
  rw [basis_raw.vec3] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨w, hw, hp⟩ := h
  have hv : v.val = [a, b, c] := by rw [vec_push_val hp, (vec2_refines ha hb hw).1]; rfl
  refine ⟨hv, ?_⟩
  rw [hv]; intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  · rw [List.mem_singleton.mp hx]; exact hc

theorem vec4_refines {T : Type} {W : T → Prop} {a b c d : T} {v : alloc.vec.Vec T}
    (ha : W a) (hb : W b) (hc : W c) (hd : W d) (h : basis_raw.vec4 a b c d = ok v) :
    v.val = [a, b, c, d] ∧ ∀ x ∈ v.val, W x := by
  rw [basis_raw.vec4] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨w, hw, hp⟩ := h
  have hv : v.val = [a, b, c, d] := by
    rw [vec_push_val hp, (vec3_refines ha hb hc hw).1]; rfl
  refine ⟨hv, ?_⟩
  rw [hv]; intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  · rw [List.mem_singleton.mp hx]; exact hd

theorem vec5_refines {T : Type} {W : T → Prop} {a b c d e : T} {v : alloc.vec.Vec T}
    (ha : W a) (hb : W b) (hc : W c) (hd : W d) (he : W e)
    (h : basis_raw.vec5 a b c d e = ok v) :
    v.val = [a, b, c, d, e] ∧ ∀ x ∈ v.val, W x := by
  rw [basis_raw.vec5] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨w, hw, hp⟩ := h
  have hv : v.val = [a, b, c, d, e] := by
    rw [vec_push_val hp, (vec4_refines ha hb hc hd hw).1]; rfl
  refine ⟨hv, ?_⟩
  rw [hv]; intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hd
  · rw [List.mem_singleton.mp hx]; exact he

/-- `ConstantVal.mk` at the anonymous-constructor literal every pin opens
with. -/
theorem cv_refines {n : name.Name} {lps : alloc.vec.Vec name.Name} {ty : expr.Expr}
    {r : env.ConstantVal} (hn : NameWF n) (hlps : NamesWF lps) (hty : ExprWF ty)
    (h : basis_raw.cv n lps ty = ok r) :
    absConstantVal r = ⟨absName n, absNames lps, absExpr ty⟩ ∧ ConstantValWF r := by
  rw [basis_raw.cv, Result.ok.injEq] at h
  subst h
  exact ⟨rfl, ⟨hn, hlps, hty⟩⟩

/-- `BasisDSL.rule`: a raw iota rule at the parse placeholders. -/
theorem rule_refines {ctor : name.Name} {nfields : Std.U64} {rhs : expr.Expr}
    {r : env.RecRule} (hc : NameWF ctor) (hr : ExprWF rhs)
    (h : basis_raw.rule ctor nfields rhs = ok r) :
    absRecRule r = ConLeche.BasisDSL.rule (absName ctor) nfields.val (absExpr rhs)
      ∧ RecRuleWF r := by
  rw [basis_raw.rule] at h
  exact ⟨by rw [Env.rec_rule_parsed_refines h]; rfl, Env.rec_rule_parsed_wf hc hr h⟩

/-- `env::ind_caps_default` in the pair shape. -/
theorem ind_caps_default_refines {c : env.IndCaps} (h : env.ind_caps_default = ok c) :
    absIndCaps c = ({} : ConLeche.IndCaps) ∧ IndCapsWF c :=
  ⟨Env.ind_caps_default_refines h, Env.ind_caps_default_wf h⟩

/-- The empty `Vec` a pin spells where con-leche writes `[]`: nothing in it,
so every entry is well formed. -/
theorem vec_new_wf {T : Type} {W : T → Prop} : ∀ x ∈ (alloc.vec.Vec.new T).val, W x := by
  intro x hx; simp [alloc.vec.Vec.new] at hx

/-- `name::dup` in the pair shape (`nat_rec_raw` reuses its recursor name). -/
theorem name_dup_refines {n r : name.Name} (hn : NameWF n) (h : name.dup n = ok r) :
    absName r = absName n ∧ NameWF r := by
  rw [name_dup_eq, Result.ok.injEq] at h
  exact ⟨by rw [← h], h ▸ hn⟩

/-- `prop_when::if_all_zero` in the pair shape (`punit_raw`'s `sortZ`). -/
theorem if_all_zero_refines {ps : alloc.vec.Vec name.Name} {pw : prop_when.PropWhen}
    (hps : NamesWF ps) (h : prop_when.if_all_zero ps = ok pw) :
    absPropWhen pw = ConLeche.PropWhen.ifAllZero (absNames ps) ∧ PropWhenWF pw :=
  ⟨PropWhen.if_all_zero_refines hps h, PropWhen.if_all_zero_wf hps h⟩

/-- `{ ic with rule_k := true }`, the one field an `indInfo` pin sets. -/
theorem absIndCaps_rule_k {c : env.IndCaps} (h : absIndCaps c = ({} : ConLeche.IndCaps)) :
    absIndCaps { c with rule_k := true } = { ruleK := true } := by
  rw [show ({ ruleK := true } : ConLeche.IndCaps)
      = { ({} : ConLeche.IndCaps) with ruleK := true } from rfl, ← h]
  rfl

/-- The six fields `punit_raw` sets: `PUnit` is the one pin whose `IndCaps`
is not the default (it is η-capable, unit-like, and `Sort u`-zero exactly
when `u` is). -/
theorem absIndCaps_punit {c : env.IndCaps} {n : name.Name} {pw : prop_when.PropWhen}
    (h : absIndCaps c = ({} : ConLeche.IndCaps)) :
    absIndCaps
        { c with
          eta := true, eta_ctor := n, eta_params := 0#u64,
          eta_fields := 0#u64, unitlike := true, sort_z := pw }
      = { eta := true, etaCtor := absName n, etaParams := 0, etaFields := 0,
          unitlike := true, sortZ := absPropWhen pw } := by
  rw [show
        ({ eta := true, etaCtor := absName n, etaParams := 0, etaFields := 0,
           unitlike := true, sortZ := absPropWhen pw } : ConLeche.IndCaps)
        = { ({} : ConLeche.IndCaps) with
            eta := true, etaCtor := absName n, etaParams := 0, etaFields := 0,
            unitlike := true, sortZ := absPropWhen pw } from rfl, ← h]
  rfl

/-! ## The pins

One lemma per `pub fn` of `basis_raw.rs`, in the module's own order.  Each is
the same three steps: unfold the generated body, peel its flat `do` chain with
`bind_eq_ok_iff`, and compose one lemma per bind.  The closing `simp` unfolds
`BasisDSL` on both sides — the port has one `pi` where con-leche has
`pi`/`piI`/`piA` and one `lm` where it has `lm`/`lmI`, the binder name and
binder info not being part of an `Expr` (con-leche task #205). -/

attribute [local simp] ConLeche.BasisDSL.pi ConLeche.BasisDSL.piI ConLeche.BasisDSL.piA
  ConLeche.BasisDSL.lm ConLeche.BasisDSL.lmI ConLeche.BasisDSL.bv ConLeche.BasisDSL.srt
  ConLeche.BasisDSL.prop ConLeche.BasisDSL.type1 ConLeche.BasisDSL.cnst
  ConLeche.BasisDSL.ap2 ConLeche.BasisDSL.ap3 ConLeche.BasisDSL.ap4
  ConLeche.BasisDSL.rule

/-! ### `Eq` -/

/-- `ConLeche/Kernel/Basis/Eq.lean:22-28 eqRaw` -/
theorem eq_raw_refines {ci : env.ConstantInfo} (h : basis_raw.eq_raw = ok ci) :
    absConstantInfo ci = ConLeche.eqRaw ∧ ConstantInfoWF ci := by
  rw [basis_raw.eq_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨ic, hic, n, hn, n1, hn1, v, hv, l, hl, e, he, e1, he1, e2, he2, e3, he3,
    e4, he4, e5, he5, e6, he6, cv, hcv, rfl⟩ := h
  obtain ⟨aic, wic⟩ := ind_caps_default_refines hic
  obtain ⟨an, wn⟩ := BasisNames.eq_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨ae2, we2⟩ := bv_refines he2
  obtain ⟨ae3, we3⟩ := prop_refines he3
  obtain ⟨ae4, we4⟩ := pi_refines we2 we3 he4
  obtain ⟨ae5, we5⟩ := pi_refines we1 we4 he5
  obtain ⟨ae6, we6⟩ := pi_refines we we5 he6
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we6 hcv
  refine ⟨?_, ⟨wcv, wic⟩⟩
  simp [absConstantInfo, acv, an, ae6, ae5, ae4, ae3, ae2, ae1, ae, al, an1,
    absNames, av, absIndCaps_rule_k aic, ConLeche.eqRaw]

theorem eq_refl_raw_refines {r : env.ConstantInfo} (h : basis_raw.eq_refl_raw = ok r) :
    absConstantInfo r = ConLeche.eqReflRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.eq_refl_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, v, hv, l, hl, e, he, e1, he1, n2, hn2, v1, hv1, e2, he2, e3, he3,
    e4, he4, e5, he5, e6, he6, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.eq_refl_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨an2, wn2⟩ := BasisNames.eq_name_refines hn2
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae2, we2⟩ := cnst_refines wn2 wv1 he2
  obtain ⟨ae3, we3⟩ := bv_refines he3
  obtain ⟨ae4, we4⟩ := ap3_refines we2 we3 we1 we1 he4
  obtain ⟨ae5, we5⟩ := pi_refines we1 we4 he5
  obtain ⟨ae6, we6⟩ := pi_refines we we5 he6
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we6 hcv
  refine ⟨?_, wcv⟩
  simp [absConstantInfo, absNames, absLevels, acv, ae6, ae5, ae4, ae3, ae2, av1, an2, ae1, ae, al, av, an1, an,
    ConLeche.eqReflRaw]

theorem eq_rec_motive_refines {r : expr.Expr} (h : basis_raw.eq_rec_motive = ok r) :
    absExpr r = ConLeche.eqRecMotive ∧ ExprWF r := by
  rw [basis_raw.eq_rec_motive] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, n, hn, l, hl, v, hv, e1, he1, e2, he2, e3, he3, e4, he4, l1, hl1, e5, he5,
    e6, he6, hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨an, wn⟩ := BasisNames.eq_name_refines hn
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av, wv⟩ := vec1_refines wl hv
  obtain ⟨ae1, we1⟩ := cnst_refines wn wv he1
  obtain ⟨ae2, we2⟩ := bv_refines he2
  obtain ⟨ae3, we3⟩ := bv_refines he3
  obtain ⟨ae4, we4⟩ := ap3_refines we1 we2 we we3 he4
  obtain ⟨al1, wl1⟩ := u1_refines hl1
  obtain ⟨ae5, we5⟩ := srt_refines wl1 he5
  obtain ⟨ae6, we6⟩ := pi_refines we4 we5 he6
  obtain ⟨ares, wres⟩ := pi_refines we we6 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae6, ae5, al1, ae4, ae3, ae2, ae1, av, al, an, ae,
    ConLeche.eqRecMotive]

theorem eq_rec_refl_dom_refines {r : expr.Expr} (h : basis_raw.eq_rec_refl_dom = ok r) :
    absExpr r = ConLeche.BasisDSL.ap2 (ConLeche.BasisDSL.bv 0) (ConLeche.BasisDSL.bv 1)
        (ConLeche.BasisDSL.ap2 (ConLeche.BasisDSL.cnst ConLeche.eqReflName [ConLeche.BasisDSL.u])
          (ConLeche.BasisDSL.bv 2) (ConLeche.BasisDSL.bv 1))
      ∧ ExprWF r := by
  rw [basis_raw.eq_rec_refl_dom] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, e1, he1, n, hn, l, hl, v, hv, e2, he2, e3, he3, e4, he4, hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨an, wn⟩ := BasisNames.eq_refl_name_refines hn
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av, wv⟩ := vec1_refines wl hv
  obtain ⟨ae2, we2⟩ := cnst_refines wn wv he2
  obtain ⟨ae3, we3⟩ := bv_refines he3
  obtain ⟨ae4, we4⟩ := ap2_refines we2 we3 we1 he4
  obtain ⟨ares, wres⟩ := ap2_refines we we1 we4 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae4, ae3, ae2, av, al, an, ae1, ae,
    ConLeche.BasisDSL.ap2, ConLeche.BasisDSL.cnst]

theorem eq_rec_raw_refines {r : env.ConstantInfo} (h : basis_raw.eq_rec_raw = ok r) :
    absConstantInfo r = ConLeche.eqRecRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.eq_rec_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, n2, hn2, n3, hn3, v, hv, l, hl, e, he, e1, he1, e2, he2, e3, he3,
    e4, he4, v1, hv1, e5, he5, e6, he6, e7, he7, e8, he8, e9, he9, e10, he10, e11, he11,
    e12, he12, e13, he13, e14, he14, e15, he15, cv, hcv, n4, hn4, e16, he16, e17, he17,
    e18, he18, e19, he19, e20, he20, rr, hrr, v2, hv2, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.eq_name_refines hn
  obtain ⟨an1, wn1⟩ := BasisNames.rec_of_refines wn hn1
  obtain ⟨an2, wn2⟩ := u1_n_refines hn2
  obtain ⟨an3, wn3⟩ := u_n_refines hn3
  obtain ⟨av, wv⟩ := vec2_refines wn2 wn3 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨ae2, we2⟩ := eq_rec_motive_refines he2
  obtain ⟨ae3, we3⟩ := eq_rec_refl_dom_refines he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae5, we5⟩ := cnst_refines wn wv1 he5
  obtain ⟨ae6, we6⟩ := bv_refines he6
  obtain ⟨ae7, we7⟩ := ap3_refines we5 we6 we4 we1 he7
  obtain ⟨ae8, we8⟩ := bv_refines he8
  obtain ⟨ae9, we9⟩ := ap2_refines we4 we8 we1 he9
  obtain ⟨ae10, we10⟩ := pi_refines we7 we9 he10
  obtain ⟨ae11, we11⟩ := pi_refines we4 we10 he11
  obtain ⟨ae12, we12⟩ := pi_refines we3 we11 he12
  obtain ⟨ae13, we13⟩ := pi_refines we2 we12 he13
  obtain ⟨ae14, we14⟩ := pi_refines we1 we13 he14
  obtain ⟨ae15, we15⟩ := pi_refines we we14 he15
  obtain ⟨acv, wcv⟩ := cv_refines wn1 wv we15 hcv
  obtain ⟨an4, wn4⟩ := BasisNames.eq_refl_name_refines hn4
  obtain ⟨ae16, we16⟩ := srt_refines wl he16
  obtain ⟨ae17, we17⟩ := lm_refines we3 we1 he17
  obtain ⟨ae18, we18⟩ := lm_refines we2 we17 he18
  obtain ⟨ae19, we19⟩ := lm_refines we1 we18 he19
  obtain ⟨ae20, we20⟩ := lm_refines we16 we19 he20
  obtain ⟨arr, wrr⟩ := rule_refines wn4 we20 hrr
  obtain ⟨av2, wv2⟩ := vec1_refines wrr hv2
  refine ⟨?_, ⟨wcv, wv2⟩⟩
  simp [absConstantInfo, absNames, absLevels, av2, arr, ae20, ae19, ae18, ae17, ae16, an4, acv, ae15, ae14, ae13, ae12, ae11, ae10, ae9, ae8, ae7, ae6, ae5, av1, ae4, ae3, ae2, ae1, ae, al, av, an3, an2, an1, an,
    ConLeche.eqRecRaw]

theorem eq_basis_refines {r : alloc.vec.Vec env.ConstantInfo} (h : basis_raw.eq_basis = ok r) :
    absConstantInfos r = ConLeche.eqBasis ∧ ConstantInfosWF r := by
  rw [basis_raw.eq_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, ci1, hci1, ci2, hci2, hres⟩ := h
  obtain ⟨aci, wci⟩ := eq_raw_refines hci
  obtain ⟨aci1, wci1⟩ := eq_refl_raw_refines hci1
  obtain ⟨aci2, wci2⟩ := eq_rec_raw_refines hci2
  obtain ⟨ares, wres⟩ := vec3_refines wci wci1 wci2 hres
  refine ⟨?_, wres⟩
  simp [absConstantInfos, absConstantInfos, ares, aci2, aci1, aci,
    ConLeche.eqBasis]

theorem nat_t_refines {r : expr.Expr} (h : basis_raw.nat_t = ok r) :
    absExpr r = ConLeche.natT ∧ ExprWF r := by
  rw [basis_raw.nat_t] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, hres⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.nat_name_refines hn
  obtain ⟨ares, wres⟩ := cnst_refines wn vec_new_wf hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, an,
    ConLeche.natT]

theorem nat_raw_refines {r : env.ConstantInfo} (h : basis_raw.nat_raw = ok r) :
    absConstantInfo r = ConLeche.natRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.nat_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, cv, hcv, ic, hic, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.nat_name_refines hn
  obtain ⟨ae, we⟩ := type1_refines he
  obtain ⟨acv, wcv⟩ := cv_refines wn vec_new_wf we hcv
  obtain ⟨aic, wic⟩ := ind_caps_default_refines hic
  refine ⟨?_, ⟨wcv, wic⟩⟩
  simp [absConstantInfo, absNames, aic, acv, ae, an,
    ConLeche.natRaw]

theorem nat_zero_raw_refines {r : env.ConstantInfo} (h : basis_raw.nat_zero_raw = ok r) :
    absConstantInfo r = ConLeche.natZeroRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.nat_zero_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.nat_zero_name_refines hn
  obtain ⟨ae, we⟩ := nat_t_refines he
  obtain ⟨acv, wcv⟩ := cv_refines wn vec_new_wf we hcv
  refine ⟨?_, wcv⟩
  simp [absConstantInfo, absNames, acv, ae, an,
    ConLeche.natZeroRaw]

theorem nat_succ_raw_refines {r : env.ConstantInfo} (h : basis_raw.nat_succ_raw = ok r) :
    absConstantInfo r = ConLeche.natSuccRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.nat_succ_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, e1, he1, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.nat_succ_name_refines hn
  obtain ⟨ae, we⟩ := nat_t_refines he
  obtain ⟨ae1, we1⟩ := pi_refines we we he1
  obtain ⟨acv, wcv⟩ := cv_refines wn vec_new_wf we1 hcv
  refine ⟨?_, wcv⟩
  simp [absConstantInfo, absNames, acv, ae1, ae, an,
    ConLeche.natSuccRaw]

theorem nat_rec_motive_refines {r : expr.Expr} (h : basis_raw.nat_rec_motive = ok r) :
    absExpr r = ConLeche.natRecMotive ∧ ExprWF r := by
  rw [basis_raw.nat_rec_motive] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, l, hl, e1, he1, hres⟩ := h
  obtain ⟨ae, we⟩ := nat_t_refines he
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae1, we1⟩ := srt_refines wl he1
  obtain ⟨ares, wres⟩ := pi_refines we we1 hres
  refine ⟨?_, wres⟩
  simp [ares, ae1, al, ae,
    ConLeche.natRecMotive]

theorem nat_rec_succ_refines {r : expr.Expr} (h : basis_raw.nat_rec_succ = ok r) :
    absExpr r = ConLeche.natRecSucc ∧ ExprWF r := by
  rw [basis_raw.nat_rec_succ] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, e1, he1, e2, he2, e3, he3, e4, he4, n, hn, e5, he5, e6, he6, e7, he7, e8,
    he8, e9, he9, hres⟩ := h
  obtain ⟨ae, we⟩ := nat_t_refines he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨ae2, we2⟩ := bv_refines he2
  obtain ⟨ae3, we3⟩ := mk_app_refines we1 we2 he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨an, wn⟩ := BasisNames.nat_succ_name_refines hn
  obtain ⟨ae5, we5⟩ := cnst_refines wn vec_new_wf he5
  obtain ⟨ae6, we6⟩ := bv_refines he6
  obtain ⟨ae7, we7⟩ := mk_app_refines we5 we6 he7
  obtain ⟨ae8, we8⟩ := mk_app_refines we4 we7 he8
  obtain ⟨ae9, we9⟩ := pi_refines we3 we8 he9
  obtain ⟨ares, wres⟩ := pi_refines we we9 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae9, ae8, ae7, ae6, ae5, an, ae4, ae3, ae2, ae1, ae,
    ConLeche.natRecSucc]

theorem nat_rec_zero_dom_refines {r : expr.Expr} (h : basis_raw.nat_rec_zero_dom = ok r) :
    absExpr r = .app (ConLeche.BasisDSL.bv 0)
        (ConLeche.BasisDSL.cnst ConLeche.natZeroName []) ∧ ExprWF r := by
  rw [basis_raw.nat_rec_zero_dom] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, n, hn, e1, he1, hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨an, wn⟩ := BasisNames.nat_zero_name_refines hn
  obtain ⟨ae1, we1⟩ := cnst_refines wn vec_new_wf he1
  obtain ⟨ares, wres⟩ := mk_app_refines we we1 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae1, an, ae,
    ConLeche.BasisDSL.cnst]

theorem nat_rec_raw_refines {r : env.ConstantInfo} (h : basis_raw.nat_rec_raw = ok r) :
    absConstantInfo r = ConLeche.natRecRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.nat_rec_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, rec_name, hrec_name, n1, hn1, n2, hn2, v, hv, e, he, e1, he1, e2, he2, e3,
    he3, e4, he4, e5, he5, e6, he6, e7, he7, e8, he8, e9, he9, e10, he10, cv, hcv, n3, hn3,
    e11, he11, e12, he12, e13, he13, e14, he14, rr, hrr, n4, hn4, l, hl, v1, hv1, e15,
    he15, e16, he16, e17, he17, e18, he18, e19, he19, e20, he20, e21, he21, e22, he22, e23,
    he23, rr1, hrr1, v2, hv2, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.nat_name_refines hn
  obtain ⟨arec_name, wrec_name⟩ := BasisNames.rec_of_refines wn hrec_name
  obtain ⟨an1, wn1⟩ := name_dup_refines wrec_name hn1
  obtain ⟨an2, wn2⟩ := u_n_refines hn2
  obtain ⟨av, wv⟩ := vec1_refines wn2 hv
  obtain ⟨ae, we⟩ := nat_rec_motive_refines he
  obtain ⟨ae1, we1⟩ := nat_rec_zero_dom_refines he1
  obtain ⟨ae2, we2⟩ := nat_rec_succ_refines he2
  obtain ⟨ae3, we3⟩ := nat_t_refines he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨ae5, we5⟩ := bv_refines he5
  obtain ⟨ae6, we6⟩ := mk_app_refines we4 we5 he6
  obtain ⟨ae7, we7⟩ := pi_refines we3 we6 he7
  obtain ⟨ae8, we8⟩ := pi_refines we2 we7 he8
  obtain ⟨ae9, we9⟩ := pi_refines we1 we8 he9
  obtain ⟨ae10, we10⟩ := pi_refines we we9 he10
  obtain ⟨acv, wcv⟩ := cv_refines wn1 wv we10 hcv
  obtain ⟨an3, wn3⟩ := BasisNames.nat_zero_name_refines hn3
  obtain ⟨ae11, we11⟩ := bv_refines he11
  obtain ⟨ae12, we12⟩ := lm_refines we2 we11 he12
  obtain ⟨ae13, we13⟩ := lm_refines we1 we12 he13
  obtain ⟨ae14, we14⟩ := lm_refines we we13 he14
  obtain ⟨arr, wrr⟩ := rule_refines wn3 we14 hrr
  obtain ⟨an4, wn4⟩ := BasisNames.nat_succ_name_refines hn4
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae15, we15⟩ := cnst_refines wn1 wv1 he15
  obtain ⟨ae16, we16⟩ := bv_refines he16
  obtain ⟨ae17, we17⟩ := ap3_refines we15 we4 we16 we11 he17
  obtain ⟨ae18, we18⟩ := mk_app_refines we17 we5 he18
  obtain ⟨ae19, we19⟩ := ap2_refines we11 we5 we18 he19
  obtain ⟨ae20, we20⟩ := lm_refines we3 we19 he20
  obtain ⟨ae21, we21⟩ := lm_refines we2 we20 he21
  obtain ⟨ae22, we22⟩ := lm_refines we1 we21 he22
  obtain ⟨ae23, we23⟩ := lm_refines we we22 he23
  obtain ⟨arr1, wrr1⟩ := rule_refines wn4 we23 hrr1
  obtain ⟨av2, wv2⟩ := vec2_refines wrr wrr1 hv2
  refine ⟨?_, ⟨wcv, wv2⟩⟩
  simp [absConstantInfo, absNames, absLevels, av2, arr1, ae23, ae22, ae21, ae20, ae19, ae18, ae17, ae16, ae15, av1, al, an4, arr, ae14, ae13, ae12, ae11, an3, acv, ae10, ae9, ae8, ae7, ae6, ae5, ae4, ae3, ae2, ae1, ae, av, an2, an1, arec_name, an,
    ConLeche.natRecRaw]

theorem nat_basis_refines {r : alloc.vec.Vec env.ConstantInfo} (h : basis_raw.nat_basis = ok r) :
    absConstantInfos r = ConLeche.natBasis ∧ ConstantInfosWF r := by
  rw [basis_raw.nat_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, ci1, hci1, ci2, hci2, ci3, hci3, hres⟩ := h
  obtain ⟨aci, wci⟩ := nat_raw_refines hci
  obtain ⟨aci1, wci1⟩ := nat_zero_raw_refines hci1
  obtain ⟨aci2, wci2⟩ := nat_succ_raw_refines hci2
  obtain ⟨aci3, wci3⟩ := nat_rec_raw_refines hci3
  obtain ⟨ares, wres⟩ := vec4_refines wci wci1 wci2 wci3 hres
  refine ⟨?_, wres⟩
  simp [absConstantInfos, absConstantInfos, ares, aci3, aci2, aci1, aci,
    ConLeche.natBasis]

theorem punit_raw_refines {r : env.ConstantInfo} (h : basis_raw.punit_raw = ok r) :
    absConstantInfo r = ConLeche.punitRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.punit_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, v, hv, pw, hpw, ic, hic, n2, hn2, v1, hv1, l, hl, e, he, cv, hcv,
    rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.punit_unit_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨apw, wpw⟩ := if_all_zero_refines wv hpw
  obtain ⟨aic, wic⟩ := ind_caps_default_refines hic
  obtain ⟨an2, wn2⟩ := BasisNames.punit_name_refines hn2
  obtain ⟨av1, wv1⟩ := vec1_refines wn1 hv1
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨acv, wcv⟩ := cv_refines wn2 wv1 we hcv
  refine ⟨?_, ⟨wcv, ⟨wn, wpw⟩⟩⟩
  simp [absConstantInfo, absNames, acv, ae, al, av1, an2,
    absIndCaps_punit aic, apw, av, an1, an, ConLeche.punitRaw]

theorem punit_unit_raw_refines {r : env.ConstantInfo} (h : basis_raw.punit_unit_raw = ok r) :
    absConstantInfo r = ConLeche.punitUnitRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.punit_unit_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, v, hv, n2, hn2, l, hl, v1, hv1, e, he, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.punit_unit_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨an2, wn2⟩ := BasisNames.punit_name_refines hn2
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae, we⟩ := cnst_refines wn2 wv1 he
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we hcv
  refine ⟨?_, wcv⟩
  simp [absConstantInfo, absNames, absLevels, acv, ae, av1, al, an2, av, an1, an,
    ConLeche.punitUnitRaw]

theorem punit_rec_motive_refines {r : expr.Expr} (h : basis_raw.punit_rec_motive = ok r) :
    absExpr r = ConLeche.punitRecMotive ∧ ExprWF r := by
  rw [basis_raw.punit_rec_motive] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, l, hl, v, hv, e, he, l1, hl1, e1, he1, hres⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.punit_name_refines hn
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av, wv⟩ := vec1_refines wl hv
  obtain ⟨ae, we⟩ := cnst_refines wn wv he
  obtain ⟨al1, wl1⟩ := u1_refines hl1
  obtain ⟨ae1, we1⟩ := srt_refines wl1 he1
  obtain ⟨ares, wres⟩ := pi_refines we we1 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae1, al1, ae, av, al, an,
    ConLeche.punitRecMotive]

theorem punit_rec_unit_dom_refines {r : expr.Expr} (h : basis_raw.punit_rec_unit_dom = ok r) :
    absExpr r = .app (ConLeche.BasisDSL.bv 0)
        (ConLeche.BasisDSL.cnst ConLeche.punitUnitName [ConLeche.BasisDSL.u]) ∧ ExprWF r := by
  rw [basis_raw.punit_rec_unit_dom] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, n, hn, l, hl, v, hv, e1, he1, hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨an, wn⟩ := BasisNames.punit_unit_name_refines hn
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av, wv⟩ := vec1_refines wl hv
  obtain ⟨ae1, we1⟩ := cnst_refines wn wv he1
  obtain ⟨ares, wres⟩ := mk_app_refines we we1 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae1, av, al, an, ae,
    ConLeche.BasisDSL.cnst]

theorem punit_rec_raw_refines {r : env.ConstantInfo} (h : basis_raw.punit_rec_raw = ok r) :
    absConstantInfo r = ConLeche.punitRecRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.punit_rec_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, n2, hn2, v, hv, e, he, e1, he1, n3, hn3, l, hl, v1, hv1, e2, he2,
    e3, he3, e4, he4, e5, he5, e6, he6, e7, he7, e8, he8, cv, hcv, n4, hn4, e9, he9, e10,
    he10, rr, hrr, v2, hv2, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.punit_rec_name_refines hn
  obtain ⟨an1, wn1⟩ := u1_n_refines hn1
  obtain ⟨an2, wn2⟩ := u_n_refines hn2
  obtain ⟨av, wv⟩ := vec2_refines wn1 wn2 hv
  obtain ⟨ae, we⟩ := punit_rec_motive_refines he
  obtain ⟨ae1, we1⟩ := punit_rec_unit_dom_refines he1
  obtain ⟨an3, wn3⟩ := BasisNames.punit_name_refines hn3
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae2, we2⟩ := cnst_refines wn3 wv1 he2
  obtain ⟨ae3, we3⟩ := bv_refines he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨ae5, we5⟩ := mk_app_refines we3 we4 he5
  obtain ⟨ae6, we6⟩ := pi_refines we2 we5 he6
  obtain ⟨ae7, we7⟩ := pi_refines we1 we6 he7
  obtain ⟨ae8, we8⟩ := pi_refines we we7 he8
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we8 hcv
  obtain ⟨an4, wn4⟩ := BasisNames.punit_unit_name_refines hn4
  obtain ⟨ae9, we9⟩ := lm_refines we1 we4 he9
  obtain ⟨ae10, we10⟩ := lm_refines we we9 he10
  obtain ⟨arr, wrr⟩ := rule_refines wn4 we10 hrr
  obtain ⟨av2, wv2⟩ := vec1_refines wrr hv2
  refine ⟨?_, ⟨wcv, wv2⟩⟩
  simp [absConstantInfo, absNames, absLevels, av2, arr, ae10, ae9, an4, acv, ae8, ae7, ae6, ae5, ae4, ae3, ae2, av1, al, an3, ae1, ae, av, an2, an1, an,
    ConLeche.punitRecRaw]

theorem punit_basis_refines {r : alloc.vec.Vec env.ConstantInfo} (h : basis_raw.punit_basis = ok r) :
    absConstantInfos r = ConLeche.punitBasis ∧ ConstantInfosWF r := by
  rw [basis_raw.punit_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, ci1, hci1, ci2, hci2, hres⟩ := h
  obtain ⟨aci, wci⟩ := punit_raw_refines hci
  obtain ⟨aci1, wci1⟩ := punit_unit_raw_refines hci1
  obtain ⟨aci2, wci2⟩ := punit_rec_raw_refines hci2
  obtain ⟨ares, wres⟩ := vec3_refines wci wci1 wci2 hres
  refine ⟨?_, wres⟩
  simp [absConstantInfos, absConstantInfos, ares, aci2, aci1, aci,
    ConLeche.punitBasis]

theorem empty_raw_refines {r : env.ConstantInfo} (h : basis_raw.empty_raw = ok r) :
    absConstantInfo r = ConLeche.emptyRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.empty_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, cv, hcv, ic, hic, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.empty_name_refines hn
  obtain ⟨ae, we⟩ := type1_refines he
  obtain ⟨acv, wcv⟩ := cv_refines wn vec_new_wf we hcv
  obtain ⟨aic, wic⟩ := ind_caps_default_refines hic
  refine ⟨?_, ⟨wcv, wic⟩⟩
  simp [absConstantInfo, absNames, aic, acv, ae, an,
    ConLeche.emptyRaw]

theorem empty_rec_raw_refines {r : env.ConstantInfo} (h : basis_raw.empty_rec_raw = ok r) :
    absConstantInfo r = ConLeche.emptyRecRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.empty_rec_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, n2, hn2, v, hv, e, he, l, hl, e1, he1, e2, he2, e3, he3, e4, he4,
    e5, he5, e6, he6, e7, he7, e8, he8, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.empty_name_refines hn
  obtain ⟨an1, wn1⟩ := BasisNames.rec_of_refines wn hn1
  obtain ⟨an2, wn2⟩ := u_n_refines hn2
  obtain ⟨av, wv⟩ := vec1_refines wn2 hv
  obtain ⟨ae, we⟩ := cnst_refines wn vec_new_wf he
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae1, we1⟩ := srt_refines wl he1
  obtain ⟨ae2, we2⟩ := pi_refines we we1 he2
  obtain ⟨ae3, we3⟩ := cnst_refines wn vec_new_wf he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨ae5, we5⟩ := bv_refines he5
  obtain ⟨ae6, we6⟩ := mk_app_refines we4 we5 he6
  obtain ⟨ae7, we7⟩ := pi_refines we3 we6 he7
  obtain ⟨ae8, we8⟩ := pi_refines we2 we7 he8
  obtain ⟨acv, wcv⟩ := cv_refines wn1 wv we8 hcv
  refine ⟨?_, ⟨wcv, vec_new_wf⟩⟩
  simp [absConstantInfo, absNames, absLevels, acv, ae8, ae7, ae6, ae5, ae4, ae3, ae2, ae1, al, ae, av, an2, an1, an,
    ConLeche.emptyRecRaw]

theorem empty_basis_refines {r : alloc.vec.Vec env.ConstantInfo} (h : basis_raw.empty_basis = ok r) :
    absConstantInfos r = ConLeche.emptyBasis ∧ ConstantInfosWF r := by
  rw [basis_raw.empty_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, ci1, hci1, hres⟩ := h
  obtain ⟨aci, wci⟩ := empty_raw_refines hci
  obtain ⟨aci1, wci1⟩ := empty_rec_raw_refines hci1
  obtain ⟨ares, wres⟩ := vec2_refines wci wci1 hres
  refine ⟨?_, wres⟩
  simp [absConstantInfos, absConstantInfos, ares, aci1, aci,
    ConLeche.emptyBasis]

theorem false_raw_refines {r : env.ConstantInfo} (h : basis_raw.false_raw = ok r) :
    absConstantInfo r = ConLeche.falseRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.false_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, e, he, cv, hcv, ic, hic, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.false_name_refines hn
  obtain ⟨ae, we⟩ := prop_refines he
  obtain ⟨acv, wcv⟩ := cv_refines wn vec_new_wf we hcv
  obtain ⟨aic, wic⟩ := ind_caps_default_refines hic
  refine ⟨?_, ⟨wcv, wic⟩⟩
  simp [absConstantInfo, absNames, aic, acv, ae, an,
    ConLeche.falseRaw]

theorem false_rec_raw_refines {r : env.ConstantInfo} (h : basis_raw.false_rec_raw = ok r) :
    absConstantInfo r = ConLeche.falseRecRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.false_rec_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, n2, hn2, v, hv, e, he, l, hl, e1, he1, e2, he2, e3, he3, e4, he4,
    e5, he5, e6, he6, e7, he7, e8, he8, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.false_name_refines hn
  obtain ⟨an1, wn1⟩ := BasisNames.rec_of_refines wn hn1
  obtain ⟨an2, wn2⟩ := u_n_refines hn2
  obtain ⟨av, wv⟩ := vec1_refines wn2 hv
  obtain ⟨ae, we⟩ := cnst_refines wn vec_new_wf he
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae1, we1⟩ := srt_refines wl he1
  obtain ⟨ae2, we2⟩ := pi_refines we we1 he2
  obtain ⟨ae3, we3⟩ := cnst_refines wn vec_new_wf he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨ae5, we5⟩ := bv_refines he5
  obtain ⟨ae6, we6⟩ := mk_app_refines we4 we5 he6
  obtain ⟨ae7, we7⟩ := pi_refines we3 we6 he7
  obtain ⟨ae8, we8⟩ := pi_refines we2 we7 he8
  obtain ⟨acv, wcv⟩ := cv_refines wn1 wv we8 hcv
  refine ⟨?_, ⟨wcv, vec_new_wf⟩⟩
  simp [absConstantInfo, absNames, absLevels, acv, ae8, ae7, ae6, ae5, ae4, ae3, ae2, ae1, al, ae, av, an2, an1, an,
    ConLeche.falseRecRaw]

theorem false_basis_refines {r : alloc.vec.Vec env.ConstantInfo} (h : basis_raw.false_basis = ok r) :
    absConstantInfos r = ConLeche.falseBasis ∧ ConstantInfosWF r := by
  rw [basis_raw.false_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, ci1, hci1, hres⟩ := h
  obtain ⟨aci, wci⟩ := false_raw_refines hci
  obtain ⟨aci1, wci1⟩ := false_rec_raw_refines hci1
  obtain ⟨ares, wres⟩ := vec2_refines wci wci1 hres
  refine ⟨?_, wres⟩
  simp [absConstantInfos, absConstantInfos, ares, aci1, aci,
    ConLeche.falseBasis]

theorem quot_rel_refines {r : expr.Expr} (h : basis_raw.quot_rel = ok r) :
    absExpr r = ConLeche.quotRel ∧ ExprWF r := by
  rw [basis_raw.quot_rel] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, e1, he1, e2, he2, e3, he3, hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨ae2, we2⟩ := prop_refines he2
  obtain ⟨ae3, we3⟩ := pi_refines we1 we2 he3
  obtain ⟨ares, wres⟩ := pi_refines we we3 hres
  refine ⟨?_, wres⟩
  simp [ares, ae3, ae2, ae1, ae,
    ConLeche.quotRel]

theorem quot_raw_refines {r : env.ConstantInfo} (h : basis_raw.quot_raw = ok r) :
    absConstantInfo r = ConLeche.quotRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.quot_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, v, hv, l, hl, e, he, e1, he1, e2, he2, e3, he3, e4, he4, cv, hcv,
    ic, hic, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.quot_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := quot_rel_refines he1
  obtain ⟨ae2, we2⟩ := srt_refines wl he2
  obtain ⟨ae3, we3⟩ := pi_refines we1 we2 he3
  obtain ⟨ae4, we4⟩ := pi_refines we we3 he4
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we4 hcv
  obtain ⟨aic, wic⟩ := ind_caps_default_refines hic
  refine ⟨?_, ⟨wcv, wic⟩⟩
  simp [absConstantInfo, absNames, aic, acv, ae4, ae3, ae2, ae1, ae, al, av, an1, an,
    ConLeche.quotRaw]

theorem quot_mk_raw_refines {r : env.ConstantInfo} (h : basis_raw.quot_mk_raw = ok r) :
    absConstantInfo r = ConLeche.quotMkRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.quot_mk_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, v, hv, l, hl, e, he, e1, he1, e2, he2, n2, hn2, v1, hv1, e3, he3,
    e4, he4, e5, he5, e6, he6, e7, he7, e8, he8, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.quot_mk_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := quot_rel_refines he1
  obtain ⟨ae2, we2⟩ := bv_refines he2
  obtain ⟨an2, wn2⟩ := BasisNames.quot_name_refines hn2
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae3, we3⟩ := cnst_refines wn2 wv1 he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨ae5, we5⟩ := ap2_refines we3 we4 we2 he5
  obtain ⟨ae6, we6⟩ := pi_refines we2 we5 he6
  obtain ⟨ae7, we7⟩ := pi_refines we1 we6 he7
  obtain ⟨ae8, we8⟩ := pi_refines we we7 he8
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we8 hcv
  refine ⟨?_, wcv⟩
  simp [absConstantInfo, absNames, absLevels, acv, ae8, ae7, ae6, ae5, ae4, ae3, av1, an2, ae2, ae1, ae, al, av, an1, an,
    ConLeche.quotMkRaw]

theorem quot_lift_f_refines {r : expr.Expr} (h : basis_raw.quot_lift_f = ok r) :
    absExpr r = ConLeche.quotLiftF ∧ ExprWF r := by
  rw [basis_raw.quot_lift_f] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, e1, he1, hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨ares, wres⟩ := pi_refines we we1 hres
  refine ⟨?_, wres⟩
  simp [ares, ae1, ae,
    ConLeche.quotLiftF]

theorem quot_lift_h_refines {r : expr.Expr} (h : basis_raw.quot_lift_h = ok r) :
    absExpr r = ConLeche.quotLiftH ∧ ExprWF r := by
  rw [basis_raw.quot_lift_h] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, e1, he1, e2, he2, e3, he3, e4, he4, n, hn, l, hl, v, hv, e5, he5, e6, he6,
    e7, he7, e8, he8, e9, he9, e10, he10, e11, he11, hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨ae2, we2⟩ := bv_refines he2
  obtain ⟨ae3, we3⟩ := bv_refines he3
  obtain ⟨ae4, we4⟩ := ap2_refines we1 we2 we3 he4
  obtain ⟨an, wn⟩ := BasisNames.eq_name_refines hn
  obtain ⟨al, wl⟩ := v_refines hl
  obtain ⟨av, wv⟩ := vec1_refines wl hv
  obtain ⟨ae5, we5⟩ := cnst_refines wn wv he5
  obtain ⟨ae6, we6⟩ := bv_refines he6
  obtain ⟨ae7, we7⟩ := mk_app_refines we we6 he7
  obtain ⟨ae8, we8⟩ := mk_app_refines we we2 he8
  obtain ⟨ae9, we9⟩ := ap3_refines we5 we1 we7 we8 he9
  obtain ⟨ae10, we10⟩ := pi_refines we4 we9 he10
  obtain ⟨ae11, we11⟩ := pi_refines we1 we10 he11
  obtain ⟨ares, wres⟩ := pi_refines we we11 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae11, ae10, ae9, ae8, ae7, ae6, ae5, av, al, an, ae4, ae3, ae2, ae1, ae,
    ConLeche.quotLiftH]

theorem quot_lift_raw_refines {r : env.ConstantInfo} (h : basis_raw.quot_lift_raw = ok r) :
    absConstantInfo r = ConLeche.quotLiftRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.quot_lift_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, n2, hn2, v, hv, l, hl, e, he, e1, he1, l1, hl1, e2, he2, e3, he3,
    e4, he4, n3, hn3, v1, hv1, e5, he5, e6, he6, e7, he7, e8, he8, e9, he9, e10, he10, e11,
    he11, e12, he12, e13, he13, e14, he14, cv, hcv, n4, hn4, e15, he15, e16, he16, e17,
    he17, e18, he18, e19, he19, e20, he20, e21, he21, e22, he22, e23, he23, e24, he24, e25,
    he25, rr, hrr, v2, hv2, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.quot_lift_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨an2, wn2⟩ := v_n_refines hn2
  obtain ⟨av, wv⟩ := vec2_refines wn1 wn2 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := quot_rel_refines he1
  obtain ⟨al1, wl1⟩ := v_refines hl1
  obtain ⟨ae2, we2⟩ := srt_refines wl1 he2
  obtain ⟨ae3, we3⟩ := quot_lift_f_refines he3
  obtain ⟨ae4, we4⟩ := quot_lift_h_refines he4
  obtain ⟨an3, wn3⟩ := BasisNames.quot_name_refines hn3
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae5, we5⟩ := cnst_refines wn3 wv1 he5
  obtain ⟨ae6, we6⟩ := bv_refines he6
  obtain ⟨ae7, we7⟩ := bv_refines he7
  obtain ⟨ae8, we8⟩ := ap2_refines we5 we6 we7 he8
  obtain ⟨ae9, we9⟩ := pi_refines we8 we7 he9
  obtain ⟨ae10, we10⟩ := pi_refines we4 we9 he10
  obtain ⟨ae11, we11⟩ := pi_refines we3 we10 he11
  obtain ⟨ae12, we12⟩ := pi_refines we2 we11 he12
  obtain ⟨ae13, we13⟩ := pi_refines we1 we12 he13
  obtain ⟨ae14, we14⟩ := pi_refines we we13 he14
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we14 hcv
  obtain ⟨an4, wn4⟩ := BasisNames.quot_mk_name_refines hn4
  obtain ⟨ae15, we15⟩ := srt_refines wl he15
  obtain ⟨ae16, we16⟩ := srt_refines wl1 he16
  obtain ⟨ae17, we17⟩ := bv_refines he17
  obtain ⟨ae18, we18⟩ := bv_refines he18
  obtain ⟨ae19, we19⟩ := mk_app_refines we17 we18 he19
  obtain ⟨ae20, we20⟩ := lm_refines we6 we19 he20
  obtain ⟨ae21, we21⟩ := lm_refines we4 we20 he21
  obtain ⟨ae22, we22⟩ := lm_refines we3 we21 he22
  obtain ⟨ae23, we23⟩ := lm_refines we16 we22 he23
  obtain ⟨ae24, we24⟩ := lm_refines we1 we23 he24
  obtain ⟨ae25, we25⟩ := lm_refines we15 we24 he25
  obtain ⟨arr, wrr⟩ := rule_refines wn4 we25 hrr
  obtain ⟨av2, wv2⟩ := vec1_refines wrr hv2
  refine ⟨?_, ⟨wcv, wv2⟩⟩
  simp [absConstantInfo, absNames, absLevels, av2, arr, ae25, ae24, ae23, ae22, ae21, ae20, ae19, ae18, ae17, ae16, ae15, an4, acv, ae14, ae13, ae12, ae11, ae10, ae9, ae8, ae7, ae6, ae5, av1, an3, ae4, ae3, ae2, al1, ae1, ae, al, av, an2, an1, an,
    ConLeche.quotLiftRaw]

theorem quot_ind_motive_refines {r : expr.Expr} (h : basis_raw.quot_ind_motive = ok r) :
    absExpr r = ConLeche.quotIndMotive ∧ ExprWF r := by
  rw [basis_raw.quot_ind_motive] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, l, hl, v, hv, e, he, e1, he1, e2, he2, e3, he3, e4, he4, hres⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.quot_name_refines hn
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av, wv⟩ := vec1_refines wl hv
  obtain ⟨ae, we⟩ := cnst_refines wn wv he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨ae2, we2⟩ := bv_refines he2
  obtain ⟨ae3, we3⟩ := ap2_refines we we1 we2 he3
  obtain ⟨ae4, we4⟩ := prop_refines he4
  obtain ⟨ares, wres⟩ := pi_refines we3 we4 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae4, ae3, ae2, ae1, ae, av, al, an,
    ConLeche.quotIndMotive]

theorem quot_ind_mk_refines {r : expr.Expr} (h : basis_raw.quot_ind_mk = ok r) :
    absExpr r = ConLeche.quotIndMk ∧ ExprWF r := by
  rw [basis_raw.quot_ind_mk] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, he, e1, he1, n, hn, l, hl, v, hv, e2, he2, e3, he3, e4, he4, e5, he5, e6, he6,
    hres⟩ := h
  obtain ⟨ae, we⟩ := bv_refines he
  obtain ⟨ae1, we1⟩ := bv_refines he1
  obtain ⟨an, wn⟩ := BasisNames.quot_mk_name_refines hn
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨av, wv⟩ := vec1_refines wl hv
  obtain ⟨ae2, we2⟩ := cnst_refines wn wv he2
  obtain ⟨ae3, we3⟩ := bv_refines he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨ae5, we5⟩ := ap3_refines we2 we3 we we4 he5
  obtain ⟨ae6, we6⟩ := mk_app_refines we1 we5 he6
  obtain ⟨ares, wres⟩ := pi_refines we we6 hres
  refine ⟨?_, wres⟩
  simp [absLevels, ares, ae6, ae5, ae4, ae3, ae2, av, al, an, ae1, ae,
    ConLeche.quotIndMk]

theorem quot_ind_raw_refines {r : env.ConstantInfo} (h : basis_raw.quot_ind_raw = ok r) :
    absConstantInfo r = ConLeche.quotIndRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.quot_ind_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, v, hv, l, hl, e, he, e1, he1, e2, he2, e3, he3, n2, hn2, v1, hv1,
    e4, he4, e5, he5, e6, he6, e7, he7, e8, he8, e9, he9, e10, he10, e11, he11, e12, he12,
    e13, he13, e14, he14, cv, hcv, n3, hn3, e15, he15, e16, he16, e17, he17, e18, he18,
    e19, he19, e20, he20, e21, he21, e22, he22, rr, hrr, v2, hv2, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.quot_ind_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := quot_rel_refines he1
  obtain ⟨ae2, we2⟩ := quot_ind_motive_refines he2
  obtain ⟨ae3, we3⟩ := quot_ind_mk_refines he3
  obtain ⟨an2, wn2⟩ := BasisNames.quot_name_refines hn2
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae4, we4⟩ := cnst_refines wn2 wv1 he4
  obtain ⟨ae5, we5⟩ := bv_refines he5
  obtain ⟨ae6, we6⟩ := bv_refines he6
  obtain ⟨ae7, we7⟩ := ap2_refines we4 we5 we6 he7
  obtain ⟨ae8, we8⟩ := bv_refines he8
  obtain ⟨ae9, we9⟩ := mk_app_refines we6 we8 he9
  obtain ⟨ae10, we10⟩ := pi_refines we7 we9 he10
  obtain ⟨ae11, we11⟩ := pi_refines we3 we10 he11
  obtain ⟨ae12, we12⟩ := pi_refines we2 we11 he12
  obtain ⟨ae13, we13⟩ := pi_refines we1 we12 he13
  obtain ⟨ae14, we14⟩ := pi_refines we we13 he14
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we14 hcv
  obtain ⟨an3, wn3⟩ := BasisNames.quot_mk_name_refines hn3
  obtain ⟨ae15, we15⟩ := srt_refines wl he15
  obtain ⟨ae16, we16⟩ := bv_refines he16
  obtain ⟨ae17, we17⟩ := mk_app_refines we16 we8 he17
  obtain ⟨ae18, we18⟩ := lm_refines we5 we17 he18
  obtain ⟨ae19, we19⟩ := lm_refines we3 we18 he19
  obtain ⟨ae20, we20⟩ := lm_refines we2 we19 he20
  obtain ⟨ae21, we21⟩ := lm_refines we1 we20 he21
  obtain ⟨ae22, we22⟩ := lm_refines we15 we21 he22
  obtain ⟨arr, wrr⟩ := rule_refines wn3 we22 hrr
  obtain ⟨av2, wv2⟩ := vec1_refines wrr hv2
  refine ⟨?_, ⟨wcv, wv2⟩⟩
  simp [absConstantInfo, absNames, absLevels, av2, arr, ae22, ae21, ae20, ae19, ae18, ae17, ae16, ae15, an3, acv, ae14, ae13, ae12, ae11, ae10, ae9, ae8, ae7, ae6, ae5, ae4, av1, an2, ae3, ae2, ae1, ae, al, av, an1, an,
    ConLeche.quotIndRaw]

theorem quot_sound_raw_refines {r : env.ConstantInfo} (h : basis_raw.quot_sound_raw = ok r) :
    absConstantInfo r = ConLeche.quotSoundRaw ∧ ConstantInfoWF r := by
  rw [basis_raw.quot_sound_raw] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n, hn, n1, hn1, v, hv, l, hl, e, he, e1, he1, e2, he2, e3, he3, e4, he4, e5, he5,
    n2, hn2, v1, hv1, e6, he6, n3, hn3, v2, hv2, e7, he7, e8, he8, e9, he9, e10, he10, n4,
    hn4, v3, hv3, e11, he11, e12, he12, v4, hv4, e13, he13, e14, he14, e15, he15, e16,
    he16, e17, he17, e18, he18, e19, he19, e20, he20, cv, hcv, rfl⟩ := h
  obtain ⟨an, wn⟩ := BasisNames.quot_sound_name_refines hn
  obtain ⟨an1, wn1⟩ := u_n_refines hn1
  obtain ⟨av, wv⟩ := vec1_refines wn1 hv
  obtain ⟨al, wl⟩ := u_refines hl
  obtain ⟨ae, we⟩ := srt_refines wl he
  obtain ⟨ae1, we1⟩ := quot_rel_refines he1
  obtain ⟨ae2, we2⟩ := bv_refines he2
  obtain ⟨ae3, we3⟩ := bv_refines he3
  obtain ⟨ae4, we4⟩ := bv_refines he4
  obtain ⟨ae5, we5⟩ := ap2_refines we3 we2 we4 he5
  obtain ⟨an2, wn2⟩ := BasisNames.eq_name_refines hn2
  obtain ⟨av1, wv1⟩ := vec1_refines wl hv1
  obtain ⟨ae6, we6⟩ := cnst_refines wn2 wv1 he6
  obtain ⟨an3, wn3⟩ := BasisNames.quot_name_refines hn3
  obtain ⟨av2, wv2⟩ := vec1_refines wl hv2
  obtain ⟨ae7, we7⟩ := cnst_refines wn3 wv2 he7
  obtain ⟨ae8, we8⟩ := bv_refines he8
  obtain ⟨ae9, we9⟩ := bv_refines he9
  obtain ⟨ae10, we10⟩ := ap2_refines we7 we8 we9 he10
  obtain ⟨an4, wn4⟩ := BasisNames.quot_mk_name_refines hn4
  obtain ⟨av3, wv3⟩ := vec1_refines wl hv3
  obtain ⟨ae11, we11⟩ := cnst_refines wn4 wv3 he11
  obtain ⟨ae12, we12⟩ := ap3_refines we11 we8 we9 we3 he12
  obtain ⟨av4, wv4⟩ := vec1_refines wl hv4
  obtain ⟨ae13, we13⟩ := cnst_refines wn4 wv4 he13
  obtain ⟨ae14, we14⟩ := ap3_refines we13 we8 we9 we2 he14
  obtain ⟨ae15, we15⟩ := ap3_refines we6 we10 we12 we14 he15
  obtain ⟨ae16, we16⟩ := pi_refines we5 we15 he16
  obtain ⟨ae17, we17⟩ := pi_refines we3 we16 he17
  obtain ⟨ae18, we18⟩ := pi_refines we2 we17 he18
  obtain ⟨ae19, we19⟩ := pi_refines we1 we18 he19
  obtain ⟨ae20, we20⟩ := pi_refines we we19 he20
  obtain ⟨acv, wcv⟩ := cv_refines wn wv we20 hcv
  refine ⟨?_, wcv⟩
  simp [absConstantInfo, absNames, absLevels, acv, ae20, ae19, ae18, ae17, ae16, ae15, ae14, ae13, av4, ae12, ae11, av3, an4, ae10, ae9, ae8, ae7, av2, an3, ae6, av1, an2, ae5, ae4, ae3, ae2, ae1, ae, al, av, an1, an,
    ConLeche.quotSoundRaw]

theorem quot_basis_refines {r : alloc.vec.Vec env.ConstantInfo} (h : basis_raw.quot_basis = ok r) :
    absConstantInfos r = ConLeche.quotBasis ∧ ConstantInfosWF r := by
  rw [basis_raw.quot_basis] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ci, hci, ci1, hci1, ci2, hci2, ci3, hci3, ci4, hci4, hres⟩ := h
  obtain ⟨aci, wci⟩ := quot_raw_refines hci
  obtain ⟨aci1, wci1⟩ := quot_mk_raw_refines hci1
  obtain ⟨aci2, wci2⟩ := quot_lift_raw_refines hci2
  obtain ⟨aci3, wci3⟩ := quot_ind_raw_refines hci3
  obtain ⟨aci4, wci4⟩ := quot_sound_raw_refines hci4
  obtain ⟨ares, wres⟩ := vec5_refines wci wci1 wci2 wci3 wci4 hres
  refine ⟨?_, wres⟩
  simp [absConstantInfos, absConstantInfos, ares, aci4, aci3, aci2, aci1, aci,
    ConLeche.quotBasis]

/-! ## `BasisKind.decls` -/

/-- `ConLeche/Kernel/Basis.lean:40-47 BasisKind.decls` — the constants of one
basis block, in dependency order. -/
theorem basis_kind_decls_refines {k : env.BasisKind} {r : alloc.vec.Vec env.ConstantInfo}
    (h : basis_raw.basis_kind_decls k = ok r) :
    absConstantInfos r = ConLeche.BasisKind.decls (absBasisKind k) ∧ ConstantInfosWF r := by
  cases k <;>
    (rw [basis_raw.basis_kind_decls] at h
     simp only [absBasisKind, ConLeche.BasisKind.decls])
  exacts [eq_basis_refines h, nat_basis_refines h, punit_basis_refines h,
    empty_basis_refines h, false_basis_refines h, quot_basis_refines h]

/-! ## Recognising a pinned block in a stream record (con-leche task #293)

`basisPinHit` is a `List.find?` by member NAME followed by a single
`Option.filter` by `canonEqList` — the task-#215 pre-filter, which is what
keeps a block that is not one of the five away from `ConstantInfo.canon`.  The
port spells the two phases as one index recursion (§3.4 forbids closures), and
the lemma below is stated on the suffix `ks.drop i` so that the `find?` and the
`filter` stay in the cited order. -/

/-- The five kinds the block match tries, as con-leche's inline literal. -/
theorem block_pin_kinds_refines {r : alloc.vec.Vec env.BasisKind}
    (h : basis_raw.block_pin_kinds = ok r) :
    r.val.map absBasisKind
      = [ConLeche.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK] := by
  rw [basis_raw.block_pin_kinds] at h
  rw [(vec5_refines (W := fun _ : env.BasisKind => True) trivial trivial trivial trivial
    trivial h).1]
  rfl

/-! `env::constant_info_names_from` is `kernel::env`'s, not this module's: it
is the index recursion behind `Declaration.names`' `block.map (·.name)` and
`ConRon/Refine/Env.lean` has no lemma for it (nothing had called it until
con-leche's task #293 gave the pin match a name pre-filter).  It is proved
here, locally, and **should move to `Refine/Env.lean`** when that file is next
touched — the same note `Refine/PropRead.lean` carries for `to_constant_val`. -/

theorem constant_info_names_from_aux (N : Nat) :
    ∀ (block : alloc.vec.Vec env.ConstantInfo) (i : Std.Usize)
      (out r : alloc.vec.Vec name.Name),
      ConstantInfosWF block → NamesWF out → block.val.length - i.val = N →
      env.constant_info_names_from block i out = ok r →
      absNames r = absNames out ++
          ((absConstantInfos block).drop i.val).map ConLeche.ConstantInfo.name
        ∧ NamesWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro block i out r hblock hout hN h
    rw [env.constant_info_names_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : (absConstantInfos block).length ≤ i.val := by
        have := alloc.vec.Vec.len_val block
        simp only [absConstantInfos, List.length_map]; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
      exact ⟨by simp, hout⟩
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ci, hidx, n, hn, out1, hpush, i2, hi2, hrec⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < block.val.length := by
        have := alloc.vec.Vec.len_val block; scalar_tac
      have hx : block.val[i.val] = ci := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hciwf : ConstantInfoWF ci := hblock ci (by rw [← hx]; exact List.getElem_mem hlt)
      have hnwf : NameWF n := Env.constant_info_name_wf hciwf hn
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hout1 : NamesWF out1 := by
        intro y hy
        rw [vec_push_val hpush] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hout y hy
        · rw [List.mem_singleton.mp hy]; exact hnwf
      obtain ⟨habs, hwf⟩ :=
        ih (block.val.length - i2.val) (by omega) block i2 out1 r hblock hout1 rfl hrec
      refine ⟨?_, hwf⟩
      rw [habs, hi2v]
      simp only [absNames, vec_push_val hpush, List.map_append, List.map_cons,
        List.map_nil, Env.constant_info_name_refines hn]
      rw [show (absConstantInfos block).drop i.val
          = absConstantInfo ci :: (absConstantInfos block).drop (i.val + 1) from by
        rw [absConstantInfos, List.drop_eq_getElem_cons (by simpa using hlt),
          List.getElem_map, hx]]
      simp

/-- `ConLeche/Kernel/Env.lean:659-670` — `env::constant_info_names_from` at
the entry point's `0`/`[]`: a block's member names. -/
theorem constant_info_names_refines {block : alloc.vec.Vec env.ConstantInfo}
    {r : alloc.vec.Vec name.Name} (hblock : ConstantInfosWF block)
    (h : env.constant_info_names_from block 0#usize (alloc.vec.Vec.new name.Name) = ok r) :
    absNames r = (absConstantInfos block).map ConLeche.ConstantInfo.name ∧ NamesWF r := by
  obtain ⟨habs, hwf⟩ :=
    constant_info_names_from_aux _ block 0#usize (alloc.vec.Vec.new name.Name) r hblock
      (fun x hx => by simp [alloc.vec.Vec.new] at hx) rfl h
  refine ⟨?_, hwf⟩
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [habs, h0, List.drop_zero]
  simp [absNames, alloc.vec.Vec.new]

/-- `ConLeche/Kernel/Basis.lean:60-71` — the NAME pre-filter,
`k.decls.map (·.name) == block.map (·.name)`. -/
theorem basis_pin_names_eq_refines {decls block : alloc.vec.Vec env.ConstantInfo} {b : Bool}
    (hd : ConstantInfosWF decls) (hb : ConstantInfosWF block)
    (h : basis_raw.basis_pin_names_eq decls block = ok b) :
    b = decide ((absConstantInfos decls).map ConLeche.ConstantInfo.name
      = (absConstantInfos block).map ConLeche.ConstantInfo.name) := by
  rw [basis_raw.basis_pin_names_eq] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, hv, v1, hv1, hbeq⟩ := h
  obtain ⟨hvabs, hvwf⟩ := constant_info_names_refines hd hv
  obtain ⟨hv1abs, hv1wf⟩ := constant_info_names_refines hb hv1
  rw [Env.names_beq_refines hvwf hv1wf hbeq, hvabs, hv1abs]

theorem basis_pin_hit_from_aux (N : Nat) :
    ∀ (ks : alloc.vec.Vec env.BasisKind) (block : alloc.vec.Vec env.ConstantInfo)
      (i : Std.Usize) (o : Option env.BasisKind),
      ConstantInfosWF block → ks.val.length - i.val = N →
      basis_raw.basis_pin_hit_from ks block i = ok o →
      o.map absBasisKind =
        ((((ks.val.map absBasisKind).drop i.val).find? fun k =>
            (ConLeche.BasisKind.decls k).map (·.name)
              == (absConstantInfos block).map (·.name)).filter
          fun k => ConLeche.canonEqList (absConstantInfos block)
            (ConLeche.BasisKind.decls k)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ks block i o hblock hN h
    rw [basis_raw.basis_pin_hit_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : (ks.val.map absBasisKind).length ≤ i.val := by
        have := alloc.vec.Vec.len_val ks
        simp only [List.length_map]; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
      rfl
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨bk, hidx, decls, hdecls, b, hb, h⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < ks.val.length := by
        have := alloc.vec.Vec.len_val ks; scalar_tac
      have hx : ks.val[i.val] = bk := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      obtain ⟨hdabs, hdwf⟩ := basis_kind_decls_refines hdecls
      have hbabs := basis_pin_names_eq_refines hdwf hblock hb
      rw [show (ks.val.map absBasisKind).drop i.val
          = absBasisKind bk :: (ks.val.map absBasisKind).drop (i.val + 1) from by
        rw [List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map, hx]]
      rw [List.find?_cons]
      cases hbv : b
      · rw [hbv] at hbabs h
        simp only [Bool.false_eq_true, if_false] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, hrec⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hne : ¬ ((ConLeche.BasisKind.decls (absBasisKind bk)).map (·.name)
            = (absConstantInfos block).map (·.name)) := by
          rw [← hdabs]; exact of_decide_eq_false hbabs.symm
        rw [show ((ConLeche.BasisKind.decls (absBasisKind bk)).map (·.name)
            == (absConstantInfos block).map (·.name)) = false from by simpa using hne]
        have hrecabs := ih (ks.val.length - i2.val) (by omega) ks block i2 o hblock rfl hrec
        rwa [hi2v] at hrecabs
      · rw [hbv] at hbabs h
        have heq : (ConLeche.BasisKind.decls (absBasisKind bk)).map (·.name)
            = (absConstantInfos block).map (·.name) := by
          rw [← hdabs]; exact of_decide_eq_true hbabs.symm
        rw [show ((ConLeche.BasisKind.decls (absBasisKind bk)).map (·.name)
            == (absConstantInfos block).map (·.name)) = true from by simpa using heq]
        simp only []
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨c, hc, h⟩ := h
        have hcabs := Canon.canon_eq_list_deref_refines hblock hdwf hc
        cases hcv : c
        · rw [hcv] at hcabs h
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
          rw [← h]
          simp only [Option.filter, Option.map_none]
          rw [if_neg (by rw [← hdabs, ← hcabs]; simp)]
        · rw [hcv] at hcabs h
          simp only [if_true, bind_eq_ok_iff, Result.ok.injEq] at h
          obtain ⟨k', hk', rfl⟩ := h
          rw [Env.basis_kind_dup_refines hk']
          simp only [Option.map_some, Option.filter]
          rw [if_pos (by rw [← hdabs, ← hcabs])]

/-- **The basis-pin match** (`ConLeche/Kernel/Basis.lean:60-71 basisPinHit`).
The two phases stay in the cited order: `List.find?` picks the candidate by
member NAMES, and only that one candidate is `Option.filter`ed by
`canonEqList`. -/
theorem basis_pin_hit_refines {block : alloc.vec.Vec env.ConstantInfo}
    {o : Option env.BasisKind} (hblock : ConstantInfosWF block)
    (h : basis_raw.basis_pin_hit block = ok o) :
    o.map absBasisKind = ConLeche.basisPinHit (absConstantInfos block) := by
  rw [basis_raw.basis_pin_hit] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨ks, hks, h⟩ := h
  have hfrom := basis_pin_hit_from_aux _ ks block 0#usize o hblock rfl h
  have h0 : (0#usize : Std.Usize).val = 0 := rfl
  rw [h0, List.drop_zero, block_pin_kinds_refines hks] at hfrom
  rw [hfrom, ConLeche.basisPinHit]

/-! ## The quotient package, slot by slot -/

/-! `env::to_constant_val`'s well-formedness half belongs to `Refine/Env.lean`
too (that file proves only the abstraction); it is proved here for the same
reason as `constant_info_names_from` above, and **should move with it**. -/

theorem to_constant_val_wf {ci : env.ConstantInfo} {cv : env.ConstantVal}
    (hci : ConstantInfoWF ci) (h : env.to_constant_val ci = ok cv) : ConstantValWF cv := by
  rw [env.to_constant_val.eq_def] at h
  cases ci with
  | AxiomInfo v => rw [Env.constant_val_dup_refines h]; exact hci
  | DefnInfo v x hint => rw [Env.constant_val_dup_refines h]; exact hci.1
  | ThmInfo v x => rw [Env.constant_val_dup_refines h]; exact hci.1
  | IndInfo v c => rw [Env.constant_val_dup_refines h]; exact hci.1
  | CtorInfo v a b => rw [Env.constant_val_dup_refines h]; exact hci
  | RecInfo v a b rs => rw [Env.constant_val_dup_refines h]; exact hci.1
  | ProjInfo tbl =>
    obtain ⟨hsn, hlp, -, -, -, -⟩ := hci
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, v, hv, l, hl, l1, hl1, e, he, hcv⟩ := h
    have hvv : v.val = tbl.level_params.val := PropWhen.names_copy_val hv
    subst hcv
    exact ⟨Env.proj_table_name_wf hsn hn,
      fun m hm => hlp m (by rw [hvv] at hm; exact hm),
      Expr.sort_wf (Level.succ_wf (Level.zero_wf hl) hl1) he⟩

/-- `ConLeche/Kernel/Env.lean:503-504 QuotKind.slot` -/
theorem quot_kind_slot_refines {k : env.QuotKind} {i : Std.U64}
    (h : env.quot_kind_slot k = ok i) : i.val = (absQuotKind k).slot := by
  cases k <;> simp only [env.quot_kind_slot, Result.ok.injEq] at h <;>
    rw [← h] <;> rfl

/-- `ConLeche/Kernel/Basis.lean:73-78` — the pinned quotient package's
constant at one slot, with the cited `getD`'s total-function fallback.  The
fallback is unreachable (`quotBasis` has exactly the five members
`QuotKind.slot` indexes), and Lean's `default : ConstantVal` is the derived
`Inhabited` instance `⟨.anonymous, [], .bvar 0⟩`. -/
theorem quot_basis_at_refines {slot : Std.U64} {ci : env.ConstantInfo}
    (h : basis_raw.quot_basis_at slot = ok ci) :
    absConstantInfo ci
        = (ConLeche.BasisKind.quotK.decls.getD slot.val (.axiomInfo default))
      ∧ ConstantInfoWF ci := by
  rw [basis_raw.quot_basis_at] at h
  simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨decls, hdecls, h⟩ := h
  obtain ⟨hdabs, hdwf⟩ := quot_basis_refines hdecls
  have hdlen : (ConLeche.BasisKind.quotK.decls).length = decls.val.length := by
    rw [ConLeche.BasisKind.decls, ← hdabs]; simp [absConstantInfos]
  split at h
  · rename_i hlt
    simp only [bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨ci', hidx, hdup⟩ := h
    have hcast : (Std.UScalar.cast Std.UScalarTy.Usize slot).val = slot.val := by
      apply Env.u64_cast_usize_val
      have := Env.usize_cast_u64_val (alloc.vec.Vec.len decls)
      scalar_tac
    have hslt : slot.val < decls.val.length := by
      have := Env.usize_cast_u64_val (alloc.vec.Vec.len decls)
      have := alloc.vec.Vec.len_val decls
      scalar_tac
    have hg := ExprOps.vec_index_getElem? hidx
    rw [hcast] at hg
    have hx : decls.val[slot.val] = ci' := by
      rw [List.getElem?_eq_getElem hslt] at hg; exact Option.some_injective _ hg
    rw [Env.constant_info_dup_refines hdup]
    refine ⟨?_, hdwf ci' (by rw [← hx]; exact List.getElem_mem hslt)⟩
    rw [ConLeche.BasisKind.decls, ← hdabs, absConstantInfos,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hslt, hx]
    rfl
  · rename_i hge
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, e, he, cv, hcv, rfl⟩ := h
    obtain ⟨acv, wcv⟩ :=
      cv_refines (Name.anonymous_wf hn) vec_new_wf (Expr.bvar_wf he) hcv
    refine ⟨?_, wcv⟩
    have hslt : decls.val.length ≤ slot.val := by
      have := Env.usize_cast_u64_val (alloc.vec.Vec.len decls)
      have := alloc.vec.Vec.len_val decls
      scalar_tac
    rw [absConstantInfo, acv, Name.anonymous_refines hn, Expr.bvar_refines he,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega)]
    simp [absNames, alloc.vec.Vec.new]
    rfl

/-- **The quotient-pin match** (`ConLeche/Kernel/Basis.lean:73-78
quotPinHit`): the record is the pinned package's constant at the slot it
declares itself at, compared at `toConstantVal`. -/
theorem quot_pin_hit_refines {k : env.QuotKind} {cv : env.ConstantVal} {b : Bool}
    (hcv : ConstantValWF cv) (h : basis_raw.quot_pin_hit k cv = ok b) :
    b = ConLeche.quotPinHit (absQuotKind k) (absConstantVal cv) := by
  rw [basis_raw.quot_pin_hit] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i, hi, ci, hci, cv1, hcv1, hb⟩ := h
  obtain ⟨hciabs, hciwf⟩ := quot_basis_at_refines hci
  have hcv1abs := Env.to_constant_val_refines hcv1
  have hcv1wf := to_constant_val_wf hciwf hcv1
  rw [Canon.constant_val_canon_eq_refines hcv hcv1wf hb, ConLeche.quotPinHit,
    hcv1abs, hciabs, quot_kind_slot_refines hi]

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.BasisRaw.basis_pin_hit_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms basis_pin_hit_refines

/--
info: 'ConRon.Refine.BasisRaw.quot_pin_hit_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms quot_pin_hit_refines

end ConRon.Refine.BasisRaw
