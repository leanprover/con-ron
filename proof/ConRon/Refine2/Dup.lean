/-
# `ConRon.Refine2.Dup` — the `arena::env` record copies are identities

**Task #97-P5-Front round 2.**  The Rust copies an owned record where the
twin shares an immutable one (`arena::env`'s `*_dup` family: `dup2` on a
handle, the `Vec` copiers, the record copiers); under the abstraction every
one of them is the identity.  These lemmas were written by the Theorem 2
Inductives and Core tiers (`Inductives/Shape.lean`, `Inductives/NativeParts.lean`,
`Core/Arms/Delta.lean`) and moved here, unchanged, so that the frontend tier
— which cannot import either — can cite them: `Frontend/Prepare.lean`'s
`i_declaration_dup_abs` is the one new lemma, the whole `IDeclaration` copy.

With them the two cursor principles the copiers are instances of
(`cursor_induction`, `vec_cursor_copy`), from `Inductives/Shape.lean`.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Specs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## `nidx_vec_dup`, the identity

`arena::env::nidx_vec_dup` copies a `Vec<NIdx>` because the Rust needs an
owned one; `dup2` is the identity on a handle (`Refine2/Inv.lean`'s
`dupId_nidx`), so the copy is the identity on the VALUE.  The `_from` cursor
has no twin (DESIGN §3.4's standing `List`-as-`Vec` deviation), so the shape
step is the tier's usual measure induction on `ns.size - i`. -/

private theorem nidx_vec_dup_from_val (N : Nat) :
    ∀ {ns out r : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize},
      ns.val.length - i.val = N →
      arena.env.nidx_vec_dup_from ns i out = ok r →
      r.val = out.val ++ ns.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ns out r i hN h
    rw [arena.env.nidx_vec_dup_from] at h
    split at h
    · rename_i hge
      have hge' : ns.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hge']
      simp
    · rename_i hge
      have hlt : i.val < ns.val.length := by scalar_tac
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnv : n = ns.val[i.val] := by
        have h1 := vec_index_some hn
        rw [List.getElem?_eq_getElem hlt] at h1
        exact (Option.some_inj.mp h1).symm
      have hn1v : n1 = ns.val[i.val] := (dupId_nidx _ _ hn1).trans hnv
      have hi2v : i2.val = i.val + 1 := by
        have h3 := ConRon.Refine.Nat.uadd_val hi2
        simpa using h3
      have hN2 : ns.val.length - i2.val = N - 1 := by rw [hi2v]; omega
      have hrec := ih (N - 1) (by omega) hN2 h
      rw [hrec, ConRon.Refine.vec_push_val hout1, hi2v, hn1v,
        List.drop_eq_getElem_cons hlt]
      simp

/-- **`arena::env::nidx_vec_dup` is the identity on the value.** -/
theorem nidx_vec_dup_val {ns r : alloc.vec.Vec arena.handle.NIdx}
    (h : arena.env.nidx_vec_dup ns = ok r) : r.val = ns.val := by
  rw [arena.env.nidx_vec_dup] at h
  have h2 := nidx_vec_dup_from_val (ns.val.length - (0#usize).val) rfl h
  rw [h2]
  simp [alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-! ## The state-free cursor recursion, once

DESIGN §3.4's third rule turns every `List` operation of a twin into a named
cursor recursion over a `Vec`, and the state-free half of this tier is that
recursion fifty-odd times: `if i ≥ len then ok out else <read, transform,
push>; f (i+1) out'`.  Round 2 wrote the measure induction out by hand twice
(`kinds_copy`, `u64_vec_dup`) and measured it at thirty lines; the two
declarations below are that induction factored out, so an instance owes only
its own two arms.

`cursor_induction` is the induction itself and says nothing about `Vec`s —
any recursion whose cursor moves up by one towards a fixed bound is an
instance.  `vec_cursor_copy` is the specialisation every *copier* of the tier
wants: read the source at the cursor, push ONE element computed from it, and
the answer is the accumulator followed by the image of what is left. -/

/-- **The cursor recursion's induction principle.**  A property that holds
past the bound and is preserved backwards by a single step of the cursor holds
everywhere.  The step gets its induction hypothesis for *every* `j` whose
value is `i + 1`, not for one chosen `j`, because the port's `i + 1#usize` is
a `Result` and the successor is only known through `absSz_add_one`. -/
theorem cursor_induction {ι : Type} {γ : Sort u} (val : ι → Nat) (n : Nat)
    (P : ι → γ → Prop)
    (hbase : ∀ (i : ι) (a : γ), n ≤ val i → P i a)
    (hstep : ∀ (i : ι) (a : γ), val i < n →
      (∀ (j : ι) (b : γ), val j = val i + 1 → P j b) → P i a) :
    ∀ (i : ι) (a : γ), P i a := by
  have key : ∀ (k : Nat) (i : ι) (a : γ), n - val i ≤ k → P i a := by
    intro k
    induction k with
    | zero => intro i a hk; exact hbase i a (by omega)
    | succ k ih =>
      intro i a hk
      by_cases h : n ≤ val i
      · exact hbase i a h
      · exact hstep i a (by omega) (fun j b hj => ih j b (by omega))
  intro i a
  exact key (n - val i) i a (Nat.le_refl _)

/-- **The tier's copier, once.**  `F` reads `xs` at the cursor, pushes one
element computed from it, and recurses; the answer, READ THROUGH THE
ABSTRACTION, is the accumulator followed by the image of the suffix.  A caller
supplies the two arms — `hstop` (past the end the accumulator comes back
unchanged) and `hstep` (one element in, one element out, and the pushed
element abstracts to the source element's image) — and gets the measure
induction for free.  The two abstractions `f` and `g` are separate because the
port's element type is often narrower than the source's (`ctors_of` drops a
field, `rhss_of` keeps one), and the conclusion is stated at `List.map`
because every `absXL` of this file is exactly that. -/
theorem vec_cursor_copy {α β δ : Type} (xs : alloc.vec.Vec α) (f : β → δ) (g : α → δ)
    (F : Std.Usize → alloc.vec.Vec β → Result (alloc.vec.Vec β))
    (hstop : ∀ (i : Std.Usize) (out o : alloc.vec.Vec β),
      xs.val.length ≤ i.val → F i out = ok o → o.val = out.val)
    (hstep : ∀ (i : Std.Usize) (x : α) (out o : alloc.vec.Vec β),
      xs.val[i.val]? = some x → F i out = ok o →
      ∃ (j : Std.Usize) (y : β) (out1 : alloc.vec.Vec β),
        j.val = i.val + 1 ∧ out1.val = out.val ++ [y] ∧ f y = g x ∧ F j out1 = ok o) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec β), F i out = ok o →
      o.val.map f = out.val.map f ++ (xs.val.drop i.val).map g := by
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i out => ∀ o, F i out = ok o →
      o.val.map f = out.val.map f ++ (xs.val.drop i.val).map g) ?_ ?_
  · intro i out hn o h
    rw [hstop i out o hn h, List.drop_eq_nil_of_le hn]
    simp
  · intro i out hi ih o h
    obtain ⟨x, hx⟩ : ∃ x, xs.val[i.val]? = some x :=
      ⟨xs.val[i.val], List.getElem?_eq_getElem hi⟩
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨j, y, out1, hj, hout1, hfy, hF⟩ := hstep i x out o hx h
    rw [ih j out1 hj o hF, hout1, hj, List.drop_eq_getElem_cons hb, hxv]
    simp [hfy]

/-- **`arena::env::i_constant_val_dup` is the identity on the abstraction.**
Three `dup2`s and `nidx_vec_dup`, all four of them identities
(`Refine2/Inv.lean`'s `DupId` rows and `Core/Arms/Delta.lean`'s
`nidx_vec_dup_val`).  Six functions of this tier copy a constructor record
and every one of them goes through this. -/
theorem i_constant_val_dup_abs {cv o : arena.env.IConstantVal}
    (h : arena.env.i_constant_val_dup cv = ok o) :
    absIConstantVal o = absIConstantVal cv := by
  rw [arena.env.i_constant_val_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ho := Result.ok_injective h
  subst ho
  simp only [absIConstantVal, dupId_nidx _ _ hn, dupId_eidx _ _ he,
    nidx_vec_dup_val hv]

/-! ### The four `arena::env` copies this tier inherits

`nidx_vec_dup` and `lidx_vec_dup` already have their identity lemmas
(`Core/Arms/Delta.lean`, `Refine2/Specs.lean`); the other two are stated here,
as the first two instances of `vec_cursor_copy`, because `inductive_shape_dup`
and every `IRecRule` copier of this tier goes through them. -/

private theorem eidx_vec_dup_from_map {es : alloc.vec.Vec arena.handle.EIdx} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.EIdx),
      arena.env.eidx_vec_dup_from es i out = ok o →
      o.val.map id = out.val.map id ++ (es.val.drop i.val).map id := by
  refine vec_cursor_copy es id id (arena.env.eidx_vec_dup_from es) ?_ ?_
  · intro i out o hn h
    rw [arena.env.eidx_vec_dup_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < es.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.env.eidx_vec_dup_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len es by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hex : e = x := by
      have h1 := vec_index_some he; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    exact ⟨i2, e1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [← hex, dupId_eidx _ _ he1], h⟩

/-- **`arena::env::eidx_vec_dup` is the identity on the value.** -/
theorem eidx_vec_dup_val {es r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.env.eidx_vec_dup es = ok r) : r.val = es.val := by
  rw [arena.env.eidx_vec_dup] at h
  have h2 := eidx_vec_dup_from_map 0#usize _ r h
  simpa [alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2

/-- `arena::env::i_rec_rule_fire_dup` is the identity on the abstraction. -/
theorem i_rec_rule_fire_dup_abs {f o : arena.env.IRecRuleFire}
    (h : arena.env.i_rec_rule_fire_dup f = ok o) :
    absIRecRuleFire o = absIRecRuleFire f := by
  rw [arena.env.i_rec_rule_fire_dup.eq_def] at h
  cases f with
  | Inert => rw [Result.ok_injective h]
  | Plain => rw [Result.ok_injective h]
  | Nested lvls pins =>
    simp only [] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIRecRuleFire, lidx_vec_dup_eq (by rw [arena.env.lidx_vec_dup] at hv; exact hv),
      eidx_vec_dup_val hv1]

/-- `arena::env::i_rec_rule_dup` is the identity on the abstraction. -/
theorem i_rec_rule_dup_abs {r o : arena.env.IRecRule}
    (h : arena.env.i_rec_rule_dup r = ok o) : absIRecRule o = absIRecRule r := by
  rw [arena.env.i_rec_rule_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨irf, hirf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIRecRule, dupId_nidx _ _ hn, dupId_eidx _ _ he,
    i_rec_rule_fire_dup_abs hirf]

private theorem i_rec_rules_dup_from_map {rs : alloc.vec.Vec arena.env.IRecRule} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IRecRule),
      arena.env.i_rec_rules_dup_from rs i out = ok o →
      o.val.map absIRecRule
        = out.val.map absIRecRule ++ (rs.val.drop i.val).map absIRecRule := by
  refine vec_cursor_copy rs absIRecRule absIRecRule
    (arena.env.i_rec_rules_dup_from rs) ?_ ?_
  · intro i out o hn h
    rw [arena.env.i_rec_rules_dup_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < rs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.env.i_rec_rules_dup_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)] at h
    obtain ⟨ir, hir, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ir1, hir1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hex : ir = x := by
      have h1 := vec_index_some hir; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    exact ⟨i2, ir1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [← hex, i_rec_rule_dup_abs hir1], h⟩

/-- **`arena::env::i_rec_rules_dup` is the identity on the abstraction.** -/
theorem i_rec_rules_dup_abs {rs r : alloc.vec.Vec arena.env.IRecRule}
    (h : arena.env.i_rec_rules_dup rs = ok r) :
    r.val.map absIRecRule = rs.val.map absIRecRule := by
  rw [arena.env.i_rec_rules_dup] at h
  have h2 := i_rec_rules_dup_from_map 0#usize _ r h
  simpa [alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2

/-- `arena::env::i_ind_caps_dup` is the identity on the abstraction. -/
theorem i_ind_caps_dup_abs {c o : arena.env.IIndCaps}
    (h : arena.env.i_ind_caps_dup c = ok o) : absIIndCaps o = absIIndCaps c := by
  rw [arena.env.i_ind_caps_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIIndCaps, dupId_nidx _ _ hn, ConRon.Refine.PropWhen.dup_eq hpw]

/-- `arena::env::i_proj_table_dup` is the identity on the abstraction. -/
theorem i_proj_table_dup_abs {t o : arena.env.IProjTable}
    (h : arena.env.i_proj_table_dup t = ok o) : absIProjTable o = absIProjTable t := by
  rw [arena.env.i_proj_table_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v2, hv2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIProjTable, dupId_nidx _ _ hn, dupId_nidx _ _ hn1,
    dupId_nidx _ _ hn2, dupId_lidx _ _ hl, nidx_vec_dup_val hv,
    eidx_vec_dup_val hv1,
    lidx_vec_dup_eq (by rw [arena.env.lidx_vec_dup] at hv2; exact hv2)]

/-- **`arena::env::i_constant_info_dup` is the identity on the abstraction.** -/
theorem i_constant_info_dup_abs {c o : arena.env.IConstantInfo}
    (h : arena.env.i_constant_info_dup c = ok o) :
    absIConstantInfo o = absIConstantInfo c := by
  rw [arena.env.i_constant_info_dup.eq_def] at h
  cases c with
  | AxiomInfo cv =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv]
  | DefnInfo cv v hint =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rh, hrh, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    have hrhv : rh = hint := by
      rw [kernel.env.reducibility_hint_dup.eq_def] at hrh
      cases hint <;> simp only [] at hrh <;> exact (Result.ok_injective hrh).symm
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, dupId_eidx _ _ he, hrhv]
  | ThmInfo cv v =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, dupId_eidx _ _ he]
  | IndInfo cv caps =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ic, hic, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, i_ind_caps_dup_abs hic]
  | CtorInfo cv a b =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv]
  | RecInfo cv a b rs =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, i_rec_rules_dup_abs hv]
  | ProjInfo t =>
    obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_proj_table_dup_abs hit]


/-- `i_constant_infos_dup_from` copies `cs` from the cursor on onto `out`
(`native_rec_pin_ok`'s `rest`). -/
theorem i_constant_infos_dup_from_abs {cs : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize} {out o : alloc.vec.Vec arena.env.IConstantInfo}
    (hrun : arena.env.i_constant_infos_dup_from cs i out = ok o) :
    o.val.map absIConstantInfo
      = out.val.map absIConstantInfo ++ (cs.val.drop i.val).map absIConstantInfo := by
  refine vec_cursor_copy cs absIConstantInfo absIConstantInfo
    (arena.env.i_constant_infos_dup_from cs) ?_ ?_ i out o hrun
  · intro i out o hn h
    rw [arena.env.i_constant_infos_dup_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < cs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.env.i_constant_infos_dup_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hvx : v = x := by
      have h1 := vec_index_some hv; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hvx
    exact ⟨i2, v1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      i_constant_info_dup_abs hv1, h⟩


/-- `arena::env::i_constant_infos_dup` is the identity on the abstraction. -/
theorem i_constant_infos_dup_abs {cs o : alloc.vec.Vec arena.env.IConstantInfo}
    (h : arena.env.i_constant_infos_dup cs = ok o) :
    o.val.map absIConstantInfo = cs.val.map absIConstantInfo := by
  rw [arena.env.i_constant_infos_dup] at h
  have h2 := i_constant_infos_dup_from_abs h
  simpa [alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2

/-- **`arena::env::i_declaration_dup` is the identity under the abstraction**
— every arm is a record copy above, or an enum copy (`basis_kind_dup`,
`quot_kind_dup`, `reducibility_hint_dup`) that answers its argument. -/
theorem i_declaration_dup_abs {d o : arena.env.IDeclaration}
    (h : arena.env.i_declaration_dup d = ok o) :
    absIDeclaration o = absIDeclaration d := by
  rw [arena.env.i_declaration_dup.eq_def] at h
  cases d with
  | AxiomDecl cv =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIDeclaration, i_constant_val_dup_abs hiv]
  | DefnDecl cv v hint =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rh, hrh, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    have hrhv : rh = hint := by
      rw [kernel.env.reducibility_hint_dup.eq_def] at hrh
      cases hint <;> simp only [] at hrh <;> exact (Result.ok_injective hrh).symm
    simp only [absIDeclaration, i_constant_val_dup_abs hiv, dupId_eidx _ _ he, hrhv]
  | ThmDecl cv v =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIDeclaration, i_constant_val_dup_abs hiv, dupId_eidx _ _ he]
  | OpaqueDecl cv v =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIDeclaration, i_constant_val_dup_abs hiv, dupId_eidx _ _ he]
  | BasisDecl k =>
    obtain ⟨bk, hbk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    have hk : bk = k := by
      rw [kernel.env.basis_kind_dup.eq_def] at hbk
      cases k <;> simp only [] at hbk <;> exact (Result.ok_injective hbk).symm
    rw [hk]
  | IndDecl bl n =>
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIDeclaration, i_constant_infos_dup_abs hv]
  | QuotDecl k cv =>
    obtain ⟨qk, hqk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    have hk : qk = k := by
      rw [kernel.env.quot_kind_dup.eq_def] at hqk
      cases k <;> simp only [] at hqk <;> exact (Result.ok_injective hqk).symm
    simp only [absIDeclaration, i_constant_val_dup_abs hiv, hk]

/-- info: 'ConRon.Refine2.i_declaration_dup_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms i_declaration_dup_abs

end ConRon.Refine2
