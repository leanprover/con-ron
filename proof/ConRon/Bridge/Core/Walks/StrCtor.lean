/-
# `ConRon.Bridge.Core.Walks.StrCtor` — a string literal's constructor form

Task #97-P3-Core round 5.  `strLitToConstructor` (`Arena/Core.lean:556`) builds
the `String.ofList (List.cons … (List.nil Char))` spine of a string literal in
the store; con-leche's `strLitToConstructor` (`Kernel/CoreDefs.lean:288-299`)
is the same term as a `foldr`.  Two of the tier's walks read it: the `.proj`
clause's `projLitToCtor` (and `litMajorToCtor`, the ι major's), and the
`defeq` step's two string-literal congruence exits.  It is the first rule of
this tier whose postcondition is a genuine `Ext` built by a RECURSION of
interns (`strLitConsSpine`), which is why it is a module of its own.
-/
import ConRon.Bridge.Core.Walks.Nat

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: none — `internE_spec` at the checker's invariant: an intern
extends the store and leaves caches and pins alone, so `CheckOK` survives. -/
theorem internE_ok_spec (s₀ : AState) (w : ENodeView)
    (hok : CheckOK mode env fe s₀) (hv : s₀.store.ViewOK w) :
    ⦃fun s => ⌜s = s₀⌝⦄ internE w
    ⦃⇓? h s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store h = denoteEView s'.store w⌝⦄ :=
  triple_mono (internE_spec s₀ w hok.state.wf hv)
    (fun _ _ ⟨hwf', hx', _, _, _, _, hc', hp', _, hd⟩ =>
      ⟨hok.mono ⟨hwf'⟩ hx' hc' hp', hx', hp', hd⟩)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor — the
`List.cons` spine, as the `foldr` con-leche writes: each character becomes
`List.cons Char (Char.ofNat (lit c))` in front of the rest. -/
def strSpineE (cx ox nx : Expr) (cs : List Char) : Expr :=
  cs.foldr (fun c e => .app (.app cx (.app ox (.lit (.natVal c.toNat)))) e) nx

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor —
**THEOREM 1 for the spine recursion** `strLitConsSpine`: one character per
level, four interns each. -/
theorem strLitConsSpine_spec (cons ofNat nilE : EIdx) (cx ox nx : Expr) :
    ∀ (cs : List Char) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteE s₀.store cons = some cx → denoteE s₀.store ofNat = some ox →
      denoteE s₀.store nilE = some nx →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.strLitConsSpine cons ofNat nilE cs
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          denoteE s'.store r = some (strSpineE cx ox nx cs)⌝⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro s₀ hok _ _ hn
    mvcgen [ConRon.Arena.strLitConsSpine]
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hn⟩
  | cons c cs ih =>
    intro s₀ hok hc ho hn
    unfold ConRon.Arena.strLitConsSpine
    refine triple_seq (ih s₀ hok hc ho hn) ?_
    rintro rest s1 ⟨hok1, hx1, hp1, hrest⟩
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s1 (.lit (.natVal c.toNat)) hok1 viewOK_lit) ?_
    rintro lit s2 ⟨hok2, hx2, hp2, hlit⟩
    have ho2 := denote_ext ho (hx1.trans hx2)
    have hlit' : denoteE s2.store lit = some (.lit (.natVal c.toNat)) := by
      rw [hlit]; rfl
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s2 (.app ofNat lit) hok2 (viewOK_app (by rw [ho2]; rfl)
        (by rw [hlit']; rfl))) ?_
    rintro ch s3 ⟨hok3, hx3, hp3, hch⟩
    have hch' : denoteE s3.store ch =
        some (.app ox (.lit (.natVal c.toNat))) := by
      rw [hch]
      simp only [denoteEView, denote_ext ho2 hx3, denote_ext hlit' hx3, opt2]
    have hc3 := denote_ext hc (hx1.trans (hx2.trans hx3))
    refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s3 (.app cons ch) hok3 (viewOK_app (by rw [hc3]; rfl)
        (by rw [hch']; rfl))) ?_
    rintro f s4 ⟨hok4, hx4, hp4, hf⟩
    have hf' : denoteE s4.store f =
        some (.app cx (.app ox (.lit (.natVal c.toNat)))) := by
      rw [hf]
      simp only [denoteEView, denote_ext hc3 hx4, denote_ext hch' hx4, opt2]
    have hrest4 := denote_ext hrest (hx2.trans (hx3.trans hx4))
    refine triple_mono (internE_ok_spec (mode := mode) (env := env) (fe := fe)
      s4 (.app f rest) hok4 (viewOK_app (by rw [hf']; rfl)
        (by rw [hrest4]; rfl))) ?_
    rintro r s5 ⟨hok5, hx5, hp5, hr⟩
    refine ⟨hok5, hx1.trans (hx2.trans (hx3.trans (hx4.trans hx5))),
      hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1))), ?_⟩
    rw [hr]
    simp only [denoteEView, denote_ext hf' hx5, denote_ext hrest4 hx5, opt2,
      strSpineE, List.foldr_cons]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor —
**THEOREM 1 for `strLitToConstructor`**: the handle the twin builds denotes
con-leche's constructor form, staged over the five pins, three `constE`s,
five interns and the spine. -/
theorem strLitToConstructor_spec (s₀ : AState) (str : String)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.strLitToConstructor str
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.strLitToConstructor str)⌝⦄ := by
  unfold ConRon.Arena.strLitToConstructor
  -- the universe list `[0]`
  refine triple_seq (pinZeroLevel_spec s₀ hok.pins) ?_
  rintro z s1 ⟨hs1, hz⟩
  subst s1
  refine triple_seq (internLsNode_spec s₀ [z] hok.state.wf
    (by intro c hc; simp at hc; subst hc
        exact lview_isSome_of_denote hz)) ?_
  rintro zs s2 ⟨hwf2, hx2, _, _, _, _, hc2, hp2, _, hzs⟩
  have hok2 : CheckOK mode env fe s2 := hok.mono ⟨hwf2⟩ hx2 hc2 hp2
  have hzs' : denoteLs s2.store.lss zs = some [Level.zero] := by
    rw [hzs]
    simp only [denoteLsView, denoteLList]
    have hz2 : denoteL s2.store.lss.ls z = some Level.zero := denoteL_ext hz hx2
    simp [hz2, opt2]
  -- `Char`
  refine triple_seq (pinAt_spec s2 PIN_CHAR hok2.pins) ?_
  rintro chN s3 ⟨hs3, hchN⟩
  subst s3
  refine triple_seq (constE_spec s2 chN ConLeche.charName hok2 (hchN _ rfl)) ?_
  rintro chC s4 ⟨hok4, hx4, hp4, hchC⟩
  -- `List.nil.{0} Char`
  refine triple_seq (pinAt_spec s4 PIN_LIST_NIL hok4.pins) ?_
  rintro lnN s5 ⟨hs5, hlnN⟩
  subst s5
  have hzs4 := denoteLs_ext hzs' hx4
  refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
    s4 (.const lnN zs) hok4 (viewOK_const
      (nview_isSome_of_denote (hlnN _ rfl))
      (by obtain ⟨w, hw, _⟩ := denoteLs_view hzs4; rw [hw]; rfl))) ?_
  rintro ln s6 ⟨hok6, hx6, hp6, hln⟩
  have hln' : denoteE s6.store ln = some (.const ConLeche.listNilName [.zero]) := by
    rw [hln]
    simp only [denoteEView, denoteN_ext (hlnN _ rfl) hx6, denoteLs_ext hzs4 hx6,
      opt2]
  have hchC6 := denote_ext hchC hx6
  refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
    s6 (.app ln chC) hok6 (viewOK_app (by rw [hln']; rfl)
      (by rw [hchC6]; rfl))) ?_
  rintro nilE s7 ⟨hok7, hx7, hp7, hnil⟩
  have hnil' : denoteE s7.store nilE = some (.app (.const ConLeche.listNilName
      [.zero]) (.const ConLeche.charName [])) := by
    rw [hnil]
    simp only [denoteEView, denote_ext hln' hx7, denote_ext hchC6 hx7, opt2]
  -- `List.cons.{0} Char`
  refine triple_seq (pinAt_spec s7 PIN_LIST_CONS hok7.pins) ?_
  rintro lcN s8 ⟨hs8, hlcN⟩
  subst s8
  have hzs7 := denoteLs_ext hzs4 (hx6.trans hx7)
  refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
    s7 (.const lcN zs) hok7 (viewOK_const
      (nview_isSome_of_denote (hlcN _ rfl))
      (by obtain ⟨w, hw, _⟩ := denoteLs_view hzs7; rw [hw]; rfl))) ?_
  rintro lc s9 ⟨hok9, hx9, hp9, hlc⟩
  have hlc' : denoteE s9.store lc =
      some (.const ConLeche.listConsName [.zero]) := by
    rw [hlc]
    simp only [denoteEView, denoteN_ext (hlcN _ rfl) hx9, denoteLs_ext hzs7 hx9,
      opt2]
  have hchC9 := denote_ext hchC6 (hx7.trans hx9)
  refine triple_seq (internE_ok_spec (mode := mode) (env := env) (fe := fe)
    s9 (.app lc chC) hok9 (viewOK_app (by rw [hlc']; rfl)
      (by rw [hchC9]; rfl))) ?_
  rintro cons s10 ⟨hok10, hx10, hp10, hcons⟩
  have hcons' : denoteE s10.store cons = some (.app (.const
      ConLeche.listConsName [.zero]) (.const ConLeche.charName [])) := by
    rw [hcons]
    simp only [denoteEView, denote_ext hlc' hx10, denote_ext hchC9 hx10, opt2]
  -- `Char.ofNat`
  refine triple_seq (pinAt_spec s10 PIN_CHAR_OF_NAT hok10.pins) ?_
  rintro coN s11 ⟨hs11, hcoN⟩
  subst s11
  refine triple_seq (constE_spec s10 coN ConLeche.charOfNatName hok10
    (hcoN _ rfl)) ?_
  rintro ofNat s12 ⟨hok12, hx12, hp12, hofNat⟩
  -- the spine
  have hnil12 := denote_ext hnil' (hx9.trans (hx10.trans hx12))
  refine triple_seq (strLitConsSpine_spec cons ofNat nilE _ _ _ str.toList s12
    hok12 (denote_ext hcons' hx12) hofNat hnil12) ?_
  rintro spine s13 ⟨hok13, hx13, hp13, hspine⟩
  -- `String.ofList`
  refine triple_seq (pinAt_spec s13 PIN_STRING_OF_LIST hok13.pins) ?_
  rintro slN s14 ⟨hs14, hslN⟩
  subst s14
  refine triple_seq (constE_spec s13 slN ConLeche.stringOfListName hok13
    (hslN _ rfl)) ?_
  rintro sl s15 ⟨hok15, hx15, hp15, hsl⟩
  have hspine15 := denote_ext hspine hx15
  refine triple_mono (internE_ok_spec (mode := mode) (env := env) (fe := fe)
    s15 (.app sl spine) hok15 (viewOK_app (by rw [hsl]; rfl)
      (by rw [hspine15]; rfl))) ?_
  rintro r s16 ⟨hok16, hx16, hp16, hr⟩
  refine ⟨hok16,
    hx2.trans (hx4.trans (hx6.trans (hx7.trans (hx9.trans (hx10.trans
      (hx12.trans (hx13.trans (hx15.trans hx16)))))))),
    hp16.trans (hp15.trans (hp13.trans (hp12.trans (hp10.trans (hp9.trans
      (hp7.trans (hp6.trans (hp4.trans hp2)))))))), ?_⟩
  rw [hr]
  simp only [denoteEView, denote_ext hsl hx16, denote_ext hspine15 hx16, opt2,
    ConLeche.strLitToConstructor, strSpineE]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor — the
constructor form mentions no free variable, so it is well-scoped at every
depth. -/
theorem strLitToConstructor_WScoped (str : String) (d : Nat) :
    Expr.WScoped d (ConLeche.strLitToConstructor str) := by
  apply Expr.WScoped.of_not_hasFvar
  simp only [ConLeche.strLitToConstructor]
  induction str.toList with
  | nil => simp [Expr.hasFvar]
  | cons c cs ih => simp_all [Expr.hasFvar]

section Census

#print axioms internE_ok_spec
#print axioms strLitConsSpine_spec
#print axioms strLitToConstructor_spec
#print axioms strLitToConstructor_WScoped

end Census

end ConRon.Bridge.Core
