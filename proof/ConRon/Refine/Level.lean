/-
`ConRon.Refine.Level` -- the refinement lemmas of
`crates/con-ron-core/src/level.rs` against the `Level` part of
`ConLeche/Kernel/Expr.lean` (lines 40-139) and `ConLeche/Kernel/Level.lean`
(DESIGN.md §3.5; P3.3 of §5).

Ported at task #17 from `ConRon/Spike/LevelName/Refine.lean` (task #5) by
renaming `level_name.` to `ConRon.Generated.` -- i.e. by nothing, since this
file `open`s `ConRon.Generated` -- and by qualifying the four `Name` helpers
that now live in `ConRon/Refine/Name.lean`.  All 63 generated `name.*`/`level.*`
definitions are byte-identical to the spike's, so every proof script transfers
verbatim; the crate's `level.rs` gained only the two `crate::hashmap`
dictionaries and unit tests at task #9, neither of which Charon turns into a
changed function body.

Shape, as fixed by task #5: **exact result on success**.  `ptr_eq` is `false`
in the model (DESIGN.md §3.2), so `level_beq_refl` is what makes the real
program's fast path agree.  Two of the cascade's members (`rest`,
`imax_rules`, `by_cases`) are proved against *arm-selection lemmas* for
con-leche's overlapping `match` patterns, written first as `rw [f] <;>
simp_all` one-liners; `leq_core` is the only member that consumes the
induction, at `fuel - 1`.
-/
import ConRon.Refine.Name

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Level

/-! ## `absLevel` is injective on well-formed input -/

theorem level_zero_inv' {u} (h : level.zero = ok u) : ∃ hh, u = level.Level.mk (level.LevelNode.mk hh .Zero) := ⟨_, level_zero_inv h⟩

theorem absLevel_injective {a b : level.Level} (ha : LevelWF a) (hb : LevelWF b) :
    absLevel a = absLevel b → a = b := by
  induction ha generalizing b with
  | @zero u1 h1 =>
    obtain rfl := level_zero_inv h1
    intro hab
    cases hb with
    | @zero u2 h2 =>
      obtain rfl := level_zero_inv h2
      rfl
    | @succ x2 u2 hx2 h2 =>
      obtain ⟨_, rfl⟩ := level_succ_inv h2
      simp at hab
    | @max x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_max_inv h2
      simp at hab
    | @imax x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_imax_inv h2
      simp at hab
    | @param n2 u2 hn2 h2 =>
      obtain ⟨_, rfl⟩ := level_param_inv h2
      simp at hab
  | @succ x1 u1 hx1 h1 ih1 =>
    obtain ⟨_, rfl⟩ := level_succ_inv h1
    intro hab
    cases hb with
    | @zero u2 h2 =>
      obtain rfl := level_zero_inv h2
      simp at hab
    | @succ x2 u2 hx2 h2 =>
      obtain ⟨_, rfl⟩ := level_succ_inv h2
      simp at hab
      have e1 := ih1 hx2 hab
      subst e1
      exact Result.ok_injective (h1.symm.trans h2)
    | @max x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_max_inv h2
      simp at hab
    | @imax x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_imax_inv h2
      simp at hab
    | @param n2 u2 hn2 h2 =>
      obtain ⟨_, rfl⟩ := level_param_inv h2
      simp at hab
  | @max x1 y1 u1 hx1 hy1 h1 ih1 ih2 =>
    obtain ⟨_, rfl⟩ := level_max_inv h1
    intro hab
    cases hb with
    | @zero u2 h2 =>
      obtain rfl := level_zero_inv h2
      simp at hab
    | @succ x2 u2 hx2 h2 =>
      obtain ⟨_, rfl⟩ := level_succ_inv h2
      simp at hab
    | @max x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_max_inv h2
      simp at hab
      have e1 := ih1 hx2 hab.1
      have e2 := ih2 hy2 hab.2
      subst e1
      subst e2
      exact Result.ok_injective (h1.symm.trans h2)
    | @imax x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_imax_inv h2
      simp at hab
    | @param n2 u2 hn2 h2 =>
      obtain ⟨_, rfl⟩ := level_param_inv h2
      simp at hab
  | @imax x1 y1 u1 hx1 hy1 h1 ih1 ih2 =>
    obtain ⟨_, rfl⟩ := level_imax_inv h1
    intro hab
    cases hb with
    | @zero u2 h2 =>
      obtain rfl := level_zero_inv h2
      simp at hab
    | @succ x2 u2 hx2 h2 =>
      obtain ⟨_, rfl⟩ := level_succ_inv h2
      simp at hab
    | @max x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_max_inv h2
      simp at hab
    | @imax x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_imax_inv h2
      simp at hab
      have e1 := ih1 hx2 hab.1
      have e2 := ih2 hy2 hab.2
      subst e1
      subst e2
      exact Result.ok_injective (h1.symm.trans h2)
    | @param n2 u2 hn2 h2 =>
      obtain ⟨_, rfl⟩ := level_param_inv h2
      simp at hab
  | @param n1 u1 hn1 h1 =>
    obtain ⟨_, rfl⟩ := level_param_inv h1
    intro hab
    cases hb with
    | @zero u2 h2 =>
      obtain rfl := level_zero_inv h2
      simp at hab
    | @succ x2 u2 hx2 h2 =>
      obtain ⟨_, rfl⟩ := level_succ_inv h2
      simp at hab
    | @max x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_max_inv h2
      simp at hab
    | @imax x2 y2 u2 hx2 hy2 h2 =>
      obtain ⟨_, rfl⟩ := level_imax_inv h2
      simp at hab
    | @param n2 u2 hn2 h2 =>
      obtain ⟨_, rfl⟩ := level_param_inv h2
      simp at hab
      have e1 := Name.absName_injective hn1 hn2 hab
      subst e1
      exact Result.ok_injective (h1.symm.trans h2)

theorem level_beq_refl {a : level.Level} (h : LevelWF a) : level.beq a a = ok true := by
  induction h with
  | @zero u h =>
    obtain rfl := level_zero_inv h
    rw [level.beq.eq_def]; simp [level.ptr_eq, level.hash_data]
  | @succ x u hx h ih =>
    obtain ⟨hh, rfl⟩ := level_succ_inv h
    rw [level.beq.eq_def]; simp [level.ptr_eq, level.hash_data, ih]
  | @max x y u hx hy h ih1 ih2 =>
    obtain ⟨hh, rfl⟩ := level_max_inv h
    rw [level.beq.eq_def]; simp [level.ptr_eq, level.hash_data, ih1, ih2]
  | @imax x y u hx hy h ih1 ih2 =>
    obtain ⟨hh, rfl⟩ := level_imax_inv h
    rw [level.beq.eq_def]; simp [level.ptr_eq, level.hash_data, ih1, ih2]
  | @param n u hn h =>
    obtain ⟨hh, rfl⟩ := level_param_inv h
    rw [level.beq.eq_def]; simp [level.ptr_eq, level.hash_data, Name.name_beq_refl hn]

theorem level_beq_abs {a : level.Level} (ha : LevelWF a) :
    ∀ b, level.beq a b = ok true → absLevel a = absLevel b := by
  induction ha with
  | @zero u h =>
    obtain rfl := level_zero_inv h
    intro b hb
    rw [level.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Zero =>
      simp [level.ptr_eq, level.hash_data] at hb ⊢
    | Succ y =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Max y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Imax y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Param m =>
      simp [level.ptr_eq, level.hash_data] at hb
  | @succ x u hx h ih =>
    obtain ⟨hh, rfl⟩ := level_succ_inv h
    intro b hb
    rw [level.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Zero =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Succ y =>
      simp [level.ptr_eq, level.hash_data] at hb
      split at hb
      case isFalse => simp at hb
      case isTrue => simp [ih y hb]
    | Max y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Imax y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Param m =>
      simp [level.ptr_eq, level.hash_data] at hb
  | @max x1 x2 u hx1 hx2 h ih1 ih2 =>
    obtain ⟨hh, rfl⟩ := level_max_inv h
    intro b hb
    rw [level.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Zero =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Succ y =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Max y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
      split at hb
      case isFalse => simp at hb
      case isTrue =>
        simp only [bind_eq_ok_iff] at hb
        obtain ⟨z, hz, hb⟩ := hb
        cases z
        · simp at hb
        · simp [ih1 y1 hz, ih2 y2 (by simpa using hb)]
    | Imax y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Param m =>
      simp [level.ptr_eq, level.hash_data] at hb
  | @imax x1 x2 u hx1 hx2 h ih1 ih2 =>
    obtain ⟨hh, rfl⟩ := level_imax_inv h
    intro b hb
    rw [level.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Zero =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Succ y =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Max y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Imax y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
      split at hb
      case isFalse => simp at hb
      case isTrue =>
        simp only [bind_eq_ok_iff] at hb
        obtain ⟨z, hz, hb⟩ := hb
        cases z
        · simp at hb
        · simp [ih1 y1 hz, ih2 y2 (by simpa using hb)]
    | Param m =>
      simp [level.ptr_eq, level.hash_data] at hb
  | @param n u hn h =>
    obtain ⟨hh, rfl⟩ := level_param_inv h
    intro b hb
    rw [level.beq.eq_def] at hb
    obtain ⟨⟨h2, kb⟩⟩ := b
    cases kb with
    | Zero =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Succ y =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Max y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Imax y1 y2 =>
      simp [level.ptr_eq, level.hash_data] at hb
    | Param m =>
      simp [level.ptr_eq, level.hash_data] at hb
      split at hb
      case isFalse => simp at hb
      case isTrue => simp [Name.name_beq_abs hn m hb]

/-! ## The per-function refinements

The two structural induction principles these use (`Level.ind'`, `Name.ind'`)
live in `ConRon/Refine/Abs.lean`. -/

theorem level_has_param_refines' (u : level.Level) :
    ∀ b, level.level_has_param u = ok b → b = ConLeche.levelHasParam (absLevel u) := by
  induction u using Level.ind' with
  | zero h =>
    intro b hb; rw [level.level_has_param.eq_def] at hb
    simp at hb; simp [← hb, ConLeche.levelHasParam]
  | param h n =>
    intro b hb; rw [level.level_has_param.eq_def] at hb
    simp at hb; simp [← hb, ConLeche.levelHasParam]
  | succ h x ih =>
    intro b hb; rw [level.level_has_param.eq_def] at hb
    simp at hb; simp [ConLeche.levelHasParam, ih b hb]
  | max h x y ih1 ih2 =>
    intro b hb; rw [level.level_has_param.eq_def] at hb
    simp at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, rfl⟩
    · simp [ConLeche.levelHasParam, ← ih1 _ h1, ih2 _ h2]
    · simp [ConLeche.levelHasParam, ← ih1 _ h1]
  | imax h x y ih1 ih2 =>
    intro b hb; rw [level.level_has_param.eq_def] at hb
    simp at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, rfl⟩
    · simp [ConLeche.levelHasParam, ← ih1 _ h1, ih2 _ h2]
    · simp [ConLeche.levelHasParam, ← ih1 _ h1]

theorem LevelWF.succ_inv {h a} (w : LevelWF (.mk (.mk h (.Succ a)))) : LevelWF a := by
  cases w with
  | @zero u hu =>
    exact absurd (level_zero_inv hu) (by simp)
  | @succ x u hx hu =>
    obtain ⟨_, hu⟩ := level_succ_inv hu
    cases hu
    exact hx
  | @max x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_max_inv hu
    simp at hu
  | @imax x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_imax_inv hu
    simp at hu
  | @param m u hm hu =>
    obtain ⟨_, hu⟩ := level_param_inv hu
    simp at hu

theorem LevelWF.max_inv {h a b} (w : LevelWF (.mk (.mk h (.Max a b)))) : LevelWF a ∧ LevelWF b := by
  cases w with
  | @zero u hu =>
    exact absurd (level_zero_inv hu) (by simp)
  | @succ x u hx hu =>
    obtain ⟨_, hu⟩ := level_succ_inv hu
    simp at hu
  | @max x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_max_inv hu
    cases hu
    exact ⟨hx, hy⟩
  | @imax x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_imax_inv hu
    simp at hu
  | @param m u hm hu =>
    obtain ⟨_, hu⟩ := level_param_inv hu
    simp at hu

theorem LevelWF.imax_inv {h a b} (w : LevelWF (.mk (.mk h (.Imax a b)))) : LevelWF a ∧ LevelWF b := by
  cases w with
  | @zero u hu =>
    exact absurd (level_zero_inv hu) (by simp)
  | @succ x u hx hu =>
    obtain ⟨_, hu⟩ := level_succ_inv hu
    simp at hu
  | @max x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_max_inv hu
    simp at hu
  | @imax x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_imax_inv hu
    cases hu
    exact ⟨hx, hy⟩
  | @param m u hm hu =>
    obtain ⟨_, hu⟩ := level_param_inv hu
    simp at hu

theorem LevelWF.param_inv {h n} (w : LevelWF (.mk (.mk h (.Param n)))) : NameWF n := by
  cases w with
  | @zero u hu =>
    exact absurd (level_zero_inv hu) (by simp)
  | @succ x u hx hu =>
    obtain ⟨_, hu⟩ := level_succ_inv hu
    simp at hu
  | @max x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_max_inv hu
    simp at hu
  | @imax x y u hx hy hu =>
    obtain ⟨_, hu⟩ := level_imax_inv hu
    simp at hu
  | @param m u hm hu =>
    obtain ⟨_, hu⟩ := level_param_inv hu
    cases hu
    exact hm

theorem is_never_zero_refines' (u : level.Level) :
    ∀ b, level.is_never_zero u = ok b → b = ConLeche.Level.isNeverZero (absLevel u) := by
  induction u using Level.ind' with
  | zero h => intro b hb; rw [level.is_never_zero.eq_def] at hb; simp at hb
              simp [← hb, ConLeche.Level.isNeverZero]
  | param h n => intro b hb; rw [level.is_never_zero.eq_def] at hb; simp at hb
                 simp [← hb, ConLeche.Level.isNeverZero]
  | succ h x ih => intro b hb; rw [level.is_never_zero.eq_def] at hb; simp at hb
                   simp [← hb, ConLeche.Level.isNeverZero]
  | imax h x y ih1 ih2 => intro b hb; rw [level.is_never_zero.eq_def] at hb; simp at hb
                          simp [ConLeche.Level.isNeverZero, ih2 b hb]
  | max h x y ih1 ih2 =>
    intro b hb; rw [level.is_never_zero.eq_def] at hb; simp at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, rfl⟩
    · simp [ConLeche.Level.isNeverZero, ← ih1 _ h1, ih2 _ h2]
    · simp [ConLeche.Level.isNeverZero, ← ih1 _ h1]

theorem combining_refines : ∀ (l : level.Level) (r : level.Level), LevelWF l → LevelWF r →
    ∀ w, level.combining l r = ok w →
      absLevel w = ConLeche.Level.combining (absLevel l) (absLevel r) ∧ LevelWF w := by
  intro l
  induction l using Level.ind' with
  | zero h =>
    intro r hl hr w hw
    rw [level.combining.eq_def] at hw; simp at hw
    subst hw; exact ⟨by simp [ConLeche.Level.combining], hr⟩
  | succ h a ih =>
    intro r hl hr w hw
    obtain ⟨⟨h2, kr⟩⟩ := r
    rw [level.combining.eq_def] at hw
    cases kr with
    | Zero => simp at hw; subst hw; exact ⟨by simp [ConLeche.Level.combining], hl⟩
    | Succ b =>
      simp at hw
      obtain ⟨l1, hl1, hw⟩ := hw
      obtain ⟨_, rfl⟩ := level_succ_inv hw
      obtain ⟨e1, e2⟩ := ih b (LevelWF.succ_inv hl) (LevelWF.succ_inv hr) l1 hl1
      exact ⟨by simp [ConLeche.Level.combining, e1], LevelWF.succ e2 hw⟩
    | Max y1 y2 =>
      simp at hw
      obtain ⟨_, rfl⟩ := level_max_inv hw
      exact ⟨by simp [ConLeche.Level.combining], LevelWF.max hl hr hw⟩
    | Imax y1 y2 =>
      simp at hw
      obtain ⟨_, rfl⟩ := level_max_inv hw
      exact ⟨by simp [ConLeche.Level.combining], LevelWF.max hl hr hw⟩
    | Param m =>
      simp at hw
      obtain ⟨_, rfl⟩ := level_max_inv hw
      exact ⟨by simp [ConLeche.Level.combining], LevelWF.max hl hr hw⟩
  | max h a b ih1 ih2 =>
    intro r hl hr w hw
    obtain ⟨⟨h2, kr⟩⟩ := r
    rw [level.combining.eq_def] at hw
    cases kr with
    | Zero => simp at hw; subst hw; exact ⟨by simp [ConLeche.Level.combining], hl⟩
    | Succ b1 | Max y1 y2 | Imax y1 y2 | Param m =>
      simp at hw
      obtain ⟨_, rfl⟩ := level_max_inv hw
      exact ⟨by simp [ConLeche.Level.combining], LevelWF.max hl hr hw⟩
  | imax h a b ih1 ih2 =>
    intro r hl hr w hw
    obtain ⟨⟨h2, kr⟩⟩ := r
    rw [level.combining.eq_def] at hw
    cases kr with
    | Zero => simp at hw; subst hw; exact ⟨by simp [ConLeche.Level.combining], hl⟩
    | Succ b1 | Max y1 y2 | Imax y1 y2 | Param m =>
      simp at hw
      obtain ⟨_, rfl⟩ := level_max_inv hw
      exact ⟨by simp [ConLeche.Level.combining], LevelWF.max hl hr hw⟩
  | param h n =>
    intro r hl hr w hw
    obtain ⟨⟨h2, kr⟩⟩ := r
    rw [level.combining.eq_def] at hw
    cases kr with
    | Zero => simp at hw; subst hw; exact ⟨by simp [ConLeche.Level.combining], hl⟩
    | Succ b1 | Max y1 y2 | Imax y1 y2 | Param m =>
      simp at hw
      obtain ⟨_, rfl⟩ := level_max_inv hw
      exact ⟨by simp [ConLeche.Level.combining], LevelWF.max hl hr hw⟩

theorem is_zero_kind_refines (u : level.Level) (b : Bool) :
    level.is_zero_kind u = ok b → b = decide (absLevel u = .zero) := by
  obtain ⟨⟨hh, k⟩⟩ := u
  cases k <;> (intro h; simp [level.is_zero_kind] at h; simp [← h])

theorem is_one_kind_refines (u : level.Level) (b : Bool) :
    level.is_one_kind u = ok b → b = decide (absLevel u = .succ .zero) := by
  obtain ⟨⟨hh, k⟩⟩ := u
  cases k with
  | Succ v =>
    intro h; simp [level.is_one_kind] at h
    have := is_zero_kind_refines v b h
    simp [this]
  | _ => intro h; simp [level.is_one_kind] at h; simp [← h]

theorem simplify_refines' : ∀ (u : level.Level), LevelWF u → ∀ u', level.simplify u = ok u' →
    absLevel u' = ConLeche.Level.simplify (absLevel u) ∧ LevelWF u' := by
  intro u
  induction u using Level.ind' with
  | zero h =>
    intro hu u' hu'
    rw [level.simplify.eq_def] at hu'; simp at hu'
    obtain rfl := (level_zero_inv hu').symm
    exact ⟨by simp [ConLeche.Level.simplify], LevelWF.zero hu'⟩
  | param h n =>
    intro hu u' hu'
    rw [level.simplify.eq_def] at hu'; simp at hu'
    obtain ⟨_, rfl⟩ := level_param_inv hu'
    exact ⟨by simp [ConLeche.Level.simplify], LevelWF.param (LevelWF.param_inv hu) hu'⟩
  | succ h x ih =>
    intro hu u' hu'
    rw [level.simplify.eq_def] at hu'; simp at hu'
    obtain ⟨l1, hl1, hu'⟩ := hu'
    obtain ⟨e1, e2⟩ := ih (LevelWF.succ_inv hu) l1 hl1
    obtain ⟨_, rfl⟩ := level_succ_inv hu'
    exact ⟨by simp [ConLeche.Level.simplify, e1], LevelWF.succ e2 hu'⟩
  | max h x y ih1 ih2 =>
    intro hu u' hu'
    rw [level.simplify.eq_def] at hu'; simp at hu'
    obtain ⟨l1, hl1, l2, hl2, hu'⟩ := hu'
    obtain ⟨hx, hy⟩ := LevelWF.max_inv hu
    obtain ⟨e1, e2⟩ := ih1 hx l1 hl1
    obtain ⟨f1, f2⟩ := ih2 hy l2 hl2
    obtain ⟨g1, g2⟩ := combining_refines l1 l2 e2 f2 u' hu'
    exact ⟨by simp [ConLeche.Level.simplify, g1, e1, f1], g2⟩
  | imax h x y ih1 ih2 =>
    intro hu u' hu'
    rw [level.simplify.eq_def] at hu'; simp at hu'
    obtain ⟨ls, hls, rs, hrs, hcase⟩ := hu'
    obtain ⟨hx, hy⟩ := LevelWF.imax_inv hu
    obtain ⟨e1, e2⟩ := ih1 hx ls hls
    obtain ⟨f1, f2⟩ := ih2 hy rs hrs
    rcases hcase with ⟨hz, ⟨ho, hm⟩ | ⟨ho, rfl⟩⟩ | ⟨hz, rfl⟩
    · have hz' := is_zero_kind_refines ls false hz
      have ho' := is_one_kind_refines ls false ho
      simp at hz' ho'
      obtain ⟨⟨hr2, kr⟩⟩ := rs
      cases kr with
      | Zero =>
        simp at hm
        obtain rfl := (level_zero_inv hm).symm
        refine ⟨by simp [ConLeche.Level.simplify, ← e1, ← f1, hz', ho'], LevelWF.zero hm⟩
      | Succ v =>
        obtain ⟨g1, g2⟩ := combining_refines ls _ e2 f2 u' hm
        refine ⟨by simp [ConLeche.Level.simplify, ← e1, ← f1, hz', ho', g1], g2⟩
      | Max v1 v2 | Imax v1 v2 | Param m =>
        obtain ⟨_, rfl⟩ := level_imax_inv hm
        refine ⟨by simp [ConLeche.Level.simplify, ← e1, ← f1, hz', ho'], LevelWF.imax e2 f2 hm⟩
    · have ho' := is_one_kind_refines ls true ho
      simp at ho'
      refine ⟨by simp [ConLeche.Level.simplify, ← e1, ← f1, ho'], f2⟩
    · have hz' := is_zero_kind_refines ls true hz
      simp at hz'
      refine ⟨by simp [ConLeche.Level.simplify, ← e1, ← f1, hz'], f2⟩

theorem subst_go_refines {ks : alloc.vec.Vec name.Name} {vs : alloc.vec.Vec level.Level}
    {n : name.Name} (hks : ∀ k ∈ ks.val, NameWF k) (hvs : ∀ v ∈ vs.val, LevelWF v)
    (hn : NameWF n) :
    ∀ m (i : Std.Usize), ks.length - i.val ≤ m → ∀ u', level.subst_go ks vs i n = ok u' →
      absLevel u' = ConLeche.Level.subst.go ((ks.val.map absName).drop i.val)
        ((vs.val.map absLevel).drop i.val) (absName n) ∧ LevelWF u' := by
  intro m
  induction m with
  | zero =>
    intro i hi u' hu'
    rw [level.subst_go.eq_def] at hu'
    rw [if_pos (by scalar_tac)] at hu'
    simp at hu'
    obtain ⟨_, rfl⟩ := level_param_inv hu'
    rw [List.drop_eq_nil_of_le (by simp; scalar_tac)]
    exact ⟨by simp [ConLeche.Level.subst.go], LevelWF.param hn hu'⟩
  | succ m ih =>
    intro i hi u' hu'
    rw [level.subst_go.eq_def] at hu'
    simp only [] at hu'
    split at hu'
    · simp at hu'
      obtain ⟨_, rfl⟩ := level_param_inv hu'
      rw [List.drop_eq_nil_of_le (by simp; scalar_tac)]
      exact ⟨by simp [ConLeche.Level.subst.go], LevelWF.param hn hu'⟩
    · rename_i hlt
      have hbk : i.val < ks.length := by scalar_tac
      split at hu'
      · rename_i hlt2
        simp at hu'
        obtain ⟨_, rfl⟩ := level_param_inv hu'
        rw [show (vs.val.map absLevel).drop i.val = [] from
          List.drop_eq_nil_of_le (by simp; scalar_tac)]
        rw [List.drop_eq_getElem_cons (l := ks.val.map absName) (by simp; scalar_tac)]
        exact ⟨by simp [ConLeche.Level.subst.go], LevelWF.param hn hu'⟩
      · rename_i hlt2
        have hbv : i.val < vs.length := by scalar_tac
        have hmax : i.val + 1 ≤ Std.Usize.max := by have := ks.slice.property; scalar_tac
        obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
        obtain ⟨k, hk, hkv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ks i hbk)
        obtain ⟨v, hv, hvv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec vs i hbv)
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hk, hv, hw,
          Result.ok.injEq] at hu'
        obtain ⟨k', rfl, c, hc, hu'⟩ := hu'
        rw [show (ks.val.map absName).drop i.val
              = absName ks.val[i.val] :: (ks.val.map absName).drop (i.val + 1) from by
            rw [List.drop_eq_getElem_cons (by simp; scalar_tac)]; simp]
        rw [show (vs.val.map absLevel).drop i.val
              = absLevel vs.val[i.val] :: (vs.val.map absLevel).drop (i.val + 1) from by
            rw [List.drop_eq_getElem_cons (by simp; scalar_tac)]; simp]
        simp only [ConLeche.Level.subst.go]
        have hce : c = decide (absName k = absName n) :=
          Name.name_beq_exact' (hks k (hkv ▸ List.getElem_mem _)) hn hc
        cases c
        · simp only [Bool.false_eq, decide_eq_false_iff_not] at hce
          rw [if_neg (by rw [← hkv]; exact hce)]
          simp at hu'
          rw [← hwv]
          exact ih w (by scalar_tac) u' hu'
        · simp only [Bool.true_eq, decide_eq_true_eq] at hce
          rw [if_pos (by rw [← hkv]; exact hce)]
          simp at hu'
          subst hu'
          exact ⟨by rw [hvv], hvs v (hvv ▸ List.getElem_mem _)⟩

theorem subst_refines' : ∀ (u : level.Level), LevelWF u →
    ∀ (ks : alloc.vec.Vec name.Name) (vs : alloc.vec.Vec level.Level),
      (∀ k ∈ ks.val, NameWF k) → (∀ v ∈ vs.val, LevelWF v) →
      ∀ u', level.subst ks vs u = ok u' →
        absLevel u' =
          ConLeche.Level.subst (ks.val.map absName) (vs.val.map absLevel) (absLevel u)
        ∧ LevelWF u' := by
  intro u
  induction u using Level.ind' with
  | zero h =>
    intro hu ks vs hks hvs u' hu'
    rw [level.subst.eq_def] at hu'; simp at hu'
    obtain rfl := (level_zero_inv hu').symm
    exact ⟨by simp [ConLeche.Level.subst], LevelWF.zero hu'⟩
  | param h n =>
    intro hu ks vs hks hvs u' hu'
    rw [level.subst.eq_def] at hu'; simp at hu'
    have := subst_go_refines hks hvs (LevelWF.param_inv hu) ks.length 0#usize
      (by scalar_tac) u' hu'
    simpa [ConLeche.Level.subst] using this
  | succ h x ih =>
    intro hu ks vs hks hvs u' hu'
    rw [level.subst.eq_def] at hu'; simp at hu'
    obtain ⟨l1, hl1, hu'⟩ := hu'
    obtain ⟨e1, e2⟩ := ih (LevelWF.succ_inv hu) ks vs hks hvs l1 hl1
    obtain ⟨_, rfl⟩ := level_succ_inv hu'
    exact ⟨by simp [ConLeche.Level.subst, e1], LevelWF.succ e2 hu'⟩
  | max h x y ih1 ih2 =>
    intro hu ks vs hks hvs u' hu'
    rw [level.subst.eq_def] at hu'; simp at hu'
    obtain ⟨l1, hl1, l2, hl2, hu'⟩ := hu'
    obtain ⟨hx, hy⟩ := LevelWF.max_inv hu
    obtain ⟨e1, e2⟩ := ih1 hx ks vs hks hvs l1 hl1
    obtain ⟨f1, f2⟩ := ih2 hy ks vs hks hvs l2 hl2
    obtain ⟨_, rfl⟩ := level_max_inv hu'
    exact ⟨by simp [ConLeche.Level.subst, e1, f1], LevelWF.max e2 f2 hu'⟩
  | imax h x y ih1 ih2 =>
    intro hu ks vs hks hvs u' hu'
    rw [level.subst.eq_def] at hu'; simp at hu'
    obtain ⟨l1, hl1, l2, hl2, hu'⟩ := hu'
    obtain ⟨hx, hy⟩ := LevelWF.imax_inv hu
    obtain ⟨e1, e2⟩ := ih1 hx ks vs hks hvs l1 hl1
    obtain ⟨f1, f2⟩ := ih2 hy ks vs hks hvs l2 hl2
    obtain ⟨_, rfl⟩ := level_imax_inv hu'
    exact ⟨by simp [ConLeche.Level.subst, e1, f1], LevelWF.imax e2 f2 hu'⟩


/-- The `leq_core` refinement statement at one fuel value: the induction
hypothesis that the whole `rest`/`imax_rules`/`by_cases` cascade runs on. -/
abbrev LeqCoreSpec (fuel : Std.U64) : Prop :=
  ∀ l r, LevelWF l → LevelWF r → ∀ (diff : Std.I64) (o : Option Bool),
    level.leq_core fuel l r diff = ok o →
      ConLeche.Level.leqCore fuel.val (absLevel l) (absLevel r) diff.val = o

theorem by_cases_refines_aux {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {p : name.Name} {l r : level.Level} (hp : NameWF p) (hl : LevelWF l) (hr : LevelWF r)
    {diff : Std.I64} {o : Option Bool} :
    level.by_cases fuel p l r diff = ok o →
      ConLeche.Level.byCases fuel.val (absName p) (absLevel l) (absLevel r) diff.val = o := by
  intro h
  rw [level.by_cases.eq_def] at h
  simp [name.singleton, level.singleton] at h
  obtain ⟨ks, hks, z, hz, vz, hvz, l2, hl2, l0, hl0, r2, hr2, r0, hr0, c, hc, h⟩ := h
  -- the two singleton vectors
  obtain ⟨ks', hks', hksv⟩ := vec_singleton (α := name.Name) p
  have : ks = ks' := Result.ok_injective (hks.symm.trans hks')
  subst this
  obtain ⟨vz', hvz', hvzv⟩ := vec_singleton (α := level.Level) z
  have : vz = vz' := Result.ok_injective (hvz.symm.trans hvz')
  subst this
  have hzwf : LevelWF z := LevelWF.zero hz
  have habsz : absLevel z = .zero := by rw [level_zero_inv hz]; simp
  have hkswf : ∀ k ∈ ks.val, NameWF k := by rw [hksv]; simpa using hp
  have hvzwf : ∀ v ∈ vz.val, LevelWF v := by rw [hvzv]; simpa using hzwf
  -- the zero substitution on both sides
  obtain ⟨e1, e1w⟩ := subst_refines' l hl ks vz hkswf hvzwf l2 hl2
  obtain ⟨e2, e2w⟩ := simplify_refines' l2 e1w l0 hl0
  obtain ⟨f1, f1w⟩ := subst_refines' r hr ks vz hkswf hvzwf r2 hr2
  obtain ⟨f2, f2w⟩ := simplify_refines' r2 f1w r0 hr0
  rw [hksv, hvzv] at e1 f1
  simp only [List.map_cons, List.map_nil, habsz] at e1 f1
  have hcl := hQ l0 r0 e2w f2w diff c hc
  rw [ConLeche.Level.byCases]
  simp only [e2, e1, f2, f1] at hcl ⊢
  rw [hcl]
  cases c with
  | none => simp at h; simp [← h]
  | some b =>
    cases b
    · simp at h; simp [← h]
    · simp at h
      obtain ⟨l4, hl4, l5, hl5, vp, hvp, l6, hl6, ls, hls, l7, hl7, rs, hrs, hlast⟩ := h
      obtain ⟨vp', hvp', hvpv⟩ := vec_singleton (α := level.Level) l5
      have hvpe : vp = vp' := Result.ok_injective (hvp.symm.trans hvp')
      subst hvpe
      have hl5wf : LevelWF l5 := LevelWF.succ (LevelWF.param hp hl4) hl5
      have habsl5 : absLevel l5 = .succ (.param (absName p)) := by
        obtain ⟨_, h5⟩ := level_succ_inv hl5
        obtain ⟨_, h4⟩ := level_param_inv hl4
        rw [h5, h4]; simp
      have hvpwf : ∀ v ∈ vp.val, LevelWF v := by rw [hvpv]; simpa using hl5wf
      obtain ⟨g1, g1w⟩ := subst_refines' l hl ks vp hkswf hvpwf l6 hl6
      obtain ⟨g2, g2w⟩ := simplify_refines' l6 g1w ls hls
      obtain ⟨k1, k1w⟩ := subst_refines' r hr ks vp hkswf hvpwf l7 hl7
      obtain ⟨k2, k2w⟩ := simplify_refines' l7 k1w rs hrs
      rw [hksv, hvpv] at g1 k1
      simp only [List.map_cons, List.map_nil, habsl5] at g1 k1
      have hfin := hQ ls rs g2w k2w diff o hlast
      simp only [g2, g1, k2, k1] at hfin
      simpa using hfin

theorem is_imax_param_true {u : level.Level} (h : level.is_imax_param u = ok true) :
    ∃ hh a hh2 p, u = .mk (.mk hh (.Imax a (.mk (.mk hh2 (.Param p))))) := by
  obtain ⟨⟨hh, k⟩⟩ := u
  cases k with
  | Imax a b =>
    obtain ⟨⟨hh2, k2⟩⟩ := b
    cases k2 <;> simp [level.is_imax_param] at h ⊢
  | _ => simp [level.is_imax_param] at h

theorem is_imax_param_false {u : level.Level} (h : level.is_imax_param u = ok false) :
    ∀ a p, absLevel u ≠ .imax a (.param p) := by
  obtain ⟨⟨hh, k⟩⟩ := u
  cases k with
  | Imax a b =>
    obtain ⟨⟨hh2, k2⟩⟩ := b
    cases k2 <;> simp [level.is_imax_param] at h ⊢
  | _ => intro a p; simp

theorem by_cases_left_refines {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool}
    (hb1 : level.is_imax_param l = ok true) :
    level.by_cases_left fuel l r diff = ok o →
      ConLeche.Level.imaxRules fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  obtain ⟨hh, a, hh2, p, rfl⟩ := is_imax_param_true hb1
  rw [level.by_cases_left.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, level.LevelNode.kind._simpLemma_,
    level.Level._0._simpLemma_] at h
  simp only [absLevel_mk, absLevelKind]
  rw [ConLeche.Level.imaxRules]
  exact by_cases_refines_aux hQ (LevelWF.param_inv (LevelWF.imax_inv hl).2) hl hr h

theorem by_cases_right_refines {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool}
    (hb1 : level.is_imax_param l = ok false) (hb2 : level.is_imax_param r = ok true) :
    level.by_cases_right fuel l r diff = ok o →
      ConLeche.Level.imaxRules fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  obtain ⟨hh, a, hh2, p, rfl⟩ := is_imax_param_true hb2
  rw [level.by_cases_right.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok, level.LevelNode.kind._simpLemma_,
    level.Level._0._simpLemma_] at h
  simp only [absLevel_mk, absLevelKind]
  rw [ConLeche.Level.imaxRules]
  · exact by_cases_refines_aux hQ (LevelWF.param_inv (LevelWF.imax_inv hr).2) hl hr h
  · simpa using is_imax_param_false hb1

/-! ### The Lean-side arm selection of `ConLeche.Level.imaxRules` -/

theorem imaxRules_none {fuel l r diff}
    (h1 : ∀ a p, l ≠ .imax a (.param p)) (h2 : ∀ x p, r ≠ .imax x (.param p))
    (h3 : ∀ a x y, l ≠ .imax a (.imax x y)) (h4 : ∀ a x y, l ≠ .imax a (.max x y))
    (h5 : ∀ x j k, r ≠ .imax x (.imax j k)) (h6 : ∀ x j k, r ≠ .imax x (.max j k)) :
    ConLeche.Level.imaxRules fuel l r diff = none := by
  rw [ConLeche.Level.imaxRules] <;> simp_all

theorem imaxRules_r_imax_imax {fuel l x j k diff}
    (h1 : ∀ a p, l ≠ .imax a (.param p))
    (h3 : ∀ a u v, l ≠ .imax a (.imax u v)) (h4 : ∀ a u v, l ≠ .imax a (.max u v)) :
    ConLeche.Level.imaxRules fuel l (.imax x (.imax j k)) diff
      = ConLeche.Level.leqCore fuel l (.max (.imax x k) (.imax j k)) diff := by
  rw [ConLeche.Level.imaxRules] <;> simp_all

theorem imaxRules_r_imax_max {fuel l x j k diff}
    (h1 : ∀ a p, l ≠ .imax a (.param p))
    (h3 : ∀ a u v, l ≠ .imax a (.imax u v)) (h4 : ∀ a u v, l ≠ .imax a (.max u v)) :
    ConLeche.Level.imaxRules fuel l (.imax x (.max j k)) diff
      = ConLeche.Level.leqCore fuel l
          (ConLeche.Level.simplify (.max (.imax x j) (.imax x k))) diff := by
  rw [ConLeche.Level.imaxRules] <;> simp_all

theorem imaxRules_l_imax_imax {fuel a x y r diff} (h2 : ∀ q s, r ≠ .imax q (.param s)) :
    ConLeche.Level.imaxRules fuel (.imax a (.imax x y)) r diff
      = ConLeche.Level.leqCore fuel (.max (.imax a y) (.imax x y)) r diff := by
  rw [ConLeche.Level.imaxRules]; simp_all

theorem imaxRules_l_imax_max {fuel a x y r diff} (h2 : ∀ q s, r ≠ .imax q (.param s)) :
    ConLeche.Level.imaxRules fuel (.imax a (.max x y)) r diff
      = ConLeche.Level.leqCore fuel
          (ConLeche.Level.simplify (.max (.imax a x) (.imax a y))) r diff := by
  rw [ConLeche.Level.imaxRules]; simp_all

theorem imax_rules_distrib_right_refines {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool}
    (hb1 : level.is_imax_param l = ok false) (hb2 : level.is_imax_param r = ok false)
    (h3 : ∀ a x y, absLevel l ≠ .imax a (.imax x y))
    (h4 : ∀ a x y, absLevel l ≠ .imax a (.max x y)) :
    level.imax_rules_distrib_right fuel l r diff = ok o →
      ConLeche.Level.imaxRules fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  have h1 := is_imax_param_false hb1
  rw [level.imax_rules_distrib_right.eq_def] at h
  obtain ⟨⟨hh, kr⟩⟩ := r
  cases kr with
  | Zero | Succ _ | Max _ _ | Param _ =>
    simp at h
    simp only [absLevel_mk, absLevelKind]
    rw [imaxRules_none h1 (by simp) h3 h4 (by simp) (by simp), ← h]
  | Imax x y =>
    obtain ⟨hx, hy⟩ := LevelWF.imax_inv hr
    obtain ⟨⟨hh2, ky⟩⟩ := y
    cases ky with
    | Zero | Succ _ =>
      simp at h
      simp only [absLevel_mk, absLevelKind]
      rw [imaxRules_none h1 (by simp) h3 h4 (by simp) (by simp), ← h]
    | Param q => simp [level.is_imax_param] at hb2
    | Imax j k =>
      obtain ⟨hj, hk⟩ := LevelWF.imax_inv hy
      simp at h
      obtain ⟨n1, hn1, n2, hn2, nr, hnr, hlast⟩ := h
      have hn1w := LevelWF.imax hx hk hn1
      have hn2w := LevelWF.imax hj hk hn2
      obtain ⟨_, rfl⟩ := level_imax_inv hn1
      obtain ⟨_, rfl⟩ := level_imax_inv hn2
      obtain ⟨_, rfl⟩ := level_max_inv hnr
      have hres := hQ l _ hl (LevelWF.max hn1w hn2w hnr) diff o hlast
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [imaxRules_r_imax_imax h1 h3 h4]
      exact hres
    | Max j k =>
      obtain ⟨hj, hk⟩ := LevelWF.max_inv hy
      simp at h
      obtain ⟨n1, hn1, n2, hn2, n3, hn3, nr, hnr, hlast⟩ := h
      have hn1w := LevelWF.imax hx hj hn1
      have hn2w := LevelWF.imax hx hk hn2
      have hn3w := LevelWF.max hn1w hn2w hn3
      obtain ⟨_, rfl⟩ := level_imax_inv hn1
      obtain ⟨_, rfl⟩ := level_imax_inv hn2
      obtain ⟨_, rfl⟩ := level_max_inv hn3
      obtain ⟨e1, e1w⟩ := simplify_refines' _ hn3w nr hnr
      have hres := hQ l nr hl e1w diff o hlast
      simp only [absLevel_mk, absLevelKind] at e1 hres ⊢
      rw [imaxRules_r_imax_max h1 h3 h4, ← e1]
      exact hres

theorem imax_rules_distrib_refines {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool}
    (hb1 : level.is_imax_param l = ok false) (hb2 : level.is_imax_param r = ok false) :
    level.imax_rules_distrib fuel l r diff = ok o →
      ConLeche.Level.imaxRules fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  have h2 := is_imax_param_false hb2
  rw [level.imax_rules_distrib.eq_def] at h
  obtain ⟨⟨hh, kl⟩⟩ := l
  cases kl with
  | Zero | Succ _ | Max _ _ | Param _ =>
    simp at h
    exact imax_rules_distrib_right_refines hQ hl hr hb1 hb2 (by simp) (by simp) h
  | Imax a b =>
    obtain ⟨ha, hbw⟩ := LevelWF.imax_inv hl
    obtain ⟨⟨hh2, kb⟩⟩ := b
    cases kb with
    | Zero | Succ _ =>
      simp at h
      exact imax_rules_distrib_right_refines hQ hl hr hb1 hb2 (by simp) (by simp) h
    | Param p => simp [level.is_imax_param] at hb1
    | Imax x y =>
      obtain ⟨hx, hy⟩ := LevelWF.imax_inv hbw
      simp at h
      obtain ⟨n1, hn1, n2, hn2, nl, hnl, hlast⟩ := h
      have hn1w := LevelWF.imax ha hy hn1
      have hn2w := LevelWF.imax hx hy hn2
      obtain ⟨_, rfl⟩ := level_imax_inv hn1
      obtain ⟨_, rfl⟩ := level_imax_inv hn2
      obtain ⟨_, rfl⟩ := level_max_inv hnl
      have hres := hQ _ r (LevelWF.max hn1w hn2w hnl) hr diff o hlast
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [imaxRules_l_imax_imax h2]
      exact hres
    | Max x y =>
      obtain ⟨hx, hy⟩ := LevelWF.max_inv hbw
      simp at h
      obtain ⟨n1, hn1, n2, hn2, n3, hn3, nl, hnl, hlast⟩ := h
      have hn1w := LevelWF.imax ha hx hn1
      have hn2w := LevelWF.imax ha hy hn2
      have hn3w := LevelWF.max hn1w hn2w hn3
      obtain ⟨_, rfl⟩ := level_imax_inv hn1
      obtain ⟨_, rfl⟩ := level_imax_inv hn2
      obtain ⟨_, rfl⟩ := level_max_inv hn3
      obtain ⟨e1, e1w⟩ := simplify_refines' _ hn3w nl hnl
      have hres := hQ nl r e1w hr diff o hlast
      simp only [absLevel_mk, absLevelKind] at e1 hres ⊢
      rw [imaxRules_l_imax_max h2, ← e1]
      exact hres

theorem imax_rules_refines {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool} :
    level.imax_rules fuel l r diff = ok o →
      ConLeche.Level.imaxRules fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  rw [level.imax_rules.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b1, hb1, h⟩ := h
  cases b1
  · simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
    obtain ⟨b2, hb2, h⟩ := h
    cases b2
    · simp only [Bool.false_eq_true, if_false] at h
      exact imax_rules_distrib_refines hQ hl hr hb1 hb2 h
    · simp only [if_true] at h
      exact by_cases_right_refines hQ hl hr hb1 hb2 h
  · simp only [if_true] at h
    exact by_cases_left_refines hQ hl hr hb1 h

theorem level_beq_exact' {a b : level.Level} (ha : LevelWF a) (hb : LevelWF b) {c : Bool}
    (h : level.beq a b = ok c) : c = decide (absLevel a = absLevel b) := by
  cases c
  · symm; simp only [decide_eq_false_iff_not]
    intro heq
    have hab : a = b := absLevel_injective ha hb heq
    subst hab
    rw [level_beq_refl ha] at h
    simp at h
  · symm; simp only [decide_eq_true_eq]
    exact level_beq_abs ha b h

theorem i64_add_val {x y z : Std.I64} (h : x + y = ok z) : z.val = x.val + y.val := by
  have he := Std.IScalar.add_equiv x y
  rw [h] at he
  simp only [Result.match.ok] at he
  exact he.2.1

theorem i64_sub_val {x y z : Std.I64} (h : x - y = ok z) : z.val = x.val - y.val := by
  have he := Std.IScalar.sub_equiv x y
  rw [h] at he
  simp only [Result.match.ok] at he
  exact he.2.1

theorem rest_succ {fuel s r diff} : ConLeche.Level.rest fuel (.succ s) r diff = ConLeche.Level.leqCore fuel s r (diff - 1) := by
  rw [ConLeche.Level.rest]
theorem rest_r_succ {fuel l s diff} (h : ∀ t, l ≠ .succ t) :
    ConLeche.Level.rest fuel l (.succ s) diff = ConLeche.Level.leqCore fuel l s (diff + 1) := by
  rw [ConLeche.Level.rest]; simp_all
theorem rest_max {fuel a b r diff} (h : ∀ s, r ≠ .succ s) :
    ConLeche.Level.rest fuel (.max a b) r diff
      = (do if ← ConLeche.Level.leqCore fuel a r diff then ConLeche.Level.leqCore fuel b r diff else pure false) := by
  rw [ConLeche.Level.rest]; simp_all
theorem rest_zero_max {fuel x y diff} :
    ConLeche.Level.rest fuel .zero (.max x y) diff
      = (do if ← ConLeche.Level.leqCore fuel .zero x diff then pure true else ConLeche.Level.leqCore fuel .zero y diff) := by
  rw [ConLeche.Level.rest]
theorem rest_param_max {fuel p x y diff} :
    ConLeche.Level.rest fuel (.param p) (.max x y) diff
      = (do if ← ConLeche.Level.leqCore fuel (.param p) x diff then pure true else ConLeche.Level.leqCore fuel (.param p) y diff) := by
  rw [ConLeche.Level.rest]
theorem rest_param_param {fuel a x diff} :
    ConLeche.Level.rest fuel (.param a) (.param x) diff = some (decide (a = x) && decide (diff ≥ 0)) := by
  rw [ConLeche.Level.rest]
theorem rest_param_zero {fuel a diff} : ConLeche.Level.rest fuel (.param a) .zero diff = some false := by
  rw [ConLeche.Level.rest]
theorem rest_zero_param {fuel p diff} :
    ConLeche.Level.rest fuel .zero (.param p) diff = some (decide (diff ≥ 0)) := by
  rw [ConLeche.Level.rest]
theorem rest_imax_imax {fuel a b x y diff} :
    ConLeche.Level.rest fuel (.imax a b) (.imax x y) diff
      = if a = x && b = y && diff ≥ 0 then some true
        else ConLeche.Level.imaxRules fuel (.imax a b) (.imax x y) diff := by
  rw [ConLeche.Level.rest]
theorem rest_zero_zero {fuel diff} :
    ConLeche.Level.rest fuel .zero .zero diff = ConLeche.Level.imaxRules fuel .zero .zero diff := by
  rw [ConLeche.Level.rest] <;> simp_all
theorem rest_zero_imax {fuel x y diff} :
    ConLeche.Level.rest fuel .zero (.imax x y) diff = ConLeche.Level.imaxRules fuel .zero (.imax x y) diff := by
  rw [ConLeche.Level.rest] <;> simp_all
theorem rest_imax_r {fuel a b r diff} (h2 : ∀ s, r ≠ .succ s) (h3 : ∀ x y, r ≠ .imax x y) :
    ConLeche.Level.rest fuel (.imax a b) r diff = ConLeche.Level.imaxRules fuel (.imax a b) r diff := by
  rw [ConLeche.Level.rest] <;> simp_all
theorem rest_param_imax {fuel p x y diff} :
    ConLeche.Level.rest fuel (.param p) (.imax x y) diff = ConLeche.Level.imaxRules fuel (.param p) (.imax x y) diff := by
  rw [ConLeche.Level.rest] <;> simp_all

theorem rest_refines_aux {fuel : Std.U64} (hQ : LeqCoreSpec fuel)
    {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {diff : Std.I64} {o : Option Bool} :
    level.rest fuel l r diff = ok o →
      ConLeche.Level.rest fuel.val (absLevel l) (absLevel r) diff.val = o := by
  intro h
  rw [level.rest.eq_def] at h
  obtain ⟨⟨hhl, kl⟩⟩ := l
  obtain ⟨⟨hhr, kr⟩⟩ := r
  cases kl with
  | Zero =>
    cases kr with
    | Zero =>
      simp at h
      have hres := imax_rules_refines hQ hl hr h
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_zero_zero]
      exact hres
    | Succ t =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ hl (LevelWF.succ_inv hr) d' o hlast
      rw [i64_add_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_r_succ (by simp)]
      simpa using hres
    | Max x y =>
      simp at h
      obtain ⟨o1, ho1, h⟩ := h
      obtain ⟨hx, hy⟩ := LevelWF.max_inv hr
      have e1 := hQ _ _ hl hx diff o1 ho1
      simp only [absLevel_mk, absLevelKind] at e1 ⊢
      rw [rest_zero_max, e1]
      cases o1 with
      | none => simpa using h
      | some b1 =>
        cases b1
        · have hres := hQ _ _ hl hy diff o h
          simp only [absLevel_mk, absLevelKind] at hres
          simpa using hres
        · simpa using h
    | Imax x y =>
      simp at h
      have hres := imax_rules_refines hQ hl hr h
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_zero_imax]
      exact hres
    | Param q =>
      simp at h
      simp only [absLevel_mk, absLevelKind]
      rw [rest_zero_param]
      simp [← h]
  | Succ s =>
    cases kr with
    | Zero =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ (LevelWF.succ_inv hl) hr d' o hlast
      rw [i64_sub_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_succ]
      simpa using hres
    | Succ t =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ (LevelWF.succ_inv hl) hr d' o hlast
      rw [i64_sub_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_succ]
      simpa using hres
    | Max x y =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ (LevelWF.succ_inv hl) hr d' o hlast
      rw [i64_sub_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_succ]
      simpa using hres
    | Imax x y =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ (LevelWF.succ_inv hl) hr d' o hlast
      rw [i64_sub_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_succ]
      simpa using hres
    | Param q =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ (LevelWF.succ_inv hl) hr d' o hlast
      rw [i64_sub_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_succ]
      simpa using hres
  | Max a b =>
    cases kr with
    | Zero =>
      simp at h
      obtain ⟨o1, ho1, h⟩ := h
      obtain ⟨ha, hb⟩ := LevelWF.max_inv hl
      have e1 := hQ _ _ ha hr diff o1 ho1
      simp only [absLevel_mk, absLevelKind] at e1 ⊢
      rw [rest_max (by simp), e1]
      cases o1 with
      | none => simpa using h
      | some b1 =>
        cases b1
        · simpa using h
        · have hres := hQ _ _ hb hr diff o h
          simp only [absLevel_mk, absLevelKind] at hres
          simpa using hres
    | Succ t =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ hl (LevelWF.succ_inv hr) d' o hlast
      rw [i64_add_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_r_succ (by simp)]
      simpa using hres
    | Max x y =>
      simp at h
      obtain ⟨o1, ho1, h⟩ := h
      obtain ⟨ha, hb⟩ := LevelWF.max_inv hl
      have e1 := hQ _ _ ha hr diff o1 ho1
      simp only [absLevel_mk, absLevelKind] at e1 ⊢
      rw [rest_max (by simp), e1]
      cases o1 with
      | none => simpa using h
      | some b1 =>
        cases b1
        · simpa using h
        · have hres := hQ _ _ hb hr diff o h
          simp only [absLevel_mk, absLevelKind] at hres
          simpa using hres
    | Imax x y =>
      simp at h
      obtain ⟨o1, ho1, h⟩ := h
      obtain ⟨ha, hb⟩ := LevelWF.max_inv hl
      have e1 := hQ _ _ ha hr diff o1 ho1
      simp only [absLevel_mk, absLevelKind] at e1 ⊢
      rw [rest_max (by simp), e1]
      cases o1 with
      | none => simpa using h
      | some b1 =>
        cases b1
        · simpa using h
        · have hres := hQ _ _ hb hr diff o h
          simp only [absLevel_mk, absLevelKind] at hres
          simpa using hres
    | Param q =>
      simp at h
      obtain ⟨o1, ho1, h⟩ := h
      obtain ⟨ha, hb⟩ := LevelWF.max_inv hl
      have e1 := hQ _ _ ha hr diff o1 ho1
      simp only [absLevel_mk, absLevelKind] at e1 ⊢
      rw [rest_max (by simp), e1]
      cases o1 with
      | none => simpa using h
      | some b1 =>
        cases b1
        · simpa using h
        · have hres := hQ _ _ hb hr diff o h
          simp only [absLevel_mk, absLevelKind] at hres
          simpa using hres
  | Imax a b =>
    cases kr with
    | Zero =>
      simp at h
      have hres := imax_rules_refines hQ hl hr h
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_imax_r (by simp) (by simp)]
      exact hres
    | Succ t =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ hl (LevelWF.succ_inv hr) d' o hlast
      rw [i64_add_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_r_succ (by simp)]
      simpa using hres
    | Max x y =>
      simp at h
      have hres := imax_rules_refines hQ hl hr h
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_imax_r (by simp) (by simp)]
      exact hres
    | Imax x y =>
      simp at h
      simp only [absLevel_mk, absLevelKind]
      rw [rest_imax_imax]
      obtain ⟨ha, hb⟩ := LevelWF.imax_inv hl
      obtain ⟨hx, hy⟩ := LevelWF.imax_inv hr
      rcases h with ⟨h1, h2⟩ | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
      · have e := level_beq_exact' ha hx h1
        replace e : ¬ (absLevel a = absLevel x) := by simpa using e.symm
        rw [if_neg (by simp [e])]
        have hres := imax_rules_refines hQ hl hr h2
        simpa using hres
      · have e := level_beq_exact' hb hy h2
        replace e : ¬ (absLevel b = absLevel y) := by simpa using e.symm
        rw [if_neg (by simp [e])]
        have hres := imax_rules_refines hQ hl hr h3
        simpa using hres
      · have e1 := level_beq_exact' ha hx h1
        have e2 := level_beq_exact' hb hy h2
        replace e1 : absLevel a = absLevel x := by simpa using e1.symm
        replace e2 : absLevel b = absLevel y := by simpa using e2.symm
        split at h3
        · rename_i hd
          rw [if_pos (by simp [e1, e2]; scalar_tac)]
          simpa using h3
        · rename_i hd
          rw [if_neg (by simp [e1, e2]; scalar_tac)]
          have hres := imax_rules_refines hQ hl hr h3
          simpa using hres
    | Param q =>
      simp at h
      have hres := imax_rules_refines hQ hl hr h
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_imax_r (by simp) (by simp)]
      exact hres
  | Param p =>
    cases kr with
    | Zero =>
      simp at h
      simp only [absLevel_mk, absLevelKind]
      rw [rest_param_zero]
      simp [← h]
    | Succ t =>
      simp at h
      obtain ⟨d', hd', hlast⟩ := h
      have hres := hQ _ _ hl (LevelWF.succ_inv hr) d' o hlast
      rw [i64_add_val hd'] at hres
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_r_succ (by simp)]
      simpa using hres
    | Max x y =>
      simp at h
      obtain ⟨o1, ho1, h⟩ := h
      obtain ⟨hx, hy⟩ := LevelWF.max_inv hr
      have e1 := hQ _ _ hl hx diff o1 ho1
      simp only [absLevel_mk, absLevelKind] at e1 ⊢
      rw [rest_param_max, e1]
      cases o1 with
      | none => simpa using h
      | some b1 =>
        cases b1
        · have hres := hQ _ _ hl hy diff o h
          simp only [absLevel_mk, absLevelKind] at hres
          simpa using hres
        · simpa using h
    | Imax x y =>
      simp at h
      have hres := imax_rules_refines hQ hl hr h
      simp only [absLevel_mk, absLevelKind] at hres ⊢
      rw [rest_param_imax]
      exact hres
    | Param q =>
      simp at h
      simp only [absLevel_mk, absLevelKind]
      rw [rest_param_param]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hce := Name.name_beq_exact' (LevelWF.param_inv hl) (LevelWF.param_inv hr) h1
        replace hce : ¬ (absName p = absName q) := by simpa using hce.symm
        simp [hce, ← h2]
      · have hce := Name.name_beq_exact' (LevelWF.param_inv hl) (LevelWF.param_inv hr) h1
        replace hce : absName p = absName q := by simpa using hce.symm
        simp [hce, ← h2]

theorem u64_sub_val {x y z : Std.U64} (h : x - y = ok z) : z.val = x.val - y.val := by
  have he := Std.UScalar.sub_equiv x y
  rw [h] at he
  simp only [Result.match.ok] at he
  omega

theorem leqCore_zero (l r : ConLeche.Level) (diff : Int) :
    ConLeche.Level.leqCore 0 l r diff = none := by rw [ConLeche.Level.leqCore]

theorem leqCore_succ (n : Nat) (l r : ConLeche.Level) (diff : Int) :
    ConLeche.Level.leqCore (n + 1) l r diff =
      (if l = .zero ∧ diff ≥ 0 then some true
       else if r = .zero ∧ diff < 0 then some false
       else ConLeche.Level.rest n l r diff) := by rw [ConLeche.Level.leqCore]

theorem leq_core_refines_aux (N : Nat) : ∀ (fuel : Std.U64), fuel.val = N → LeqCoreSpec fuel := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro fuel hfN l r hl hr diff o h
    rw [level.leq_core.eq_def] at h
    split at h
    · rename_i hf0
      simp at h
      have hz : fuel.val = 0 := by simp [hf0]
      rw [hz, leqCore_zero]
      exact h
    · rename_i hf0
      obtain ⟨M, hM⟩ : ∃ M, fuel.val = M + 1 := ⟨fuel.val - 1, by scalar_tac⟩
      obtain ⟨f', hf', hf'v⟩ : ∃ f' : Std.U64, fuel - 1#u64 = ok f' ∧ f'.val = M := by
        obtain ⟨w, hw, _⟩ :=
          WP.spec_imp_exists (Std.U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
        exact ⟨w, hw, by have := u64_sub_val hw; scalar_tac⟩
      have hQ' : LeqCoreSpec f' := ih M (by scalar_tac) f' hf'v
      rw [hM, leqCore_succ]
      simp only [bind_eq_ok_iff, hf'] at h
      obtain ⟨bz, hbz, h⟩ := h
      have ez := is_zero_kind_refines l bz hbz
      cases bz
      · replace ez : ¬ (absLevel l = ConLeche.Level.zero) := by simpa using ez.symm
        rw [if_neg (by simp [ez])]
        simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
        obtain ⟨bz2, hbz2, h⟩ := h
        have ez2 := is_zero_kind_refines r bz2 hbz2
        cases bz2
        · replace ez2 : ¬ (absLevel r = ConLeche.Level.zero) := by simpa using ez2.symm
          rw [if_neg (by simp [ez2])]
          simp only [Bool.false_eq_true, if_false, bind_tc_ok] at h
          have hres := rest_refines_aux hQ' hl hr h
          rw [hf'v] at hres; exact hres
        · replace ez2 : absLevel r = ConLeche.Level.zero := by simpa using ez2.symm
          simp only [if_true] at h
          split at h
          · rename_i hd
            rw [if_pos ⟨ez2, by scalar_tac⟩]
            simpa using h
          · rename_i hd
            rw [if_neg (by simp [ez2]; scalar_tac)]
            simp only [bind_tc_ok] at h
            have hres := rest_refines_aux hQ' hl hr h
            rw [hf'v] at hres; exact hres
      · replace ez : absLevel l = ConLeche.Level.zero := by simpa using ez.symm
        simp only [if_true] at h
        split at h
        · rename_i hd
          rw [if_pos ⟨ez, by scalar_tac⟩]
          simpa using h
        · rename_i hd
          rw [if_neg (by simp [ez]; scalar_tac)]
          simp only [bind_eq_ok_iff] at h
          obtain ⟨bz2, hbz2, h⟩ := h
          have ez2 := is_zero_kind_refines r bz2 hbz2
          cases bz2
          · replace ez2 : ¬ (absLevel r = ConLeche.Level.zero) := by simpa using ez2.symm
            rw [if_neg (by simp [ez2])]
            simp only [Bool.false_eq_true, if_false, bind_tc_ok] at h
            have hres := rest_refines_aux hQ' hl hr h
            rw [hf'v] at hres; exact hres
          · replace ez2 : absLevel r = ConLeche.Level.zero := by simpa using ez2.symm
            simp only [if_true] at h
            split at h
            · rename_i hd2
              rw [if_pos ⟨ez2, by scalar_tac⟩]
              simpa using h
            · rename_i hd2
              rw [if_neg (by simp [ez2]; scalar_tac)]
              simp only [bind_tc_ok] at h
              have hres := rest_refines_aux hQ' hl hr h
              rw [hf'v] at hres; exact hres

theorem leq_refines' {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {o : Option Bool} :
    level.leq l r = ok o → ConLeche.Level.leq (absLevel l) (absLevel r) = o := by
  intro h
  rw [level.leq] at h
  simp only [level.default_fuel, bind_eq_ok_iff] at h
  obtain ⟨fl, hfl, l1, hl1, l2, hl2, hlast⟩ := h
  simp only [Result.ok.injEq] at hfl
  subst hfl
  obtain ⟨e1, e1w⟩ := simplify_refines' l hl l1 hl1
  obtain ⟨e2, e2w⟩ := simplify_refines' r hr l2 hl2
  have hQ := leq_core_refines_aux 10000 10000#u64 (by simp)
  have hres := hQ l1 l2 e1w e2w 0#i64 o hlast
  rw [ConLeche.Level.leq, ConLeche.Level.defaultFuel]
  simpa [e1, e2] using hres

theorem is_equiv_refines' {l r : level.Level} (hl : LevelWF l) (hr : LevelWF r) {o : Option Bool} :
    level.is_equiv l r = ok o → ConLeche.Level.isEquiv (absLevel l) (absLevel r) = o := by
  intro h
  rw [level.is_equiv] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  have eb := level_beq_exact' hl hr hb
  rw [ConLeche.Level.isEquiv]
  cases b
  · replace eb : ¬ (absLevel l = absLevel r) := by simpa using eb.symm
    rw [if_neg (by simpa using eb)]
    simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
    obtain ⟨l1, hl1, l2, hl2, b1, hb1, h⟩ := h
    obtain ⟨e1, e1w⟩ := simplify_refines' l hl l1 hl1
    obtain ⟨e2, e2w⟩ := simplify_refines' r hr l2 hl2
    have eb1 := level_beq_exact' e1w e2w hb1
    cases b1
    · replace eb1 : ¬ (absLevel l1 = absLevel l2) := by simpa using eb1.symm
      rw [if_neg (by rw [← e1, ← e2]; exact eb1)]
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
      obtain ⟨o1, ho1, h⟩ := h
      have g1 := leq_refines' hl hr ho1
      rw [g1]
      cases o1 with
      | none => simpa using h
      | some b2 =>
        cases b2
        · simpa using h
        · have g2 := leq_refines' hr hl h
          simpa using g2
    · replace eb1 : absLevel l1 = absLevel l2 := by simpa using eb1.symm
      rw [if_pos (by rw [← e1, ← e2]; exact eb1)]
      simpa using h
  · replace eb : absLevel l = absLevel r := by simpa using eb.symm
    rw [if_pos (by simpa using eb)]
    simp only [if_true] at h
    simpa using h

/-! ## `levelsHaveParam` (task #20)

Left unproved at tasks #5 and #17 because nothing then consumed it;
`kernel::expr`'s `mk_const` does -- the `.const` node's level-param bit *is*
`levelsHaveParam us` (`Expr.lean:369`, `hasLP_const`).  The shape is task #5's
index-loop one: the conclusion is stated on `List.drop i`, so that `i = 0`
collapses to the whole list. -/

theorem levels_have_param_from_refines {us : alloc.vec.Vec level.Level} :
    ∀ k : Nat, ∀ (i : Std.Usize) (b : Bool), us.val.length - i.val ≤ k →
      level.levels_have_param_from us i = ok b →
      b = ConLeche.levelsHaveParam ((us.val.drop i.val).map absLevel) := by
  intro k
  induction k with
  | zero =>
    intro i b hk h
    rw [level.levels_have_param_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len us by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
    rfl
  | succ k ih =>
    intro i b hk h
    rw [level.levels_have_param_from.eq_def] at h; simp only [] at h
    by_cases hi : i.val ≥ us.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len us by scalar_tac), Result.ok.injEq] at h
      rw [← h, List.drop_eq_nil_of_le (by scalar_tac)]
      rfl
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len us by scalar_tac)] at h
      have hlt : i.val < us.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := us.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec us i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨b0, hb0, h⟩ := h
      have hb0' := level_has_param_refines' _ _ hb0
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ConLeche.levelsHaveParam, ← hb0']
      cases hc : b0
      · simp only [hc, Bool.false_eq_true, if_false, bind_tc_ok] at h
        simp only [Bool.false_or]
        have hrec := ih w b (by scalar_tac) h
        rw [hwv] at hrec
        exact hrec
      · simp only [hc, if_true, Result.ok.injEq] at h
        simp only [Bool.true_or]
        exact h.symm

/-- `level::levels_have_param` refines `levelsHaveParam`. -/
theorem levels_have_param_refines {us : alloc.vec.Vec level.Level} {b : Bool}
    (h : level.levels_have_param us = ok b) :
    b = ConLeche.levelsHaveParam (absLevels us) := by
  rw [level.levels_have_param] at h
  have := levels_have_param_from_refines us.val.length 0#usize b (by scalar_tac) h
  simpa [absLevels] using this

/-! ## The task-#5 statements, under the `ConRon/Refine/README.md` names

`ConRon.Generated.level.<fn>` is refined by `ConRon.Refine.Level.<fn>_refines`;
`<fn>_wf` is the well-formedness half, which by the §3.5 convention is
literally a `LevelWF` constructor.  Everything below is a one-liner; the work
is in the sections above. -/

theorem zero_wf {u : level.Level} : level.zero = ok u → LevelWF u := LevelWF.zero

theorem succ_wf {u v : level.Level} (h : LevelWF u) :
    level.succ u = ok v → LevelWF v := LevelWF.succ h

theorem max_wf {u v w : level.Level} (hu : LevelWF u) (hv : LevelWF v) :
    level.max u v = ok w → LevelWF w := LevelWF.max hu hv

theorem imax_wf {u v w : level.Level} (hu : LevelWF u) (hv : LevelWF v) :
    level.imax u v = ok w → LevelWF w := LevelWF.imax hu hv

theorem param_wf {n : name.Name} {u : level.Level} (hn : NameWF n) :
    level.param n = ok u → LevelWF u := LevelWF.param hn

theorem zero_refines {u : level.Level} : level.zero = ok u → absLevel u = .zero := by
  intro h; rw [level_zero_inv h]; simp

theorem succ_refines {u v : level.Level} :
    level.succ u = ok v → absLevel v = .succ (absLevel u) := by
  intro h; obtain ⟨_, rfl⟩ := level_succ_inv h; simp

theorem max_refines {u v w : level.Level} :
    level.max u v = ok w → absLevel w = .max (absLevel u) (absLevel v) := by
  intro h; obtain ⟨_, rfl⟩ := level_max_inv h; simp

theorem imax_refines {u v w : level.Level} :
    level.imax u v = ok w → absLevel w = .imax (absLevel u) (absLevel v) := by
  intro h; obtain ⟨_, rfl⟩ := level_imax_inv h; simp

theorem param_refines {n : name.Name} {u : level.Level} :
    level.param n = ok u → absLevel u = .param (absName n) := by
  intro h; obtain ⟨_, rfl⟩ := level_param_inv h; simp

theorem name_beq_exact {a b : name.Name} {c : Bool} (ha : NameWF a) (hb : NameWF b) :
    name.beq a b = ok c → c = decide (absName a = absName b) := Name.name_beq_exact' ha hb

theorem beq_refines {a b : level.Level} {c : Bool} (ha : LevelWF a) (hb : LevelWF b) :
    level.beq a b = ok c → c = decide (absLevel a = absLevel b) := level_beq_exact' ha hb

theorem level_has_param_refines {u : level.Level} {b : Bool} :
    level.level_has_param u = ok b → b = ConLeche.levelHasParam (absLevel u) :=
  level_has_param_refines' u b

/-- `hks` is an addition to Fable's statement: the exactness of the `name.beq`
inside `subst_go` needs the keys well-formed too (task-#5 report). -/
theorem subst_refines {u u' : level.Level} {ks : alloc.vec.Vec name.Name}
    {vs : alloc.vec.Vec level.Level} (hu : LevelWF u)
    (hks : ∀ k ∈ ks.val, NameWF k) (hvs : ∀ v ∈ vs.val, LevelWF v) :
    level.subst ks vs u = ok u' →
      absLevel u' =
        ConLeche.Level.subst (ks.val.map absName) (vs.val.map absLevel) (absLevel u)
      ∧ LevelWF u' :=
  subst_refines' u hu ks vs hks hvs u'

theorem is_never_zero_refines {u : level.Level} {b : Bool} :
    level.is_never_zero u = ok b → b = ConLeche.Level.isNeverZero (absLevel u) :=
  is_never_zero_refines' u b

theorem simplify_refines {u u' : level.Level} (hu : LevelWF u) :
    level.simplify u = ok u' →
      absLevel u' = ConLeche.Level.simplify (absLevel u) ∧ LevelWF u' :=
  simplify_refines' u hu u'

theorem leq_core_refines {fuel : Std.U64} {l r : level.Level} {diff : Std.I64}
    {o : Option Bool} (hl : LevelWF l) (hr : LevelWF r) :
    level.leq_core fuel l r diff = ok o →
      ConLeche.Level.leqCore fuel.val (absLevel l) (absLevel r) diff.val = o :=
  leq_core_refines_aux fuel.val fuel rfl l r hl hr diff o

theorem rest_refines {fuel : Std.U64} {l r : level.Level} {diff : Std.I64}
    {o : Option Bool} (hl : LevelWF l) (hr : LevelWF r) :
    level.rest fuel l r diff = ok o →
      ConLeche.Level.rest fuel.val (absLevel l) (absLevel r) diff.val = o :=
  rest_refines_aux (leq_core_refines_aux fuel.val fuel rfl) hl hr

theorem by_cases_refines {fuel : Std.U64} {p : name.Name} {l r : level.Level}
    {diff : Std.I64} {o : Option Bool} (hl : LevelWF l) (hr : LevelWF r) (hp : NameWF p) :
    level.by_cases fuel p l r diff = ok o →
      ConLeche.Level.byCases fuel.val (absName p) (absLevel l) (absLevel r) diff.val = o :=
  by_cases_refines_aux (leq_core_refines_aux fuel.val fuel rfl) hp hl hr

theorem leq_refines {l r : level.Level} {o : Option Bool} (hl : LevelWF l) (hr : LevelWF r) :
    level.leq l r = ok o → ConLeche.Level.leq (absLevel l) (absLevel r) = o :=
  leq_refines' hl hr

theorem is_equiv_refines {l r : level.Level} {o : Option Bool}
    (hl : LevelWF l) (hr : LevelWF r) :
    level.is_equiv l r = ok o → ConLeche.Level.isEquiv (absLevel l) (absLevel r) = o :=
  is_equiv_refines' hl hr

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing from Aeneas's library, nothing from the `Arc` models, no `sorry`:
the three standard Lean axioms only. -/

/-- info: 'ConRon.Refine.Level.leq_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leq_refines

/-- info: 'ConRon.Refine.Level.simplify_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simplify_refines

/-- info: 'ConRon.Refine.Level.beq_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beq_refines

end ConRon.Refine.Level
