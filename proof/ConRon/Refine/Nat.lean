import ConRon.Generated

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine.Nat

def limbsToNat : List Std.U64 → Nat
  | [] => 0
  | x :: r => x.val + 2 ^ 64 * limbsToNat r

def toNat (a : ron.nat.Nat) : Nat := limbsToNat a.limbs.val

def LimbsWF (l : List Std.U64) : Prop := ∀ x, l.getLast? = some x → x.val ≠ 0

def NatWF (a : ron.nat.Nat) : Prop := LimbsWF a.limbs.val

@[local simp] theorem limbsToNat_nil : limbsToNat [] = 0 := rfl
@[local simp] theorem limbsToNat_cons (x : Std.U64) (r) :
    limbsToNat (x :: r) = x.val + 2 ^ 64 * limbsToNat r := rfl

theorem limbsToNat_append (l₁ l₂ : List Std.U64) :
    limbsToNat (l₁ ++ l₂) = limbsToNat l₁ + 2 ^ (64 * l₁.length) * limbsToNat l₂ := by
  induction l₁ with
  | nil => simp
  | cons x r ih =>
    simp [ih, List.length_cons, Nat.mul_add, Nat.pow_add]
    ring

example (x : Std.U64) : x.val < 2^64 := by scalar_tac

@[local simp] theorem bind_eq_ok_iff {α β : Type} {e : Result α} {f : α → Result β} {v : β} :
    ((do let x ← e; f x) = ok v) ↔ ∃ y, e = ok y ∧ f y = ok v := by
  constructor
  · cases e with
    | ret r => intro h; exact ⟨r, rfl, by simpa using h⟩
    | vis i k => intro h; simp at h
    | div => intro h; simp at h
  · rintro ⟨y, rfl, h⟩; simpa using h

@[local simp] theorem index_usize_eq_ok_iff {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize)
    (x : α) : alloc.vec.Vec.index_usize v i = ok x ↔ v.val[i.val]? = some x := by
  simp only [alloc.vec.Vec.index_usize]
  cases h : v.val[i.val]? <;> simp

/-- `Vec::push` succeeds exactly when the vector may grow, and then appends.
The capacity conjunct is noise for the refinement (which only ever reads the
lemma left-to-right), but keeping the `iff` lets `simp` unfold a whole function
body in one step. -/
@[local simp] theorem push_eq_ok_iff {α : Type} (v : alloc.vec.Vec α) (x : α)
    (w : alloc.vec.Vec α) : alloc.vec.Vec.push v x = ok w ↔
      (v.val.length + 1 ≤ Std.U32.max ∨ v.val.length + 1 ≤ Std.Usize.max) ∧
        w.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push
  simp only []
  split <;> rename_i hc <;> simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
  · simp only [Result.ok.injEq, hc, true_and]
    constructor
    · rintro rfl; simp
    · intro h; apply alloc.vec.Vec.ext; simpa using h.symm
  · constructor
    · intro h; simp at h
    · rintro ⟨h, -⟩; omega

/-! ## Forward readings of the machine-word operations

Every one of these says "the Rust call returned `ok z`, so `z` is *this*";
nothing is claimed about failure, which is exactly the direction §3.5 asks
for (an overflow makes the hypothesis false and the goal vacuous). -/

theorem uadd_val {ty} {x y z : Std.UScalar ty} (h : x + y = ok z) :
    z.val = x.val + y.val := by
  have he := Std.UScalar.add_equiv x y
  rw [h] at he; simp only [Result.match.ok] at he; exact he.2.1

theorem usub_val {ty} {x y z : Std.UScalar ty} (h : x - y = ok z) :
    y.val ≤ x.val ∧ z.val = x.val - y.val := by
  have he := Std.UScalar.sub_equiv x y
  rw [h] at he; simp only [Result.match.ok] at he; omega

theorem umul_val {ty} {x y z : Std.UScalar ty} (h : x * y = ok z) :
    x.val * y.val < 2 ^ ty.numBits ∧ z.val = x.val * y.val := by
  have he := Std.UScalar.mul_equiv x y
  rw [show x * y = Std.UScalar.mul x y from rfl] at h
  rw [h] at he; simp only [Result.match.ok] at he
  have hp : 0 < 2 ^ ty.numBits := Nat.two_pow_pos _
  have hb : Std.UScalar.max ty + 1 = 2 ^ ty.numBits := by
    simp only [Std.UScalar.max]; omega
  exact ⟨by omega, he.2.1⟩

theorem udiv_val {ty} {x y z : Std.UScalar ty} (h : x / y = ok z) :
    z.val = x.val / y.val := by
  simp only [HDiv.hDiv, Std.UScalar.div] at h
  split at h
  · simp only [Result.ok.injEq] at h; subst h
    show (x.bv / y.bv).toNat = _
    simp only [Std.UScalar.val, BitVec.toNat_udiv]
  · simp at h

theorem urem_val {ty} {x y z : Std.UScalar ty} (h : x % y = ok z) :
    z.val = x.val % y.val := by
  simp only [HMod.hMod, Std.UScalar.rem] at h
  split at h
  · simp only [Result.ok.injEq] at h; subst h
    show (x.bv % y.bv).toNat = _
    simp only [Std.UScalar.val, BitVec.toNat_umod]
  · simp at h

theorem ushiftLeft_val {ty tys} {x z : Std.UScalar ty} {s : Std.UScalar tys}
    (h : x <<< s = ok z) : s.val < ty.numBits ∧ z.val = x.val * 2 ^ s.val % 2 ^ ty.numBits := by
  simp only [HShiftLeft.hShiftLeft, Std.UScalar.shiftLeft_UScalar, Std.UScalar.shiftLeft] at h
  split at h <;> rename_i hs
  · refine ⟨hs, ?_⟩
    simp only [Result.ok.injEq] at h; subst h
    simp only [Std.UScalar.val, BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · simp at h

theorem ushiftLeftI_val {ty tys} {x z : Std.UScalar ty} {s : Std.IScalar tys}
    (h : x <<< s = ok z) :
    s.toNat < ty.numBits ∧ z.val = x.val * 2 ^ s.toNat % 2 ^ ty.numBits := by
  simp only [HShiftLeft.hShiftLeft, Std.UScalar.shiftLeft_IScalar] at h
  split at h
  · simp only [Std.UScalar.shiftLeft] at h
    split at h <;> rename_i hs
    · refine ⟨hs, ?_⟩
      simp only [Result.ok.injEq] at h; subst h
      simp only [Std.UScalar.val, BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    · simp at h
  · simp at h

theorem ushiftRight_val {ty tys} {x z : Std.UScalar ty} {s : Std.UScalar tys}
    (h : x >>> s = ok z) : s.val < ty.numBits ∧ z.val = x.val / 2 ^ s.val := by
  simp only [HShiftRight.hShiftRight, Std.UScalar.shiftRight_UScalar, Std.UScalar.shiftRight] at h
  split at h <;> rename_i hs
  · refine ⟨hs, ?_⟩
    simp only [Result.ok.injEq] at h; subst h
    simp only [Std.UScalar.val, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
  · simp at h

theorem ushiftRightI_val {ty tys} {x z : Std.UScalar ty} {s : Std.IScalar tys}
    (h : x >>> s = ok z) : s.toNat < ty.numBits ∧ z.val = x.val / 2 ^ s.toNat := by
  simp only [HShiftRight.hShiftRight, Std.UScalar.shiftRight_IScalar] at h
  split at h
  · simp only [Std.UScalar.shiftRight] at h
    split at h <;> rename_i hs
    · refine ⟨hs, ?_⟩
      simp only [Result.ok.injEq] at h; subst h
      simp only [Std.UScalar.val, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
    · simp at h
  · simp at h

/-! ## `limb` and the partial sums `seg` -/

/-- Limb `i` of a limb list, `0` past the end (`ron::nat::limb`). -/
def limbAt (v : List Std.U64) (i : Nat) : Std.U64 := v.getD i 0#u64

/-- `∑_{k = i}^{n-1} v[k] · 2^(64 (k - i))` — the value of the limb window
`[i, n)`, which is what every `*_from` loop of `nat.rs` consumes. -/
def seg (v : List Std.U64) (i n : Nat) : Nat := limbsToNat ((v.drop i).take (n - i))

theorem seg_of_le {v : List Std.U64} {i n : Nat} (h : n ≤ i) : seg v i n = 0 := by
  simp [seg, Nat.sub_eq_zero_of_le h]

theorem seg_succ (v : List Std.U64) {i n : Nat} (h : i < n) :
    seg v i n = (limbAt v i).val + 2 ^ 64 * seg v (i + 1) n := by
  unfold seg limbAt
  rw [show n - i = (n - (i + 1)) + 1 by omega]
  rcases Nat.lt_or_ge i v.length with hi | hi
  · rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.getD_eq_getElem _ _ hi,
      limbsToNat_cons]
  · rw [List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega : v.length ≤ i + 1),
      List.getD_eq_default _ _ hi]
    simp

theorem seg_full (v : List Std.U64) {n : Nat} (h : v.length ≤ n) :
    seg v 0 n = limbsToNat v := by
  simp [seg, List.take_of_length_le (by simpa using h)]

theorem limb_refines {v : alloc.vec.Vec Std.U64} {i : Std.Usize} {x : Std.U64}
    (h : ron.nat.limb v i = ok x) : x = limbAt v.val i.val := by
  rw [ron.nat.limb] at h
  simp only [limbAt] at *
  split at h <;> rename_i hi
  · have hlt : i.val < v.val.length := by scalar_tac
    simp only [alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff,
      List.getElem?_eq_getElem hlt, Option.some.injEq] at h
    rw [List.getD_eq_getElem _ _ hlt, h]
  · have hge : v.val.length ≤ i.val := by scalar_tac
    simp only [Result.ok.injEq] at h
    rw [List.getD_eq_default _ _ hge, h]

/-! ## `copy_from`: the plain limb copy -/

theorem copy_from_val (v : alloc.vec.Vec Std.U64) (e : Std.Usize) (he : e.val ≤ v.val.length) :
    ∀ (d : Nat) (i : Std.Usize) (out w : alloc.vec.Vec Std.U64), e.val - i.val ≤ d →
      ron.nat.copy_from v i e out = ok w →
      w.val = out.val ++ (v.val.drop i.val).take (e.val - i.val) := by
  intro d
  induction d with
  | zero =>
    intro i out w hd h
    rw [ron.nat.copy_from] at h
    have hie : e.val ≤ i.val := by omega
    rw [if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h; simp [Nat.sub_eq_zero_of_le hie]
  | succ d ih =>
    intro i out w hd h
    rw [ron.nat.copy_from] at h
    split at h <;> rename_i hie
    · simp only [Result.ok.injEq] at h
      have : e.val ≤ i.val := by scalar_tac
      subst h; simp [Nat.sub_eq_zero_of_le this]
    · have hlt : i.val < e.val := by scalar_tac
      simp only [] at h
      split at h <;> rename_i hiv
      · have : v.val.length ≤ i.val := by scalar_tac
        omega
      · have hiv' : i.val < v.val.length := by scalar_tac
        simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, index_usize_eq_ok_iff,
          push_eq_ok_iff] at h
        obtain ⟨x, hx, out1, ⟨-, hout1⟩, i3, hi3, h⟩ := h
        have hx' : x = v.val[i.val] := by
          rw [List.getElem?_eq_getElem hiv'] at hx; exact (Option.some.injEq _ _ ▸ hx).symm
        have hi3' : i3.val = i.val + 1 := by
          have := uadd_val hi3; simpa using this
        rw [ih i3 out1 w (by omega) h, hout1, hi3', hx']
        rw [List.drop_eq_getElem_cons hiv', show e.val - i.val = (e.val - (i.val+1)) + 1 by omega,
          List.take_succ_cons]
        simp

theorem copy_from_refines {v : alloc.vec.Vec Std.U64} {i e : Std.Usize}
    {out w : alloc.vec.Vec Std.U64} (he : e.val ≤ v.val.length)
    (h : ron.nat.copy_from v i e out = ok w) :
    w.val = out.val ++ (v.val.drop i.val).take (e.val - i.val) :=
  copy_from_val v e he (e.val - i.val) i out w le_rfl h

/-! ## `sig_len` and `norm`: re-establishing the no-trailing-zero invariant -/

theorem limbsWF_nil : LimbsWF [] := by intro x hx; simp at hx

theorem limbsWF_take_succ {v : List Std.U64} {k : Nat} (hk : k < v.length)
    (h : (v[k]'hk).val ≠ 0) : LimbsWF (v.take (k + 1)) := by
  intro x hx
  rw [List.take_add_one, List.getElem?_eq_getElem hk] at hx
  simp only [Option.toList_some, List.getLast?_concat, Option.some.injEq] at hx
  exact hx ▸ h

theorem limbsToNat_take_succ_of_zero {v : List Std.U64} {k : Nat} (hk : k < v.length)
    (h : (v[k]'hk).val = 0) : limbsToNat (v.take (k + 1)) = limbsToNat (v.take k) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, limbsToNat_append]
  simp [h]

theorem sig_len_val (v : alloc.vec.Vec Std.U64) :
    ∀ (d : Nat) (k s : Std.Usize), k.val ≤ d → k.val ≤ v.val.length →
      ron.nat.sig_len v k = ok s →
      s.val ≤ k.val ∧ LimbsWF (v.val.take s.val) ∧
        limbsToNat (v.val.take s.val) = limbsToNat (v.val.take k.val) := by
  intro d
  induction d with
  | zero =>
    intro k s hd hk h
    rw [ron.nat.sig_len] at h
    rw [if_pos (by scalar_tac : k = 0#usize)] at h
    simp only [Result.ok.injEq] at h
    subst h
    have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
    have hk0 : k.val = 0 := by omega
    rw [h0, hk0]
    exact ⟨le_rfl, limbsWF_nil, rfl⟩
  | succ d ih =>
    intro k s hd hk h
    rw [ron.nat.sig_len] at h
    split at h <;> rename_i hk0
    · simp only [Result.ok.injEq] at h
      subst h
      have : k.val = 0 := by scalar_tac
      simp [this, limbsWF_nil]
    · have hk0' : 0 < k.val := by scalar_tac
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, index_usize_eq_ok_iff] at h
      obtain ⟨i, hi, x, hx, h⟩ := h
      have hi' : i.val = k.val - 1 := (usub_val hi).2.trans (by simp)
      have hiv : i.val < v.val.length := by omega
      have hx' : x = v.val[i.val] := by
        rw [List.getElem?_eq_getElem hiv] at hx; exact (Option.some.injEq _ _ ▸ hx).symm
      split at h <;> rename_i hxz
      · simp only [Result.ok.injEq] at h
        subst h
        refine ⟨le_rfl, ?_, rfl⟩
        rw [show k.val = i.val + 1 by omega]
        exact limbsWF_take_succ hiv (by rw [← hx']; scalar_tac)
      · have hxz' : (v.val[i.val]'hiv).val = 0 := by rw [← hx']; scalar_tac
        obtain ⟨h1, h2, h3⟩ := ih i s (by omega) (by omega) h
        refine ⟨by omega, h2, ?_⟩
        rw [h3, show k.val = i.val + 1 by omega, limbsToNat_take_succ_of_zero hiv hxz']

theorem norm_refines {limbs : alloc.vec.Vec Std.U64} {n : ron.nat.Nat}
    (h : ron.nat.norm limbs = ok n) : toNat n = limbsToNat limbs.val ∧ NatWF n := by
  rw [ron.nat.norm] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨h1, h2, h3⟩ :=
    sig_len_val limbs limbs.val.length (alloc.vec.Vec.len limbs) s le_rfl (by scalar_tac) hs
  have hlen : (alloc.vec.Vec.len limbs).val = limbs.val.length := by scalar_tac
  rw [hlen] at h1 h3
  rw [List.take_length] at h3
  split at h <;> rename_i hsn
  · simp only [Result.ok.injEq] at h
    subst h
    have hse : s.val = limbs.val.length := by rw [← hlen, hsn]
    rw [hse, List.take_length] at h2
    exact ⟨rfl, h2⟩
  · simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨w, hw, h⟩ := h
    subst h
    have hwv : w.val = limbs.val.take s.val := by
      have hcf := copy_from_refines (v := limbs) (i := 0#usize) (e := s)
        (out := alloc.vec.Vec.new Std.U64) (w := w) h1 hw
      have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
      rw [h0] at hcf
      simpa using hcf
    exact ⟨by simp only [toNat, hwv]; exact h3, by simp only [NatWF, hwv]; exact h2⟩

/-! ## Bounds, and injectivity of `toNat` under the invariant -/

theorem limbsToNat_lt (l : List Std.U64) : limbsToNat l < 2 ^ (64 * l.length) := by
  induction l with
  | nil => simp
  | cons x r ih =>
    have hx : x.val < 2 ^ 64 := by scalar_tac
    have : 64 * (x :: r).length = 64 * r.length + 64 := by simp [Nat.mul_add]
    rw [limbsToNat_cons, this, Nat.pow_add]
    have : limbsToNat r + 1 ≤ 2 ^ (64 * r.length) := ih
    calc x.val + 2 ^ 64 * limbsToNat r < 2 ^ 64 * (limbsToNat r + 1) := by omega
      _ ≤ 2 ^ 64 * 2 ^ (64 * r.length) := by exact Nat.mul_le_mul_left _ this
      _ = 2 ^ (64 * r.length) * 2 ^ 64 := by ring

theorem limbsWF_tail {x : Std.U64} {r : List Std.U64} (h : LimbsWF (x :: r)) : LimbsWF r := by
  intro y hy
  refine h y ?_
  cases r with
  | nil => simp at hy
  | cons z t => rw [List.getLast?_cons_cons]; exact hy

theorem limbsToNat_eq_zero {l : List Std.U64} (hw : LimbsWF l) (h : limbsToNat l = 0) :
    l = [] := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    rw [limbsToNat_cons] at h
    have hr : r = [] := ih (limbsWF_tail hw) (by omega)
    subst hr
    exact absurd (hw x (by simp)) (by omega)

theorem limbs_inj {l₁ l₂ : List Std.U64} (h₁ : LimbsWF l₁) (h₂ : LimbsWF l₂)
    (h : limbsToNat l₁ = limbsToNat l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact (limbsToNat_eq_zero h₂ (by simpa using h.symm)).symm
  | cons x r ih =>
    cases l₂ with
    | nil => exact absurd (limbsToNat_eq_zero h₁ (by simpa using h)) (by simp)
    | cons y t =>
      have hx : x.val < 2 ^ 64 := by scalar_tac
      have hy : y.val < 2 ^ 64 := by scalar_tac
      rw [limbsToNat_cons, limbsToNat_cons] at h
      have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
      rw [h64] at h hx hy
      have hxy : x.val = y.val := by omega
      have hrt : limbsToNat r = limbsToNat t := by omega
      rw [ih (limbsWF_tail h₁) (limbsWF_tail h₂) hrt]
      congr 1
      exact Std.UScalar.eq_of_val_eq hxy

theorem toNat_inj {a b : ron.nat.Nat} (ha : NatWF a) (hb : NatWF b) (h : toNat a = toNat b) :
    a = b := by
  cases a; cases b
  simp only [ron.nat.Nat.mk.injEq]
  exact alloc.vec.Vec.ext _ _ (limbs_inj ha hb h)

/-- `LimbsWF` pins the top limb, so a nonempty normalised list is at least
`2^(64 (len - 1))` — the fact that makes `cmp`'s length test a numeric test. -/
theorem limbsToNat_ge {l : List Std.U64} (hw : LimbsWF l) (hne : l ≠ []) :
    2 ^ (64 * (l.length - 1)) ≤ limbsToNat l := by
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  rw [limbsToNat_append, List.length_dropLast]
  have hlast : (l.getLast hne).val ≠ 0 := hw _ (List.getLast?_eq_some_getLast hne)
  have : 1 ≤ (l.getLast hne).val := by omega
  calc 2 ^ (64 * (l.length - 1)) = 2 ^ (64 * (l.length - 1)) * 1 := by ring
    _ ≤ 2 ^ (64 * (l.length - 1)) * (l.getLast hne).val := Nat.mul_le_mul_left _ this
    _ ≤ _ := by simp

/-! ## Constructors and destructors -/

theorem zero_refines {n : ron.nat.Nat} (h : ron.nat.zero = ok n) : toNat n = 0 ∧ NatWF n := by
  rw [ron.nat.zero] at h
  simp only [Result.ok.injEq] at h
  subst h
  exact ⟨rfl, by simpa [NatWF] using limbsWF_nil⟩

theorem from_u64_refines {x : Std.U64} {n : ron.nat.Nat} (h : ron.nat.from_u64 x = ok n) :
    toNat n = x.val ∧ NatWF n := by
  rw [ron.nat.from_u64] at h
  split at h <;> rename_i hx
  · simp only [Result.ok.injEq] at h
    subst h
    have : x.val = 0 := by scalar_tac
    exact ⟨by simp [toNat, this], by simpa [NatWF] using limbsWF_nil⟩
  · simp only [bind_eq_ok_iff, push_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨v, ⟨-, hv⟩, h⟩ := h
    subst h
    have hxz : x.val ≠ 0 := by scalar_tac
    refine ⟨by simp [toNat, hv], ?_⟩
    intro y hy
    rw [hv] at hy
    have hxy : x = y := by simpa using hy
    exact hxy ▸ hxz

theorem one_refines {n : ron.nat.Nat} (h : ron.nat.one = ok n) : toNat n = 1 ∧ NatWF n := by
  rw [ron.nat.one] at h
  have := from_u64_refines h
  exact ⟨by rw [this.1]; scalar_tac, this.2⟩

theorem is_zero_refines {a : ron.nat.Nat} {b : Bool} (ha : NatWF a) (h : ron.nat.is_zero a = ok b) :
    b = decide (toNat a = 0) := by
  rw [ron.nat.is_zero] at h
  simp only [Result.ok.injEq] at h
  subst h
  by_cases hz : a.limbs.val = []
  · have : toNat a = 0 := by simp [toNat, hz]
    simp only [this, decide_true, decide_eq_true_eq]
    scalar_tac
  · have h1 : ¬ (alloc.vec.Vec.len a.limbs = 0#usize) := by
      intro hc
      exact hz (List.eq_nil_of_length_eq_zero (by scalar_tac))
    have h2 : toNat a ≠ 0 := fun hc => hz (limbsToNat_eq_zero ha hc)
    simp [h1, h2]

theorem clone_refines {a n : ron.nat.Nat} (h : ron.nat.clone a = ok n) :
    n.limbs.val = a.limbs.val ∧ toNat n = toNat a := by
  rw [ron.nat.clone] at h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨v, hv, h⟩ := h
  subst h
  have := copy_from_refines (v := a.limbs) (i := 0#usize)
    (e := alloc.vec.Vec.len a.limbs) (out := alloc.vec.Vec.new Std.U64) (w := v)
    (by scalar_tac) hv
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  have hl : (alloc.vec.Vec.len a.limbs).val = a.limbs.val.length := by scalar_tac
  rw [h0, hl] at this
  simp only [Nat.sub_zero, List.drop_zero, List.take_length] at this
  exact ⟨this, by simp [toNat, this]⟩

theorem to_u64_refines {a : ron.nat.Nat} {o : Option Std.U64} (ha : NatWF a)
    (h : ron.nat.to_u64 a = ok o) :
    (∃ x : Std.U64, o = some x ∧ x.val = toNat a) ∨ (o = none ∧ 2 ^ 64 ≤ toNat a) := by
  rw [ron.nat.to_u64] at h
  split at h <;> rename_i h0
  · simp only [Result.ok.injEq] at h
    have : a.limbs.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    refine Or.inl ⟨0#u64, h.symm, ?_⟩
    simp only [toNat, this, limbsToNat_nil]
    scalar_tac
  · simp only [] at h
    split at h <;> rename_i h1
    · have hlen : a.limbs.val.length = 1 := by scalar_tac
      obtain ⟨y, hy⟩ : ∃ y, a.limbs.val = [y] := by
        match hv : a.limbs.val with
        | [y] => exact ⟨y, rfl⟩
        | [] => simp [hv] at hlen
        | _ :: _ :: _ => simp [hv] at hlen
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, index_usize_eq_ok_iff,
        Result.ok.injEq] at h
      obtain ⟨x, hx, h⟩ := h
      refine Or.inl ⟨x, h.symm, ?_⟩
      have h0' : (0#usize : Std.Usize).val = 0 := by scalar_tac
      rw [h0', hy] at hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      simp [toNat, hy, ← hx]
    · simp only [Result.ok.injEq] at h
      refine Or.inr ⟨h.symm, ?_⟩
      have hlen : 2 ≤ a.limbs.val.length := by scalar_tac
      have := limbsToNat_ge ha (by intro hc; rw [hc] at hlen; simp at hlen)
      calc (2 : Nat) ^ 64 = 2 ^ (64 * 1) := by norm_num
        _ ≤ 2 ^ (64 * (a.limbs.val.length - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ toNat a := this

/-! ## Comparison: `cmp`, `beq`, `ble`, `blt` -/

theorem seg_zero_succ (v : List Std.U64) (i : Nat) :
    seg v 0 (i + 1) = seg v 0 i + 2 ^ (64 * i) * (limbAt v i).val := by
  simp only [seg, Nat.sub_zero, List.drop_zero, limbAt]
  rcases Nat.lt_or_ge i v.length with hi | hi
  · rw [List.take_add_one, List.getElem?_eq_getElem hi, limbsToNat_append,
      List.getD_eq_getElem _ _ hi]
    simp [List.length_take, Nat.min_eq_left (le_of_lt hi)]
  · rw [List.take_of_length_le hi, List.take_of_length_le (by omega),
      List.getD_eq_default _ _ hi]
    simp

theorem seg_zero_lt (v : List Std.U64) (n : Nat) : seg v 0 n < 2 ^ (64 * n) := by
  simp only [seg, Nat.sub_zero, List.drop_zero]
  refine lt_of_lt_of_le (limbsToNat_lt _) (Nat.pow_le_pow_right (by omega) ?_)
  have : (v.take n).length ≤ n := by simp
  omega

theorem cmp_from_val (a b : alloc.vec.Vec Std.U64) :
    ∀ (d : Nat) (k : Std.Usize) (c : ron.nat.Cmp), k.val ≤ d → ron.nat.cmp_from a b k = ok c →
      (c = .Lt ∧ seg a.val 0 k.val < seg b.val 0 k.val) ∨
      (c = .Eq ∧ seg a.val 0 k.val = seg b.val 0 k.val) ∨
      (c = .Gt ∧ seg b.val 0 k.val < seg a.val 0 k.val) := by
  intro d
  induction d with
  | zero =>
    intro k c hd h
    rw [ron.nat.cmp_from] at h
    rw [if_pos (by scalar_tac : k = 0#usize)] at h
    simp only [Result.ok.injEq] at h
    have hk : k.val = 0 := by omega
    exact Or.inr (Or.inl ⟨h.symm, by rw [hk]; rfl⟩)
  | succ d ih =>
    intro k c hd h
    rw [ron.nat.cmp_from] at h
    split at h <;> rename_i hk0
    · simp only [Result.ok.injEq] at h
      have hk : k.val = 0 := by scalar_tac
      exact Or.inr (Or.inl ⟨h.symm, by rw [hk]; rfl⟩)
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, x, hx, y, hy, h⟩ := h
      have hk0' : 0 < k.val := by scalar_tac
      have hi' : i.val = k.val - 1 := (usub_val hi).2.trans (by simp)
      have hks : k.val = i.val + 1 := by omega
      have hxa : x = limbAt a.val i.val := limb_refines hx
      have hyb : y = limbAt b.val i.val := limb_refines hy
      have hA := seg_zero_lt a.val i.val
      have hB := seg_zero_lt b.val i.val
      rw [hks, seg_zero_succ, seg_zero_succ, ← hxa, ← hyb]
      split at h <;> rename_i hxy
      · simp only [Result.ok.injEq] at h
        refine Or.inl ⟨h.symm, ?_⟩
        have hlt : x.val < y.val := (Std.UScalar.lt_equiv x y).mp hxy
        nlinarith [Nat.mul_le_mul_left (2 ^ (64 * i.val)) hlt]
      · split at h <;> rename_i hxy2
        · simp only [Result.ok.injEq] at h
          refine Or.inr (Or.inr ⟨h.symm, ?_⟩)
          have hlt : y.val < x.val := (Std.UScalar.lt_equiv y x).mp hxy2
          nlinarith [Nat.mul_le_mul_left (2 ^ (64 * i.val)) hlt]
        · have hxye : x.val = y.val := by
            have h1 : ¬ (x.val < y.val) := fun hc => hxy ((Std.UScalar.lt_equiv x y).mpr hc)
            have h2 : ¬ (y.val < x.val) := fun hc => hxy2 ((Std.UScalar.lt_equiv y x).mpr hc)
            omega
          rcases ih i c (by omega) h with ⟨hc, hs⟩ | ⟨hc, hs⟩ | ⟨hc, hs⟩
          · exact Or.inl ⟨hc, by rw [hxye]; omega⟩
          · exact Or.inr (Or.inl ⟨hc, by rw [hxye, hs]⟩)
          · exact Or.inr (Or.inr ⟨hc, by rw [hxye]; omega⟩)

theorem cmp_refines {a b : ron.nat.Nat} {c : ron.nat.Cmp} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.cmp a b = ok c) :
    (c = .Lt ∧ toNat a < toNat b) ∨ (c = .Eq ∧ toNat a = toNat b) ∨
    (c = .Gt ∧ toNat b < toNat a) := by
  -- a shorter normalised operand is numerically smaller
  have key : ∀ u v : ron.nat.Nat, NatWF v → u.limbs.val.length < v.limbs.val.length →
      toNat u < toNat v := by
    intro u v hv hlt
    have h1 : toNat u < 2 ^ (64 * u.limbs.val.length) := limbsToNat_lt _
    have h2 : 2 ^ (64 * (v.limbs.val.length - 1)) ≤ toNat v :=
      limbsToNat_ge hv (by intro hc; rw [hc] at hlt; simp at hlt)
    have h3 : (2 : Nat) ^ (64 * u.limbs.val.length) ≤ 2 ^ (64 * (v.limbs.val.length - 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rw [ron.nat.cmp] at h
  split at h <;> rename_i h1
  · simp only [Result.ok.injEq] at h
    exact Or.inl ⟨h.symm, key a b hb (by scalar_tac)⟩
  · split at h <;> rename_i h2
    · simp only [Result.ok.injEq] at h
      exact Or.inr (Or.inr ⟨h.symm, key b a ha (by scalar_tac)⟩)
    · have hlen : a.limbs.val.length = b.limbs.val.length := by scalar_tac
      have hla : (alloc.vec.Vec.len a.limbs).val = a.limbs.val.length := by scalar_tac
      have hsa : seg a.limbs.val 0 (alloc.vec.Vec.len a.limbs).val = toNat a := by
        rw [hla]; exact seg_full _ le_rfl
      have hsb : seg b.limbs.val 0 (alloc.vec.Vec.len a.limbs).val = toNat b := by
        rw [hla, hlen]; exact seg_full _ le_rfl
      rcases cmp_from_val a.limbs b.limbs (alloc.vec.Vec.len a.limbs).val
          (alloc.vec.Vec.len a.limbs) c le_rfl h with
        ⟨hc, hs⟩ | ⟨hc, hs⟩ | ⟨hc, hs⟩
      · exact Or.inl ⟨hc, by rwa [hsa, hsb] at hs⟩
      · exact Or.inr (Or.inl ⟨hc, by rwa [hsa, hsb] at hs⟩)
      · exact Or.inr (Or.inr ⟨hc, by rwa [hsa, hsb] at hs⟩)

theorem beq_refines {a b : ron.nat.Nat} {r : Bool} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.beq a b = ok r) : r = decide (toNat a = toNat b) := by
  rw [ron.nat.beq] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rcases cmp_refines ha hb hc with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩ <;>
    simp only [Result.ok.injEq] at h <;> rw [← h] <;> simp <;> omega

/-! ## Reflexivity (task #20)

`kernel::expr`'s `beq` keeps a pointer fast path at every level, and DESIGN.md
§3.2's transparency obligation for it is that the model's walk is *reflexive*.
`nat::beq` is one of its leaves (a `natVal` literal), hence this. -/

theorem limb_ok (v : alloc.vec.Vec Std.U64) (i : Std.Usize) :
    ∃ x, ron.nat.limb v i = ok x := by
  rw [ron.nat.limb]
  split
  · rename_i hi
    have hlt : i.val < v.val.length := by scalar_tac
    obtain ⟨y, hy, -⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hlt)
    exact ⟨y, by simpa using hy⟩
  · exact ⟨_, rfl⟩

theorem cmp_from_refl (v : alloc.vec.Vec Std.U64) :
    ∀ n : Nat, ∀ k : Std.Usize, k.val ≤ n → ron.nat.cmp_from v v k = ok .Eq := by
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [ron.nat.cmp_from.eq_def, if_pos (show k = 0#usize by scalar_tac)]
  | succ n ih =>
    intro k hk
    rw [ron.nat.cmp_from.eq_def]
    by_cases hz : k = 0#usize
    · rw [if_pos hz]
    · rw [if_neg hz]
      obtain ⟨w, hw, hwv⟩ :=
        WP.spec_imp_exists (Std.Usize.sub_spec (x := k) (y := 1#usize) (by scalar_tac))
      obtain ⟨x, hx⟩ := limb_ok v w
      simp only [hw, hx, bind_tc_ok]
      rw [if_neg (by simp), if_neg (by simp)]
      exact ih w (by scalar_tac)

theorem cmp_refl (a : ron.nat.Nat) : ron.nat.cmp a a = ok .Eq := by
  rw [ron.nat.cmp.eq_def]
  rw [if_neg (by simp), if_neg (by simp)]
  exact cmp_from_refl a.limbs (alloc.vec.Vec.len a.limbs).val (alloc.vec.Vec.len a.limbs) le_rfl

/-- `ron::nat::beq` is reflexive -- the pointer fast path of a `natVal`
literal's comparison is transparent (DESIGN.md §3.2). -/
theorem beq_refl (a : ron.nat.Nat) : ron.nat.beq a a = ok true := by
  rw [ron.nat.beq, cmp_refl]
  simp

theorem ble_refines {a b : ron.nat.Nat} {r : Bool} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.ble a b = ok r) : r = decide (toNat a ≤ toNat b) := by
  rw [ron.nat.ble] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rcases cmp_refines ha hb hc with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩ <;>
    simp only [Result.ok.injEq] at h <;> rw [← h] <;> simp <;> omega

theorem blt_refines {a b : ron.nat.Nat} {r : Bool} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.blt a b = ok r) : r = decide (toNat a < toNat b) := by
  rw [ron.nat.blt] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rcases cmp_refines ha hb hc with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩ <;>
    simp only [Result.ok.injEq] at h <;> rw [← h] <;> simp <;> omega

/-! ## Addition, subtraction, predecessor

`overflowing_add`/`overflowing_sub` return a *pair*, and Charon binds it with
`let (s, c) ← …`.  `simp only` cannot get inside the resulting `match`, so the
recipe for those loop bodies is: unfold the two `UScalar` definitions (which
makes the pair a literal constructor), then run a *full* `simp`, which
iota-reduces the match and pushes everything to the bit-vector level.  The two
word lemmas below then absorb all the bit-vector reasoning. -/

@[local simp] theorem lift_eq_ok_iff {α : Type} (x y : α) :
    (Std.lift x : Result α) = ok y ↔ x = y := by
  simp [Std.lift]

theorem pow_two_64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num

/-- The carry-out of one ripple-carry limb, in the shape the full `simp` of
`add_from`'s body leaves behind. -/
theorem add_carry_word {x y carry cc : Std.U64} (hc : carry.val ≤ 1)
    (hcc : (if x.bv.uaddOverflow y.bv = true then ok (1#u64)
            else if (x.bv + y.bv).uaddOverflow carry.bv = true then ok (1#u64)
            else ok (0#u64)) = (ok cc : Result Std.U64)) :
    cc.val ≤ 1 ∧
      (⟨x.bv + y.bv + carry.bv⟩ : Std.U64).val + 2 ^ 64 * cc.val
        = x.val + y.val + carry.val := by
  have hX : x.bv.toNat < 2 ^ 64 := x.bv.isLt
  have hY : y.bv.toNat < 2 ^ 64 := y.bv.isLt
  have hxv : x.val = x.bv.toNat := rfl
  have hyv : y.val = y.bv.toNat := rfl
  have hcv : carry.val = carry.bv.toNat := rfl
  have hs : (⟨x.bv + y.bv + carry.bv⟩ : Std.U64).val
      = (x.bv.toNat + y.bv.toNat + carry.bv.toNat) % 2 ^ 64 := by
    show (x.bv + y.bv + carry.bv).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_add_mod]
  simp only [BitVec.uaddOverflow, ge_iff_le, decide_eq_true_eq, BitVec.toNat_add] at hcc
  rw [hcv] at hc
  rw [hxv, hyv, hcv, hs, pow_two_64]
  rw [pow_two_64] at hcc hX hY
  split at hcc <;> [skip; split at hcc] <;> rename_i hov <;>
    simp only [Result.ok.injEq] at hcc <;> subst hcc <;>
    refine ⟨by scalar_tac, ?_⟩ <;>
    simp only [show (1#u64 : Std.U64).val = 1 from rfl,
      show (0#u64 : Std.U64).val = 0 from rfl] <;> omega

/-- The borrow-out of one ripple-borrow limb, likewise. -/
theorem sub_borrow_word {x y borrow bo : Std.U64} (hb : borrow.val ≤ 1)
    (hbo : (if x.bv.usubOverflow y.bv = true then ok (1#u64)
            else if (x.bv - y.bv).usubOverflow borrow.bv = true then ok (1#u64)
            else ok (0#u64)) = (ok bo : Result Std.U64)) :
    bo.val ≤ 1 ∧
      (⟨x.bv - y.bv - borrow.bv⟩ : Std.U64).val + y.val + borrow.val
        = x.val + 2 ^ 64 * bo.val := by
  have hX : x.bv.toNat < 2 ^ 64 := x.bv.isLt
  have hY : y.bv.toNat < 2 ^ 64 := y.bv.isLt
  have hxv : x.val = x.bv.toNat := rfl
  have hyv : y.val = y.bv.toNat := rfl
  have hbv : borrow.val = borrow.bv.toNat := rfl
  have hs : (⟨x.bv - y.bv - borrow.bv⟩ : Std.U64).val
      = (x.bv.toNat + (2 ^ 64 - y.bv.toNat) + (2 ^ 64 - borrow.bv.toNat)) % 2 ^ 64 := by
    show (x.bv - y.bv - borrow.bv).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_sub, Nat.add_mod_mod]
    congr 1
    rw [pow_two_64]
    omega
  simp only [BitVec.usubOverflow, decide_eq_true_eq, BitVec.toNat_sub] at hbo
  rw [hbv] at hb
  rw [hxv, hyv, hbv, hs, pow_two_64]
  rw [pow_two_64] at hbo hX hY
  split at hbo <;> [skip; split at hbo] <;> rename_i hov <;>
    simp only [Result.ok.injEq] at hbo <;> subst hbo <;>
    refine ⟨by scalar_tac, ?_⟩ <;>
    simp only [show (1#u64 : Std.U64).val = 1 from rfl,
      show (0#u64 : Std.U64).val = 0 from rfl] <;> omega

/-- The ripple-carry step, as pure arithmetic. -/
theorem add_step_arith (W O P Q Sa Sb s2 x y c carry : Nat)
    (hIH : W = O + P * s2 + P * Q * (Sa + Sb + c))
    (hw : s2 + Q * c = x + y + carry) :
    W = O + P * (x + Q * Sa + (y + Q * Sb) + carry) :=
  calc W = O + P * s2 + P * Q * (Sa + Sb + c) := hIH
    _ = O + P * (s2 + Q * c) + P * Q * Sa + P * Q * Sb := by ring
    _ = O + P * (x + y + carry) + P * Q * Sa + P * Q * Sb := by rw [hw]
    _ = O + P * (x + Q * Sa + (y + Q * Sb) + carry) := by ring

/-- The ripple-borrow step, as pure arithmetic (`bl` is the borrow this limb
produces, `bo` the borrow that leaves the whole window). -/
theorem sub_step_arith (W O P Q Sa Sb R d2 x y bl borrow bo : Nat)
    (hIH : W + P * Q * (Sb + bl) = O + P * d2 + P * Q * (Sa + R * bo))
    (hw : d2 + y + borrow = x + Q * bl) :
    W + P * (y + Q * Sb + borrow) = O + P * (x + Q * Sa + Q * R * bo) := by
  refine Nat.add_right_cancel (m := P * Q * Sb + P * Q * bl) ?_
  calc W + P * (y + Q * Sb + borrow) + (P * Q * Sb + P * Q * bl)
      = W + P * Q * (Sb + bl) + P * (y + borrow) + P * Q * Sb := by ring
    _ = O + P * d2 + P * Q * (Sa + R * bo) + P * (y + borrow) + P * Q * Sb := by rw [hIH]
    _ = O + P * (d2 + y + borrow) + P * Q * Sa + P * Q * R * bo + P * Q * Sb := by ring
    _ = O + P * (x + Q * bl) + P * Q * Sa + P * Q * R * bo + P * Q * Sb := by rw [hw]
    _ = O + P * (x + Q * Sa + Q * R * bo) + (P * Q * Sb + P * Q * bl) := by ring

theorem add_from_val (a b : alloc.vec.Vec Std.U64) (n : Std.Usize) :
    ∀ (d : Nat) (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      n.val - i.val ≤ d → carry.val ≤ 1 → ron.nat.add_from a b i n carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (seg a.val i.val n.val + seg b.val i.val n.val + carry.val) := by
  have base : ∀ (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      n.val ≤ i.val → ron.nat.add_from a b i n carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (seg a.val i.val n.val + seg b.val i.val n.val + carry.val) := by
    intro i carry out w hni h
    rw [ron.nat.add_from, if_pos (by scalar_tac)] at h
    rw [seg_of_le hni, seg_of_le hni]
    split at h <;> rename_i hcz
    · simp only [Result.ok.injEq] at h
      subst h
      have hz : carry.val = 0 := by scalar_tac
      simp [hz]
    · simp only [push_eq_ok_iff] at h
      rw [h.2, limbsToNat_append]
      simp
  intro d
  induction d with
  | zero =>
    intro i carry out w hd _ h
    exact base i carry out w (by omega) h
  | succ d ih =>
    intro i carry out w hd hc h
    rcases Nat.lt_or_ge i.val n.val with hin | hin
    · rw [ron.nat.add_from, if_neg (by scalar_tac)] at h
      simp only [Std.core.num.U64.overflowing_add, Std.UScalar.overflowing_add] at h
      simp at h
      obtain ⟨x, hx, y, hy, cc, hcc, -, out1, hout1, i1, hi1, h⟩ := h
      obtain ⟨hccb, hstep⟩ := add_carry_word hc hcc
      have hi1' : i1.val = i.val + 1 := by have := uadd_val hi1; simpa using this
      have hIH := ih i1 cc out1 w (by omega) hccb h
      rw [hout1] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append] at hIH
      rw [seg_succ a.val hin, seg_succ b.val hin, ← limb_refines hx, ← limb_refines hy, ← hi1']
      refine add_step_arith _ _ _ _ _ _ _ _ _ cc.val _ ?_ hstep
      rw [hIH]
      simp only [limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero,
        Nat.mul_add, Nat.pow_add]
      ring
    · exact base i carry out w hin h

theorem add_refines {a b c : ron.nat.Nat} (h : ron.nat.add a b = ok c) :
    toNat c = toNat a + toNat b ∧ NatWF c := by
  rw [ron.nat.add] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, h⟩ := h
  have hna : a.limbs.val.length ≤ n.val ∧ b.limbs.val.length ≤ n.val := by
    split at hn <;> simp only [Result.ok.injEq] at hn <;> subst hn <;>
      constructor <;> scalar_tac
  have hseg := add_from_val a.limbs b.limbs n n.val 0#usize 0#u64
    (alloc.vec.Vec.new Std.U64) v (by omega) (by scalar_tac) hv
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  have h0' : (0#u64 : Std.U64).val = 0 := by scalar_tac
  rw [h0, h0', seg_full _ hna.1, seg_full _ hna.2] at hseg
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
    Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at hseg
  obtain ⟨hnv, hwf⟩ := norm_refines h
  exact ⟨by rw [hnv, hseg]; rfl, hwf⟩

/-- A shorter normalised operand is numerically smaller — the fact behind
`cmp`'s length test, needed again to bound `sub`'s window. -/
theorem toNat_lt_of_length_lt {u v : ron.nat.Nat} (hv : NatWF v)
    (hlt : u.limbs.val.length < v.limbs.val.length) : toNat u < toNat v := by
  have h1 : toNat u < 2 ^ (64 * u.limbs.val.length) := limbsToNat_lt _
  have h2 : 2 ^ (64 * (v.limbs.val.length - 1)) ≤ toNat v :=
    limbsToNat_ge hv (by intro hc; rw [hc] at hlt; simp at hlt)
  have h3 : (2 : Nat) ^ (64 * u.limbs.val.length) ≤ 2 ^ (64 * (v.limbs.val.length - 1)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem sub_from_val (a b : alloc.vec.Vec Std.U64) (n : Std.Usize) :
    ∀ (d : Nat) (i : Std.Usize) (borrow : Std.U64) (out w : alloc.vec.Vec Std.U64),
      n.val - i.val ≤ d → borrow.val ≤ 1 → ron.nat.sub_from a b i n borrow out = ok w →
      w.val.length = out.val.length + (n.val - i.val) ∧
      ∃ bo : Nat, bo ≤ 1 ∧
        limbsToNat w.val + 2 ^ (64 * out.val.length) * (seg b.val i.val n.val + borrow.val)
          = limbsToNat out.val + 2 ^ (64 * out.val.length) *
              (seg a.val i.val n.val + 2 ^ (64 * (n.val - i.val)) * bo) := by
  have base : ∀ (i : Std.Usize) (borrow : Std.U64) (out w : alloc.vec.Vec Std.U64),
      n.val ≤ i.val → borrow.val ≤ 1 → ron.nat.sub_from a b i n borrow out = ok w →
      w.val.length = out.val.length + (n.val - i.val) ∧
      ∃ bo : Nat, bo ≤ 1 ∧
        limbsToNat w.val + 2 ^ (64 * out.val.length) * (seg b.val i.val n.val + borrow.val)
          = limbsToNat out.val + 2 ^ (64 * out.val.length) *
              (seg a.val i.val n.val + 2 ^ (64 * (n.val - i.val)) * bo) := by
    intro i borrow out w hni hb h
    rw [ron.nat.sub_from, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [seg_of_le hni, seg_of_le hni, Nat.sub_eq_zero_of_le hni]
    exact ⟨by omega, borrow.val, hb, by simp⟩
  intro d
  induction d with
  | zero =>
    intro i borrow out w hd hb h
    exact base i borrow out w (by omega) hb h
  | succ d ih =>
    intro i borrow out w hd hb h
    rcases Nat.lt_or_ge i.val n.val with hin | hin
    · rw [ron.nat.sub_from, if_neg (by scalar_tac)] at h
      simp only [Std.core.num.U64.overflowing_sub, Std.UScalar.overflowing_sub] at h
      simp at h
      obtain ⟨x, hx, y, hy, bl, hbl, -, out1, hout1, i1, hi1, h⟩ := h
      obtain ⟨hblb, hstep⟩ := sub_borrow_word hb hbl
      have hi1' : i1.val = i.val + 1 := by have := uadd_val hi1; simpa using this
      obtain ⟨hlen, bo, hbo1, hIH⟩ := ih i1 bl out1 w (by omega) hblb h
      rw [hout1] at hlen hIH
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen hIH
      rw [limbsToNat_append] at hIH
      refine ⟨by rw [hlen, hi1']; omega, bo, hbo1, ?_⟩
      rw [seg_succ a.val hin, seg_succ b.val hin, ← limb_refines hx, ← limb_refines hy]
      rw [hi1'] at hIH
      have hR : (2 : Nat) ^ (64 * (n.val - i.val))
          = 2 ^ 64 * 2 ^ (64 * (n.val - (i.val + 1))) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [hR]
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      simp only [limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      refine sub_step_arith _ _ _ _ _ _ _ _ _ _ bl.val _ bo ?_ hstep
      linarith [hIH]
    · exact base i borrow out w hin hb h

theorem sub_refines {a b c : ron.nat.Nat} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.sub a b = ok c) : toNat c = toNat a - toNat b ∧ NatWF c := by
  rw [ron.nat.sub] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨cc, hcc, h⟩ := h
  rcases cmp_refines ha hb hcc with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩
  · obtain ⟨hz, hwf⟩ := zero_refines h
    exact ⟨by rw [hz]; omega, hwf⟩
  · obtain ⟨hz, hwf⟩ := zero_refines h
    exact ⟨by rw [hz]; omega, hwf⟩
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨v, hsf, h⟩ := h
    have hta : toNat a = limbsToNat a.limbs.val := rfl
    have htb : toNat b = limbsToNat b.limbs.val := rfl
    have hlb : b.limbs.val.length ≤ a.limbs.val.length := by
      by_contra hcn
      exact absurd (toNat_lt_of_length_lt (u := a) (v := b) hb (by omega)) (by omega)
    have hla : (alloc.vec.Vec.len a.limbs).val = a.limbs.val.length := by scalar_tac
    obtain ⟨hlen, bo, hbo1, hseg⟩ := sub_from_val a.limbs b.limbs
      (alloc.vec.Vec.len a.limbs) (alloc.vec.Vec.len a.limbs).val 0#usize 0#u64
      (alloc.vec.Vec.new Std.U64) v le_rfl (by scalar_tac) hsf
    have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
    have h0' : (0#u64 : Std.U64).val = 0 := by scalar_tac
    rw [h0, h0', hla, seg_full _ le_rfl, seg_full _ hlb] at hseg
    rw [h0, hla] at hlen
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
      Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.sub_zero] at hseg hlen
    have hwlt : limbsToNat v.val < 2 ^ (64 * a.limbs.val.length) := by
      have hl := limbsToNat_lt v.val
      rw [hlen] at hl
      exact hl
    have halt : limbsToNat a.limbs.val < 2 ^ (64 * a.limbs.val.length) := limbsToNat_lt _
    have hbo0 : bo = 0 := by
      rcases Nat.eq_zero_or_pos bo with h1 | h1
      · exact h1
      · have h2 : bo = 1 := by omega
        rw [h2] at hseg
        omega
    rw [hbo0] at hseg
    obtain ⟨hnv, hwf⟩ := norm_refines h
    refine ⟨?_, hwf⟩
    rw [hnv]
    simp only [Nat.mul_zero, Nat.add_zero] at hseg
    omega

theorem pred_refines {a c : ron.nat.Nat} (ha : NatWF a) (h : ron.nat.pred a = ok c) :
    toNat c = toNat a - 1 ∧ NatWF c := by
  rw [ron.nat.pred] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o, ho, h⟩ := h
  obtain ⟨ho1, howf⟩ := one_refines ho
  obtain ⟨hcv, hwf⟩ := sub_refines ha howf h
  exact ⟨by rw [hcv, ho1], hwf⟩

/-! ## Bitwise operations

One limb of a bitwise operation is one `2^64`-block of the corresponding
`Nat.bitwise`, which is `Nat.testBit` extensionality plus
`Nat.testBit_two_pow_mul_add`. -/

theorem bitwise_block {f : Bool → Bool → Bool} (hf : f false false = false)
    {m x y : Nat} (hx : x < 2 ^ m) (hy : y < 2 ^ m) (A B : Nat) :
    Nat.bitwise f (x + 2 ^ m * A) (y + 2 ^ m * B)
      = Nat.bitwise f x y + 2 ^ m * Nat.bitwise f A B := by
  refine Nat.eq_of_testBit_eq (fun j => ?_)
  rw [Nat.add_comm x, Nat.add_comm y, Nat.add_comm (Nat.bitwise f x y)]
  rw [Nat.testBit_bitwise hf, Nat.testBit_two_pow_mul_add _ hx,
    Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ (Nat.bitwise_lt_two_pow (f := f) hx hy)]
  by_cases hj : j < m <;> simp only [hj, if_true, if_false, Nat.testBit_bitwise hf]

theorem land_limb {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (A B : Nat) :
    Nat.land (x + 2 ^ 64 * A) (y + 2 ^ 64 * B) = Nat.land x y + 2 ^ 64 * Nat.land A B :=
  bitwise_block (f := (· && ·)) rfl hx hy A B

theorem lor_limb {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (A B : Nat) :
    Nat.lor (x + 2 ^ 64 * A) (y + 2 ^ 64 * B) = Nat.lor x y + 2 ^ 64 * Nat.lor A B :=
  bitwise_block (f := (· || ·)) rfl hx hy A B

theorem xor_limb {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (A B : Nat) :
    Nat.xor (x + 2 ^ 64 * A) (y + 2 ^ 64 * B) = Nat.xor x y + 2 ^ 64 * Nat.xor A B :=
  bitwise_block (f := (· ^^ ·)) rfl hx hy A B

/-- The window `[0, n)` of a limb list is the value cut down to `n` limbs. -/
theorem seg_zero_mod (v : List Std.U64) (n : Nat) :
    seg v 0 n = limbsToNat v % 2 ^ (64 * n) := by
  rcases Nat.lt_or_ge n v.length with hn | hn
  · have hsplit : limbsToNat v
        = limbsToNat (v.take n) + 2 ^ (64 * n) * limbsToNat (v.drop n) := by
      conv_lhs => rw [← List.take_append_drop n v]
      rw [limbsToNat_append, List.length_take, Nat.min_eq_left (le_of_lt hn)]
    have hlt : limbsToNat (v.take n) < 2 ^ (64 * n) := by
      have hl := limbsToNat_lt (v.take n)
      rw [List.length_take, Nat.min_eq_left (le_of_lt hn)] at hl
      exact hl
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    rfl
  · rw [seg_full v hn, Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le (limbsToNat_lt v) (Nat.pow_le_pow_right (by omega) (by omega))

theorem nat_land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl
theorem nat_lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl
theorem nat_xor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl

/-- `land` only ever needs the shorter operand's window: the bits above it are
`0` on one side. -/
theorem land_mod_two_pow (A B k : Nat) (h : A < 2 ^ k ∨ B < 2 ^ k) :
    Nat.land (A % 2 ^ k) (B % 2 ^ k) = Nat.land A B := by
  refine Nat.eq_of_testBit_eq (fun j => ?_)
  simp only [nat_land_eq, Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hj : j < k
  · simp [hj]
  · have hAB : A.testBit j = false ∨ B.testBit j = false := by
      rcases h with h | h
      · exact Or.inl (Nat.testBit_lt_two_pow
          (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))))
      · exact Or.inr (Nat.testBit_lt_two_pow
          (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))))
    rcases hAB with hAB | hAB <;> simp [hj, hAB]

theorem and_from_val (a b : alloc.vec.Vec Std.U64) (n : Std.Usize) :
    ∀ (d : Nat) (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      n.val - i.val ≤ d → ron.nat.and_from a b i n out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        Nat.land (seg a.val i.val n.val) (seg b.val i.val n.val) := by
  have base : ∀ (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      n.val ≤ i.val → ron.nat.and_from a b i n out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        Nat.land (seg a.val i.val n.val) (seg b.val i.val n.val) := by
    intro i out w hni h
    rw [ron.nat.and_from, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [seg_of_le hni, seg_of_le hni]
    simp
  intro d
  induction d with
  | zero => intro i out w hd h; exact base i out w (by omega) h
  | succ d ih =>
    intro i out w hd h
    rcases Nat.lt_or_ge i.val n.val with hin | hin
    · rw [ron.nat.and_from, if_neg (by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, push_eq_ok_iff, exists_eq_left'] at h
      obtain ⟨x, hx, y, hy, out1, ⟨-, hout1⟩, i1, hi1, h⟩ := h
      have hi1' : i1.val = i.val + 1 := by have := uadd_val hi1; simpa using this
      have hIH := ih i1 out1 w (by omega) h
      rw [hout1, hi1'] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append,
        limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      rw [seg_succ a.val hin, seg_succ b.val hin, ← limb_refines hx, ← limb_refines hy,
        land_limb (by scalar_tac) (by scalar_tac)]
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [hIH]
      simp only [Std.UScalar.val_and, nat_land_eq]
      ring
    · exact base i out w hin h

theorem land_refines {a b c : ron.nat.Nat} (h : ron.nat.land a b = ok c) :
    toNat c = Nat.land (toNat a) (toNat b) ∧ NatWF c := by
  rw [ron.nat.land] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, h⟩ := h
  have hna : n.val ≤ a.limbs.val.length ∧ n.val ≤ b.limbs.val.length ∧
      (a.limbs.val.length ≤ n.val ∨ b.limbs.val.length ≤ n.val) := by
    split at hn <;> simp only [Result.ok.injEq] at hn <;> subst hn <;>
      refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    · exact Or.inl (by scalar_tac)
    · exact Or.inr (by scalar_tac)
  have hseg := and_from_val a.limbs b.limbs n n.val 0#usize (alloc.vec.Vec.new Std.U64) v
    (by omega) hv
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  rw [h0, seg_zero_mod, seg_zero_mod] at hseg
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
    Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add] at hseg
  rw [land_mod_two_pow _ _ _ ?_] at hseg
  · obtain ⟨hnv, hwf⟩ := norm_refines h
    exact ⟨by rw [hnv, hseg]; rfl, hwf⟩
  · rcases hna.2.2 with hc | hc
    · exact Or.inl (lt_of_lt_of_le (limbsToNat_lt _)
        (Nat.pow_le_pow_right (by omega) (by omega)))
    · exact Or.inr (lt_of_lt_of_le (limbsToNat_lt _)
        (Nat.pow_le_pow_right (by omega) (by omega)))

theorem or_from_val (a b : alloc.vec.Vec Std.U64) (n : Std.Usize) :
    ∀ (d : Nat) (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      n.val - i.val ≤ d → ron.nat.or_from a b i n out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        Nat.lor (seg a.val i.val n.val) (seg b.val i.val n.val) := by
  have base : ∀ (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      n.val ≤ i.val → ron.nat.or_from a b i n out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        Nat.lor (seg a.val i.val n.val) (seg b.val i.val n.val) := by
    intro i out w hni h
    rw [ron.nat.or_from, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [seg_of_le hni, seg_of_le hni]
    simp
  intro d
  induction d with
  | zero => intro i out w hd h; exact base i out w (by omega) h
  | succ d ih =>
    intro i out w hd h
    rcases Nat.lt_or_ge i.val n.val with hin | hin
    · rw [ron.nat.or_from, if_neg (by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, push_eq_ok_iff, exists_eq_left'] at h
      obtain ⟨x, hx, y, hy, out1, ⟨-, hout1⟩, i1, hi1, h⟩ := h
      have hi1' : i1.val = i.val + 1 := by have := uadd_val hi1; simpa using this
      have hIH := ih i1 out1 w (by omega) h
      rw [hout1, hi1'] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append,
        limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      rw [seg_succ a.val hin, seg_succ b.val hin, ← limb_refines hx, ← limb_refines hy,
        lor_limb (by scalar_tac) (by scalar_tac)]
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [hIH]
      simp only [Std.UScalar.val_or, nat_lor_eq]
      ring
    · exact base i out w hin h

theorem lor_refines {a b c : ron.nat.Nat} (h : ron.nat.lor a b = ok c) :
    toNat c = Nat.lor (toNat a) (toNat b) ∧ NatWF c := by
  rw [ron.nat.lor] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, h⟩ := h
  have hna : a.limbs.val.length ≤ n.val ∧ b.limbs.val.length ≤ n.val := by
    split at hn <;> simp only [Result.ok.injEq] at hn <;> subst hn <;>
      constructor <;> scalar_tac
  have hseg := or_from_val a.limbs b.limbs n n.val 0#usize (alloc.vec.Vec.new Std.U64) v
    (by omega) hv
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  rw [h0, seg_full _ hna.1, seg_full _ hna.2] at hseg
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
    Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add] at hseg
  obtain ⟨hnv, hwf⟩ := norm_refines h
  exact ⟨by rw [hnv, hseg]; rfl, hwf⟩

theorem xor_from_val (a b : alloc.vec.Vec Std.U64) (n : Std.Usize) :
    ∀ (d : Nat) (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      n.val - i.val ≤ d → ron.nat.xor_from a b i n out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        Nat.xor (seg a.val i.val n.val) (seg b.val i.val n.val) := by
  have base : ∀ (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      n.val ≤ i.val → ron.nat.xor_from a b i n out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        Nat.xor (seg a.val i.val n.val) (seg b.val i.val n.val) := by
    intro i out w hni h
    rw [ron.nat.xor_from, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [seg_of_le hni, seg_of_le hni]
    simp
  intro d
  induction d with
  | zero => intro i out w hd h; exact base i out w (by omega) h
  | succ d ih =>
    intro i out w hd h
    rcases Nat.lt_or_ge i.val n.val with hin | hin
    · rw [ron.nat.xor_from, if_neg (by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, push_eq_ok_iff, exists_eq_left'] at h
      obtain ⟨x, hx, y, hy, out1, ⟨-, hout1⟩, i1, hi1, h⟩ := h
      have hi1' : i1.val = i.val + 1 := by have := uadd_val hi1; simpa using this
      have hIH := ih i1 out1 w (by omega) h
      rw [hout1, hi1'] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append,
        limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      rw [seg_succ a.val hin, seg_succ b.val hin, ← limb_refines hx, ← limb_refines hy,
        xor_limb (by scalar_tac) (by scalar_tac)]
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [hIH]
      simp only [Std.UScalar.val_xor, nat_xor_eq]
      ring
    · exact base i out w hin h

theorem xor_refines {a b c : ron.nat.Nat} (h : ron.nat.xor a b = ok c) :
    toNat c = Nat.xor (toNat a) (toNat b) ∧ NatWF c := by
  rw [ron.nat.xor] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, h⟩ := h
  have hna : a.limbs.val.length ≤ n.val ∧ b.limbs.val.length ≤ n.val := by
    split at hn <;> simp only [Result.ok.injEq] at hn <;> subst hn <;>
      constructor <;> scalar_tac
  have hseg := xor_from_val a.limbs b.limbs n n.val 0#usize (alloc.vec.Vec.new Std.U64) v
    (by omega) hv
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  rw [h0, seg_full _ hna.1, seg_full _ hna.2] at hseg
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
    Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add] at hseg
  obtain ⟨hnv, hwf⟩ := norm_refines h
  exact ⟨by rw [hnv, hseg]; rfl, hwf⟩


/-! ## Shifts -/

theorem nat_shiftLeft_eq (x k : Nat) : Nat.shiftLeft x k = x * 2 ^ k := by
  simp [Nat.shiftLeft_eq]

theorem nat_shiftRight_eq (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k := by
  simp [Nat.shiftRight_eq_div_pow]

/-- Dropping `s` limbs divides by `2^(64 s)`. -/
theorem limbsToNat_drop (v : List Std.U64) (s : Nat) :
    limbsToNat (v.drop s) = limbsToNat v / 2 ^ (64 * s) := by
  rcases Nat.lt_or_ge v.length s with hs | hs
  · rw [List.drop_eq_nil_of_le (le_of_lt hs), Nat.div_eq_of_lt]
    · rfl
    · exact lt_of_lt_of_le (limbsToNat_lt v) (Nat.pow_le_pow_right (by omega) (by omega))
  · have hsplit : limbsToNat v
        = limbsToNat (v.take s) + 2 ^ (64 * s) * limbsToNat (v.drop s) := by
      conv_lhs => rw [← List.take_append_drop s v]
      rw [limbsToNat_append, List.length_take, Nat.min_eq_left hs]
    have hlt : limbsToNat (v.take s) < 2 ^ (64 * s) := by
      have hl := limbsToNat_lt (v.take s)
      rw [List.length_take, Nat.min_eq_left hs] at hl
      exact hl
    rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt]
    omega

/-- `a ||| b = a + b` when `b` fills only the low `m` bits and `a` only the
high ones — the shape both bit-shift loops assemble their limbs in. -/
theorem lor_disjoint (m q b : Nat) (hb : b < 2 ^ m) :
    Nat.lor b (2 ^ m * q) = b + 2 ^ m * q := by
  have hz : (0 : Nat) < 2 ^ m := Nat.two_pow_pos m
  have hw : Nat.lor (b + 2 ^ m * 0) (0 + 2 ^ m * q) = Nat.lor b 0 + 2 ^ m * Nat.lor 0 q :=
    bitwise_block (f := (· || ·)) rfl hb hz 0 q
  simp only [nat_lor_eq] at hw ⊢
  simpa using hw

theorem lor_disjoint' (m q b : Nat) (hb : b < 2 ^ m) :
    Nat.lor (2 ^ m * q) b = b + 2 ^ m * q := by
  have hz : (0 : Nat) < 2 ^ m := Nat.two_pow_pos m
  have hw : Nat.lor (0 + 2 ^ m * q) (b + 2 ^ m * 0) = Nat.lor 0 b + 2 ^ m * Nat.lor q 0 :=
    bitwise_block (f := (· || ·)) rfl hz hb q 0
  simp only [nat_lor_eq] at hw ⊢
  simpa using hw

theorem two_pow_split {bits : Nat} (h : bits ≤ 64) :
    (2 : Nat) ^ 64 = 2 ^ bits * 2 ^ (64 - bits) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- One limb of a sub-word left shift: the `|` assembles two disjoint halves. -/
theorem shl_word {x carry bits : Nat} (hb2 : bits < 64) (hx : x < 2 ^ 64)
    (hc : carry < 2 ^ bits) :
    Nat.lor (x * 2 ^ bits % 2 ^ 64) carry + 2 ^ 64 * (x / 2 ^ (64 - bits))
        = 2 ^ bits * x + carry ∧
      x / 2 ^ (64 - bits) < 2 ^ bits := by
  have hsp := two_pow_split (bits := bits) (by omega)
  have hmod : x * 2 ^ bits % 2 ^ 64 = 2 ^ bits * (x % 2 ^ (64 - bits)) := by
    rw [Nat.mul_comm x, hsp, Nat.mul_mod_mul_left]
  have hdiv : x / 2 ^ (64 - bits) < 2 ^ bits :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hsp]; exact hx)
  refine ⟨?_, hdiv⟩
  rw [hmod, lor_disjoint' bits (x % 2 ^ (64 - bits)) carry hc, hsp]
  have hmd := Nat.mod_add_div x (2 ^ (64 - bits))
  calc carry + 2 ^ bits * (x % 2 ^ (64 - bits))
        + 2 ^ bits * 2 ^ (64 - bits) * (x / 2 ^ (64 - bits))
      = carry + 2 ^ bits * (x % 2 ^ (64 - bits) + 2 ^ (64 - bits) * (x / 2 ^ (64 - bits))) := by
        ring
    _ = carry + 2 ^ bits * x := by rw [hmd]
    _ = 2 ^ bits * x + carry := by ring

/-- The left-shift loop step, as pure arithmetic. -/
theorem shl_step_arith (W O P Q S D H L X C : Nat)
    (hIH : W = O + P * L + P * Q * (S * D + H))
    (hw : L + Q * H = S * X + C) :
    W = O + P * (S * (X + Q * D) + C) :=
  calc W = O + P * L + P * Q * (S * D + H) := hIH
    _ = O + P * (L + Q * H) + P * Q * S * D := by ring
    _ = O + P * (S * X + C) + P * Q * S * D := by rw [hw]
    _ = O + P * (S * (X + Q * D) + C) := by ring

theorem push_zeros_val :
    ∀ (d : Nat) (out w : alloc.vec.Vec Std.U64) (count : Std.U64), count.val ≤ d →
      ron.nat.push_zeros out count = ok w →
      limbsToNat w.val = limbsToNat out.val ∧ w.val.length = out.val.length + count.val := by
  intro d
  induction d with
  | zero =>
    intro out w count hd h
    rw [ron.nat.push_zeros, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    have : count.val = 0 := by omega
    simp [this]
  | succ d ih =>
    intro out w count hd h
    rw [ron.nat.push_zeros] at h
    split at h <;> rename_i hz
    · simp only [Result.ok.injEq] at h
      subst h
      have : count.val = 0 := by scalar_tac
      simp [this]
    · simp only [bind_eq_ok_iff, push_eq_ok_iff] at h
      obtain ⟨out1, ⟨-, hout1⟩, c1, hc1, h⟩ := h
      have hc1' : c1.val = count.val - 1 := (usub_val hc1).2.trans (by simp)
      have hcz : 0 < count.val := by scalar_tac
      obtain ⟨hv, hl⟩ := ih out1 w c1 (by omega) h
      rw [hout1] at hv hl
      simp only [limbsToNat_append, limbsToNat_cons, limbsToNat_nil, Nat.mul_zero,
        Nat.add_zero, List.length_append, List.length_cons, List.length_nil] at hv hl
      refine ⟨hv, ?_⟩
      rw [hl, hc1']
      omega

theorem shl_bits_from_val (v : alloc.vec.Vec Std.U64) (bits : Std.U64) (hb2 : bits.val < 64) :
    ∀ (d : Nat) (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      v.val.length - i.val ≤ d → carry.val < 2 ^ bits.val →
      ron.nat.shl_bits_from v i bits carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (2 ^ bits.val * limbsToNat (v.val.drop i.val) + carry.val) := by
  have base : ∀ (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      v.val.length ≤ i.val → ron.nat.shl_bits_from v i bits carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (2 ^ bits.val * limbsToNat (v.val.drop i.val) + carry.val) := by
    intro i carry out w hni h
    rw [ron.nat.shl_bits_from, if_pos (by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le hni]
    split at h <;> rename_i hcz
    · simp only [Result.ok.injEq] at h
      subst h
      have : carry.val = 0 := by scalar_tac
      simp [this]
    · simp only [push_eq_ok_iff] at h
      rw [h.2, limbsToNat_append]
      simp
  intro d
  induction d with
  | zero => intro i carry out w hd hc h; exact base i carry out w (by omega) h
  | succ d ih =>
    intro i carry out w hd hc h
    rcases Nat.lt_or_ge i.val v.val.length with hin | hin
    · rw [ron.nat.shl_bits_from, if_neg (by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, push_eq_ok_iff, exists_eq_left',
        alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff] at h
      obtain ⟨x, hx, i2, hi2, i3, hi3, hi, hhi, out1, ⟨-, hout1⟩, i4, hi4, h⟩ := h
      have hx' : x = v.val[i.val] := by
        rw [List.getElem?_eq_getElem hin] at hx; exact (Option.some.injEq _ _ ▸ hx).symm
      have hi2' : i2.val = x.val * 2 ^ bits.val % 2 ^ 64 := by
        have := (ushiftLeft_val hi2).2; simpa using this
      have hi3' : i3.val = 64 - bits.val := (usub_val hi3).2.trans (by simp)
      have hhi' : hi.val = x.val / 2 ^ (64 - bits.val) := by
        have := (ushiftRight_val hhi).2; rw [hi3'] at this; simpa using this
      have hi4' : i4.val = i.val + 1 := by have := uadd_val hi4; simpa using this
      obtain ⟨hword, hhib⟩ := shl_word (x := x.val) (carry := carry.val) hb2 (by scalar_tac) hc
      have hIH := ih i4 hi out1 w (by omega) (by rw [hhi']; exact hhib) h
      rw [hout1, hi4'] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append,
        limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [List.drop_eq_getElem_cons hin, limbsToNat_cons, ← hx']
      have hlov : (i2 ||| carry).val = Nat.lor i2.val carry.val := by
        simp only [Std.UScalar.val_or, nat_lor_eq]
      have hw2 : (i2 ||| carry).val + 2 ^ 64 * hi.val = 2 ^ bits.val * x.val + carry.val := by
        rw [hlov, hi2', hhi']; exact hword
      exact shl_step_arith _ _ _ _ _ _ _ _ _ _ hIH hw2
    · exact base i carry out w hin h

/-- The tail both left shifts share: `a`'s limbs shifted left by `bits` and
appended to `out`, whose value is `0` (a run of zero limbs). -/
theorem shl_onto_refines {a c : ron.nat.Nat} {bits : Std.U64} {out : alloc.vec.Vec Std.U64}
    (hb : bits.val < 64) (hout : limbsToNat out.val = 0)
    (h : ron.nat.shl_onto a bits out = ok c) :
    toNat c = toNat a * 2 ^ (64 * out.val.length + bits.val) ∧ NatWF c := by
  rw [ron.nat.shl_onto] at h
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  split at h <;> rename_i hbz2
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hcf := copy_from_refines (v := a.limbs) (i := 0#usize)
      (e := alloc.vec.Vec.len a.limbs) (out := out) (w := v) (by scalar_tac) hv
    have hle : (alloc.vec.Vec.len a.limbs).val = a.limbs.val.length := by scalar_tac
    rw [h0, hle] at hcf
    simp only [Nat.sub_zero, List.drop_zero, List.take_length] at hcf
    have hvv : limbsToNat v.val = 2 ^ (64 * out.val.length) * toNat a := by
      rw [hcf, limbsToNat_append, hout]
      simp [toNat]
    obtain ⟨hnv, hwf⟩ := norm_refines h
    refine ⟨?_, hwf⟩
    have hbz3 : bits.val = 0 := by rw [hbz2]; scalar_tac
    rw [hnv, hvv, hbz3, Nat.add_zero]
    ring
  · obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    have hsl := shl_bits_from_val a.limbs bits hb a.limbs.val.length 0#usize 0#u64
      out v (by omega) (by simp) hv
    rw [h0] at hsl
    simp only [List.drop_zero, hout, Nat.zero_add] at hsl
    have h0' : (0#u64 : Std.U64).val = 0 := by scalar_tac
    rw [h0', Nat.add_zero] at hsl
    obtain ⟨hnv, hwf⟩ := norm_refines h
    refine ⟨?_, hwf⟩
    rw [hnv, hsl, Nat.pow_add]
    simp only [toNat]
    ring

theorem shift_left_refines {a c : ron.nat.Nat} {k : Std.U64}
    (h : ron.nat.shift_left a k = ok c) :
    toNat c = Nat.shiftLeft (toNat a) k.val ∧ NatWF c := by
  rw [ron.nat.shift_left] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  rw [ron.nat.is_zero] at hb
  simp only [Result.ok.injEq] at hb
  split at h <;> rename_i hbz
  · rw [hbz] at hb
    have hz : a.limbs.val = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      have h0 : alloc.vec.Vec.len a.limbs = 0#usize := by simpa using hb
      scalar_tac
    obtain ⟨hc0, hwf⟩ := zero_refines h
    refine ⟨hc0.trans ?_, hwf⟩
    rw [nat_shiftLeft_eq]
    simp [toNat, hz]
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨words, hwords, out, hout, bits, hbits, h⟩ := h
    have hwv : words.val = k.val / 64 := by have := udiv_val hwords; simpa using this
    have hbvv : bits.val = k.val % 64 := by have := urem_val hbits; simpa using this
    obtain ⟨hov, hol⟩ :=
      push_zeros_val words.val (alloc.vec.Vec.new Std.U64) out words le_rfl hout
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil,
      List.length_nil, Nat.zero_add] at hov hol
    obtain ⟨hcv, hwf⟩ := shl_onto_refines (by omega) hov h
    refine ⟨?_, hwf⟩
    rw [hcv, nat_shiftLeft_eq, hol, hwv, hbvv]
    congr 2
    omega

/-- `push_zeros_nat` appends `count` zero limbs, for a bignum `count` (task
#98-SHIFT).  Partial correctness: an amount beyond `u64` pushes `u64::MAX`
zeros and recurses, and the lemma speaks only of a run that returned. -/
theorem push_zeros_nat_val :
    ∀ (d : Nat) (out w : alloc.vec.Vec Std.U64) (count : ron.nat.Nat), NatWF count →
      toNat count ≤ d → ron.nat.push_zeros_nat out count = ok w →
      limbsToNat w.val = limbsToNat out.val ∧ w.val.length = out.val.length + toNat count := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro out w count hwf hd h
  rw [ron.nat.push_zeros_nat] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  rcases to_u64_refines hwf ho with ⟨x, hx, hxv⟩ | ⟨hn, hge⟩
  · subst hx
    obtain ⟨hv, hl⟩ := push_zeros_val x.val out w x le_rfl h
    exact ⟨hv, by rw [hl, hxv]⟩
  · subst hn
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o1, ho1, m, hm, rest, hrest, h⟩ := h
    obtain ⟨hv1, hl1⟩ := push_zeros_val _ out o1 _ le_rfl ho1
    obtain ⟨hmv, hmwf⟩ := from_u64_refines hm
    obtain ⟨hrv, hrwf⟩ := sub_refines hwf hmwf hrest
    have hmv' : toNat m = 2 ^ 64 - 1 := by rw [hmv]; scalar_tac
    have hl1' : o1.val.length = out.val.length + (2 ^ 64 - 1) := by rw [hl1]; scalar_tac
    obtain ⟨hv2, hl2⟩ := ih (toNat rest) (by rw [hrv, hmv']; omega) o1 w rest hrwf le_rfl h
    refine ⟨hv2.trans hv1, ?_⟩
    rw [hl2, hl1', hrv, hmv']
    omega

/-- The low limb is the value modulo `2^64`. -/
theorem low_limb_val {a : ron.nat.Nat} {x : Std.U64} (h : ron.nat.low_limb a = ok x) :
    x.val = toNat a % 2 ^ 64 := by
  rw [ron.nat.low_limb] at h
  split at h <;> rename_i h0
  · simp only [Result.ok.injEq] at h
    subst h
    have : a.limbs.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    simp [toNat, this]
  · simp only [alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff] at h
    have hne : 0 < a.limbs.val.length := by scalar_tac
    obtain ⟨y, r, hyr⟩ := List.exists_cons_of_length_pos hne
    have hx : x = y := by
      rw [hyr] at h; simpa using h.symm
    subst hx
    simp only [toNat, hyr, limbsToNat_cons]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by scalar_tac)]

/-! ### Right shift -/

theorem skip_index_val (v : alloc.vec.Vec Std.U64) :
    ∀ (d : Nat) (i : Std.Usize) (remaining : Std.U64) (s : Std.Usize),
      remaining.val ≤ d → i.val ≤ v.val.length →
      ron.nat.skip_index v i remaining = ok s →
      s.val = min (i.val + remaining.val) v.val.length := by
  intro d
  induction d with
  | zero =>
    intro i remaining s hd hi h
    rw [ron.nat.skip_index, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    omega
  | succ d ih =>
    intro i remaining s hd hi h
    rw [ron.nat.skip_index] at h
    split at h <;> rename_i hr
    · simp only [Result.ok.injEq] at h
      subst h
      have : remaining.val = 0 := by scalar_tac
      omega
    · have hr' : 0 < remaining.val := by scalar_tac
      simp only [] at h
      split at h <;> rename_i hiv
      · simp only [Result.ok.injEq] at h
        subst h
        have : v.val.length ≤ i.val := by scalar_tac
        have hl : (alloc.vec.Vec.len v).val = v.val.length := by scalar_tac
        omega
      · have hiv' : i.val < v.val.length := by scalar_tac
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, r2, hr2, h⟩ := h
        have hi2' : i2.val = i.val + 1 := by have := uadd_val hi2; simpa using this
        have hr2' : r2.val = remaining.val - 1 := (usub_val hr2).2.trans (by simp)
        have := ih i2 r2 s (by omega) (by omega) h
        omega

/-- One limb of a sub-word right shift. -/
theorem shr_word {X D bits : Nat} (hb2 : bits < 64) (hX : X < 2 ^ 64) :
    Nat.lor (X / 2 ^ bits) (2 ^ (64 - bits) * (D % 2 ^ bits)) + 2 ^ 64 * (D / 2 ^ bits)
      = (X + 2 ^ 64 * D) / 2 ^ bits := by
  have hsp := two_pow_split (bits := bits) (le_of_lt hb2)
  have hlt : X / 2 ^ bits < 2 ^ (64 - bits) :=
    Nat.div_lt_of_lt_mul (by rw [← hsp]; exact hX)
  rw [lor_disjoint (64 - bits) (D % 2 ^ bits) (X / 2 ^ bits) hlt]
  have hdiv : (X + 2 ^ 64 * D) / 2 ^ bits = X / 2 ^ bits + 2 ^ (64 - bits) * D := by
    rw [hsp, show 2 ^ bits * 2 ^ (64 - bits) * D = 2 ^ (64 - bits) * D * 2 ^ bits by ring,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos bits)]
  rw [hdiv]
  have hD := Nat.mod_add_div D (2 ^ bits)
  calc X / 2 ^ bits + 2 ^ (64 - bits) * (D % 2 ^ bits) + 2 ^ 64 * (D / 2 ^ bits)
      = X / 2 ^ bits
          + 2 ^ (64 - bits) * (D % 2 ^ bits + 2 ^ bits * (D / 2 ^ bits)) := by
        rw [hsp]; ring
    _ = X / 2 ^ bits + 2 ^ (64 - bits) * D := by rw [hD]

/-- The right-shift loop step, as pure arithmetic. -/
theorem shr_step_arith (W O P L R : Nat) (hIH : W = O + P * L + P * R) :
    W = O + P * (L + R) := by rw [hIH]; ring

theorem shr_bits_from_val (v : alloc.vec.Vec Std.U64) (bits : Std.U64) (hb2 : bits.val < 64) :
    ∀ (d : Nat) (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      v.val.length - i.val ≤ d → ron.nat.shr_bits_from v i bits out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (limbsToNat (v.val.drop i.val) / 2 ^ bits.val) := by
  have base : ∀ (i : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      v.val.length ≤ i.val → ron.nat.shr_bits_from v i bits out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (limbsToNat (v.val.drop i.val) / 2 ^ bits.val) := by
    intro i out w hni h
    rw [ron.nat.shr_bits_from, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le hni]
    simp
  intro d
  induction d with
  | zero => intro i out w hd h; exact base i out w (by omega) h
  | succ d ih =>
    intro i out w hd h
    rcases Nat.lt_or_ge i.val v.val.length with hin | hin
    · rw [ron.nat.shr_bits_from, if_neg (by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, push_eq_ok_iff, exists_eq_left',
        alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff] at h
      obtain ⟨x, hx, lo, hlo, i3, hi3, hi, hhi, out1, ⟨-, hout1⟩, h⟩ := h
      have hx' : x = v.val[i.val] := by
        rw [List.getElem?_eq_getElem hin] at hx; exact (Option.some.injEq _ _ ▸ hx).symm
      have hlo' : lo.val = x.val / 2 ^ bits.val := by
        have := (ushiftRight_val hlo).2; simpa using this
      have hi3' : i3.val = i.val + 1 := by have := uadd_val hi3; simpa using this
      -- the high half is `2^(64-bits)` times the low `bits` bits of the rest
      have hsp := two_pow_split (bits := bits.val) (le_of_lt hb2)
      have hhi' : hi.val
          = 2 ^ (64 - bits.val) * (limbsToNat (v.val.drop i3.val) % 2 ^ bits.val) := by
        split at hhi <;> rename_i hlt2
        · have hlt3 : i3.val < v.val.length := by scalar_tac
          simp only [bind_eq_ok_iff, index_usize_eq_ok_iff] at hhi
          obtain ⟨y, hy, i6, hi6, hhi⟩ := hhi
          have hy' : y = v.val[i3.val] := by
            rw [List.getElem?_eq_getElem hlt3] at hy
            exact (Option.some.injEq _ _ ▸ hy).symm
          have hi6' : i6.val = 64 - bits.val := (usub_val hi6).2.trans (by simp)
          have hhv : hi.val = y.val * 2 ^ (64 - bits.val) % 2 ^ 64 := by
            have := (ushiftLeft_val hhi).2; rw [hi6'] at this; simpa using this
          rw [hhv, Nat.mul_comm y.val, hsp, Nat.mul_comm (2 ^ bits.val),
            Nat.mul_mod_mul_left]
          rw [List.drop_eq_getElem_cons hlt3, limbsToNat_cons, ← hy']
          rw [show 2 ^ 64 * limbsToNat (v.val.drop (i3.val + 1))
              = 2 ^ bits.val * (2 ^ (64 - bits.val)
                  * limbsToNat (v.val.drop (i3.val + 1))) by rw [hsp]; ring,
            Nat.add_mul_mod_self_left]
        · have hge : v.val.length ≤ i3.val := by scalar_tac
          simp only [Result.ok.injEq] at hhi
          rw [← hhi, List.drop_eq_nil_of_le hge]
          simp
      have hIH := ih i3 out1 w (by omega) h
      rw [hout1] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append,
        limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [List.drop_eq_getElem_cons hin, limbsToNat_cons, ← hx']
      have hlov : (lo ||| hi).val = Nat.lor lo.val hi.val := by
        simp only [Std.UScalar.val_or, nat_lor_eq]
      have hkey : (lo ||| hi).val
            + 2 ^ 64 * (limbsToNat (v.val.drop i3.val) / 2 ^ bits.val)
          = (x.val + 2 ^ 64 * limbsToNat (v.val.drop i3.val)) / 2 ^ bits.val := by
        rw [hlov, hlo', hhi']
        exact shr_word hb2 (by scalar_tac)
      rw [hi3'] at hIH hkey
      calc limbsToNat w.val
          = limbsToNat out.val + 2 ^ (64 * out.val.length) * (lo ||| hi).val
              + 2 ^ (64 * out.val.length) * 2 ^ 64
                * (limbsToNat (v.val.drop (i.val + 1)) / 2 ^ bits.val) := hIH
        _ = limbsToNat out.val + 2 ^ (64 * out.val.length)
              * ((lo ||| hi).val
                  + 2 ^ 64 * (limbsToNat (v.val.drop (i.val + 1)) / 2 ^ bits.val)) := by ring
        _ = _ := by rw [hkey]
    · exact base i out w hin h

/-- The tail both right shifts share: `a`'s limbs from `s` on, shifted right
by `bits`. -/
theorem shr_from_refines {a c : ron.nat.Nat} {s : Std.Usize} {bits : Std.U64}
    (hb : bits.val < 64) (hs : s.val ≤ a.limbs.val.length)
    (h : ron.nat.shr_from a s bits = ok c) :
    toNat c = toNat a / 2 ^ (64 * s.val) / 2 ^ bits.val ∧ NatWF c := by
  rw [ron.nat.shr_from] at h
  have hdrop : limbsToNat (a.limbs.val.drop s.val) = toNat a / 2 ^ (64 * s.val) :=
    limbsToNat_drop _ _
  split at h <;> rename_i hbz2
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hcf := copy_from_refines (v := a.limbs) (i := s)
      (e := alloc.vec.Vec.len a.limbs) (out := alloc.vec.Vec.new Std.U64) (w := v)
      (by scalar_tac) hv
    have hle : (alloc.vec.Vec.len a.limbs).val = a.limbs.val.length := by scalar_tac
    rw [hle] at hcf
    rw [List.take_of_length_le (by simp)] at hcf
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] at hcf
    obtain ⟨hnv, hwf⟩ := norm_refines h
    refine ⟨?_, hwf⟩
    have hbz3 : bits.val = 0 := by rw [hbz2]; scalar_tac
    rw [hnv, hcf, hdrop, hbz3, pow_zero, Nat.div_one]
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hsr := shr_bits_from_val a.limbs bits hb a.limbs.val.length s
      (alloc.vec.Vec.new Std.U64) v (by omega) hv
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
      Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add] at hsr
    obtain ⟨hnv, hwf⟩ := norm_refines h
    refine ⟨?_, hwf⟩
    rw [hnv, hsr, hdrop]

/-- Skipping `min words len` limbs and then `bits` bits is shifting by
`64 * words + bits`: past the length, both sides are `0`. -/
theorem skip_shr_key (a : ron.nat.Nat) (words bits s : Nat)
    (hs : s = min words a.limbs.val.length) :
    toNat a / 2 ^ (64 * s) / 2 ^ bits = toNat a / 2 ^ (64 * words + bits) := by
  rcases Nat.lt_or_ge a.limbs.val.length words with hgt | hle
  · have hsl : s = a.limbs.val.length := by omega
    have h1 : toNat a / 2 ^ (64 * s) = 0 := by
      refine Nat.div_eq_of_lt ?_
      rw [hsl]
      exact limbsToNat_lt _
    have h2 : toNat a / 2 ^ (64 * words + bits) = 0 := by
      refine Nat.div_eq_of_lt (lt_of_lt_of_le (limbsToNat_lt _) ?_)
      refine Nat.pow_le_pow_right (by omega) ?_
      omega
    rw [h1, h2]
    simp
  · have hsw : s = words := by omega
    rw [hsw, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem shift_right_refines {a c : ron.nat.Nat} {k : Std.U64}
    (h : ron.nat.shift_right a k = ok c) :
    toNat c = Nat.shiftRight (toNat a) k.val ∧ NatWF c := by
  rw [ron.nat.shift_right] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨words, hwords, s, hs, bits, hbits, h⟩ := h
  have hwv : words.val = k.val / 64 := by have := udiv_val hwords; simpa using this
  have hbvv : bits.val = k.val % 64 := by have := urem_val hbits; simpa using this
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  have hsv := skip_index_val a.limbs words.val 0#usize words s le_rfl (by omega) hs
  rw [h0, Nat.zero_add] at hsv
  obtain ⟨hcv, hwf⟩ := shr_from_refines (by omega) (by omega) h
  refine ⟨?_, hwf⟩
  rw [hcv, skip_shr_key a words.val bits.val s.val hsv, nat_shiftRight_eq]
  congr 2
  omega

/-- **`Nat.shiftRight a k` for a bignum amount** (task #98-SHIFT): total and
exact.  A whole-word part beyond `u64` exceeds every limb count, so the
answer there is `0`. -/
theorem shift_right_nat_refines {a k c : ron.nat.Nat} (hk : NatWF k)
    (h : ron.nat.shift_right_nat a k = ok c) :
    toNat c = Nat.shiftRight (toNat a) (toNat k) ∧ NatWF c := by
  rw [ron.nat.shift_right_nat] at h
  obtain ⟨words, hwords, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hwv, hwwf⟩ := shift_right_refines hwords
  have h6 : (6#u64 : Std.U64).val = 6 := by scalar_tac
  rw [h6, nat_shiftRight_eq] at hwv
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  rcases to_u64_refines hwwf ho with ⟨w, hw, hwv'⟩ | ⟨hn, hge⟩
  · subst hw
    simp only [bind_eq_ok_iff] at h
    obtain ⟨s, hs, lo, hlo, bits, hbits, h⟩ := h
    have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
    have hsv := skip_index_val a.limbs w.val 0#usize w s le_rfl (by omega) hs
    rw [h0, Nat.zero_add] at hsv
    have hlov := low_limb_val hlo
    have hbvv : bits.val = toNat k % 64 := by
      have h1 : bits.val = lo.val % 64 := by have := urem_val hbits; simpa using this
      rw [h1, hlov, Nat.mod_mod_of_dvd _ (by norm_num)]
    obtain ⟨hcv, hwf⟩ := shr_from_refines (by omega) (by omega) h
    refine ⟨?_, hwf⟩
    rw [hcv, skip_shr_key a w.val bits.val s.val hsv, nat_shiftRight_eq]
    congr 2
    omega
  · subst hn
    obtain ⟨hc0, hwf⟩ := zero_refines h
    refine ⟨?_, hwf⟩
    rw [hc0, nat_shiftRight_eq]
    have hlen : a.limbs.val.length < 2 ^ 64 := by
      have h1 : a.limbs.val.length ≤ Std.Usize.max := a.limbs.property
      have h2 : Std.Usize.max < 2 ^ 64 := by
        simp only [Std.Usize.max, Std.Usize.numBits]
        rcases System.Platform.numBits_eq with h | h <;> simp [h]
      omega
    symm
    refine Nat.div_eq_of_lt (lt_of_lt_of_le (limbsToNat_lt _) ?_)
    refine Nat.pow_le_pow_right (by omega) ?_
    omega

/-- **`Nat.shiftLeft a k` for a bignum amount** (task #98-SHIFT): unbounded;
a run that returns computed the exact shift. -/
theorem shift_left_nat_refines {a k c : ron.nat.Nat} (hk : NatWF k)
    (h : ron.nat.shift_left_nat a k = ok c) :
    toNat c = Nat.shiftLeft (toNat a) (toNat k) ∧ NatWF c := by
  rw [ron.nat.shift_left_nat] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  rw [ron.nat.is_zero] at hb
  simp only [Result.ok.injEq] at hb
  split at h <;> rename_i hbz
  · rw [hbz] at hb
    have hz : a.limbs.val = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      have h0 : alloc.vec.Vec.len a.limbs = 0#usize := by simpa using hb
      scalar_tac
    obtain ⟨hc0, hwf⟩ := zero_refines h
    refine ⟨hc0.trans ?_, hwf⟩
    rw [nat_shiftLeft_eq]
    simp [toNat, hz]
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨words, hwords, out, hout, lo, hlo, bits, hbits, h⟩ := h
    obtain ⟨hwv, hwwf⟩ := shift_right_refines hwords
    have h6 : (6#u64 : Std.U64).val = 6 := by scalar_tac
    rw [h6, nat_shiftRight_eq] at hwv
    obtain ⟨hov, hol⟩ :=
      push_zeros_nat_val _ (alloc.vec.Vec.new Std.U64) out words hwwf le_rfl hout
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil,
      List.length_nil, Nat.zero_add] at hov hol
    have hlov := low_limb_val hlo
    have hbvv : bits.val = toNat k % 64 := by
      have h1 : bits.val = lo.val % 64 := by have := urem_val hbits; simpa using this
      rw [h1, hlov, Nat.mod_mod_of_dvd _ (by norm_num)]
    obtain ⟨hcv, hwf⟩ := shl_onto_refines (by omega) hov h
    refine ⟨?_, hwf⟩
    rw [hcv, nat_shiftLeft_eq, hol, hwv, hbvv]
    congr 2
    omega

/-! ## Multiplication and power -/

theorem mul_u64_from_val (v : alloc.vec.Vec Std.U64) (m : Std.U64) :
    ∀ (d : Nat) (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      v.val.length - i.val ≤ d → ron.nat.mul_u64_from v i m carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (m.val * limbsToNat (v.val.drop i.val) + carry.val) := by
  have base : ∀ (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      v.val.length ≤ i.val → ron.nat.mul_u64_from v i m carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (m.val * limbsToNat (v.val.drop i.val) + carry.val) := by
    intro i carry out w hni h
    rw [ron.nat.mul_u64_from, if_pos (by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le hni]
    split at h <;> rename_i hcz
    · simp only [Result.ok.injEq] at h
      subst h
      have hz : carry.val = 0 := by scalar_tac
      simp [hz]
    · simp only [push_eq_ok_iff] at h
      rw [h.2, limbsToNat_append]
      simp
  intro d
  induction d with
  | zero => intro i carry out w hd h; exact base i carry out w (by omega) h
  | succ d ih =>
    intro i carry out w hd h
    rcases Nat.lt_or_ge i.val v.val.length with hin | hin
    · rw [ron.nat.mul_u64_from, if_neg (by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, push_eq_ok_iff, exists_eq_left',
        alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff] at h
      obtain ⟨x, hx, i5, hi5, t, ht, i7, hi7, out1, ⟨-, hout1⟩, i8, hi8, h⟩ := h
      have hx' : x = v.val[i.val] := by
        rw [List.getElem?_eq_getElem hin] at hx; exact (Option.some.injEq _ _ ▸ hx).symm
      have hxv : (Std.UScalar.cast .U128 x).val = x.val := by
        rw [Std.UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hmv : (Std.UScalar.cast .U128 m).val = m.val := by
        rw [Std.UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hcv : (Std.UScalar.cast .U128 carry).val = carry.val := by
        rw [Std.UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hi5' : i5.val = x.val * m.val := by
        have := (umul_val hi5).2; rw [hxv, hmv] at this; exact this
      have htv : t.val = x.val * m.val + carry.val := by
        have := uadd_val ht; rw [hi5', hcv] at this; exact this
      have hi7' : i7.val = t.val / 2 ^ 64 := by
        have := (ushiftRightI_val hi7).2; simpa using this
      have hlov : (Std.UScalar.cast .U64 t).val = t.val % 2 ^ 64 :=
        Std.UScalar.cast_val_eq _ _
      have hhiv : (Std.UScalar.cast .U64 i7).val = i7.val := by
        rw [Std.UScalar.cast_val_eq]
        refine Nat.mod_eq_of_lt ?_
        rw [hi7', htv]
        have hx64 : x.val < 2 ^ 64 := by scalar_tac
        have hm64 : m.val < 2 ^ 64 := by scalar_tac
        have hc64 : carry.val < 2 ^ 64 := by scalar_tac
        refine Nat.div_lt_of_lt_mul ?_
        calc x.val * m.val + carry.val
            < (2 ^ 64 - 1) * (2 ^ 64 - 1) + 2 ^ 64 := by
              refine Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul (by omega) (by omega)) hc64
          _ ≤ 2 ^ 64 * 2 ^ 64 := by
              have : (2 : Nat) ^ 64 = 18446744073709551616 := pow_two_64
              rw [this]; omega
      have hi8' : i8.val = i.val + 1 := by have := uadd_val hi8; simpa using this
      have hword : (Std.UScalar.cast .U64 t : Std.U64).val
          + 2 ^ 64 * (Std.UScalar.cast .U64 i7 : Std.U64).val = m.val * x.val + carry.val := by
        rw [hlov, hhiv, hi7', htv]
        have := Nat.mod_add_div (x.val * m.val + carry.val) (2 ^ 64)
        rw [Nat.mul_comm m.val]
        omega
      have hIH := ih i8 (Std.UScalar.cast .U64 i7) out1 w (by omega) h
      rw [hout1, hi8'] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append,
        limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [List.drop_eq_getElem_cons hin, limbsToNat_cons, ← hx']
      exact shl_step_arith _ _ _ _ _ _ _ _ _ _ hIH hword
    · exact base i carry out w hin h

theorem mul_u64_refines {a c : ron.nat.Nat} {m : Std.U64} (h : ron.nat.mul_u64 a m = ok c) :
    toNat c = m.val * toNat a ∧ NatWF c := by
  rw [ron.nat.mul_u64] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hmf := mul_u64_from_val a.limbs m a.limbs.val.length 0#usize 0#u64
    (alloc.vec.Vec.new Std.U64) v (by omega) hv
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  have h0' : (0#u64 : Std.U64).val = 0 := by scalar_tac
  rw [h0, h0'] at hmf
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
    Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, List.drop_zero] at hmf
  obtain ⟨hnv, hwf⟩ := norm_refines h
  exact ⟨by rw [hnv, hmf]; rfl, hwf⟩

theorem mul_from_val (a b : ron.nat.Nat) :
    ∀ (d : Nat) (i : Std.Usize) (sh : Std.U64) (acc c : ron.nat.Nat),
      b.limbs.val.length - i.val ≤ d → sh.val = 64 * i.val → NatWF acc →
      ron.nat.mul_from a b i sh acc = ok c →
      toNat c = toNat acc + 2 ^ sh.val * toNat a * seg b.limbs.val i.val b.limbs.val.length
        ∧ NatWF c := by
  intro d
  induction d with
  | zero =>
    intro i sh acc c hd hsh hwf h
    rw [ron.nat.mul_from, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    rw [seg_of_le (by omega)]
    exact ⟨by simp, hwf⟩
  | succ d ih =>
    intro i sh acc c hd hsh hwf h
    rw [ron.nat.mul_from] at h
    split at h <;> rename_i hie
    · simp only [Result.ok.injEq] at h
      subst h
      rw [seg_of_le (by scalar_tac)]
      exact ⟨by simp, hwf⟩
    · have hin : i.val < b.limbs.val.length := by scalar_tac
      simp only [bind_eq_ok_iff, alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff] at h
      obtain ⟨y, hy, p, hp, ps, hps, acc2, hacc2, i3, hi3, i4, hi4, h⟩ := h
      have hy' : y = b.limbs.val[i.val] := by
        rw [List.getElem?_eq_getElem hin] at hy; exact (Option.some.injEq _ _ ▸ hy).symm
      have hlimb : limbAt b.limbs.val i.val = y := by
        rw [limbAt, List.getD_eq_getElem _ _ hin, hy']
      have hpv := (mul_u64_refines hp).1
      have hpsv := (shift_left_refines hps).1
      obtain ⟨haccv, haccwf⟩ := add_refines hacc2
      have hi3' : i3.val = i.val + 1 := by have := uadd_val hi3; simpa using this
      have hi4' : i4.val = sh.val + 64 := by have := uadd_val hi4; simpa using this
      obtain ⟨hIH, hcwf⟩ := ih i3 i4 acc2 c (by omega) (by omega) haccwf h
      refine ⟨?_, hcwf⟩
      rw [hIH, haccv, hpsv, nat_shiftLeft_eq, hpv, hi4', hi3']
      rw [seg_succ b.limbs.val hin, hlimb, Nat.pow_add, hsh]
      ring

theorem mul_refines {a b c : ron.nat.Nat} (h : ron.nat.mul a b = ok c) :
    toNat c = toNat a * toNat b ∧ NatWF c := by
  rw [ron.nat.mul] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨hz0, hzwf⟩ := zero_refines hz
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  have h0' : (0#u64 : Std.U64).val = 0 := by scalar_tac
  obtain ⟨hmf, hwf⟩ := mul_from_val a b b.limbs.val.length 0#usize 0#u64 z c (by omega)
    (by rw [h0, h0']) hzwf h
  rw [h0, h0', hz0, seg_full _ le_rfl] at hmf
  refine ⟨?_, hwf⟩
  rw [hmf]
  simp [toNat]

theorem pow_refines : ∀ (E : Nat) (a c : ron.nat.Nat) (e : Std.U64), e.val = E →
    ron.nat.pow a e = ok c → toNat c = toNat a ^ e.val ∧ NatWF c := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ihE =>
    intro a c e hE h
    rw [ron.nat.pow] at h
    split at h <;> rename_i hez
    · obtain ⟨h1, hwf⟩ := one_refines h
      have he0 : e.val = 0 := by scalar_tac
      rw [he0]
      exact ⟨by rw [h1]; simp, hwf⟩
    · have hez' : 0 < e.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, f, hf, hh2, hmul, i1, hi1, h⟩ := h
      have hi' : i.val = e.val / 2 := by have := udiv_val hi; simpa using this
      have hi1' : i1.val = e.val % 2 := by have := urem_val hi1; simpa using this
      obtain ⟨hfv, hfwf⟩ := ihE i.val (by omega) a f i rfl hf
      obtain ⟨hh2v, hh2wf⟩ := mul_refines hmul
      split at h <;> rename_i hpar
      · simp only [Result.ok.injEq] at h
        subst h
        refine ⟨?_, hh2wf⟩
        have hp : e.val % 2 = 0 := by rw [← hi1', hpar]; scalar_tac
        rw [hh2v, hfv, hi', ← Nat.pow_add]
        congr 1
        omega
      · obtain ⟨hcv, hcwf⟩ := mul_refines h
        refine ⟨?_, hcwf⟩
        have hp : e.val % 2 = 1 := by
          have hne : i1.val ≠ 0 := fun hc => hpar (by scalar_tac)
          omega
        rw [hcv, hh2v, hfv, hi', ← Nat.pow_add, ← Nat.pow_succ]
        congr 1
        omega

/-! ## Division, remainder, gcd

Shift-subtract long division: `dm_bits` runs the standard restoring
remainder/quotient invariant one bit at a time, `dm_limbs` one limb at a
time, and `div_mod` reverses the most-significant-first quotient limbs. -/

theorem mod_two_pow_succ (X m : Nat) :
    X % 2 ^ (m + 1) = X % 2 ^ m + 2 ^ m * (X / 2 ^ m % 2) := by
  rw [Nat.pow_succ, Nat.mod_mul]

theorem lor_one_of_even {e : Nat} (he : e % 2 = 0) : Nat.lor e 1 = e + 1 := by
  have h2 : e = 2 ^ 1 * (e / 2) := by
    have := Nat.div_add_mod e 2
    simp only [pow_one]
    omega
  rw [h2, lor_disjoint' 1 (e / 2) 1 (by norm_num)]
  omega

theorem shl1_from_val (v : alloc.vec.Vec Std.U64) :
    ∀ (d : Nat) (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      v.val.length - i.val ≤ d → carry.val ≤ 1 →
      ron.nat.shl1_from v i carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (2 * limbsToNat (v.val.drop i.val) + carry.val) := by
  have base : ∀ (i : Std.Usize) (carry : Std.U64) (out w : alloc.vec.Vec Std.U64),
      v.val.length ≤ i.val → ron.nat.shl1_from v i carry out = ok w →
      limbsToNat w.val = limbsToNat out.val + 2 ^ (64 * out.val.length) *
        (2 * limbsToNat (v.val.drop i.val) + carry.val) := by
    intro i carry out w hni h
    rw [ron.nat.shl1_from, if_pos (by scalar_tac)] at h
    rw [List.drop_eq_nil_of_le hni]
    split at h <;> rename_i hcz
    · simp only [Result.ok.injEq] at h
      subst h
      have hz : carry.val = 0 := by scalar_tac
      simp [hz]
    · simp only [push_eq_ok_iff] at h
      rw [h.2, limbsToNat_append]
      simp
  intro d
  induction d with
  | zero => intro i carry out w hd hc h; exact base i carry out w (by omega) h
  | succ d ih =>
    intro i carry out w hd hc h
    rcases Nat.lt_or_ge i.val v.val.length with hin | hin
    · rw [ron.nat.shl1_from, if_neg (by scalar_tac)] at h
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, push_eq_ok_iff, exists_eq_left',
        alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff] at h
      obtain ⟨x, hx, i2, hi2, out1, ⟨-, hout1⟩, i4, hi4, i5, hi5, h⟩ := h
      have hx' : x = v.val[i.val] := by
        rw [List.getElem?_eq_getElem hin] at hx; exact (Option.some.injEq _ _ ▸ hx).symm
      have hi2' : i2.val = x.val * 2 ^ 1 % 2 ^ 64 := by
        have := (ushiftLeftI_val hi2).2; simpa using this
      have hi5' : i5.val = x.val / 2 ^ (64 - 1) := by
        have := (ushiftRightI_val hi5).2; simpa using this
      have hi4' : i4.val = i.val + 1 := by have := uadd_val hi4; simpa using this
      obtain ⟨hword, hib⟩ :=
        shl_word (x := x.val) (carry := carry.val) (bits := 1) (by omega) (by scalar_tac)
          (by simpa using hc)
      have hIH := ih i4 i5 out1 w (by omega) (by rw [hi5']; simpa using hib) h
      rw [hout1, hi4'] at hIH
      simp only [List.length_append, List.length_cons, List.length_nil, limbsToNat_append,
        limbsToNat_cons, limbsToNat_nil, Nat.mul_zero, Nat.add_zero] at hIH
      rw [show 64 * (out.val.length + (0 + 1)) = 64 * out.val.length + 64 by omega,
        Nat.pow_add] at hIH
      rw [List.drop_eq_getElem_cons hin, limbsToNat_cons, ← hx']
      have hlov : (i2 ||| carry).val = Nat.lor i2.val carry.val := by
        simp only [Std.UScalar.val_or, nat_lor_eq]
      have hw2 : (i2 ||| carry).val + 2 ^ 64 * i5.val = 2 * x.val + carry.val := by
        rw [hlov, hi2', hi5']
        simpa using hword
      exact shl_step_arith _ _ _ _ _ _ _ _ _ _ hIH hw2
    · exact base i carry out w hin h

theorem shl1_or_refines {a c : ron.nat.Nat} {bit : Std.U64} (hbit : bit.val ≤ 1)
    (h : ron.nat.shl1_or a bit = ok c) : toNat c = 2 * toNat a + bit.val ∧ NatWF c := by
  rw [ron.nat.shl1_or] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hsf := shl1_from_val a.limbs a.limbs.val.length 0#usize bit
    (alloc.vec.Vec.new Std.U64) v (by omega) hbit hv
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  rw [h0] at hsf
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, limbsToNat_nil, List.length_nil,
    Nat.mul_zero, pow_zero, Nat.one_mul, Nat.zero_add, List.drop_zero] at hsf
  obtain ⟨hnv, hwf⟩ := norm_refines h
  exact ⟨by rw [hnv, hsf]; rfl, hwf⟩

theorem dm_bits_val (a b : ron.nat.Nat) (i : Std.Usize) (x : Std.U64)
    (hx : a.limbs.val[i.val]? = some x) (hbw : NatWF b) (hb : 0 < toNat b) :
    ∀ (d : Nat) (j qacc : Std.U64) (rem : ron.nat.Nat) (ql : Std.U64) (r : ron.nat.Nat),
      j.val ≤ d → NatWF rem → toNat rem < toNat b →
      ron.nat.dm_bits a b i j qacc rem = ok (ql, r) →
      ql.val = (qacc.val * 2 ^ j.val
          + (toNat rem * 2 ^ j.val + x.val % 2 ^ j.val) / toNat b) % 2 ^ 64 ∧
        toNat r = (toNat rem * 2 ^ j.val + x.val % 2 ^ j.val) % toNat b ∧ NatWF r := by
  have base : ∀ (qacc : Std.U64) (rem : ron.nat.Nat) (ql : Std.U64) (r : ron.nat.Nat)
      (j : Std.U64), j.val = 0 → NatWF rem → toNat rem < toNat b →
      ron.nat.dm_bits a b i j qacc rem = ok (ql, r) →
      ql.val = (qacc.val * 2 ^ j.val
          + (toNat rem * 2 ^ j.val + x.val % 2 ^ j.val) / toNat b) % 2 ^ 64 ∧
        toNat r = (toNat rem * 2 ^ j.val + x.val % 2 ^ j.val) % toNat b ∧ NatWF r := by
    intro qacc rem ql r j hj hrw hrb h
    rw [ron.nat.dm_bits, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [hj]
    refine ⟨?_, ?_, hrw⟩
    · simp only [pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero,
        Nat.div_eq_of_lt hrb]
      have : qacc.val < 2 ^ 64 := by scalar_tac
      omega
    · simp only [pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero]
      exact (Nat.mod_eq_of_lt hrb).symm
  intro d
  induction d with
  | zero =>
    intro j qacc rem ql r hd hrw hrb h
    exact base qacc rem ql r j (by omega) hrw hrb h
  | succ d ih =>
    intro j qacc rem ql r hd hrw hrb h
    rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
    · exact base qacc rem ql r j hj0 hrw hrb h
    rw [ron.nat.dm_bits, if_neg (by scalar_tac)] at h
    simp only [bind_eq_ok_iff, lift_eq_ok_iff, exists_eq_left',
      alloc.vec.Vec.index_slice_index, index_usize_eq_ok_iff] at h
    obtain ⟨i1, hi1, i2, hi2, i3, hi3, r1, hr1, cc, hcc, h⟩ := h
    have hi1x : i1 = x := by
      rw [hx] at hi1; exact (Option.some.injEq _ _ ▸ hi1).symm
    have hi2' : i2.val = j.val - 1 := (usub_val hi2).2.trans (by simp)
    have hi3' : i3.val = x.val / 2 ^ (j.val - 1) := by
      have := (ushiftRight_val hi3).2; rw [hi2', hi1x] at this; exact this
    set m := j.val - 1 with hm
    have hjm : j.val = m + 1 := by omega
    have hbitv : (i3 &&& 1#u64 : Std.U64).val = x.val / 2 ^ m % 2 := by
      simp only [Std.UScalar.val_and]
      rw [show (1#u64 : Std.U64).val = 1 from rfl, Nat.and_one_is_mod, hi3']
    have hbitb : (i3 &&& 1#u64 : Std.U64).val ≤ 1 := by rw [hbitv]; omega
    obtain ⟨hr1v, hr1w⟩ := shl1_or_refines hbitb hr1
    rw [hbitv] at hr1v
    -- the window value, split at bit `m`
    have hV : toNat rem * 2 ^ j.val + x.val % 2 ^ j.val
        = toNat r1 * 2 ^ m + x.val % 2 ^ m := by
      rw [hjm, mod_two_pow_succ, hr1v, Nat.pow_succ]
      ring
    have hqacc : ∀ (q2 : Std.U64) (Z : Nat), q2.val = qacc.val * 2 % 2 ^ 64 →
        (q2.val * 2 ^ m + Z) % 2 ^ 64 = (qacc.val * 2 ^ j.val + Z) % 2 ^ 64 := by
      intro q2 Z hq2
      rw [hq2, hjm,
        show qacc.val * 2 ^ (m + 1) = qacc.val * 2 * 2 ^ m by rw [Nat.pow_succ]; ring]
      exact (Nat.ModEq.add_right Z
        (Nat.ModEq.mul_right (2 ^ m) (Nat.mod_modEq (qacc.val * 2) (2 ^ 64))))
    have hqacc1 : ∀ (q2 : Std.U64) (Z : Nat), q2.val = qacc.val * 2 % 2 ^ 64 + 1 →
        ((q2.val * 2 ^ m + Z) % 2 ^ 64) = (qacc.val * 2 ^ j.val + (Z + 2 ^ m)) % 2 ^ 64 := by
      intro q2 Z hq2
      rw [hq2, hjm,
        show qacc.val * 2 ^ (m + 1) + (Z + 2 ^ m) = qacc.val * 2 * 2 ^ m + 2 ^ m + Z by
          rw [Nat.pow_succ]; ring,
        show (qacc.val * 2 % 2 ^ 64 + 1) * 2 ^ m + Z
            = qacc.val * 2 % 2 ^ 64 * 2 ^ m + 2 ^ m + Z by ring]
      exact (Nat.ModEq.add_right Z (Nat.ModEq.add_right (2 ^ m)
        (Nat.ModEq.mul_right (2 ^ m) (Nat.mod_modEq (qacc.val * 2) (2 ^ 64)))))
    rcases cmp_refines hr1w hbw hcc with ⟨rfl, hlt⟩ | ⟨rfl, heq⟩ | ⟨rfl, hgt⟩
    · -- no subtraction
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i4, hi4, h⟩ := h
      have hi4' : i4.val = qacc.val * 2 % 2 ^ 64 := by
        have := (ushiftLeftI_val hi4).2; simpa using this
      obtain ⟨h1, h2, h3⟩ := ih i2 i4 r1 ql r (by omega) hr1w hlt h
      rw [hi2'] at h1 h2
      refine ⟨?_, ?_, h3⟩
      · rw [h1, hV]; exact hqacc i4 _ hi4'
      · rw [h2, hV]
    · -- `r1 = b`: subtract, quotient bit 1
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, exists_eq_left'] at h
      obtain ⟨r2, hr2, i4, hi4, h⟩ := h
      obtain ⟨hr2v, hr2w⟩ := sub_refines hr1w hbw hr2
      have hi4' : i4.val = qacc.val * 2 % 2 ^ 64 := by
        have := (ushiftLeftI_val hi4).2; simpa using this
      have hev : i4.val % 2 = 0 := by
        rw [hi4', Nat.mod_mod_of_dvd _ (by norm_num : (2 : Nat) ∣ 2 ^ 64)]
        omega
      have hi5' : (i4 ||| 1#u64 : Std.U64).val = qacc.val * 2 % 2 ^ 64 + 1 := by
        simp only [Std.UScalar.val_or]
        rw [show (1#u64 : Std.U64).val = 1 from rfl, ← nat_lor_eq, lor_one_of_even hev, hi4']
      have hr2lt : toNat r2 < toNat b := by rw [hr2v]; omega
      obtain ⟨h1, h2, h3⟩ := ih i2 (i4 ||| 1#u64) r2 ql r (by omega) hr2w hr2lt h
      rw [hi2'] at h1 h2
      have hsplit : toNat r1 * 2 ^ m + x.val % 2 ^ m
          = toNat r2 * 2 ^ m + x.val % 2 ^ m + toNat b * 2 ^ m := by
        have hd2 : toNat r1 = toNat r2 + toNat b := by omega
        rw [hd2]
        ring
      refine ⟨?_, ?_, h3⟩
      · rw [h1, hV, hsplit, Nat.add_mul_div_left _ _ hb]
        exact hqacc1 (i4 ||| 1#u64) _ hi5'
      · rw [h2, hV, hsplit, Nat.add_mul_mod_self_left]
    · -- `r1 > b`: same branch body
      simp only [bind_eq_ok_iff, lift_eq_ok_iff, exists_eq_left'] at h
      obtain ⟨r2, hr2, i4, hi4, h⟩ := h
      obtain ⟨hr2v, hr2w⟩ := sub_refines hr1w hbw hr2
      have hi4' : i4.val = qacc.val * 2 % 2 ^ 64 := by
        have := (ushiftLeftI_val hi4).2; simpa using this
      have hev : i4.val % 2 = 0 := by
        rw [hi4', Nat.mod_mod_of_dvd _ (by norm_num : (2 : Nat) ∣ 2 ^ 64)]
        omega
      have hi5' : (i4 ||| 1#u64 : Std.U64).val = qacc.val * 2 % 2 ^ 64 + 1 := by
        simp only [Std.UScalar.val_or]
        rw [show (1#u64 : Std.U64).val = 1 from rfl, ← nat_lor_eq, lor_one_of_even hev, hi4']
      have hr1b : toNat r1 < 2 * toNat b := by rw [hr1v]; omega
      have hr2lt : toNat r2 < toNat b := by rw [hr2v]; omega
      obtain ⟨h1, h2, h3⟩ := ih i2 (i4 ||| 1#u64) r2 ql r (by omega) hr2w hr2lt h
      rw [hi2'] at h1 h2
      have hsplit : toNat r1 * 2 ^ m + x.val % 2 ^ m
          = toNat r2 * 2 ^ m + x.val % 2 ^ m + toNat b * 2 ^ m := by
        have hd2 : toNat r1 = toNat r2 + toNat b := by omega
        rw [hd2]
        ring
      refine ⟨?_, ?_, h3⟩
      · rw [h1, hV, hsplit, Nat.add_mul_div_left _ _ hb]
        exact hqacc1 (i4 ||| 1#u64) _ hi5'
      · rw [h2, hV, hsplit, Nat.add_mul_mod_self_left]

theorem rev_copy_from_val (v : alloc.vec.Vec Std.U64) :
    ∀ (d : Nat) (k : Std.Usize) (out w : alloc.vec.Vec Std.U64),
      k.val ≤ d → k.val ≤ v.val.length → ron.nat.rev_copy_from v k out = ok w →
      w.val = out.val ++ (v.val.take k.val).reverse := by
  intro d
  induction d with
  | zero =>
    intro k out w hd hk h
    rw [ron.nat.rev_copy_from, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    have hz : k.val = 0 := by omega
    simp [hz]
  | succ d ih =>
    intro k out w hd hk h
    rw [ron.nat.rev_copy_from] at h
    split at h <;> rename_i hk0
    · simp only [Result.ok.injEq] at h
      subst h
      have hz : k.val = 0 := by scalar_tac
      simp [hz]
    · have hk0' : 0 < k.val := by scalar_tac
      simp only [] at h
      split at h <;> rename_i hkv
      · have : v.val.length < k.val := by scalar_tac
        omega
      · simp only [bind_eq_ok_iff, push_eq_ok_iff, alloc.vec.Vec.index_slice_index,
          index_usize_eq_ok_iff] at h
        obtain ⟨i1, hi1, y, hy, out1, ⟨-, hout1⟩, h⟩ := h
        have hi1' : i1.val = k.val - 1 := (usub_val hi1).2.trans (by simp)
        have hlt : i1.val < v.val.length := by omega
        obtain ⟨n, hkn⟩ : ∃ n, k.val = n + 1 := ⟨k.val - 1, by omega⟩
        have hi1n : i1.val = n := by omega
        have hn : n < v.val.length := by omega
        have hy' : y = v.val[n] := by
          rw [hi1n, List.getElem?_eq_getElem hn] at hy
          exact (Option.some.injEq _ _ ▸ hy).symm
        rw [ih i1 out1 w (by omega) (by omega) h, hout1, hi1n, hy', hkn]
        rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some,
          List.reverse_append, List.reverse_singleton, List.singleton_append]
        simp

theorem dm_limbs_val (a b : ron.nat.Nat) (hbw : NatWF b) (hb : 0 < toNat b) :
    ∀ (d : Nat) (i : Std.Usize) (qrev qrev' : alloc.vec.Vec Std.U64)
      (rem rem' : ron.nat.Nat),
      i.val ≤ d → i.val ≤ a.limbs.val.length → NatWF rem → toNat rem < toNat b →
      toNat rem = toNat a / 2 ^ (64 * i.val) % toNat b →
      ron.nat.dm_limbs a b i qrev rem = ok (qrev', rem') →
      (∃ l : List Std.U64, qrev'.val = qrev.val ++ l ∧ l.length = i.val ∧
        limbsToNat l.reverse = toNat a / toNat b % 2 ^ (64 * i.val)) ∧
      toNat rem' = toNat a % toNat b ∧ NatWF rem' := by
  have base : ∀ (i : Std.Usize) (qrev qrev' : alloc.vec.Vec Std.U64)
      (rem rem' : ron.nat.Nat), i.val = 0 → NatWF rem →
      toNat rem = toNat a / 2 ^ (64 * i.val) % toNat b →
      ron.nat.dm_limbs a b i qrev rem = ok (qrev', rem') →
      (∃ l : List Std.U64, qrev'.val = qrev.val ++ l ∧ l.length = i.val ∧
        limbsToNat l.reverse = toNat a / toNat b % 2 ^ (64 * i.val)) ∧
      toNat rem' = toNat a % toNat b ∧ NatWF rem' := by
    intro i qrev qrev' rem rem' hi0 hrw hrv h
    rw [ron.nat.dm_limbs, if_pos (by scalar_tac)] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [hi0] at hrv ⊢
    refine ⟨⟨[], by simp, by simp,
      by simp only [List.reverse_nil, limbsToNat_nil, Nat.mul_zero, pow_zero, Nat.mod_one]⟩,
      ?_, hrw⟩
    rw [hrv]
    simp
  intro d
  induction d with
  | zero =>
    intro i qrev qrev' rem rem' hd hil hrw hrb hrv h
    exact base i qrev qrev' rem rem' (by omega) hrw hrv h
  | succ d ih =>
    intro i qrev qrev' rem rem' hd hil hrw hrb hrv h
    rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
    · exact base i qrev qrev' rem rem' hi0 hrw hrv h
    rw [ron.nat.dm_limbs, if_neg (by scalar_tac)] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, h⟩ := h
    have hi1' : i1.val = i.val - 1 := (usub_val hi1).2.trans (by simp)
    have hlt : i1.val < a.limbs.val.length := by omega
    obtain ⟨p, hp, h⟩ := h
    obtain ⟨ql, rem2⟩ := p
    replace h : (do let qrev1 ← alloc.vec.Vec.push qrev ql
                    ron.nat.dm_limbs a b i1 qrev1 rem2) = ok (qrev', rem') := h
    obtain ⟨x, hx⟩ : ∃ x, a.limbs.val[i1.val]? = some x :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hxe : a.limbs.val[i1.val] = x := by
      rw [List.getElem?_eq_getElem hlt] at hx; exact Option.some.injEq _ _ ▸ hx
    have hAi1 : toNat a / 2 ^ (64 * i1.val)
        = x.val + 2 ^ 64 * (toNat a / 2 ^ (64 * i.val)) := by
      simp only [toNat]
      rw [← limbsToNat_drop, ← limbsToNat_drop, List.drop_eq_getElem_cons hlt,
        limbsToNat_cons, hxe, show i1.val + 1 = i.val by omega]
    obtain ⟨hql, hrem2, hrem2w⟩ :=
      dm_bits_val a b i1 x hx hbw hb 64 64#u64 0#u64 rem ql rem2 (by scalar_tac) hrw hrb hp
    have h64 : (64#u64 : Std.U64).val = 64 := by scalar_tac
    have h0 : (0#u64 : Std.U64).val = 0 := by scalar_tac
    rw [h64, Nat.mod_eq_of_lt (by scalar_tac : x.val < 2 ^ 64)] at hql hrem2
    rw [h0] at hql
    simp only [Nat.zero_mul, Nat.zero_add] at hql
    have hAdecomp : toNat a / 2 ^ (64 * i1.val)
        = (2 ^ 64 * toNat rem + x.val)
            + toNat b * (2 ^ 64 * (toNat a / 2 ^ (64 * i.val) / toNat b)) := by
      rw [hAi1, hrv]
      have hdm := Nat.div_add_mod (toNat a / 2 ^ (64 * i.val)) (toNat b)
      calc x.val + 2 ^ 64 * (toNat a / 2 ^ (64 * i.val))
          = x.val + 2 ^ 64 * (toNat b * (toNat a / 2 ^ (64 * i.val) / toNat b)
              + toNat a / 2 ^ (64 * i.val) % toNat b) := by rw [hdm]
        _ = _ := by ring
    have hrem2' : toNat rem2 = toNat a / 2 ^ (64 * i1.val) % toNat b := by
      rw [hrem2, hAdecomp, Nat.add_mul_mod_self_left]
      congr 1
      ring
    rw [show toNat rem * 2 ^ 64 = 2 ^ 64 * toNat rem from Nat.mul_comm _ _] at hql
    have hqlv : ql.val = toNat a / toNat b / 2 ^ (64 * i1.val) % 2 ^ 64 := by
      have hB : toNat a / toNat b / 2 ^ (64 * i1.val)
          = (2 ^ 64 * toNat rem + x.val) / toNat b
              + 2 ^ 64 * (toNat a / 2 ^ (64 * i.val) / toNat b) := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm (toNat b), ← Nat.div_div_eq_div_mul,
          hAdecomp, Nat.add_mul_div_left _ _ hb]
      rw [hql, hB, Nat.add_mul_mod_self_left]
    simp only [bind_eq_ok_iff, push_eq_ok_iff] at h
    obtain ⟨qrev1, ⟨-, hqrev1⟩, h⟩ := h
    obtain ⟨⟨l, hl1, hl2, hl3⟩, hrem', hrem'w⟩ :=
      ih i1 qrev1 qrev' rem2 rem' (by omega) (by omega) hrem2w
        (by rw [hrem2']; exact Nat.mod_lt _ hb) hrem2' h
    refine ⟨⟨ql :: l, ?_, ?_, ?_⟩, hrem', hrem'w⟩
    · rw [hl1, hqrev1]; simp
    · simp only [List.length_cons, hl2]; omega
    · rw [List.reverse_cons, limbsToNat_append, hl3, List.length_reverse, hl2,
        limbsToNat_cons, limbsToNat_nil]
      rw [show 64 * i.val = 64 * i1.val + 64 by omega, Nat.pow_add, Nat.mod_mul, hqlv]
      ring

theorem div_mod_refines {a b q r : ron.nat.Nat} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.div_mod a b = ok (q, r)) :
    toNat q = toNat a / toNat b ∧ toNat r = toNat a % toNat b ∧ NatWF q ∧ NatWF r := by
  rw [ron.nat.div_mod] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b1, hb1, h⟩ := h
  rw [ron.nat.is_zero] at hb1
  simp only [Result.ok.injEq] at hb1
  split at h <;> rename_i hbz
  · rw [hbz] at hb1
    have hbn : b.limbs.val = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      have h0 : alloc.vec.Vec.len b.limbs = 0#usize := by simpa using hb1
      scalar_tac
    have hb0 : toNat b = 0 := by simp [toNat, hbn]
    simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨z, hz, ac, hac, h1, h2⟩ := h
    subst h1; subst h2
    obtain ⟨hz0, hzwf⟩ := zero_refines hz
    obtain ⟨hacl, hacv⟩ := clone_refines hac
    exact ⟨by rw [hz0, hb0]; simp, by rw [hacv, hb0]; simp, hzwf,
      by simp only [NatWF, hacl]; exact ha⟩
  · have hbne : b.limbs.val ≠ [] := by
      intro hc
      apply hbz
      rw [← hb1]
      have hz : alloc.vec.Vec.len b.limbs = 0#usize := by
        have hl0 : b.limbs.val.length = 0 := by rw [hc]; rfl
        scalar_tac
      simp [hz]
    have hb0 : 0 < toNat b := by
      have hge := limbsToNat_ge hb hbne
      have hp : 0 < 2 ^ (64 * (b.limbs.val.length - 1)) := Nat.two_pow_pos _
      simp only [toNat]
      omega
    simp only [bind_eq_ok_iff] at h
    obtain ⟨z, hz, h⟩ := h
    obtain ⟨hz0, hzwf⟩ := zero_refines hz
    obtain ⟨p, hp, h⟩ := h
    obtain ⟨qrev, rr⟩ := p
    replace h : (do let v ← ron.nat.rev_copy_from qrev (alloc.vec.Vec.len qrev)
                      (alloc.vec.Vec.new Std.U64)
                    let n ← ron.nat.norm v
                    ok (n, rr)) = ok (q, r) := h
    have hazero : toNat a / 2 ^ (64 * a.limbs.val.length) = 0 :=
      Nat.div_eq_of_lt (limbsToNat_lt _)
    have hlen : (alloc.vec.Vec.len a.limbs).val = a.limbs.val.length := by scalar_tac
    obtain ⟨⟨l, hl1, hl2, hl3⟩, hrr, hrrw⟩ :=
      dm_limbs_val a b hb hb0 a.limbs.val.length (alloc.vec.Vec.len a.limbs)
        (alloc.vec.Vec.new Std.U64) qrev z rr (by omega) (by omega) hzwf
        (by rw [hz0]; exact hb0) (by rw [hz0, hlen, hazero]; simp) hp
    rw [hlen] at hl2 hl3
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] at hl1
    have hQ : toNat a / toNat b % 2 ^ (64 * a.limbs.val.length) = toNat a / toNat b :=
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (limbsToNat_lt _))
    rw [hQ] at hl3
    simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨v, hv, n, hn, h1, h2⟩ := h
    subst h1; subst h2
    have hkl : (alloc.vec.Vec.len qrev).val = qrev.val.length := by scalar_tac
    have hrc := rev_copy_from_val qrev qrev.val.length (alloc.vec.Vec.len qrev)
      (alloc.vec.Vec.new Std.U64) v (by omega) (by omega) hv
    rw [hkl, List.take_of_length_le le_rfl] at hrc
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] at hrc
    obtain ⟨hnv, hnwf⟩ := norm_refines hn
    refine ⟨?_, hrr, hnwf, hrrw⟩
    rw [hnv, hrc, hl1, hl3]

theorem div_refines {a b c : ron.nat.Nat} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.div a b = ok c) : toNat c = toNat a / toNat b ∧ NatWF c := by
  rw [ron.nat.div] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q, r⟩ := p
  replace h : (ok q : Result ron.nat.Nat) = ok c := h
  simp only [Result.ok.injEq] at h
  subst h
  obtain ⟨h1, -, h3, -⟩ := div_mod_refines ha hb hp
  exact ⟨h1, h3⟩

theorem modulo_refines {a b c : ron.nat.Nat} (ha : NatWF a) (hb : NatWF b)
    (h : ron.nat.modulo a b = ok c) : toNat c = toNat a % toNat b ∧ NatWF c := by
  rw [ron.nat.modulo] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨q, r⟩ := p
  replace h : (ok r : Result ron.nat.Nat) = ok c := h
  simp only [Result.ok.injEq] at h
  subst h
  obtain ⟨-, h2, -, h4⟩ := div_mod_refines ha hb hp
  exact ⟨h2, h4⟩

theorem gcd_refines : ∀ (N : Nat) (a b c : ron.nat.Nat), toNat a = N → NatWF a → NatWF b →
    ron.nat.gcd a b = ok c → toNat c = Nat.gcd (toNat a) (toNat b) ∧ NatWF c := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro a b c hN ha hb h
    rw [ron.nat.gcd] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    rw [ron.nat.is_zero] at hb1
    simp only [Result.ok.injEq] at hb1
    split at h <;> rename_i hbz
    · rw [hbz] at hb1
      have han : a.limbs.val = [] := by
        refine List.eq_nil_of_length_eq_zero ?_
        have h0 : alloc.vec.Vec.len a.limbs = 0#usize := by simpa using hb1
        scalar_tac
      have ha0 : toNat a = 0 := by simp [toNat, han]
      obtain ⟨hcl, hcv⟩ := clone_refines h
      refine ⟨?_, by simp only [NatWF, hcl]; exact hb⟩
      rw [hcv, ha0, Nat.gcd_zero_left]
    · have hane : a.limbs.val ≠ [] := by
        intro hc
        apply hbz
        rw [← hb1]
        have hz : alloc.vec.Vec.len a.limbs = 0#usize := by
          have hl0 : a.limbs.val.length = 0 := by rw [hc]; rfl
          scalar_tac
        simp [hz]
      have ha0 : 0 < toNat a := by
        have hge := limbsToNat_ge ha hane
        have hp : 0 < 2 ^ (64 * (a.limbs.val.length - 1)) := Nat.two_pow_pos _
        simp only [toNat]
        omega
      simp only [bind_eq_ok_iff] at h
      obtain ⟨m, hm, h⟩ := h
      obtain ⟨hmv, hmw⟩ := modulo_refines hb ha hm
      obtain ⟨hcv, hcw⟩ := ihN (toNat m) (by rw [hmv, ← hN]; exact Nat.mod_lt _ ha0)
        m a c rfl hmw ha h
      refine ⟨?_, hcw⟩
      rw [hcv, hmv, ← Nat.gcd_rec]

/-! ## Axiom census

Committed gate (task #5's convention): the three representative operations
depend on nothing beyond Lean's three classical axioms — no `sorry`, nothing
from Aeneas's library, nothing from the hand-written `Arc` model. -/

/-- info: 'ConRon.Refine.Nat.add_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms add_refines

/-- info: 'ConRon.Refine.Nat.div_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms div_refines

/-- info: 'ConRon.Refine.Nat.land_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms land_refines

end ConRon.Refine.Nat
