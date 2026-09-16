import LiouvilleGoldbach.Completion
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp

namespace LiouvilleGoldbach

def doubleDefect (p : ℕ) (f : ℕ → ℤ) (x : ZMod p) : ℤ :=
  oddCompletion p f (-2 * x) - oddCompletion p f x

def tripleDefect (p : ℕ) (f : ℕ → ℤ) (x : ZMod p) : ℤ :=
  oddCompletion p f (-3 * x) - oddCompletion p f x

variable {p : ℕ} {f : ℕ → ℤ}

theorem doubleDefect_zero : doubleDefect p f 0 = 0 := by simp [doubleDefect]
theorem tripleDefect_zero : tripleDefect p f 0 = 0 := by simp [tripleDefect]

theorem doubleDefect_neg (hp2 : p % 2 = 1) (x : ZMod p) :
    doubleDefect p f (-x) = -doubleDefect p f x := by
  simp only [doubleDefect, mul_neg, oddCompletion_neg hp2]
  ring

theorem tripleDefect_neg (hp2 : p % 2 = 1) (x : ZMod p) :
    tripleDefect p f (-x) = -tripleDefect p f x := by
  simp only [tripleDefect, mul_neg, oddCompletion_neg hp2]
  ring

/-- The two multiplicative transports commute. -/
theorem defect_commuting_square (x : ZMod p) :
    doubleDefect p f (-3 * x) + tripleDefect p f x =
      tripleDefect p f (-2 * x) + doubleDefect p f x := by
  simp only [doubleDefect, tripleDefect]
  have he : (-2 : ZMod p) * (-3 * x) = -3 * (-2 * x) := by ring
  rw [he]
  ring

namespace IntervalSigns

variable (H : IntervalSigns p f)
include H

theorem doubleDefect_small (hp2 : p % 2 = 1) {n : ℕ}
    (hn : 0 < n) (hhi : 4 * n < p) : doubleDefect p f n = 0 := by
  have he : (-2 : ZMod p) * n = -((2 * n : ℕ) : ZMod p) := by push_cast; ring
  rw [doubleDefect, he, oddCompletion_neg hp2,
    oddCompletion_nat (by omega) (by omega), oddCompletion_nat hn (by omega),
    H.two n hn (by omega)]
  ring

omit H in
theorem doubleDefect_wrap {n : ℕ} (hlo : p < 4 * n) (hhi : 2 * n < p) :
    doubleDefect p f n = f (p - 2 * n) - f n := by
  have he : (-2 : ZMod p) * n = ((p - 2 * n : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]
    push_cast
    ring
  rw [doubleDefect, he, oddCompletion_nat (by omega) (by omega),
    oddCompletion_nat (by omega) hhi]

theorem doubleDefect_nonneg (hp2 : p % 2 = 1) {n : ℕ}
    (hn : 0 < n) (hhi : 2 * n < p) : 0 ≤ doubleDefect p f n := by
  by_cases hs : 4 * n < p
  · rw [H.doubleDefect_small hp2 hn hs]
  · rw [doubleDefect_wrap (by omega) hhi]
    have h := H.doubleReflection hn hhi
    omega

theorem doubleDefect_upper {n : ℕ} (hlo : p < 3 * n) (hhi : 2 * n < p) :
    doubleDefect p f n = 0 := by
  rw [doubleDefect_wrap (by omega) hhi, (H.upperBand hlo hhi).1]
  omega

theorem doubleDefect_support (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) (hd : 0 < doubleDefect p f n) :
    p < 4 * n ∧ 3 * n < p := by
  constructor
  · by_contra h
    have hs : 4 * n < p := by omega
    rw [H.doubleDefect_small hp2 hn hs] at hd
    omega
  · by_contra h
    have hs : p < 3 * n := by omega
    rw [H.doubleDefect_upper hs hhi] at hd
    omega

theorem tripleDefect_small (hp2 : p % 2 = 1) {n : ℕ}
    (hn : 0 < n) (hhi : 6 * n < p) : tripleDefect p f n = 0 := by
  have he : (-3 : ZMod p) * n = -((3 * n : ℕ) : ZMod p) := by push_cast; ring
  rw [tripleDefect, he, oddCompletion_neg hp2,
    oddCompletion_nat (by omega) (by omega), oddCompletion_nat hn (by omega),
    H.three n hn (by omega)]
  ring

omit H in
theorem tripleDefect_middle {n : ℕ} (hlo : p < 6 * n) (hhi : 3 * n < p) :
    tripleDefect p f n = f (p - 3 * n) - f n := by
  have he : (-3 : ZMod p) * n = ((p - 3 * n : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : 3 * n ≤ p), ZMod.natCast_self]
    push_cast
    ring
  rw [tripleDefect, he, oddCompletion_nat (by omega) (by omega),
    oddCompletion_nat (by omega) (by omega)]

theorem tripleDefect_upper (hp2 : p % 2 = 1) {n : ℕ}
    (hlo : p < 3 * n) (hhi : 2 * n < p) : tripleDefect p f n = 0 := by
  have he : (-3 : ZMod p) * n = -((3 * n - p : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : p ≤ 3 * n), ZMod.natCast_self]
    push_cast
    ring
  rw [tripleDefect, he, oddCompletion_neg hp2,
    oddCompletion_nat (by omega) (by omega), oddCompletion_nat (by omega) hhi]
  have h := (H.upperBand hlo hhi).2
  omega

theorem tripleDefect_nonneg (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) : 0 ≤ tripleDefect p f n := by
  by_cases hs : 6 * n < p
  · rw [H.tripleDefect_small hp2 hn hs]
  by_cases hu : p < 3 * n
  · rw [H.tripleDefect_upper hp2 hu hhi]
  have hlo : p < 6 * n := by omega
  have hupper : 3 * n < p := by omega
  rw [tripleDefect_middle hlo hupper]
  have h := H.reflection (show 0 < 3 * n by omega) hupper
  rw [H.three n hn (by omega)] at h
  omega

theorem defects_equal_quarter {n : ℕ} (hlo : p < 4 * n) (hhi : 3 * n < p) :
    doubleDefect p f n = tripleDefect p f n := by
  rw [doubleDefect_wrap hlo (by omega), tripleDefect_middle (by omega) hhi]
  have hu := (H.upperBand (n := p - 2 * n) (by omega) (by omega)).2
  have he : 3 * (p - 2 * n) - p = 2 * (p - 3 * n) := by omega
  rw [he, H.two (p - 3 * n) (by omega) (by omega)] at hu
  omega

/-- The unused part of the tripling band disappears by a commuting square. -/
theorem tripleDefect_lower_middle (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    {n : ℕ} (hlo : p < 6 * n) (hhi : 4 * n < p) : tripleDefect p f n = 0 := by
  have hsq := defect_commuting_square (f := f) (p := p) (n : ZMod p)
  have he2 : (-2 : ZMod p) * n = -((2 * n : ℕ) : ZMod p) := by push_cast; ring
  have he3 : (-3 : ZMod p) * n = ((p - 3 * n : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : 3 * n ≤ p), ZMod.natCast_self]
    push_cast
    ring
  rw [he2, tripleDefect_neg hp2, H.tripleDefect_upper hp2 (n := 2 * n) (by omega) (by omega),
    H.doubleDefect_small hp2 (by omega) hhi, he3] at hsq
  have ha := H.doubleDefect_nonneg hp2 (n := p - 3 * n) (by omega) (by omega)
  have hb := H.tripleDefect_nonneg hp2 hp3 (n := n) (by omega) (by omega)
  omega

theorem defects_equal_nat (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    doubleDefect p f n = tripleDefect p f n := by
  by_cases hu : p < 3 * n
  · rw [H.doubleDefect_upper hu hhi, H.tripleDefect_upper hp2 hu hhi]
  have hthird : 3 * n < p := by omega
  by_cases hq : p < 4 * n
  · exact H.defects_equal_quarter hq hthird
  have hquarter : 4 * n < p := by omega
  rw [H.doubleDefect_small hp2 hn hquarter]
  by_cases hs : 6 * n < p
  · rw [H.tripleDefect_small hp2 hn hs]
  · rw [H.tripleDefect_lower_middle hp2 hp3 (by omega) hquarter]

theorem defects_equal [NeZero p] (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    (x : ZMod p) : doubleDefect p f x = tripleDefect p f x := by
  by_cases hx : x = 0
  · simp [hx, doubleDefect_zero, tripleDefect_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]
    exact H.defects_equal_nat hp2 hp3 hn hhi
  · rw [h, doubleDefect_neg hp2, tripleDefect_neg hp2,
      H.defects_equal_nat hp2 hp3 hn hhi]

theorem completion_two_eq_three [NeZero p] (hp2 : p % 2 = 1)
    (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    oddCompletion p f (2 * x) = oddCompletion p f (3 * x) := by
  have h := H.defects_equal hp2 hp3 x
  simp only [doubleDefect, tripleDefect, neg_mul, oddCompletion_neg hp2] at h
  omega

theorem doubleDefect_two_eq_three [NeZero p] (hp2 : p % 2 = 1)
    (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    doubleDefect p f (2 * x) = doubleDefect p f (3 * x) := by
  have h1 := H.completion_two_eq_three hp2 hp3 x
  have h2 := H.completion_two_eq_three hp2 hp3 (-2 * x)
  have he2 : (2 : ZMod p) * (-2 * x) = -2 * (2 * x) := by ring
  have he3 : (3 : ZMod p) * (-2 * x) = -2 * (3 * x) := by ring
  rw [he2, he3] at h2
  simp only [doubleDefect]
  rw [h1, h2]

/-- An invariant positive defect cannot remain in the short quarter band. -/
theorem doubleDefect_eq_zero_nat [Fact p.Prime] (hpgt : 3 < p)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) {n : ℕ}
    (hn : 0 < n) (hhi : 2 * n < p) : doubleDefect p f n = 0 := by
  by_contra hne
  have hnonneg := H.doubleDefect_nonneg hp2 hn hhi
  have hd : 0 < doubleDefect p f n := by omega
  obtain ⟨hnlo, hnhi⟩ := H.doubleDefect_support hp2 hp3 hn hhi hd
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro he
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_ofNat, ZMod.val_zero] at hv
    rw [Nat.mod_eq_of_lt hpgt] at hv
    omega
  let z : ZMod p := (n : ZMod p) / 3
  have hz : 3 * z = (n : ZMod p) := by dsimp [z]; field_simp
  have hd23 := H.doubleDefect_two_eq_three hp2 hp3 z
  rw [hz] at hd23
  have hdy : 0 < doubleDefect p f (2 * z) := by omega
  have hy : 2 * z ≠ 0 := by
    intro he
    rw [he, doubleDefect_zero] at hdy
    omega
  obtain ⟨m, hm, hmhi, he | he⟩ := centralRepresentative hp2 hy
  · rw [he] at hdy
    obtain ⟨hmlo, hmthird⟩ := H.doubleDefect_support hp2 hp3 hm hmhi hdy
    have hc : ((3 * m : ℕ) : ZMod p) = ((2 * n : ℕ) : ZMod p) := by
      push_cast
      calc
        (3 : ZMod p) * m = 3 * (2 * z) := by rw [he]
        _ = 2 * (3 * z) := by ring
        _ = 2 * (n : ZMod p) := by rw [hz]
    have hv := congrArg ZMod.val hc
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt hmthird, Nat.mod_eq_of_lt hhi] at hv
    omega
  · rw [he, doubleDefect_neg hp2] at hdy
    have hnm := H.doubleDefect_nonneg hp2 hm hmhi
    omega

theorem doubleDefect_eq_zero [Fact p.Prime] (hpgt : 3 < p)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    doubleDefect p f x = 0 := by
  by_cases hx : x = 0
  · simp [hx, doubleDefect_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]
    exact H.doubleDefect_eq_zero_nat hpgt hp2 hp3 hn hhi
  · rw [h, doubleDefect_neg hp2, H.doubleDefect_eq_zero_nat hpgt hp2 hp3 hn hhi]
    omega

/-- Exact doubling, obtained without division into residue classes modulo three. -/
theorem commuting_completion_two [Fact p.Prime] (hpgt : 3 < p)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    oddCompletion p f (2 * x) = -oddCompletion p f x := by
  have h := H.doubleDefect_eq_zero hpgt hp2 hp3 x
  simp only [doubleDefect, neg_mul, oddCompletion_neg hp2] at h
  omega

/-- Exact tripling follows simultaneously from the same commuting square. -/
theorem commuting_completion_three [Fact p.Prime] (hpgt : 3 < p)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    oddCompletion p f (3 * x) = -oddCompletion p f x := by
  have h := (H.defects_equal hp2 hp3 x).symm.trans (H.doubleDefect_eq_zero hpgt hp2 hp3 x)
  simp only [tripleDefect, neg_mul, oddCompletion_neg hp2] at h
  omega

end IntervalSigns
end LiouvilleGoldbach
