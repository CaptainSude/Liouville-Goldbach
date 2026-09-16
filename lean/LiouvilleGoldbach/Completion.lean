import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace LiouvilleGoldbach

/-- The local sign information used by the interval part of the argument. -/
structure IntervalSigns (p : ℕ) (f : ℕ → ℤ) : Prop where
  sign : ∀ n, 0 < n → n < 2 * p → f n = 1 ∨ f n = -1
  two : ∀ n, 0 < n → n < p → f (2 * n) = - f n
  three : ∀ n, 0 < n → 3 * n < 2 * p → f (3 * n) = - f n
  noPP : ∀ a b, 0 < a → 0 < b → a + b = 2 * p → ¬ (f a = 1 ∧ f b = 1)

namespace IntervalSigns

variable {p : ℕ} {f : ℕ → ℤ} (H : IntervalSigns p f)
include H

theorem noNN {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = p) :
    ¬ (f a = -1 ∧ f b = -1) := by
  intro h
  have h2a := H.two a ha (by omega)
  have h2b := H.two b hb (by omega)
  exact H.noPP (2 * a) (2 * b) (by omega) (by omega) (by omega)
    ⟨by omega, by omega⟩

theorem reflection {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    -f n ≤ f (p - n) := by
  have h := H.noNN hn (show 0 < p - n by omega) (show n + (p - n) = p by omega)
  rcases H.sign n hn (by omega) with h1 | h1 <;>
    rcases H.sign (p - n) (by omega) (by omega) with h2 | h2 <;> omega

theorem translation {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    f (p + n) ≤ f n := by
  have hr := H.reflection hn hnp
  have h := H.noPP (p - n) (p + n) (by omega) (by omega) (by omega)
  rcases H.sign n hn (by omega) with h1 | h1 <;>
    rcases H.sign (p + n) (by omega) (by omega) with h2 | h2 <;>
    rcases H.sign (p - n) (by omega) (by omega) with h3 | h3 <;> omega

theorem four {n : ℕ} (hn : 0 < n) (hnp : 2 * n < p) : f (4 * n) = f n := by
  have h1 := H.two n hn (by omega)
  have h2 := H.two (2 * n) (by omega) hnp
  have he : 2 * (2 * n) = 4 * n := by omega
  rw [he] at h2
  omega

theorem eight {n : ℕ} (hn : 0 < n) (hnp : 4 * n < p) : f (8 * n) = -f n := by
  have h1 := H.four hn (show 2 * n < p by omega)
  have h2 := H.two (4 * n) (by omega) hnp
  have he : 2 * (4 * n) = 8 * n := by omega
  rw [he] at h2
  omega

theorem doubleReflection {n : ℕ} (hn : 0 < n) (hnp : 2 * n < p) :
    f n ≤ f (p - 2 * n) := by
  have hf := H.four hn hnp
  have ht := H.two (p - 2 * n) (by omega) (by omega)
  have h := H.noPP (4 * n) (2 * (p - 2 * n)) (by omega) (by omega) (by omega)
  rcases H.sign n hn (by omega) with h1 | h1 <;>
    rcases H.sign (p - 2 * n) (by omega) (by omega) with h2 | h2 <;> omega

theorem reflectNegative {n : ℕ} (hn : 0 < n) (hnp : n < p) (hs : f n = -1) :
    f (p - n) = 1 := by
  have h := H.reflection hn hnp
  rcases H.sign (p - n) (by omega) (by omega) with h1 | h1 <;> omega

theorem reflectPositive {n : ℕ} (hn : 0 < n) (hnp : n < 2 * p) (hs : f n = 1) :
    f (2 * p - n) = -1 := by
  have h := H.noPP n (2 * p - n) hn (by omega) (by omega)
  rcases H.sign (2 * p - n) (by omega) (by omega) with h1 | h1 <;> omega

theorem translateNegative {n : ℕ} (hn : 0 < n) (hnp : n < p) (hs : f n = -1) :
    f (p + n) = -1 := by
  have h := H.translation hn hnp
  rcases H.sign (p + n) (by omega) (by omega) with h1 | h1 <;> omega

theorem reverseTranslatePositive {n : ℕ} (hn : p < n) (hnp : n < 2 * p)
    (hs : f n = 1) : f (n - p) = 1 := by
  have h := H.translation (show 0 < n - p by omega) (show n - p < p by omega)
  have he : p + (n - p) = n := by omega
  rw [he] at h
  rcases H.sign (n - p) (by omega) (by omega) with h1 | h1 <;> omega

/-- The two exact identities in the upper third of the central interval. -/
theorem upperBand {n : ℕ} (hlo : p < 3 * n) (hhi : 2 * n < p) :
    f n = f (p - 2 * n) ∧ f n = -f (3 * n - p) := by
  have hn : 0 < n := by omega
  have hu : 0 < p - 2 * n := by omega
  have hv : 0 < 3 * n - p := by omega
  have hnu := H.doubleReflection hn hhi
  have htv := H.translation hv (show 3 * n - p < p by omega)
  have h3n := H.three n hn (by omega)
  have hev : p + (3 * n - p) = 3 * n := by omega
  rw [hev, h3n] at htv
  have h3u := H.three (p - 2 * n) hu (by omega)
  have h2v := H.two (3 * n - p) hv (by omega)
  have hnn := H.noNN (show 0 < 3 * (p - 2 * n) by omega)
    (show 0 < 2 * (3 * n - p) by omega)
    (show 3 * (p - 2 * n) + 2 * (3 * n - p) = p by omega)
  rcases H.sign n hn (by omega) with h1 | h1 <;>
    rcases H.sign (p - 2 * n) hu (by omega) with h2 | h2 <;>
    rcases H.sign (3 * n - p) hv (by omega) with h3 | h3 <;>
    constructor <;> omega

/-- The quarter-to-third identity, proved by its three integral residue cases. -/
theorem quarterBand (hp3 : p % 3 ≠ 0) {n : ℕ} (hlo : p < 4 * n)
    (hhi : 3 * n < p) : f n = f (p - 2 * n) := by
  have hn : 0 < n := by omega
  have hu : 0 < p - 2 * n := by omega
  have hnu := H.doubleReflection hn (show 2 * n < p by omega)
  by_contra hne
  have hnSign := H.sign n hn (show n < 2 * p by omega)
  have huSign := H.sign (p - 2 * n) hu (show p - 2 * n < 2 * p by omega)
  have fn : f n = -1 := by omega
  have fu : f (p - 2 * n) = 1 := by omega
  have hcases : n % 3 = 0 ∨ (p - n) % 3 = 0 ∨ (p + n) % 3 = 0 := by
    have hpmod := Nat.mod_lt p (by omega : 0 < 3)
    have hnmod := Nat.mod_lt n (by omega : 0 < 3)
    have hsubmod := Nat.mod_lt (p - n) (by omega : 0 < 3)
    have hsum := Nat.add_mod p n 3
    have hsub := Nat.add_mod (p - n) n 3
    have he : p - n + n = p := by omega
    rw [he] at hsub
    have hp12 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have hn012 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hn012 with hn0 | hn1 | hn2
    · exact Or.inl hn0
    · rcases hp12 with hp1 | hp2
      · right; left
        rw [hp1, hn1] at hsub
        omega
      · right; right
        rw [hp2, hn1] at hsum
        norm_num at hsum
        exact hsum
    · rcases hp12 with hp1 | hp2
      · right; right
        rw [hp1, hn2] at hsum
        norm_num at hsum
        exact hsum
      · right; left
        rw [hp2, hn2] at hsub
        omega
  rcases hcases with hcase | hcase | hcase
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hcase
    have hkpos : 0 < k := by omega
    have h3 := H.three k hkpos (show 3 * k < 2 * p by omega)
    have fk : f k = 1 := by rw [← hk] at h3; omega
    have h8 := H.eight hkpos (show 4 * k < p by omega)
    have f8 : f (8 * k) = -1 := by omega
    have ft := H.reflectNegative (show 0 < 8 * k by omega) (show 8 * k < p by omega) f8
    have h4 := H.four hu (show 2 * (p - 2 * n) < p by omega)
    have f4 : f (4 * (p - 2 * n)) = 1 := by omega
    have fr := H.reverseTranslatePositive
      (show p < 4 * (p - 2 * n) by omega)
      (show 4 * (p - 2 * n) < 2 * p by omega) f4
    have he : 4 * (p - 2 * n) - p = 3 * (p - 8 * k) := by omega
    rw [he] at fr
    have ht := H.three (p - 8 * k) (by omega) (by omega)
    omega
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hcase
    have h2 := H.two n hn (show n < p by omega)
    have f2 : f (2 * n) = 1 := by omega
    have fr := H.reflectPositive (show 0 < 2 * n by omega) (show 2 * n < 2 * p by omega) f2
    have he : 2 * p - 2 * n = 3 * (2 * k) := by omega
    rw [he] at fr
    have ht := H.three (2 * k) (by omega) (by omega)
    have hd := H.two (2 * k) (by omega) (by omega)
    have he2 : 2 * (2 * k) = 4 * k := by omega
    rw [he2] at hd
    have f4k : f (4 * k) = -1 := by omega
    have h2u := H.two (p - 2 * n) hu (by omega)
    have f2u : f (2 * (p - 2 * n)) = -1 := by omega
    have fs := H.reflectNegative (show 0 < 2 * (p - 2 * n) by omega)
      (show 2 * (p - 2 * n) < p by omega) f2u
    have he3 : p - 2 * (p - 2 * n) = 3 * (n - k) := by omega
    rw [he3] at fs
    have ht2 := H.three (n - k) (by omega) (by omega)
    have fnk : f (n - k) = -1 := by omega
    have fr2 := H.reflectNegative (show 0 < n - k by omega) (show n - k < p by omega) fnk
    have he4 : p - (n - k) = 4 * k := by omega
    rw [he4] at fr2
    omega
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hcase
    have he : p - 2 * n = 3 * (k - n) := by omega
    rw [he] at fu
    have ht := H.three (k - n) (by omega) (by omega)
    have fkn : f (k - n) = -1 := by omega
    have fr := H.reflectNegative (show 0 < k - n by omega) (show k - n < p by omega) fkn
    have he2 : p - (k - n) = 2 * k := by omega
    rw [he2] at fr
    have fs := H.translateNegative hn (show n < p by omega) fn
    rw [hk] at fs
    have ht2 := H.three k (by omega) (by omega)
    have hd := H.two k (by omega) (by omega)
    omega

/-- The doubling wrap identity across the entire upper half of the central interval. -/
theorem centralBand (hp3 : p % 3 ≠ 0) {n : ℕ} (hlo : p < 4 * n)
    (hhi : 2 * n < p) : f n = f (p - 2 * n) := by
  rcases lt_trichotomy (3 * n) p with h | h | h
  · exact H.quarterBand hp3 hlo h
  · have he : p % 3 = 0 := by omega
    contradiction
  · exact (H.upperBand h hhi).1

end IntervalSigns

/-- Odd completion of a sign sequence on the lower half of a residue interval. -/
def oddCompletion (p : ℕ) (f : ℕ → ℤ) (x : ZMod p) : ℤ :=
  x.valMinAbs.sign * f x.valMinAbs.natAbs

theorem oddCompletion_zero (p : ℕ) (f : ℕ → ℤ) : oddCompletion p f 0 = 0 := by
  simp [oddCompletion]

theorem oddCompletion_nat {p n : ℕ} {f : ℕ → ℤ} (hn : 0 < n) (hhi : 2 * n < p) :
    oddCompletion p f (n : ZMod p) = f n := by
  have hc := ZMod.valMinAbs_natCast_of_le_half (show n ≤ p / 2 by omega)
  simp only [oddCompletion, hc, Int.natAbs_natCast]
  have hs : Int.sign (n : ℤ) = 1 := Int.sign_eq_one_iff_pos.mpr (by exact_mod_cast hn)
  rw [hs, one_mul]

theorem oddCompletion_one {p : ℕ} {f : ℕ → ℤ} (hp : 2 < p) (hf : f 1 = 1) :
    oddCompletion p f 1 = 1 := by
  simpa using (oddCompletion_nat (f := f) (p := p) (n := 1) (by omega) (by omega)).trans hf

theorem oddCompletion_neg {p : ℕ} {f : ℕ → ℤ} (hp2 : p % 2 = 1) (x : ZMod p) :
    oddCompletion p f (-x) = -oddCompletion p f x := by
  have hne : 2 * x.val ≠ p := by omega
  simp [oddCompletion, ZMod.valMinAbs_neg_of_ne_half hne, Int.sign_neg, neg_mul]

theorem centralRepresentative {p : ℕ} [NeZero p] (hp2 : p % 2 = 1)
    {x : ZMod p} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ 2 * n < p ∧ (x = (n : ZMod p) ∨ x = -(n : ZMod p)) := by
  have hv := x.val_lt
  have hv0 : x.val ≠ 0 := by simpa using hx
  by_cases h : 2 * x.val < p
  · exact ⟨x.val, by omega, h, Or.inl (ZMod.natCast_zmod_val x).symm⟩
  · refine ⟨p - x.val, by omega, by omega, Or.inr ?_⟩
    rw [Nat.cast_sub (by omega : x.val ≤ p), ZMod.natCast_self, ZMod.natCast_zmod_val]
    simp

theorem oddCompletion_sign {p : ℕ} [NeZero p] {f : ℕ → ℤ}
    (H : IntervalSigns p f) (hp2 : p % 2 = 1) {x : ZMod p} (hx : x ≠ 0) :
    oddCompletion p f x = 1 ∨ oddCompletion p f x = -1 := by
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h, oddCompletion_nat hn hhi]
    exact H.sign n hn (by omega)
  · rw [h, oddCompletion_neg hp2, oddCompletion_nat hn hhi]
    rcases H.sign n hn (show n < 2 * p by omega) with h1 | h1 <;> omega

theorem oddCompletion_two_nat {p n : ℕ} {f : ℕ → ℤ} (H : IntervalSigns p f)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (hn : 0 < n) (hhi : 2 * n < p) :
    oddCompletion p f (2 * (n : ZMod p)) = -oddCompletion p f (n : ZMod p) := by
  rw [oddCompletion_nat hn hhi]
  by_cases h : 4 * n < p
  · have he : (2 : ZMod p) * n = ((2 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, oddCompletion_nat (by omega) (by omega), H.two n hn (by omega)]
  · have hp4 : p < 4 * n := by omega
    have he : (2 : ZMod p) * n = -((p - 2 * n : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]
      push_cast
      ring
    rw [he, oddCompletion_neg hp2, oddCompletion_nat (by omega) (by omega)]
    rw [H.centralBand hp3 hp4 hhi]

theorem oddCompletion_two {p : ℕ} [NeZero p] {f : ℕ → ℤ} (H : IntervalSigns p f)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    oddCompletion p f (2 * x) = -oddCompletion p f x := by
  by_cases hx : x = 0
  · simp [hx, oddCompletion_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]
    exact oddCompletion_two_nat H hp2 hp3 hn hhi
  · rw [h, mul_neg, oddCompletion_neg hp2, oddCompletion_neg hp2,
      oddCompletion_two_nat H hp2 hp3 hn hhi]

theorem oddCompletion_neg_two {p : ℕ} [NeZero p] {f : ℕ → ℤ} (H : IntervalSigns p f)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    oddCompletion p f (-2 * x) = oddCompletion p f x := by
  rw [neg_mul, oddCompletion_neg hp2, oddCompletion_two H hp2 hp3, neg_neg]

theorem oddCompletion_three_upper {p n : ℕ} {f : ℕ → ℤ} (H : IntervalSigns p f)
    (hlo : p < 3 * n) (hhi : 2 * n < p) :
    oddCompletion p f (3 * (n : ZMod p)) = -oddCompletion p f (n : ZMod p) := by
  have he : (3 : ZMod p) * n = ((3 * n - p : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : p ≤ 3 * n), ZMod.natCast_self]
    push_cast
    ring
  rw [he, oddCompletion_nat (by omega) (by omega), oddCompletion_nat (by omega) hhi]
  have h := (H.upperBand hlo hhi).2
  omega

theorem oddCompletion_three_nat {p n : ℕ} [NeZero p] {f : ℕ → ℤ}
    (H : IntervalSigns p f) (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    (hn : 0 < n) (hhi : 2 * n < p) :
    oddCompletion p f (3 * (n : ZMod p)) = -oddCompletion p f (n : ZMod p) := by
  by_cases hlo : 6 * n < p
  · have he : (3 : ZMod p) * n = ((3 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, oddCompletion_nat (by omega) (by omega), oddCompletion_nat hn hhi,
      H.three n hn (by omega)]
  by_cases hup : p < 3 * n
  · exact oddCompletion_three_upper H hup hhi
  have hnlo : p < 6 * n := by omega
  have hnhi : 3 * n < p := by omega
  by_cases hsmall : 4 * n < p
  · have hupper := oddCompletion_three_upper H
      (show p < 3 * (2 * n) by omega) (show 2 * (2 * n) < p by omega)
    have he : ((2 * n : ℕ) : ZMod p) = 2 * (n : ZMod p) := by push_cast; rfl
    rw [he] at hupper
    have he2 : 3 * (2 * (n : ZMod p)) = 2 * (3 * (n : ZMod p)) := by ring
    rw [he2, oddCompletion_two H hp2 hp3, oddCompletion_two H hp2 hp3] at hupper
    omega
  · have hupper := oddCompletion_three_upper H
      (show p < 3 * (p - 2 * n) by omega) (show 2 * (p - 2 * n) < p by omega)
    have he : ((p - 2 * n : ℕ) : ZMod p) = -2 * (n : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]
      push_cast
      ring
    rw [he] at hupper
    have he2 : 3 * (-2 * (n : ZMod p)) = -2 * (3 * (n : ZMod p)) := by ring
    rw [he2, oddCompletion_neg_two H hp2 hp3, oddCompletion_neg_two H hp2 hp3] at hupper
    exact hupper

theorem oddCompletion_three {p : ℕ} [NeZero p] {f : ℕ → ℤ} (H : IntervalSigns p f)
    (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    oddCompletion p f (3 * x) = -oddCompletion p f x := by
  by_cases hx : x = 0
  · simp [hx, oddCompletion_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]
    exact oddCompletion_three_nat H hp2 hp3 hn hhi
  · rw [h, mul_neg, oddCompletion_neg hp2, oddCompletion_neg hp2,
      oddCompletion_three_nat H hp2 hp3 hn hhi]

theorem oddCompletion_short_mul {p a b : ℕ} {f : ℕ → ℤ}
    (hmul : ∀ a b, f (a * b) = f a * f b) (ha : 0 < a) (hb : 0 < b)
    (hhi : 2 * (a * b) < p) :
    oddCompletion p f ((a : ZMod p) * (b : ZMod p)) =
      oddCompletion p f (a : ZMod p) * oddCompletion p f (b : ZMod p) := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have ha' : a ≤ a * b := by nlinarith
  have hb' : b ≤ a * b := by nlinarith
  rw [← Nat.cast_mul, oddCompletion_nat hab hhi,
    oddCompletion_nat ha (by omega), oddCompletion_nat hb (by omega), hmul]

end LiouvilleGoldbach
