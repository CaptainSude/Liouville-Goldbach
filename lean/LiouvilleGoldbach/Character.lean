import LiouvilleGoldbach.Reduction
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace LiouvilleGoldbach.Final

/-- A function that is one on nonzero squares and minus one at minus one and
two cannot agree with Liouville throughout the lower half of a prime modulus.
Only the square criteria and quadratic reciprocity are used: no classification
of real characters is needed. -/
theorem no_square_character_agreement {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (F : ZMod p → ℤ)
    (hsq : ∀ x : ZMod p, x ≠ 0 → F (x * x) = 1)
    (hneg : F (-1) = -1) (htwo : F 2 = -1)
    (hagree : ∀ n : ℕ, 0 < n → 2 * n < p → F n = liouville n) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have hval : ∀ x : ZMod p, x ≠ 0 → IsSquare x → F x = 1 := by
    intro x hx hs
    obtain ⟨y, hy⟩ := hs
    have hy0 : y ≠ 0 := by
      intro heq
      apply hx
      simp [heq] at hy ⊢
      exact hy
    rw [hy]
    exact hsq y hy0
  have hnonsqneg : ¬ IsSquare (-1 : ZMod p) := by
    intro h
    have := hval (-1) (neg_ne_zero.mpr one_ne_zero) h
    omega
  have hp4 : p % 4 = 3 := by
    by_contra h
    exact hnonsqneg (ZMod.exists_sq_eq_neg_one_iff.mpr h)
  have hp2 : p ≠ 2 := by omega
  have htwo0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 2) hdvd
    omega
  have hnonsqtwo : ¬ IsSquare (2 : ZMod p) := by
    intro h
    have := hval 2 htwo0 h
    omega
  have hp8 : p % 8 = 3 := by
    have h : ¬ (p % 8 = 1 ∨ p % 8 = 7) := by
      intro h
      exact hnonsqtwo ((ZMod.exists_sq_eq_two_iff hp2).mpr h)
    omega
  let L := (p + 1) / 4
  have hL : 1 < L := by dsimp [L]; omega
  have hLodd : L % 2 = 1 := by dsimp [L]; omega
  have hL4 : 4 * L = p + 1 := by dsimp [L]; omega
  obtain ⟨ℓ, hℓ, hℓL⟩ := Nat.exists_prime_and_dvd (by omega : L ≠ 1)
  let : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓpos := hℓ.pos
  have hℓbound : ℓ ≤ L := Nat.le_of_dvd (by omega) hℓL
  have hℓhalf : 2 * ℓ < p := by omega
  have hℓp : ℓ < p := by omega
  have hℓ2 : ℓ ≠ 2 := by
    intro heq
    rw [heq] at hℓL
    have := Nat.mod_eq_zero_of_dvd hℓL
    omega
  have hℓdiv : ℓ ∣ p + 1 := by
    rw [← hL4]
    exact dvd_mul_of_dvd_right hℓL 4
  have hpcast : (p : ZMod ℓ) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff (p + 1) ℓ).mpr hℓdiv
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  have hℓ4 : ℓ % 4 = 1 ∨ ℓ % 4 = 3 := by
    have := (Nat.Prime.mod_two_eq_one_iff_ne_two hℓ).mpr hℓ2
    omega
  have hℓsquare : IsSquare (ℓ : ZMod p) := by
    rcases hℓ4 with hℓ4 | hℓ4
    · apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
        (p := ℓ) (q := p) hℓ4 hp2).mp
      rw [hpcast]
      apply ZMod.exists_sq_eq_neg_one_iff.mpr
      omega
    · apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three
        (p := p) (q := ℓ) hp4 hℓ4 (by omega)).mpr
      rw [hpcast]
      intro hs
      have := ZMod.exists_sq_eq_neg_one_iff.mp hs
      exact this hℓ4
  have hℓ0 : (ℓ : ZMod p) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff ℓ p).mp hz
    have := Nat.le_of_dvd hℓpos hdvd
    omega
  have hone := hval ℓ hℓ0 hℓsquare
  rw [hagree ℓ hℓpos hℓhalf, liouville_prime hℓ] at hone
  norm_num at hone

/-- Convenient multiplicative formulation of the preceding contradiction. -/
theorem no_multiplicative_agreement {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (F : ZMod p → ℤ)
    (hmul : ∀ x y : ZMod p, x ≠ 0 → y ≠ 0 → F (x * y) = F x * F y)
    (hsign : ∀ x : ZMod p, x ≠ 0 → F x = 1 ∨ F x = -1)
    (hneg : F (-1) = -1) (htwo : F 2 = -1)
    (hagree : ∀ n : ℕ, 0 < n → 2 * n < p → F n = liouville n) : False := by
  apply no_square_character_agreement hp hp3 F ?_ hneg htwo hagree
  intro x hx
  rw [hmul x x hx hx]
  rcases hsign x hx with h | h <;> rw [h] <;> norm_num

end LiouvilleGoldbach.Final


