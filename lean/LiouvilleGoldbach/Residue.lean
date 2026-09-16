import LiouvilleGoldbach.Reduction
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace LiouvilleGoldbach.Final

/-- Every prime `p > 3` congruent to three modulo four has a prime quadratic
residue strictly below its half interval. Any prime divisor of `(p+1)/4`
works, including the prime two. -/
theorem exists_prime_square_below_half {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hp4 : p % 4 = 3) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 2 * ℓ < p ∧ IsSquare (ℓ : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let L := (p + 1) / 4
  have hL : 1 < L := by dsimp [L]; omega
  have hL4 : 4 * L = p + 1 := by dsimp [L]; omega
  obtain ⟨ℓ, hℓ, hℓL⟩ := Nat.exists_prime_and_dvd (by omega : L ≠ 1)
  let : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓbound : ℓ ≤ L := Nat.le_of_dvd (by omega) hℓL
  have hℓhalf : 2 * ℓ < p := by omega
  refine ⟨ℓ, hℓ, hℓhalf, ?_⟩
  by_cases hℓ2 : ℓ = 2
  · subst ℓ
    have hLmod : L % 2 = 0 := Nat.mod_eq_zero_of_dvd hℓL
    have hp8 : p % 8 = 7 := by omega
    exact (ZMod.exists_sq_eq_two_iff (by omega : p ≠ 2)).mpr (Or.inr hp8)
  · have hℓdiv : ℓ ∣ p + 1 := by
      rw [← hL4]
      exact dvd_mul_of_dvd_right hℓL 4
    have hpcast : (p : ZMod ℓ) = -1 := by
      have hz := (ZMod.natCast_eq_zero_iff (p + 1) ℓ).mpr hℓdiv
      push_cast at hz
      exact eq_neg_of_add_eq_zero_left hz
    have hℓ4 : ℓ % 4 = 1 ∨ ℓ % 4 = 3 := by
      have := (Nat.Prime.mod_two_eq_one_iff_ne_two hℓ).mpr hℓ2
      omega
    rcases hℓ4 with hℓ4 | hℓ4
    · apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
        (p := ℓ) (q := p) hℓ4 (by omega : p ≠ 2)).mp
      rw [hpcast]
      apply ZMod.exists_sq_eq_neg_one_iff.mpr
      omega
    · apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three
        (p := p) (q := ℓ) hp4 hℓ4 (by omega)).mpr
      rw [hpcast]
      intro hs
      have := ZMod.exists_sq_eq_neg_one_iff.mp hs
      exact this hℓ4

/-- An odd function which is one on nonzero squares cannot agree with
Liouville on the full positive half interval. No condition at two is needed. -/
theorem no_square_character_agreement_of_odd {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (F : ZMod p → ℤ)
    (hsq : ∀ x : ZMod p, x ≠ 0 → F (x * x) = 1)
    (hneg : F (-1) = -1)
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
  obtain ⟨ℓ, hℓ, hℓhalf, hℓsquare⟩ := exists_prime_square_below_half hp hp3 hp4
  have hℓ0 : (ℓ : ZMod p) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff ℓ p).mp hz
    have := Nat.le_of_dvd hℓ.pos hdvd
    omega
  have hone := hval ℓ hℓ0 hℓsquare
  rw [hagree ℓ hℓ.pos hℓhalf, liouville_prime hℓ] at hone
  norm_num at hone

/-- Odd multiplicativity alone supplies the final contradiction; neither
character classification nor a prescribed value at two is required. -/
theorem no_multiplicative_agreement_of_odd {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (F : ZMod p → ℤ)
    (hmul : ∀ x y : ZMod p, x ≠ 0 → y ≠ 0 → F (x * y) = F x * F y)
    (hsign : ∀ x : ZMod p, x ≠ 0 → F x = 1 ∨ F x = -1)
    (hneg : F (-1) = -1)
    (hagree : ∀ n : ℕ, 0 < n → 2 * n < p → F n = liouville n) : False := by
  apply no_square_character_agreement_of_odd hp hp3 F ?_ hneg hagree
  intro x hx
  rw [hmul x x hx hx]
  rcases hsign x hx with h | h <;> rw [h] <;> norm_num

end LiouvilleGoldbach.Final
