import LiouvilleGoldbach.Commuting
import LiouvilleGoldbach.Coset
import LiouvilleGoldbach.Residue

namespace LiouvilleGoldbach

open Final

theorem liouville_intervalSigns {p : ℕ}
    (h : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = 2 * p ∧
      liouville a = 1 ∧ liouville b = 1) :
    IntervalSigns p liouville := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn _
    exact liouville_sign hn
  · intro n _ _
    rw [ArithmeticFunction.liouville_apply_mul,
      liouville_prime Nat.prime_two, neg_one_mul]
  · intro n _ _
    rw [ArithmeticFunction.liouville_apply_mul,
      liouville_prime Nat.prime_three, neg_one_mul]
  · intro a b ha hb hab hs
    exact h ⟨a, b, ha, hb, hab, hs.1, hs.2⟩

/-- Every prime greater than three has a positive-positive Liouville pair at twice the prime. -/
theorem positive_prime_pairs : PositivePrimePairs := by
  intro p hp hp3
  by_contra hpair
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hpmod3 : p % 3 ≠ 0 := by
    intro hz
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hz
    have he := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp hd
    omega
  have H := liouville_intervalSigns hpair
  let F := oddCompletion p liouville
  have hF0 : F 0 = 0 := oddCompletion_zero p liouville
  have hF1 : F 1 = 1 := by
    exact oddCompletion_one (by omega) ArithmeticFunction.liouville_apply_one
  have hFneg : ∀ x, F (-x) = -F x := oddCompletion_neg hpodd
  have hFtwo : ∀ x, F (2 * x) = -F x := H.commuting_completion_two hp3 hpodd hpmod3
  have hFthree : ∀ x, F (3 * x) = -F x := H.commuting_completion_three hp3 hpodd hpmod3
  have hm1 : F (-1) = -1 := by simpa [hF1] using hFneg 1
  have h2 : F 2 = -1 := by simpa [hF1] using hFtwo 1
  have h3 : F 3 = -1 := by simpa [hF1] using hFthree 1
  have hsign : ∀ x : ZMod p, x ≠ 0 → F x = 1 ∨ F x = -1 := by
    intro x hx
    exact oddCompletion_sign H hpodd hx
  have hFnz : ∀ x : ZMod p, x ≠ 0 → F x ≠ 0 := by
    intro x hx
    rcases hsign x hx with hs | hs <;> omega
  have hminus : IsGood F (-1) := by
    intro x
    simpa [hm1] using hFneg x
  have htwo : IsGood F 2 := by
    intro x
    simpa [h2] using hFtwo x
  have hthree : IsGood F 3 := by
    intro x
    simpa [h3] using hFthree x
  have hlocal : ∀ a b : ℕ, 0 < a → 0 < b → 2 * (a * b) < p →
      F ((a * b : ℕ) : ZMod p) = F a * F b := by
    intro a b ha hb hab
    simpa only [Nat.cast_mul] using
      oddCompletion_short_mul ArithmeticFunction.liouville_apply_mul ha hb hab
  have hmul := half_interval_extension_via_invariance p hp hp3 F hF0 hF1 hFnz
    hminus htwo hthree hlocal
  exact no_multiplicative_agreement_of_odd hp hp3 F (fun x y _ _ => hmul x y)
    hsign hm1 (fun n hn hnp => oddCompletion_nat hn hnp)

/-- Shusterman's Liouville-Goldbach assertion, with no analytic or conjectural hypothesis. -/
theorem liouville_goldbach (N : ℕ) (hEven : Even N) (hN : 2 < N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      ArithmeticFunction.liouville a = -1 ∧ ArithmeticFunction.liouville b = -1 := by
  exact all_even_of_positivePrimePairs positive_prime_pairs N hEven hN

end LiouvilleGoldbach
