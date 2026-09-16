import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LiouvilleGoldbach.Final

abbrev liouville := ArithmeticFunction.liouville

theorem liouville_sign {n : ℕ} (hn : 0 < n) :
    liouville n = 1 ∨ liouville n = -1 := by
  rw [ArithmeticFunction.liouville_apply (Nat.ne_of_gt hn)]
  exact neg_one_pow_eq_or ℤ _

theorem liouville_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]
  norm_num

def NegativePair (N : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧ liouville a = -1 ∧ liouville b = -1

def PositivePrimePairs : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p →
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = 2 * p ∧
      liouville a = 1 ∧ liouville b = 1

theorem NegativePair.scale {N c : ℕ} (h : NegativePair N)
    (hc : 0 < c) (hlam : liouville c = 1) : NegativePair (c * N) := by
  rcases h with ⟨a, b, ha, hb, hab, hlama, hlamb⟩
  refine ⟨c * a, c * b, Nat.mul_pos hc ha, Nat.mul_pos hc hb, ?_, ?_, ?_⟩
  · rw [← mul_add, hab]
  · rw [ArithmeticFunction.liouville_apply_mul, hlam, hlama, one_mul]
  · rw [ArithmeticFunction.liouville_apply_mul, hlam, hlamb, one_mul]

theorem negativePair_eight : NegativePair 8 := by
  refine ⟨3, 5, by omega, by omega, by omega, ?_, ?_⟩ <;>
    exact liouville_prime (by decide)

theorem negativePair_twelve : NegativePair 12 := by
  refine ⟨5, 7, by omega, by omega, by omega, ?_, ?_⟩ <;>
    exact liouville_prime (by decide)

theorem negativePair_eighteen : NegativePair 18 := by
  refine ⟨7, 11, by omega, by omega, by omega, ?_, ?_⟩ <;>
    exact liouville_prime (by decide)

theorem negativePair_of_large_prime (H : PositivePrimePairs) {m p : ℕ}
    (hm : 0 < m) (hlamm : liouville m = 1) (hp : p.Prime)
    (hplarge : 3 < p) (hpdvd : p ∣ m) : NegativePair (2 * m) := by
  rcases hpdvd with ⟨c, rfl⟩
  have hc : 0 < c := Nat.pos_of_mul_pos_left hm
  have hlamc : liouville c = -1 := by
    rw [ArithmeticFunction.liouville_apply_mul, liouville_prime hp] at hlamm
    linarith
  rcases H p hp hplarge with ⟨a, b, ha, hb, hab, hlama, hlamb⟩
  refine ⟨c * a, c * b, Nat.mul_pos hc ha, Nat.mul_pos hc hb, ?_, ?_, ?_⟩
  · calc
      c * a + c * b = c * (a + b) := by ring
      _ = c * (2 * p) := by rw [hab]
      _ = 2 * (p * c) := by ring
  · rw [ArithmeticFunction.liouville_apply_mul, hlamc, hlama, mul_one]
  · rw [ArithmeticFunction.liouville_apply_mul, hlamc, hlamb, mul_one]

/-- Two successive prime divisors suffice for the final reduction, avoiding
any separate factorization theorem for numbers supported on 2 and 3. -/
theorem all_even_of_positivePrimePairs (H : PositivePrimePairs) :
    ∀ N : ℕ, Even N → 2 < N → NegativePair N := by
  intro N hNeven hN
  rcases hNeven with ⟨m, rfl⟩
  have hm : 1 < m := by omega
  have hgoal : NegativePair (2 * m) := by
    rcases liouville_sign (by omega : 0 < m) with hlamm | hlamm
    · obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      by_cases hpbig : 3 < p
      · exact negativePair_of_large_prime H (by omega) hlamm hp hpbig hpdiv
      rcases hpdiv with ⟨c, hmc⟩
      have hc : 0 < c := by nlinarith
      have hlamc : liouville c = -1 := by
        rw [hmc, ArithmeticFunction.liouville_apply_mul, liouville_prime hp] at hlamm
        linarith
      have hc1 : c ≠ 1 := by
        intro heq
        rw [heq, ArithmeticFunction.liouville_apply_one] at hlamc
        norm_num at hlamc
      obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hc1
      by_cases hqbig : 3 < q
      · apply negativePair_of_large_prime H (by omega) hlamm hq hqbig
        exact dvd_trans hqdiv (by rw [hmc]; exact dvd_mul_left c p)
      rcases hqdiv with ⟨d, hcd⟩
      have hd : 0 < d := by nlinarith
      have hlamd : liouville d = 1 := by
        rw [hcd, ArithmeticFunction.liouville_apply_mul, liouville_prime hq] at hlamc
        linarith
      have hp23 : p = 2 ∨ p = 3 := by have := hp.two_le; omega
      have hq23 : q = 2 ∨ q = 3 := by have := hq.two_le; omega
      have hbase : NegativePair (2 * (p * q)) := by
        rcases hp23 with rfl | rfl <;> rcases hq23 with rfl | rfl
        · exact negativePair_eight
        · exact negativePair_twelve
        · exact negativePair_twelve
        · exact negativePair_eighteen
      convert hbase.scale hd hlamd using 1
      rw [hmc, hcd]
      ring
    · exact ⟨m, m, by omega, by omega, by omega, hlamm, hlamm⟩
  simpa only [two_mul] using hgoal

end LiouvilleGoldbach.Final

