import LiouvilleGoldbach.Extension

namespace LiouvilleGoldbach

/-- In the remaining narrow strip, one of the two odd multiples immediately
adjacent to `2*q` is divisible by three. Its distance from `p` is even and
less than `2*n`, so the same halving step handles both residue classes of `q`. -/
theorem uniform_even_descent (p q n : ℕ) (hq : 5 ≤ q)
    (hlo : (2 * q - 1) * n < p) (hhi : p < 2 * q * n)
    (hpodd : p % 2 = 1) (hnodd : n % 2 = 1)
    (hqmod : q % 3 = 1 ∨ q % 3 = 2) :
    ∃ j r : ℕ, 0 < j ∧ j < q ∧ 0 < r ∧ r < n ∧
      (3 * j * n = p + 2 * r ∨ p = 3 * j * n + 2 * r) := by
  have hn : 0 < n := by omega
  have hs : 2 * q - 1 + 1 = 2 * q := by omega
  rcases hqmod with hqm | hqm
  · let a := 2 * q + 1
    let j := a / 3
    let v := a * n - p
    have ha : a = 3 * j := by dsimp [a, j]; omega
    have hj : 0 < j ∧ j < q := by dsimp [j, a]; omega
    have hvpos : p < a * n := by dsimp [a]; nlinarith
    have hv : v + p = a * n := Nat.sub_add_cancel hvpos.le
    have hvbound : 0 < v ∧ v < 2 * n := by
      constructor
      · dsimp [v]; omega
      · dsimp [a] at hv; nlinarith
    have haodd : a % 2 = 1 := by dsimp [a]; omega
    have heven : v % 2 = 0 := by
      have hm := congrArg (fun t : ℕ => t % 2) hv
      rw [Nat.add_mod, Nat.mul_mod, hpodd, hnodd, haodd] at hm
      omega
    refine ⟨j, v / 2, hj.1, hj.2, by omega, by omega, Or.inl ?_⟩
    rw [← ha]
    omega
  · let a := 2 * q - 1
    let j := a / 3
    let v := p - a * n
    have ha : a = 3 * j := by dsimp [a, j]; omega
    have hj : 0 < j ∧ j < q := by dsimp [j, a]; omega
    have hvpos : a * n < p := hlo
    have hv : v + a * n = p := Nat.sub_add_cancel hvpos.le
    have hvbound : 0 < v ∧ v < n := by
      constructor
      · dsimp [v]; omega
      · dsimp [a] at hv; nlinarith
    have haodd : a % 2 = 1 := by dsimp [a]; omega
    have heven : v % 2 = 0 := by
      have hm := congrArg (fun t : ℕ => t % 2) hv
      rw [Nat.add_mod, Nat.mul_mod, hpodd, hnodd, haodd] at hm
      omega
    refine ⟨j, v / 2, hj.1, hj.2, by omega, by omega, Or.inr ?_⟩
    rw [← ha]
    omega

/-- A symmetric version of the descent certificate. The narrow strip uses
one halved odd remainder in both residue classes; outside it, an adjacent
even multiple gives a smaller remainder directly. -/
theorem extension_descent_certificate_symmetric
    (p q n : ℕ) (hq : 5 ≤ q) (hn : 1 < n)
    (hnsmall : 2 * n < p) (hshort : p < 2 * q * n)
    (hpodd : p % 2 = 1) (hnodd : n % 2 = 1)
    (hrem : p % n ≠ 0) (hqmod : q % 3 = 1 ∨ q % 3 = 2) :
    ∃ a b j r : ℕ,
      0 < j ∧ j < q ∧ 0 < r ∧ r < n ∧
      (a = 2 * j ∨ a = 3 * j) ∧ (b = 1 ∨ b = 2) ∧
      (a * n = p + b * r ∨ p = a * n + b * r) := by
  by_cases hstrip : (2 * q - 1) * n < p
  · obtain ⟨j, r, hj, hjq, hr, hrn, heq⟩ :=
      uniform_even_descent p q n hq hstrip hshort hpodd hnodd hqmod
    exact ⟨3 * j, 2, j, r, hj, hjq, hr, hrn, Or.inr rfl, Or.inr rfl, heq⟩
  · have hneq : (2 * q - 1) * n ≠ p := by
      intro heq
      apply hrem
      rw [← heq]
      simp
    have hlarge : p < (2 * q - 1) * n := by omega
    let t := p / n
    let s := p % n
    have hdiv : t * n + s = p := by
      dsimp [t, s]
      simpa [Nat.mul_comm] using Nat.div_add_mod p n
    have hspos : 0 < s := by dsimp [s]; omega
    have hslt : s < n := Nat.mod_lt p (by omega)
    have htlo : 2 ≤ t := by
      by_contra ht
      have ht' : t ≤ 1 := by omega
      nlinarith
    have hthi : t < 2 * q - 1 := by
      by_contra ht
      have ht' : 2 * q - 1 ≤ t := by omega
      nlinarith
    by_cases htmod : t % 2 = 0
    · let j := t / 2
      have ht : t = 2 * j := by dsimp [j]; omega
      have hj : 0 < j ∧ j < q := by dsimp [j]; omega
      refine ⟨t, 1, j, s, hj.1, hj.2, hspos, hslt, Or.inl ht, Or.inl rfl,
        Or.inr ?_⟩
      omega
    · let a := t + 1
      let j := a / 2
      let r := n - s
      have htmod' : t % 2 = 1 := by omega
      have ha : a = 2 * j := by dsimp [a]; omega
      have hj : 0 < j ∧ j < q := by dsimp [j, a]; omega
      have hrpos : 0 < r := by dsimp [r]; omega
      have hrlt : r < n := by dsimp [r]; omega
      have hre : r + s = n := Nat.sub_add_cancel (Nat.le_of_lt hslt)
      refine ⟨a, 1, j, r, hj.1, hj.2, hrpos, hrlt, Or.inl ha, Or.inl rfl,
        Or.inl ?_⟩
      dsimp [a]
      nlinarith

end LiouvilleGoldbach
