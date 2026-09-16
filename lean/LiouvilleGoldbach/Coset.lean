import LiouvilleGoldbach.Descent
import Mathlib.Data.Nat.Find

namespace LiouvilleGoldbach

/-- In the narrow strip, either neighbouring odd multiplier gives a smaller
argument after division by two. This packages the two residue cases uniformly. -/
theorem halved_strip_remainder
    (p q n a : ℕ) (hq : 1 ≤ q) (_hn : 0 < n)
    (hpodd : p % 2 = 1) (hnodd : n % 2 = 1)
    (hstrip : (2 * q - 1) * n < p) (hshort : p < 2 * q * n)
    (ha : a = 2 * q - 1 ∨ a = 2 * q + 1) (hne : a * n ≠ p) :
    ∃ r : ℕ, 0 < r ∧ r < n ∧
      (a * n = p + 2 * r ∨ p = a * n + 2 * r) := by
  have hsum : (2 * q - 1) + 1 = 2 * q := by omega
  have haodd : a % 2 = 1 := by rcases ha with rfl | rfl <;> omega
  have halo : 2 * q - 1 ≤ a := by rcases ha with rfl | rfl <;> omega
  have hahi : a ≤ 2 * q + 1 := by rcases ha with rfl | rfl <;> omega
  by_cases hap : p < a * n
  · let v := a * n - p
    have hv : v + p = a * n := Nat.sub_add_cancel hap.le
    have hvpos : 0 < v := by dsimp [v]; omega
    have hvlt : v < 2 * n := by nlinarith
    have hveven : v % 2 = 0 := by
      have hm := congrArg (fun t : ℕ => t % 2) hv
      rw [Nat.add_mod, Nat.mul_mod, hpodd, hnodd, haodd] at hm
      omega
    refine ⟨v / 2, by omega, by omega, Or.inl ?_⟩
    omega
  · have hap' : a * n < p := by omega
    let v := p - a * n
    have hv : v + a * n = p := Nat.sub_add_cancel hap'.le
    have hvpos : 0 < v := by dsimp [v]; omega
    have hvlt : v < 2 * n := by nlinarith
    have hveven : v % 2 = 0 := by
      have hm := congrArg (fun t : ℕ => t % 2) hv
      rw [Nat.add_mod, Nat.mul_mod, hpodd, hnodd, haodd] at hm
      omega
    refine ⟨v / 2, by omega, by omega, Or.inr ?_⟩
    omega

/-- Every nonempty set of nonzero residues invariant under negation and
multipliers below `q` has a representative below `p / (2*q)`. For a subgroup
containing those multipliers, apply this to any multiplicative coset. -/
theorem short_representative_of_invariance
    (p q : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (hq : q.Prime) (hqge : 5 ≤ q) (hqp : 2 * q < p)
    (P : ZMod p → Prop)
    (hneg : ∀ x, P (-x) ↔ P x)
    (hsmall : ∀ j : ℕ, 0 < j → j < q → ∀ x,
      P ((j : ZMod p) * x) ↔ P x)
    (hex : ∃ x : ZMod p, x ≠ 0 ∧ P x) :
    ∃ n : ℕ, 0 < n ∧ 2 * (q * n) < p ∧ P (n : ZMod p) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hqmod : q % 3 = 1 ∨ q % 3 = 2 := by
    have hm : q % 3 ≠ 0 := by
      intro hm
      have hd := hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hm)
      omega
    omega
  have hexnat : ∃ n : ℕ, 0 < n ∧ 2 * n < p ∧ P (n : ZMod p) := by
    obtain ⟨x, hx, hPx⟩ := hex
    obtain ⟨n, hn, hnsmall, hrep⟩ := central_nat_rep p hpodd x hx
    refine ⟨n, hn, hnsmall, ?_⟩
    rcases hrep with rfl | rfl
    · exact hPx
    · exact (hneg _).mp hPx
  let n := Nat.find hexnat
  have hn : 0 < n ∧ 2 * n < p ∧ P (n : ZMod p) := Nat.find_spec hexnat
  have hminimal : ∀ r : ℕ, 0 < r → r < n → ¬ P (r : ZMod p) := by
    intro r hr hrlt hPr
    have hnr := Nat.find_min' hexnat ⟨hr, by omega, hPr⟩
    change n ≤ r at hnr
    omega
  refine ⟨n, hn.1, ?_, hn.2.2⟩
  by_contra hshort
  have hn1 : 1 < n := by
    have hne : n ≠ 1 := by
      intro he
      apply hshort
      simpa only [he, mul_one] using hqp
    omega
  have htwo : ∀ x, P ((2 : ZMod p) * x) ↔ P x := by
    simpa using hsmall 2 (by decide) (by omega)
  have hthree : ∀ x, P ((3 : ZMod p) * x) ↔ P x := by
    simpa using hsmall 3 (by decide) (by omega)
  have hnodd : n % 2 = 1 := by
    by_contra ho
    have heven : n % 2 = 0 := by omega
    have hcast : (2 : ZMod p) * (n / 2 : ℕ) = (n : ZMod p) := by
      have he : 2 * (n / 2) = n := by omega
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun t : ℕ => (t : ZMod p)) he
    have hhalf : P ((n / 2 : ℕ) : ZMod p) := (htwo _).mp (by rw [hcast]; exact hn.2.2)
    exact hminimal (n / 2) (by omega) (by omega) hhalf
  have hshort' : p < 2 * q * n := by
    have hne : 2 * q * n ≠ p := by
      intro he
      have hm := congrArg (fun t : ℕ => t % 2) he
      simp [Nat.mul_mod, hpodd] at hm
    have hle : p ≤ 2 * q * n := by
      simpa only [mul_assoc] using Nat.le_of_not_gt hshort
    omega
  have hrem : p % n ≠ 0 := by
    intro hr
    have hd := hp.eq_one_or_self_of_dvd n (Nat.dvd_of_mod_eq_zero hr)
    omega
  obtain ⟨a, b, j, r, hjpos, hjlt, hrpos, hrlt, ha, hb, heq⟩ :=
    extension_descent_certificate_symmetric p q n hqge hn1 hn.2.1 hshort'
      hpodd hnodd hrem hqmod
  have haP : P ((a : ZMod p) * n) := by
    rcases ha with ha | ha
    · rw [ha, Nat.cast_mul, mul_assoc]
      exact (htwo _).mpr ((hsmall j hjpos hjlt _).mpr hn.2.2)
    · rw [ha, Nat.cast_mul, mul_assoc]
      exact (hthree _).mpr ((hsmall j hjpos hjlt _).mpr hn.2.2)
  have hbP : P ((b : ZMod p) * r) := by
    rcases heq with heq | heq
    · have hcast := congrArg (fun t : ℕ => (t : ZMod p)) heq
      simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_add] at hcast
      rwa [hcast] at haP
    · have hcast := congrArg (fun t : ℕ => (t : ZMod p)) heq
      simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self] at hcast
      have han : (a : ZMod p) * n = -(b * (r : ZMod p)) := by
        linear_combination -hcast
      rw [han] at haP
      exact (hneg _).mp haP
  apply hminimal r hrpos hrlt
  rcases hb with rfl | rfl
  · simpa using hbP
  · exact (htwo _).mp hbP

/-- The extension theorem proved through the short-representative principle.
The only descent is now contained in the invariant-set lemma. -/
theorem half_interval_extension_via_invariance
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (F : ZMod p → ℤ) (hFzero : F 0 = 0) (hFone : F 1 = 1)
    (hFnz : ∀ x, x ≠ 0 → F x ≠ 0)
    (hminus : IsGood F (-1)) (htwo : IsGood F 2) (hthree : IsGood F 3)
    (hlocal : ∀ a b : ℕ, 0 < a → 0 < b → 2 * (a * b) < p →
      F ((a * b : ℕ) : ZMod p) = F (a : ZMod p) * F (b : ZMod p)) :
    ∀ x y : ZMod p, F (x * y) = F x * F y := by
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hgood : ∀ q : ℕ, 0 < q → 2 * q < p → IsGood F (q : ZMod p) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hqpos hqp
      by_cases hq1 : q = 1
      · subst q
        simpa using isGood_one hFone
      by_cases hq2 : q = 2
      · subst q
        exact htwo
      by_cases hq3 : q = 3
      · subst q
        exact hthree
      by_cases hq : q.Prime
      · have hqge := hq.five_le_of_ne_two_of_ne_three hq2 hq3
        have hprev : ∀ j : ℕ, 0 < j → j < q → IsGood F (j : ZMod p) := by
          intro j hjpos hjlt
          exact ih j hjlt hjpos (by omega)
        intro x
        by_contra hx
        have hxnz : x ≠ 0 := by
          intro he
          subst x
          simp [hFzero] at hx
        let P : ZMod p → Prop := fun y => F ((q : ZMod p) * y) ≠ F q * F y
        have hneg : ∀ y, P (-y) ↔ P y := by
          intro y
          have he := exact_mul_iff (q := (q : ZMod p)) (x := y)
            hminus (hFnz (-1) (by simp))
          simpa only [neg_one_mul] using not_congr he
        have hsmall : ∀ j : ℕ, 0 < j → j < q → ∀ y,
            P ((j : ZMod p) * y) ↔ P y := by
          intro j hjpos hjlt y
          exact not_congr (exact_mul_iff (q := (q : ZMod p)) (x := y)
            (hprev j hjpos hjlt)
            (hFnz j (natCast_ne_zero_of_pos_lt hjpos (by omega))))
        obtain ⟨n, hn, hnshort, hnP⟩ :=
          short_representative_of_invariance p q hp hpgt hq hqge hqp
            P hneg hsmall ⟨x, hxnz, hx⟩
        apply hnP
        simpa only [Nat.cast_mul] using hlocal q n hqpos hn hnshort
      · obtain ⟨a, b, ha, hb, hab⟩ :=
          (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ q)).mp hq
        have hapos : 0 < a := by nlinarith
        have hbpos : 0 < b := by nlinarith
        have haga := ih a ha hapos (by omega)
        have hagb := ih b hb hbpos (by omega)
        rw [← hab, Nat.cast_mul]
        exact isGood_mul haga hagb
  intro x y
  by_cases hx : x = 0
  · simp [hx, hFzero]
  obtain ⟨n, hn, hnsmall, hxrep⟩ := central_nat_rep p hpodd x hx
  rcases hxrep with rfl | rfl
  · exact hgood n hn hnsmall y
  · have hg := isGood_mul hminus (hgood n hn hnsmall)
    simpa using hg y

end LiouvilleGoldbach
