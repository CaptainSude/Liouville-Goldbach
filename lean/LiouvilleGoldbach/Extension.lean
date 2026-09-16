import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace LiouvilleGoldbach

/-- The arithmetic step in the half-interval extension argument.  Every
possible minimal bad argument admits a smaller congruent argument after
multiplication by `2*j` or `3*j`, where `j < q`. -/
theorem extension_descent_certificate
    (p q n : ℕ) (hq : 5 ≤ q) (hn : 1 < n)
    (hnsmall : 2 * n < p) (hshort : p < 2 * q * n)
    (hpodd : p % 2 = 1) (hnodd : n % 2 = 1)
    (hrem : p % n ≠ 0) (hqmod : q % 3 = 1 ∨ q % 3 = 2) :
    ∃ a b j r : ℕ,
      0 < j ∧ j < q ∧ 0 < r ∧ r < n ∧
      (a = 2 * j ∨ a = 3 * j) ∧ (b = 1 ∨ b = 2) ∧
      (a * n = p + b * r ∨ p = a * n + b * r) := by
  have hs : (2 * q - 1) + 1 = 2 * q := by omega
  by_cases hstrip : (2 * q - 1) * n < p
  · rcases hqmod with hqm | hqm
    · let a := 2 * q + 1
      let j := a / 3
      let v := a * n - p
      have ha : a = 3 * j := by dsimp [a, j]; omega
      have hj : 0 < j ∧ j < q := by dsimp [j, a]; omega
      have hpn : p < a * n := by dsimp [a]; nlinarith
      have hv : v + p = a * n := Nat.sub_add_cancel (Nat.le_of_lt hpn)
      have hvlow : n < v := by dsimp [a] at hv; nlinarith
      have hvhigh : v < 2 * n := by dsimp [a] at hv; nlinarith
      have hvaodd : a % 2 = 1 := by dsimp [a]; omega
      have hvmod : v % 2 = 0 := by
        have hm := congrArg (fun t : ℕ => t % 2) hv
        rw [Nat.add_mod, Nat.mul_mod, hpodd, hnodd, hvaodd] at hm
        omega
      have hvdouble : 2 * (v / 2) = v := by omega
      refine ⟨a, 2, j, v / 2, hj.1, hj.2, ?_, ?_, Or.inr ha, Or.inr rfl,
        Or.inl ?_⟩
      · omega
      · omega
      · omega
    · let a := 2 * q - 1
      let j := a / 3
      let r := p - a * n
      have ha : a = 3 * j := by dsimp [a, j]; omega
      have hj : 0 < j ∧ j < q := by dsimp [j, a]; omega
      have hr : r + a * n = p := Nat.sub_add_cancel (Nat.le_of_lt hstrip)
      have hrpos : 0 < r := by dsimp [r, a]; omega
      have hrlt : r < n := by dsimp [a] at hr; nlinarith
      refine ⟨a, 1, j, r, hj.1, hj.2, hrpos, hrlt, Or.inr ha, Or.inl rfl,
        Or.inr ?_⟩
      omega
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
      have ha : a = 2 * j := by dsimp [a, j]; omega
      have hj : 0 < j ∧ j < q := by dsimp [j, a]; omega
      have hrpos : 0 < r := by dsimp [r]; omega
      have hrlt : r < n := by dsimp [r]; omega
      have hre : r + s = n := Nat.sub_add_cancel (Nat.le_of_lt hslt)
      refine ⟨a, 1, j, r, hj.1, hj.2, hrpos, hrlt, Or.inl ha, Or.inl rfl,
        Or.inl ?_⟩
      dsimp [a]
      nlinarith

/-- Multiplication by this residue is already known to be exact. -/
def IsGood {p : ℕ} (F : ZMod p → ℤ) (c : ZMod p) : Prop :=
  ∀ x, F (c * x) = F c * F x

theorem isGood_one {p : ℕ} {F : ZMod p → ℤ} (hF : F 1 = 1) : IsGood F 1 := by
  intro x
  simp [hF]

theorem isGood_mul {p : ℕ} {F : ZMod p → ℤ} {a b : ZMod p}
    (ha : IsGood F a) (hb : IsGood F b) : IsGood F (a * b) := by
  intro x
  calc
    F (a * b * x) = F a * F (b * x) := by simpa [mul_assoc] using ha (b * x)
    _ = F a * (F b * F x) := by rw [hb]
    _ = F (a * b) * F x := by rw [ha]; ring

/-- An exact nonvanishing multiplier preserves whether a multiplicativity
equation is true. -/
theorem exact_mul_iff {p : ℕ} {F : ZMod p → ℤ} {c q x : ZMod p}
    (hc : IsGood F c) (hFc : F c ≠ 0) :
    (F (q * (c * x)) = F q * F (c * x)) ↔
      (F (q * x) = F q * F x) := by
  rw [show q * (c * x) = c * (q * x) by ring, hc, hc]
  rw [show F q * (F c * F x) = F c * (F q * F x) by ring]
  constructor
  · exact mul_left_cancel₀ hFc
  · intro h
    rw [h]

theorem central_nat_rep (p : ℕ) [NeZero p] (hpodd : p % 2 = 1)
    (x : ZMod p) (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ 2 * n < p ∧ (x = n ∨ x = -(n : ZMod p)) := by
  have hvlt : x.val < p := ZMod.val_lt x
  have hvpos : 0 < x.val := by
    by_contra hv
    have hvzero : x.val = 0 := by omega
    apply hx
    rw [← ZMod.natCast_zmod_val x, hvzero]
    simp
  by_cases hhalf : 2 * x.val < p
  · exact ⟨x.val, hvpos, hhalf, Or.inl (ZMod.natCast_zmod_val x).symm⟩
  · refine ⟨p - x.val, by omega, by omega, Or.inr ?_⟩
    rw [Nat.cast_sub hvlt.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
    simp

theorem natCast_ne_zero_of_pos_lt {p n : ℕ} (hn : 0 < n) (hnp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  exact Nat.not_dvd_of_pos_of_lt hn hnp ((ZMod.natCast_eq_zero_iff n p).mp hz)

/-- Prime induction step: all smaller positive multipliers and the two exact
small multipliers suffice to make this prime globally exact. -/
theorem extension_prime_step (p q : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (hq : q.Prime) (hqge : 5 ≤ q) (hqp : 2 * q < p)
    (F : ZMod p → ℤ) (hFzero : F 0 = 0) (hFone : F 1 = 1)
    (hFnz : ∀ x, x ≠ 0 → F x ≠ 0)
    (hminus : IsGood F (-1)) (htwo : IsGood F 2) (hthree : IsGood F 3)
    (hlocal : ∀ a b : ℕ, 0 < a → 0 < b → 2 * (a * b) < p →
      F ((a * b : ℕ) : ZMod p) = F (a : ZMod p) * F (b : ZMod p))
    (hprev : ∀ j : ℕ, 0 < j → j < q → IsGood F (j : ZMod p)) :
    IsGood F (q : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have htwo_nz : (2 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_pos_lt (p := p) (n := 2) (by decide) (by omega)
  have hthree_nz : (3 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_pos_lt (p := p) (n := 3) (by decide) hpgt
  have hqmod : q % 3 = 1 ∨ q % 3 = 2 := by
    have hm : q % 3 ≠ 0 := by
      intro hm
      have hd := hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hm)
      omega
    omega
  have hcentral : ∀ n : ℕ, 0 < n → 2 * n < p →
      F ((q : ZMod p) * n) = F (q : ZMod p) * F (n : ZMod p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hnsmall
      by_cases hn1 : n = 1
      · subst n
        simp [hFone]
      have hnone : 1 < n := by omega
      by_cases hneven : n % 2 = 0
      · have hnhalf : 0 < n / 2 ∧ n / 2 < n ∧ 2 * (n / 2) < p := by omega
        have he := (exact_mul_iff htwo (hFnz 2 htwo_nz)).mpr
          (ih (n / 2) hnhalf.2.1 hnhalf.1 hnhalf.2.2)
        have hnat : 2 * (n / 2) = n := by omega
        have hcast : (2 : ZMod p) * (n / 2 : ℕ) = (n : ZMod p) := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using
            congrArg (fun t : ℕ => (t : ZMod p)) hnat
        rw [hcast] at he
        exact he
      have hnodd : n % 2 = 1 := by omega
      by_cases hshort : 2 * (q * n) < p
      · simpa only [Nat.cast_mul] using hlocal q n (by omega) hn hshort
      have hshort' : p < 2 * q * n := by
        have hne : 2 * q * n ≠ p := by
          intro he
          have hm := congrArg (fun t : ℕ => t % 2) he
          simp [Nat.mul_mod, hpodd] at hm
        have hle : p ≤ 2 * q * n := by nlinarith
        omega
      have hrem : p % n ≠ 0 := by
        intro hr
        have hd := hp.eq_one_or_self_of_dvd n (Nat.dvd_of_mod_eq_zero hr)
        omega
      obtain ⟨a, b, j, r, hjpos, hjlt, hrpos, hrlt, ha, hb, heq⟩ :=
        extension_descent_certificate p q n hqge hnone hnsmall hshort'
          hpodd hnodd hrem hqmod
      have hjgood := hprev j hjpos hjlt
      have hjnz : (j : ZMod p) ≠ 0 := natCast_ne_zero_of_pos_lt hjpos (by omega)
      have hagood : IsGood F (a : ZMod p) := by
        rcases ha with ha | ha
        · rw [ha, Nat.cast_mul]
          exact isGood_mul htwo hjgood
        · rw [ha, Nat.cast_mul]
          exact isGood_mul hthree hjgood
      have hanz : (a : ZMod p) ≠ 0 := by
        rcases ha with ha | ha
        · rw [ha, Nat.cast_mul]
          exact mul_ne_zero htwo_nz hjnz
        · rw [ha, Nat.cast_mul]
          exact mul_ne_zero hthree_nz hjnz
      have hbgood : IsGood F (b : ZMod p) := by
        rcases hb with rfl | rfl
        · simpa using isGood_one hFone
        · exact htwo
      have hbnz : (b : ZMod p) ≠ 0 := by
        rcases hb with rfl | rfl
        · simp
        · exact htwo_nz
      have hre := ih r hrlt hrpos (by omega)
      have hbre := (exact_mul_iff hbgood (hFnz b hbnz)).mpr hre
      apply (exact_mul_iff hagood (hFnz a hanz)).mp
      rcases heq with heq | heq
      · have hcast := congrArg (fun t : ℕ => (t : ZMod p)) heq
        simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_add] at hcast
        rw [hcast]
        exact hbre
      · have hcast := congrArg (fun t : ℕ => (t : ZMod p)) heq
        simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self] at hcast
        have han : (a : ZMod p) * n = -(b * (r : ZMod p)) := by
          linear_combination -hcast
        rw [han, show -(b * (r : ZMod p)) = (-1 : ZMod p) * (b * r) by ring]
        exact (exact_mul_iff hminus (hFnz (-1) (by simp))).mpr hbre
  intro x
  by_cases hx : x = 0
  · simp [hx, hFzero]
  obtain ⟨n, hn, hnsmall, hxrep⟩ := central_nat_rep p hpodd x hx
  rcases hxrep with rfl | rfl
  · exact hcentral n hn hnsmall
  · rw [show -(n : ZMod p) = (-1 : ZMod p) * n by ring]
    exact (exact_mul_iff hminus (hFnz (-1) (by simp))).mpr (hcentral n hn hnsmall)

/-- A function on a prime residue field which is locally multiplicative below
the half interval and globally exact at `-1`, `2`, and `3` is multiplicative
everywhere. No finite computation or unproved extension hypothesis is used. -/
theorem half_interval_extension (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
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
      · apply extension_prime_step p q hp hpgt hq
          (hq.five_le_of_ne_two_of_ne_three hq2 hq3) hqp F hFzero hFone hFnz
          hminus htwo hthree hlocal
        intro j hjpos hjlt
        exact ih j hjlt hjpos (by omega)
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
